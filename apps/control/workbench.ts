// Workbench wiring: state directory, controller lock, installed kernel,
// coordinator, verifier environment, planner pool, engine; plus the
// human-authorized bootstrap (trust root) and the startup recovery protocol.

import * as fs from "node:fs";
import * as path from "node:path";
import { randomBytes } from "node:crypto";
import { canonicalize, digestOf, sha256Hex, type Json } from "../../packages/protocol/json.ts";
import type { Actor, Config, KernelState, Release } from "../../packages/protocol/kernel-types.ts";
import { BlobStore } from "../../packages/store/blobs.ts";
import { Db, nowIso } from "../../packages/store/db.ts";
import { Docker, LABEL_ROOT } from "../../packages/runner/docker.ts";
import { writeProfile } from "../../packages/codex-adapter/profile.ts";
import { probeCodex } from "../../packages/codex-adapter/doctor.ts";
import type { CodexConfig } from "../../packages/codex-adapter/types.ts";
import { computeIdentities, type Identities } from "../../protected/verifier/identity.ts";
import { importPackageDir } from "../../protected/verifier/package-source.ts";
import { buildPhase, protectedTests, provePhase, receiptText, type VerifierEnv } from "../../protected/verifier/verifier.ts";
import { Coordinator, MonotonicClock, type Clock } from "./coordinator.ts";
import { KernelClient, fileDigest } from "./kernel.ts";
import { Engine, COORD } from "./engine.ts";
import { PlannerPool } from "./planner.ts";
import { createBundle, verifyBundle } from "./releases.ts";
import { REPO_ROOT, statePaths, type Settings } from "./config.ts";
import type { AttemptCtx } from "./executors.ts";

export class LockError extends Error {}

function takeLock(file: string): void {
  try {
    fs.writeFileSync(file, String(process.pid), { flag: "wx", mode: 0o600 });
    return;
  } catch (e: any) {
    if (e.code !== "EEXIST") throw e;
  }
  const pid = Number(fs.readFileSync(file, "utf8").trim());
  let alive = false;
  try {
    process.kill(pid, 0);
    alive = pid !== process.pid;
  } catch {
    alive = false;
  }
  if (alive) throw new LockError(`another controller (pid ${pid}) holds ${file}; refusing a second writer`);
  fs.writeFileSync(file, String(process.pid), { mode: 0o600 });
}

export interface OpenOptions {
  clock?: Clock;
  /** Skip the controller lock (read-only inspection tools). */
  inspectOnly?: boolean;
}

export class Workbench {
  readonly settings: Settings;
  readonly paths: ReturnType<typeof statePaths>;
  readonly repo = REPO_ROOT;
  readonly db: Db;
  readonly blobs: BlobStore;
  readonly docker = new Docker();
  kernel!: KernelClient;
  coord!: Coordinator;
  ids!: Identities;
  verifierEnv!: VerifierEnv;
  planners!: PlannerPool;
  engine!: Engine;
  readonly logs: string[] = [];
  private codexCache: { cfg: CodexConfig; fake: boolean; blocked: string | null; configDigest: string } | null = null;
  private locked = false;

  private constructor(settings: Settings, opts: OpenOptions) {
    this.settings = settings;
    this.paths = statePaths(settings.stateDir);
    for (const d of [settings.stateDir, this.paths.attempts, this.paths.staging, this.paths.releases, this.paths.operator, this.paths.kernel]) {
      fs.mkdirSync(d, { recursive: true, mode: 0o700 });
    }
    fs.chmodSync(this.paths.operator, 0o700);
    if (!opts.inspectOnly) {
      takeLock(this.paths.lock);
      this.locked = true;
    }
    this.db = new Db(this.paths.db);
    this.blobs = new BlobStore(this.paths.blobs);
  }

  static async open(settings: Settings, opts: OpenOptions = {}): Promise<Workbench> {
    const wb = new Workbench(settings, opts);
    await wb.init(opts.clock ?? new MonotonicClock());
    return wb;
  }

  private async init(clock: Clock): Promise<void> {
    const kbin = path.join(this.paths.kernel, "factory-kernel");
    const kdigest = this.db.getMeta("kernel_digest");
    if (kdigest && fs.existsSync(kbin)) {
      this.kernel = new KernelClient(kbin, kdigest, this.settings.limits.kernelTimeoutMs);
    } else {
      // Not yet bootstrapped: use the freshly built protected kernel (bootstrap installs it).
      const built = path.join(this.repo, "protected/lean/.lake/build/bin/factory-kernel");
      this.kernel = new KernelClient(built, fs.existsSync(built) ? fileDigest(built) : "missing", this.settings.limits.kernelTimeoutMs);
    }
    this.coord = new Coordinator(this.db, this.kernel, clock);
    const img = await this.docker.inspectImage(this.settings.verifierImage);
    this.ids = computeIdentities(this.repo, this.settings.verifierImage, img?.id ?? "unavailable", img?.labels ?? {});
    this.verifierEnv = {
      docker: this.docker, blobs: this.blobs, kernel: this.kernel, ids: this.ids,
      scratch: this.paths.staging, instance: this.settings.instance,
      buildTimeoutMs: this.settings.limits.buildTimeoutMs, proveTimeoutMs: this.settings.limits.proofTimeoutMs,
      testTimeoutMs: this.settings.limits.testTimeoutMs,
    };
    this.planners = new PlannerPool({ stateDir: this.settings.stateDir, image: this.settings.verifierImage,
      instance: this.settings.instance, timeoutMs: this.settings.limits.plannerTimeoutMs });
    this.engine = new Engine(this);
  }

  log(msg: string): void {
    const line = `${nowIso()} ${msg}`;
    this.logs.push(line);
    if (this.logs.length > 2000) this.logs.shift();
    if (process.env.FACTORY_VERBOSE) console.error(line);
  }

  operator(): Actor {
    return { type: "operator", name: this.settings.operatorName };
  }

  state(): KernelState {
    return this.coord.state().state;
  }

  bootstrapped(): boolean {
    return !!this.db.getMeta("genesis_release");
  }

  /** Assurance-relevant trust anchors recorded at bootstrap, compared now. */
  trustStatus(): { id: string; ok: boolean; detail: string }[] {
    const out: { id: string; ok: boolean; detail: string }[] = [];
    const cmp = (id: string, key: string, now: string) => {
      const was = this.db.getMeta(key);
      out.push({ id, ok: !!was && was === now, detail: was === now ? now : `recorded ${was ?? "none"}, observed ${now}` });
    };
    cmp("contract_digest", "contract_digest", this.ids.contract_digest);
    cmp("core_digest", "core_digest", this.ids.core_digest);
    cmp("harness_digest", "harness_digest", this.ids.harness_digest);
    cmp("verifier_image_id", "verifier_image_id", this.ids.verifier_image_id);
    cmp("toolchain", "toolchain", this.ids.toolchain);
    const kd = this.db.getMeta("kernel_digest");
    const kbin = path.join(this.paths.kernel, "factory-kernel");
    const now = fs.existsSync(kbin) ? fileDigest(kbin) : "missing";
    out.push({ id: "kernel_digest", ok: !!kd && kd === now, detail: kd === now ? now : `recorded ${kd ?? "none"}, observed ${now}` });
    return out;
  }

  verifierAvailable(): { ok: boolean; detail: string } {
    const bad = this.trustStatus().filter((c) => !c.ok);
    if (this.ids.verifier_image_id === "unavailable") return { ok: false, detail: `verifier image ${this.settings.verifierImage} unavailable` };
    if (bad.length) return { ok: false, detail: `protected identity drift: ${bad.map((b) => b.id).join(", ")}` };
    return { ok: true, detail: "installed verifier matches bootstrap trust anchors" };
  }

  codexConfig(): { cfg: CodexConfig; fake: boolean; blocked: string | null; configDigest: string } {
    if (this.codexCache) return this.codexCache;
    const c = this.settings.codex;
    const fake = c.mode === "fake";
    writeProfile(c.codexHome);
    const cfg: CodexConfig = {
      executable: c.executable, argsPrefix: c.argsPrefix, globalArgs: c.globalArgs, codexHome: c.codexHome,
      workspaceRoot: path.join(this.paths.attempts, "llm-workspaces"), model: c.model,
      env: fake ? { FAKE_CODEX_NODE: process.execPath, FAKE_CODEX_SCENARIO: c.fakeScenario ?? "",
        ...(process.env.FAKE_CODEX_LATENCY_MS ? { FAKE_CODEX_LATENCY_MS: process.env.FAKE_CODEX_LATENCY_MS } : {}) } : {},
    };
    const blocked = fake ? null : this.db.getMeta("live_codex_ok") === "1" ? null : "live Codex mode requires a passing `node apps/control/cli.ts doctor --live --consent` (see OPEN-ITEMS: unified_exec)";
    this.codexCache = { cfg, fake, blocked, configDigest: digestOf({ executable: c.executable, argsPrefix: c.argsPrefix, model: c.model ?? null, fake } as unknown as Json) };
    return this.codexCache;
  }

  async doctorCodex() {
    const { cfg } = this.codexConfig();
    const report = await probeCodex(cfg);
    if (!this.codexConfig().fake) this.db.setMeta("live_codex_ok", report.ok ? "1" : "0");
    return report;
  }

  recordReceipt(digest: string, ctx: AttemptCtx, subject: string, kind: string): void {
    this.db.db.prepare("INSERT OR IGNORE INTO receipts_meta(receipt_digest, job, step, gen, subject, kind, created) VALUES (?,?,?,?,?,?,?)")
      .run(digest, ctx.job.id, ctx.attempt.step, Number(ctx.attempt.gen), subject, kind, nowIso());
  }

  // ------------------------------------------------------------------ bootstrap

  /** Human-authorized bootstrap: install the kernel, verify genesis with the
   *  fixed verifier, build the genesis bundle, and commit the trust root. */
  async bootstrap(genesisDir: string, progress: (m: string) => void = () => {}): Promise<string> {
    if (this.bootstrapped()) throw new Error("already bootstrapped");
    const built = path.join(this.repo, "protected/lean/.lake/build/bin/factory-kernel");
    if (!fs.existsSync(built)) throw new Error("kernel not built: run `lake build` in protected/lean (scripts/bootstrap does this)");
    const kbin = path.join(this.paths.kernel, "factory-kernel");
    fs.copyFileSync(built, kbin);
    fs.chmodSync(kbin, 0o555);
    const kd = fileDigest(kbin);
    this.db.setMeta("kernel_digest", kd);
    this.kernel.stop();
    this.kernel = new KernelClient(kbin, kd, this.settings.limits.kernelTimeoutMs);
    this.coord = new Coordinator(this.db, this.kernel, this.coord.clock);
    this.verifierEnv.kernel = this.kernel;
    this.engine = new Engine(this);
    if (this.ids.verifier_image_id === "unavailable") throw new Error(`verifier image ${this.settings.verifierImage} not available`);
    if (this.ids.core_digest === "unavailable") throw new Error("verifier image lacks protected identity labels; build it with scripts/build-images.sh");
    for (const [k, v] of Object.entries({ contract_digest: this.ids.contract_digest, core_digest: this.ids.core_digest,
      harness_digest: this.ids.harness_digest, verifier_image_id: this.ids.verifier_image_id, toolchain: this.ids.toolchain })) {
      this.db.setMeta(k, v);
    }
    await this.coord.initialize();
    progress("importing genesis package");
    const g = importPackageDir(genesisDir, this.blobs);
    const gsrc = this.blobs.put(canonicalize(g as unknown as Json));
    const tag = `${this.settings.instance}-genesis-${randomBytes(3).toString("hex")}`;
    progress("verifier build phase (sandboxed)");
    const b = await buildPhase(this.verifierEnv, { name: `fw-${tag}-build`, labels: {} }, g, g);
    if (b.receipt.outcome !== "pass") throw new Error(`genesis build failed: ${b.receipt.failure}`);
    const bd = this.blobs.put(receiptText(b.receipt));
    progress("verifier proof phase (bridge, axioms, leanchecker --fresh)");
    const p = await provePhase(this.verifierEnv, { name: `fw-${tag}-prove`, labels: {} }, g, g, b.receipt, bd);
    if (p.outcome !== "pass") throw new Error(`genesis proofs failed: ${p.failure}`);
    const pd = this.blobs.put(receiptText(p));
    progress("protected tests");
    const t = await protectedTests(this.verifierEnv, { name: `fw-${tag}-tests`, labels: {} }, b.receipt, g);
    if (t.outcome !== "pass") throw new Error(`genesis protected tests failed: ${t.detail}`);
    const td = this.blobs.put(receiptText(t));
    const envelope = {
      payload_digest: b.receipt.payload_digest!, recipe: "pin_only", lineage: { parent: null, producer: null },
      evidence: [
        { role: "build", job: null, step: null, gen: null, result: bd },
        { role: "prove", job: null, step: null, gen: null, result: pd },
        { role: "protected_tests", job: null, step: null, gen: null, result: td },
      ],
    };
    const { releaseDigest } = createBundle(this.settings.stateDir, this.blobs, this.db, { source: g, build: b.receipt, buildReceiptDigest: bd, envelope });
    const genesis: Release = {
      digest: releaseDigest, payload: b.receipt.payload_digest!, source: gsrc, parent: null, contract: this.ids.contract_digest,
      workflows: b.receipt.exports, assets: b.receipt.assets, evidence_job: null, producer: null,
    };
    const L = this.settings.limits;
    const config: Config = { llm_slots: String(L.llmSlots), container_slots: String(L.containerSlots),
      lease_ticks: String(L.leaseMs), max_jobs: String(L.maxJobs), max_steps: String(L.maxSteps) };
    // The bootstrap command itself goes through the kernel.
    const r = await this.coord.submit(this.operator(), { type: "bootstrap", genesis, contract: this.ids.contract_digest, config }, "bootstrap:genesis");
    if (!r.accepted) throw new Error(`kernel rejected bootstrap: ${r.reject_code}`);
    this.db.setMeta("genesis_release", releaseDigest);
    this.db.db.prepare("INSERT OR IGNORE INTO fixtures(digest, name, manifest_digest, created) VALUES (?,?,?,?)")
      .run(gsrc, "genesis-package", gsrc, nowIso());
    const token = randomBytes(32).toString("hex");
    fs.writeFileSync(path.join(this.paths.operator, "token"), token, { mode: 0o600 });
    fs.writeFileSync(path.join(this.paths.operator, "genesis-manifest.json"), canonicalize({
      genesis_release: releaseDigest, payload_digest: genesis.payload, source_digest: gsrc, kernel_digest: kd,
      identities: this.ids, receipts: { build: bd, prove: pd, protected_tests: td }, bootstrapped_by: this.settings.operatorName,
      note: "Human-authorized trust root. Not a self-certified release.",
    } as unknown as Json), { mode: 0o600 });
    return releaseDigest;
  }

  // ------------------------------------------------------------------ recovery

  /** Startup protocol (§11): integrity → new epoch (fences old authority) →
   *  reconcile/terminate old containers → discard fenced staged results. */
  async recover(): Promise<{ epoch: string; terminated: number; lost: number; superseded: number; staleStaged: number }> {
    const cur = this.coord.stateText();
    if (sha256Hex(cur.text) !== cur.digest) throw new Error("state blob does not match its digest; refusing to start");
    const last = this.db.db.prepare("SELECT state_digest FROM journal ORDER BY seq DESC LIMIT 1").get() as { state_digest: string } | undefined;
    if (last && last.state_digest !== cur.digest) throw new Error("latest journal entry does not match stored state; refusing to start");
    const genesis = this.db.getMeta("genesis_release");
    if (genesis) verifyBundle(this.settings.stateDir, genesis);
    // Kernel-evaluated invariant diagnostics (the same Boolean checkers the K-theorems are stated over).
    const invariants = await this.kernel.query({ op: "invariants", state: JSON.parse(cur.text) });
    if (invariants.safe !== true) throw new Error(`state fails kernel invariants; refusing to start: ${JSON.stringify(invariants.violations)}`);
    const before = this.state();
    const liveBefore = before.jobs.flatMap((j) => j.attempts.filter((a) => ["authorized", "starting", "running"].includes(a.status))).length;
    const r = await this.coord.submit(COORD, { type: "recover_controller" }, `recover:${Number(before.ctrl_epoch) + 1}`);
    if (!r.accepted) throw new Error(`recover_controller rejected: ${r.reject_code}`);
    let terminated = 0;
    const inv = await this.docker.inventory(this.settings.instance).catch(() => []);
    for (const c of inv) {
      await this.docker.terminate(c.id, this.settings.limits.graceSec);
      terminated++;
    }
    this.db.db.prepare("UPDATE launches SET state = 'reconciled', updated = ? WHERE state IN ('intent','started')").run(nowIso());
    const sup = this.db.db.prepare("UPDATE outbox SET status = 'superseded', note = 'fenced by controller recovery (execution outcome unknown)', updated = ? WHERE status IN ('pending','dispatched') AND kind = 'launch'")
      .run(nowIso());
    const stale = this.db.db.prepare("UPDATE staged_results SET status = 'submitted' WHERE status = 'staged'").run();
    this.db.db.prepare("INSERT INTO audit(kind, detail, created) VALUES ('recovery', ?, ?)")
      .run(canonicalize({ epoch: this.state().ctrl_epoch, terminated, lost: liveBefore } as unknown as Json), nowIso());
    return { epoch: this.state().ctrl_epoch, terminated, lost: liveBefore, superseded: Number(sup.changes), staleStaged: Number(stale.changes) };
  }

  async start(): Promise<void> {
    if (!this.bootstrapped()) throw new Error("not bootstrapped; run `node apps/control/cli.ts bootstrap`");
    await this.recover();
    this.engine.start();
  }

  async close(): Promise<void> {
    await this.engine.stop();
    this.planners.stopAll();
    this.kernel.stop();
    this.db.close();
    if (this.locked) {
      try {
        if (fs.readFileSync(this.paths.lock, "utf8").trim() === String(process.pid)) fs.rmSync(this.paths.lock);
      } catch {
        /* ignore */
      }
    }
  }

  /** Labels identifying this workbench's containers (for UI/diagnostics). */
  static instanceLabel(instance: string): string {
    return `${LABEL_ROOT}.instance=${instance}`;
  }
}
