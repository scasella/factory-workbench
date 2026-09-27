// The single authoritative write coordinator (§7.1).
//
// For every mutating request:
//   1. authenticate (caller supplies an authenticated Actor), bound size, check command id;
//   2. enter the write mutex and BEGIN IMMEDIATE;
//   3. resolve idempotency; load authoritative state + revision;
//   4. call the installed, digest-checked Lean kernel `apply`;
//   5. on acceptance atomically append journal, update state, insert outbox intents;
//      on rejection append an audit journal row without changing state;
//   6. COMMIT; only then return the receipt / allow effect dispatch.
// Any kernel fault aborts the transaction and disables mutation.

import { canonicalize, digestOf, sha256Hex, strictParse, type Json } from "../../packages/protocol/json.ts";
import type { Actor, Command, EffectIntent, Envelope, KernelState } from "../../packages/protocol/kernel-types.ts";
import { Db, nowIso } from "../../packages/store/db.ts";
import { KernelClient, KernelFault } from "./kernel.ts";

export interface Clock {
  /** Monotonic tick within the current controller epoch (ms). */
  tick(): number;
  /** Start a new epoch origin (called when the controller epoch advances). */
  resetOrigin(): void;
}

export class MonotonicClock implements Clock {
  private origin = process.hrtime.bigint();
  tick(): number {
    return Number((process.hrtime.bigint() - this.origin) / 1_000_000n);
  }
  resetOrigin(): void {
    this.origin = process.hrtime.bigint();
  }
}

/** Test clock: advanced explicitly. */
export class ManualClock implements Clock {
  now = 0;
  tick(): number {
    return this.now;
  }
  resetOrigin(): void {
    this.now = 0;
  }
  advance(ms: number): void {
    this.now += ms;
  }
}

export interface Receipt {
  command_id: string;
  seq: number;
  accepted: boolean;
  reject_code: string | null;
  events: Json[];
  effects: EffectIntent[];
  state_digest: string;
  duplicate?: boolean;
}

export class CommandConflict extends Error {
  readonly code = "COMMAND_ID_CONFLICT";
  constructor(id: string) {
    super(`command id ${id} was already used with a different request`);
  }
}

export const MAX_COMMAND_BYTES = 4 * 1024 * 1024;
export const MAX_STATE_BYTES = 64 * 1024 * 1024;

/** Test-only fault injection points (A23). Not reachable from the API. */
export interface CoordinatorFaults {
  afterKernelBeforeCommit?: () => void;
  afterCommitBeforeReturn?: () => void;
}

export class Coordinator {
  readonly db: Db;
  readonly kernel: KernelClient;
  readonly clock: Clock;
  private mutex: Promise<unknown> = Promise.resolve();
  disabled: string | null = null;
  faults: CoordinatorFaults = {};
  private listeners: ((r: Receipt) => void)[] = [];

  constructor(db: Db, kernel: KernelClient, clock: Clock) {
    this.db = db;
    this.kernel = kernel;
    this.clock = clock;
  }

  onCommit(fn: (r: Receipt) => void): void {
    this.listeners.push(fn);
  }

  /** Current authoritative state (read model). */
  state(): { seq: number; state: KernelState; digest: string } {
    const r = this.db.db.prepare("SELECT seq, state, digest FROM kstate WHERE id = 1").get() as
      | { seq: number; state: string; digest: string }
      | undefined;
    if (!r) throw new Error("state not initialized");
    return { seq: r.seq, state: strictParse(r.state, { numbers: "reject", maxBytes: MAX_STATE_BYTES }) as unknown as KernelState, digest: r.digest };
  }

  stateText(): { seq: number; text: string; digest: string } {
    const r = this.db.db.prepare("SELECT seq, state, digest FROM kstate WHERE id = 1").get() as
      | { seq: number; state: string; digest: string }
      | undefined;
    if (!r) throw new Error("state not initialized");
    return { seq: r.seq, text: r.state, digest: r.digest };
  }

  /** Initialize the kernel state from the kernel's own `initial` op. */
  async initialize(): Promise<void> {
    const exists = this.db.db.prepare("SELECT 1 FROM kstate WHERE id = 1").get();
    if (exists) return;
    const r = await this.kernel.query({ op: "initial" });
    const text = canonicalize(r.state);
    this.db.db.prepare("INSERT INTO kstate(id, seq, state, digest) VALUES (1, 0, ?, ?)").run(text, sha256Hex(text));
    this.db.setMeta("initial_state_digest", sha256Hex(text));
  }

  private lock<T>(fn: () => Promise<T>): Promise<T> {
    const r = this.mutex.then(fn, fn);
    this.mutex = r.catch(() => {});
    return r;
  }

  async submit(actor: Actor, command: Command, commandId: string): Promise<Receipt> {
    if (this.disabled) throw new KernelFault(`mutation disabled: ${this.disabled}`);
    if (!/^[A-Za-z0-9._:\-]{1,200}$/.test(commandId)) throw new Error("invalid command id");
    const request = { actor, command } as unknown as Json;
    const reqText = canonicalize(request);
    if (Buffer.byteLength(reqText) > MAX_COMMAND_BYTES) throw new Error("command too large");
    const requestDigest = sha256Hex(reqText);
    return this.lock(async () => {
      if (this.disabled) throw new KernelFault(`mutation disabled: ${this.disabled}`);
      const db = this.db;
      db.begin();
      let receipt: Receipt;
      try {
        const prior = db.db.prepare("SELECT * FROM journal WHERE command_id = ?").get(commandId) as any;
        if (prior) {
          db.rollback();
          if (prior.request_digest !== requestDigest) throw new CommandConflict(commandId);
          return { ...rowToReceipt(prior), duplicate: true };
        }
        const cur = db.db.prepare("SELECT seq, state, digest FROM kstate WHERE id = 1").get() as
          { seq: number; state: string; digest: string } | undefined;
        if (!cur) throw new Error("state not initialized");
        const epochNow = Number(JSON.parse(cur.state).ctrl_epoch as string);
        const isRecover = command.type === "recover_controller";
        const envelope: Envelope = {
          actor,
          epoch: String(isRecover ? epochNow + 1 : epochNow),
          tick: String(this.clock.tick()),
          command,
        };
        const stateJson = strictParse(cur.state, { numbers: "reject", maxBytes: MAX_STATE_BYTES });
        const resp = await this.kernel.call({ op: "apply", state: stateJson, envelope: envelope as unknown as Json });
        if (resp.ok !== true) {
          // The kernel could not even decode the request: a boundary/codec fault.
          throw new KernelFault(`kernel rejected request encoding: ${String(resp.code)} ${String(resp.message)}`);
        }
        const seq = cur.seq + 1;
        const wall = nowIso();
        if (resp.accepted === true) {
          const t = resp.transition as Record<string, Json>;
          const newText = canonicalize(t.state);
          if (Buffer.byteLength(newText) > MAX_STATE_BYTES) throw new KernelFault("state size limit exceeded");
          const newDigest = sha256Hex(newText);
          const effects = t.effects as unknown as EffectIntent[];
          db.db.prepare(
            "INSERT INTO journal(seq, command_id, request_digest, envelope, accepted, reject_code, events, effects, state_digest, wall_time) VALUES (?,?,?,?,1,NULL,?,?,?,?)",
          ).run(seq, commandId, requestDigest, canonicalize(envelope as unknown as Json), canonicalize(t.events),
            canonicalize(t.effects), newDigest, wall);
          db.db.prepare("UPDATE kstate SET seq = ?, state = ?, digest = ? WHERE id = 1").run(seq, newText, newDigest);
          const ins = db.db.prepare(
            "INSERT INTO outbox(effect_id, seq, kind, body, status, attempts, note, updated) VALUES (?,?,?,?, 'pending', 0, NULL, ?) ON CONFLICT(effect_id) DO NOTHING",
          );
          for (const eff of effects) ins.run(eff.id, seq, eff.kind, canonicalize(eff as unknown as Json), wall);
          receipt = { command_id: commandId, seq, accepted: true, reject_code: null, events: t.events as Json[],
            effects, state_digest: newDigest };
        } else {
          db.db.prepare(
            "INSERT INTO journal(seq, command_id, request_digest, envelope, accepted, reject_code, events, effects, state_digest, wall_time) VALUES (?,?,?,?,0,?,'[]','[]',?,?)",
          ).run(seq, commandId, requestDigest, canonicalize(envelope as unknown as Json), String(resp.reject), cur.digest, wall);
          db.db.prepare("UPDATE kstate SET seq = ? WHERE id = 1").run(seq);
          receipt = { command_id: commandId, seq, accepted: false, reject_code: String(resp.reject), events: [],
            effects: [], state_digest: cur.digest };
        }
        this.faults.afterKernelBeforeCommit?.();
        db.commit();
        // A recover command sets the kernel clock to its own tick: the new epoch's
        // monotonic origin. Ticks continue from this process's monotonic clock.
      } catch (e) {
        db.rollback();
        if (e instanceof KernelFault) this.disabled = e.message;
        throw e;
      }
      this.faults.afterCommitBeforeReturn?.();
      for (const l of this.listeners) {
        try {
          l(receipt);
        } catch {
          /* listeners are observers only */
        }
      }
      return receipt;
    });
  }

  /** Rebuild state from the initial state + accepted journal (A22) and compare. */
  async verifyJournal(): Promise<{ ok: boolean; entries: number; accepted: number; detail: string[] }> {
    const detail: string[] = [];
    const init = await this.kernel.query({ op: "initial" });
    let state: Json = init.state;
    if (sha256Hex(canonicalize(state)) !== this.db.getMeta("initial_state_digest")) {
      detail.push("initial state digest differs from recorded initial state");
    }
    // Snapshot the stored state and the journal together (synchronously, no
    // await between them) so commits made while verifying cannot cause a
    // false mismatch.
    const cur = this.stateText();
    const rows = this.db.db.prepare("SELECT * FROM journal ORDER BY seq").all() as any[];
    let accepted = 0;
    let prevDigest = sha256Hex(canonicalize(state));
    for (const row of rows) {
      const env = strictParse(row.envelope, { numbers: "reject" });
      const r = await this.kernel.query({ op: "apply", state, envelope: env });
      if (row.accepted === 1) {
        accepted++;
        if (r.accepted !== true) {
          detail.push(`seq ${row.seq}: journal says accepted, replay rejected (${String(r.reject)})`);
          break;
        }
        const t = r.transition as Record<string, Json>;
        state = t.state;
        const d = sha256Hex(canonicalize(state));
        if (d !== row.state_digest) detail.push(`seq ${row.seq}: state digest mismatch`);
        if (canonicalize(t.effects) !== row.effects) detail.push(`seq ${row.seq}: effects mismatch`);
        if (canonicalize(t.events) !== row.events) detail.push(`seq ${row.seq}: events mismatch`);
        prevDigest = d;
      } else {
        if (r.accepted === true) detail.push(`seq ${row.seq}: journal says rejected, replay accepted`);
        else if (String(r.reject) !== row.reject_code) detail.push(`seq ${row.seq}: reject code differs`);
        if (row.state_digest !== prevDigest) detail.push(`seq ${row.seq}: rejected entry changed state digest`);
      }
    }
    // Whole-journal fold through the kernel's own `replay` must agree too.
    const envs = rows.filter((r) => r.accepted === 1).map((r) => strictParse(r.envelope, { numbers: "reject" }));
    const rep = await this.kernel.query({ op: "replay", state: init.state, envelopes: envs });
    if (sha256Hex(canonicalize(rep.state)) !== cur.digest) detail.push("kernel replay fold differs from stored state");
    if (sha256Hex(cur.text) !== cur.digest) detail.push("stored state blob does not match its digest");
    return { ok: detail.length === 0, entries: rows.length, accepted, detail };
  }
}

function rowToReceipt(row: any): Receipt {
  return {
    command_id: row.command_id,
    seq: row.seq,
    accepted: row.accepted === 1,
    reject_code: row.reject_code,
    events: strictParse(row.events, { numbers: "reject" }) as Json[],
    effects: strictParse(row.effects, { numbers: "reject" }) as unknown as EffectIntent[],
    state_digest: row.state_digest,
  };
}

export function commandDigest(actor: Actor, command: Command): string {
  return digestOf({ actor, command });
}
