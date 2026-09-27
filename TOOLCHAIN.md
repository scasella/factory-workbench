# Toolchain

Pinned identities are recorded in [`toolchains.lock.json`](toolchains.lock.json) and checked by
`workbench doctor`. Versions below were observed on the build host on 2026-09-26.

| Component | Pinned value | Where checked |
|---|---|---|
| Lean | `leanprover/lean4:v4.34.1` (commit `5045d005…`), elan 4.2.4 | `protected/lean/lean-toolchain`, image label `io.factory-workbench.toolchain`, doctor `lean_in_sandbox` / `lean_host_kernel_toolchain` |
| Independent proof checker | `leanchecker` bundled with the toolchain, invoked as `lake env leanchecker --fresh <Module>` (re-checks the module **and all imports from `Init`** from the `.olean` proof objects with the kernel type checker) | verifier `prove.sh`, `scripts/check-proofs.ts` |
| Node.js | 25.8.1 (native TypeScript type stripping; no transpile step) | doctor `node` |
| npm packages | `fastify 5.12.5`, `typescript 5.9.3`, `@types/node 25.0.3`; UI pins in `apps/web/package.json` | `package-lock.json` (`npm ci`) |
| SQLite | `node:sqlite` built-in (SQLite 3.51.3); WAL, `synchronous=FULL`, foreign keys | doctor `sqlite_pragmas` |
| Docker | client/server 29.8.0, `linux/aarch64` | doctor `container_engine` |
| Base image | `factory-lean-base:v4.34.1` from `debian:bookworm-slim` (Dockerfile now pins `@sha256:3783cc01…`); non-root `builder` (uid 10001) | `toolchains.lock.json` `images.lean_base.id` |
| Verifier/runtime image | `factory-verifier:dev` = base + protected Lean library prebuilt (`lake build Factory Factory:static factory-kernel`) + fixed harness; labels carry `core-digest`, `contract-digest`, `harness-digest`, `toolchain` computed from the sources copied in | `toolchains.lock.json` `images.verifier.id`; bootstrap records the id and labels; drift ⇒ verifier unavailable |
| Codex CLI | `codex-cli 0.155.1` at `/opt/homebrew/bin/codex`; noninteractive command `codex exec`; `codex --exec` is rejected | doctor `codex.*` |

## Offline provisioning

Network is needed only to build images (elan downloads the pinned toolchain; apt installs
`ca-certificates curl zstd git libc6-dev`) and for `npm ci`. Supply-chain note: the base image is
pinned by digest and the Lean toolchain by version, but `elan-init.sh` is fetched by tag without a
checksum and apt package versions are not pinned; the resulting image IDs are recorded in
`toolchains.lock.json`, and bootstrap binds the verifier image ID as a trust anchor. After that, every candidate build,
proof check, protected test and planner execution runs with `--network none`.

To move to an air-gapped host: `docker save factory-lean-base:v4.34.1 factory-verifier:dev`, copy
`node_modules` (or an npm cache), `docker load` on the target, and verify the image IDs against
`toolchains.lock.json` with `workbench doctor`.

## Rebuilding

```bash
./scripts/build-images.sh
```

Rebuilds the base image only if missing, rebuilds the verifier image with fresh identity labels, and
updates `toolchains.lock.json`. Any change to protected Lean sources, contracts or the harness
produces a different image id/labels. Because bootstrap pins these identities, an already
bootstrapped state treats the new image as **verifier drift** (build/prove/reproduce steps refuse to
run; nothing can be published) until an explicit maintenance re-bootstrap — there is no automatic
escape hatch (§12.1).

## Independent proof-checker setup

`leanchecker` ships with every Lean 4 toolchain installed by elan (`~/.elan/toolchains/<tc>/bin/leanchecker`
on the host; inside the image via `lake env`). The verifier runs it in the sandbox on the generated
trusted bridge module; `scripts/check-proofs.ts` runs it on `Factory.Proofs` (kernel theorems) on the
host. A fresh compilation alone is never labelled as independent replay.
