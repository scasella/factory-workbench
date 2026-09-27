# Contributing

Thanks for looking at Factory Workbench. Before changing anything, read [`AGENTS.md`](AGENTS.md): it
lists the invariants that must not break (one authority through the Lean kernel, proofs about the
executed code, the protected/evolvable boundary, evidence binding, fail-closed behaviour).

## Development loop

```bash
npm ci && npm run build:web
```

```bash
cd protected/lean && lake build
```

The fast checks need the kernel built above (the canonical-JSON tests run the real `factory-kernel`):

```bash
npm run typecheck
```

```bash
npm run test:fast
```

`protected/tests/unit/session-link.test.ts` and all acceptance tests also need Docker and the images
from `./scripts/build-images.sh` (they bootstrap a real state). Run one acceptance file with:

```bash
node --test --test-concurrency=1 protected/tests/acceptance/lifecycle.test.ts
```

Before a pull request that touches the control plane, kernel, verifier or UI, run the full gate
(30–60 minutes; it regenerates the evidence files under `docs/` and `DEMO-RESULTS.md`, which should be
committed with the change):

```bash
./scripts/check-all
```

## Changing protected code

Anything under `protected/` is part of the trust base. After changing it, rebuild the images
(`./scripts/build-images.sh`); existing bootstrapped state directories will then (correctly) report
verifier drift and must be re-bootstrapped. Never weaken a statement in `Contracts.lean` or
`PackageContracts.lean` to make a proof pass: if a statement is false, the kernel has a bug.

## UI and video

The operator UI lives in `apps/web` (React, no UI libraries). Design decisions are recorded in
[`docs/design/UI-REDESIGN.md`](docs/design/UI-REDESIGN.md). Browser end-to-end and recording scripts
live in `scripts/demo-video` (their own `package.json`, with Playwright); see
[`docs/video/README.md`](docs/video/README.md).

## Live inference

Never run live Codex inference or read `~/.codex` without the operator's explicit consent. Tests and
the demo use the deterministic fake (`packages/codex-adapter/fake-codex.ts`).
