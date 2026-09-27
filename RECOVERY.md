# Recovery procedures

The journal is the recovery authority. The workbench never recovers by replaying LLM calls.

## Normal restart (crash or clean stop)

`node apps/control/cli.ts serve` always runs the startup protocol (§11) before dispatching anything:

1. Take the exclusive controller lock (`<state>/controller.lock`); a live second writer is refused.
2. Verify integrity: the stored kernel-state blob matches its digest; the latest journal entry's
   state digest matches the stored state; the installed kernel binary matches its recorded digest;
   the genesis bundle verifies.
3. Commit `recover_controller` through the kernel: the controller epoch advances, every attempt that
   still held authority (authorized/starting/running) becomes `lost`, steps lose authority, and the
   kernel emits `terminate` intents. Committed results are untouched. Retries happen only under the
   step's retry policy and the remaining parent budget (a lost attempt consumes one retry).
4. Reconcile containers by the instance label `io.factory-workbench.instance=<instance>` and
   terminate them (never by broad name matching; unrelated containers are not touched). Launch
   registry rows become `reconciled`; undispatched/uncertain launch intents become `superseded`.
5. Staged-but-unsubmitted results from the old epoch are discarded (they would be rejected as stale
   anyway — duplicate computation is possible, duplicate accepted commits are not).
6. Dispatch resumes from committed state.

Everything above is journaled (`audit` table has a `recovery` row with counts).

## Journal verification

```bash
node apps/control/cli.ts journal verify
```

Replays every journal entry (accepted and rejected) through the installed kernel from the recorded
initial state, comparing each state digest, event list and effect list (it stops at the first accepted entry that
replay rejects, since later entries depend on it), then compares the kernel's whole-journal `replay`
fold with the stored state. No model is invoked. Exit status 1 on any mismatch.

```bash
node apps/control/cli.ts journal export --out journal.jsonl
```

## Stalled or lost workers

- A silent long proof is not necessarily dead: the supervisor heartbeats while the container runs;
  the kernel only expires an attempt when a trusted monotonic tick reaches its lease deadline
  (equality is expired). Expiry fences the attempt and emits a terminate intent.
- A running process whose attempt lost authority is killed by the supervisor (heartbeat rejected →
  abort; terminate intents → `docker stop -t 3` then `rm -f` of the labelled container).
- The job page separates authorization, OS observation, transport outcome, accepted result, and
  cleanup (`none`/`pending`/`done`).

## Paused recovery / out-of-band pause

```bash
node apps/control/cli.ts recovery pause-all
```

Requests pause for every dispatchable job (stops new authorization; running attempts settle; each
job reaches `paused` only after the kernel accepts a trusted quiescence observation). Inspect with
`job show`, export the journal, then `job resume <id>` individually. If the UI or a planner is
broken, the CLI still works against the API; if the server cannot start, `journal verify/export`
work directly on the state directory.

A job whose pinned planner crashes, times out, or returns a plan violating the fixed contract is
**blocked from scheduling** with a diagnostic; it never silently switches to another planner. It can
be cancelled, or (audit jobs) paused and explicitly migrated to another activated release.

## Package rollback vs. backup restoration

- **Rollback** is an ordinary audited activation of a retained, published release (e.g. P0) with a
  fresh exact-digest approval against the current active base. It changes the default for *new*
  jobs only; it does not rewrite history or move existing jobs.
- **Backup restoration** (copying back an older `workbench.sqlite` + blob store) is a maintenance
  action outside the product: it discards every journal entry after the backup. After restoring,
  start the server normally — a new controller epoch fences everything that was live in the backup —
  and treat any external work performed after the backup as unknown. Keep the pre-restore state
  directory for audit. This is not equivalent to rollback.
- Kernel/schema/verifier changes are a maintenance upgrade with a new trust inventory: rebuild images,
  re-bootstrap a new state directory, and keep the old one read-only for audit.
