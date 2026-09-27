// TypeScript mirrors of the Lean codec encoding (protected/lean/Factory/Codec.lean).
// These are READ models for projections/UI; authority lives in the Lean kernel.
// Naturals are canonical decimal strings.

export type NatStr = string;
export type Digest = string;

export type Role = "author" | "materialize" | "build" | "prove" | "reproduce" | "refute" | "summarize";
export type JobKind = "package_audit" | "change_author" | "change_evaluate";
export type Outcome = "pass" | "fail" | "inconclusive";
export type JobStatus =
  | "queued" | "running" | "pause_requested" | "paused" | "blocked" | "succeeded" | "failed" | "cancelled";
export type StepStatus = "pending" | "active" | "succeeded" | "failed" | "blocked";
export type AttemptStatus =
  | "authorized" | "starting" | "running" | "succeeded" | "failed" | "expired" | "cancelled" | "lost";

export type InputSource = { type: "job_input" } | { type: "step_output"; step: string };
export interface InputBinding { name: string; source: InputSource }
export interface StepSpec {
  id: string; role: Role; after: string[]; inputs: InputBinding[]; prompt: string; retries: NatStr;
}
export interface WorkflowDef { kind: JobKind; steps: StepSpec[]; max_parallel: NatStr }
export interface PlannerView { workflow: WorkflowDef; ready: string[]; slots: NatStr }

export interface Accepted {
  gen: NatStr; job_epoch: NatStr; ctrl_epoch: NatStr; lease_deadline: NatStr; accepted_at: NatStr;
  release: Digest; subject: Digest; fingerprint: Digest; result: Digest; outcome: Outcome;
  produced: Digest | null; exports: WorkflowDef[]; contract: Digest;
}
export interface Attempt {
  step: string; role: Role; gen: NatStr; job_epoch: NatStr; ctrl_epoch: NatStr; deadline: NatStr;
  status: AttemptStatus; subject: Digest; fingerprint: Digest; inputs: [string, Digest][]; container: string;
}
export interface StepState {
  id: string; status: StepStatus; current: NatStr | null; accepted: Accepted | null; failures: NatStr;
}
export interface Job {
  id: string; kind: JobKind; release: Digest; input: Digest; subject: Digest; epoch: NatStr;
  status: JobStatus; steps: StepState[]; attempts: Attempt[]; budget: string; change: string | null;
  revision: NatStr;
}
export interface Budget { id: string; limit: NatStr; used: NatStr }
export interface Asset { path: string; digest: Digest }
export interface Release {
  digest: Digest; payload: Digest; source: Digest; parent: Digest | null; contract: Digest;
  workflows: WorkflowDef[]; assets: Asset[]; evidence_job: string | null; producer: Digest | null;
}
export interface Approval {
  id: string; release: Digest; expected_base: Digest; contract: Digest; operator: string; at: NatStr;
  revoked: boolean;
}
export interface Activation { release: Digest; base: Digest | null; approval: string | null; at: NatStr }
export interface Change {
  id: string; request: Digest; base: Digest; budget: string; revision_limit: NatStr; revisions: NatStr;
  jobs: string[]; candidates: Digest[]; status: "open" | "published" | "exhausted" | "closed";
}
export interface Migration {
  job: string; from: Digest; to: Digest; revision: NatStr; kept: string[]; reset: string[];
  retired: string[]; at: NatStr;
}
export interface Report { job: string; digest: Digest; subject: Digest }
export interface Config {
  llm_slots: NatStr; container_slots: NatStr; lease_ticks: NatStr; max_jobs: NatStr; max_steps: NatStr;
}
export interface KernelState {
  ctrl_epoch: NatStr; clock: NatStr; contract: Digest; config: Config; releases: Release[];
  active: Digest | null; activations: Activation[]; approvals: Approval[]; jobs: Job[];
  budgets: Budget[]; changes: Change[]; migrations: Migration[]; reports: Report[];
}

export type Actor =
  | { type: "operator"; name: string }
  | { type: "coordinator" }
  | { type: "supervisor" }
  | { type: "verifier" };

export interface ResultEnvelope {
  result: Digest; model_outcome: Outcome; trusted_outcome: Outcome; produced: Digest | null;
  exports: WorkflowDef[]; contract: Digest; fingerprint: Digest;
}

export type Command =
  | { type: "bootstrap"; genesis: Release; contract: Digest; config: Config }
  | { type: "create_job"; job: string; kind: JobKind; input: Digest; subject: Digest; release: Digest | null;
      budget: string; limit: NatStr }
  | { type: "start_attempt"; job: string; step: string; fingerprint: Digest }
  | { type: "observe_launch_dispatched"; job: string; step: string; gen: NatStr }
  | { type: "observe_process_started"; job: string; step: string; gen: NatStr; container: string }
  | { type: "heartbeat"; job: string; step: string; gen: NatStr }
  | { type: "commit_result"; job: string; step: string; gen: NatStr; result: ResultEnvelope }
  | { type: "record_verification"; job: string; step: string; gen: NatStr; result: ResultEnvelope }
  | { type: "fail_attempt"; job: string; step: string; gen: NatStr }
  | { type: "expire_attempt"; job: string; step: string; gen: NatStr }
  | { type: "pause_job"; job: string }
  | { type: "acknowledge_quiescence"; job: string; containers_clear: boolean }
  | { type: "resume_job"; job: string }
  | { type: "cancel_job"; job: string }
  | { type: "create_change"; change: string; request: Digest; author_job: string; budget: string;
      attempt_limit: NatStr; revision_limit: NatStr }
  | { type: "revise_change"; change: string; author_job: string; diagnostics: Digest }
  | { type: "register_candidate"; change: string; author_job: string; eval_job: string; source: Digest }
  | { type: "publish_report"; job: string; report: Digest }
  | { type: "publish_release"; job: string; release: Digest; assets: Asset[] }
  | { type: "record_approval"; approval: string; release: Digest; expected_base: Digest }
  | { type: "revoke_approval"; approval: string }
  | { type: "activate_release"; release: Digest; expected_active: Digest; approval: string }
  | { type: "migrate_job"; job: string; target: Digest; expected_revision: NatStr }
  | { type: "recover_controller" };

export interface Envelope { actor: Actor; epoch: NatStr; tick: NatStr; command: Command }

export interface EffectIntent {
  id: string; kind: "launch" | "terminate" | "release_published" | "report_published";
  job: string; step: string; gen: NatStr; subject: Digest; inputs: [string, Digest][];
}
export interface DomainEvent { type: string; [k: string]: unknown }
export interface Transition { state: KernelState; events: DomainEvent[]; effects: EffectIntent[] }

export const LIVE_ATTEMPT: ReadonlySet<AttemptStatus> = new Set(["authorized", "starting", "running"]);
export const TERMINAL_JOB: ReadonlySet<JobStatus> = new Set(["blocked", "succeeded", "failed", "cancelled"]);
export const VERIFIER_ROLES: ReadonlySet<Role> = new Set(["build", "prove"]);
export const LLM_ROLES: ReadonlySet<Role> = new Set(["author", "reproduce", "refute", "summarize"]);
