// Authoritative SQLite store (§7.1). WAL, FULL synchronous, foreign keys,
// single serialized writer (enforced by the coordinator's write mutex and the
// controller lock file). The canonical kernel-state blob + revision is the
// write model; all other tables are projections/host observations.

import { DatabaseSync } from "node:sqlite";
import * as fs from "node:fs";
import * as path from "node:path";

export const SCHEMA_VERSION = "1";

const DDL = `
CREATE TABLE IF NOT EXISTS meta (key TEXT PRIMARY KEY, value TEXT NOT NULL);
CREATE TABLE IF NOT EXISTS kstate (
  id INTEGER PRIMARY KEY CHECK (id = 1),
  seq INTEGER NOT NULL,
  state TEXT NOT NULL,
  digest TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS journal (
  seq INTEGER PRIMARY KEY,
  command_id TEXT NOT NULL UNIQUE,
  request_digest TEXT NOT NULL,
  envelope TEXT NOT NULL,
  accepted INTEGER NOT NULL CHECK (accepted IN (0,1)),
  reject_code TEXT,
  events TEXT NOT NULL,
  effects TEXT NOT NULL,
  state_digest TEXT NOT NULL,
  wall_time TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS outbox (
  effect_id TEXT PRIMARY KEY,
  seq INTEGER NOT NULL REFERENCES journal(seq),
  kind TEXT NOT NULL,
  body TEXT NOT NULL,
  status TEXT NOT NULL CHECK (status IN ('pending','dispatched','done','superseded')),
  attempts INTEGER NOT NULL DEFAULT 0,
  note TEXT,
  updated TEXT NOT NULL
);
CREATE INDEX IF NOT EXISTS outbox_status ON outbox(status);
CREATE TABLE IF NOT EXISTS artifacts (
  digest TEXT PRIMARY KEY,
  kind TEXT NOT NULL,
  size INTEGER NOT NULL,
  media TEXT NOT NULL,
  label TEXT,
  created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS attempt_obs (
  job TEXT NOT NULL, step TEXT NOT NULL, gen INTEGER NOT NULL,
  container TEXT, phase TEXT NOT NULL, last_output TEXT, cleanup TEXT NOT NULL DEFAULT 'none',
  detail TEXT, updated TEXT NOT NULL,
  PRIMARY KEY (job, step, gen)
);
CREATE TABLE IF NOT EXISTS invocations (
  id TEXT PRIMARY KEY, job TEXT NOT NULL, step TEXT NOT NULL, gen INTEGER NOT NULL, role TEXT NOT NULL,
  fake INTEGER NOT NULL, config_digest TEXT NOT NULL, prompt_digest TEXT NOT NULL,
  context_digest TEXT NOT NULL, transcript_digest TEXT, stderr_digest TEXT, transport TEXT,
  exit_code INTEGER, usage TEXT, result_digest TEXT, diagnostics TEXT, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS staged_results (
  job TEXT NOT NULL, step TEXT NOT NULL, gen INTEGER NOT NULL,
  command TEXT NOT NULL, status TEXT NOT NULL CHECK (status IN ('staged','submitted')),
  created TEXT NOT NULL,
  PRIMARY KEY (job, step, gen)
);
CREATE TABLE IF NOT EXISTS changes_meta (
  change_id TEXT PRIMARY KEY, request_text TEXT NOT NULL, request_digest TEXT NOT NULL,
  base TEXT NOT NULL, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS candidates (
  source_digest TEXT PRIMARY KEY, change_id TEXT NOT NULL, revision INTEGER NOT NULL,
  author_job TEXT NOT NULL, manifest_digest TEXT NOT NULL, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS rejected_candidates (
  id INTEGER PRIMARY KEY AUTOINCREMENT, change_id TEXT NOT NULL, author_job TEXT NOT NULL,
  stage TEXT NOT NULL, reason TEXT NOT NULL, detail_digest TEXT, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS release_bundles (
  release_digest TEXT PRIMARY KEY, payload_digest TEXT NOT NULL, source_digest TEXT NOT NULL,
  envelope_digest TEXT NOT NULL, bundle_dir TEXT NOT NULL, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS receipts_meta (
  receipt_digest TEXT PRIMARY KEY, job TEXT NOT NULL, step TEXT NOT NULL, gen INTEGER NOT NULL,
  subject TEXT NOT NULL, kind TEXT NOT NULL, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS launches (
  effect_id TEXT PRIMARY KEY, container_name TEXT NOT NULL, container_id TEXT,
  job TEXT NOT NULL, step TEXT NOT NULL, gen INTEGER NOT NULL, epoch INTEGER NOT NULL,
  state TEXT NOT NULL, updated TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS job_diagnostics (
  id INTEGER PRIMARY KEY AUTOINCREMENT, job TEXT NOT NULL, kind TEXT NOT NULL, detail TEXT NOT NULL, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS revisions (
  change_id TEXT NOT NULL, from_job TEXT NOT NULL, new_job TEXT, status TEXT NOT NULL, created TEXT NOT NULL,
  PRIMARY KEY (change_id, from_job)
);
CREATE TABLE IF NOT EXISTS audit (
  id INTEGER PRIMARY KEY AUTOINCREMENT, kind TEXT NOT NULL, detail TEXT NOT NULL, created TEXT NOT NULL
);
CREATE TABLE IF NOT EXISTS fixtures (
  digest TEXT PRIMARY KEY, name TEXT NOT NULL, manifest_digest TEXT NOT NULL, created TEXT NOT NULL
);
`;

export class Db {
  readonly db: DatabaseSync;
  readonly file: string;

  constructor(file: string) {
    this.file = file;
    fs.mkdirSync(path.dirname(file), { recursive: true, mode: 0o700 });
    this.db = new DatabaseSync(file);
    this.db.exec("PRAGMA journal_mode = WAL;");
    this.db.exec("PRAGMA synchronous = FULL;");
    this.db.exec("PRAGMA foreign_keys = ON;");
    this.db.exec("PRAGMA busy_timeout = 5000;");
    this.db.exec(DDL);
    const v = this.getMeta("schema_version");
    if (v === undefined) this.setMeta("schema_version", SCHEMA_VERSION);
    else if (v !== SCHEMA_VERSION) throw new Error(`schema version ${v} unsupported (want ${SCHEMA_VERSION})`);
  }

  pragma(name: string): unknown {
    const row = this.db.prepare(`PRAGMA ${name}`).get() as Record<string, unknown> | undefined;
    return row ? Object.values(row)[0] : undefined;
  }

  getMeta(key: string): string | undefined {
    const r = this.db.prepare("SELECT value FROM meta WHERE key = ?").get(key) as { value: string } | undefined;
    return r?.value;
  }

  setMeta(key: string, value: string): void {
    this.db.prepare("INSERT INTO meta(key, value) VALUES(?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value")
      .run(key, value);
  }

  begin(): void {
    this.db.exec("BEGIN IMMEDIATE");
  }
  commit(): void {
    this.db.exec("COMMIT");
  }
  rollback(): void {
    if (this.db.isTransaction) this.db.exec("ROLLBACK");
  }

  close(): void {
    this.db.close();
  }
}

export function nowIso(): string {
  return new Date().toISOString();
}
