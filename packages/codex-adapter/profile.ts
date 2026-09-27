// Runner-owned Codex security profile (SPEC §3.2, §10.2) and argument builder.

import { accessSync, constants, mkdirSync, statSync, writeFileSync } from "node:fs";
import { dirname, isAbsolute, join, resolve } from "node:path";
import type { CodexConfig } from "./types.ts";

/** Capabilities that must be off for the LLM runner. Verified by doctor against the pinned CLI. */
export const FORBIDDEN_FEATURES: readonly string[] = [
  "shell_tool", "unified_exec", "multi_agent", "multi_agent_v2", "apps", "plugins", "remote_plugin",
  "hooks", "memories", "browser_use", "browser_use_external", "computer_use", "in_app_browser",
  "image_generation", "tool_suggest", "skill_mcp_dependency_install", "workspace_dependencies",
  "code_mode_host", "goals", "sleep_tool",
];

/** config.toml text. `[features]` is deliberately the LAST table so doctor can append a sentinel key. */
export function profileToml(): string {
  const lines = [
    "# Factory Workbench runner-owned Codex profile. Generated; do not edit.",
    'approval_policy = "never"',
    'sandbox_mode = "read-only"',
    "mcp_servers = {}",
    "",
    "[features]",
    ...FORBIDDEN_FEATURES.map((f) => `${f} = false`),
  ];
  return lines.join("\n") + "\n";
}

export function writeProfile(codexHome: string): string {
  mkdirSync(codexHome, { recursive: true, mode: 0o700 });
  const path = join(codexHome, "config.toml");
  writeFileSync(path, profileToml(), { mode: 0o600 });
  return path;
}

export interface InvocationPaths {
  schemaPath: string;
  outPath: string;
  workspace: string;
  model?: string;
}

/** Full argv (excluding the executable). The prompt is never an argument: `-` means stdin. */
export function buildArgs(cfg: Pick<CodexConfig, "argsPrefix" | "globalArgs">, p: InvocationPaths): string[] {
  return [
    ...cfg.globalArgs,
    ...cfg.argsPrefix,
    "--sandbox", "read-only",
    "--json",
    "--output-schema", p.schemaPath,
    "--output-last-message", p.outPath,
    "--ephemeral",
    "--skip-git-repo-check",
    "--ignore-rules",
    "--strict-config",
    ...FORBIDDEN_FEATURES.flatMap((f) => ["--disable", f]),
    "-C", p.workspace,
    ...(p.model ? ["-m", p.model] : []),
    "-",
  ];
}

/** Flags the adapter relies on that must appear in `<prefix> --help`. */
export const EXEC_FLAGS: readonly string[] = [
  "--sandbox", "--json", "--output-schema", "--output-last-message", "--ephemeral",
  "--skip-git-repo-check", "--ignore-rules", "--strict-config", "--disable", "--cd", "--model",
];

/** Resolve a bare executable name against the controller's PATH (the child PATH is minimal). */
export function resolveExecutable(executable: string, searchPath = process.env.PATH ?? ""): string | null {
  const candidates = executable.includes("/") ? [executable] : searchPath.split(":").filter(Boolean).map((d) => join(d, executable));
  for (const c of candidates) {
    try {
      accessSync(c, constants.X_OK);
      if (!statSync(c).isFile()) continue;
      return isAbsolute(c) ? c : resolve(c);
    } catch {
      /* try next */
    }
  }
  return null;
}

/** Minimal child environment: nothing inherited except what is listed here. */
export function childEnv(cfg: Pick<CodexConfig, "executable" | "codexHome" | "env">, home: string): Record<string, string> {
  const exeDir = cfg.executable.includes("/") ? dirname(cfg.executable) : null;
  const path = ["/usr/bin", "/bin", "/usr/sbin", "/sbin", ...(exeDir ? [exeDir] : [])].join(":");
  return { ...(cfg.env ?? {}), PATH: path, HOME: home, CODEX_HOME: cfg.codexHome, LANG: "C.UTF-8" };
}
