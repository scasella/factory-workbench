// Source lint for candidate Lean packages (§9.3 step 5). Lint SUPPLEMENTS the
// real checks (bridge elaboration, axiom closure, leanchecker replay, binary
// differential agreement); it never replaces them. It is deliberately
// conservative: forbidden tokens are rejected even inside comments.

export interface LintFinding { file: string; rule: string; detail: string }

const FORBIDDEN_WORDS = [
  "sorry", "admit", "axiom", "native_decide", "implemented_by", "extern", "unsafe", "partial",
  "opaque", "run_cmd", "run_tac", "run_elab", "elab", "elab_rules", "macro", "macro_rules", "syntax",
  "initialize", "builtin_initialize", "csimp", "_root_", "decreasing_trivial_pre_omega",
  "ofReduceBool", "ofReduceNat", "trustCompiler", "debug", "Lean.Elab", "Lean.Meta", "IO",
  "unsafeCast", "unsafeIO", "panic", "dbg_trace", "dbgTrace", "noncomputable",
];
const FORBIDDEN_COMMANDS = ["#eval", "#exit", "#print", "#check_failure", "#reduce", "#synth", "#guard_msgs"];
const ALLOWED_SET_OPTIONS = new Set(["maxRecDepth", "maxHeartbeats", "autoImplicit"]);

const IMPORT_ALLOW: Record<string, string[]> = {
  "Package.lean": ["Factory.Types"],
  "Planner.lean": ["Factory.Types", "Factory.Workflow", "FactoryPkg.Package"],
  "Proofs.lean": [
    "Factory.Types", "Factory.Workflow", "Factory.PackageContracts",
    "FactoryPkg.Package", "FactoryPkg.Planner", "FactoryPrev.Package", "FactoryPrev.Planner",
  ],
};

function wordRe(w: string): RegExp {
  const esc = w.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return new RegExp(`(^|[^A-Za-z0-9_'.])${esc}($|[^A-Za-z0-9_'])`);
}

export function lintLean(file: string, text: string): LintFinding[] {
  const out: LintFinding[] = [];
  if (!(file in IMPORT_ALLOW)) {
    out.push({ file, rule: "unexpected-lean-file", detail: "only Package.lean, Planner.lean, Proofs.lean are compiled" });
    return out;
  }
  for (const w of FORBIDDEN_WORDS) if (wordRe(w).test(text)) out.push({ file, rule: "forbidden-token", detail: w });
  for (const c of FORBIDDEN_COMMANDS) if (text.includes(c)) out.push({ file, rule: "forbidden-command", detail: c });
  // attributes: only a small allowlist
  for (const m of text.matchAll(/@\[([^\]]*)\]/g)) {
    const names = m[1].split(",").map((s) => s.trim().replace(/^local\s+|^scoped\s+/, "").split(/\s+/)[0]);
    for (const n of names) {
      if (!["simp", "inline", "reducible", "specialize", "grind", "irreducible", "match_pattern"].includes(n)) {
        out.push({ file, rule: "forbidden-attribute", detail: n });
      }
    }
  }
  if (/\battribute\s*\[/.test(text)) out.push({ file, rule: "forbidden-attribute-command", detail: "attribute [..]" });
  for (const m of text.matchAll(/\bset_option\s+([A-Za-z0-9_.]+)/g)) {
    if (!ALLOWED_SET_OPTIONS.has(m[1])) out.push({ file, rule: "forbidden-set-option", detail: m[1] });
  }
  // imports: exact allowlist, must appear before any other command
  const lines = text.split("\n");
  for (const line of lines) {
    const m = /^\s*import\s+(.+)$/.exec(line);
    if (m) {
      for (const mod of m[1].trim().split(/\s+/)) {
        if (!IMPORT_ALLOW[file].includes(mod)) out.push({ file, rule: "forbidden-import", detail: mod });
      }
    }
  }
  // namespaces: only FactoryPkg (and its children)
  for (const m of text.matchAll(/\bnamespace\s+([A-Za-z0-9_.']+)/g)) {
    if (!(m[1] === "FactoryPkg" || m[1].startsWith("FactoryPkg."))) out.push({ file, rule: "forbidden-namespace", detail: m[1] });
  }
  if (!/\bnamespace\s+FactoryPkg\b/.test(text)) out.push({ file, rule: "missing-namespace", detail: "namespace FactoryPkg" });
  // no declarations with explicit protected prefixes
  if (/\b(def|theorem|lemma|abbrev|instance|structure|inductive|class|example)\s+(Factory|FactoryPrev|FactoryBridge)\b/.test(text)) {
    out.push({ file, rule: "protected-declaration", detail: "declaration into a protected namespace" });
  }
  if (file !== "Proofs.lean" && /\bFactoryPrev\b/.test(text)) {
    out.push({ file, rule: "predecessor-reference", detail: "only Proofs.lean may reference FactoryPrev" });
  }
  return out;
}

export function lintJson(file: string, text: string): LintFinding[] {
  try {
    JSON.parse(text);
    return [];
  } catch (e) {
    return [{ file, rule: "invalid-json", detail: (e as Error).message }];
  }
}
