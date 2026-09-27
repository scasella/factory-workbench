// Strict JSON Schema validator for the subset used by the role schemas.
// Unknown schema keywords are rejected (fail closed) rather than ignored.

import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { strictParse, digestOf } from "../protocol/json.ts";
import type { LlmRole } from "./types.ts";

type Schema = Record<string, unknown>;

const KNOWN = new Set([
  "$schema", "title", "description", "type", "enum", "required", "additionalProperties",
  "properties", "items", "maxLength", "minLength", "maxItems", "minItems", "pattern", "oneOf",
]);
const TYPES = new Set(["object", "array", "string", "boolean", "null", "integer"]);

export class SchemaError extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "SchemaError";
  }
}

function typeOf(v: unknown): string {
  if (v === null) return "null";
  if (Array.isArray(v)) return "array";
  if (typeof v === "number") return Number.isSafeInteger(v) ? "integer" : "number";
  return typeof v;
}

/** Returns a list of violations (empty = valid). Throws SchemaError on an unsupported schema. */
export function validate(schema: Schema, value: unknown, path = "$"): string[] {
  for (const k of Object.keys(schema)) if (!KNOWN.has(k)) throw new SchemaError(`unsupported keyword '${k}' at ${path}`);
  const errs: string[] = [];
  if (schema.oneOf !== undefined) {
    const alts = schema.oneOf as Schema[];
    const matches = alts.filter((s) => validate(s, value, path).length === 0).length;
    if (matches !== 1) errs.push(`${path}: matched ${matches} oneOf alternatives (need exactly 1)`);
  }
  if (schema.type !== undefined) {
    const types = Array.isArray(schema.type) ? (schema.type as string[]) : [schema.type as string];
    for (const t of types) if (!TYPES.has(t)) throw new SchemaError(`unsupported type '${t}' at ${path}`);
    if (!types.includes(typeOf(value))) {
      errs.push(`${path}: expected ${types.join("|")}, got ${typeOf(value)}`);
      return errs;
    }
  }
  if (schema.enum !== undefined && !(schema.enum as unknown[]).some((e) => e === value)) {
    errs.push(`${path}: value not in enum`);
  }
  if (typeof value === "string") {
    const len = [...value].length;
    if (typeof schema.maxLength === "number" && len > schema.maxLength) errs.push(`${path}: longer than ${schema.maxLength}`);
    if (typeof schema.minLength === "number" && len < schema.minLength) errs.push(`${path}: shorter than ${schema.minLength}`);
    if (typeof schema.pattern === "string" && !new RegExp(schema.pattern, "u").test(value)) errs.push(`${path}: does not match pattern`);
  }
  if (Array.isArray(value)) {
    if (typeof schema.maxItems === "number" && value.length > schema.maxItems) errs.push(`${path}: more than ${schema.maxItems} items`);
    if (typeof schema.minItems === "number" && value.length < schema.minItems) errs.push(`${path}: fewer than ${schema.minItems} items`);
    if (schema.items !== undefined) value.forEach((x, i) => errs.push(...validate(schema.items as Schema, x, `${path}[${i}]`)));
  }
  if (typeOf(value) === "object") {
    const obj = value as Record<string, unknown>;
    const props = (schema.properties ?? {}) as Record<string, Schema>;
    for (const r of (schema.required ?? []) as string[]) if (!Object.hasOwn(obj, r)) errs.push(`${path}: missing required '${r}'`);
    if (schema.additionalProperties !== undefined && schema.additionalProperties !== false) {
      throw new SchemaError(`only additionalProperties:false is supported at ${path}`);
    }
    for (const k of Object.keys(obj)) {
      if (Object.hasOwn(props, k)) errs.push(...validate(props[k], obj[k], `${path}.${k}`));
      else if (schema.additionalProperties === false) errs.push(`${path}: unexpected field '${k}'`);
    }
  }
  return errs;
}

const SCHEMA_FILES: Record<LlmRole, string> = {
  author: "author.schema.json",
  proof_repair: "author.schema.json",
  reproduce: "review.schema.json",
  refute: "review.schema.json",
  summarize: "summary.schema.json",
};

export function roleSchemaPath(role: LlmRole): string {
  return fileURLToPath(new URL(`./schemas/${SCHEMA_FILES[role]}`, import.meta.url));
}

export function loadSchema(path: string): Schema {
  const v = strictParse(readFileSync(path, "utf8"));
  if (v === null || typeof v !== "object" || Array.isArray(v)) throw new SchemaError(`${path}: schema must be an object`);
  return v as Schema;
}

export function roleSchema(role: LlmRole): { schema: Schema; digest: string } {
  const schema = loadSchema(roleSchemaPath(role));
  return { schema, digest: digestOf(schema) };
}
