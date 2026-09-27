// Strict JSON + canonical encoding shared by every TS component.
//
// Canonical form (must match protected/lean/Factory/Json.lean `render`):
//   * object keys sorted by UTF-16 code units (Array.prototype.sort default);
//   * no insignificant whitespace;
//   * strings escaped exactly as ECMAScript JSON.stringify does;
//   * numbers: only safe integers are representable here; the kernel boundary
//     uses decimal strings exclusively (numbers are rejected by the Lean codec).
// Golden vectors in protected/tests/vectors/canonical.json pin both sides.

import { createHash } from "node:crypto";

export type Json = null | boolean | number | string | Json[] | { [k: string]: Json };

export class JsonError extends Error {
  constructor(msg: string) {
    super(msg);
    this.name = "JsonError";
  }
}

export function canonicalize(v: unknown): string {
  if (v === null) return "null";
  if (v === true) return "true";
  if (v === false) return "false";
  if (typeof v === "string") return JSON.stringify(v);
  if (typeof v === "number") {
    if (!Number.isSafeInteger(v)) throw new JsonError(`non-canonical number ${v}`);
    return String(v);
  }
  if (Array.isArray(v)) return "[" + v.map(canonicalize).join(",") + "]";
  if (typeof v === "object") {
    const keys = Object.keys(v as object).sort();
    const parts: string[] = [];
    for (const k of keys) {
      const x = (v as Record<string, unknown>)[k];
      if (x === undefined) throw new JsonError(`undefined value at key ${k}`);
      parts.push(JSON.stringify(k) + ":" + canonicalize(x));
    }
    return "{" + parts.join(",") + "}";
  }
  throw new JsonError(`unsupported value type ${typeof v}`);
}

export function sha256Hex(data: string | Uint8Array): string {
  return createHash("sha256").update(data).digest("hex");
}

export function digestOf(v: unknown): string {
  return sha256Hex(canonicalize(v));
}

export function isDigest(s: unknown): s is string {
  return typeof s === "string" && /^[0-9a-f]{64}$/.test(s);
}

export interface StrictParseOptions {
  maxBytes?: number;
  maxDepth?: number;
  /** "reject": any number token is an error (kernel boundary). "safe-integers": only safe integers. */
  numbers?: "reject" | "safe-integers";
}

/** Strict JSON parser: rejects duplicate keys, trailing data, lone surrogates,
 *  raw control characters, and (by policy) numbers. */
export function strictParse(text: string, opts: StrictParseOptions = {}): Json {
  const maxBytes = opts.maxBytes ?? 16 * 1024 * 1024;
  const maxDepth = opts.maxDepth ?? 64;
  const numbers = opts.numbers ?? "safe-integers";
  if (Buffer.byteLength(text, "utf8") > maxBytes) throw new JsonError("input too large");
  let i = 0;
  const n = text.length;
  const fail = (m: string): never => {
    throw new JsonError(`json: ${m} at ${i}`);
  };
  const ws = () => {
    while (i < n) {
      const c = text.charCodeAt(i);
      if (c === 0x20 || c === 0x0a || c === 0x0d || c === 0x09) i++;
      else break;
    }
  };
  const str = (): string => {
    // assumes text[i] === '"'
    i++;
    let out = "";
    while (true) {
      if (i >= n) fail("unterminated string");
      const c = text.charCodeAt(i);
      if (c === 0x22) {
        i++;
        return out;
      }
      if (c === 0x5c) {
        i++;
        const e = text[i];
        i++;
        switch (e) {
          case '"': out += '"'; break;
          case "\\": out += "\\"; break;
          case "/": out += "/"; break;
          case "b": out += "\b"; break;
          case "f": out += "\f"; break;
          case "n": out += "\n"; break;
          case "r": out += "\r"; break;
          case "t": out += "\t"; break;
          case "u": {
            const h = text.slice(i, i + 4);
            if (!/^[0-9a-fA-F]{4}$/.test(h)) fail("bad \\u escape");
            i += 4;
            const u = parseInt(h, 16);
            if (u >= 0xd800 && u <= 0xdbff) {
              if (text[i] !== "\\" || text[i + 1] !== "u") fail("lone high surrogate");
              const h2 = text.slice(i + 2, i + 6);
              if (!/^[0-9a-fA-F]{4}$/.test(h2)) fail("bad \\u escape");
              const l = parseInt(h2, 16);
              if (l < 0xdc00 || l > 0xdfff) fail("lone high surrogate");
              i += 6;
              out += String.fromCharCode(u, l);
            } else if (u >= 0xdc00 && u <= 0xdfff) {
              fail("lone low surrogate");
            } else out += String.fromCharCode(u);
            break;
          }
          default:
            fail("bad escape");
        }
        continue;
      }
      if (c < 0x20) fail("raw control character");
      if (c >= 0xd800 && c <= 0xdbff) {
        const d = text.charCodeAt(i + 1);
        if (!(d >= 0xdc00 && d <= 0xdfff)) fail("lone surrogate");
        out += text[i] + text[i + 1];
        i += 2;
        continue;
      }
      if (c >= 0xdc00 && c <= 0xdfff) fail("lone surrogate");
      out += text[i];
      i++;
    }
  };
  const value = (depth: number): Json => {
    if (depth > maxDepth) fail("nesting too deep");
    ws();
    if (i >= n) fail("unexpected end");
    const c = text[i];
    if (c === "{") {
      i++;
      const obj: Record<string, Json> = Object.create(null);
      const seen = new Set<string>();
      ws();
      if (text[i] === "}") {
        i++;
        return Object.assign({}, obj);
      }
      while (true) {
        ws();
        if (text[i] !== '"') fail("expected key");
        const k = str();
        if (seen.has(k)) fail(`duplicate key '${k}'`);
        seen.add(k);
        ws();
        if (text[i] !== ":") fail("expected ':'");
        i++;
        obj[k] = value(depth + 1);
        ws();
        if (text[i] === ",") { i++; continue; }
        if (text[i] === "}") { i++; break; }
        fail("expected ',' or '}'");
      }
      const plain: Record<string, Json> = {};
      for (const k of Object.keys(obj)) {
        Object.defineProperty(plain, k, { value: obj[k], enumerable: true, writable: true, configurable: true });
      }
      return plain;
    }
    if (c === "[") {
      i++;
      const arr: Json[] = [];
      ws();
      if (text[i] === "]") { i++; return arr; }
      while (true) {
        arr.push(value(depth + 1));
        ws();
        if (text[i] === ",") { i++; continue; }
        if (text[i] === "]") { i++; break; }
        fail("expected ',' or ']'");
      }
      return arr;
    }
    if (c === '"') return str();
    if (text.startsWith("true", i)) { i += 4; return true; }
    if (text.startsWith("false", i)) { i += 5; return false; }
    if (text.startsWith("null", i)) { i += 4; return null; }
    if (c === "-" || (c >= "0" && c <= "9")) {
      if (numbers === "reject") fail("JSON numbers are not permitted (use decimal strings)");
      const m = /^-?(0|[1-9][0-9]*)/.exec(text.slice(i, i + 32));
      if (!m) fail("bad number");
      const after = text[i + m![0].length];
      if (after === "." || after === "e" || after === "E") fail("non-integer number");
      const v = Number(m![0]);
      if (!Number.isSafeInteger(v)) fail("unsafe integer");
      i += m![0].length;
      return v;
    }
    return fail(`unexpected character '${c}'`);
  };
  const v = value(0);
  ws();
  if (i < n) fail("trailing data");
  return v;
}

/** Exact field-set check for decoded objects. */
export function exactFields(o: unknown, fields: readonly string[], what = "object"): Record<string, Json> {
  if (o === null || typeof o !== "object" || Array.isArray(o)) throw new JsonError(`${what}: expected object`);
  const keys = Object.keys(o);
  for (const k of keys) if (!fields.includes(k)) throw new JsonError(`${what}: unexpected field '${k}'`);
  for (const f of fields) if (!keys.includes(f)) throw new JsonError(`${what}: missing field '${f}'`);
  return o as Record<string, Json>;
}

/** Canonical decimal natural (kernel encoding). */
export function nat(n: number | bigint): string {
  if (typeof n === "number" && (!Number.isSafeInteger(n) || n < 0)) throw new JsonError(`bad natural ${n}`);
  if (typeof n === "bigint" && n < 0n) throw new JsonError(`bad natural ${n}`);
  return n.toString();
}

export function parseNat(s: string): number {
  if (!/^(0|[1-9][0-9]{0,19})$/.test(s)) throw new JsonError(`noncanonical natural '${s}'`);
  const v = Number(s);
  if (!Number.isSafeInteger(v)) throw new JsonError(`natural exceeds safe integer range '${s}'`);
  return v;
}
