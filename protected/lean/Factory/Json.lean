/-
  Factory.Json — strict, canonical JSON for the kernel boundary (audited,
  NOT covered by the kernel theorems; see ASSURANCE.md "Codec").

  * No JSON numbers at all: naturals travel as canonical decimal strings
    (no sign, no leading zeros, at most 20 digits). Any number token,
    float, exponent or negative value is rejected.
  * Duplicate object keys are rejected. Objects keep source order; decoders
    demand an exact key set (no extra, none missing).
  * Lone surrogates, raw control characters and trailing data are rejected.
  * Nesting depth and input size are bounded.
  * Encoding is canonical: keys sorted by UTF-16 code units (equal to code
    point order for BMP-only keys, which all protocol keys are), no
    whitespace, escapes identical to ECMAScript JSON.stringify.
-/
namespace Factory.Json

inductive J where
  | null
  | bool (b : Bool)
  | str (s : String)
  | arr (xs : List J)
  | obj (kvs : List (String × J))
  deriving Inhabited, Repr, BEq

abbrev Err := String

/-! ### Parser -/

structure P where
  s   : String
  pos : String.Pos.Raw

abbrev PM := StateT P (Except Err)

def maxDepth : Nat := 64

def peek? : PM (Option Char) := do
  let p ← get
  if p.pos.byteIdx < p.s.utf8ByteSize then return some (p.pos.get p.s) else return none

def advance : PM Unit := modify fun p => { p with pos := p.pos.next p.s }

def fail {α} (m : String) : PM α := do
  let p ← get
  throw s!"json: {m} at byte {p.pos.byteIdx}"

def skipWs : PM Unit := do
  repeat
    match ← peek? with
    | some ' ' | some '\n' | some '\r' | some '\t' => advance
    | _ => break

def expectChar (c : Char) : PM Unit := do
  match ← peek? with
  | some d => if d == c then advance else fail s!"expected '{c}'"
  | none => fail s!"expected '{c}', got end"

def expectLit (lit : String) : PM Unit := do
  for c in lit.toList do expectChar c

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hex4 : PM Nat := do
  let mut v := 0
  for _ in [0:4] do
    match ← peek? with
    | some c => match hexVal c with
      | some h => v := v * 16 + h; advance
      | none => fail "bad \\u escape"
    | none => fail "truncated \\u escape"
  return v

partial def parseStrBody (acc : String) : PM String := do
  match ← peek? with
  | none => fail "unterminated string"
  | some '"' => advance; return acc
  | some '\\' =>
    advance
    match ← peek? with
    | some '"' => advance; parseStrBody (acc.push '"')
    | some '\\' => advance; parseStrBody (acc.push '\\')
    | some '/' => advance; parseStrBody (acc.push '/')
    | some 'b' => advance; parseStrBody (acc.push (Char.ofNat 8))
    | some 'f' => advance; parseStrBody (acc.push (Char.ofNat 12))
    | some 'n' => advance; parseStrBody (acc.push '\n')
    | some 'r' => advance; parseStrBody (acc.push '\r')
    | some 't' => advance; parseStrBody (acc.push '\t')
    | some 'u' =>
      advance
      let u ← hex4
      if 0xD800 ≤ u && u ≤ 0xDBFF then
        expectChar '\\'; expectChar 'u'
        let l ← hex4
        if 0xDC00 ≤ l && l ≤ 0xDFFF then
          let cp := 0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00)
          parseStrBody (acc.push (Char.ofNat cp))
        else fail "lone high surrogate"
      else if 0xDC00 ≤ u && u ≤ 0xDFFF then fail "lone low surrogate"
      else parseStrBody (acc.push (Char.ofNat u))
    | _ => fail "bad escape"
  | some c =>
    if c.toNat < 0x20 then fail "raw control character in string"
    else do advance; parseStrBody (acc.push c)

partial def parseValue (depth : Nat) : PM J := do
  if depth > maxDepth then fail "nesting too deep"
  skipWs
  match ← peek? with
  | none => fail "unexpected end"
  | some 'n' => expectLit "null"; return .null
  | some 't' => expectLit "true"; return .bool true
  | some 'f' => expectLit "false"; return .bool false
  | some '"' => advance; return .str (← parseStrBody "")
  | some '[' =>
    advance; skipWs
    if (← peek?) == some ']' then advance; return .arr []
    let mut xs : Array J := #[]
    repeat
      xs := xs.push (← parseValue (depth + 1))
      skipWs
      match ← peek? with
      | some ',' => advance
      | some ']' => advance; break
      | _ => fail "expected ',' or ']'"
    return .arr xs.toList
  | some '{' =>
    advance; skipWs
    if (← peek?) == some '}' then advance; return .obj []
    let mut kvs : Array (String × J) := #[]
    repeat
      skipWs
      expectChar '"'
      let k ← parseStrBody ""
      if kvs.any (·.1 == k) then fail s!"duplicate key '{k}'"
      skipWs; expectChar ':'
      let v ← parseValue (depth + 1)
      kvs := kvs.push (k, v)
      skipWs
      match ← peek? with
      | some ',' => advance
      | some '}' => advance; break
      | _ => fail "expected ',' or '}'"
    return .obj kvs.toList
  | some c =>
    if c == '-' || ('0' ≤ c && c ≤ '9') then fail "JSON numbers are not permitted (use decimal strings)"
    else fail s!"unexpected character '{c}'"

def maxInputBytes : Nat := 64 * 1024 * 1024

def parse (s : String) : Except Err J := do
  if s.utf8ByteSize > maxInputBytes then throw "json: input too large"
  let (v, p) ← (do let v ← parseValue 0; skipWs; return v).run { s := s, pos := 0 }
  if p.pos.byteIdx < s.utf8ByteSize then throw "json: trailing data"
  return v

/-! ### Canonical encoder -/

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def escapeInto (acc : String) (s : String) : String :=
  s.foldl (fun a c =>
    if c == '"' then a ++ "\\\""
    else if c == '\\' then a ++ "\\\\"
    else if c.toNat == 8 then a ++ "\\b"
    else if c.toNat == 12 then a ++ "\\f"
    else if c == '\n' then a ++ "\\n"
    else if c == '\r' then a ++ "\\r"
    else if c == '\t' then a ++ "\\t"
    else if c.toNat < 0x20 then
      a ++ "\\u00" |>.push (hexDigit (c.toNat / 16)) |>.push (hexDigit (c.toNat % 16))
    else a.push c) acc

def keyLt (a b : String × J) : Bool := decide (a.1 < b.1)

partial def render (acc : String) : J → String
  | .null => acc ++ "null"
  | .bool true => acc ++ "true"
  | .bool false => acc ++ "false"
  | .str s => (escapeInto (acc.push '"') s).push '"'
  | .arr xs =>
    let (a, _) := xs.foldl (fun (a, first) x => (render (if first then a else a.push ',') x, false))
      (acc.push '[', true)
    a.push ']'
  | .obj kvs =>
    let sorted := kvs.toArray.qsort keyLt |>.toList
    let (a, _) := sorted.foldl (fun (a, first) (k, v) =>
      let a := if first then a else a.push ','
      let a := (escapeInto (a.push '"') k).push '"' |>.push ':'
      (render a v, false)) (acc.push '{', true)
    a.push '}'

def J.compress (j : J) : String := render "" j

/-! ### Typed decoding helpers -/

def J.getObj : J → Except Err (List (String × J))
  | .obj kvs => .ok kvs
  | _ => .error "expected object"

def J.getArr : J → Except Err (List J)
  | .arr xs => .ok xs
  | _ => .error "expected array"

def J.getStr : J → Except Err String
  | .str s => .ok s
  | _ => .error "expected string"

def J.getBool : J → Except Err Bool
  | .bool b => .ok b
  | _ => .error "expected boolean"

/-- Exact field set: every declared field present, nothing extra. -/
def fields (j : J) (names : List String) : Except Err (String → J) := do
  let kvs ← j.getObj
  for (k, _) in kvs do
    unless names.contains k do throw s!"unexpected field '{k}'"
  for n in names do
    unless kvs.any (·.1 == n) do throw s!"missing field '{n}'"
  return fun n => (kvs.find? (·.1 == n)).map (·.2) |>.getD .null

def decNat (j : J) : Except Err Nat := do
  let s ← j.getStr
  if s.isEmpty || s.length > 20 then throw s!"noncanonical natural '{s}'"
  unless s.all Char.isDigit do throw s!"noncanonical natural '{s}'"
  if s.length > 1 && s.front == '0' then throw s!"noncanonical natural '{s}'"
  return s.toNat!

def encNat (n : Nat) : J := .str (toString n)

def decList {α} (f : J → Except Err α) (j : J) : Except Err (List α) := do
  (← j.getArr).mapM f

def decOpt {α} (f : J → Except Err α) : J → Except Err (Option α)
  | .null => .ok none
  | j => some <$> f j

def encOpt {α} (f : α → J) : Option α → J
  | none => .null
  | some a => f a

end Factory.Json
