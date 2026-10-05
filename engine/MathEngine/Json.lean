/-!
# Minimal JSON

Hand-rolled on purpose: `Lean.Json` lives in `libLean.a` (118 MB in the wasm32 toolchain)
and drags the compiler's initializer chain into the wasm module. This is ~120 lines,
depends only on `Init`, and is a nice small interpreter exercise for the book.
-/
namespace MathEngine

inductive Json where
  | null | bool (b : Bool) | num (s : String) | str (s : String)
  | arr (xs : Array Json) | obj (kvs : Array (String × Json))
  deriving Repr, Inhabited

namespace Json

def get? (j : Json) (k : String) : Option Json :=
  match j with | .obj kvs => (kvs.find? (·.1 == k)).map (·.2) | _ => none
def getStr? (j : Json) (k : String) : Option String :=
  match j.get? k with | some (.str s) => some s | _ => none
def getBool (j : Json) (k : String) (d := false) : Bool :=
  match j.get? k with | some (.bool b) => b | _ => d

/-- `s` appended to `acc` as the body of a JSON string: the quote, the backslash and the control
characters escaped (the other control characters as `\u` and four hex digits, since JSON allows
nothing shorter). -/
private def pushEscaped (acc : String) (s : String) : String :=
  s.foldl (fun acc c => match c with
    | '"' => acc ++ "\\\"" | '\\' => acc ++ "\\\\" | '\n' => acc ++ "\\n" | '\r' => acc ++ "\\r" | '\t' => acc ++ "\\t"
    | c => if c.val < 32 then acc ++ "\\u00" ++ (if c.val < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 c.val.toNat) else acc.push c) acc

/-- The text of `j`, written into one buffer: a value's children are written in place after it,
not rendered on their own and copied in, so a value `d` deep renders in time linear in its text,
not `d` times it (the term of a reply is a `Json` as deep as the term). The buffer is passed along
and never shared, so each `++` and `push` extends it in place. -/
partial def render (j : Json) : String := go j ""
where
  go : Json → String → String
  | .null, acc => acc ++ "null"
  | .bool b, acc => acc ++ toString b
  | .num s, acc => acc ++ s
  | .str s, acc => (pushEscaped (acc.push '"') s).push '"'
  | .arr xs, acc => Id.run do
    let mut acc := acc.push '['
    for h : i in [:xs.size] do
      if i > 0 then acc := acc.push ','
      acc := go xs[i] acc
    return acc.push ']'
  | .obj kvs, acc => Id.run do
    let mut acc := acc.push '{'
    for h : i in [:kvs.size] do
      if i > 0 then acc := acc.push ','
      acc := go kvs[i].2 ((pushEscaped (acc.push '"') kvs[i].1).push '"' |>.push ':')
    return acc.push '}'

-- --- parser -------------------------------------------------------------
structure P where
  s : String
  i : String.Pos.Raw := {}

abbrev PM := StateT P (Except String)

private def peek : PM (Option Char) := do let p ← get; pure (if p.i.atEnd p.s then none else some (p.i.get p.s))
private def adv : PM Unit := modify fun p => { p with i := p.i.next p.s }
private def ws : PM Unit := do
  repeat
    match ← peek with
    | some c => if c.isWhitespace then adv else break
    | none => break
private def expectC (c : Char) : PM Unit := do
  match ← peek with
  | some d => if d == c then adv else throw s!"expected '{c}' got '{d}'"
  | none => throw s!"expected '{c}' got end of input"
private def lit (w : String) (v : Json) : PM Json := do
  for c in w.toList do expectC c
  pure v

/-- The four hex digits of a `\u` escape. -/
private def hex4 : PM Nat := do
  let mut code := 0
  for _ in [0:4] do
    match ← peek with
    | some h =>
      let d := if h.isDigit then h.toNat - '0'.toNat else if 'a' ≤ h.toLower && h.toLower ≤ 'f' then h.toLower.toNat - 'a'.toNat + 10 else 16
      if d == 16 then throw "bad \\u escape"
      adv; code := code * 16 + d
    | none => throw "bad \\u escape"
  pure code

private partial def strLit : PM String := do
  expectC '"'
  let rec go (acc : String) : PM String := do
    match ← peek with
    | none => throw "unterminated string"
    | some '"' => adv; pure acc
    | some '\\' =>
      adv
      match ← peek with
      | some 'n' => adv; go (acc.push '\n')
      | some 't' => adv; go (acc.push '\t')
      | some 'r' => adv; go (acc.push '\r')
      | some 'b' => adv; go (acc.push '\x08')
      | some 'f' => adv; go (acc.push '\x0c')
      | some 'u' =>
        adv
        let code ← hex4
        -- a character beyond the BMP comes as a surrogate pair, `\uD83D\uDE00`
        if 0xD800 ≤ code && code < 0xDC00 && (← peek) == some '\\' then
          adv; expectC 'u'
          let lo ← hex4
          if 0xDC00 ≤ lo && lo < 0xE000 then go (acc.push (Char.ofNat (0x10000 + (code - 0xD800) * 0x400 + (lo - 0xDC00))))
          else throw "bad surrogate pair"
        else go (acc.push (Char.ofNat code))
      | some c => adv; go (acc.push c)
      | none => throw "bad escape"
    | some c => adv; go (acc.push c)
  go ""

private partial def number : PM Json := do
  let rec go (acc : String) : PM String := do
    match ← peek with
    | some c => if c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' then adv; go (acc.push c) else pure acc
    | none => pure acc
  pure (.num (← go ""))

partial def value : PM Json := do
  ws
  match ← peek with
  | none => throw "unexpected end of input"
  | some '{' =>
    adv; ws
    let mut kvs : Array (String × Json) := #[]
    if (← peek) == some '}' then adv; pure (.obj kvs) else
    repeat
      ws; let k ← strLit; ws; expectC ':'; let v ← value; kvs := kvs.push (k, v); ws
      match ← peek with
      | some ',' => adv
      | some '}' => adv; break
      | _ => throw "expected ',' or '}'"
    pure (.obj kvs)
  | some '[' =>
    adv; ws
    let mut xs : Array Json := #[]
    if (← peek) == some ']' then adv; pure (.arr xs) else
    repeat
      xs := xs.push (← value); ws
      match ← peek with
      | some ',' => adv
      | some ']' => adv; break
      | _ => throw "expected ',' or ']'"
    pure (.arr xs)
  | some '"' => .str <$> strLit
  | some 't' => lit "true" (.bool true)
  | some 'f' => lit "false" (.bool false)
  | some 'n' => lit "null" .null
  | some _ => number

def parse (s : String) : Except String Json := (value.run' { s }).mapError (s!"JSON: {·}")

end Json
end MathEngine
