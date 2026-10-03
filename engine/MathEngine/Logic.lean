import MathEngine.Parser
import MathEngine.Rewrite
import MathEngine.Numeric
import MathEngine.Print
/-!
# The logic world

A fourth world in the engine: formulas of propositional logic, and of first-order logic over finite
sets of numbers. Like the λ and order worlds it has its own syntax and its own parser; formulas are
encoded into `Expr` for the wire (`fn "∧" [a, b]`, `fn "∀" [x, D, body]`, …), and the printer knows
the heads.

- **Propositional formulas** are decided by truth tables: `taut`, `sat` (with a satisfying
  assignment, written as a conjunction of literals), `falsify`, `equiv` (with an assignment that
  tells the two apart), `truthtable`. With at most `maxVars` variables, nothing is out of reach.
- **Normal forms** are rewrites, one law at a time, each a step: implications and biconditionals
  eliminated, negations pushed in (De Morgan, double negation), constants simplified, then `∨`
  distributed over `∧` (CNF) or `∧` over `∨` (DNF). Each pass is a total function, structural or on a
  size measure, so there is no budget; `LogicProofs.lean` proves each pass keeps the meaning.
- **Bounded quantifiers** `∀ n ∈ D, φ` and `∃ n ∈ D, φ` range over a finite set of numbers (`{1, 2, 3}`
  or `1..10`); their atoms are comparisons of expressions (`n^2 ≥ n`, `d ∣ n`) and a few predicates
  (`prime`, `even`, `odd`), evaluated by the pipeline. The answer names the element that decided it.

The grammar (ASCII and words are read as the glyphs: `->`, `<->`, `&&`/`and`, `||`/`or`, `!`/`not`,
`true`, `false`, `forall … in`, `exists … in`, `<=`, `>=`, `!=`):

```
stmt    := 'let' IDENT '=' formula | CMD '(' formula (',' formula)? ')' | formula
CMD     := truthtable | taut | sat | falsify | nnf | cnf | dnf | equiv     -- equiv takes two
formula := ('∀' | '∃') IDENT '∈' dom ',' formula | iff
iff     := imp ('↔' iff)?                         -- right-assoc
imp     := or ('→' imp)?                          -- right-assoc
or      := and ('∨' and)*
and     := not ('∧' not)*
not     := '¬' not | atom
atom    := '⊤' | '⊥' | '(' formula ')' | PRED '(' expr,* ')' | expr CMP expr | IDENT
dom     := expr '..' expr | '{' expr,* '}'
PRED    := prime | even | odd
CMP     := '<' | '≤' | '>' | '≥' | '=' | '≠' | '∣'
```

`expr` is the math grammar (`Parser.lean`); an `IDENT` alone is a propositional variable, or a formula
bound by `let`. A quantifier's body is everything after its comma, so in the middle of a formula a
quantifier goes in brackets. `=>`, `/\`, `\/` and `~` are read too. In a CNF answer, the pass after distributing turns a clause with `p` and `¬p` into `⊤`
(a DNF term with them into `⊥`), and constants are simplified again.
-/
namespace MathEngine
namespace Logic

/-- A quantifier's domain: the integers `lo..hi`, or a list of expressions. -/
inductive Dom where
  | range (lo hi : Expr)
  | list (xs : List Expr)
  deriving Inhabited

inductive Fm where
  | var (x : String)
  | tt
  | ff
  | not (a : Fm)
  | and (a b : Fm)
  | or (a b : Fm)
  | imp (a b : Fm)
  | iff (a b : Fm)
  /-- `l op r` for `op` one of `<`, `≤`, `>`, `≥`, `=`, `≠`, `∣`. -/
  | cmp (op : String) (l r : Expr)
  /-- `prime(n)`, `even(n)`, `odd(n)`. -/
  | pred (p : String) (args : List Expr)
  | all (x : String) (d : Dom) (body : Fm)
  | ex (x : String) (d : Dom) (body : Fm)
  deriving Inhabited

namespace Fm

/-- A formula of propositional logic: variables, constants and connectives only. -/
def isProp : Fm → Bool
  | .var _ | .tt | .ff => true
  | .not a => a.isProp
  | .and a b | .or a b | .imp a b | .iff a b => a.isProp && b.isProp
  | _ => false

/-- The propositional variables, each once, in order of first appearance. -/
def vars : Fm → List String
  | .var x => [x]
  | .not a => a.vars
  | .and a b | .or a b | .imp a b | .iff a b => (a.vars ++ b.vars).eraseDups
  | .all _ _ b | .ex _ _ b => b.vars
  | _ => []

/-- The truth value under an assignment (propositional formulas). -/
def eval (σ : String → Bool) : Fm → Bool
  | .var x => σ x
  | .tt => true
  | .ff => false
  | .not a => !a.eval σ
  | .and a b => a.eval σ && b.eval σ
  | .or a b => a.eval σ || b.eval σ
  | .imp a b => !a.eval σ || b.eval σ
  | .iff a b => a.eval σ == b.eval σ
  | _ => false

def size : Fm → Nat
  | .not a => a.size + 1
  | .and a b | .or a b | .imp a b | .iff a b => a.size + b.size + 1
  | _ => 1

theorem size_pos (f : Fm) : 0 < f.size := by cases f <;> simp [size]

end Fm

/-! ## Encoding for the wire and the printer -/

def Dom.toExpr : Dom → Expr
  | .range a b => .fn "range" [a, b]
  | .list xs => .fn "set" xs

def Fm.toExpr : Fm → Expr
  | .var x => .var x
  | .tt => .fn "⊤" []
  | .ff => .fn "⊥" []
  | .not a => .fn "¬" [a.toExpr]
  | .and a b => .fn "∧" [a.toExpr, b.toExpr]
  | .or a b => .fn "∨" [a.toExpr, b.toExpr]
  | .imp a b => .fn "→" [a.toExpr, b.toExpr]
  | .iff a b => .fn "↔" [a.toExpr, b.toExpr]
  | .cmp op l r => .fn op [l, r]
  | .pred p args => .fn p args
  | .all x d b => .fn "∀" [.var x, d.toExpr, b.toExpr]
  | .ex x d b => .fn "∃" [.var x, d.toExpr, b.toExpr]

def Fm.toText (f : Fm) : String := f.toExpr.toText

/-! ## The parser: glyphs or ASCII, one formula per string -/

/-- Characters that may make up a name: letters (Greek too), digits, `_` and `'`. -/
def identChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || (c.val ≥ 0x370 && c.val ≤ 0x3FF)

/-- Words and ASCII spellings, as the glyphs the parser reads. -/
def wordGlyph : List (String × String) :=
  [("and", "∧"), ("or", "∨"), ("not", "¬"), ("implies", "→"), ("iff", "↔"), ("forall", "∀"), ("exists", "∃"),
   ("in", "∈"), ("true", "⊤"), ("false", "⊥")]

/-- Rewrite ASCII and word spellings into glyphs: `<->` `->` `&&` `/\` `||` `\/` `!` `~` `<=` `>=` `!=`
`==`, and the words `and or not implies iff forall exists in true false`. -/
partial def glyphsGo : List Char → List Char → List Char
    | [], acc => acc.reverse
    | '<' :: '-' :: '>' :: cs, acc => glyphsGo cs ('↔' :: acc)
    | '-' :: '>' :: cs, acc => glyphsGo cs ('→' :: acc)
    | '=' :: '>' :: cs, acc => glyphsGo cs ('→' :: acc)
    | '&' :: '&' :: cs, acc => glyphsGo cs ('∧' :: acc)
    | '/' :: '\\' :: cs, acc => glyphsGo cs ('∧' :: acc)
    | '|' :: '|' :: cs, acc => glyphsGo cs ('∨' :: acc)
    | '\\' :: '/' :: cs, acc => glyphsGo cs ('∨' :: acc)
    | '<' :: '=' :: cs, acc => glyphsGo cs ('≤' :: acc)
    | '>' :: '=' :: cs, acc => glyphsGo cs ('≥' :: acc)
    | '!' :: '=' :: cs, acc => glyphsGo cs ('≠' :: acc)
    | '=' :: '=' :: cs, acc => glyphsGo cs ('=' :: acc)
    | '!' :: cs, acc => glyphsGo cs ('¬' :: acc)
    | '~' :: cs, acc => glyphsGo cs ('¬' :: acc)
    | c :: cs, acc =>
      if identChar c && !(acc.head?.map identChar |>.getD false) then
        let w := (c :: cs).takeWhile identChar
        let rest := (c :: cs).drop w.length
        match wordGlyph.lookup (String.ofList w) with
        | some g => glyphsGo rest (g.toList.reverse ++ acc)
        | none => glyphsGo rest (w.reverse ++ acc)
      else glyphsGo cs (c :: acc)

def glyphs (src : String) : String := String.ofList (glyphsGo src.toList [])

private def trim (s : List Char) : List Char := (s.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace |>.reverse

private def opens (c : Char) : Bool := c == '(' || c == '{' || c == '['
private def closes (c : Char) : Bool := c == ')' || c == '}' || c == ']'

/-- The positions of `c` at bracket depth 0, before any quantifier at depth 0 (a quantifier's body
reaches to the end, so what follows it is its own). -/
def topPositions (s : List Char) (c : Char) : List Nat := go s 0 0 []
where
  go : List Char → Nat → Nat → List Nat → List Nat
    | [], _, _, acc => acc.reverse
    | x :: xs, i, d, acc =>
      if opens x then go xs (i + 1) (d + 1) acc
      else if closes x then go xs (i + 1) (d - 1) acc
      else if d == 0 && (x == '∀' || x == '∃') then acc.reverse
      else if d == 0 && x == c then go xs (i + 1) d (i :: acc)
      else go xs (i + 1) d acc

/-- Is the whole of `s` one bracketed group `( … )`? -/
def wrapped (s : List Char) : Bool :=
  match s.head?, s.getLast? with
  | some '(', some ')' =>
    -- the opening bracket closes only at the end
    (go s.tail 1).isNone
  | _, _ => false
where
  go : List Char → Nat → Option Unit
    | [], _ => none
    | [_], _ => none   -- the last character is the closing bracket
    | x :: xs, d =>
      let d' := if opens x then d + 1 else if closes x then d - 1 else d
      if d' == 0 then some () else go xs d'

/-- Split at top-level commas. -/
def splitCommas (s : List Char) : List (List Char) := go s 0 [] []
where
  go : List Char → Nat → List Char → List (List Char) → List (List Char)
    | [], _, cur, acc => (cur.reverse :: acc).reverse
    | x :: xs, d, cur, acc =>
      if d == 0 && x == ',' then go xs d [] (cur.reverse :: acc)
      else go xs (if opens x then d + 1 else if closes x then d - 1 else d) (x :: cur) acc

def predicates : List String := ["prime", "even", "odd"]

private def mathOf (s : List Char) : Except String Expr :=
  -- `x = true` compares with the name, though the word became `⊤` with the glyphs
  let t := String.ofList (trim s)
  if t == "⊤" then .ok (.var "true") else if t == "⊥" then .ok (.var "false") else
  match parse t with
  | .ok e => .ok e
  | .error e => .error s!"{String.ofList (trim s)}: {e.message}"

/-- A quantifier's domain: `{e, …}` or `lo..hi`. -/
def parseDom (s : List Char) : Except String Dom := do
  let s := trim s
  if s.head? == some '{' && s.getLast? == some '}' then
    let inner := trim ((s.drop 1).dropLast)
    if inner.isEmpty then return .list []
    return .list (← (splitCommas inner).mapM mathOf)
  match (List.range s.length).find? fun i => s[i]? == some '.' && s[i+1]? == some '.' with
  | some i => return .range (← mathOf (s.take i)) (← mathOf (s.drop (i + 2)))
  | none => throw s!"{String.ofList s} is not a domain: write {"{"}1, 2, 3} or 1..10"

/-- Comparison operators, in the order they are looked for. -/
def cmpOps : List Char := ['≤', '≥', '≠', '<', '>', '=', '∣', '|']

/-- An atom: a constant, a comparison, a predicate, or a propositional variable. -/
def parseAtom (s : List Char) : Except String Fm := do
  let s := trim s
  let str := String.ofList s
  if str == "⊤" then return .tt
  if str == "⊥" then return .ff
  -- a comparison: the first comparison operator at depth 0
  for op in cmpOps do
    match topPositions s op with
    | i :: _ => return .cmp (if op == '|' then "∣" else op.toString) (← mathOf (s.take i)) (← mathOf (s.drop (i + 1)))
    | [] => pure ()
  -- a predicate: prime(n), even(n), odd(n)
  let name := s.takeWhile identChar
  let rest := trim (s.drop name.length)
  if predicates.contains (String.ofList name) && wrapped rest then
    return .pred (String.ofList name) (← (splitCommas (trim ((rest.drop 1).dropLast))).mapM mathOf)
  if !s.isEmpty && s.all identChar && !(s.head?.map Char.isDigit |>.getD false) then return .var str
  throw s!"{str} is not a formula"

/-- Where a quantifier's domain ends: the first top-level `,` or `:`. -/
def domainEnd : List Char → Nat → Nat → Option Nat
  | [], _, _ => none
  | c :: cs, i, d =>
    if opens c then domainEnd cs (i + 1) (d + 1)
    else if closes c then domainEnd cs (i + 1) (d - 1)
    else if d == 0 && (c == ',' || c == ':') then some i
    else domainEnd cs (i + 1) d

/-- A formula, lowest precedence first: a quantifier (to the end), `↔` and `→` (to the right), `∨` and
`∧` (to the left), `¬`, brackets, atoms. -/
partial def parseFm (s0 : List Char) : Except String Fm := do
  let s := trim s0
  if s.isEmpty then throw "expected a formula"
  match s.head? with
  | some '∀' | some '∃' =>
    let isAll := s.head? == some '∀'
    let s := trim s.tail
    let x := s.takeWhile identChar
    if x.isEmpty then throw "expected a variable after the quantifier"
    let s := trim (s.drop x.length)
    if s.head? != some '∈' then throw s!"expected ∈ (or in) after ∀ {String.ofList x}"
    let s := s.tail
    match domainEnd s 0 0 with
    | none => throw "expected ',' after the quantifier's domain"
    | some i =>
      let d ← parseDom (s.take i)
      let body ← parseFm (s.drop (i + 1))
      return if isAll then .all (String.ofList x) d body else .ex (String.ofList x) d body
  | _ => pure ()
  match topPositions s '↔' with
  | i :: _ => return .iff (← parseFm (s.take i)) (← parseFm (s.drop (i + 1)))
  | [] => pure ()
  match topPositions s '→' with
  | i :: _ => return .imp (← parseFm (s.take i)) (← parseFm (s.drop (i + 1)))
  | [] => pure ()
  match (topPositions s '∨').getLast? with
  | some i => return .or (← parseFm (s.take i)) (← parseFm (s.drop (i + 1)))
  | none => pure ()
  match (topPositions s '∧').getLast? with
  | some i => return .and (← parseFm (s.take i)) (← parseFm (s.drop (i + 1)))
  | none => pure ()
  if s.head? == some '¬' then return .not (← parseFm s.tail)
  if wrapped s then
    -- a bracketed formula; brackets around arithmetic (`(n+1)^2 > n`) never wrap the whole atom
    return ← parseFm ((s.drop 1).dropLast)
  parseAtom s

def parseFormula (src : String) : Except String Fm := parseFm (glyphs src).toList

/-! ## Commands and statements -/

def commands : List String := ["truthtable", "taut", "sat", "falsify", "equiv", "nnf", "cnf", "dnf"]

/-- A logic cell: `[let name =] command(formula, …)` or `[let name =] formula`. -/
inductive Stmt where
  | cmd (name : Option String) (head : String) (args : List Fm)
  | fm (name : Option String) (f : Fm)

def parseStmt (src : String) : Except String Stmt := do
  let s := trim (glyphs src).toList
  -- `let name = …`: the `=` after a name is the binding's, not a comparison's
  let (name, body) :=
    if s.take 4 == "let ".toList then
      let r := trim (s.drop 4)
      let n := r.takeWhile identChar
      let r := trim (r.drop n.length)
      if !n.isEmpty && r.head? == some '=' then (some (String.ofList n), r.tail) else (none, s)
    else (none, s)
  let body := trim body
  let head := body.takeWhile identChar
  let rest := trim (body.drop head.length)
  if commands.contains (String.ofList head) && wrapped rest then
    let args ← (splitCommas ((rest.drop 1).dropLast)).mapM parseFm
    return .cmd name (String.ofList head) args
  return .fm name (← parseFm body)

/-- Is this a logic cell? A logic command first, or a connective or quantifier written as a glyph (`¬ ∧ ∨ →
↔ ⊤ ⊥ ∀ ∃`) or as `<->`, `->`, `&&`, `||`, or a first word `forall`/`exists`. (`!` and `~` alone do not
make a cell logic; the order world, which also writes `->`, is asked first, and a λ-cell is not logic.) -/
def isLogicSource (src : String) : Bool :=
  let words := ((src.splitOn " ").map (·.trimAscii.copy)).filter (· != "")
  let first := match words with | "let" :: _ :: "=" :: w :: _ => w | w :: _ => w | [] => ""
  let glyph := src.any fun c => c == '¬' || c == '∧' || c == '∨' || c == '→' || c == '↔' || c == '⊤' || c == '⊥' || c == '∀' || c == '∃'
  let ascii := ["<->", "->", "&&", "||"].any (fun t => (src.splitOn t).length > 1)
  (commands.any (fun c => first.startsWith (c ++ "(")) || glyph || ascii || first == "forall" || first == "exists")
    && !src.any (fun c => c == 'λ' || c == '\\')

/-! ## Truth tables -/

/-- Every assignment to `vs`, as rows of truth values: true before false, the first variable slowest. -/
def rows : List String → List (List Bool)
  | [] => [[]]
  | _ :: vs => (rows vs).map (true :: ·) ++ (rows vs).map (false :: ·)

/-- The assignment a row stands for (variables outside `vs` are false). -/
def assignment (vs : List String) (row : List Bool) : String → Bool := fun x =>
  match (vs.zip row).lookup x with | some b => b | none => false

/-- The most variables a truth table is built for (2¹² rows). -/
def maxVars : Nat := 12

/-- The first row of `vs` where `p` holds. -/
def findRow (vs : List String) (p : (String → Bool) → Bool) : Option (List Bool) :=
  (rows vs).find? fun r => p (assignment vs r)

/-- A row as a conjunction of literals: `p ∧ ¬q`. -/
def literals (vs : List String) (row : List Bool) : Fm :=
  match (vs.zip row).map (fun (x, b) => if b then Fm.var x else .not (.var x)) with
  | [] => .tt
  | l :: ls => ls.foldl .and l

def rowText (vs : List String) (row : List Bool) : String :=
  ", ".intercalate ((vs.zip row).map fun (x, b) => s!"{x} = {if b then "true" else "false"}")

/-! ## Normal forms, one law at a time -/

private def st (rule text : String) (path : Path) (before after : Fm) : Step :=
  ⟨rule, text, path, before.toExpr, after.toExpr, none⟩

/-- Eliminate `→` and `↔`, bottom-up. `ctx` rebuilds the whole formula from the subterm at `path`. -/
def arrows (ctx : Fm → Fm) (path : Path) : Fm → Fm × Array Step
  | .not a =>
    let (a', s) := arrows (fun x => ctx (.not x)) (path ++ [0]) a
    (.not a', s)
  | .and a b =>
    let (a', s1) := arrows (fun x => ctx (.and x b)) (path ++ [0]) a
    let (b', s2) := arrows (fun x => ctx (.and a' x)) (path ++ [1]) b
    (.and a' b', s1 ++ s2)
  | .or a b =>
    let (a', s1) := arrows (fun x => ctx (.or x b)) (path ++ [0]) a
    let (b', s2) := arrows (fun x => ctx (.or a' x)) (path ++ [1]) b
    (.or a' b', s1 ++ s2)
  | .imp a b =>
    let (a', s1) := arrows (fun x => ctx (.imp x b)) (path ++ [0]) a
    let (b', s2) := arrows (fun x => ctx (.imp a' x)) (path ++ [1]) b
    let r := Fm.or (.not a') b'
    (r, (s1 ++ s2).push (st "logic.implication" "$a \\to b \\equiv \\lnot a \\lor b$: an implication fails only when its premise holds and its conclusion does not." path (ctx (.imp a' b')) (ctx r)))
  | .iff a b =>
    let (a', s1) := arrows (fun x => ctx (.iff x b)) (path ++ [0]) a
    let (b', s2) := arrows (fun x => ctx (.iff a' x)) (path ++ [1]) b
    let m1 := Fm.and (.imp a' b') (.imp b' a')
    let m2 := Fm.and (.or (.not a') b') (.imp b' a')
    let r := Fm.and (.or (.not a') b') (.or (.not b') a')
    (r, (s1 ++ s2)
      |>.push (st "logic.biconditional" "$a \\leftrightarrow b \\equiv (a \\to b) \\land (b \\to a)$." path (ctx (.iff a' b')) (ctx m1))
      |>.push (st "logic.implication" "$a \\to b \\equiv \\lnot a \\lor b$." (path ++ [0]) (ctx m1) (ctx m2))
      |>.push (st "logic.implication" "$a \\to b \\equiv \\lnot a \\lor b$." (path ++ [1]) (ctx m2) (ctx r)))
  | f => (f, #[])

/-- Push negations in to the variables (for an arrow-free formula). The subterm shown at `path` is
`¬f` when `neg`, else `f`; the result is the negation normal form of what is shown. -/
def nnf (neg : Bool) (ctx : Fm → Fm) (path : Path) : Fm → Fm × Array Step
  | .not a =>
    if neg then
      let (r, s) := nnf false ctx path a
      (r, #[st "logic.double-negation" "$\\lnot\\lnot a \\equiv a$." path (ctx (.not (.not a))) (ctx a)] ++ s)
    else nnf true ctx path a
  | .and a b =>
    if neg then
      let s0 := st "logic.de-morgan" "De Morgan: $\\lnot(a \\land b) \\equiv \\lnot a \\lor \\lnot b$." path (ctx (.not (.and a b))) (ctx (.or (.not a) (.not b)))
      let (a', s1) := nnf true (fun x => ctx (.or x (.not b))) (path ++ [0]) a
      let (b', s2) := nnf true (fun x => ctx (.or a' x)) (path ++ [1]) b
      (.or a' b', #[s0] ++ s1 ++ s2)
    else
      let (a', s1) := nnf false (fun x => ctx (.and x b)) (path ++ [0]) a
      let (b', s2) := nnf false (fun x => ctx (.and a' x)) (path ++ [1]) b
      (.and a' b', s1 ++ s2)
  | .or a b =>
    if neg then
      let s0 := st "logic.de-morgan" "De Morgan: $\\lnot(a \\lor b) \\equiv \\lnot a \\land \\lnot b$." path (ctx (.not (.or a b))) (ctx (.and (.not a) (.not b)))
      let (a', s1) := nnf true (fun x => ctx (.and x (.not b))) (path ++ [0]) a
      let (b', s2) := nnf true (fun x => ctx (.and a' x)) (path ++ [1]) b
      (.and a' b', #[s0] ++ s1 ++ s2)
    else
      let (a', s1) := nnf false (fun x => ctx (.or x b)) (path ++ [0]) a
      let (b', s2) := nnf false (fun x => ctx (.or a' x)) (path ++ [1]) b
      (.or a' b', s1 ++ s2)
  | .tt => if neg then (.ff, #[st "logic.negate-constant" "$\\lnot\\top \\equiv \\bot$." path (ctx (.not .tt)) (ctx .ff)]) else (.tt, #[])
  | .ff => if neg then (.tt, #[st "logic.negate-constant" "$\\lnot\\bot \\equiv \\top$." path (ctx (.not .ff)) (ctx .tt)]) else (.ff, #[])
  | f => (if neg then .not f else f, #[])

/-- Simplify the constants out of a formula, bottom-up: `a ∧ ⊤ = a`, `a ∧ ⊥ = ⊥`, `a ∨ ⊤ = ⊤`, `a ∨ ⊥ = a`. -/
def consts (ctx : Fm → Fm) (path : Path) : Fm → Fm × Array Step
  | .and a b =>
    let (a', s1) := consts (fun x => ctx (.and x b)) (path ++ [0]) a
    let (b', s2) := consts (fun x => ctx (.and a' x)) (path ++ [1]) b
    let step (r : Fm) (law : String) := (r, (s1 ++ s2).push (st "logic.constants" law path (ctx (.and a' b')) (ctx r)))
    match a', b' with
    | .tt, _ => step b' "$\\top \\land a \\equiv a$."
    | _, .tt => step a' "$a \\land \\top \\equiv a$."
    | .ff, _ | _, .ff => step .ff "$a \\land \\bot \\equiv \\bot$."
    | _, _ => (.and a' b', s1 ++ s2)
  | .or a b =>
    let (a', s1) := consts (fun x => ctx (.or x b)) (path ++ [0]) a
    let (b', s2) := consts (fun x => ctx (.or a' x)) (path ++ [1]) b
    let step (r : Fm) (law : String) := (r, (s1 ++ s2).push (st "logic.constants" law path (ctx (.or a' b')) (ctx r)))
    match a', b' with
    | .ff, _ => step b' "$\\bot \\lor a \\equiv a$."
    | _, .ff => step a' "$a \\lor \\bot \\equiv a$."
    | .tt, _ | _, .tt => step .tt "$a \\lor \\top \\equiv \\top$."
    | _, _ => (.or a' b', s1 ++ s2)
  | f => (f, #[])

def outerOp (cnf : Bool) (x y : Fm) : Fm := if cnf then .or x y else .and x y
def innerOp (cnf : Bool) (x y : Fm) : Fm := if cnf then .and x y else .or x y
private def distLaw (cnf : Bool) : String :=
  if cnf then "Distribute: $a \\lor (b \\land c) \\equiv (a \\lor b) \\land (a \\lor c)$."
  else "Distribute: $a \\land (b \\lor c) \\equiv (a \\land b) \\lor (a \\land c)$."

/-- `a ∨ b` (`cnf`) or `a ∧ b` with the right operand `b` a normal form and `a` a clause (a term):
distribute over `b`'s conjuncts (disjuncts). Structural on `b`. -/
def distribR (cnf : Bool) (ctx : Fm → Fm) (path : Path) (a : Fm) : Fm → Fm × Array Step
  | .and b1 b2 =>
    if cnf then
      let s0 := st "logic.distribute" (distLaw cnf) path (ctx (outerOp cnf a (.and b1 b2))) (ctx (innerOp cnf (outerOp cnf a b1) (outerOp cnf a b2)))
      let (l, s1) := distribR cnf (fun x => ctx (innerOp cnf x (outerOp cnf a b2))) (path ++ [0]) a b1
      let (m, s2) := distribR cnf (fun x => ctx (innerOp cnf l x)) (path ++ [1]) a b2
      (innerOp cnf l m, #[s0] ++ s1 ++ s2)
    else (outerOp cnf a (.and b1 b2), #[])
  | .or b1 b2 =>
    if !cnf then
      let s0 := st "logic.distribute" (distLaw cnf) path (ctx (outerOp cnf a (.or b1 b2))) (ctx (innerOp cnf (outerOp cnf a b1) (outerOp cnf a b2)))
      let (l, s1) := distribR cnf (fun x => ctx (innerOp cnf x (outerOp cnf a b2))) (path ++ [0]) a b1
      let (m, s2) := distribR cnf (fun x => ctx (innerOp cnf l x)) (path ++ [1]) a b2
      (innerOp cnf l m, #[s0] ++ s1 ++ s2)
    else (outerOp cnf a (.or b1 b2), #[])
  | b => (outerOp cnf a b, #[])

/-- Distribute `∨` over `∧` (`cnf`) or `∧` over `∨`: the normal form of `a ∨ b` (`a ∧ b`) from normal
forms `a` and `b`, the subterm at `path` being that disjunction (conjunction). Structural on `a`; at
`a`'s clauses (terms), `distribR` takes over. -/
def distrib (cnf : Bool) (ctx : Fm → Fm) (path : Path) : Fm → Fm → Fm × Array Step
  | .and a1 a2, b =>
    if cnf then
      let s0 := st "logic.distribute" (distLaw cnf) path (ctx (outerOp cnf (.and a1 a2) b)) (ctx (innerOp cnf (outerOp cnf a1 b) (outerOp cnf a2 b)))
      let (l, s1) := distrib cnf (fun x => ctx (innerOp cnf x (outerOp cnf a2 b))) (path ++ [0]) a1 b
      let (m, s2) := distrib cnf (fun x => ctx (innerOp cnf l x)) (path ++ [1]) a2 b
      (innerOp cnf l m, #[s0] ++ s1 ++ s2)
    else distribR cnf ctx path (.and a1 a2) b
  | .or a1 a2, b =>
    if !cnf then
      let s0 := st "logic.distribute" (distLaw cnf) path (ctx (outerOp cnf (.or a1 a2) b)) (ctx (innerOp cnf (outerOp cnf a1 b) (outerOp cnf a2 b)))
      let (l, s1) := distrib cnf (fun x => ctx (innerOp cnf x (outerOp cnf a2 b))) (path ++ [0]) a1 b
      let (m, s2) := distrib cnf (fun x => ctx (innerOp cnf l x)) (path ++ [1]) a2 b
      (innerOp cnf l m, #[s0] ++ s1 ++ s2)
    else distribR cnf ctx path (.or a1 a2) b
  | a, b => distribR cnf ctx path a b

/-- CNF (or DNF) of a negation normal form, bottom-up. -/
def normal (cnf : Bool) (ctx : Fm → Fm) (path : Path) : Fm → Fm × Array Step
  | .and a b =>
    let (a', s1) := normal cnf (fun x => ctx (.and x b)) (path ++ [0]) a
    let (b', s2) := normal cnf (fun x => ctx (.and a' x)) (path ++ [1]) b
    if cnf then (.and a' b', s1 ++ s2)
    else let (r, s3) := distrib false ctx path a' b'; (r, s1 ++ s2 ++ s3)
  | .or a b =>
    let (a', s1) := normal cnf (fun x => ctx (.or x b)) (path ++ [0]) a
    let (b', s2) := normal cnf (fun x => ctx (.or a' x)) (path ++ [1]) b
    if cnf then let (r, s3) := distrib true ctx path a' b'; (r, s1 ++ s2 ++ s3)
    else (.or a' b', s1 ++ s2)
  | f => (f, #[])

/-- The variables a term (`cnf = false`: an `∧` of literals) or a clause (`cnf = true`: an `∨` of
them) has as literals: plainly, and negated. -/
def litVars (cnf : Bool) : Fm → List String × List String
  | .var x => ([x], [])
  | .not (.var x) => ([], [x])
  | .and a b => if cnf then ([], []) else ((litVars cnf a).1 ++ (litVars cnf b).1, (litVars cnf a).2 ++ (litVars cnf b).2)
  | .or a b => if cnf then ((litVars cnf a).1 ++ (litVars cnf b).1, (litVars cnf a).2 ++ (litVars cnf b).2) else ([], [])
  | _ => ([], [])

/-- A variable the term or clause has both plainly and negated. -/
def clash (cnf : Bool) (c : Fm) : Option String := (litVars cnf c).1.find? fun x => (litVars cnf c).2.contains x

/-- A term with `p` and `¬p` is `⊥`; a clause with them is `⊤`. -/
def complementLeaf (cnf : Bool) (ctx : Fm → Fm) (path : Path) (c : Fm) : Fm × Array Step :=
  match clash cnf c with
  | some x =>
    let r := if cnf then Fm.tt else Fm.ff
    let law := if cnf then s!"A clause with ${x}$ and $\\lnot {x}$ is true: $p \\lor \\lnot p \\equiv \\top$."
      else s!"A term with ${x}$ and $\\lnot {x}$ is false: $p \\land \\lnot p \\equiv \\bot$."
    (r, #[st "logic.complement" law path (ctx c) (ctx r)])
  | none => (c, #[])

/-- In a CNF, every clause with complementary literals becomes `⊤`; in a DNF, every such term `⊥`. -/
def complement (cnf : Bool) (ctx : Fm → Fm) (path : Path) : Fm → Fm × Array Step
  | .and a b =>
    if cnf then
      let (a', s1) := complement cnf (fun x => ctx (.and x b)) (path ++ [0]) a
      let (b', s2) := complement cnf (fun x => ctx (.and a' x)) (path ++ [1]) b
      (.and a' b', s1 ++ s2)
    else complementLeaf cnf ctx path (.and a b)
  | .or a b =>
    if cnf then complementLeaf cnf ctx path (.or a b)
    else
      let (a', s1) := complement cnf (fun x => ctx (.or x b)) (path ++ [0]) a
      let (b', s2) := complement cnf (fun x => ctx (.or a' x)) (path ++ [1]) b
      (.or a' b', s1 ++ s2)
  | f => complementLeaf cnf ctx path f

/-- What `nnf`, `cnf` and `dnf` produce: the passes in order, every step on the whole formula. -/
def toNormal (target : String) (f : Fm) : Fm × Array Step :=
  let r1 := arrows id [] f
  let r2 := nnf false id [] r1.1
  let r3 := consts id [] r2.1
  if target == "nnf" then (r3.1, r1.2 ++ r2.2 ++ r3.2) else
  let cnf := target == "cnf"
  let r4 := normal cnf id [] r3.1
  let r5 := complement cnf id [] r4.1
  let r6 := consts id [] r5.1
  (r6.1, r1.2 ++ r2.2 ++ r3.2 ++ r4.2 ++ r5.2 ++ r6.2)

/-! ## The shapes the normal forms have (checked on every result) -/

def isLiteral : Fm → Bool
  | .var _ | .tt | .ff | .not (.var _) => true
  | _ => false
def isNNF : Fm → Bool
  | .and a b | .or a b => isNNF a && isNNF b
  | f => isLiteral f
def isClause : Fm → Bool
  | .or a b => isClause a && isClause b
  | f => isLiteral f
def isTerm : Fm → Bool
  | .and a b => isTerm a && isTerm b
  | f => isLiteral f
def isCNF : Fm → Bool
  | .and a b => isCNF a && isCNF b
  | f => isClause f
def isDNF : Fm → Bool
  | .or a b => isDNF a && isDNF b
  | f => isTerm f

def hasShape (target : String) (f : Fm) : Bool :=
  match target with | "nnf" => isNNF f | "cnf" => isCNF f | "dnf" => isDNF f | _ => true

/-! ## First-order formulas over finite sets of numbers -/

/-- The integers of a domain, its expressions evaluated by `num`. -/
def Dom.values (num : Expr → Option Q) : Dom → Except String (List Q)
  | .range lo hi => do
    let some a := num lo | throw s!"{lo.toText} is not a number"
    let some b := num hi | throw s!"{hi.toText} is not a number"
    if !a.isInt || !b.isInt then throw "a range's ends must be integers"
    let (a, b) := (a.val.num, b.val.num)
    if b - a > 10000 then throw "a range of more than 10000 numbers"
    return (List.range (b - a + 1).toNat).map fun k => Q.ofInt (a + Int.ofNat k)
  | .list xs => xs.mapM fun e => match num e with | some q => .ok q | none => .error s!"{e.toText} is not a number"

def isPrime (n : Int) : Bool := n ≥ 2 && (List.range (n.toNat - 2)).all fun k => n % (Int.ofNat k + 2) != 0

/-- The truth of a closed formula, its bound variables given by `env` and its arithmetic evaluated by
`num` (which sees `env`). A propositional variable has no value here. -/
def decide (num : List (String × Q) → Expr → Option Q) (env : List (String × Q)) : Fm → Except String Bool
  | .tt => .ok true
  | .ff => .ok false
  | .var x => .error s!"{x} is a propositional variable, with no value of its own: truthtable, taut and sat decide formulas in variables"
  | .not a => do return !(← decide num env a)
  | .and a b => do return (← decide num env a) && (← decide num env b)
  | .or a b => do return (← decide num env a) || (← decide num env b)
  | .imp a b => do return !(← decide num env a) || (← decide num env b)
  | .iff a b => do return (← decide num env a) == (← decide num env b)
  | .cmp op l r => do
    let some x := num env l | throw s!"{l.toText} is not a number"
    let some y := num env r | throw s!"{r.toText} is not a number"
    match op with
    | "<" => return x.val < y.val
    | "≤" => return x.val ≤ y.val
    | ">" => return x.val > y.val
    | "≥" => return x.val ≥ y.val
    | "=" => return x.val == y.val
    | "≠" => return x.val != y.val
    | "∣" =>
      if !x.isInt || !y.isInt then throw "∣ (divides) is for integers"
      return if x.val.num == 0 then y.val.num == 0 else y.val.num % x.val.num == 0
    | _ => throw s!"unknown comparison {op}"
  | .pred p args => do
    let [e] := args | throw s!"{p} takes one argument"
    let some x := num env e | throw s!"{e.toText} is not a number"
    if !x.isInt then throw s!"{p} is for integers"
    let n := x.val.num
    match p with
    | "prime" => return isPrime n
    | "even" => return n % 2 == 0
    | "odd" => return n % 2 != 0
    | _ => throw s!"unknown predicate {p}"
  | .all x d b => do
    let vs ← d.values (num env)
    for v in vs do
      if !(← decide num ((x, v) :: env) b) then return false
    return true
  | .ex x d b => do
    let vs ← d.values (num env)
    for v in vs do
      if (← decide num ((x, v) :: env) b) then return true
    return false

/-- For a formula whose outermost connective is a quantifier: the element that decided it (the first
counterexample of a `∀` that fails, the first witness of an `∃` that holds). -/
def decidingElement (num : List (String × Q) → Expr → Option Q) : Fm → Except String (Option (String × Q))
  | .all x d b => do
    for v in ← d.values (num []) do
      if !(← decide num [(x, v)] b) then return some (x, v)
    return none
  | .ex x d b => do
    for v in ← d.values (num []) do
      if (← decide num [(x, v)] b) then return some (x, v)
    return none
  | _ => return none

/-- Substitute a number for a bound variable, for showing an instance (`at n = 4: 4^2 ≥ 20`). -/
def instantiate (x : String) (v : Expr) : Fm → Fm
  | .not a => .not (instantiate x v a)
  | .and a b => .and (instantiate x v a) (instantiate x v b)
  | .or a b => .or (instantiate x v a) (instantiate x v b)
  | .imp a b => .imp (instantiate x v a) (instantiate x v b)
  | .iff a b => .iff (instantiate x v a) (instantiate x v b)
  | .cmp op l r => .cmp op (substVar x v l) (substVar x v r)
  | .pred p args => .pred p (args.map (substVar x v))
  | .all y d b => if y == x then .all y d b else .all y d (instantiate x v b)
  | .ex y d b => if y == x then .ex y d b else .ex y d (instantiate x v b)
  | f => f

/-- Replace the names a session has bound to formulas by those formulas. -/
def expand (defs : List (String × Fm)) : Fm → Fm
  | .var x => (defs.lookup x).getD (.var x)
  | .not a => .not (expand defs a)
  | .and a b => .and (expand defs a) (expand defs b)
  | .or a b => .or (expand defs a) (expand defs b)
  | .imp a b => .imp (expand defs a) (expand defs b)
  | .iff a b => .iff (expand defs a) (expand defs b)
  | .all x d b => .all x d (expand defs b)
  | .ex x d b => .ex x d (expand defs b)
  | f => f

/-- Apply `g` to every arithmetic expression of a formula (a session's names put in). -/
def mapExprs (g : Expr → Expr) : Fm → Fm
  | .not a => .not (mapExprs g a)
  | .and a b => .and (mapExprs g a) (mapExprs g b)
  | .or a b => .or (mapExprs g a) (mapExprs g b)
  | .imp a b => .imp (mapExprs g a) (mapExprs g b)
  | .iff a b => .iff (mapExprs g a) (mapExprs g b)
  | .cmp op l r => .cmp op (g l) (g r)
  | .pred p args => .pred p (args.map g)
  | .all x d b => .all x (match d with | .range a c => .range (g a) (g c) | .list xs => .list (xs.map g)) (mapExprs g b)
  | .ex x d b => .ex x (match d with | .range a c => .range (g a) (g c) | .list xs => .list (xs.map g)) (mapExprs g b)
  | f => f

/-- Does a formula mention arithmetic or quantifiers (so it is decided by evaluation, not a table)? -/
def isClosedArith (f : Fm) : Bool := !f.isProp && f.vars.isEmpty

end Logic
end MathEngine
