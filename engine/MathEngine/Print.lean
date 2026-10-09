import MathEngine.Expr
import MathEngine.IntRoot
/-!
# Printer

Recovers human notation from the minimal AST, mirroring `printer.ts` line for line:

```
add [a, mul [-1, b]]   →  a - b
mul [a, pow b (-1)]    →  a / b     (LaTeX: \frac{a}{b})
mul [-1, a]            →  -a
pow a (1/2)            →  sqrt(a)
fn exp [a]             →  exp(a)    (LaTeX: e^{a})
```

Every printed subterm knows its `Path`; with `paths := true` the LaTeX output wraps each
subterm in `\htmlData{path=...}{...}`, which KaTeX renders as `<span data-path="0.1">`. That is
how the notebook turns a click into a `Path` for `engine.explain`.

The printer carries a subterm's path reversed, innermost index first: going down is then a cons
rather than a copy of the path so far, which on a deep term cost its depth at every node. A label
spells the path out, so it is as long as the subterm is deep; the subterms of a term nested deeper
than `pathLabelDepth` are not labelled, so a pathological input (ten thousand `-` signs) renders in
time and space linear in it. The notebook already finds a subterm by its nearest labelled
ancestor.

The text is written into one buffer, passed down and never shared, so every `++` extends it in
place: a subterm is written after what precedes it, not rendered on its own and copied into its
parent, which on a term `d` deep copied each character `d` times (`sin(sin(…))` twenty thousand deep
spent seconds in it). A `Target` therefore gives the pieces of each notation (`\frac{`, `}{`, `}`)
rather than a function of the finished parts. Parentheses are the one piece a printer cannot write
until it knows how tightly the subterm binds, so each case of `printRaw` decides its precedence
before it writes anything, and opens them first.
-/
namespace MathEngine
open Expr

/-- What differs between the text and LaTeX outputs: the pieces of each notation, written around
the parts as they are printed. -/
structure Target where
  /-- Open, and close, a subterm's label with its path, given innermost index first. -/
  wrapOpen : Path → String → String
  wrapClose : Path → String → String
  num : Q → String
  var : String → String
  /-- `\frac{n}{d}`, or `n/d`: before the numerator, between the two, after the denominator. -/
  fracOpen : String
  fracMid : String
  fracClose : String
  /-- `{b}^{e}`, or `b^e`. -/
  powOpen : String
  powMid : String
  powClose : String
  /-- `\sqrt{a}`, or `sqrt(a)`. -/
  sqrtOpen : String
  sqrtClose : String
  /-- A call's head and opening bracket, by its name; the closing bracket; between two arguments. -/
  fnOpen : String → String
  fnClose : String
  argSep : String
  /-- A matrix: its brackets, and what separates its rows and the entries of a row. -/
  matOpen : String
  rowSep : String
  colSep : String
  matClose : String
  times : String
  /-- Parentheses. -/
  lpar : String
  rpar : String
  /-- Context precedence for a denominator: text needs parens around products (`a/(b*c)`); `\frac` does not. -/
  denomPrec : Nat

-- precedence levels: what the *context* demands vs. what the term *provides* (reducible, so a
-- proof can see `P_ATOM < ctx` and `4 < ctx` as one proposition)
abbrev P_ADD : Nat := 1
abbrev P_MUL : Nat := 2
abbrev P_LAM : Nat := 1
abbrev P_APP : Nat := 2
abbrev P_NEG : Nat := 2
abbrev P_POW : Nat := 3
abbrev P_ATOM : Nat := 4

def textTarget : Target where
  wrapOpen _ acc := acc
  wrapClose _ acc := acc
  num q := q.toText
  var n := n
  fracOpen := ""
  fracMid := "/"
  fracClose := ""
  powOpen := ""
  powMid := "^"
  powClose := ""
  sqrtOpen := "sqrt("
  sqrtClose := ")"
  fnOpen n := n ++ "("
  fnClose := ")"
  argSep := ", "
  matOpen := "["
  rowSep := "; "
  colSep := ", "
  matClose := "]"
  times := "*"
  lpar := "("
  rpar := ")"
  denomPrec := P_POW

private def greek : List (String × String) :=
  [("π", "\\pi"), ("alpha", "\\alpha"), ("beta", "\\beta"), ("theta", "\\theta"), ("lambda", "\\lambda"),
   ("α", "\\alpha"), ("β", "\\beta"), ("γ", "\\gamma"), ("δ", "\\delta"), ("ε", "\\varepsilon"), ("θ", "\\theta"),
   ("λ", "\\lambda"), ("μ", "\\mu"), ("σ", "\\sigma"), ("τ", "\\tau"), ("φ", "\\varphi"), ("ψ", "\\psi"), ("ω", "\\omega"),
   ("ζ", "\\zeta"), ("η", "\\eta"), ("ι", "\\iota"), ("κ", "\\kappa"), ("ν", "\\nu"), ("ξ", "\\xi"), ("ρ", "\\rho"), ("χ", "\\chi"),
   ("Γ", "\\Gamma"), ("Δ", "\\Delta"), ("Θ", "\\Theta"), ("Λ", "\\Lambda"), ("Σ", "\\Sigma"), ("Φ", "\\Phi"), ("Ω", "\\Omega")]
private def pathStr (p : Path) : String := if p.isEmpty then "root" else ".".intercalate (p.map toString)

/-- How deep a subterm may sit and still be labelled with its path. -/
def pathLabelDepth : Nat := 64

/-- Whether a subterm at `p` (reversed, innermost index first) is labelled: `drop` tests the
path's length in at most `pathLabelDepth` steps. -/
private def labelled (paths : Bool) (p : Path) : Bool := paths && (p.drop pathLabelDepth).isEmpty

def latexTarget (paths : Bool) : Target where
  wrapOpen p acc := if labelled paths p then acc ++ "\\htmlData{path=" ++ pathStr p.reverse ++ "}{" else acc
  wrapClose p acc := if labelled paths p then acc.push '}' else acc
  num q := q.toLatex
  var n := match greek.lookup n with
    | some g => g
    | none =>
      -- a Greek letter and digits, as type variables are named (`τ1`): the digits a subscript
      let cs := n.toList
      let hd := String.ofList (cs.takeWhile (!·.isDigit))
      let ds := String.ofList (cs.dropWhile (!·.isDigit))
      match greek.lookup hd with
      | some g => if !ds.isEmpty && ds.all Char.isDigit then g ++ "_{" ++ ds ++ "}" else s!"\\mathit\{{n}}"
      | none =>
      -- a subsets-poset element is named by its set literal: braces are LaTeX grouping, so escape them
      if n.startsWith "{" then (if n == "{}" then "\\varnothing" else "\\{" ++ (n.drop 1).dropRight 1 ++ "\\}")
      else if n.length > 1 then s!"\\mathit\{{n}}" else n
  fracOpen := "\\frac{"
  fracMid := "}{"
  fracClose := "}"
  powOpen := "{"
  powMid := "}^{"
  powClose := "}"
  sqrtOpen := "\\sqrt{"
  sqrtClose := "}"
  fnOpen n :=
    (if ["sin", "cos", "tan", "arcsin", "arccos", "arctan", "exp", "ln", "log", "arg"].contains n then "\\" ++ n else "\\operatorname{" ++ n ++ "}")
      ++ "\\left("
  fnClose := "\\right)"
  argSep := ", "
  matOpen := "\\begin{bmatrix}"
  rowSep := " \\\\ "
  colSep := " & "
  matClose := "\\end{bmatrix}"
  times := " \\cdot "
  lpar := "\\left("
  rpar := "\\right)"
  denomPrec := P_MUL

/-- `acc` with `T`'s opening parenthesis when `b`, and with its closing one: a subterm's, when it
binds looser than its context. -/
@[inline] def Target.openIf (T : Target) (b : Bool) (acc : String) : String := if b then acc ++ T.lpar else acc
@[inline] def Target.closeIf (T : Target) (b : Bool) (acc : String) : String := if b then acc ++ T.rpar else acc

/-- A leaf's text `s` after `acc`, labelled with its path `p`. -/
@[inline] def Target.leaf (T : Target) (p : Path) (s : String) (acc : String) : String :=
  T.wrapClose p (T.wrapOpen p acc ++ s)

/-- Split a term into (coefficient, rest); `rest` keeps the original child paths. `restPathOffset`
is the child index of `rest` inside the term, or `none` when the whole term is the rest. -/
private def enum (l : List α) : List (Nat × α) := (List.range l.length).zip l

def splitCoeff : Expr → Q × Option Expr × Option Nat
  | .num q => (q, none, none)
  | .mul (.num q :: rest@(_ :: _)) => (q, some (match rest with | [r] => r | rs => .mul rs), some 1)
  | e => (Q.one, some e, none)

/-- `a^(p/q)` for an integer `a ≥ 2` and `0 < p/q` not an integer, the way a textbook writes it:
the `q`-th-power part of `a` and the integer part of `p/q` come out as a coefficient (`2^(3/2)` is
`2√2`, `12^(1/2)` is `2√3`). Display only — the term is unchanged, and the ordering the rules
decrease cannot turn one power into a product, so this is the printer's job — except for a base
that is itself a perfect power (`4^(1/2)`, `8^(1/2)`): `simp.power` and `simp.radical` reduce those in
a step of their own, so they print as they are, `√4`, `√8`, and that step shows. -/
def radicalParts (a q : Q) : Option (Nat × String) :=
  if !(a.isInt && a.val.num ≥ 2 && !q.isInt && !q.isNeg && !q.isZero) then none else
  let n := a.val.num.toNat
  if (perfectPower n).isSome then none else
  let p := q.val.num.toNat
  let d := q.val.den
  let i := p / d
  let f := p % d
  -- the coefficient is at most `n^(i+1)`; past 65536 bits (`10^(10^9 + 1/2)`) the power prints as it
  -- is, and an `m` of 1 is not raised to `p`, which is as long as the exponent's numerator
  -- (`10^1.6020599913279623` has `p = 16020599913279623`, and Lean's runtime stops on such a `Nat.pow`)
  if (i + 1) * (Nat.log2 n + 1) > 65536 then none else
  let (m, s) := qthPowerPart n d
  let coef := (if m == 1 then 1 else m ^ p) * s ^ i
  let inner := if f == 1 then toString s else s!"{s}^\{{f}}"
  let rad := if s == 1 then "" else if d == 2 then s!"\\sqrt\{{inner}}" else s!"\\sqrt[{d}]\{{inner}}"
  some (coef, rad)

private def radicalLatex (b x : Expr) : Option (String × Nat) :=
  match b, x with
  | .num a, .num q =>
    (radicalParts a q).map fun (coef, rad) =>
      if rad.isEmpty then (toString coef, P_ATOM)
      else if coef == 1 then (rad, P_ATOM) else (s!"{coef}{rad}", P_MUL)
  | _, _ => none

/-- `c · a^(p/q)` with a positive coefficient folds into the displayed coefficient: `5√12` is
`10√3` and `½ · 2√2` is `√2`. -/
private def mulRadicalLatex (numStr : Q → String) : List Expr → Option (String × Nat)
  | [.num c, .pow (.num a) (.num q)] =>
    if !c.isNeg && !c.isZero then
      (radicalParts a q).map fun (coef, rad) =>
        let k := c * Q.ofInt coef
        if rad.isEmpty then (numStr k, P_ATOM)
        else if k.isOne then (rad, P_ATOM) else (s!"{numStr k}{rad}", P_MUL)
    else none
  | _ => none

/-- The logic world's connectives, and how tightly each binds (quantifiers reach as far right as they can). -/
def logicLevel : String → Nat
  | "∀" | "∃" => 0 | "↔" => 1 | "→" => 2 | "∨" => 3 | "∧" => 4 | "¬" => 5 | _ => 6
def isLogicHead (h : String) : Bool := ["∀", "∃", "↔", "→", "∨", "∧", "¬"].contains h

/-- A logic connective's operand is bracketed when it is a connective binding looser than `lvl`. -/
private def logicGroups (c : Expr) (lvl : Nat) : Bool :=
  match c with
  | .fn h _ => isLogicHead h && logicLevel h < lvl
  | _ => false

/-- Whether the `i`-th factor of a product has a part in the numerator, and in the denominator: a
negative exponent goes below the line, and a leading rational coefficient `p/d` puts `p` above
and `d` below (`x/(2π)`, as a hand derivation writes it, not `½·x/π`). -/
def factorInNumer (f : Expr) (i : Nat) : Bool :=
  match f with
  | .num q =>
    if i == 0 then
      let a := q.abs
      -- an integer (a `1` stays visible: the identity step removes it) or an approximate decimal prints as is
      if a.isInt || q.approx then !(q.isNeg && a.isOne) else !(Q.ofInt a.val.num).isOne
    else true
  | .pow _ (.num q) => !q.isNeg
  | _ => true

def factorInDenom (f : Expr) (i : Nat) : Bool :=
  match f with
  | .num q => i == 0 && !(q.abs.isInt || q.approx)
  | .pow _ (.num q) => q.isNeg
  | _ => false

/-- Whether a product's first factor is a negative numeral, printed as a unary minus. -/
def leadingNeg : List Expr → Bool
  | .num q :: _ => q.isNeg
  | _ => false

/-- How many factors from the `i`-th satisfy `p`. -/
def countFactors (p : Expr → Nat → Bool) : List Expr → Nat → Nat
  | [], _ => 0
  | f :: rest, i => (if p f i then 1 else 0) + countFactors p rest (i + 1)

/-- The printer's termination goals: a subterm, or a member of a subterm's list, weighs less. -/
local macro "print_decreasing" : tactic => `(tactic| (
  simp_wf
  (try have := Expr.size_le_sizeList (by assumption))
  (try have := Expr.sizeList_le_sizeRows (by assumption))
  (try simp only [Expr.size, Expr.sizeList, Expr.sizeRows] at *)
  (try omega)))

/-! The printer is structural in all but name: every call prints a subterm, or a product rebuilt
from a subterm's factors with a new coefficient, which weighs no more than the subterm. The measure
counts nodes (`Expr.size`, a numeral weighing 1 whatever its value), times eight, so each function in
the block sits at its own offset below the one that calls it on the same term. Every function takes
the buffer written so far and returns it extended. -/
set_option maxHeartbeats 4000000 in
mutual
  /-- `e` at `path` after `acc`, in a context demanding precedence `ctx`: labelled with its path,
  and in parentheses when it binds looser than `ctx`. -/
  def print (e : Expr) (path : Path) (T : Target) (ctx : Nat) (acc : String) : String :=
    T.wrapClose path (printRaw e path T ctx (T.wrapOpen path acc))
  termination_by 8 * e.size + 4
  decreasing_by all_goals print_decreasing

  /-- `e` without its label. Each case knows how tightly it binds before it writes anything, and
  opens the parentheses its context needs first. -/
  def printRaw (e : Expr) (path : Path) (T : Target) (ctx : Nat) (acc : String) : String :=
    match e with
    -- in text an exact non-integer numeral prints as a division, `4/9`, so it binds like one: the base
    -- of a power is `(4/9)^(3/2)`, not `4/9^(3/2)`, which reads back as 4/27 (`\frac` groups itself)
    | .num q =>
      let prec := if q.isNeg then P_NEG else if q.isSci || (T.times == "*" && !q.isInt && !q.approx) then P_MUL else P_ATOM
      T.closeIf (prec < ctx) (T.openIf (prec < ctx) acc ++ T.num q)
    | .var x => T.closeIf (P_ATOM < ctx) (T.openIf (P_ATOM < ctx) acc ++ T.var x)
    | .matrix rows =>
      let w := (rows.head?.map List.length).getD 0
      let acc := T.openIf (P_ATOM < ctx) acc ++ T.matOpen
      let acc := (enum rows.attach).foldl (init := acc) fun acc (r, ⟨row, _⟩) =>
        (enum row.attach).foldl (init := if r == 0 then acc else acc ++ T.rowSep) fun acc (j, ⟨c, _⟩) =>
          print c ((r * w + j) :: path) T P_ADD (if j == 0 then acc else acc ++ T.colSep)
      T.closeIf (P_ATOM < ctx) (acc ++ T.matClose)
    | .fn name args =>
      -- the heads that print their children at a precedence of their own come first
      match name, args with
      -- the λ-calculus world: λx. body binds as far right as possible; application is juxtaposition
      | "λ", [xv, body] =>
        let acc := T.openIf (P_LAM < ctx) acc ++ (if T.times != "*" then "\\lambda " else "λ")
        let acc := print xv (0 :: path) T P_ADD acc ++ (if T.times != "*" then ".\\, " else ". ")
        T.closeIf (P_LAM < ctx) (print body (1 :: path) T P_LAM acc)
      | "λ:", [xv, ty, body] =>
        let acc := T.openIf (P_LAM < ctx) acc ++ (if T.times != "*" then "\\lambda " else "λ")
        let acc := print xv (0 :: path) T P_ADD acc ++ (if T.times != "*" then "{:}" else ":")
        let arrow := match ty with | .fn "→" _ => true | _ => false
        let acc := T.closeIf arrow (print ty (1 :: path) T P_ADD (T.openIf arrow acc)) ++ (if T.times != "*" then ".\\, " else ". ")
        T.closeIf (P_LAM < ctx) (print body (2 :: path) T P_LAM acc)
      | "λ.", [body] =>
        let acc := T.openIf (P_LAM < ctx) acc ++ (if T.times != "*" then "\\lambda.\\, " else "λ. ")
        T.closeIf (P_LAM < ctx) (print body (0 :: path) T P_LAM acc)
      | "@", [f, a] =>
        let acc := print f (0 :: path) T P_APP (T.openIf (P_APP < ctx) acc) ++ (if T.times != "*" then "\\ " else " ")
        T.closeIf (P_APP < ctx) (print a (1 :: path) T (P_APP + 1) acc)
      -- Mathematica's Part: m[[2, 1;;3]], and the specs it takes
      | "part", m :: specs =>
        let acc := print m (0 :: path) T P_ATOM (T.openIf (P_ATOM < ctx) acc) ++ (if T.times != "*" then "\\llbracket " else "[[")
        T.closeIf (P_ATOM < ctx) (printArgs specs 1 path T "" acc ++ (if T.times != "*" then "\\rrbracket" else "]]"))
      -- MATLAB's entrywise operators. Lower than a product as a whole, so it is grouped wherever a
      -- factor or a left operand would otherwise take it in: `x*(a ./ b)`, `(a ./ b) ./ c`
      | "ediv", [a, b] | "emul", [a, b] =>
        let op := if T.times != "*" then (if name == "ediv" then "\\oslash" else "\\odot") else (if name == "ediv" then "./" else ".*")
        let acc := print a (0 :: path) T P_MUL (T.openIf (P_ADD < ctx) acc) ++ " " ++ op ++ " "
        T.closeIf (P_ADD < ctx) (print b (1 :: path) T P_POW acc)
      -- the logic world: connectives by their own precedence (↔ < → < ∨ < ∧ < ¬), quantifiers reach right
      | "¬", [a] =>
        let acc := T.openIf (P_ATOM < ctx) acc ++ (if T.times != "*" then "\\lnot " else "¬")
        T.closeIf (P_ATOM < ctx) (logicOperand a 0 path T 5 acc)
      | "∧", [a, b] | "∨", [a, b] =>
        let lvl := logicLevel name
        let op := if T.times != "*" then (if name == "∧" then " \\land " else " \\lor ") else " " ++ name ++ " "
        let acc := logicOperand a 0 path T lvl (T.openIf (P_ATOM < ctx) acc) ++ op
        T.closeIf (P_ATOM < ctx) (logicOperand b 1 path T (lvl + 1) acc)
      | "→", [a, b] | "↔", [a, b] =>
        let lvl := logicLevel name
        let op := if T.times != "*" then (if name == "→" then " \\to " else " \\leftrightarrow ") else " " ++ name ++ " "
        let acc := logicOperand a 0 path T (lvl + 1) (T.openIf (P_ATOM < ctx) acc) ++ op
        T.closeIf (P_ATOM < ctx) (logicOperand b 1 path T lvl acc)
      | "∀", [xv, dv, body] | "∃", [xv, dv, body] =>
        let acc := T.openIf (P_ATOM < ctx) acc ++ (if T.times != "*" then (if name == "∀" then "\\forall " else "\\exists ") else name ++ " ")
        let acc := print xv (0 :: path) T P_ADD acc ++ (if T.times != "*" then " \\in " else " ∈ ")
        let acc := print dv (1 :: path) T P_ADD acc ++ (if T.times != "*" then ",\\ " else ", ")
        T.closeIf (P_ATOM < ctx) (logicOperand body 2 path T 0 acc)
      | name, args => fnRaw T name args path ctx acc
    | .pow b x =>
      match (if T.times != "*" then radicalLatex b x else none) with
      | some (r, prec) => T.closeIf (prec < ctx) (T.openIf (prec < ctx) acc ++ r)
      | none =>
      if x.isNumEq (Q.ofRat (mkRat 1 2)) then
        T.closeIf (P_ATOM < ctx) (print b (0 :: path) T P_ADD (T.openIf (P_ATOM < ctx) acc ++ T.sqrtOpen) ++ T.sqrtClose)
      else match x with
      | .num q =>
        if q.isNeg then
          -- standalone x^(-n) → 1/x^n
          let acc := T.openIf (P_MUL < ctx) acc ++ T.fracOpen ++ T.num Q.one ++ T.fracMid
          T.closeIf (P_MUL < ctx) (powDenom b q.neg path T acc ++ T.fracClose)
        else powRaw b (.num q) path T ctx acc
      | x => powRaw b x path T ctx acc
    | .add args => T.closeIf (P_ADD < ctx) (addTerms args 0 path T (T.openIf (P_ADD < ctx) acc))
    | .mul args => mulRaw args path 0 T ctx acc
  termination_by 8 * e.size + 3
  decreasing_by all_goals print_decreasing

  /-- A logic connective's operand `c`, child `i`, bracketed when it is a connective binding looser
  than `lvl`. -/
  def logicOperand (c : Expr) (i : Nat) (path : Path) (T : Target) (lvl : Nat) (acc : String) : String :=
    let g := logicGroups c lvl
    T.closeIf g (print c (i :: path) T P_ADD (T.openIf g acc))
  termination_by 8 * c.size + 5
  decreasing_by all_goals print_decreasing

  /-- A call whose children print at the context of an argument, by its name first: a match on the
  name and the arguments together has equations too costly to derive. A name whose arguments are
  not the shape it expects prints as a plain call. -/
  def fnRaw (T : Target) (name : String) (args : List Expr) (path : Path) (ctx : Nat) (acc : String) : String :=
    let g : Bool := P_ATOM < ctx
    match name with
    | "sqrt" => match args with
      | [a] => T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ T.sqrtOpen) ++ T.sqrtClose)
      | as => fnPlain T name as path ctx acc
    | "π" => match args with
      | [] => T.closeIf g (T.openIf g acc ++ (if T.times != "*" then "\\pi" else "π"))
      | as => fnPlain T name as path ctx acc
    | "i" => match args with
      | [] => T.closeIf g (T.openIf g acc ++ "i")
      | as => fnPlain T name as path ctx acc
    | "conj" => match args with
      | [a] =>
        if T.times != "*" then T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "\\overline{") ++ "}")
        else T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "conj(") ++ ")")
      | as => fnPlain T name as path ctx acc
    | "re" => match args with
      | [a] =>
        if T.times != "*" then T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "\\operatorname{Re}\\left(") ++ "\\right)")
        else T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "re(") ++ ")")
      | as => fnPlain T name as path ctx acc
    | "im" => match args with
      | [a] =>
        if T.times != "*" then T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "\\operatorname{Im}\\left(") ++ "\\right)")
        else T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "im(") ++ ")")
      | as => fnPlain T name as path ctx acc
    | "abs" => match args with
      | [a] =>
        if T.times != "*" then T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "\\left|") ++ "\\right|")
        else T.closeIf g (print a (0 :: path) T P_ADD (T.openIf g acc ++ "abs(") ++ ")")
      | as => fnPlain T name as path ctx acc
    -- in LaTeX exp(x) is e^{x}, which binds as a power; the text stays exp(x), which reads back as itself
    | "exp" => match args with
      | [.num q] =>
        if q.isOne then T.closeIf g (T.openIf g acc ++ (if T.times != "*" then "e" else "ℯ"))
        else if T.times != "*" then T.closeIf (P_POW < ctx) (print (.num q) (0 :: path) T P_ADD (T.openIf (P_POW < ctx) acc ++ "e^{") ++ "}")
        else fnPlain T name [.num q] path ctx acc
      | [a] =>
        if T.times != "*" then T.closeIf (P_POW < ctx) (print a (0 :: path) T P_ADD (T.openIf (P_POW < ctx) acc ++ "e^{") ++ "}")
        else fnPlain T name [a] path ctx acc
      | as => fnPlain T name as path ctx acc
    | "diff" => match args with
      | [a, .var x] =>
        if T.times != "*" then
          let acc := print (.var x) (1 :: path) T P_ADD (T.openIf (P_MUL < ctx) acc ++ "\\frac{d}{d") ++ "}\\left("
          T.closeIf (P_MUL < ctx) (print a (0 :: path) T P_ADD acc ++ "\\right)")
        else fnPlain T name [a, .var x] path ctx acc
      | as => fnPlain T name as path ctx acc
    | "integrate" => match args with
      | [a, .var x] =>
        if T.times != "*" then
          let acc := print a (0 :: path) T P_ADD (T.openIf (P_MUL < ctx) acc ++ "\\int ") ++ " \\, d"
          T.closeIf (P_MUL < ctx) (print (.var x) (1 :: path) T P_ADD acc)
        else fnPlain T name [a, .var x] path ctx acc
      | [a, .var x, lo, hi] =>
        if T.times != "*" then
          let acc := print lo (2 :: path) T P_ADD (T.openIf (P_MUL < ctx) acc ++ "\\int_{") ++ "}^{"
          let acc := print hi (3 :: path) T P_ADD acc ++ "} "
          let acc := print a (0 :: path) T P_ADD acc ++ " \\, d"
          T.closeIf (P_MUL < ctx) (print (.var x) (1 :: path) T P_ADD acc)
        else fnPlain T name [a, .var x, lo, hi] path ctx acc
      | as => fnPlain T name as path ctx acc
    | "sum" => match args with
      | [a, .var k, lo, hi] =>
        if T.times != "*" then
          let acc := print (.var k) (1 :: path) T P_ADD (T.openIf (P_MUL < ctx) acc ++ "\\sum_{") ++ "="
          let acc := print lo (2 :: path) T P_ADD acc ++ "}^{"
          let acc := print hi (3 :: path) T P_ADD acc ++ "} "
          T.closeIf (P_MUL < ctx) (print a (0 :: path) T P_ADD acc)
        else fnPlain T name [a, .var k, lo, hi] path ctx acc
      | as => fnPlain T name as path ctx acc
    -- the order-theory world
    | "set" | "List" =>
      let acc := printArgs args 0 path T "" (T.openIf g acc ++ (if T.times != "*" then "\\{" else "{"))
      T.closeIf g (acc ++ (if T.times != "*" then "\\}" else "}"))
    | "poset" => match args with
      | [ss, _] => T.closeIf g (print ss (0 :: path) T P_ADD (T.openIf g acc ++ (if T.times != "*" then "\\text{poset }" else "poset ")))
      | as => fnPlain T name as path ctx acc
    | "pair" => match args with
      | [a, b] =>
        let acc := print a (0 :: path) T P_ADD (T.openIf g acc ++ "(") ++ ", "
        T.closeIf g (print b (1 :: path) T P_ADD acc ++ ")")
      | as => fnPlain T name as path ctx acc
    | "rel" => match args with
      | [_, ps] => T.closeIf g (print ps (1 :: path) T P_ADD (T.openIf g acc))
      | as => fnPlain T name as path ctx acc
    | "↦" => match args with
      | [a, b] =>
        let acc := print a (0 :: path) T P_ADD (T.openIf (P_ADD < ctx) acc) ++ (if T.times != "*" then " \\mapsto " else "↦")
        T.closeIf (P_ADD < ctx) (print b (1 :: path) T P_ADD acc)
      | as => fnPlain T name as path ctx acc
    | "covers" => match args with
      | [a, b] =>
        let acc := print a (0 :: path) T P_ADD (T.openIf (P_MUL < ctx) acc) ++ (if T.times != "*" then " \\lessdot " else " ⋖ ")
        T.closeIf (P_MUL < ctx) (print b (1 :: path) T P_ADD acc)
      | as => fnPlain T name as path ctx acc
    | "span" => match args with
      | [a, b, c] =>
        let sep := if T.times != "*" then "\\mathbin{;;}" else ";;"
        let acc := print a (0 :: path) T P_ADD (T.openIf (P_ADD < ctx) acc) ++ sep
        let acc := print b (1 :: path) T P_ADD acc
        T.closeIf (P_ADD < ctx) (if c.isOne then acc else print c (2 :: path) T P_ADD (acc ++ sep))
      | as => fnPlain T name as path ctx acc
    -- the logic world
    | "⊤" => match args with
      | [] => T.closeIf g (T.openIf g acc ++ (if T.times != "*" then "\\top" else "⊤"))
      | as => fnPlain T name as path ctx acc
    | "⊥" => match args with
      | [] => T.closeIf g (T.openIf g acc ++ (if T.times != "*" then "\\bot" else "⊥"))
      | as => fnPlain T name as path ctx acc
    | "range" => match args with
      | [a, b] =>
        if T.times != "*" then
          let acc := print a (0 :: path) T P_ADD (T.openIf g acc ++ "\\{") ++ ", \\dots, "
          T.closeIf g (print b (1 :: path) T P_ADD acc ++ "\\}")
        else
          let acc := print a (0 :: path) T P_ADD (T.openIf g acc) ++ ".."
          T.closeIf g (print b (1 :: path) T P_ADD acc)
      | as => fnPlain T name as path ctx acc
    | "<" | "≤" | ">" | "≥" | "=" | "≠" | "∣" => match args with
      | [a, b] =>
        let op := if T.times == "*" then name else match name with
          | "≤" => "\\le" | "≥" => "\\ge" | "≠" => "\\ne" | "∣" => "\\mid" | o => o
        let acc := print a (0 :: path) T P_ADD (T.openIf g acc) ++ " " ++ op ++ " "
        T.closeIf g (print b (1 :: path) T P_ADD acc)
      | as => fnPlain T name as path ctx acc
    | "All" => match args with
      | [] => T.closeIf g (T.openIf g acc ++ (if T.times != "*" then "\\mathrm{All}" else "All"))
      | as => fnPlain T name as path ctx acc
    -- a world's input as written (`Surface.lean`): its literal pieces (the first argument, never
    -- printed) around its children
    | "§" => match args with
      | .var ps :: kids => printPieces kids (ps.splitOn "␟") 1 path T acc
      | as => fnPlain T name as path ctx acc
    | _ => fnPlain T name args path ctx acc
  termination_by 8 * Expr.sizeList args + 7
  decreasing_by all_goals print_decreasing

  /-- A plain call: the head, its arguments at the precedence of an argument, the brackets. -/
  def fnPlain (T : Target) (name : String) (args : List Expr) (path : Path) (ctx : Nat) (acc : String) : String :=
    T.closeIf (P_ATOM < ctx) (printArgs args 0 path T "" (T.openIf (P_ATOM < ctx) acc ++ T.fnOpen name) ++ T.fnClose)
  termination_by 8 * Expr.sizeList args + 6
  decreasing_by all_goals print_decreasing

  /-- `b^x` with a non-negative or symbolic exponent. -/
  def powRaw (b x : Expr) (path : Path) (T : Target) (ctx : Nat) (acc : String) : String :=
    -- left of ^ needs parens for anything non-atomic incl. -3 and 2^3; right-assoc: 2^3^4 is 2^(3^4)
    let acc := print b (0 :: path) T (P_POW + 1) (T.openIf (P_POW < ctx) acc ++ T.powOpen) ++ T.powMid
    -- in text a fractional exponent needs its parentheses: 2^(3/2), not 2^3/2 (an exact one binds as a
    -- division and has them already; a decimal, 2^(0.5), does not)
    let g := T.times == "*" && (match x with | .num q => !q.isInt && q.approx | _ => false)
    let acc := T.closeIf g (print x (1 :: path) T P_POW (T.openIf g acc))
    T.closeIf (P_POW < ctx) (acc ++ T.powClose)
  termination_by 8 * (b.size + x.size) + 5
  decreasing_by all_goals print_decreasing

  /-- The denominator `b^n` of `1/b^n`, printed for `b^(-n)` at `p`: `x` for `n = 1`, `√x` for
  `n = ½`, a radical where LaTeX has one. -/
  def powDenom (b : Expr) (n : Q) (p : Path) (T : Target) (acc : String) : String :=
    match (if T.times != "*" then radicalLatex b (.num n) else none) with
    | some (r, _) => acc ++ r
    | none =>
      if n.isOne then print b (0 :: p) T T.denomPrec acc
      else if (Expr.num n).isNumEq (Q.ofRat (mkRat 1 2)) then print b (0 :: p) T P_ADD (acc ++ T.sqrtOpen) ++ T.sqrtClose   -- x^(-1/2) → 1/sqrt(x)
      else
        -- in text a fractional exponent needs its parentheses: 1/2^(3/2), not 1/2^3/2
        let acc := print b (0 :: p) T (P_POW + 1) (acc ++ T.powOpen) ++ T.powMid
        let g := T.times == "*" && !n.isInt
        T.closeIf g (T.leaf (1 :: p) (T.num n) (T.openIf g acc)) ++ T.powClose
  termination_by 8 * b.size + 5
  decreasing_by all_goals print_decreasing

  /-- The arguments of a call from the `i`-th, each at the precedence of an argument, `sep` before
  the first of them and `T.argSep` before each of the rest. -/
  def printArgs (args : List Expr) (i : Nat) (path : Path) (T : Target) (sep : String) (acc : String) : String :=
    match args with
    | [] => acc
    | a :: rest => printArgs rest (i + 1) path T T.argSep (print a (i :: path) T P_ADD (acc ++ sep))
  termination_by 8 * Expr.sizeList args + 5
  decreasing_by all_goals (have := Expr.size_pos a; print_decreasing)

  /-- A node as its source has it (`Surface.tpl`): each literal piece, unlabelled, then the next
  child, labelled with its path (from 1: the pieces are argument 0). A piece is its LaTeX and its
  text, separated by `␞`. -/
  def printPieces (args : List Expr) (pieces : List String) (i : Nat) (path : Path) (T : Target) (acc : String) : String :=
    let piece := match pieces.head? with
      | some p => match p.splitOn "␞" with
        | [l, t] => if T.times != "*" then l else t
        | _ => p
      | none => ""
    match args with
    | [] => acc ++ piece
    | a :: rest => printPieces rest pieces.tail (i + 1) path T (print a (i :: path) T P_ADD (acc ++ piece))
  termination_by 8 * Expr.sizeList args + 5
  decreasing_by all_goals (have := Expr.size_pos a; print_decreasing)

  /-- The terms of a sum from the `i`-th, after `acc`. -/
  def addTerms (args : List Expr) (i : Nat) (path : Path) (T : Target) (acc : String) : String :=
    match args with
    | [] => acc
    | a :: rest =>
      let negative := (splitCoeff a).1.isNeg
      let acc := if i == 0 && !negative then print a (i :: path) T P_ADD acc
        else
          let acc := acc ++ (if i == 0 then "-" else if negative then " - " else " + ")
          if negative then negTerm a (i :: path) T acc else print a (i :: path) T P_MUL acc
      addTerms rest (i + 1) path T acc
  termination_by 8 * Expr.sizeList args + 7
  decreasing_by all_goals (have := Expr.size_pos a; print_decreasing)

  /-- A term of a sum whose coefficient is negative (`splitCoeff`), printed without its sign:
  `-3`, `-x` and `-2x` print `3`, `x` and `2*x` after the ` - `. -/
  def negTerm (a : Expr) (p : Path) (T : Target) (acc : String) : String :=
    match a with
    | .num q => T.leaf p (T.num q.neg) acc
    -- `-(a·b)`: there is no node for the product without its `-1`, so it is the signed term's (`p`)
    -- and its factors keep their true paths, `p.1`, `p.2`, … (not `p.1.0`)
    | .mul [.num q, .mul rs] =>
      if q.neg.isOne then T.wrapClose p (mulRaw rs p 1 T P_MUL (T.wrapOpen p acc))
      -- the product printer, on the term with its sign dropped, so `− x²/4` and `x²/4` agree (and the
      -- factors keep their true paths: the numeral is child 0, the rest follow)
      else print (.mul (.num q.neg :: rs)) p T P_MUL acc
    | .mul [.num q, r] =>
      if q.neg.isOne then print r (1 :: p) T P_MUL acc else print (.mul [.num q.neg, r]) p T P_MUL acc
    | .mul (.num q :: r :: rs) =>
      if q.neg.isOne then T.wrapClose p (mulRaw (r :: rs) p 1 T P_MUL (T.wrapOpen p acc))
      else print (.mul (.num q.neg :: r :: rs)) p T P_MUL acc
    -- not reached: any other term's coefficient is 1
    | a => print a p T P_MUL acc
  termination_by 8 * a.size + 5
  decreasing_by all_goals print_decreasing

  /-- The product of `args`, its `i`-th factor at `i + off :: path`: `off` is 1 for the factors
  of `mul [-1, a, b]` printed without their sign. A leading `-1` becomes a unary minus; the factors
  are sorted into a numerator and a denominator (`factorInNumer`, `factorInDenom`) and written in
  that order, each once. -/
  def mulRaw (args : List Expr) (path : Path) (off : Nat) (T : Target) (ctx : Nat) (acc : String) : String :=
    match (if T.times != "*" then mulRadicalLatex T.num args else none) with
    | some (r, prec) => T.closeIf (prec < ctx) (T.openIf (prec < ctx) acc ++ r)
    | none =>
    let sign := leadingNeg args
    let prec := if sign then P_NEG else P_MUL
    let denoms := countFactors factorInDenom args 0
    let acc := T.openIf (prec < ctx) acc
    let acc := if sign then acc ++ "-" else acc
    let acc := if denoms > 0 then acc ++ T.fracOpen else acc
    let acc := if countFactors factorInNumer args 0 > 0 then mulNumer args 0 path off T "" acc else acc ++ T.num Q.one
    let acc := if denoms > 0 then
        let g := denoms > 1 && T.denomPrec > P_MUL
        T.closeIf g (mulDenom args 0 path off T "" (T.openIf g (acc ++ T.fracMid))) ++ T.fracClose
      else acc
    T.closeIf (prec < ctx) acc
  termination_by 8 * Expr.sizeList args + 7
  decreasing_by all_goals print_decreasing

  /-- The numerator parts of the factors from the `i`-th, `sep` before the first and `T.times`
  before each of the rest. -/
  def mulNumer (args : List Expr) (i : Nat) (path : Path) (off : Nat) (T : Target) (sep : String) (acc : String) : String :=
    match args with
    | [] => acc
    | f :: rest =>
      if factorInNumer f i then mulNumer rest (i + 1) path off T T.times (numerPart f i ((i + off) :: path) T (acc ++ sep))
      else mulNumer rest (i + 1) path off T sep acc
  termination_by 8 * Expr.sizeList args + 6
  decreasing_by all_goals (have := Expr.size_pos f; print_decreasing)

  /-- The numerator part of the `i`-th factor `f`, at `p`. -/
  def numerPart (f : Expr) (i : Nat) (p : Path) (T : Target) (acc : String) : String :=
    match f with
    | .num q =>
      if i == 0 then
        let a := q.abs
        if a.isInt || q.approx then T.leaf p (T.num a) acc else T.leaf p (T.num (Q.ofInt a.val.num)) acc
      else print (.num q) p T (P_MUL + 1) acc
    | f => print f p T P_MUL acc
  termination_by 8 * f.size + 5
  decreasing_by all_goals print_decreasing

  /-- The denominator parts of the factors from the `i`-th, `sep` before the first and `T.times`
  before each of the rest. -/
  def mulDenom (args : List Expr) (i : Nat) (path : Path) (off : Nat) (T : Target) (sep : String) (acc : String) : String :=
    match args with
    | [] => acc
    | f :: rest =>
      if factorInDenom f i then mulDenom rest (i + 1) path off T T.times (denomPart f ((i + off) :: path) T (acc ++ sep))
      else mulDenom rest (i + 1) path off T sep acc
  termination_by 8 * Expr.sizeList args + 6
  decreasing_by all_goals (have := Expr.size_pos f; print_decreasing)

  /-- The denominator part of a factor `f` at `p`. A leading coefficient's denominator carries the
  coefficient's label when its numerator part is a `1` that is not shown. -/
  def denomPart (f : Expr) (p : Path) (T : Target) (acc : String) : String :=
    match f with
    | .num q =>
      let a := q.abs
      let dn := T.num (Q.ofInt (Int.ofNat a.val.den))
      if (Q.ofInt a.val.num).isOne then T.leaf p dn acc else acc ++ dn
    | .pow b (.num q) => T.wrapClose p (powDenom b q.neg p T (T.wrapOpen p acc))
    -- not reached: no other factor has a part below the line
    | _ => acc
  termination_by 8 * f.size + 5
  decreasing_by all_goals print_decreasing
end

def Expr.toText (e : Expr) : String := print e [] textTarget P_ADD ""
def Expr.toLatex (e : Expr) (paths := false) : String := print e [] (latexTarget paths) P_ADD ""

end MathEngine
