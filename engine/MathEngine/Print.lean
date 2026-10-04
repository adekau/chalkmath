import MathEngine.Expr
/-!
# Printer

Recovers human notation from the minimal AST, mirroring `printer.ts` line for line:

```
add [a, mul [-1, b]]   →  a - b
mul [a, pow b (-1)]    →  a / b     (LaTeX: \frac{a}{b})
mul [-1, a]            →  -a
pow a (1/2)            →  sqrt(a)
```

Every printed subterm knows its `Path`; with `paths := true` the LaTeX output wraps each
subterm in `\htmlData{path=...}{...}`, which KaTeX renders as `<span data-path="0.1">`. That is
how the notebook turns a click into a `Path` for `engine.explain`.
-/
namespace MathEngine
open Expr

/-- What differs between the text and LaTeX outputs. -/
structure Target where
  wrap : Path → String → String
  num : Q → String
  var : String → String
  frac : String → String → String
  pow : String → String → String
  sqrt : String → String
  fn : String → List String → String
  matrix : List (List String) → String
  times : String
  parens : String → String
  /-- Context precedence for a denominator: text needs parens around products (`a/(b*c)`); `\frac` does not. -/
  denomPrec : Nat

-- precedence levels: what the *context* demands vs. what the term *provides*
def P_ADD := 1
def P_MUL := 2
def P_LAM := 1
def P_APP := 2
def P_NEG := 2
def P_POW := 3
def P_ATOM := 4

def textTarget : Target where
  wrap _ s := s
  num q := q.toText
  var n := n
  frac n d := s!"{n}/{d}"
  pow b e := s!"{b}^{e}"
  sqrt s := s!"sqrt({s})"
  fn n a := let args := ", ".intercalate a; s!"{n}({args})"
  matrix rows := "[" ++ "; ".intercalate (rows.map (", ".intercalate ·)) ++ "]"
  times := "*"
  parens s := s!"({s})"
  denomPrec := P_POW

private def greek : List (String × String) :=
  [("π", "\\pi"), ("alpha", "\\alpha"), ("beta", "\\beta"), ("theta", "\\theta"), ("lambda", "\\lambda"),
   ("α", "\\alpha"), ("β", "\\beta"), ("γ", "\\gamma"), ("δ", "\\delta"), ("ε", "\\varepsilon"), ("θ", "\\theta"),
   ("λ", "\\lambda"), ("μ", "\\mu"), ("σ", "\\sigma"), ("τ", "\\tau"), ("φ", "\\varphi"), ("ψ", "\\psi"), ("ω", "\\omega"),
   ("ζ", "\\zeta"), ("η", "\\eta"), ("ι", "\\iota"), ("κ", "\\kappa"), ("ν", "\\nu"), ("ξ", "\\xi"), ("ρ", "\\rho"), ("χ", "\\chi"),
   ("Γ", "\\Gamma"), ("Δ", "\\Delta"), ("Θ", "\\Theta"), ("Λ", "\\Lambda"), ("Σ", "\\Sigma"), ("Φ", "\\Phi"), ("Ω", "\\Omega")]
private def pathStr (p : Path) : String := if p.isEmpty then "root" else ".".intercalate (p.map toString)

def latexTarget (paths : Bool) : Target where
  wrap p s := if paths then s!"\\htmlData\{path={pathStr p}}\{{s}}" else s
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
  frac n d := s!"\\frac\{{n}}\{{d}}"
  pow b e := s!"\{{b}}^\{{e}}"
  sqrt s := s!"\\sqrt\{{s}}"
  fn n a :=
    let head := if ["sin", "cos", "tan", "arcsin", "arccos", "arctan", "exp", "ln", "log"].contains n then s!"\\{n}" else s!"\\operatorname\{{n}}"
    let args := ", ".intercalate a
    s!"{head}\\left({args}\\right)"
  matrix rows := "\\begin{bmatrix}" ++ " \\\\ ".intercalate (rows.map (" & ".intercalate ·)) ++ "\\end{bmatrix}"
  times := " \\cdot "
  parens s := s!"\\left({s}\\right)"
  denomPrec := P_MUL

/-- Split a term into (coefficient, rest); `rest` keeps the original child paths. `restPathOffset`
is the child index of `rest` inside the term, or `none` when the whole term is the rest. -/
private def enum (l : List α) : List (Nat × α) := (List.range l.length).zip l

def splitCoeff : Expr → Q × Option Expr × Option Nat
  | .num q => (q, none, none)
  | .mul (.num q :: rest@(_ :: _)) => (q, some (match rest with | [r] => r | rs => .mul rs), some 1)
  | e => (Q.one, some e, none)

/-- Is `n ≥ 2` a perfect `k`-th power for some `k ≥ 2`? (`4`, `8`, `16`: yes; `12`, `50`: no.) -/
private def isPerfectPower (n : Nat) : Bool :=
  (List.range (Nat.log2 n + 1)).any fun k =>
    k ≥ 2 &&
    -- the k-th root by bisection, then a check
    (let rec go (lo hi : Nat) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => lo
        | fuel + 1 => if lo ≥ hi then lo else
            let mid := (lo + hi + 1) / 2
            if mid ^ k ≤ n then go mid hi fuel else go lo (mid - 1) fuel
      let r := go 1 (2 ^ (Nat.log2 n / k + 1)) 64
      r ^ k == n)

/-- `a^(p/q)` for an integer `a ≥ 2` and `0 < p/q` not an integer, the way a textbook writes it:
the `q`-th-power part of `a` and the integer part of `p/q` come out as a coefficient (`2^(3/2)` is
`2√2`, `12^(1/2)` is `2√3`). Display only — the term is unchanged, and the ordering the rules
decrease cannot turn one power into a product, so this is the printer's job — except for a base
that is itself a perfect power (`4^(1/2)`, `8^(1/2)`): `simp.power` and `simp.radical` reduce those in
a step of their own, so they print as they are, `√4`, `√8`, and that step shows. -/
def radicalParts (a q : Q) : Option (Nat × String) :=
  if !(a.isInt && a.val.num ≥ 2 && !q.isInt && !q.isNeg && !q.isZero) then none else
  let n := a.val.num.toNat
  if isPerfectPower n then none else
  let p := q.val.num.toNat
  let d := q.val.den
  let i := p / d
  let f := p % d
  let hi := 2 ^ (Nat.log2 n / d + 1)
  let m := ((List.range (hi + 1)).reverse.find? fun m => m ≥ 1 && n % (m ^ d) == 0).getD 1
  let s := n / (m ^ d)
  let coef := m ^ p * s ^ i
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

/-- A logic connective's operand: bracketed when it is a connective binding looser than `lvl`. -/
private def logicOperand (T : Target) (c : Expr) (str : String) (lvl : Nat) : String :=
  match c with
  | .fn h _ => if isLogicHead h && logicLevel h < lvl then T.parens str else str
  | _ => str

/-- A call whose children print at the context of an argument, `as` being their text. -/
def fnRaw (T : Target) (name : String) (args : List Expr) (as : List String) : String × Nat :=
  let plain := (T.fn name as, P_ATOM)
  -- by name first: a match on the name and the arguments together has equations too costly to derive
  match name with
  | "sqrt" => match args, as with | [_], [a] => (T.sqrt a, P_ATOM) | _, _ => plain
  | "π" => match args with | [] => (if T.times != "*" then "\\pi" else "π", P_ATOM) | _ => plain
  | "i" => match args with | [] => ("i", P_ATOM) | _ => plain
  | "conj" => match args, as with
    | [_], [a] => (if T.times != "*" then s!"\\overline\{{a}}" else s!"conj({a})", P_ATOM) | _, _ => plain
  | "re" => match args, as with
    | [_], [a] => (if T.times != "*" then s!"\\operatorname\{Re}\\left({a}\\right)" else s!"re({a})", P_ATOM) | _, _ => plain
  | "im" => match args, as with
    | [_], [a] => (if T.times != "*" then s!"\\operatorname\{Im}\\left({a}\\right)" else s!"im({a})", P_ATOM) | _, _ => plain
  | "abs" => match args, as with
    | [_], [a] => (if T.times != "*" then s!"\\left|{a}\\right|" else s!"abs({a})", P_ATOM) | _, _ => plain
  | "exp" => match args with
    | [.num q] => if q.isOne then (if T.times != "*" then "e" else "ℯ", P_ATOM) else plain
    | _ => plain
  | "diff" => match args, as with
    | [_, .var _], [a, x] => if T.times != "*" then (s!"\\frac\{d}\{d{x}}\\left({a}\\right)", P_MUL) else plain
    | _, _ => plain
  | "integrate" => match args, as with
    | [_, .var _], [a, x] => if T.times != "*" then (s!"\\int {a} \\, d{x}", P_MUL) else plain
    | [_, .var _, _, _], [a, x, lo, hi] =>
      if T.times != "*" then (s!"\\int_\{{lo}}^\{{hi}} {a} \\, d{x}", P_MUL) else plain
    | _, _ => plain
  | "sum" => match args, as with
    | [_, .var _, _, _], [a, k, lo, hi] => if T.times != "*" then (s!"\\sum_\{{k}={lo}}^\{{hi}} {a}", P_MUL) else plain
    | _, _ => plain
  -- the order-theory world
  | "set" =>
    let inner := ", ".intercalate as
    (if T.times != "*" then "\\{" ++ inner ++ "\\}" else "{" ++ inner ++ "}", P_ATOM)
  | "poset" => match args, as with
    | [_, _], [ss, _] => (if T.times != "*" then "\\text{poset }" ++ ss else "poset " ++ ss, P_ATOM)
    | _, _ => plain
  | "pair" => match args, as with
    | [_, _], [a, b] => (if T.times != "*" then s!"({a}, {b})" else s!"({a}, {b})", P_ATOM) | _, _ => plain
  | "rel" => match args, as with | [_, _], [_, ps] => (ps, P_ATOM) | _, _ => plain
  | "↦" => match args, as with
    | [_, _], [a, b] => (if T.times != "*" then s!"{a} \\mapsto {b}" else s!"{a}↦{b}", P_ADD) | _, _ => plain
  | "covers" => match args, as with
    | [_, _], [a, b] => (if T.times != "*" then s!"{a} \\lessdot {b}" else s!"{a} ⋖ {b}", P_MUL) | _, _ => plain
  | "span" => match args, as with
    | [_, _, c], [a, b, cs] =>
      let sep := if T.times != "*" then "\\mathbin{;;}" else ";;"
      (if c.isOne then s!"{a}{sep}{b}" else s!"{a}{sep}{b}{sep}{cs}", P_ADD)
    | _, _ => plain
  -- the logic world
  | "⊤" => match args with | [] => (if T.times != "*" then "\\top" else "⊤", P_ATOM) | _ => plain
  | "⊥" => match args with | [] => (if T.times != "*" then "\\bot" else "⊥", P_ATOM) | _ => plain
  | "range" => match args, as with
    | [_, _], [a, b] => (if T.times != "*" then "\\{" ++ a ++ ", \\dots, " ++ b ++ "\\}" else s!"{a}..{b}", P_ATOM)
    | _, _ => plain
  | "<" | "≤" | ">" | "≥" | "=" | "≠" | "∣" => match args, as with
    | [_, _], [a, b] =>
      let op := if T.times == "*" then name else match name with
        | "≤" => "\\le" | "≥" => "\\ge" | "≠" => "\\ne" | "∣" => "\\mid" | o => o
      (s!"{a} {op} {b}", P_ATOM)
    | _, _ => plain
  | "All" => match args with | [] => (if T.times != "*" then "\\mathrm{All}" else "All", P_ATOM) | _ => plain
  | "List" =>
    let inner := ", ".intercalate as
    (if T.times != "*" then "\\{" ++ inner ++ "\\}" else "{" ++ inner ++ "}", P_ATOM)
  | _ => plain

/-- The printer's termination goals: a subterm, or a member of a subterm's list, weighs less. -/
local macro "print_decreasing" : tactic => `(tactic| (
  simp_wf
  (try have := Expr.size_le_sizeList (by assumption))
  (try have := Expr.sizeList_le_sizeRows (by assumption))
  (try simp only [Expr.size, Expr.sizeList, Expr.sizeRows] at *)
  (try omega)))

/-! The printer is structural in all but name: every call prints a subterm, or a product rebuilt
from a subterm's factors with a new coefficient, which weighs no more than the subterm. The measure
counts nodes (`Expr.size`, a numeral weighing 1 whatever its value), times four, so each function in
the block sits at its own offset below the one that calls it on the same term. -/
set_option maxHeartbeats 4000000 in
mutual
  /-- Print `e` at `path` in a context demanding precedence `ctx`. -/
  def print (e : Expr) (path : Path) (T : Target) (ctx : Nat) : String :=
    let (s, prec) := printRaw e path T
    T.wrap path (if prec < ctx then T.parens s else s)
  termination_by 8 * e.size + 4
  decreasing_by all_goals print_decreasing

  def printRaw (e : Expr) (path : Path) (T : Target) : String × Nat :=
    match e with
    -- in text an exact non-integer numeral prints as a division, `4/9`, so it binds like one: the base
    -- of a power is `(4/9)^(3/2)`, not `4/9^(3/2)`, which reads back as 4/27 (`\frac` groups itself)
    | .num q => (T.num q, if q.isNeg then P_NEG else if q.isSci || (T.times == "*" && !q.isInt && !q.approx) then P_MUL else P_ATOM)
    | .var x => (T.var x, P_ATOM)
    | .matrix rows =>
      let w := (rows.head?.map List.length).getD 0
      let rs := (enum rows.attach).map fun (r, ⟨row, _⟩) =>
        (enum row.attach).map fun (j, ⟨c, _⟩) => print c (path ++ [r * w + j]) T P_ADD
      (T.matrix rs, P_ATOM)
    | .fn name args =>
      -- the heads that print their children at a precedence of their own come first, so no child is
      -- printed twice (printing every child up front for these was exponential in a term's depth)
      let own : Option (String × Nat) := match name, args with
        -- the λ-calculus world: λx. body binds as far right as possible; application is juxtaposition
        | "λ", [xv, body] =>
          let x := print xv (path ++ [0]) T P_ADD
          let b := print body (path ++ [1]) T P_LAM
          some (if T.times != "*" then s!"\\lambda {x}.\\, {b}" else s!"λ{x}. {b}", P_LAM)
        | "λ:", [xv, ty, body] =>
          let x := print xv (path ++ [0]) T P_ADD
          let ts := print ty (path ++ [1]) T P_ADD
          let b := print body (path ++ [2]) T P_LAM
          let ts := match ty with | .fn "→" _ => T.parens ts | _ => ts
          some (if T.times != "*" then s!"\\lambda {x}\{:}{ts}.\\, {b}" else s!"λ{x}:{ts}. {b}", P_LAM)
        | "λ.", [body] =>
          let b := print body (path ++ [0]) T P_LAM
          some (if T.times != "*" then s!"\\lambda.\\, {b}" else s!"λ. {b}", P_LAM)
        | "@", [f, a] =>
          let fs := print f (path ++ [0]) T P_APP
          let as := print a (path ++ [1]) T (P_APP + 1)
          some (if T.times != "*" then s!"{fs}\\ {as}" else s!"{fs} {as}", P_APP)
        -- Mathematica's Part: m[[2, 1;;3]], and the specs it takes
        | "part", m :: specs =>
          let ms := print m (path ++ [0]) T P_ATOM
          let inner := ", ".intercalate (printArgs specs 1 path T)
          some (if T.times != "*" then s!"{ms}\\llbracket {inner}\\rrbracket" else s!"{ms}[[{inner}]]", P_ATOM)
        -- MATLAB's entrywise operators. Lower than a product as a whole, so it is grouped wherever a
        -- factor or a left operand would otherwise take it in: `x*(a ./ b)`, `(a ./ b) ./ c`
        | "ediv", [a, b] | "emul", [a, b] =>
          let l := print a (path ++ [0]) T P_MUL
          let r := print b (path ++ [1]) T P_POW
          let op := if T.times != "*" then (if name == "ediv" then "\\oslash" else "\\odot") else (if name == "ediv" then "./" else ".*")
          some (s!"{l} {op} {r}", P_ADD)
        -- the logic world: connectives by their own precedence (↔ < → < ∨ < ∧ < ¬), quantifiers reach right
        | "¬", [a] => some ((if T.times != "*" then "\\lnot " else "¬") ++ logicOperand T a (print a (path ++ [0]) T P_ADD) 5, P_ATOM)
        | "∧", [a, b] | "∨", [a, b] =>
          let lvl := logicLevel name
          let op := if T.times != "*" then (if name == "∧" then " \\land " else " \\lor ") else s!" {name} "
          some (logicOperand T a (print a (path ++ [0]) T P_ADD) lvl ++ op ++ logicOperand T b (print b (path ++ [1]) T P_ADD) (lvl + 1), P_ATOM)
        | "→", [a, b] | "↔", [a, b] =>
          let lvl := logicLevel name
          let op := if T.times != "*" then (if name == "→" then " \\to " else " \\leftrightarrow ") else s!" {name} "
          some (logicOperand T a (print a (path ++ [0]) T P_ADD) (lvl + 1) ++ op ++ logicOperand T b (print b (path ++ [1]) T P_ADD) lvl, P_ATOM)
        | "∀", [xv, dv, body] | "∃", [xv, dv, body] =>
          let x := print xv (path ++ [0]) T P_ADD
          let d := print dv (path ++ [1]) T P_ADD
          let body := logicOperand T body (print body (path ++ [2]) T P_ADD) 0
          some (if T.times != "*" then s!"{if name == "∀" then "\\forall" else "\\exists"} {x} \\in {d},\\ {body}" else s!"{name} {x} ∈ {d}, {body}", P_ATOM)
        | _, _ => none
      match own with
      | some r => r
      | none =>
      let as := printArgs args 0 path T
      fnRaw T name args as
    | .pow b x =>
      match (if T.times != "*" then radicalLatex b x else none) with
      | some r => r
      | none =>
      if x.isNumEq (Q.ofRat (mkRat 1 2)) then (T.sqrt (print b (path ++ [0]) T P_ADD), P_ATOM)
      else match x with
      | .num q =>
        if q.isNeg then
          -- standalone x^(-n) → 1/x^n
          let n := q.neg
          let base := print b (path ++ [0]) T (if n.isOne then T.denomPrec else P_POW + 1)
          let den := match (if T.times != "*" then radicalLatex b (.num n) else none) with
            | some (r, _) => r
            | none =>
              if n.isOne then base
              else if (Expr.num n).isNumEq (Q.ofRat (mkRat 1 2)) then T.sqrt (print b (path ++ [0]) T P_ADD)   -- x^(-1/2) → 1/sqrt(x)
              else
                -- in text a fractional exponent needs its parentheses: 1/2^(3/2), not 1/2^3/2
                let e := T.wrap (path ++ [1]) (T.num n)
                T.pow base (if T.times == "*" && !n.isInt then T.parens e else e)
          (T.frac (T.num Q.one) den, P_MUL)
        else powRaw b (.num q) path T
      | x => powRaw b x path T
    | .add args => (addTerms args 0 path T "", P_ADD)
    | .mul args => mulRaw args path 0 T
  termination_by 8 * e.size + 3
  decreasing_by all_goals print_decreasing

  /-- `b^x` with a non-negative or symbolic exponent. -/
  def powRaw (b x : Expr) (path : Path) (T : Target) : String × Nat :=
    let bs := print b (path ++ [0]) T (P_POW + 1)  -- left of ^ needs parens for anything non-atomic incl. -3 and 2^3
    let xs := print x (path ++ [1]) T P_POW        -- right-assoc: 2^3^4 is 2^(3^4)
    -- in text a fractional exponent needs its parentheses: 2^(3/2), not 2^3/2 (an exact one binds as a
    -- division and has them already; a decimal, 2^(0.5), does not)
    let xs := if T.times == "*" && (match x with | .num q => !q.isInt && q.approx | _ => false) then T.parens xs else xs
    (T.pow bs xs, P_POW)
  termination_by 8 * (b.size + x.size) + 5
  decreasing_by all_goals print_decreasing

  /-- The arguments of a call from the `i`-th, each at the precedence of an argument. -/
  def printArgs (args : List Expr) (i : Nat) (path : Path) (T : Target) : List String :=
    match args with
    | [] => []
    | a :: rest => print a (path ++ [i]) T P_ADD :: printArgs rest (i + 1) path T
  termination_by 8 * Expr.sizeList args + 5
  decreasing_by all_goals (have := Expr.size_pos a; print_decreasing)

  /-- The terms of a sum from the `i`-th, after `acc`. -/
  def addTerms (args : List Expr) (i : Nat) (path : Path) (T : Target) (acc : String) : String :=
    match args with
    | [] => acc
    | a :: rest =>
      let negative := (splitCoeff a).1.isNeg
      let acc := if i == 0 && !negative then acc ++ print a (path ++ [i]) T P_ADD
        else
          let sign := if negative then " - " else " + "
          let termStr := if negative then negTerm a (path ++ [i]) T else print a (path ++ [i]) T P_MUL
          acc ++ (if i == 0 then sign.trimAscii.copy else sign) ++ termStr
      addTerms rest (i + 1) path T acc
  termination_by 8 * Expr.sizeList args + 7
  decreasing_by all_goals (have := Expr.size_pos a; print_decreasing)

  /-- A term of a sum whose coefficient is negative (`splitCoeff`), printed without its sign:
  `-3`, `-x` and `-2x` print `3`, `x` and `2*x` after the ` - `. -/
  def negTerm (a : Expr) (p : Path) (T : Target) : String :=
    match a with
    | .num q => T.wrap p (T.num q.neg)
    -- `-(a·b)`: there is no node for the product without its `-1`, so it is the signed term's (`p`)
    -- and its factors keep their true paths, `p.1`, `p.2`, … (not `p.1.0`)
    | .mul [.num q, .mul rs] =>
      if q.neg.isOne then
        let (s, prec) := mulRaw rs p 1 T
        T.wrap p (if prec < P_MUL then T.parens s else s)
      -- the product printer, on the term with its sign dropped, so `− x²/4` and `x²/4` agree (and the
      -- factors keep their true paths: the numeral is child 0, the rest follow)
      else print (.mul (.num q.neg :: rs)) p T P_MUL
    | .mul [.num q, r] =>
      if q.neg.isOne then print r (p ++ [1]) T P_MUL else print (.mul [.num q.neg, r]) p T P_MUL
    | .mul (.num q :: r :: rs) =>
      if q.neg.isOne then
        let (s, prec) := mulRaw (r :: rs) p 1 T
        T.wrap p (if prec < P_MUL then T.parens s else s)
      else print (.mul (.num q.neg :: r :: rs)) p T P_MUL
    -- not reached: any other term's coefficient is 1
    | a => print a p T P_MUL
  termination_by 8 * a.size + 5
  decreasing_by all_goals print_decreasing

  /-- The product of `args`, its `i`-th factor at `path ++ [i + off]`: `off` is 1 for the factors
  of `mul [-1, a, b]` printed without their sign. -/
  def mulRaw (args : List Expr) (path : Path) (off : Nat) (T : Target) : String × Nat :=
    match (if T.times != "*" then mulRadicalLatex T.num args else none) with
    | some r => r
    | none =>
    -- Partition into numerator / denominator factors; a leading -1 becomes a unary minus.
    let (sign, numer, denom) := mulFactors args 0 path off T "" [] []
    let n := if numer.isEmpty then T.num Q.one else T.times.intercalate numer
    if denom.isEmpty then (sign ++ n, if sign.isEmpty then P_MUL else P_NEG)
    else
      let d := if denom.length > 1 && T.denomPrec > P_MUL then T.parens (T.times.intercalate denom) else T.times.intercalate denom
      (sign ++ T.frac n d, if sign.isEmpty then P_MUL else P_NEG)
  termination_by 8 * Expr.sizeList args + 7
  decreasing_by all_goals print_decreasing

  /-- The factors of a product from the `i`-th, sorted into a sign, a numerator and a denominator. -/
  def mulFactors (args : List Expr) (i : Nat) (path : Path) (off : Nat) (T : Target)
      (sign : String) (numer denom : List String) : String × List String × List String :=
    match args with
    | [] => (sign, numer, denom)
    | f :: rest =>
      let (sign, numer, denom) := mulFactor f i (path ++ [i + off]) T sign numer denom
      mulFactors rest (i + 1) path off T sign numer denom
  termination_by 8 * Expr.sizeList args + 6
  decreasing_by all_goals (have := Expr.size_pos f; print_decreasing)

  /-- The `i`-th factor `f` of a product, at `p`, into the sign, numerator and denominator so far. -/
  def mulFactor (f : Expr) (i : Nat) (p : Path) (T : Target)
      (sign : String) (numer denom : List String) : String × List String × List String :=
    match f with
      | .num q =>
        if i == 0 then
          -- a rational coefficient p/d puts p in the numerator and d in the denominator — `x/(2π)`,
          -- as a hand derivation writes it, not `½·x/π`
          let sign := if q.isNeg then ("-" : String) else sign
          let a := q.abs
          -- an integer (a `1` stays visible: the identity step removes it) or an approximate decimal prints as is
          if a.isInt || q.approx then (sign, if q.isNeg && a.isOne then numer else numer ++ [T.wrap p (T.num a)], denom)
          else
            let pn := Q.ofInt a.val.num
            let dn := Q.ofInt (Int.ofNat a.val.den)
            (sign, if pn.isOne then numer else numer ++ [T.wrap p (T.num pn)], denom ++ [if pn.isOne then T.wrap p (T.num dn) else T.num dn])
        else (sign, numer ++ [print (.num q) p T (P_MUL + 1)], denom)
      | .pow b (.num q) =>
        if q.isNeg then
          let n := q.neg
          let base := print b (p ++ [0]) T (if n.isOne then T.denomPrec else P_POW + 1)
          let den := match (if T.times != "*" then radicalLatex b (.num n) else none) with
            | some (r, _) => r
            | none =>
              if n.isOne then base
              else if (Expr.num n).isNumEq (Q.ofRat (mkRat 1 2)) then T.sqrt (print b (p ++ [0]) T P_ADD)   -- ·x^(-1/2) → /sqrt(x)
              else
                let e := T.wrap (p ++ [1]) (T.num n)
                T.pow base (if T.times == "*" && !n.isInt then T.parens e else e)
          (sign, numer, denom ++ [T.wrap p den])
        else (sign, numer ++ [print (.pow b (.num q)) p T P_MUL], denom)
      | a => (sign, numer ++ [print a p T P_MUL], denom)
  termination_by 8 * f.size + 5
  decreasing_by all_goals print_decreasing
end

def Expr.toText (e : Expr) : String := print e [] textTarget P_ADD
def Expr.toLatex (e : Expr) (paths := false) : String := print e [] (latexTarget paths) P_ADD

end MathEngine
