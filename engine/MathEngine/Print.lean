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
private def P_ADD := 1
private def P_MUL := 2
private def P_LAM := 1
private def P_APP := 2
private def P_NEG := 2
private def P_POW := 3
private def P_ATOM := 4

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
    let head := if ["sin", "cos", "tan", "arcsin", "arccos", "arctan", "exp", "ln", "log", "arg"].contains n then s!"\\{n}" else s!"\\operatorname\{{n}}"
    let args := ", ".intercalate a
    s!"{head}\\left({args}\\right)"
  matrix rows := "\\begin{bmatrix}" ++ " \\\\ ".intercalate (rows.map (" & ".intercalate ·)) ++ "\\end{bmatrix}"
  times := " \\cdot "
  parens s := s!"\\left({s}\\right)"
  denomPrec := P_MUL

/-- Split a term into (coefficient, rest); `rest` keeps the original child paths. `restPathOffset`
is the child index of `rest` inside the term, or `none` when the whole term is the rest. -/
private def enum (l : List α) : List (Nat × α) := (List.range l.length).zip l

private def splitCoeff : Expr → Q × Option Expr × Option Nat
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

mutual
  /-- Print `e` at `path` in a context demanding precedence `ctx`. -/
  partial def print (e : Expr) (path : Path) (T : Target) (ctx : Nat) : String :=
    let (s, prec) := printRaw e path T
    T.wrap path (if prec < ctx then T.parens s else s)

  partial def printRaw (e : Expr) (path : Path) (T : Target) : String × Nat :=
    let child (c : Expr) (i : Nat) (ctx : Nat) := print c (path ++ [i]) T ctx
    -- a logic connective's operand: bracketed when it is a connective binding looser than `lvl`
    let lchild (c : Expr) (i : Nat) (lvl : Nat) :=
      let str := print c (path ++ [i]) T P_ADD
      match c with
      | .fn h _ => if isLogicHead h && logicLevel h < lvl then T.parens str else str
      | _ => str
    match e with
    -- in text an exact non-integer numeral prints as a division, `4/9`, so it binds like one: the base
    -- of a power is `(4/9)^(3/2)`, not `4/9^(3/2)`, which reads back as 4/27 (`\frac` groups itself)
    | .num q => (T.num q, if q.isNeg then P_NEG else if q.isSci || (T.times == "*" && !q.isInt && !q.approx) then P_MUL else P_ATOM)
    | .var x => (T.var x, P_ATOM)
    | .matrix rows =>
      let w := (rows.head?.map List.length).getD 0
      let rs := (enum rows).map fun (r, row) => (enum row).map fun (j, c) => child c (r * w + j) P_ADD
      (T.matrix rs, P_ATOM)
    | .fn name args =>
      -- the heads that print their children at a precedence of their own come first, so no child is
      -- printed twice (printing every child up front for these was exponential in a term's depth)
      let own : Option (String × Nat) := match name, args with
        -- the λ-calculus world: λx. body binds as far right as possible; application is juxtaposition
        | "λ", [xv, body] =>
          let x := child xv 0 P_ADD
          let b := print body (path ++ [1]) T P_LAM
          some (if T.times != "*" then s!"\\lambda {x}.\\, {b}" else s!"λ{x}. {b}", P_LAM)
        | "λ:", [xv, ty, body] =>
          let x := child xv 0 P_ADD
          let ts := child ty 1 P_ADD
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
          let inner := ", ".intercalate ((enum specs).map fun (i, a) => child a (i + 1) P_ADD)
          some (if T.times != "*" then s!"{ms}\\llbracket {inner}\\rrbracket" else s!"{ms}[[{inner}]]", P_ATOM)
        -- MATLAB's entrywise operators. Lower than a product as a whole, so it is grouped wherever a
        -- factor or a left operand would otherwise take it in: `x*(a ./ b)`, `(a ./ b) ./ c`
        | "ediv", [a, b] | "emul", [a, b] =>
          let l := print a (path ++ [0]) T P_MUL
          let r := print b (path ++ [1]) T P_POW
          let op := if T.times != "*" then (if name == "ediv" then "\\oslash" else "\\odot") else (if name == "ediv" then "./" else ".*")
          some (s!"{l} {op} {r}", P_ADD)
        -- the logic world: connectives by their own precedence (↔ < → < ∨ < ∧ < ¬), quantifiers reach right
        | "¬", [a] => some ((if T.times != "*" then "\\lnot " else "¬") ++ lchild a 0 5, P_ATOM)
        | "∧", [a, b] | "∨", [a, b] =>
          let lvl := logicLevel name
          let op := if T.times != "*" then (if name == "∧" then " \\land " else " \\lor ") else s!" {name} "
          some (lchild a 0 lvl ++ op ++ lchild b 1 (lvl + 1), P_ATOM)
        | "→", [a, b] | "↔", [a, b] =>
          let lvl := logicLevel name
          let op := if T.times != "*" then (if name == "→" then " \\to " else " \\leftrightarrow ") else s!" {name} "
          some (lchild a 0 (lvl + 1) ++ op ++ lchild b 1 lvl, P_ATOM)
        | "∀", [xv, dv, body] | "∃", [xv, dv, body] =>
          let x := child xv 0 P_ADD
          let d := child dv 1 P_ADD
          let body := lchild body 2 0
          some (if T.times != "*" then s!"{if name == "∀" then "\\forall" else "\\exists"} {x} \\in {d},\\ {body}" else s!"{name} {x} ∈ {d}, {body}", P_ATOM)
        | _, _ => none
      match own with
      | some r => r
      | none =>
      let as := (enum args).map fun (i, a) => child a i P_ADD
      match name, args, as with
      | "sqrt", [_], [a] => (T.sqrt a, P_ATOM)
      | "π", [], _ => (if T.times != "*" then "\\pi" else "π", P_ATOM)
      | "i", [], _ => ("i", P_ATOM)
      | "conj", [_], [a] => (if T.times != "*" then s!"\\overline\{{a}}" else s!"conj({a})", P_ATOM)
      | "re", [_], [a] => (if T.times != "*" then s!"\\operatorname\{Re}\\left({a}\\right)" else s!"re({a})", P_ATOM)
      | "im", [_], [a] => (if T.times != "*" then s!"\\operatorname\{Im}\\left({a}\\right)" else s!"im({a})", P_ATOM)
      | "abs", [_], [a] => (if T.times != "*" then s!"\\left|{a}\\right|" else s!"abs({a})", P_ATOM)
      | "exp", [.num q], _ => if q.isOne then (if T.times != "*" then "e" else "ℯ", P_ATOM) else (T.fn name as, P_ATOM)
      | "diff", [_, .var _], [a, x] =>
        if T.times != "*" then (s!"\\frac\{d}\{d{x}}\\left({a}\\right)", P_MUL) else (T.fn name as, P_ATOM)
      | "integrate", [_, .var _], [a, x] =>
        if T.times != "*" then (s!"\\int {a} \\, d{x}", P_MUL) else (T.fn name as, P_ATOM)
      | "integrate", [_, .var _, _, _], [a, x, lo, hi] =>
        if T.times != "*" then (s!"\\int_\{{lo}}^\{{hi}} {a} \\, d{x}", P_MUL) else (T.fn name as, P_ATOM)
      | "sum", [_, .var _, _, _], [a, k, lo, hi] =>
        if T.times != "*" then (s!"\\sum_\{{k}={lo}}^\{{hi}} {a}", P_MUL) else (T.fn name as, P_ATOM)
      -- the order-theory world
      | "set", _, _ =>
        let inner := ", ".intercalate as
        (if T.times != "*" then "\\{" ++ inner ++ "\\}" else "{" ++ inner ++ "}", P_ATOM)
      | "poset", [_, _], [ss, _] =>
        (if T.times != "*" then "\\text{poset }" ++ ss else "poset " ++ ss, P_ATOM)
      | "pair", [_, _], [a, b] => (if T.times != "*" then s!"({a}, {b})" else s!"({a}, {b})", P_ATOM)
      | "rel", [_, _], [_, ps] => (ps, P_ATOM)
      | "↦", [_, _], [a, b] => (if T.times != "*" then s!"{a} \\mapsto {b}" else s!"{a}↦{b}", P_ADD)
      | "covers", [_, _], [a, b] => (if T.times != "*" then s!"{a} \\lessdot {b}" else s!"{a} ⋖ {b}", P_MUL)
      | "span", [_, _, c], [a, b, cs] =>
        let sep := if T.times != "*" then "\\mathbin{;;}" else ";;"
        (if c.isOne then s!"{a}{sep}{b}" else s!"{a}{sep}{b}{sep}{cs}", P_ADD)
      -- the logic world: connectives by their own precedence (↔ < → < ∨ < ∧ < ¬), quantifiers reach right
      | "⊤", [], _ => (if T.times != "*" then "\\top" else "⊤", P_ATOM)
      | "⊥", [], _ => (if T.times != "*" then "\\bot" else "⊥", P_ATOM)
      | "range", [_, _], [a, b] => (if T.times != "*" then "\\{" ++ a ++ ", \\dots, " ++ b ++ "\\}" else s!"{a}..{b}", P_ATOM)
      | "<", [_, _], [a, b] | "≤", [_, _], [a, b] | ">", [_, _], [a, b] | "≥", [_, _], [a, b]
      | "=", [_, _], [a, b] | "≠", [_, _], [a, b] | "∣", [_, _], [a, b] =>
        let op := if T.times == "*" then name else match name with
          | "≤" => "\\le" | "≥" => "\\ge" | "≠" => "\\ne" | "∣" => "\\mid" | o => o
        (s!"{a} {op} {b}", P_ATOM)
      | "All", [], _ => (if T.times != "*" then "\\mathrm{All}" else "All", P_ATOM)
      | "List", _, _ =>
        let inner := ", ".intercalate as
        (if T.times != "*" then "\\{" ++ inner ++ "\\}" else "{" ++ inner ++ "}", P_ATOM)
      | _, _, _ => (T.fn name as, P_ATOM)
    | .pow b x =>
      match (if T.times != "*" then radicalLatex b x else none) with
      | some r => r
      | none =>
      if x.isNumEq (Q.ofRat (mkRat 1 2)) then (T.sqrt (child b 0 P_ADD), P_ATOM)
      else match x with
      | .num q =>
        if q.isNeg then
          -- standalone x^(-n) → 1/x^n
          let n := q.neg
          let base := child b 0 (if n.isOne then T.denomPrec else P_POW + 1)
          let den := match (if T.times != "*" then radicalLatex b (.num n) else none) with
            | some (r, _) => r
            | none =>
              if n.isOne then base
              else if (Expr.num n).isNumEq (Q.ofRat (mkRat 1 2)) then T.sqrt (child b 0 P_ADD)   -- x^(-1/2) → 1/sqrt(x)
              else
                -- in text a fractional exponent needs its parentheses: 1/2^(3/2), not 1/2^3/2
                let e := T.wrap (path ++ [1]) (T.num n)
                T.pow base (if T.times == "*" && !n.isInt then T.parens e else e)
          (T.frac (T.num Q.one) den, P_MUL)
        else powRaw b x
      | _ => powRaw b x
    | .add args =>
      let s := (enum args).foldl (init := ("" : String)) fun acc (i, a) =>
        let (coeff, rest, restOff) := splitCoeff a
        let negative := coeff.isNeg
        if i == 0 && !negative then acc ++ child a i P_ADD
        else
          let sign := if negative then " - " else " + "
          let termStr :=
            if negative then
              let absC := coeff.neg
              let p := path ++ [i]
              match rest with
              | none => T.wrap p (T.num absC)
              | some r =>
                if absC.isOne then
                  match restOff, r with
                  -- `-(a·b)`: there is no node for the product without its `-1`, so it is the signed
                  -- term's (`p`) and its factors keep their true paths, `p.1`, `p.2`, … (not `p.1.0`)
                  | some off, .mul rs =>
                    let (s, prec) := mulRaw rs p off T
                    T.wrap p (if prec < P_MUL then T.parens s else s)
                  | some off, _ => print r (p ++ [off]) T P_MUL
                  | none, _ => print r p T P_MUL
                else
                  -- the product printer, on the term with its sign dropped, so `− x²/4` and `x²/4` agree
                  -- (and the factors keep their true paths: the numeral is child 0, the rest follow)
                  print (.mul (.num absC :: (match r with | .mul rs => rs | r => [r]))) p T P_MUL
            else child a i P_MUL
          acc ++ (if i == 0 then sign.trimAscii.copy else sign) ++ termStr
      (s, P_ADD)
    | .mul args => mulRaw args path 0 T
  where
    powRaw (b x : Expr) : String × Nat :=
      let bs := print b (path ++ [0]) T (P_POW + 1)  -- left of ^ needs parens for anything non-atomic incl. -3 and 2^3
      let xs := print x (path ++ [1]) T P_POW        -- right-assoc: 2^3^4 is 2^(3^4)
      -- in text a fractional exponent needs its parentheses: 2^(3/2), not 2^3/2 (an exact one binds as a
      -- division and has them already; a decimal, 2^(0.5), does not)
      let xs := if T.times == "*" && (match x with | .num q => !q.isInt && q.approx | _ => false) then T.parens xs else xs
      (T.pow bs xs, P_POW)

  /-- The product of `args`, its `i`-th factor at `path ++ [i + off]`: `off` is 1 for the factors
  of `mul [-1, a, b]` printed without their sign. -/
  partial def mulRaw (args : List Expr) (path : Path) (off : Nat) (T : Target) : String × Nat :=
    match (if T.times != "*" then mulRadicalLatex T.num args else none) with
    | some r => r
    | none =>
    -- Partition into numerator / denominator factors; a leading -1 becomes a unary minus.
    let (sign, numer, denom) := (enum args).foldl (init := (("" : String), ([] : List String), ([] : List String)))
        fun ((sign, numer, denom) : String × List String × List String) ((i, a) : Nat × Expr) =>
      let p := path ++ [i + off]
      match i, a with
      | 0, .num q =>
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
      | _, .pow b (.num q) =>
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
        else (sign, numer ++ [print a p T P_MUL], denom)
      | _, _ => (sign, numer ++ [print a p T (P_MUL + (if i > 0 && a.isNum then 1 else 0))], denom)
    let n := if numer.isEmpty then T.num Q.one else T.times.intercalate numer
    if denom.isEmpty then (sign ++ n, if sign.isEmpty then P_MUL else P_NEG)
    else
      let d := if denom.length > 1 && T.denomPrec > P_MUL then T.parens (T.times.intercalate denom) else T.times.intercalate denom
      (sign ++ T.frac n d, if sign.isEmpty then P_MUL else P_NEG)
end

def Expr.toText (e : Expr) : String := print e [] textTarget P_ADD
def Expr.toLatex (e : Expr) (paths := false) : String := print e [] (latexTarget paths) P_ADD

end MathEngine
