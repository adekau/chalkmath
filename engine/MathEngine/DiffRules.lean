import MathEngine.Order
import MathEngine.Print
/-!
# `diff.*` — differentiation as rewriting

`diff(e, x)` is an ordinary node and the calculus rules push it inward, so the trace reads like a
textbook derivation with pending d/dx's visible at each step. Ported from `diff.ts`. These rules
duplicate subterms (product, chain); M5 orders them with `M (diff f x) = 3 ^ M f` (Order.lean) and
M4 proves each against `HasDerivAt`. Malformed `diff` nodes refuse, so a normal form has none.
-/
namespace MathEngine
open Expr

def D (e : Expr) (x : String) : Expr := .fn "diff" [e, .var x]

/-- `diff(body, x)` with a variable target, if `e` is one. -/
def target : Expr → Option (Expr × String)
  | .fn "diff" [body, .var x] => some (body, x)
  | _ => none

def rule (name : String) (f : Expr × String → Option RuleResult) : PlainRule :=
  { name, apply := fun e => target e >>= f }

def diffHigherOrder : PlainRule :=
  { name := "diff.higher-order", apply := fun e =>
      match e with
      | .fn "diff" [body, .var x, .num n] =>
        if n.isInt && n.val.num ≥ 1 then
          let k := n.val.num.toNat
          some ⟨(List.range k).foldl (fun r _ => D r x) body, s!"The {k}th derivative is {k} successive derivatives.", none, none⟩
        else some ⟨e, "", none, some "the order of a derivative must be a positive integer"⟩
      | .fn "diff" [_, .var _] => none
      | .fn "diff" [_, _] => some ⟨e, "", none, some "differentiate with respect to a variable: diff(f, x)"⟩
      | .fn "diff" _ => some ⟨e, "", none, some "diff takes (f, x) or (f, x, n)"⟩
      | _ => none }

def diffConstant : PlainRule :=
  rule "diff.constant" fun (body, x) =>
    if !body.dependsOn x then
      some ⟨Expr.zero, s!"${body.toText}$ does not depend on ${x}$, so its derivative is 0: constants have zero rate of change.", none, none⟩
    else none

def diffVariable : PlainRule :=
  rule "diff.variable" fun (body, x) =>
    match body with
    | .var y => if y == x then some ⟨Expr.one, s!"$\\frac\{d}\{d{x}} {x} = 1$: the identity function has slope 1 everywhere.", none, none⟩ else none
    | _ => none

def diffSumAll : PlainRule :=
  rule "diff.sum" fun (body, x) =>
    match body with
    | .add (a :: b :: es) => some ⟨.add ((a :: b :: es).map (D · x)), "Sum rule: the derivative of a sum is the sum of the derivatives (differentiation is linear).", none, none⟩
    | _ => none

def diffConstMul : PlainRule :=
  rule "diff.constant-multiple" fun (body, x) =>
    match body with
    | .mul es =>
      let consts := es.filter (fun a => !a.dependsOn x)
      let rest := es.filter (fun a => a.dependsOn x)
      if consts.isEmpty || rest.isEmpty then none
      else some ⟨.mul (consts ++ [D (mulN rest) x]),
        s!"Constant multiple rule: factors independent of ${x}$ (here ${(mulN consts).toText}$) pull out of the derivative.", none, none⟩
    | _ => none

/-- The product-rule terms: for each factor, its derivative first, then the other factors in order. -/
def prodTerms (x : String) : List Expr → List Expr → List Expr
  | _, [] => []
  | acc, f :: rest => .mul (D f x :: (acc ++ rest)) :: prodTerms x (acc ++ [f]) rest

def diffProductAll : PlainRule :=
  rule "diff.product" fun (body, x) =>
    match body with
    | .mul (f :: g :: fs) =>
      let expl := match fs with
        | [] => s!"Product rule: $(fg)' = f'g + fg'$ with $f = {f.toText}$ and $g = {g.toText}$."
        | _ => s!"Product rule for {fs.length + 2} factors: differentiate each factor in turn, holding the others fixed, and add."
      some ⟨.add (prodTerms x [] (f :: g :: fs)), expl, none, none⟩
    | _ => none

def diffPowerAll : PlainRule :=
  rule "diff.power" fun (body, x) =>
    match body with
    | .pow base exp =>
      let baseDep := base.dependsOn x
      let expDep := exp.dependsOn x
      if baseDep && !expDep then
        let nMinus1 := Expr.add [exp, Expr.minusOne]
        match base with
        | .var y => if y == x
            then some ⟨.mul [exp, .pow base nMinus1], s!"Power rule: $\\frac\{d}\{d{x}} {x}^n = n\\,{x}^\{n-1}$ with $n = {exp.toText}$.", none, none⟩
            else some ⟨.mul [exp, .pow base nMinus1, D base x], s!"Power rule with the chain rule: $(u^n)' = n u^\{n-1} u'$ where $u = {base.toText}$.", none, none⟩
        | _ => some ⟨.mul [exp, .pow base nMinus1, D base x], s!"Power rule with the chain rule: $(u^n)' = n u^\{n-1} u'$ where $u = {base.toText}$.", none, none⟩
      else if !baseDep && expDep then
        some ⟨.mul [body, .fn "ln" [base], D exp x], s!"Exponential rule with the chain rule: $(b^u)' = b^u \\ln b \\cdot u'$ where $u = {exp.toText}$.", none, none⟩
      else if baseDep && expDep then
        some ⟨.mul [body, .add [.mul [D exp x, .fn "ln" [base]], .mul [exp, Expr.div (D base x) base]]],
          s!"Both base and exponent depend on ${x}$: write $f^g = e^\{g \\ln f}$ and differentiate, giving $f^g\\left(g' \\ln f + g \\frac\{f'}\{f}\\right)$.", none, none⟩
      else none
    | _ => none

/-- The derivative of the outer function and the law it follows. -/
def outerOf (f : String) (u : Expr) : Option (Expr × String) :=
  match f with
  | "sin" => some (.fn "cos" [u], "\\sin' = \\cos")
  | "cos" => some (Expr.neg (.fn "sin" [u]), "\\cos' = -\\sin")
  | "tan" => some (.pow (.fn "cos" [u]) (Expr.ofInt (-2)), "\\tan' = \\sec^2 = 1/\\cos^2")
  | "exp" => some (.fn "exp" [u], "\\exp' = \\exp")
  | "ln" => some (.pow u Expr.minusOne, "\\ln' u = 1/u")
  | _ => none

/-- The chain factor `u'`, omitted when `u` is the variable itself. -/
def innerOf (u : Expr) (x : String) : List Expr :=
  match u with | .var y => if y == x then [] else [D u x] | _ => [D u x]

def diffChainAll : PlainRule :=
  rule "diff.chain" fun (body, x) =>
    match body with
    | .fn f [u] =>
      match outerOf f u with
      | some (fprime, law) =>
        let inner := innerOf u x
        some ⟨.mul (fprime :: inner),
          if inner.isEmpty then s!"${law}$." else s!"Chain rule: $(f(u))' = f'(u)\\,u'$ with ${law}$ and $u = {u.toText}$.", none, none⟩
      | none => none
    | _ => none

/-! ## Where the calculus rules hold everywhere, and what they assume elsewhere

`diff.sum`, `diff.product`, `diff.power` and `diff.chain` need the functions they split apart to be
differentiable, and `ln`, `tan`, real exponents and `b^u` need a domain condition besides. Each rule
has two halves that rewrite exactly as the whole: the verified one fires where nothing is needed,
because every part is `smooth` (differentiable everywhere) and no domain condition arises; the
`.assuming` one fires elsewhere and its step ends with what it assumes. -/

def posNumeral : Expr → Bool | .num q => !q.isNeg && !q.isZero | _ => false

mutual
  /-- Differentiable everywhere, in every variable: numerals, variables, constants, `+`, `·`, a power
  by a natural numeral, a power of a positive numeral, and `sin`, `cos`, `exp` of such a term. -/
  def smooth : Expr → Bool
    | .num _ => true
    | .var _ => true
    | .add es => smoothList es
    | .mul es => smoothList es
    | .pow b e =>
      (match e with
       | .num n => n.isInt && decide (0 ≤ n.val.num) && smooth b
       | _ => false) || (posNumeral b && smooth e)
    | .fn f [u] => (f == "sin" || f == "cos" || f == "exp") && smooth u
    | .fn _ [] => true
    | _ => false
  def smoothList : List Expr → Bool
    | [] => true
    | e :: es => smooth e && smoothList es
end

/-- `$u$ differentiable`, unless `u` is smooth. -/
def diffCond (u : Expr) : List String := if smooth u then [] else [s!"${u.toText}$ differentiable"]

/-- What a calculus step on `diff(body, x)` assumes. -/
def diffConds (e : Expr) : List String :=
  match target e with
  | none => []
  | some (body, x) =>
    match body with
    | .add es => es.flatMap diffCond
    | .mul es => es.flatMap diffCond
    | .pow b n =>
      let bd := b.dependsOn x
      let nd := n.dependsOn x
      if bd && !nd then
        (match n with
         | .num q =>
           if q.isInt && decide (0 ≤ q.val.num) then []
           else if q.isInt then [s!"${b.toText} \\neq 0$"] else [s!"${b.toText} > 0$"]
         | _ => [s!"${b.toText} > 0$"]) ++ diffCond b
      else if !bd && nd then
        (if posNumeral b then [] else [s!"${b.toText} > 0$"]) ++ diffCond n
      else [s!"${b.toText} > 0$"] ++ diffCond b ++ diffCond n
    | .fn "tan" [u] => [s!"$\\cos({u.toText}) \\neq 0$"] ++ diffCond u
    | .fn "ln" [u] => [s!"${u.toText} > 0$"] ++ diffCond u
    | .fn _ [u] => diffCond u
    | _ => []

/-- The half of a rule that fires where it assumes nothing. -/
def verifiedHalf (r : PlainRule) : PlainRule :=
  { r with apply := fun e => if (diffConds e).isEmpty then r.apply e else none }

/-- The half that fires where it assumes something, and says what. -/
def assumingHalf (r : PlainRule) (name : String) : PlainRule :=
  { r with name := name, apply := fun e =>
      let cs := diffConds e
      if cs.isEmpty then none
      else (r.apply e).map fun res => { res with explanation := res.explanation ++ s!" Assuming {", ".intercalate cs}." } }

def diffSum : PlainRule := verifiedHalf diffSumAll
def diffSumAssuming : PlainRule := assumingHalf diffSumAll "diff.sum.assuming"
def diffProduct : PlainRule := verifiedHalf diffProductAll
def diffProductAssuming : PlainRule := assumingHalf diffProductAll "diff.product.assuming"
def diffPower : PlainRule := verifiedHalf diffPowerAll
def diffPowerAssuming : PlainRule := assumingHalf diffPowerAll "diff.power.assuming"
def diffChain : PlainRule := verifiedHalf diffChainAll
def diffChainAssuming : PlainRule := assumingHalf diffChainAll "diff.chain.assuming"

theorem verifiedHalf_some {r : PlainRule} {e : Expr} {res : RuleResult} (h : (verifiedHalf r).apply e = some res) :
    r.apply e = some res ∧ diffConds e = [] := by
  simp only [verifiedHalf] at h
  split at h
  · rename_i hc; exact ⟨h, List.isEmpty_iff.mp hc⟩
  · cases h

theorem assumingHalf_some {r : PlainRule} {n : String} {e : Expr} {res : RuleResult}
    (h : (assumingHalf r n).apply e = some res) :
    ∃ r₀, r.apply e = some r₀ ∧ res.result = r₀.result ∧ res.error = r₀.error := by
  simp only [assumingHalf] at h
  split at h
  · cases h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨r₀, h₀, rfl, rfl⟩

def diffMatrix : PlainRule :=
  { name := "diff.matrix", apply := fun e => Option.map (checkedLit e) <| target e >>= fun (body, x) =>
    match body with
    | .matrix rows => some ⟨.matrix (rows.map (·.map (D · x))), "Differentiate a matrix entrywise.", none, none⟩
    | _ => none }

def diffRules : List PlainRule := [diffHigherOrder, diffConstant, diffVariable, diffSum, diffSumAssuming, diffConstMul,
  diffProduct, diffProductAssuming, diffPower, diffPowerAssuming, diffChain, diffChainAssuming, diffMatrix]

end MathEngine
