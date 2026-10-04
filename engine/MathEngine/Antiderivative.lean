import MathEngine.DiffRules
import MathEngine.ExpandRules
/-!
# `int.*` — a small antiderivative finder (M8)

The command that uses it (`cmdIntegrate`, Pipeline.lean) differentiates whatever comes back and
accepts it only if the derivative normalizes to the integrand (`cmdIntegrate_spec`, Integrate.lean).
Most of the finder's rules are proved besides, compositionally (`anti_sound`,
`proofs/Proofs/Antiderivative.lean`): if the sub-results are antiderivatives of the sub-integrands,
the result is an antiderivative of the integrand. Where a rule needs a domain condition (`ln u` needs
`u > 0`, `a^u` needs `a > 0, a ≠ 1`, dividing by a linear coefficient needs it nonzero, …) it
records it as data (`ICond`), its step is the rule's `.assuming` half, and its text ends with what it
assumes; the rest are verified. u-substitution, integration by parts and the arctangent and arcsine
forms build on the normalizer's outputs, which nothing proves things about here, so their results
are marked `checked`: the check above carries their claim alone.

Covered: constants, the variable, sums, constant factors, powers `u^n` (`ln u` at `n = −1`),
exponentials `a^u`, the elementary table (sin, cos, exp, ln, tan, arctan, arcsin, arccos, and
sec² as `cos^(-2)`), each with `u = a·x + b`; `1/(k + c·u²)` as an arctangent and `1/√(k − c·u²)` as an arcsine; then
for products, u-substitution (`∫ c·g'·H'(g) = c·H(g)`) and integration by parts (LIATE: a
logarithm first, else a power of the variable, a few levels deep). The derivatives those two
need come from the caller's normalizer, so the finder never differentiates on its own.
Every step records `∫ g dx` as its `before` and the antiderivative found as its `after`.

The finder is a total function: `anti` recurses on a depth bound as well as on the by-parts `fuel`,
and one level of it (`antiStep`) is given the recursion as an argument, so each rule is a function
of its sub-results and each has its own theorem.
-/
namespace MathEngine
namespace Anti
open Expr

def integral (f : Expr) (x : String) : Expr := .fn "integrate" [f, .var x]

/-- The coefficient of `x` in a term `c·x` or `x`. -/
def coeffOfTerm (x : String) : Expr → Option Expr
  | .var y => if y == x then some Expr.one else none
  | .mul es =>
    match es.partition (·.dependsOn x) with
    | ([.var y], cs) => if y == x then some (mulN cs) else none
    | _ => none
  | _ => none

/-- `u = a·x + b` with `a` constant: the coefficient `a`. -/
def linearCoeff (x : String) (u : Expr) : Option Expr :=
  match u with
  | .add es =>
    match es.partition (·.dependsOn x) with
    | ([t], _) => coeffOfTerm x t
    | _ => none
  | _ => coeffOfTerm x u

/-- What a finder step assumes, as data: the step's text names it, and the proofs read it as a
proposition at a point (`ICond.Holds`). -/
inductive ICond where
  /-- `u > 0` -/
  | pos (u : Expr)
  /-- `u ≠ 0` -/
  | ne (u : Expr)
  /-- `cos u > 0` -/
  | cosPos (u : Expr)
  /-- `cos u ≠ 0` -/
  | cosNe (u : Expr)
  /-- `−1 < u < 1` -/
  | inside (u : Expr)
  /-- `b > 0` and `b ≠ 1` -/
  | base (b : Expr)
  /-- `n ≠ −1` -/
  | notNegOne (n : Expr)
  deriving Inhabited

def ICond.text : ICond → String
  | .pos u => s!"${u.toText} > 0$"
  | .ne u => s!"${u.toText} \\neq 0$"
  | .cosPos u => s!"$\\cos({u.toText}) > 0$"
  | .cosNe u => s!"$\\cos({u.toText}) \\neq 0$"
  | .inside u => s!"$-1 < {u.toText} < 1$"
  | .base b => s!"${b.toText} > 0$ and ${b.toText} \\neq 1$"
  | .notNegOne n => s!"${n.toText} \\neq -1$"

/-- A step of the finder: the rule's verified half when it assumes nothing, else its `.assuming`
half, whose text ends with what it assumes. -/
def mkStep (rule text : String) (cs : List ICond) (before after : Expr) : Step :=
  if cs.isEmpty then ⟨rule, text, [], before, after, none⟩
  else
    let text := if text.endsWith "." then text else text ++ "."
    ⟨rule ++ ".assuming", text ++ s!" Assuming {", ".intercalate (cs.map ICond.text)}.", [], before, after, none⟩

/-- `a ≠ 0`, unless `a` is a nonzero numeral. -/
def neCond (a : Expr) : List ICond :=
  match a with
  | .num q => if q.isZero then [.ne a] else []
  | _ => [.ne a]

/-- `b > 0` and `b ≠ 1`, unless `b` is a numeral or a constant that is. -/
def baseConds (b : Expr) : List ICond :=
  match b with
  | .num q => if q.isNeg || q.isZero || q.isOne then [.base b] else []
  | .fn "π" [] => []
  | _ => [.base b]

/-- A candidate antiderivative, the steps that found it, what they assume, and whether one of
them is a guess only the check vouches for (`checked`). -/
structure Found where
  F : Expr
  steps : Array Step
  conds : List ICond := []
  checked : Bool := false
  deriving Inhabited

/-- Antiderivatives of the elementary functions in their argument, and what each assumes. -/
def table (g : String) (u : Expr) : Option (Expr × String × List ICond) :=
  match g with
  | "sin" => some (neg (.fn "cos" [u]), "$\\int \\sin u \\, du = -\\cos u$", [])
  | "cos" => some (.fn "sin" [u], "$\\int \\cos u \\, du = \\sin u$", [])
  | "exp" => some (.fn "exp" [u], "$\\int e^u \\, du = e^u$", [])
  | "ln" => some (sub (.mul [u, .fn "ln" [u]]) u, "$\\int \\ln u \\, du = u \\ln u - u$", [.pos u])
  | "tan" => some (neg (.fn "ln" [.fn "cos" [u]]), "$\\int \\tan u \\, du = -\\ln \\cos u$", [.cosPos u])
  | "arctan" => some (sub (.mul [u, .fn "arctan" [u]]) (.mul [.num (Q.ofRat (mkRat 1 2)), .fn "ln" [.add [Expr.one, .pow u (ofInt 2)]]]),
      "$\\int \\arctan u \\, du = u \\arctan u - \\tfrac12 \\ln(1 + u^2)$ (by parts)", [])
  | "arcsin" => some (.add [.mul [u, .fn "arcsin" [u]], .pow (sub Expr.one (.pow u (ofInt 2))) (.num (Q.ofRat (mkRat 1 2)))],
      "$\\int \\arcsin u \\, du = u \\arcsin u + \\sqrt{1 - u^2}$ (by parts)", [.inside u])
  | "arccos" => some (sub (.mul [u, .fn "arccos" [u]]) (.pow (sub Expr.one (.pow u (ofInt 2))) (.num (Q.ofRat (mkRat 1 2)))),
      "$\\int \\arccos u \\, du = u \\arccos u - \\sqrt{1 - u^2}$ (by parts)", [.inside u])
  | _ => none

/-- `c·v²` (`c` a numeral, `1` when absent): `(c, v)`. -/
def sqTerm : Expr → Option (Q × Expr)
  | .pow v (.num n) => if n.val == 2 then some (Q.one, v) else none
  | .mul [.num c, .pow v (.num n)] => if n.val == 2 then some (c, v) else none
  | _ => none

/-- A sum `k + c·v²` of a numeral and a square, in either order: `(k, c, v)`. -/
def quadForm : List Expr → Option (Q × Q × Expr)
  | [.num k, t] => (sqTerm t).map fun (c, v) => (k, c, v)
  | [t, .num k] => (sqTerm t).map fun (c, v) => (k, c, v)
  | _ => none

/-- `q^(-1/2)`, as a numeral when `q` is the square of a rational. -/
def invSqrtQ (q : Q) : Expr :=
  match exactRoot q.val 2 with
  | some r => if r == 0 then .pow (.num q) (.num (Q.ofRat (mkRat (-1) 2))) else .num (Q.ofRat r).inv
  | none => .pow (.num q) (.num (Q.ofRat (mkRat (-1) 2)))

/-- `∫ (k + c·v²)^(-1) dx` is an arctangent and `∫ (k − c·v²)^(-1/2) dx` an arcsine, for numerals
`k, c > 0` and `v = a·x + b`: `u = √(c/k)·v` turns them into `∫ du/(1 + u²)` and `∫ du/√(1 − u²)`. -/
def invTrig (x : String) (f b e : Expr) : Option (Expr × Array Step) := do
  -- `1/√(…)` is `((…)^(1/2))^(-1)`
  let (es, n) ← match b, e with
    | .add es, .num n => some (es, n)
    | .pow (.add es) (.num p), .num q => some (es, p.mul q)
    | _, _ => none
  let (k, c, v) ← quadForm es
  if !decide (0 < k.val) then none
  let a ← linearCoeff x v
  let negHalf := Q.ofRat (mkRat (-1) 2)
  -- `√(c/k)` as `c·(kc)^(-1/2)`, so that differentiating meets the radicals the integrand has
  let arg (c : Q) : Expr := if (c.div k).isOne then v else .mul [.num c, invSqrtQ (k.mul c), v]
  let byU := if v == .var x then "" else s!" with $u = {v.toText}$"
  let kc (c : Q) := if k.isOne && c.isOne then "" else s!" ($k = {(Expr.num k).toText}$, $c = {(Expr.num c).toText}$)"
  let (rule, G, why) ←
    if n.val == -1 && decide (0 < c.val) then
      some ("int.arctan", .mul [invSqrtQ (k.mul c), .fn "arctan" [arg c]],
        (if k.isOne && c.isOne then "$\\int \\frac{du}{1 + u^2} = \\arctan u$"
         else "$\\int \\frac{du}{k + c u^2} = \\frac{1}{\\sqrt{kc}}\\arctan\\left(\\sqrt{c/k}\\,u\\right)$")
        ++ kc c ++ byU ++ ". The derivative of $\\arctan u$ is $1/(1 + u^2)$.")
    else if n.val == negHalf.val && decide (c.val < 0) then
      some ("int.arcsin", .mul [invSqrtQ c.neg, .fn "arcsin" [arg c.neg]],
        (if k.isOne && c.neg.isOne then "$\\int \\frac{du}{\\sqrt{1 - u^2}} = \\arcsin u$"
         else "$\\int \\frac{du}{\\sqrt{k - c u^2}} = \\frac{1}{\\sqrt{c}}\\arcsin\\left(\\sqrt{c/k}\\,u\\right)$")
        ++ kc c.neg ++ byU ++ ". The derivative of $\\arcsin u$ is $1/\\sqrt{1 - u^2}$.")
    else none
  let F := if a.isOne then G else Expr.div G a
  let why := if a.isOne then why else why ++ s!" Since $du = {a.toText}\\,d{x}$, the result is divided by ${a.toText}$."
  return (F, #[⟨rule, why, [], integral f x, F, none⟩])

/-- `∫ u^n du` for an exponent free of the variable: the power rule, or `ln u` at `n = −1`, and what
it assumes: nothing for a natural numeral `n`, `u ≠ 0` for another integer, `u > 0` otherwise, and
`n ≠ −1` besides for a symbolic `n`. -/
def powerRule (u n : Expr) : Expr × String × List ICond :=
  if n.isNumEq Q.minusOne then (.fn "ln" [u], "$\\int u^{-1} \\, du = \\ln u$", [.pos u])
  else match n with
    | .num q =>
      let n1 := q.add Q.one
      (.mul [.num (Q.one.div n1), .pow u (.num n1)], "$\\int u^n \\, du = u^{n+1}/(n+1)$",
        if q.isInt && !q.isNeg then [] else if q.isInt then [.ne u] else [.pos u])
    | _ =>
      let n1 := .add [n, Expr.one]
      (.mul [.pow n1 Expr.minusOne, .pow u n1], "$\\int u^n \\, du = u^{n+1}/(n+1)$", [.pos u, .notNegOne n])

/-- `∫ g(a·x + b) dx = (1/a) G(a·x + b)`: the substitution step, if the coefficient is not 1; it
assumes `a ≠ 0` unless `a` is a numeral. -/
def substitute (x : String) (f G a : Expr) : Expr × Array Step × List ICond :=
  if a.isOne then (G, #[], [])
  else
    let cs := neCond a
    (Expr.div G a, #[mkStep "int.linear-substitution" s!"Linear substitution: with $u = {(f.children.headD f).toText}$, $du = ({a.toText})\\,d{x}$, so the integral in $x$ is $1/({a.toText})$ times the integral in $u$." cs (integral f x) (Expr.div G a)], cs)

/-- A factor as `base^k` for a positive natural `k` (`k = 1` for anything but a power), or `k = 0`
when it is a power by anything else. -/
def powerOf (f : Expr) : Expr × Nat :=
  match f with
  | .pow b (.num q) => if q.isInt && q.val.num ≥ 1 then (b, q.val.num.toNat) else (f, 0)
  | _ => (f, 1)

/-- `sin^m u · cos^n u` among the factors, all with the same `u`: `(u, m, n)`. Nothing else may be
present (constants have been pulled out by then). -/
def trigPowers : List Expr → Option (Expr × Nat × Nat) := go none 0 0
where
  go (u? : Option Expr) (m n : Nat) : List Expr → Option (Expr × Nat × Nat)
    | [] => u?.map fun u => (u, m, n)
    | f :: fs =>
      let (base, k) := powerOf f
      if k = 0 then none else
      let same (v : Expr) : Bool := match u? with | some u => equal u v | none => true
      match base with
      | .fn "sin" [v] => if same v then go (some v) (m + k) n fs else none
      | .fn "cos" [v] => if same v then go (some v) m (n + k) fs else none
      | _ => none

/-- `b^k` with `b^0 = 1` and `b^1 = b`. -/
def pw (b : Expr) (k : Nat) : Expr := if k = 0 then Expr.one else if k = 1 then b else .pow b (ofInt k)

/-- A product of the factors that are not `1`. -/
def prodOf (fs : List Expr) : Expr := match fs.filter (fun c => !c.isOne) with | [] => Expr.one | cs => mulN cs

/-- Factors of a product other than the one at index `i`, as one term. -/
def without (es : List Expr) (i : Nat) : Expr := mulN ((es.zipIdx.filter (·.2 != i)).map (·.1))

/-- The reduction formulas for `∫ sinᵐu cosⁿu dx`, `u` linear in `x` with coefficient `a`:
`∫ sᵐcⁿ = −sᵐ⁻¹cⁿ⁺¹/(a(m+n)) + (m−1)/(m+n) ∫ sᵐ⁻²cⁿ` (on the sine, when `m ≥ 2`) and its mirror on
the cosine — each is integration by parts followed by solving for the integral. The boundary term,
the integrand left, its coefficient, and the text. -/
def trigReduce (u a : Expr) (m n : Nat) : Option (Expr × Expr × Expr × String) :=
  let S := Expr.fn "sin" [u]; let C := Expr.fn "cos" [u]
  let total := Expr.ofInt (m + n)
  if m ≥ 2 then
    some (Expr.neg (Expr.div (.mul [pw S (m - 1), pw C (n + 1)]) (.mul [a, total])), prodOf [pw S (m - 2), pw C n],
      .num (Q.ofRat (mkRat (m - 1 : Nat) (m + n))),
      s!"Reduction formula (integration by parts, then solving for the integral): $\\int \\sin^\{{m}}u\\cos^\{{n}}u\\,du = -\\frac\{\\sin^\{{m - 1}}u\\cos^\{{n + 1}}u}\{{m + n}} + \\frac\{{m - 1}}\{{m + n}}\\int \\sin^\{{m - 2}}u\\cos^\{{n}}u\\,du$, with $u = {u.toText}$.")
  else if n ≥ 2 then
    some (Expr.div (.mul [pw S (m + 1), pw C (n - 1)]) (.mul [a, total]), prodOf [pw S m, pw C (n - 2)],
      .num (Q.ofRat (mkRat (n - 1 : Nat) (m + n))),
      s!"Reduction formula (integration by parts, then solving for the integral): $\\int \\sin^\{{m}}u\\cos^\{{n}}u\\,du = \\frac\{\\sin^\{{m + 1}}u\\cos^\{{n - 1}}u}\{{m + n}} + \\frac\{{n - 1}}\{{m + n}}\\int \\sin^\{{m}}u\\cos^\{{n - 2}}u\\,du$, with $u = {u.toText}$.")
  else none

/-- `∫ sinᵐu cosⁿu dx` by a reduction formula, `rec` integrating what is left. The check accepts the
result because its derivative is the integrand modulo `cos² = 1 − sin²`, which `identNorm` applies
before comparing; dividing by the coefficient assumes it nonzero. -/
def trigPower (rec : Nat → Expr → Option Found) (fuel : Nat) (x : String) (f u : Expr) (m n : Nat) : Option Found := do
  let a ← linearCoeff x u
  let (boundary, rest, coeff, why) ← trigReduce u a m n
  let R ← rec fuel rest
  let F := Expr.add [boundary, .mul [coeff, R.F]]
  let cs := neCond a
  return { F, steps := #[mkStep "int.trig-power" why cs (integral f x) F] ++ R.steps, conds := cs ++ R.conds, checked := R.checked }

/-- A step on `∫ f dx` with no condition of its own. -/
def stepOf (x : String) (f : Expr) (rule text : String) (F : Expr) : Step := ⟨rule, text, [], integral f x, F, none⟩

/-- `int.constant`: `∫ c dx = c·x`. -/
def antiConst (x : String) (f : Expr) : Found :=
  let F := .mul [f, .var x]
  { F, steps := #[stepOf x f "int.constant" s!"A term free of ${x}$ is a constant: $\\int c \\, d{x} = c\\,{x}$." F] }

/-- `int.variable`: `∫ x dx = x²/2`. -/
def antiVar (x : String) (f : Expr) : Found :=
  let F := .mul [.num (Q.ofRat (mkRat 1 2)), .pow (.var x) (ofInt 2)]
  { F, steps := #[stepOf x f "int.variable" s!"$\\int {x} \\, d{x} = {x}^2/2$." F] }

/-- `int.sum`: the sum of the summands' antiderivatives. -/
def antiSum (x : String) (rec : Nat → Expr → Option Found) (fuel : Nat) (f : Expr) (es : List Expr) : Option Found := do
  let parts ← es.mapM (rec fuel)
  return { F := .add (parts.map (·.F)),
           steps := #[stepOf x f "int.sum" "The integral of a sum is the sum of the integrals." (.add (es.map (integral · x)))] ++ parts.foldl (fun acc p => acc ++ p.steps) #[],
           conds := parts.flatMap (·.conds), checked := parts.any (·.checked) }

/-- `int.constant-multiple`: the factors free of `x` (`cs`) times an antiderivative of the rest. -/
def antiConstMul (x : String) (rec : Nat → Expr → Option Found) (fuel : Nat) (f : Expr) (rest cs : List Expr) : Option Found := do
  let g := mulN rest
  let r ← rec fuel g
  return { r with F := .mul (cs ++ [r.F]), steps := #[stepOf x f "int.constant-multiple" "Constant factors move outside the integral." (.mul (cs ++ [integral g x]))] ++ r.steps }

/-- Integration by parts, a logarithm first, else a power of the variable: `∫ u dv = uv − ∫ v du`. -/
def byParts (simp : Expr → Option Expr) (x : String) (rec : Nat → Expr → Option Found) (fuel : Nat) (f : Expr) (es : List Expr) : Option Found := do
  if fuel = 0 then none else
  let isLog : Expr → Bool | .fn "ln" [_] => true | _ => false
  let isPoly : Expr → Bool | .var y => y == x | .pow (.var y) (.num n) => y == x && n.isInt && !n.isNeg | _ => false
  let (u, i) ← (es.zipIdx.find? (isLog ·.1)) <|> (es.zipIdx.find? (isPoly ·.1))
  let dv := without es i
  let v ← rec fuel dv
  let du ← simp (D u x)
  let vdu ← simp (.mul [v.F, du])
  let inner ← rec (fuel - 1) vdu
  let F := Expr.sub (.mul [u, v.F]) inner.F
  return { F, steps := #[stepOf x f "int.by-parts" s!"Integration by parts, $\\int u\\,dv = uv - \\int v\\,du$, with $u = {u.toText}$ and $dv = {dv.toText}\\,d{x}$, so $v = {v.F.toText}$ and $du = ({du.toText})\\,d{x}$." F] ++ v.steps ++ inner.steps,
           conds := v.conds ++ inner.conds }

/-- u-substitution: one factor is `H'(g)` for a table or power `H`, the rest is `c·g'`; else a factor
`g` itself, as `g¹`. -/
def bySubst (simp : Expr → Option Expr) (x : String) (f : Expr) (es : List Expr) : Option Found :=
  let trySubst (i : Nat) (w G : Expr) (why : String) : Option Found := do
    if !w.dependsOn x then none else
    let w' ← simp (D w x)
    let ratio ← simp (Expr.div (without es i) w')
    if ratio.dependsOn x then none else
    let F := .mul [ratio, G]
    return { F, steps := #[stepOf x f "int.substitution" s!"Substitution $u = {w.toText}$, $du = ({w'.toText})\\,d{x}$: the other factors are $({ratio.toText})\\,du$, so this is $({ratio.toText}) \\int H'(u)\\,du$ with {why}." F] }
  (es.zipIdx.findSome? fun (g, i) => match g with
    | .fn h [w] => (table h w).bind fun (G, why, _) => trySubst i w G why
    | .pow w n => if !n.dependsOn x then let (G, why, _) := powerRule w n; trySubst i w G why else none
    | _ => none)
  <|> (es.zipIdx.findSome? fun (g, i) => match g with
    | .var _ => none
    | w => let (G, why, _) := powerRule w Expr.one; trySubst i w G why)

/-- A product with no constant factor: u-substitution, a power of sine and cosine, or integration by
parts. The first and the last build on `simp`'s outputs, so their results are marked `checked`. -/
def antiProduct (simp : Expr → Option Expr) (x : String) (rec : Nat → Expr → Option Found) (fuel : Nat) (f : Expr) (es : List Expr) : Option Found :=
  match bySubst simp x f es with
  | some r => some { r with checked := true }
  | none =>
    match trigPowers es with
    | some (u, m, n) => trigPower rec fuel x f u m n
    | none => (byParts simp x rec fuel f es).map fun r => { r with checked := true }

/-- `int.exp-power`: `(eᵘ)ᵏ = eᵏᵘ`, distributed (`Expand.dist`), and then the table applies to the
linear argument. -/
def antiExpPower (x : String) (rec : Nat → Expr → Option Found) (fuel : Nat) (f u e : Expr) : Option Found := do
  let w := Expand.dist (.mul [e, u])
  let g : Expr := .fn "exp" [w]
  let r ← rec fuel g
  return { r with steps := #[⟨"int.exp-power", s!"$(e^u)^k = e^\{k u}$: the integrand is $\\exp({w.toText})$.", [], integral f x, integral g x, none⟩] ++ r.steps }

/-- `int.table` for `sec² u`, written `cos(u)^(-2)`: `tan u`, assuming `cos u ≠ 0`. -/
def antiSecSq (x : String) (f u : Expr) : Option Found := do
  let a ← linearCoeff x u
  let cs := [ICond.cosNe u]
  let (F, ss, ca) := substitute x f (.fn "tan" [u]) a
  return { F, steps := #[mkStep "int.table" "$\\int \\sec^2 u \\, du = \\tan u$" cs (integral f x) (if a.isOne then .fn "tan" [u] else Expr.div (.fn "tan" [u]) a)] ++ ss,
           conds := cs ++ ca }

/-- `int.power`: `∫ bⁿ dx` for `b` linear in `x` and `n` free of it. -/
def antiPower (x : String) (f b e : Expr) : Option Found := do
  let a ← linearCoeff x b
  let (G, why, cs) := powerRule b e
  let (F, ss, ca) := substitute x f G a
  return { F, steps := #[mkStep "int.power" why cs (integral f x) (if a.isOne then G else Expr.div G a)] ++ ss, conds := cs ++ ca }

/-- `int.exponential`: `∫ bᵉ dx = bᵉ/ln b` for `b` free of `x` and `e` linear in it. -/
def antiExponential (x : String) (f b e : Expr) : Option Found := do
  let a ← linearCoeff x e
  let G := Expr.div (.pow b e) (.fn "ln" [b])
  let cs := baseConds b
  let (F, ss, ca) := substitute x f G a
  return { F, steps := #[mkStep "int.exponential" "$\\int a^u \\, du = a^u / \\ln a$." cs (integral f x) (if a.isOne then G else Expr.div G a)] ++ ss,
           conds := cs ++ ca }

/-- A power `bᵉ`. -/
def antiPow (x : String) (rec : Nat → Expr → Option Found) (fuel : Nat) (f b e : Expr) : Option Found :=
  if !e.dependsOn x then
    match b with
    | .fn "exp" [u] => antiExpPower x rec fuel f u e
    | .fn "cos" [u] =>
      if e.isNumEq (Q.ofInt (-2)) then antiSecSq x f u
      else match trigPowers [f] with
        | some (u, m, n) => trigPower rec fuel x f u m n
        | none => none
    | .fn "sin" [_] =>
      match trigPowers [f] with
      | some (u, m, n) => trigPower rec fuel x f u m n
      | none => none
    | _ =>
      match invTrig x f b e with
      | some (F, steps) => some { F, steps, checked := true }
      | none => antiPower x f b e
  else if !b.dependsOn x then antiExponential x f b e
  else none

/-- `int.table`: an elementary function of `u = a·x + b`. -/
def antiFn (x : String) (f : Expr) (g : String) (u : Expr) : Option Found := do
  let (G, why, cs) ← table g u
  let a ← linearCoeff x u
  let (F, ss, ca) := substitute x f G a
  return { F, steps := #[mkStep "int.table" why cs (integral f x) (if a.isOne then G else Expr.div G a)] ++ ss, conds := cs ++ ca }

/-- One level of the finder: a candidate antiderivative of `f` in `x`, with the steps that found it,
or `none`, given `rec`, which finds them for the sub-integrands (`rec fuel g`). `simp` normalizes
(and, applied to `diff`, differentiates); `fuel` bounds the depth of integration by parts. -/
def antiStep (simp : Expr → Option Expr) (x : String) (rec : Nat → Expr → Option Found) (fuel : Nat) (f : Expr) : Option Found :=
  if !f.dependsOn x then some (antiConst x f)
  else match f with
  | .var _ => some (antiVar x f)
  | .add es => antiSum x rec fuel f es
  | .mul es =>
    match es.partition (·.dependsOn x) with
    | (rest, cs) => if !cs.isEmpty then antiConstMul x rec fuel f rest cs else antiProduct simp x rec fuel f es
  | .pow b e => antiPow x rec fuel f b e
  | .fn g [u] => antiFn x f g u
  | _ => none

/-- The finder: `antiStep` with itself as the recursion, at most `depth` levels deep. -/
def anti (simp : Expr → Option Expr) (x : String) : Nat → Nat → Expr → Option Found
  | 0, _, _ => none
  | d + 1, fuel, f => antiStep simp x (anti simp x d) fuel f

/-- The depth bound `findAnti` gives `anti`: far beyond what a sum, a product and a reduction
formula nest to (`sin^m` takes `m/2` levels). -/
def maxDepth : Nat := 200

end Anti
end MathEngine
