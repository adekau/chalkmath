import MathEngine.DiffRules
import MathEngine.ExpandRules
/-!
# `int.*` — a small antiderivative finder (M8), deliberately unverified

Nothing here is proved, and nothing needs to be: the command that uses it (`cmdIntegrate`,
Pipeline.lean) differentiates whatever comes back and accepts it only if the derivative normalizes
to the integrand. A wrong rule here costs a refused evaluation, never a wrong answer — the checker,
not the finder, carries the claim (`cmdIntegrate_spec`, Integrate.lean). That is the shape of the
milestone: a verified *checker* of integrals, not a verified integrator.

Covered: constants, the variable, sums, constant factors, powers `u^n` (`ln u` at `n = −1`),
exponentials `a^u`, the elementary table (sin, cos, exp, ln, tan, arctan, arcsin, arccos, and
sec² as `cos^(-2)`), each with `u = a·x + b`; `1/(k + c·u²)` as an arctangent and `1/√(k − c·u²)` as an arcsine; then
for products, u-substitution (`∫ c·g'·H'(g) = c·H(g)`) and integration by parts (LIATE: a
logarithm first, else a power of the variable, a few levels deep). The derivatives those two
need come from the caller's normalizer, so the finder never differentiates on its own.
Every step records `∫ g dx` as its `before` and the antiderivative found as its `after`.
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

/-- Antiderivatives of the elementary functions in their argument. -/
def table (g : String) (u : Expr) : Option (Expr × String) :=
  match g with
  | "sin" => some (neg (.fn "cos" [u]), "$\\int \\sin u \\, du = -\\cos u$")
  | "cos" => some (.fn "sin" [u], "$\\int \\cos u \\, du = \\sin u$")
  | "exp" => some (.fn "exp" [u], "$\\int e^u \\, du = e^u$")
  | "ln" => some (sub (.mul [u, .fn "ln" [u]]) u, "$\\int \\ln u \\, du = u \\ln u - u$")
  | "tan" => some (neg (.fn "ln" [.fn "cos" [u]]), "$\\int \\tan u \\, du = -\\ln \\cos u$")
  | "arctan" => some (sub (.mul [u, .fn "arctan" [u]]) (.mul [.num (Q.ofRat (mkRat 1 2)), .fn "ln" [.add [Expr.one, .pow u (ofInt 2)]]]),
      "$\\int \\arctan u \\, du = u \\arctan u - \\tfrac12 \\ln(1 + u^2)$ (by parts)")
  | "arcsin" => some (.add [.mul [u, .fn "arcsin" [u]], .pow (sub Expr.one (.pow u (ofInt 2))) (.num (Q.ofRat (mkRat 1 2)))],
      "$\\int \\arcsin u \\, du = u \\arcsin u + \\sqrt{1 - u^2}$ (by parts)")
  | "arccos" => some (sub (.mul [u, .fn "arccos" [u]]) (.pow (sub Expr.one (.pow u (ofInt 2))) (.num (Q.ofRat (mkRat 1 2)))),
      "$\\int \\arccos u \\, du = u \\arccos u - \\sqrt{1 - u^2}$ (by parts)")
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

/-- `∫ u^n du` for an exponent free of the variable: the power rule, or `ln u` at `n = −1`. -/
def powerRule (u n : Expr) : Expr × String :=
  if n.isNumEq Q.minusOne then (.fn "ln" [u], "$\\int u^{-1} \\, du = \\ln u$")
  else match n with
    | .num q => let n1 := q.add Q.one; (.mul [.num (Q.one.div n1), .pow u (.num n1)], "$\\int u^n \\, du = u^{n+1}/(n+1)$")
    | _ => let n1 := .add [n, Expr.one]; (.mul [.pow n1 Expr.minusOne, .pow u n1], "$\\int u^n \\, du = u^{n+1}/(n+1)$ (assuming $n \\neq -1$)")

/-- `∫ g(a·x + b) dx = (1/a) G(a·x + b)`: the substitution step, if the coefficient is not 1. -/
def substitute (x : String) (f G : Expr) (a : Expr) : Expr × Array Step :=
  if a.isOne then (G, #[])
  else (Expr.div G a, #[⟨"int.linear-substitution", s!"Linear substitution: with $u = {(f.children.headD f).toText}$, $du = ({a.toText})\\,d{x}$, so the integral in $x$ is $1/({a.toText})$ times the integral in $u$.", [], integral f x, Expr.div G a, none⟩])

/-- `sin^m u · cos^n u` among the factors, all with the same `u`: `(u, m, n)`. Nothing else may be
present (constants have been pulled out by then). -/
def trigPowers : List Expr → Option (Expr × Nat × Nat) := go none 0 0
where
  go (u? : Option Expr) (m n : Nat) : List Expr → Option (Expr × Nat × Nat)
    | [] => u?.map fun u => (u, m, n)
    | f :: fs =>
      let (base, k) : Expr × Nat := match f with
        | .pow b (.num q) => if q.isInt && q.val.num ≥ 1 then (b, q.val.num.toNat) else (f, 0)
        | _ => (f, 1)
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

mutual
/-- `∫ sinᵐu cosⁿu dx` for `u` linear in `x` (coefficient `a`), by the reduction formulas
`∫ sᵐcⁿ = −sᵐ⁻¹cⁿ⁺¹/(a(m+n)) + (m−1)/(m+n) ∫ sᵐ⁻²cⁿ` (on the sine, when `m ≥ 2`) and its mirror on
the cosine — each is integration by parts followed by solving for the integral. The check accepts
the result because its derivative is the integrand modulo `cos² = 1 − sin²`, which `identNorm`
applies before comparing. -/
partial def trigReduce (simp : Expr → Option Expr) (x : String) (fuel : Nat) (f u : Expr) (m n : Nat) : Option (Expr × Array Step) := do
  let a ← linearCoeff x u
  let S := Expr.fn "sin" [u]; let C := Expr.fn "cos" [u]
  let total := Expr.ofInt (m + n)
  let onSine := m ≥ 2
  if !onSine && n < 2 then none else
  let (boundary, rest, k, why) :=
    if onSine then
      (Expr.neg (Expr.div (.mul [pw S (m - 1), pw C (n + 1)]) (.mul [a, total])), prodOf [pw S (m - 2), pw C n], m - 1,
       s!"Reduction formula (integration by parts, then solving for the integral): $\\int \\sin^\{{m}}u\\cos^\{{n}}u\\,du = -\\frac\{\\sin^\{{m - 1}}u\\cos^\{{n + 1}}u}\{{m + n}} + \\frac\{{m - 1}}\{{m + n}}\\int \\sin^\{{m - 2}}u\\cos^\{{n}}u\\,du$, with $u = {u.toText}$.")
    else
      (Expr.div (.mul [pw S (m + 1), pw C (n - 1)]) (.mul [a, total]), prodOf [pw S m, pw C (n - 2)], n - 1,
       s!"Reduction formula (integration by parts, then solving for the integral): $\\int \\sin^\{{m}}u\\cos^\{{n}}u\\,du = \\frac\{\\sin^\{{m + 1}}u\\cos^\{{n - 1}}u}\{{m + n}} + \\frac\{{n - 1}}\{{m + n}}\\int \\sin^\{{m}}u\\cos^\{{n - 2}}u\\,du$, with $u = {u.toText}$.")
  let (R, sub) ← anti simp x fuel rest
  let coeff : Expr := .num (Q.ofRat (mkRat k (m + n)))
  let F := Expr.add [boundary, .mul [coeff, R]]
  return (F, #[⟨"int.trig-power", why, [], integral f x, F, none⟩] ++ sub)

/-- A candidate antiderivative of `f` in `x`, with the steps that found it, or `none`. `simp`
normalizes (and, applied to `diff`, differentiates); `fuel` bounds the depth of integration by
parts. -/
partial def anti (simp : Expr → Option Expr) (x : String) (fuel : Nat) (f : Expr) : Option (Expr × Array Step) := do
  let step (rule text : String) (F : Expr) : Step := ⟨rule, text, [], integral f x, F, none⟩
  if !f.dependsOn x then
    let F := .mul [f, .var x]
    return (F, #[step "int.constant" s!"A term free of ${x}$ is a constant: $\\int c \\, d{x} = c\\,{x}$." F])
  match f with
  | .var _ =>
    let F := .mul [.num (Q.ofRat (mkRat 1 2)), .pow (.var x) (ofInt 2)]
    return (F, #[step "int.variable" s!"$\\int {x} \\, d{x} = {x}^2/2$." F])
  | .add es =>
    let parts ← es.mapM (anti simp x fuel)
    let F := .add (parts.map (·.1))
    let sub := parts.foldl (fun acc p => acc ++ p.2) #[]
    return (F, #[step "int.sum" "The integral of a sum is the sum of the integrals." (.add (es.map (integral · x)))] ++ sub)
  | .mul es =>
    match es.partition (·.dependsOn x) with
    | (rest, cs) =>
      if !cs.isEmpty then
        let g := mulN rest
        let (G, sub) ← anti simp x fuel g
        let F := .mul (cs ++ [G])
        return (F, #[step "int.constant-multiple" "Constant factors move outside the integral." (.mul (cs ++ [integral g x]))] ++ sub)
      else
        -- u-substitution: one factor is H'(g) for a table or power H, the rest is c·g'
        let trySubst (i : Nat) (w G : Expr) (why : String) : Option (Expr × Array Step) := do
          if !w.dependsOn x then none else
          let w' ← simp (D w x)
          let ratio ← simp (Expr.div (without es i) w')
          if ratio.dependsOn x then none else
          let F := .mul [ratio, G]
          return (F, #[step "int.substitution" s!"Substitution $u = {w.toText}$, $du = ({w'.toText})\\,d{x}$: the other factors are $({ratio.toText})\\,du$, so this is $({ratio.toText}) \\int H'(u)\\,du$ with {why}." F])
        -- a factor H'(g) with H from the table or a power, the rest c·g'; else a factor g itself as g¹
        let bySubst : Option (Expr × Array Step) :=
          (es.zipIdx.findSome? fun (g, i) => match g with
            | .fn h [w] => (table h w).bind fun (G, why) => trySubst i w G why
            | .pow w n => if !n.dependsOn x then let (G, why) := powerRule w n; trySubst i w G why else none
            | _ => none)
          <|> (es.zipIdx.findSome? fun (g, i) => match g with
            | .var _ => none
            | w => let (G, why) := powerRule w Expr.one; trySubst i w G why)
        match bySubst with
        | some r => return r
        | none =>
          match trigPowers es with
          | some (u, m, n) => trigReduce simp x fuel f u m n
          | none =>
          -- integration by parts, a logarithm first, else a power of the variable
          if fuel = 0 then none else
          let isLog : Expr → Bool | .fn "ln" [_] => true | _ => false
          let isPoly : Expr → Bool | .var y => y == x | .pow (.var y) (.num n) => y == x && n.isInt && !n.isNeg | _ => false
          let (u, i) ← (es.zipIdx.find? (isLog ·.1)) <|> (es.zipIdx.find? (isPoly ·.1))
          let dv := without es i
          let (v, vsteps) ← anti simp x fuel dv
          let du ← simp (D u x)
          let vdu ← simp (.mul [v, du])
          let (inner, isteps) ← anti simp x (fuel - 1) vdu
          let F := Expr.sub (.mul [u, v]) inner
          return (F, #[step "int.by-parts" s!"Integration by parts, $\\int u\\,dv = uv - \\int v\\,du$, with $u = {u.toText}$ and $dv = {dv.toText}\\,d{x}$, so $v = {v.toText}$ and $du = ({du.toText})\\,d{x}$." F] ++ vsteps ++ isteps)
  | .pow b e =>
    if !e.dependsOn x then
      match b with
      | .fn "exp" [u] =>
        -- exp(u)^k = exp(k·u): then the table applies to the linear argument
        let w ← simp (Expand.dist (.mul [e, u]))
        let g : Expr := .fn "exp" [w]
        let (G, sub) ← anti simp x fuel g
        return (G, #[⟨"int.exp-power", s!"$(e^u)^k = e^\{k u}$: the integrand is $\\exp({w.toText})$.", [], integral f x, integral g x, none⟩] ++ sub)
      | .fn "cos" [u] =>
        if e.isNumEq (Q.ofInt (-2)) then
          -- `sec² u`, written `cos(u)^(-2)`
          let a ← linearCoeff x u
          let (F, ss) := substitute x f (.fn "tan" [u]) a
          return (F, #[step "int.table" "$\\int \\sec^2 u \\, du = \\tan u$" (if a.isOne then .fn "tan" [u] else Expr.div (.fn "tan" [u]) a)] ++ ss)
        else
        match trigPowers [f] with
        | some (u, m, n) => trigReduce simp x fuel f u m n
        | none => none
      | .fn "sin" [_] =>
        match trigPowers [f] with
        | some (u, m, n) => trigReduce simp x fuel f u m n
        | none => none
      | _ =>
      match invTrig x f b e with
      | some r => return r
      | none =>
      let a ← linearCoeff x b
      let (G, why) := powerRule b e
      let (F, ss) := substitute x f G a
      return (F, #[step "int.power" why (if a.isOne then G else Expr.div G a)] ++ ss)
    else if !b.dependsOn x then
      let a ← linearCoeff x e
      let G := Expr.div (.pow b e) (.fn "ln" [b])
      let (F, ss) := substitute x f G a
      return (F, #[step "int.exponential" "$\\int a^u \\, du = a^u / \\ln a$." (if a.isOne then G else Expr.div G a)] ++ ss)
    else none
  | .fn g [u] =>
    let (G, why) ← table g u
    let a ← linearCoeff x u
    let (F, ss) := substitute x f G a
    return (F, #[step "int.table" why (if a.isOne then G else Expr.div G a)] ++ ss)
  | _ => none
end

end Anti
end MathEngine
