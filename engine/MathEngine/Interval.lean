import MathEngine.Expr
/-!
# Certified numerical values: interval arithmetic over ℚ

`N(e)` gives a decimal, and the decimal is certified. `ieval` evaluates the term once more, over the
rationals, to an interval `[lo, hi]` that contains its real value (`ieval_sound`,
`proofs/Proofs/Interval.lean`), and `certify` picks the most digits, up to 15, that the interval
pins down: a decimal `v` and a bound `u`, one unit in its last digit, with `|value − v| ≤ u`
(`certify_sound`).

How each operation keeps its interval honest:

- `+`, `−`, `·`, `1/x` are exact on rationals; afterwards each end is rounded outward to `prec` bits
  so the numbers stay small (`lower`, `upper`).
- `exp y` for `|y| ≤ 1` is the Taylor sum with its remainder (`Real.exp_bound`); a larger argument is
  halved `k` times and the result squared `k` times. `exp` is increasing, so an interval's image is
  its ends' images. The sum is itself taken in interval arithmetic (`expSumI`), each term the last
  times `y/(m+1)`, rounded outward: the exact sum's denominator grows to thousands of bits, which
  made `N` take seconds in the browser, whose runtime has no GMP.
- `sin y`, `cos y` for `|y| ≤ 1` are the imaginary and real parts of the Taylor sum of `exp(iy)`
  (`Complex.exp_bound`); a larger argument is halved and doubled back (`sin 2x = 2 sin x cos x`,
  `cos 2x = 2 cos² x − 1`). An interval's image is its midpoint's, widened by its radius: both are
  1-Lipschitz.
- `ln q` is pinned between two candidates `l` checked by `exp`: `exp l ≤ q` means `l ≤ ln q`.
- `sqrt q` is pinned between two candidates checked by squaring.
- `π` is Mathlib's twenty digits (`Real.pi_gt_d20`, `Real.pi_lt_d20`); `e` is `exp 1`.
- `b^x` is a power by an integer when `x` is one, a square root when `x = 1/2`, and `exp(x ln b)`
  when `b > 0`.

A term outside this (a variable, `sign` across zero, `tan` across a pole, a negative base under a
fractional power) gets no interval, and `N` says its value is a floating-point approximation.
-/
namespace MathEngine
namespace Ival

/-- `|y|`. -/
def rabs (y : Rat) : Rat := if y < 0 then -y else y

/-- An interval of rationals, `lo ≤ hi` where it means anything. -/
structure I where
  lo : Rat
  hi : Rat
  deriving Repr, Inhabited

/-- The working precision: bits kept below an end's leading bit. -/
def prec : Nat := 192

/-- `2 ^ k` for an integer `k`. -/
def pow2 (k : Int) : Rat :=
  if 0 ≤ k then ((2 ^ k.toNat : Nat) : Rat) else 1 / ((2 ^ (-k).toNat : Nat) : Rat)

/-- `⌊x / 2^k⌋ · 2^k`: `x` rounded down to a multiple of `2^k`. -/
def floorTo (k : Int) (x : Rat) : Rat :=
  let y := x / pow2 k
  ((y.num / (y.den : Int) : Int) : Rat) * pow2 k

/-- The exponent of the last bit kept of `x`. Any value would be sound; this one keeps `prec` bits. -/
def keepExp (x : Rat) : Int := (Nat.log2 x.num.natAbs : Int) - (Nat.log2 x.den : Int) - prec

def lower (x : Rat) : Rat := floorTo (keepExp x) x
def upper (x : Rat) : Rat := -floorTo (keepExp x) (-x)

def round (a : I) : I := ⟨lower a.lo, upper a.hi⟩
def point (q : Rat) : I := ⟨q, q⟩

def add (a b : I) : I := round ⟨a.lo + b.lo, a.hi + b.hi⟩
def neg (a : I) : I := ⟨-a.hi, -a.lo⟩
def mul (a b : I) : I :=
  let p := a.lo * b.lo
  let q := a.lo * b.hi
  let r := a.hi * b.lo
  let s := a.hi * b.hi
  round ⟨min (min p q) (min r s), max (max p q) (max r s)⟩
/-- `1/x`, when the interval keeps away from zero. -/
def inv (a : I) : Option I :=
  if 0 < a.lo ∨ a.hi < 0 then some (round ⟨1 / a.hi, 1 / a.lo⟩) else none
def npow (a : I) : Nat → I
  | 0 => point 1
  | n + 1 => mul (npow a n) a
def abs (a : I) : I :=
  if 0 ≤ a.lo then a else if a.hi ≤ 0 then neg a else ⟨0, max (-a.lo) a.hi⟩
def sign (a : I) : Option I :=
  if 0 < a.lo then some (point 1) else if a.hi < 0 then some (point (-1))
  else if a.lo = 0 ∧ a.hi = 0 then some (point 0) else none
/-- Widen by `r ≥ 0` on both sides. -/
def widen (a : I) (r : Rat) : I := round ⟨a.lo - r, a.hi + r⟩

/-! ## `exp`, `sin`, `cos` -/

/-- `n!` (core Lean has none; `fact_eq` in the proofs says it is Mathlib's). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- The number of Taylor terms. -/
def terms : Nat := 64

/-- `∑_{m<n} y^m / m!` -/
def expSum (y : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => expSum y n + y ^ n / (fact n : Rat)

/-- The real and imaginary parts of `∑_{m<n} (iy)^m / m!`. -/
def cosSum (y : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => cosSum y n + (if n % 2 = 0 then (if n % 4 = 0 then 1 else -1) * y ^ n / (fact n : Rat) else 0)
def sinSum (y : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sinSum y n + (if n % 2 = 1 then (if n % 4 = 1 then 1 else -1) * y ^ n / (fact n : Rat) else 0)

/-- `x` rounded up to 32 bits below its leading bit: small enough to raise to a power. -/
def coarseUp (x : Rat) : Rat := -floorTo ((Nat.log2 x.num.natAbs : Int) - (Nat.log2 x.den : Int) - 32) (-x)

/-- The Taylor remainder bound for `|y| ≤ 1`, `|y|^n (n+1) / (n! n)`, with `|y|` rounded up first. -/
def remainder (y : Rat) (n : Nat) : Rat := coarseUp (rabs y) ^ n * ((n + 1 : Nat) : Rat) / ((fact n * n : Nat) : Rat)

/-- `expSum` and `cosSum`, `sinSum` above are what the intervals below hold; these are what runs.
`expSumI y n` is an interval holding `expSum y n` and one holding the next term `y^n/n!`. -/
def expSumI (y : Rat) : Nat → I × I
  | 0 => (point 0, point 1)
  | n + 1 =>
    let st := expSumI y n
    (add st.1 st.2, mul st.2 (point (y / ((n + 1 : Nat) : Rat))))

/-- Intervals holding `cosSum y n`, `sinSum y n` and the next term's size `y^n/n!`. -/
def trigSumI (y : Rat) : Nat → I × I × I
  | 0 => (point 0, point 0, point 1)
  | n + 1 =>
    let p := trigSumI y n
    let t := p.2.2
    (if n % 2 = 0 then add p.1 (if n % 4 = 0 then t else neg t) else p.1,
     if n % 2 = 1 then add p.2.1 (if n % 4 = 1 then t else neg t) else p.2.1,
     mul t (point (y / ((n + 1 : Nat) : Rat))))

/-- How many halvings bring `q` into `[-1, 1]`. -/
def halvings (q : Rat) : Nat := Nat.log2 (q.num.natAbs / q.den) + 1

def sqN : Nat → I → I
  | 0, a => a
  | k + 1, a => sqN k (mul a a)

/-- `exp q`, `q` rational. -/
def expPoint (q : Rat) : Option I :=
  let k := halvings q
  let y := q / ((2 ^ k : Nat) : Rat)
  if rabs y ≤ 1 then
    let s := (expSumI y terms).1
    let r := remainder y terms
    some (sqN k (round ⟨s.lo - r, s.hi + r⟩))
  else none

/-- `f y`, reusing `f x = fx` when `y = x`: a point interval's two ends are computed once. -/
def again (f : Rat → Option I) (x y : Rat) (fx : I) : Option I := if y = x then some fx else f y

def expI (a : I) : Option I := do
  let l ← expPoint a.lo
  let h ← again expPoint a.lo a.hi l
  return ⟨l.lo, h.hi⟩

/-- Double an angle `k` times: `(sin, cos) ↦ (2 sin cos, 2 cos² − 1)`. -/
def dbl : Nat → I × I → I × I
  | 0, sc => sc
  | k + 1, (s, c) => dbl k (mul (point 2) (mul s c), add (mul (point 2) (mul c c)) (point (-1)))

/-- `(sin q, cos q)`, `q` rational. -/
def sinCosPoint (q : Rat) : Option (I × I) :=
  let k := halvings q
  let y := q / ((2 ^ k : Nat) : Rat)
  if rabs y ≤ 1 then
    let r := remainder y terms
    let cs := trigSumI y terms
    some (dbl k (round ⟨cs.2.1.lo - r, cs.2.1.hi + r⟩, round ⟨cs.1.lo - r, cs.1.hi + r⟩))
  else none

def mid (a : I) : Rat := (a.lo + a.hi) / 2
def rad (a : I) : Rat := (a.hi - a.lo) / 2

def sinI (a : I) : Option I := do
  let (s, _) ← sinCosPoint (mid a)
  return widen s (rad a)
def cosI (a : I) : Option I := do
  let (_, c) ← sinCosPoint (mid a)
  return widen c (rad a)

/-! ## `ln`, `sqrt` -/

/-- A rough `ln q`, for Newton's method to start from: the binary exponent times `ln 2`. -/
def lnGuess (q : Rat) : Rat :=
  ((Nat.log2 q.num.natAbs : Int) - (Nat.log2 q.den : Int)) * (6931471805599453 / 10000000000000000 : Rat)

/-- Newton's method for `ln q`: `l ↦ l + q·exp(−l) − 1`, on interval midpoints. -/
def lnNewton (q : Rat) : Nat → Rat → Rat
  | 0, l => l
  | n + 1, l =>
    match expPoint (-l) with
    | some e => lnNewton q n (lower (l + q * mid e - 1))
    | none => l

/-- A floating-point `ln q`, about fifteen digits, for Newton's method to start from; none where a
double overflows. Any start would be sound: the candidates are checked with `exp`. -/
def lnStart (q : Rat) : Option Rat :=
  (Q.ofFloat (Float.log (Float.ofInt q.num) - Float.log (Float.ofNat q.den))).map (·.val)

/-- Newton's answer for `ln q`. From the floating-point start three steps are enough (the error
squares each step: 2⁻⁵⁰, 2⁻¹⁰⁰, 2⁻²⁰⁰); from the rough one, twelve. -/
def lnApprox (q : Rat) : Rat :=
  match lnStart q with
  | some l => lnNewton q 3 l
  | none => lnNewton q 12 (lnGuess q)

/-- `ln q` for `q > 0`: candidates either side of Newton's answer, each checked with `exp`. -/
def lnPoint (q : Rat) : Option I :=
  if 0 < q then
    let l := lnApprox q
    let ε := (1 + rabs l) / ((2 ^ 170 : Nat) : Rat)
    let a := lower (l - ε)
    let b := upper (l + ε)
    match expPoint a, expPoint b with
    | some ea, some eb => if ea.hi ≤ q ∧ q ≤ eb.lo then some ⟨a, b⟩ else none
    | _, _ => none
  else none

def lnI (a : I) : Option I := do
  let l ← lnPoint a.lo
  let h ← again lnPoint a.lo a.hi l
  return ⟨l.lo, h.hi⟩

/-- Newton's method for `√q`: `s ↦ (s + q/s)/2`. -/
def sqrtNewton (q : Rat) : Nat → Rat → Rat
  | 0, s => s
  | n + 1, s => if s ≤ 0 then s else sqrtNewton q n (lower ((s + q / s) / 2))

/-- `√q` for `q ≥ 0`: candidates either side of Newton's answer, checked by squaring. -/
def sqrtPoint (q : Rat) : Option I :=
  if q = 0 then some (point 0) else
  if 0 < q then
    let s := sqrtNewton q 14 (pow2 (((Nat.log2 q.num.natAbs : Int) - (Nat.log2 q.den : Int)) / 2))
    let ε := (1 + rabs s) / ((2 ^ 170 : Nat) : Rat)
    let a := max 0 (lower (s - ε))
    let b := upper (s + ε)
    if a * a ≤ q ∧ q ≤ b * b ∧ 0 ≤ b then some ⟨a, b⟩ else none
  else none

def sqrtI (a : I) : Option I := do
  if a.lo < 0 then none
  let l ← sqrtPoint a.lo
  let h ← sqrtPoint a.hi
  return ⟨l.lo, h.hi⟩

/-! ## Constants and terms -/

/-- `π`, to twenty digits (`Real.pi_gt_d20`, `Real.pi_lt_d20`). -/
def piI : I := ⟨314159265358979323846 / 100000000000000000000, 314159265358979323847 / 100000000000000000000⟩

/-- An integer, if the interval is exactly one. -/
def asInt (a : I) : Option Int := if a.lo = a.hi ∧ a.lo.den = 1 then some a.lo.num else none

/-- `b ^ x`: a power by an integer, a square root for `x = 1/2` (how `sqrt` is written), or
`exp(x ln b)` for `b > 0`. -/
def powI (b x : I) : Option I :=
  match asInt x with
  | some n => if 0 ≤ n then some (npow b n.toNat) else inv (npow b n.natAbs)
  | none =>
    if x.lo = 1 / 2 ∧ x.hi = 1 / 2 then sqrtI b
    else if 0 < b.lo then do expI (mul x (← lnI b)) else none

/-! ## `arctan` -/

/-- Newton's method for `arctan q`: `θ ↦ θ − (sin θ cos θ − q cos² θ)`, on midpoints. -/
def atanNewton (q : Rat) : Nat → Rat → Rat
  | 0, θ => θ
  | n + 1, θ =>
    match sinCosPoint θ with
    | some (s, c) => let s := mid s; let c := mid c; atanNewton q n (lower (θ - (s * c - q * c * c)))
    | none => θ

/-- Candidates for `arctan q` either side of Newton's answer, from a floating-point start. Any would be
sound: `atanCheck` decides. -/
def atanCandidates (q : Rat) : Rat × Rat :=
  let start : Rat := match Q.ofFloat (Float.atan (Float.ofInt q.num / Float.ofNat q.den)) with
    | some r => r.val | none => 0
  let θ := atanNewton q 4 start
  let ε := (1 + rabs θ) / ((2 ^ 170 : Nat) : Rat)
  (lower (θ - ε), upper (θ + ε))

/-- `[a, b]` holds `arctan q` if both are inside `(−π/2, π/2)` and `tan a ≤ q ≤ tan b`, checked with
`sin` and `cos` (`cos` positive there). -/
def atanCheck (q a b : Rat) : Option I :=
  if -(piI.lo / 2) < a ∧ a ≤ b ∧ b < piI.lo / 2 then
    match sinCosPoint a, sinCosPoint b with
    | some (sa, ca), some (sb, cb) =>
      match inv ca, inv cb with
      | some ia, some ib =>
        if (mul sa ia).hi ≤ q ∧ q ≤ (mul sb ib).lo then some ⟨a, b⟩ else none
      | _, _ => none
    | _, _ => none
  else none

/-- `arctan q`, certified. -/
def atanPoint (q : Rat) : Option I := atanCheck q (atanCandidates q).1 (atanCandidates q).2

def atanI (a : I) : Option I := do
  let l ← atanPoint a.lo
  let h ← again atanPoint a.lo a.hi l
  return ⟨l.lo, h.hi⟩

def fnI (f : String) (a : I) : Option I :=
  match f with
  | "sin" => sinI a
  | "cos" => cosI a
  | "tan" => do let s ← sinI a; let c ← cosI a; return mul s (← inv c)
  | "exp" => expI a
  | "ln" => if 0 < a.lo then lnI a else none
  | "log" => if 0 < a.lo then do let l ← lnI a; let t ← lnI (point 10); return mul l (← inv t) else none
  | "sqrt" => sqrtI a
  | "arctan" => atanI a
  | "abs" => some (abs a)
  | "sign" => sign a
  | _ => none

mutual
  /-- An interval holding the term's real value, where the constants `π` and `e` have theirs. -/
  def ieval : Expr → Option I
    | .num q => some (point q.val)
    | .var x =>
      if x = "π" then some piI else if x = "e" then expPoint 1 else none
    | .add es => ievalSum es
    | .mul es => ievalProd es
    | .pow b e => do powI (← ieval b) (← ieval e)
    | .fn f [] => if f = "π" then some piI else none
    | .fn f [a] => do fnI f (← ieval a)
    | .fn _ _ => none
    | .matrix _ => none
  def ievalSum : List Expr → Option I
    | [] => some (point 0)
    | e :: es => do return add (← ieval e) (← ievalSum es)
  def ievalProd : List Expr → Option I
    | [] => some (point 1)
    | e :: es => do return mul (← ieval e) (← ievalProd es)
end

/-! ## Digits -/

/-- `10 ^ j`, for an integer `j`. -/
def pow10 (j : Int) : Rat := if 0 ≤ j then ((10 ^ j.toNat : Nat) : Rat) else 1 / ((10 ^ (-j).toNat : Nat) : Rat)

/-- `p` significant digits of the interval's midpoint, `v`, with a unit in their last place, `u`, if
the interval lies within `u` of `v`. -/
def tryDigits (a : I) (p : Nat) : Option (Rat × Rat) :=
  let m := mid a
  if m = 0 then none else
  let nk := Q.sigDigits (rabs m) p
  let v : Rat := (if m < 0 then -1 else 1) * (nk.1 : Rat) * pow10 (-nk.2)
  let u := pow10 (-nk.2)
  if v - u ≤ a.lo ∧ a.hi ≤ v + u then some (v, u) else none

/-- The most digits, up to 15, that the interval pins down: a decimal `v` and a bound `u` with the
interval inside `[v − u, v + u]`. Across zero, `0` and the interval's reach. -/
def certify (a : I) : Option (Rat × Rat) :=
  let tries := ((List.range 15).reverse.map (· + 1)).filterMap (tryDigits a)
  match tries.head? with
  | some vu => some vu
  | none =>
    if a.lo ≤ 0 ∧ 0 ≤ a.hi then
      let r := max (-a.lo) a.hi
      if r = 0 then some (0, 0) else
      -- the least power of ten at or above the reach
      let j := ((List.range 700).map (fun (i : Nat) => (i : Int) - 350)).find? (fun j => r ≤ pow10 j)
      match j with
      | some j => some (0, pow10 j)
      | none => none
    else none

/-- A power of ten as TeX, `10^{-14}`; anything else as a decimal. -/
def tenText (u : Rat) : String :=
  match ((List.range 1401).map (fun (i : Nat) => (i : Int) - 700)).find? (fun j => pow10 j = u) with
  | some 0 => "1"
  | some j => s!"10^\{{j}}"
  | none => (Q.ofRat u true).toDecimal

/-! ## Complex values: a rectangle, an interval for each part

`cieval` holds a term's complex value (`evalC`, the principal branch) in a rectangle
(`cieval_sound`, `proofs/Proofs/IntervalC.lean`): `+`, `·`, `1/z` and integer powers by their
formulas on the parts; `exp`, `sin`, `cos` through `exp`, `sin`, `cos`, `cosh`, `sinh` of the parts;
`abs`, `conj`, `re`, `im`; and `ln`, `sqrt` and real powers where the argument is real, of either sign
(`ln(-1) = πi`, `sqrt(-4) = 2i`, `(-8)^(1/3) = 2 e^(πi/3)`). A complex argument to `ln`, and any other
base under a non-integer power (`exp(e · ln b)`), take their angle from a certified `arctan` (`cargI`),
away from the branch cut along the negative real axis, where the argument jumps. -/

/-- A rectangle: the real part's interval and the imaginary part's. -/
abbrev C := I × I

def creal (a : I) : C := (a, point 0)
/-- The imaginary part is exactly 0. -/
def isReal (z : C) : Bool := z.2.lo = 0 && z.2.hi = 0

def cadd (z w : C) : C := (add z.1 w.1, add z.2 w.2)
def cmul (z w : C) : C := (add (mul z.1 w.1) (neg (mul z.2 w.2)), add (mul z.1 w.2) (mul z.2 w.1))
def cinv (z : C) : Option C := do
  let r ← inv (add (mul z.1 z.1) (mul z.2 z.2))
  return (mul z.1 r, neg (mul z.2 r))
def cnpow (z : C) : Nat → C
  | 0 => creal (point 1)
  | n + 1 => cmul (cnpow z n) z

/-- `cosh` and `sinh` of an interval, through `exp`. -/
def coshI (a : I) : Option I := do
  let p ← expI a; let m ← expI (neg a)
  return mul (point (1 / 2)) (add p m)
def sinhI (a : I) : Option I := do
  let p ← expI a; let m ← expI (neg a)
  return mul (point (1 / 2)) (add p (neg m))

def cexp (z : C) : Option C := do
  let e ← expI z.1; let c ← cosI z.2; let s ← sinI z.2
  return (mul e c, mul e s)
def csin (z : C) : Option C := do
  let s ← sinI z.1; let c ← cosI z.1; let ch ← coshI z.2; let sh ← sinhI z.2
  return (mul s ch, mul c sh)
def ccos (z : C) : Option C := do
  let s ← sinI z.1; let c ← cosI z.1; let ch ← coshI z.2; let sh ← sinhI z.2
  return (mul c ch, neg (mul s sh))

/-- The argument (principal, in `(−π, π]`) of every number in the rectangle, away from the branch cut:
`arctan(y/x)` right of the imaginary axis, `±π/2 − arctan(x/y)` above or below the real one. -/
def cargI (z : C) : Option I :=
  if 0 < z.1.lo then do atanI (mul z.2 (← inv z.1))
  else if 0 < z.2.lo then do return add (mul (point (1 / 2)) piI) (neg (← atanI (mul z.1 (← inv z.2))))
  else if z.2.hi < 0 then do return add (neg (mul (point (1 / 2)) piI)) (neg (← atanI (mul z.1 (← inv z.2))))
  else none

/-- The principal logarithm: `ln|z| = ln(x² + y²)/2`, and the argument. -/
def clnI (z : C) : Option C := do
  let n := add (mul z.1 z.1) (mul z.2 z.2)
  if 0 < n.lo then return (mul (point (1 / 2)) (← lnI n), ← cargI z) else none

/-- `|x|^y · e^(πiy)`, the principal value of `x^y` for a negative real `x` and a real `y`. -/
def negRealPow (x y : I) : Option C := do
  let m ← powI (neg x) y
  let θ := mul piI y
  return (mul m (← cosI θ), mul m (← sinI θ))

def cpowI (b e : C) : Option C :=
  match asInt e.1, isReal e with
  | some n, true => if 0 ≤ n then some (cnpow b n.toNat) else cinv (cnpow b n.natAbs)
  | _, _ =>
    if isReal b && isReal e && 0 < b.1.lo then do return creal (← powI b.1 e.1)
    else if isReal b && isReal e && b.1.hi < 0 then negRealPow b.1 e.1
    -- otherwise `exp(e · ln b)`, for `b ≠ 0` off the branch cut
    else do cexp (cmul (← clnI b) e)

def cfnI (f : String) (z : C) : Option C :=
  match f with
  | "exp" => cexp z
  | "sin" => csin z
  | "cos" => ccos z
  | "tan" => do let s ← csin z; let c ← ccos z; return cmul s (← cinv c)
  | "abs" => do return creal (← sqrtI (add (mul z.1 z.1) (mul z.2 z.2)))
  | "conj" => some (z.1, neg z.2)
  | "re" => some (creal z.1)
  | "im" => some (creal z.2)
  | "ln" =>
    if !isReal z then clnI z
    else if 0 < z.1.lo then do return creal (← lnI z.1)
    else if z.1.hi < 0 then do return (← lnI (neg z.1), piI)
    else none
  | "sqrt" =>
    if !isReal z then none
    else if 0 ≤ z.1.lo then do return creal (← sqrtI z.1)
    else if z.1.hi < 0 then do return (point 0, ← sqrtI (neg z.1))
    else none
  | _ => none

mutual
  /-- A rectangle holding the term's complex value, where `π` and `e` have theirs. -/
  def cieval : Expr → Option C
    | .num q => some (creal (point q.val))
    | .var x =>
      if x = "π" then some (creal piI) else if x = "e" then (expPoint 1).map creal else none
    | .add es => cievalSum es
    | .mul es => cievalProd es
    | .pow b e => do cpowI (← cieval b) (← cieval e)
    | .fn f [] => if f = "π" then some (creal piI) else if f = "i" then some (point 0, point 1) else none
    | .fn f [a] => do cfnI f (← cieval a)
    | .fn _ _ => none
    | .matrix _ => none
  def cievalSum : List Expr → Option C
    | [] => some (creal (point 0))
    | e :: es => do return cadd (← cieval e) (← cievalSum es)
  def cievalProd : List Expr → Option C
    | [] => some (creal (point 1))
    | e :: es => do return cmul (← cieval e) (← cievalProd es)
end

/-- Both parts' digits, each within a unit of its last place. -/
def ccertify (z : C) : Option ((Rat × Rat) × (Rat × Rat)) := do
  return (← certify z.1, ← certify z.2)

end Ival
end MathEngine
