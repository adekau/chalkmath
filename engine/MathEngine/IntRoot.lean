/-!
# Integer roots, perfect powers and `q`-th-power parts

The arithmetic under exact roots (`simp.power`), the radical rules (`RadicalRules.lean`) and the
printer's `m√s` (`radicalParts`, Print.lean). Every search here is bounded by the *size* of its
input in bits, never by its value. `√(10^401)` once hung on the two searches this replaced: a
bisection over `[1, x]` for each candidate exponent (out of fuel past `2^198`, but only after
minutes of powers of 1,300-bit numbers), then a scan of `2^667` candidates for a square factor.

Each function returns only what it has *checked* (`r ^ n = x`, `m ^ q ∣ b`), so the specifications
in `proofs/` read correctness off a final guard and never need completeness. Completeness is still
the intent: below `maxRootBits` the answers are exact, and past it the searches stop looking, which
leaves a number unsimplified (`√(10^2000)` stays a power of a numeral) but never makes it wrong.
-/
namespace MathEngine

/-- Numbers this many bits long or longer (about 1,200 digits) are not searched for roots or
`q`-th-power factors: `perfectPower` tries every exponent up to the bit length, and each try costs
powers of numbers that long. -/
def maxRootBits : Nat := 4096

/-- Binary search for a `y` with `y ^ n = x`. Top-level (rather than a `let rec`) so that
`proofs/` can state its specification: it only ever returns a `y` whose power it has *checked*,
so correctness is read straight off the final guard and completeness is never needed. -/
def natRootGo (n x : Nat) : Nat → Nat → Nat → Option Nat
  | _, _, 0 => none
  | lo, hi, fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if mid ^ n < x then natRootGo n x (mid + 1) hi fuel else natRootGo n x lo mid fuel
    else if lo ^ n = x then some lo else none

/-- Exact natural `n`-th root of `x`, if there is one. For `x ≥ 2` and `b = ⌊log₂ x⌋ / n`, the root
lies in `[2^b, 2^(b+1))`, an interval the search halves `b + 1` times; its powers stay about as
long as `x`. A root of `x ≥ 2` is at least 2, so `n` is at most `⌊log₂ x⌋`; and an `x` of
`maxRootBits` or more is not searched (the search costs `b` powers as long as `x`). -/
def natRoot (n x : Nat) : Option Nat :=
  if x < 2 then some x
  else if Nat.log2 x < n || Nat.log2 x ≥ maxRootBits then none
  else natRootGo n x (2 ^ (Nat.log2 x / n)) (2 ^ (Nat.log2 x / n + 1)) (Nat.log2 x / n + 2)

/-- The largest `k ≥ 2` with `r ^ k = a`, if `a ≥ 2` is a perfect power (and shorter than
`maxRootBits`, past which `natRoot` finds nothing). -/
def perfectPower (a : Nat) : Option (Nat × Nat) :=
  (List.range (Nat.log2 a + 1)).reverse.findSome? fun k =>
    if k ≥ 2 then (natRoot k a).map fun r => (r, k) else none

/-- `d` divides `c` `e` more times: `(c / d^e, e)`, at most `fuel` times. -/
def divideOut (d : Nat) : (fuel c e : Nat) → Nat × Nat
  | 0, c, e => (c, e)
  | fuel + 1, c, e => if c % d == 0 then divideOut d fuel (c / d) (e + 1) else (c, e)

/-- The largest `m'` with `m'^q ∣ c`, times `m`, by trial division up to `2^20`. Divisors run 2, 3,
5, 7, 9, …, so a `d` that reaches `c` has no smaller prime factors left in it. Once `c < d^(q+1)`, every
prime factor of `c` is at least `d`, so `c` has at most `q` of them: its `q`-th-power part is `c`
itself when `c` is a perfect `q`-th power, and `1` otherwise. -/
def qthPowerGo (q : Nat) : (fuel d c m : Nat) → Nat
  | 0, _, _, m => m
  | fuel + 1, d, c, m =>
    if c < d ^ (q + 1) then
      match natRoot q c with
      | some r => m * r
      | none => m
    else
      let (c', e) := divideOut d maxRootBits c 0
      qthPowerGo q fuel (if d == 2 then 3 else d + 2) c' (m * d ^ (e / q))

/-- `(m, b / m^q)` once `m^q ∣ b` is checked, `(1, b)` otherwise: `proofs/` reads
`m^q · s = b` off this guard. -/
def checkedPart (b q m : Nat) : Nat × Nat :=
  if m ≥ 1 && b % (m ^ q) == 0 then (m, b / (m ^ q)) else (1, b)

/-- `checkedPart` as it runs: `m = 1` (no factor found, always so when `2^q > b`) answers `(1, b)`
without computing `1 ^ q`. Lean's runtime stops the whole process on a `Nat.pow` exponent of `2^32` or
more, whatever the base, and `q` is a numeral's denominator: `10^1.6020599913279623` has `q = 10^16`. -/
def checkedPartImpl (b q m : Nat) : Nat × Nat :=
  if m == 1 then (1, b) else if m ≥ 1 && b % (m ^ q) == 0 then (m, b / (m ^ q)) else (1, b)

@[csimp] theorem checkedPart_eq_impl : @checkedPart = @checkedPartImpl := by
  funext b q m
  unfold checkedPart checkedPartImpl
  by_cases h : m = 1
  · subst h; simp
  · simp [h]

/-- `b = m^q · s` with `m` the largest such: the `q`-th-power part of a positive integer, exact for
`b < 2^(20(q+1))` and otherwise as far as trial division up to `2^20` finds (the factors it finds
are real; a larger one it misses leaves `s` with a `q`-th-power factor). -/
def qthPowerPart (b q : Nat) : Nat × Nat :=
  -- `m ≥ 2` needs `2^q ≤ b`, which also keeps `d^(q+1)` above as short as `b`
  checkedPart b q (if Nat.log2 b < q || Nat.log2 b ≥ maxRootBits then 1 else qthPowerGo q (2 ^ 19 + 1) 2 b 1)

end MathEngine
