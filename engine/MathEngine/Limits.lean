import MathEngine.Numeric
import MathEngine.Print
/-!
# How big an exact answer may be

`p^n` for numerals evaluates exactly (`powNumeric`), so `2^(10^9)` would build a number of a billion
bits and then print it in decimal, which no notebook can wait for (the browser's runtime has no GMP).
Before an input is normalized (`normCell`), every power of two closed numeric terms is sized in
floating point, and one whose exact value would run past `maxPowerBits` refuses the evaluation, saying
how many digits it would have. The rules themselves are untouched, so the proofs about them are too;
a power the rewriting builds out of smaller ones (`(2^40000)^2`) is not caught here, and is what
Stop is for.
-/
namespace MathEngine

/-- The most bits an exact power may have: 65536 bits, about 19,728 decimal digits. -/
def maxPowerBits : Float := 65536

/-- About `log₂ n`; a numeral too big for a double is sized by its bit length. -/
private def log2Nat (n : Nat) : Float :=
  if n == 0 then 0 else if n < 2 ^ 1000 then Float.log2 (Float.ofNat n) else Float.ofNat n.log2

/-- Built from numerals by sums, products, powers and square roots: what the rules can turn into a
numeral (`π`, `exp(1)` and the other functions stay as they are, so `π^(10^6)` is not a big number to
compute). -/
partial def numeralTerm : Expr → Bool
  | .num _ => true
  | .add es | .mul es => es.all numeralTerm
  | .pow b e => numeralTerm b && numeralTerm e
  | .fn "sqrt" [a] => numeralTerm a
  | _ => false

/-- Why `b^e` cannot be computed exactly, when it is a power of numeral terms with an integer
exponent (what `powNumeric` evaluates): its value would have more than `maxPowerBits` bits, or, for
a base of 0 or ±1, the exponent does not fit the machine word Lean's `Nat.pow` takes (it stops the
whole engine past that). -/
def powerRefusal (b e : Expr) : Option String := do
  if !(numeralTerm b && numeralTerm e) then none
  let ev ← (evalNumeric [] e).toOption
  if ev.isNaN || (ev.isFinite && ev != ev.round) then none
  let bv ← (evalNumeric [] b).toOption
  -- a numeral base is sized by its numerator and denominator, any other by its value
  let perUnit := match b with
    | .num q => log2Nat q.val.num.natAbs + log2Nat q.val.den
    | _ => if bv == 0 || !bv.isFinite then 0 else (Float.log2 bv.abs).abs
  let shown := (Expr.pow b e).toText
  if perUnit == 0 then
    if ev.abs < 2147483648 then none
    else some s!"{shown}: the exponent is too large to compute with exactly"
  else
    let bits := perUnit * ev.abs
    if bits ≤ maxPowerBits then none
    let digits := bits * 0.30103
    let size := if digits < 1e15 then s!"about {digits.floor.toUInt64.toNat} digits" else "more digits than can be counted"
    some s!"{shown} is too large to compute exactly: it has {size}, and an exact answer may have up to {(maxPowerBits * 0.30103).floor.toUInt64.toNat}"

/-- Why the input cannot be evaluated exactly, if it holds a power too big to compute. -/
partial def powerTooLarge : Expr → Option String
  | .pow b e => powerTooLarge b <|> powerTooLarge e <|> powerRefusal b e
  | .add es | .mul es | .fn _ es => es.firstM powerTooLarge
  | .matrix rows => rows.firstM (·.firstM powerTooLarge)
  | _ => none

end MathEngine
