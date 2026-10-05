import MathEngine.Json
import MathEngine.Wire
import MathEngine.Parser
import MathEngine.Print
import MathEngine.Session
import MathEngine.Exercise
/-!
# JSON-RPC surface

One pure function `handleS : Store → String → Store × String`. Every host — the Emscripten worker,
the native stdio server, a future HTTP server — is a shim around this function that keeps the
`Store` between calls (the C shim holds it in a static; `Main.lean` threads it through its loop).
The engine itself has no mutable state.
-/
namespace MathEngine
open Json

/-- Proof status of each rewrite rule, so a frontend can say which steps of a derivation are
machine-checked instead of guessing. Kept next to the rules it describes: `verified` means an
unconditional soundness theorem over ℝ (`proofs/Proofs/SimpReal.lean`), `conditional` means the
theorem needs a side condition *and* the necessity of that condition is itself proved, `unverified`
means no theorem yet, `checked` means the step's own claim is a guess, and the answer it leads to is shown only
after a check whose meaning is proved (u-substitution, integration by parts and the arctangent and arcsine
forms of the `int.*` finder, checked by `int.check`). A step
that is itself the check, evaluating a definition (`sys.step`), is `verified`. The `la.row-*` rules are proved over ℚ (`LinAlgQ.lean`), not ℝ: their claim is
that the row operation preserves the solution set. Rules absent from this list are unverified. -/
def ruleStatus : Json :=
  let entry (name status note : String) : Json :=
    .obj #[("rule", .str name), ("status", .str status), ("note", .str note)]
  -- a rule with a theorem over ℂ as well (`proofs/Proofs/Cx.lean`): the status a cell containing `i` shows
  let entryC (name status note cstatus cnote : String) : Json :=
    .obj #[("rule", .str name), ("status", .str status), ("note", .str note),
           ("complex", .obj #[("status", .str cstatus), ("note", .str cnote)])]
  .arr #[
    entryC "simp.flatten" "verified" "Associativity of + and ·. It keeps the domain: wherever its input is defined, so is its output (flatten_soundD)." "verified" "Associativity, in any field (flatten_soundC).",
    entryC "simp.identity" "verified" "The additive and multiplicative identities and the annihilator. It keeps the domain: wherever its input is defined, so is its output (identity_soundD)." "verified" "The identities and the annihilator, in any field (identity_soundC).",
    entryC "simp.fold-constants" "verified" "Exact rational arithmetic; ℚ embeds in ℝ. It keeps the domain: wherever its input is defined, so is its output (foldConstants_soundD)." "verified" "ℚ embeds in ℂ (foldConstants_soundC).",
    entryC "simp.collect-like-terms" "verified" "Distributivity: a·t + b·t = (a+b)·t. It keeps the domain: wherever its input is defined, so is its output (collectTerms_soundD)." "verified" "Distributivity (collectTerms_soundC).",
    entryC "simp.power" "verified" "Includes exact roots (the root search returns only checked roots) and (b^m)^n = b^(mn) for integer exponents, or for an integer n over a positive numeral base — so sqrt(2)^2 = 2 (Real.rpow_mul needs 0 ≤ b, which sqrt(x)^2 cannot promise). It keeps the domain: wherever its input is defined, so is its output (powerRules_soundD, parityPowMul_def, parityPowPow_def)." "verified" "The principal branch agrees with the real power on the positive rational bases the exact roots and the radical powers use (powerRules_soundC).",
    entry "simp.sort" "verified" "Commutativity: the arguments of + and · are put in a canonical order (SemEqR.canon). Silent: it reorders only.",
    entry "simp.collect-powers" "verified" "b^m·b^n = b^(m+n) for every real b: the exponents are integers of one sign (x·x = x², x⁻¹·x⁻² = x⁻³) or the base is a positive numeral (collectPowers_soundR, rpow_int_add_of_sameSign). It keeps the domain: wherever its input is defined, so is its output (collectPowers_soundD).",
    entry "simp.collect-powers.assuming" "conditional" "The other merges, x·x⁻¹ = x⁰ and x^a·x^b = x^(a+b): the step states its assumption, b ≠ 0 for integer exponents and b > 0 otherwise, and is proved under it (collectPowersAssuming_soundR_on). Without it, at x = 0, x·x⁻¹ turns 0 into 1 (not_collectPowersAssuming_soundR).",
    entryC "simp.function" "verified" "sin/cos = tan, √a = a^(1/2), ln 1 = 0, exp 0 = 1, sin 0, cos 0, and abs and sign of a numeral, for every real number (functionRules_soundR). It keeps the domain: wherever its input is defined, so is its output (functionRules_soundD)." "verified" "The same cases hold for every complex number (functionRules_soundC); the ones that hold over ℝ only are simp.function.real.",
    entryC "simp.function.real" "verified" "ln(exp x) = x, and ln(b^p) = p ln b for an odd integer p, for every real number (functionReal_soundR); an odd power keeps the domain, b^p > 0 exactly when b > 0. It keeps the domain: wherever its input is defined, so is its output (functionReal_soundD)." "unverified" "Off in a cell read over ℂ, where it is false: ln(exp x) = x fails at x = 2πi, and at x = 4i the principal value is (4 − 2π)i (not_functionReal_soundC).",
    entry "simp.function.assuming" "conditional" "exp(ln x) = x, and ln(b^p) = p ln b for p not an odd integer: the step states its assumption, x > 0 or b > 0, and is proved under it (functionAssuming_soundR_on). Without it, at x = -1, exp(ln x) turns -1 into 1 (not_functionAssuming_soundR), and ln(x²) is defined at x = −2 where 2 ln x is not.",
    entry "diff.constant" "verified" "A term the variable does not occur in has derivative 0 (diff_constant_sound).",
    entry "diff.variable" "verified" "The identity function has slope 1 everywhere (diff_variable_sound).",
    entry "diff.constant-multiple" "verified" "Constant factors pull out; no differentiability needed (diff_const_mul_sound).",
    entry "diff.sum" "verified" "Fires where every summand is smooth (built from numerals, variables, +, ·, natural powers, powers of a positive numeral, sin, cos, exp, arctan), so differentiable everywhere (smooth_differentiable), and then the sum rule holds at every point (diffSum_sound).",
    entry "diff.sum.assuming" "conditional" "The sum rule where a summand is not smooth: the step assumes it differentiable, and is proved under that (diffSumAssuming_sound_on). Without it the rule fails: for |x| + x at 0 it gives 1 where there is no derivative (not_diff_sum_sound).",
    entry "diff.product" "verified" "Fires where every factor is smooth, so differentiable everywhere; the product rule for any number of factors, as the engine writes it, then holds at every point (diffProduct_sound).",
    entry "diff.product.assuming" "conditional" "The product rule where a factor is not smooth: the step assumes it differentiable, and is proved under that (diffProductAssuming_sound_on).",
    entry "diff.power" "verified" "Fires for a natural numeral exponent over a smooth base, or a positive numeral base under a smooth exponent; then (u^n)' = n u^(n−1) u' and (b^u)' = b^u ln b u' hold at every point (diffPower_sound).",
    entry "diff.power.assuming" "conditional" "The power rule where it needs more: x ≠ 0 for a negative integer exponent, x > 0 for any other (real or symbolic) one, b > 0 for b^u, f > 0 for f^g, and the parts differentiable; the step says which, and is proved under it (diffPowerAssuming_sound_on, through HasDerivAt.rpow_const, HasDerivAt.const_rpow and HasDerivAt.rpow).",
    entry "diff.chain" "verified" "Fires for sin, cos, exp and arctan of a smooth term; the chain rule then holds at every point (diffChain_sound).",
    entry "diff.chain.assuming" "conditional" "The chain rule where it needs more: u > 0 for ln u, cos u ≠ 0 for tan u, −1 < u < 1 for arcsin u and arccos u, and u differentiable; the step says which, and is proved under it (diffChainAssuming_sound_on, through HasDerivAt.log, Real.hasDerivAt_tan, Real.hasDerivAt_arcsin and Real.hasDerivAt_arccos).",
    entry "diff.matrix" "verified" "A matrix is differentiated entry by entry (diffMatrix_sound): with matrices given a value (evalV), the theorem has content.",
    entry "diff.higher-order" "verified" "diff(f, x, n) for a positive integer n is written as n successive diff(·, x) (diffHigherOrder_spec), and those mean Mathlib's n-th iterated derivative of f read as a function of x (diffHigherOrder_soundR).",
    entry "cmd.simplify" "verified" "A cell's argument is already in normal form when the command sees it (the pipeline rewrites innermost first), so simplify returns it unchanged: the identity.",
    entry "cmd.subst" "verified" "Structural substitution e[x := v] (substVar) evaluates as e with x rebound to the value of v (cmdSubst_soundR, from substVar_soundR).",
    entry "cmd.N" "verified" "The decimal is certified: interval arithmetic over the rationals holds the exact real value (ieval_sound), with Taylor remainders for exp, sin and cos (Real.exp_bound, Complex.exp_bound) on sums taken in interval arithmetic (expSumI_mem, trigSumI_mem), ln checked by exp, sqrt and x^(1/2) by squaring and π to twenty digits (Real.pi_gt_d20), and the digits shown are the most, up to fifteen, within a unit of their last place of everything in the interval (certify_sound, cmdN_sound). arctan is pinned by tan (atanCheck_mem). A complex value is certified part by part: a rectangle of two intervals holds the principal value (cieval_sound), through the formulas for the parts of a product, a quotient, exp, sin and cos, a real argument to ln and sqrt, an integer power or a real base under a real exponent, and otherwise ln z = ln|z| + i arg z with the argument from arctan (arg_eq_arctan_of_re_pos, arg_eq_of_im_pos, clnI_mem) and b^e = exp(e ln b); each part's digits are within a unit of their last place (cmdN_soundC). Where the constants e and π have their values.",
    entry "cmd.N.float" "unverified" "A floating-point approximation in IEEE-754 double precision, for what cmd.N cannot certify: a function across a pole or a jump, the logarithm or a power of a number on (or too near) the negative real axis, where the argument jumps, and arcsin and arccos. No error bound is proved.",
    entry "la.add" "verified" "Matrices of one shape add entrywise: the output has the input's value, read in evalV, which gives a matrix its value (laAdd_sound).",
    entry "la.scalar-mul" "verified" "A real factor multiplies every entry; real factors commute past a matrix (laScalarMul_sound, for a node whose children are normal, as the pipeline fires it).",
    entry "la.mul" "verified" "Entry (i, j) of the product is row i of the left factor dotted with column j of the right; the product is associative and real factors commute past the matrices (laMul_sound, mulV_assoc).",
    entry "la.transpose" "verified" "Rows become columns (laTranspose_sound).",
    entry "la.det" "verified" "Laplace expansion along the first row has Mathlib's determinant as its value (laDet_sound, detExpr_value, Matrix.det_succ_row_zero).",
    entry "la.pow" "verified" "M^k for a positive integer k is the power in the monoid of square matrices (laPow_sound, matPow_value).",
    entry "la.context" "verified" "A refusal: a matrix literal where no rule gives it a meaning, or nested in another, is an error, never a value, so there is nothing to be wrong.",
    entry "cmd.rref" "verified" "Over ℚ the reduced matrix has the input's solution set (LinQ.sol_rref) and is in reduced row echelon form (LinQ.rref_isRref). With symbolic entries the nested row operations are the unverified .symbolic ones, and the step inherits their status.",
    entry "la.row-swap" "verified" "Exchanging two rows preserves the solution set (LinQ.sol_swap); elimination as a whole: LinQ.sol_rref.",
    entry "la.row-scale" "verified" "Scaling a row by a nonzero rational preserves the solution set (LinQ.sol_scale).",
    entry "la.row-add" "verified" "Adding a multiple of another row preserves the solution set (LinQ.sol_addMul).",
    entry "la.row-swap.symbolic" "verified" "Exchanging two rows keeps the solution set at every value of the symbols (swapRows_soundR); no arithmetic is done. The pivot is the first entry the simplifier cannot show is zero.",
    entry "la.row-scale.symbolic" "conditional" "Dividing a row by the pivot keeps the solution set wherever the pivot is not zero (scaleRowExact_soundR), and the step says so. The entries are then simplified; where a cancellation assumed something (collectPowersAssuming_soundR_on, functionAssuming_soundR_on) the step says what.",
    entry "la.row-add.symbolic.assuming" "conditional" "As la.row-add.symbolic, but simplifying the entries used a cancellation that assumes its base nonzero or positive (collectPowersAssuming_soundR_on, functionAssuming_soundR_on); the step states the assumption.",
    entry "la.row-add.symbolic" "verified" "Subtracting a multiple of another row keeps the solution set at every value of the symbols (addRowExact_soundR), and the entries are simplified by the rules that assume nothing, checked by comparing with them, so they keep their value everywhere (normalizeSafe_sound).",
    entry "simp.radical" "verified" "A perfect-power base is reduced (8^(1/2) = 2^(3/2)), same-index radicals multiply under one root, and sqrt(18) is written 18^(1/2), which shows as 3√2; unconditional, the bases are positive integers and sqrt(a) = a^(1/2) for every real a (radicalBase_soundR, mulRadicals_soundR, sqrtRadical_soundR). It keeps the domain: wherever its input is defined, so is its output (radicalBase_def, mulRadicals_def, sqrtRadical_def).",
    entry "simp.sqrt" "verified" "sqrt(a) = a^(1/2) for every real a (sqrtPower_soundR). Silent: the two print alike. It keeps the domain: wherever its input is defined, so is its output (sqrtPower_def).",
    entry "simp.collect-radicals" "verified" "Radicals with the same square-free part collect, √50 − √18 = 2√2; unconditional (collectRadicals_soundR). It keeps the domain: wherever its input is defined, so is its output (collectRadicals_def).",
    entry "cmd.factor" "conditional" "The common-denominator form is a guess the pipeline checks: it and the input, each times the denominator D, normalized and expanded, must be the same term, so it agrees with the input wherever D is not zero and the check's normalizations hold (factor_run_sound); the step says so, naming D. Without the condition it fails: factor(1/x + 1) is (x + 1)/x, 1 and 0 at x = 0 (not_factor_at_zero). Expanding the answer gives the input's value back under the same conditions, not its term (expand_factor_sound). When the check fails, the collected normal form is the answer.",
    entry "cmd.expand" "verified" "Distribution is a total function proved sound over ℝ (dist_sound, proofs/Proofs/Expand.lean); the collection afterwards is the pipeline's own steps with their statuses.",
    entry "expand.distribute" "verified" "Multiplying out a product of sums and collecting like monomials: dist_sound.",
    entry "expand.power" "verified" "A power of a sum is the sum multiplied by itself: dist_sound.",
    entry "cmd.integrate" "verified" "Accepted only when the candidate's derivative normalizes to the integrand, exactly (cmdIntegrate_spec); integrate_deriv reads that as deriv F = f wherever the differentiation steps shown are sound. The finder's steps carry claims of their own where they are verified or conditional (anti_sound); the rest are guesses only the check vouches for.",
    entryC "simp.exp-product" "verified" "exp(a)·exp(b) = exp(a+b), unconditionally (expProduct_soundR)." "verified" "Complex.exp_add (expProduct_soundC).",
    entry "int.bounds" "verified" "The fundamental theorem of calculus: the checked antiderivative evaluated at the bounds, F(b) − F(a) (cmdIntegrate_definite_spec; integrate_definite reads it as the interval integral over ℝ, for an integrand continuous on [a, b]).",
    entry "cmd.sum" "verified" "A definition: one substituted term per integer value of the index (cmdSum_spec); sum_soundR reads the result as the finite sum over ℝ.",
    entryC "cmd.exptotrig" "unverified" "Euler's formula has no content over ℝ, where i is the junk value 0." "verified" "exp(iθ) = cos θ + i sin θ for every complex θ (expToTrig_soundC).",
    entry "la.dot" "verified" "Σ uᵢvᵢ by definition; a matrix has no value in the ℝ semantics, so the claim is the definition (bilinear, as Mathematica's Dot — the Hermitian product is dot(u, conj(v))).",
    entry "la.norm" "verified" "(Σ vᵢ²)^(1/2) by definition, the Pythagorean length.",
    entry "la.conj" "verified" "Entrywise by definition.",
    entry "la.ediv" "verified" "Entrywise by definition: entry (i, j) is aᵢⱼ/bᵢⱼ, and a scalar side meets every entry; each entry's arithmetic is its nested steps, with their statuses.",
    entry "la.emul" "verified" "Entrywise by definition (the Hadamard product): entry (i, j) is aᵢⱼ·bᵢⱼ, and a scalar side meets every entry; each entry's arithmetic is its nested steps, with their statuses.",
    entry "la.entrywise" "verified" "A matrix equals the one whose entries equal its own: each entry is rewritten on its own, and the step is only as sound as the entries' steps nested below it, whose statuses it carries.",
    entry "la.part" "verified" "Mathematica's Part by definition: positions count from 1, negative ones from the end. Every position a spec selects is in range (partSpec_lt), so the selection is exactly the entries named, never a filler.",
    entry "stat.total" "verified" "Σ xᵢ by definition; over ℝ the value is the list's sum (total_soundR).",
    entry "stat.mean" "verified" "(1/n)·Σ xᵢ; over ℝ the value is the sum over the count (mean_soundR).",
    entry "stat.variance" "verified" "The one-pass form (Σxᵢ² − (Σxᵢ)²/n)/(n − 1) equals the sample variance Σ(xᵢ − x̄)²/(n − 1) over ℝ, for n ≥ 2 (variance_soundR).",
    entry "stat.stdev" "verified" "The square root of the sample variance in its one-pass form (stdev_soundR, from variance_soundR).",
    entry "stat.min" "verified" "Exact comparison of rationals: the result is an entry and no entry is smaller (minQ_spec).",
    entry "stat.max" "verified" "Exact comparison of rationals: the result is an entry and no entry is larger (maxQ_spec).",
    entry "stat.median" "verified" "The entries sorted (a sorted permutation: List.mergeSort_perm, List.pairwise_mergeSort), then the middle one or the mean of the two middle ones (medianQ_spec).",
    entry "int.check" "verified" "The differentiation of the candidate: this step carries the claim, with the statuses of its own steps.",
    entry "int.compare" "verified" "Derivative and integrand are rewritten with cos²u = 1 − sin²u, (eᵘ)ᵏ = eᵏᵘ, 1/√s = s^(-1/2) and, under a negative power, s^k = c^k·(s/c)^k for a positive constant summand c (identNorm), expanded (dist) and simplified before comparison — every rewrite proved sound for every real value (ev_identPow), and needed because the pipeline applies none of these identities nor distributes a numeral over a sum; the statuses of the simplification steps apply.",
    entry "int.constant" "verified" "∫ c dx = c·x for a term free of x, at every point (antiConst_sound). Each finder rule is proved compositionally: if the sub-results are antiderivatives of the sub-integrands, so is the result, and anti_sound puts the rules together, so an answer whose steps are all verified or conditional is an antiderivative wherever what they assume holds, before any check.",
    entry "int.variable" "verified" "∫ x dx = x²/2, at every point (antiVar_sound).",
    entry "int.sum" "verified" "Given antiderivatives of the summands, their sum is one of the sum, at every point (antiSum_sound); what the summands' own steps assume, they state.",
    entry "int.constant-multiple" "verified" "The factors free of x times an antiderivative of the rest is an antiderivative of the product, at every point (antiConstMul_sound).",
    entry "int.power" "verified" "∫ uⁿ du = uⁿ⁺¹/(n+1) for a natural numeral n, at every point, through the chain rule in u = a·x + b (powerRule_sound, linearCoeff_spec, HasDerivAt.rpow_const).",
    entry "int.power.assuming" "conditional" "The power rule where it needs more: u > 0 for ∫ u⁻¹ du = ln u and for a non-integer exponent, u ≠ 0 for a negative integer one, u > 0 and n ≠ −1 for a symbolic n; the step states which, and is proved under it (powerRule_sound, antiPower_sound). Without it ∫ x⁻¹ dx = ln x fails at x = 0, where ln has no derivative (not_power_sound, Real.differentiableAt_log_iff).",
    entry "int.exponential" "verified" "∫ bᵘ du = bᵘ/ln b for a numeral base b > 0, b ≠ 1, or π, at every point (exponential_sound, through HasDerivAt.const_rpow).",
    entry "int.exponential.assuming" "conditional" "Any other base: the step states b > 0 and b ≠ 1, and is proved under it (exponential_sound, antiExponential_sound). Without it the rule fails: at b = 1 the candidate 1ˣ/ln 1 is 0 while the integrand is 1 (not_exponential_sound).",
    entry "int.table" "verified" "sin, cos, exp and arctan of u = a·x + b: each entry's derivative is the integrand times u', at every point (table_sound, antiFn_sound).",
    entry "int.table.assuming" "conditional" "The entries that need a condition: u > 0 for ln u, cos u > 0 for tan u, −1 < u < 1 for arcsin u and arccos u, cos u ≠ 0 for sec² u; the step states which, and is proved under it (table_sound, antiSecSq_sound, through HasDerivAt.log, Real.hasDerivAt_arcsin, Real.hasDerivAt_arccos and Real.hasDerivAt_tan). Without it ∫ sec² x dx = tan x fails at x = π/2, where tan has no derivative (not_secSq_sound, Real.differentiableAt_tan).",
    entry "int.linear-substitution" "verified" "Dividing by a numeral coefficient a ≠ 0 of u = a·x + b: if G(u) has derivative g·a, then G(u)/a has derivative g, at every point (substitute_sound, linearCoeff_spec).",
    entry "int.linear-substitution.assuming" "conditional" "A coefficient that is not a numeral: the step states a ≠ 0, and is proved under it (substitute_sound). Without it the rule fails: at k = 0, sin(kx)/k is 0 while cos(kx) is 1 (not_substitute_sound).",
    entry "int.substitution" "checked" "A guess from the finder (u-substitution), verified by int.check. It is built from the normalizer's outputs, the derivative g' of the inner function and the ratio of the other factors to it, and nothing is proved about those here, so the finder marks the result checked and anti_sound claims nothing for it.",
    entry "int.by-parts" "checked" "A guess from the finder (integration by parts), verified by int.check. The derivative du and the product v·du it integrates next are the normalizer's outputs, and nothing is proved about those here, so the finder marks the result checked and anti_sound claims nothing for it.",
    entry "int.trig-power" "verified" "The reduction formulas for sinᵐu cosⁿu with a numeral coefficient of u, given an antiderivative of the integrand left: the result's derivative is sinᵐu cosⁿu, by sin²u + cos²u = 1, at every point (trigPower_sound, hasDerivAt_sineReduce, hasDerivAt_cosineReduce).",
    entry "int.trig-power.assuming" "conditional" "A coefficient k of u that is not a numeral: the step states k ≠ 0, and is proved under it (trigPower_sound). Without it the rule fails: at k = 0 the formula gives x/2 for ∫ sin²(kx) dx, the integral of 0 (not_trigPower_sound).",
    entry "int.exp-power" "verified" "(eᵘ)ᵏ = eᵏᵘ for every real u and k (Real.exp_mul), distributed by Expand.dist (dist_soundD): the integrand keeps its value, so an antiderivative of eᵏᵘ is one of (eᵘ)ᵏ (antiExpPower_sound).",
    entry "int.arctan" "checked" "A guess from the finder (1/(k + c·u²) as an arctangent), verified by int.check. Its scaling factors are radicals of the numerals, √(c/k) as c·(kc)^(-1/2), which nothing proves here, so the finder marks the result checked.",
    entry "int.arcsin" "checked" "A guess from the finder (1/√(k − c·u²) as an arcsine), verified by int.check. Its scaling factors are radicals of the numerals, which nothing proves here, so the finder marks the result checked.",
    entry "order.divisors" "verified" "The divisors of n ordered by divisibility, by definition.",
    entry "order.subsets" "verified" "The subsets of a finite set ordered by inclusion, by definition.",
    entry "order.incomparable" "verified" "x ≤ y is not in the order: decided on the reflexive-transitive closure, which is checked to be a partial order (checkPartialOrder_none).",
    entry "order.closure" "verified" "The order is the reflexive-transitive closure, and reflexivity, antisymmetry and transitivity are decided (checkPartialOrder_none).",
    entry "order.covers" "verified" "Hasse edges are exactly the covers: x < y with nothing strictly between (covers_spec).",
    entry "order.upper-bounds" "verified" "Every element above both, by the decision on the finite order.",
    entry "order.least" "verified" "The element found is an upper bound below every upper bound (sup_spec); none exists when the search fails (sup_none).",
    entry "order.lower-bounds" "verified" "Every element below both, by the decision on the finite order.",
    entry "order.greatest" "verified" "Dual of the join: the greatest lower bound.",
    entry "order.lattice" "verified" "Every pair searched for a join and a meet; the witness is reported when one is missing.",
    entry "order.cover" "verified" "A cover in the Hasse diagram; the chain composes by transitivity.",
    entry "order.monotone" "verified" "Every pair x ≤ y of the order checked; the witness is reported when it fails.",
    entry "order.iterate" "verified" "One step of the Kleene chain; each element of the chain is below every fixed point (iter_le_fixed).",
    entry "order.fixed" "verified" "The chain stopped at a fixed point (checked), which iter_le_fixed makes the least (dually, the greatest).",
    entryC "cx.i-power" "unverified" "i has no real meaning; read in ℂ." "verified" "i² = −1 (Complex.I_sq); the powers cycle.",
    entryC "cx.arithmetic" "unverified" "i has no real meaning; read in ℂ." "verified" "Products of Gaussian rationals, by the field laws and i² = −1.",
    entryC "cx.power" "unverified" "i has no real meaning; read in ℂ." "verified" "Integer powers and inverses of Gaussian rationals; 1/(a+bi) = (a−bi)/(a²+b²).",
    entryC "cx.conjugate" "unverified" "i has no real meaning; read in ℂ." "verified" "Conjugation of a Gaussian rational, and conj ∘ conj = id.",
    entryC "cx.re-im" "unverified" "i has no real meaning; read in ℂ." "verified" "Real and imaginary parts of a Gaussian rational.",
    entryC "cx.abs" "unverified" "i has no real meaning; read in ℂ." "verified" "|a + bi| = √(a² + b²), the norm (cxAbs_soundC, norm_eq_cpow_half).",
    entryC "cx.exact-trig" "verified" "sin, cos, tan at rational multiples of π: period, reflections and the reference angles (Real.sin_pi_div_four and friends)." "verified" "The real values, cast (Complex.ofReal_sin, ofReal_cos)." ,
    entryC "cx.euler" "unverified" "i has no real meaning; read in ℂ." "verified" "Euler's formula exp(iθ) = cos θ + i sin θ (Complex.exp_mul_I) with the exact values.",
    entryC "cx.euler-power" "verified" "(e¹)^b = e^b (Real.rpow_def_of_pos)." "verified" "(e¹)^b = e^b (Complex.cpow_def, log_exp with Im 1 = 0).",
    entry "rel.kernel" "verified" "Equality of labels is reflexive, symmetric and transitive, so having the same label is too: by definition.",
    entry "rel.reflexive" "verified" "Every element checked for $x \\mathrel{R} x$; the first that fails is the witness.",
    entry "rel.symmetric" "verified" "Every pair checked for its reverse; the first without one is the witness.",
    entry "rel.antisymmetric" "verified" "Every pair checked against its reverse with distinct ends.",
    entry "rel.transitive" "verified" "Every two pairs that chain checked for the pair they force; the first missing one is the witness (transitiveFailure_none).",
    entry "rel.equivalence" "verified" "Reflexive, symmetric and transitive, each checked.",
    entry "rel.preorder" "verified" "Reflexive and transitive, each checked.",
    entry "rel.reflexive-closure" "verified" "Adds exactly the missing $(x, x)$: the least reflexive relation containing the original, by definition.",
    entry "rel.symmetric-closure" "verified" "Adds exactly the missing reverses: the least symmetric relation containing the original, by definition.",
    entry "rel.transitive-closure" "verified" "Each round adds only pairs forced by two that chain, so every pair lies in any transitive relation containing the original (round_sub_transitive); the rounds stop when none is missing, and then the relation is transitive (stable_transitive): the least transitive relation containing it.",
    entry "rel.classes" "verified" "Each element's class is everything related to it; for an equivalence the classes partition the set.",
    entry "rel.finer" "verified" "Every pair of the first checked in the second.",
    entry "rel.wellfounded" "verified" "Decided with a certificate either way: peeling gives ranks checked to go down along every step, so the relation is well-founded (wellfounded_none, wf_of_measure); or what cannot be peeled holds a cycle, checked to step back into itself, so it is not (wellfounded_some, not_wf_of_closed).",
    entry "rel.measure" "verified" "Every step checked to decrease the measure; then the relation is well-founded: no infinite chain of steps (wf_of_measure).",
    entry "alg.from-order" "verified" "Each entry is the join (or meet) of its pair, found by the search that sup_spec proves least; by definition a table.",
    entry "alg.associative" "verified" "Every triple checked; when none fails the law holds on the whole set (assocFailure_none).",
    entry "alg.commutative" "verified" "Every pair checked (commFailure_none).",
    entry "alg.idempotent" "verified" "Every element checked (idemFailure_none); with the two laws above, a semilattice (isSemilattice_of_none).",
    entry "alg.identity" "verified" "An element checked against every element on both sides, by definition.",
    entry "alg.fold" "verified" "Each step is one entry of the table, by definition of a left fold.",
    entry "alg.order" "verified" "$x \\le y \\iff x \\cdot y = y$ is a partial order in which $x \\cdot y$ is the least upper bound, for a semilattice whose table stays in its set (semilattice_order); the laws are checked first and the entries when the table is made.",
    entry "order.distributive" "verified" "Every triple checked for $x \\land (y \\lor z) = (x \\land y) \\lor (x \\land z)$ (distribFailure_none).",
    entry "order.complement" "verified" "Every element checked for $x \\lor y = \\top$ and $x \\land y = \\bot$, by definition.",
    entry "order.boolean" "verified" "Distributive and complemented, each checked: the definition of a Boolean lattice.",
    entry "order.product" "verified" "Pairs ordered componentwise, by definition: the order is the product of the two orders.",
    entry "order.galois" "verified" "Every pair $(x, y)$ checked for $f(x) \\le y \\iff x \\le g(y)$ (galoisFailure_none).",
    entry "order.closure-operator" "verified" "Extensive, monotone and idempotent, each checked on every element or pair (closureOpFailure_none).",
    entry "order.concepts" "verified" "Every pair listed is a formal concept, its objects exactly those with all its attributes and its attributes exactly those its objects share (concepts_sound), and every concept is listed: intersecting attribute extents one attribute at a time reaches the extent of every set of attributes (concepts_complete, extents_complete).",
    entry "order.flow" "verified" "Every flow checked against the order of the classes (flowFailure_none).",
    entry "sys.init" "verified" "An initial state: the init condition evaluated on it, by definition.",
    entry "sys.step" "verified" "By definition: each step of a trace is re-run against the system, the action enabled there and its updates giving the next state; a step that does not re-run is refused, not shown.",
    entry "sys.found" "verified" "The last state of a re-run trace, from an initial state, where the formula is evaluated and holds. The trace is a shortest one: each state's breadth-first depth is zero initially and rises by at most one along a transition, which is checked, and no state where the formula holds is shallower than the trace is long, so every path to one is at least as long (checkShortest_spec), over the system's transitions (System.explore_edges).",
    entry "sys.violated" "verified" "The last state of a re-run trace, from an initial state, where the formula is evaluated and fails: a concrete counterexample. The trace is a shortest one: each state's breadth-first depth is zero initially and rises by at most one along a transition, which is checked, and no state that breaks the formula is shallower than the trace is long, so every path to one is at least as long (checkShortest_spec), over the system's transitions (System.explore_edges).",
    entry "sys.deadlock" "verified" "The last state of a re-run trace, with every action's guard evaluated false. When none is reported none is missed: the search finds every reachable state and every transition (System.no_deadlock).",
    entry "sys.reach" "verified" "Breadth-first search from the initial states finds exactly the reachable states, each once (System.explore_states, from exploreWith_complete, exploreWith_sound and exploreWith_nodup).",
    entry "sys.invariant" "verified" "The formula holds in every state the search found, and the search finds every reachable state (System.explore_states).",
    entry "sys.unreachable" "verified" "No state the search found satisfies the formula, and the search finds every reachable state (System.explore_states).",
    entry "sys.inductive" "verified" "Every assignment of the domains is enumerated (allStates_mem) and every enabled action from a state where the formula holds is checked.",
    entry "sys.cti" "verified" "By definition: a state where the formula holds and an action after which it fails (or leaves a domain), both evaluated by the system's own semantics, a concrete counterexample to induction.",
    entry "sys.ctl" "verified" "The set is a fixed point checked with a certificate read off its rounds, and where the check passes it is exactly the states where the formula holds by the meaning of its paths: EF some path reaches φ, EG an infinite path stays in φ, AG every reachable state is in φ, AF every maximal path reaches φ (checkEF_spec, checkEG_spec, checkAG_spec, checkAF_spec, checkEX_spec, checkAX_spec), over the graph's transitions, which are the system's (System.explore_edges).",
    entry "sys.iterate" "verified" "By definition: one round of the Kleene iteration, the transformer applied to the previous set; the rounds are the certificate sys.ctl checks (checkEF_spec and the others).",
    entry "sys.fixed" "verified" "The loop stops when a round changes nothing, and the set it stops at is checked against the operator's path meaning with sys.ctl's certificate (checkEF_spec and the others), so it is the right set without appeal to Kleene's theorem.",
    entry "sys.cycle" "verified" "A step of the lasso's cycle, inside a strongly connected set of states avoiding the goal. The whole lasso is checked to be a run: every step an edge of the graph, each joined to the next, and the cycle closing up (checkLasso_spec).",
    entry "sys.lasso" "verified" "A fair run that never reaches the goal: a path from an initial state, then a cycle repeated forever, every weakly fair action taken on it or disabled somewhere on it and every strongly fair one taken on it or disabled all along it. The lasso is checked, and a lasso that checks is a fair infinite run avoiding the goal (checkLasso_spec); a deadlock reached first is checked as a run that stops without the goal (checkDead_spec).",
    entry "sys.eventually" "verified" "Every fair run reaches the goal: checked with a certificate, a rank for each state reachable without the goal that no step raises, and where a run could stay level a helpful action, never taken there, that fairness forces (a strongly fair one hands the states where it is disabled to a further certificate). A certificate that checks means every fair infinite run and every run that stops reaches the goal (checkTrue_spec, noFair), over the graph's transitions, which are the system's (System.explore_edges). The certificate comes from Emerson and Lei's search for Streett conditions.",
    entry "sys.refines" "verified" "Every initial state and every transition between reachable states is an edge the search found (System.explore_edges), and each was mapped to an abstract initial state, step or stutter.",
    entry "trs.step" "verified" "An instance of one of the system's rules, rewritten at the position the step names (step_sound); the steps chain from the term to the answer (normalize_chain), and a normal form is one no rule applies to (normalize_normal).",
    entry "trs.decrease" "verified" "A rule passes when its left side's linear form has a larger constant and no smaller coefficient: then the left side is worth more whatever the variables are (decreases_sound), and every step lowers the term's value (step_decreases), so no term rewrites for ever (no_infinite_rewriting). A rule that fails has values that make its left side worth no more (decreases_complete).",
    entry "trs.critical" "verified" "Robinson's unification, total by well-founded recursion, returns a most general unifier when there is one (unify_mgu) and nothing only when there is none (unify_none); critical pairs every rule with every rule at every non-variable position of the first one's left side, the variables renamed apart (apart_spec), and records each overlap (mem_critical), checked to be one (isPeak_sound). Locally confluent when every pair joins: the critical pair lemma, the overlap below a variable joined by rewriting every copy of it (critical_pair_lemma, critical_sound), for every system rules(...) makes (parseSystem_wellFormed). Not confluent when a pair's sides reach two different normal forms (critical_refutes, step_complete); confluent with termination by Newman's lemma (newman_lemma). Sides that reach neither within the step limit leave it undecided.",
    entry "order.inner" "verified" "A nested call evaluated first and named: a rewriting of the source, so the commands' own statuses apply.",
    entry "crdt.update" "verified" "A local update only raises entries of the replica's state (update_inflation).",
    entry "crdt.merge" "verified" "The entrywise maximum: a join, commutative, associative and idempotent (merge_comm, merge_assoc, merge_idem).",
    entry "crdt.send" "verified" "A message is a copy of the state; nothing to prove.",
    entry "crdt.converged" "verified" "Decided by comparing the states; equal states read equal values.",
    entry "crdt.diverged" "verified" "Decided by comparing the states.",
    entry "sys.inner" "verified" "A nested call evaluated first and named: a rewriting of the source, so the commands' own statuses apply.",
    entry "order.happens-before" "verified" "The reflexive-transitive closure of program order and messages, checked to be a partial order (checkPartialOrder_none).",
    entry "order.clocks" "verified" "Each entry counts the events of a process below the event in the happens-before order, by definition.",
    entry "order.concurrent" "verified" "Neither event is below the other in the happens-before order, by definition.",
    entry "logic.implication" "verified" "$a \\to b$ and $\\lnot a \\lor b$ have the same value under every assignment, and the pass that applies it everywhere keeps the formula's value (arrows_sound).",
    entry "logic.biconditional" "verified" "$a \\leftrightarrow b$ and $(a \\to b) \\land (b \\to a)$ have the same value under every assignment; the pass keeps the formula's value (arrows_sound).",
    entry "logic.de-morgan" "verified" "$\\lnot(a \\land b) = \\lnot a \\lor \\lnot b$ and its dual, over Bool; the negation pass keeps the value (nnf_sound).",
    entry "logic.double-negation" "verified" "$\\lnot\\lnot a = a$ over Bool (nnf_sound).",
    entry "logic.negate-constant" "verified" "$\\lnot\\top = \\bot$ and $\\lnot\\bot = \\top$ (nnf_sound).",
    entry "logic.constants" "verified" "The identities and annihilators of $\\land$ and $\\lor$ over Bool (consts_sound).",
    entry "logic.distribute" "verified" "$a \\lor (b \\land c) = (a \\lor b) \\land (a \\lor c)$ and its dual over Bool (distrib_sound, normal_sound).",
    entry "logic.complement" "verified" "A term with $p$ and $\\lnot p$ is false, a clause with them true, under every assignment (complement_sound).",
    entry "logic.truthtable" "verified" "Every assignment to the formula's variables is a row (rows_complete), and a formula's value depends only on its variables (eval_congr): what holds in every row holds everywhere (taut_sound, unsat_sound), and a row returned as a witness is one (findRow_spec).",
    entry "logic.evaluate" "verified" "A formula without variables: its value by definition of the connectives.",
    entry "logic.bounded" "verified" "A quantifier over a finite set is checked element by element, by definition; the atoms are evaluated by the pipeline, whose steps' statuses apply.",
    entry "lambda.delta" "verified" "Unfolding a definition replaces a free name by its term; nothing to prove beyond that.",
    entry "lambda.beta" "verified" "Each step is one β-reduction of the de Bruijn terms: capture-avoiding substitution is de Bruijn substitution (toDB_subst), for every strategy (betaStep_beta, cbnStep_beta, cbvStep_beta, appStep_beta, betaEtaStep_beta).",
    entry "lambda.alpha-beta" "verified" "A binder renamed to avoid capture, then β: the renaming keeps the de Bruijn form (toDB_renameFor) and leaves nothing to capture (captureFree_renameFor), so the step is one β-reduction (toDB_subst).",
    entry "lambda.elided" "verified" "The β-steps of a long reduction that the work does not show, each a step of the same strategy, so a β-reduction as lambda.beta's are.",
    entry "lambda.eta" "verified" "η: λx. f x contracts to f only when x is not free in f (etaRedex_spec); η is an axiom of λβη, so nothing more to prove.",
    entry "lambda.fv" "verified" "The free variables, computed by their definition (freeVars).",
    entry "lambda.db" "verified" "De Bruijn indices, computed by their definition (toDB).",
    entry "lambda.alpha-eq" "verified" "α-equivalence is taken to be equality of de Bruijn forms, which is how the engine defines it; that this agrees with renaming bound variables one at a time is the classical theorem, not proved here.",
    entry "lambda.alpha" "verified" "Binders renamed to avoid capture: the de Bruijn form is kept (toDB_renameFor), so the term is the same up to α.",
    entry "lambda.subst" "verified" "Substitution after the renaming captures nothing (captureFree_renameFor) and is de Bruijn substitution (toDB_substRaw).",
    entry "stlc.var" "verified" "Var: the checker's derivations are typing derivations (check_sound, StlcProofs.lean).",
    entry "stlc.abs" "verified" "→I: the checker's derivations are typing derivations (check_sound).",
    entry "stlc.app" "verified" "→E: the checker's derivations are typing derivations (check_sound).",
    entry "stlc.constraints" "verified" "Inference's equations: every typing of the term solves them (gen_complete), and the type their solution gives is a type of the term, re-checked by the verified checker on the annotated term (check_sound).",
    entry "stlc.split" "verified" "Unification splits an equation of arrows into its parts, which have the same solutions: the substitution found solves every equation (unify_sound) and every solution is an instance of it (unify_most_general).",
    entry "stlc.unify" "verified" "Unification binds a type variable (with the occurs check), keeping the substitution in solved form: the one found solves every equation (unify_sound) and every solution is an instance of it (unify_most_general).",
    entry "stlc.principal" "verified" "Most general (infer_principal, Hindley's theorem): every typing of the term, whatever types its unannotated binders and free variables get, has an instance of the solved type; and it is a type of the term (check_sound, by the checker). The type shown names its variables with names not otherwise in use."]

def capabilities : Json :=
  .obj #[("engine", .str "engine-lean"), ("version", .str "0.1.0-m8"), ("verified", .bool true),
         ("features", .arr #[.str "simplify", .str "expand", .str "factor", .str "diff", .str "linalg", .str "numeric", .str "integrate", .str "plot", .str "manipulate", .str "lambda", .str "order", .str "sum", .str "exptotrig", .str "part", .str "statistics", .str "check", .str "logic", .str "systems"]),
         ("ruleStatus", ruleStatus),
         ("termination", .obj #[("status", .str "proven"), ("theorem", .str "MathEngine.pipelineOrdered"),
           ("summary", .str "Cell evaluation has no step budget: every pipeline rule decreases a five-tier ordering (commands, higher-order diff, matrix literals, the weight M, size) on nodes whose children are normal.")])]

def Rendered.toJson (e : Expr) (paths : Bool) : Json :=
  .obj #[("text", .str e.toText), ("latex", .str (e.toLatex paths))]

/-- A derivation on the wire; a λ-cell's steps also carry their de Bruijn view (`afterDeBruijn`). -/
def derivationJson (d : Derivation) (paths lambda : Bool) : Json :=
  if !lambda then d.toJson paths else
  let steps := (d.steps.zip (lambdaDbSteps d)).map fun (stp, db) =>
    match stp.toJson paths with
    | .obj fields => Json.obj (fields.push ("afterDeBruijn", Rendered.toJson db false))
    | j => j
  .obj #[("input", d.input.toJson), ("steps", .arr steps), ("output", d.output.toJson)]

/-- The work in a reply, with `showWork`: the derivation, or with `outline` only its outline —
each step's rule, explanation and path, without the terms, which are what make the derivation of a
big term large. `engine.steps` sends the derivation itself when it is wanted. -/
def workFields (params : Json) (d : Derivation) (lambda := false) : Array (String × Json) :=
  if !params.getBool "showWork" then #[] else
  let paths := params.getBool "paths"
  let work := if params.getBool "outline" then ("outline", d.outlineJson) else ("derivation", derivationJson d paths lambda)
  #[work, ("inputRendered", Rendered.toJson d.input paths)]

private def errorJson (code msg : String) (span : Option (Nat × Nat) := none) : Json :=
  let err := #[("code", .str code), ("message", .str msg)]
  let err := match span with
    | some (s, e) => err.push ("span", .obj #[("start", .num (toString s)), ("end", .num (toString e))])
    | none => err
  .obj #[("ok", .bool false), ("error", .obj err)]

private def pathOfJson : Json → Option Path
  | .arr xs => xs.toList.mapM fun j => match j with | .num s => s.toNat? | _ => none
  | _ => none

/-- A context as a judgment shows it: each variable once (the innermost binding), outermost first. -/
def ctxShown (Γ : Lam.Ctx) : Lam.Ctx :=
  (Γ.foldl (fun acc (x, T) => if acc.any (·.1 == x) then acc else acc ++ [(x, T)]) []).reverse

/-- The contexts of a derivation's judgments, root first, each once. -/
partial def typingCtxs : Lam.Deriv → List Lam.Ctx
  | .node _ Γ _ _ ps => (ctxShown Γ :: (ps.map typingCtxs).flatten).eraseDups

/-- A typing derivation as a tree for the notebook: each node its judgment `Γ ⊢ t : T`, its rule,
and its premises. When writing the contexts out would make a judgment long, each context is named
(Γ₁, Γ₂, …, each by the one it extends) and the names are explained in a legend. -/
def typingTreeVisual (d : Lam.Deriv) : Json :=
  let tex (e : Expr) := e.toLatex false
  let entryL (x : String) (A : Lam.Ty) := s!"{tex (.var x)} : {tex A.toExpr}"
  let entryT (x : String) (A : Lam.Ty) := s!"{x} : {A.text}"
  let full (Γ : Lam.Ctx) (f : String → Lam.Ty → String) := ", ".intercalate (Γ.map fun (x, A) => f x A)
  let ctxs := (typingCtxs d).filter (!·.isEmpty)
  let long := ctxs.any fun Γ => (full Γ entryT).length > 28
  let named : List (Lam.Ctx × Nat) := if long then ctxs.zip (List.range' 1 ctxs.length) else []
  let ctxL (Γ : Lam.Ctx) := match named.lookup Γ with
    | some k => s!"\\Gamma_\{{k}}"
    | none => full Γ entryL
  -- a context named by the longest named one it extends
  let legend := named.map fun (Γ, k) =>
    let base := (named.filter fun (Δ, j) => j < k && Δ.length < Γ.length && Γ.take Δ.length == Δ).foldl
      (fun best (Δ, j) => match best with | some (B, _) => if Δ.length > B.length then some (Δ, j) else best | none => some (Δ, j)) none
    let (rest, prefL, prefT) := match base with
      | some (Δ, j) => (Γ.drop Δ.length, s!"\\Gamma_\{{j}}, ", s!"Γ{j}, ")
      | none => (Γ, "", "")
    Json.obj #[("latex", .str (s!"\\Gamma_\{{k}} = " ++ prefL ++ full rest entryL)), ("text", .str (s!"Γ{k} = " ++ prefT ++ full rest entryT))]
  let rec node : Lam.Deriv → Json
    | .node rule Γ t T ps =>
      let Γ := ctxShown Γ
      let latex := (if Γ.isEmpty then "" else ctxL Γ ++ " ") ++ "\\vdash " ++ tex t.toExpr ++ " : " ++ tex T.toExpr
      let text := (if Γ.isEmpty then "" else full Γ entryT ++ " ") ++ "⊢ " ++ t.text ++ " : " ++ T.text
      let label := match rule with | "var" => "Var" | "abs" => "→I" | "app" => "→E" | r => r
      .obj #[("rule", .str label), ("latex", .str latex), ("text", .str text), ("premises", .arr (ps.attach.map fun ⟨p, _⟩ => node p).toArray)]
  .obj #[("root", node d), ("legend", .arr legend.toArray)]

/-- A λ-cell's reply: like an ordinary one, plus the de Bruijn renderings and the reading. -/
def evaluateLambda (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
  let (s, r) := lambdaCell (st.get sessionId) cellId src
  let st := st.set sessionId s
  match r with
  | .error (code, msg, span) => (st, errorJson code msg span)
  | .ok res =>
    let paths := params.getBool "paths"
    let out := res.value
    let db := match res.term with | some t => Lam.dbToExpr (Lam.toDB [] t) | none => res.value
    let r := #[("ok", .bool true), ("kind", .str "lambda"), ("value", out.toJson), ("rendered", Rendered.toJson out paths),
      ("renderedDeBruijn", Rendered.toJson db false)]
    let r := match res.reading with | some t => r.push ("reading", .str t) | none => r
    let r := match res.tree with
      | some d => r.push ("visuals", .arr #[.obj #[("kind", .str "typing.tree"), ("data", typingTreeVisual d)]])
      | none => r
    let r := r ++ workFields params res.derivation (lambda := true)
    let r := match res.name with | some n => r.push ("bound", .arr #[.str n]) | none => r
    (st, .obj r)

/-- An order-world cell's reply: the value, the derivation, and the poset to draw. -/
def evaluateOrder (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
  let (s, r) := orderCellN (st.get sessionId) cellId src
  let st := st.set sessionId s
  match r with
  | .error (code, msg, span) => (st, errorJson code msg span)
  | .ok res =>
    let paths := params.getBool "paths"
    let r := #[("ok", .bool true), ("kind", .str "poset"), ("value", res.value.toJson), ("rendered", Rendered.toJson res.value paths)]
    let r := match res.summary with | some t => r.push ("summary", .str t) | none => r
    let r := match res.poset with
      | some P =>
        let hs := Ord.heights P
        r.push ("hasse", .obj #[
          ("nodes", .arr (P.elems.map fun x => Json.obj #[("name", .str x), ("height", .num (toString (hs.getD x 0)))]).toArray),
          ("covers", .arr ((Ord.hasse P).map fun (a, b) => Json.arr #[.str a, .str b]).toArray)])
      | none => r
    let pairs (ps : List (String × String)) : Json := .arr (ps.map fun (a, b) => Json.arr #[.str a, .str b]).toArray
    let strs (xs : List String) : Json := .arr (xs.map Json.str).toArray
    let visuals : Array Json :=
      (match res.graph with
        | some (R, bad, added) => #[.obj #[("kind", .str "relation.digraph"), ("data", .obj #[
            ("nodes", strs R.elems), ("edges", pairs R.pairs), ("bad", pairs bad), ("added", pairs added)])]]
        | none => #[]) ++
      (match res.table with
        | some (o, marks) => #[.obj #[("kind", .str "algebra.optable"), ("data", .obj #[
            ("elems", strs o.elems), ("rows", .arr (o.rows.map strs).toArray), ("marks", pairs marks)])]]
        | none => #[]) ++
      (match res.context with
        | some C => #[.obj #[("kind", .str "context.table"), ("data", .obj #[
            ("objects", strs C.objs), ("attributes", strs C.attrs),
            ("has", .arr (C.objs.map fun o => Json.arr (C.attrs.map fun a => Json.bool (C.has o a)).toArray).toArray)])]]
        | none => #[])
    let r := if visuals.isEmpty then r else r.push ("visuals", .arr visuals)
    let r := r ++ workFields params res.derivation
    let r := match res.name with | some n => r.push ("bound", .arr #[.str n]) | none => r
    (st, .obj r)

/-- A logic cell's reply: the value, the derivation, and for `truthtable` the table to draw
(`visuals`, kind `logic.truthtable`). -/
def evaluateLogic (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
  let (s, r) := logicCell (st.get sessionId) cellId src
  let st := st.set sessionId s
  match r with
  | .error (code, msg, span) => (st, errorJson code msg span)
  | .ok res =>
    let paths := params.getBool "paths"
    let r := #[("ok", .bool true), ("kind", .str "logic"), ("value", res.value.toJson), ("rendered", Rendered.toJson res.value paths)]
    let r := match res.table with
      | some (vs, rows) =>
        let formula := match res.derivation.input with | .fn "truthtable" [f] => f | e => e
        r.push ("visuals", .arr #[.obj #[("kind", .str "logic.truthtable"), ("data", .obj #[
          ("vars", .arr (vs.map Json.str).toArray), ("formula", Rendered.toJson formula false),
          ("rows", .arr (rows.map fun row => Json.arr (row.map Json.bool).toArray).toArray)])]])
      | none => r
    let r := r ++ workFields params res.derivation
    let r := match res.name with | some n => r.push ("bound", .arr #[.str n]) | none => r
    (st, .obj r)

/-- A systems cell's reply: the value, the derivation (a trace is a step per action), a note, and
the state graph (`visuals`, kind `relation.digraph`) with a counterexample's transitions marked. -/
def evaluateSystem (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
  let (s, r) := systemCellN (st.get sessionId) cellId src
  let st := st.set sessionId s
  match r with
  | .error (code, msg, span) => (st, errorJson code msg span)
  | .ok res =>
    let paths := params.getBool "paths"
    let r := #[("ok", .bool true), ("kind", .str "system"), ("value", res.value.toJson), ("rendered", Rendered.toJson res.value paths)]
    let r := match res.summary with | some t => r.push ("summary", .str t) | none => r
    let r := match res.graph with
      | some (R, bad, added) =>
        let pairs (ps : List (String × String)) : Json := .arr (ps.map fun (a, b) => Json.arr #[.str a, .str b]).toArray
        let layers : Array (String × Json) := if res.layers.isEmpty then #[] else #[("layers", .arr (res.layers.map fun n => Json.num (toString n)).toArray)]
        -- where each step of the work is on the graph: the transition it takes, or the state it is at
        let mark (st : Step) : Json :=
          match Sys.labelOfStateExpr st.before, Sys.labelOfStateExpr st.after with
          | some b, some a =>
            if R.pairs.contains (b, a) then .obj #[("edge", .arr #[.str b, .str a])]
            else if R.elems.contains a then .obj #[("node", .str a)] else .null
          | _, some a => if R.elems.contains a then .obj #[("node", .str a)] else .null
          | some b, _ => if R.elems.contains b then .obj #[("node", .str b)] else .null
          | none, none => .null
        let marks := res.derivation.steps.map mark
        let stepsField : Array (String × Json) := if marks.all (fun | .null => true | _ => false) then #[] else #[("steps", .arr marks)]
        r.push ("visuals", .arr #[.obj #[("kind", .str "relation.digraph"), ("data", .obj (#[
          ("nodes", .arr (R.elems.map Json.str).toArray), ("edges", pairs R.pairs), ("bad", pairs bad), ("added", pairs added)] ++ layers ++ stepsField))]])
      | none => r
    let r := match res.spacetime with
      | some (D, evOf) =>
        let ev (e : Rep.DEvent) : Json := .obj #[("lane", .str e.lane), ("label", .str e.label), ("state", .str e.state)]
        r.push ("visuals", .arr #[.obj #[("kind", .str "replicas.spacetime"), ("data", .obj #[
          ("lanes", .arr (D.lanes.map Json.str).toArray), ("events", .arr (D.events.map ev)),
          ("messages", .arr (D.messages.map fun (a, b) => Json.arr #[.num (toString a), .num (toString b)]).toArray),
          ("steps", .arr (evOf.map fun es => Json.arr (es.map fun i => Json.num (toString i)).toArray))])]])
      | none => r
    let r := r ++ workFields params res.derivation
    let r := match res.name with | some n => r.push ("bound", .arr #[.str n]) | none => r
    (st, .obj r)

/-- Number the evaluation (`In[n]`), remember its output for `%`, and put the label in the reply. -/
def withLabel (st : Store) (sessionId cellId : String) (j : Json) : Store × Json :=
  let s := st.get sessionId
  let ok := match j.get? "ok" with | some (.bool true) => true | _ => false
  let out := if ok then (s.cells.lookup cellId).map (·.output) else none
  let (s, n) := s.tick out
  let j := match j with
    | .obj fs => Json.obj (fs.push ("label", .num (toString n)))
    | j => j
  (st.set sessionId s, j)

/-- `withLabel`, unless the request is `quiet`: a scene's samples (`quiet: true` on `engine.plot` and
`engine.manipulate`) are not evaluations. The session is left as it was before the request (`st0`),
with no `In[n]` taken and `%` untouched. -/
def numbered (st0 st : Store) (params : Json) (sessionId cellId : String) (j : Json) : Store × Json :=
  if params.getBool "quiet" then (st0, j) else withLabel st sessionId cellId j

/-- The warning for a free `e`: the letter is a variable, not Euler's number `ℯ`. -/
def eWarning : String :=
  "e here is a variable, not Euler's number: e^x is not exp(x) and does not simplify like it (only N gives e Euler's value). For the constant, type \\e (it shows as ℯ), or write exp(x)."

/-- Warnings about a cell's input (after the session's bindings are substituted), not counting the
parameters a function definition binds. -/
def inputWarnings (input : Expr) (params : List String) : List String :=
  if (Expr.freeVars input).contains "e" && !params.contains "e" then [eWarning] else []

def evaluate (st : Store) (params : Json) : Store × Json :=
  match params.getStr? "source" with
  | none => (st, errorJson "params" "missing source")
  | some src =>
    let sessionId := (params.getStr? "sessionId").getD ""
    let cellId := (params.getStr? "cellId").getD ""
    let (st, j) := evaluateCore st params sessionId cellId src
    withLabel st sessionId cellId j
where
  evaluateCore (st : Store) (params : Json) (sessionId cellId src : String) : Store × Json :=
    -- a λ-command (`type: f : A → B ⊢ f`) may hold a connective or a call; it is the λ-world's
    let lamCmd := (Lam.commandHead src).isSome
    if !lamCmd && Sys.isSystemSource src then evaluateSystem st params sessionId cellId src else
    if !lamCmd && Ord.isOrderSource src then evaluateOrder st params sessionId cellId src else
      if !lamCmd && Logic.isLogicSource src then evaluateLogic st params sessionId cellId src else
      if isLambdaCell (st.get sessionId) src then evaluateLambda st params sessionId cellId src else
      let (s, r) := evaluateCell (st.get sessionId) cellId src
      let st := st.set sessionId s
      match r with
      | .error (code, msg, span) => (st, errorJson code msg span)
      | .ok (stmt, out, d) =>
        let paths := params.getBool "paths"
        let sem := if mentionsI d.input || mentionsI out then "complex" else "real"
        let res := #[("ok", .bool true), ("value", out.toJson), ("rendered", Rendered.toJson out paths), ("semantics", .str sem)]
        let res := res ++ workFields params d
        let ps := match stmt with | .«let» _ ps _ => ps | _ => []
        let warnings := inputWarnings d.input ps
        let res := if warnings.isEmpty then res else res.push ("warnings", .arr (warnings.map .str).toArray)
        let res := match stmt with
          | .«let» name [] _ => res.push ("bound", .arr #[.str name])
          | .«let» name ps _ => (res.push ("bound", .arr #[.str name])).push ("params", .arr (ps.map .str).toArray)
          | _ => res
        (st, .obj res)

private def floatJson (x : Float) : Json := .num (toString x)

/-- A plot's own fields on the wire: the variable and range, each curve's term and samples, and
the epicycles' circles. -/
def plotFields (pl : Plot) : Array (String × Json) :=
  let ptsJson (pts : Array (Float × Option Float)) : Json :=
    .arr (pts.map fun (t, y) => Json.arr #[floatJson t, match y with | some v => floatJson v | none => .null])
  let series := pl.series.map fun sr => Json.obj #[("rendered", Rendered.toJson sr.term false), ("points", ptsJson sr.points), ("parametric", .bool sr.parametric)]
  let terms := pl.terms.map fun (k, c, ex) => Json.obj (#[("k", .num (toString k)), ("re", floatJson c.re), ("im", floatJson c.im)] ++
    (match ex with | some e => #[("rendered", Rendered.toJson e false)] | none => #[]))
  #[("var", .str pl.var), ("from", floatJson pl.from_), ("to", floatJson pl.to), ("series", .arr series), ("terms", .arr terms)]

def plot (st : Store) (params : Json) : Store × Json :=
  let st0 := st
  match params.getStr? "source" with
  | none => (st, errorJson "params" "missing source")
  | some src =>
    let sessionId := (params.getStr? "sessionId").getD ""
    let cellId := (params.getStr? "cellId").getD ""
    let (s, r) := plotCell (st.get sessionId) cellId src
    let st := st.set sessionId s
    let (st, j) := match r with
    | .error (code, msg, span) => (st, errorJson code msg span)
    | .ok (_, out, d, pl) =>
      let paths := params.getBool "paths"
      let res := #[("ok", .bool true), ("kind", .str "plot"), ("value", out.toJson), ("rendered", Rendered.toJson out paths)] ++ plotFields pl
      let res := res ++ workFields params d
      (st, .obj res)
    numbered st0 st params sessionId cellId j

/-- `manipulate(e, p, from, to[, frames])`: every frame's value of `p` (as a number and as the
engine prints it), the body's normal form there, and a plot body's samples; the cell's own value,
rendering and work are the first frame's. -/
def manipulate (st : Store) (params : Json) : Store × Json :=
  let st0 := st
  match params.getStr? "source" with
  | none => (st, errorJson "params" "missing source")
  | some src =>
    let sessionId := (params.getStr? "sessionId").getD ""
    let cellId := (params.getStr? "cellId").getD ""
    let (s, r) := manipulateCell (st.get sessionId) cellId src
    let st := st.set sessionId s
    let (st, j) := match r with
    | .error (code, msg, span) => (st, errorJson code msg span)
    | .ok (out, d, p, frames) =>
      let paths := params.getBool "paths"
      -- a calculation is sent when it has more than its result
      let workJson (w : Array Expr) : Array (String × Json) :=
        if w.size ≤ 1 then #[] else #[("work", Json.arr (w.map fun e => Rendered.toJson e false))]
      let plotJson (pl : Option Plot) : Array (String × Json) :=
        match pl with | some pl => #[("plot", Json.obj (plotFields pl))] | none => #[]
      let partJson (pt : FramePart) : Json := Json.obj (#[("rendered", Rendered.toJson pt.output false)] ++
        (match pt.label with | some l => #[("label", Json.str l)] | none => #[]) ++ plotJson pt.plot ++ workJson pt.work)
      let frameJson (f : Frame) : Json := Json.obj (#[("value", floatJson f.value.toFloat),
        ("valueRendered", Rendered.toJson (.num f.value) false), ("rendered", Rendered.toJson f.output false)] ++
        plotJson f.plot ++ workJson f.work ++
        (if f.parts.isEmpty then #[] else #[("parts", Json.arr (f.parts.map partJson))]))
      let res := #[("ok", .bool true), ("kind", .str "manipulate"), ("value", out.toJson), ("rendered", Rendered.toJson out paths),
        ("param", .str p), ("frames", .arr (frames.map frameJson))]
      (st, .obj (res ++ workFields params d))
    numbered st0 st params sessionId cellId j

def explain (st : Store) (params : Json) : Except String Json := do
  let sessionId := (params.getStr? "sessionId").getD ""
  let cellId := (params.getStr? "cellId").getD ""
  let path ← match params.get? "path" >>= pathOfJson with | some p => pure p | none => throw "missing or malformed path"
  -- which term the path is into: the output (default), the input, or the term after step n
  let ref : TermRef := match params.get? "term" with
    | some t => match t.getStr? "kind" with
      | some "input" => .input
      | some "step" => match t.get? "index" with
        | some (.num n) => .step (n.toNat?.getD 0)
        | _ => .output
      | _ => .output
    | none => .output
  let (sub, steps, rels) ← explainCell (st.get sessionId) cellId path ref
  let traceJson := rels.map fun (i, r) => Json.obj #[("index", .num (toString i)), ("relation", .str r.toString)]
  pure (.obj #[("subterm", sub.toJson), ("rendered", Rendered.toJson sub false), ("steps", .arr (steps.map Step.toJson)),
    ("trace", .arr traceJson.toArray)])

/-- A cell's derivation, from the session that evaluated it: what `outline` replies leave out. -/
def steps (st : Store) (params : Json) : Except String Json := do
  let sessionId := (params.getStr? "sessionId").getD ""
  let cellId := (params.getStr? "cellId").getD ""
  match (st.get sessionId).cells.lookup cellId with
  | none => throw s!"unknown cell {cellId}: the session has not evaluated it"
  | some cell =>
    let paths := params.getBool "paths"
    let d := cell.derivation
    pure (.obj #[("derivation", derivationJson d paths cell.lambda), ("inputRendered", Rendered.toJson d.input paths)])

/-- An exercise (`Exercise.lean`): the question's value and worked solution, and whether the
answer, if one is sent, reduces to the same normal form. Nothing is bound or numbered. -/
def check (st : Store) (params : Json) : Store × Json :=
  match params.getStr? "source" with
  | none => (st, errorJson "params" "missing source")
  | some src =>
    let sessionId := (params.getStr? "sessionId").getD ""
    let cellId := (params.getStr? "cellId").getD ""
    let answer := (params.getStr? "answer").filter (!·.trimAscii.isEmpty)
    let (s, r) := checkAnswer (st.get sessionId) cellId src answer
    let st := st.set sessionId s
    match r with
    | .error (code, msg, span) => (st, errorJson code msg span)
    | .ok res =>
      let paths := params.getBool "paths"
      let r := #[("ok", .bool true), ("kind", .str (if res.lambda then "lambda" else "exercise")),
        ("rendered", Rendered.toJson res.expected paths), ("normalForm", Rendered.toJson res.expectedCanon false),
        ("inputRendered", Rendered.toJson res.derivation.input paths)]
      let r := r ++ (workFields params res.derivation res.lambda).filter (·.1 != "inputRendered")
      let r := match res.given with
        | none => r
        | some (.ok c) => (r.push ("answer", .obj #[("ok", .bool true), ("rendered", Rendered.toJson c.value false),
            ("normalForm", Rendered.toJson c.canon false)])).push ("equivalent", .bool res.equivalent)
        | some (.error (code, msg, span)) =>
          let e := errorJson code msg span
          (r.push ("answer", e)).push ("equivalent", .bool false)
      (st, .obj r)

def dispatch (st : Store) (req : Json) : Store × Json :=
  let id := (req.get? "id").getD .null
  let params := (req.get? "params").getD (.obj #[])
  let reply (r : Json) : Json := .obj #[("jsonrpc", .str "2.0"), ("id", id), ("result", r)]
  let fail (code : Int) (msg : String) : Json :=
    .obj #[("jsonrpc", .str "2.0"), ("id", id), ("error", .obj #[("code", .num (toString code)), ("message", .str msg)])]
  match req.getStr? "method" with
  | some "engine.capabilities" => (st, reply capabilities)
  | some "engine.evaluate" => let (st, r) := evaluate st params; (st, reply r)
  | some "engine.plot" => let (st, r) := plot st params; (st, reply r)
  | some "engine.manipulate" => let (st, r) := manipulate st params; (st, reply r)
  | some "engine.check" => let (st, r) := check st params; (st, reply r)
  | some "engine.explain" =>
    match explain st params with
    | .ok r => (st, reply r)
    | .error msg => (st, fail (-32000) msg)
  | some "engine.steps" =>
    match steps st params with
    | .ok r => (st, reply r)
    | .error msg => (st, fail (-32000) msg)
  | some "engine.resetSession" => (st.reset ((params.getStr? "sessionId").getD ""), reply (.obj #[("ok", .bool true)]))
  | some m => (st, fail (-32601) s!"unknown method {m}")
  | none => (st, fail (-32600) "missing method")

/-- The single entry point. C symbol `mathengine_handle_state`: `lean_object* (lean_object* store, lean_object* request)`,
returning the pair (new store, response). Both arguments are consumed. -/
@[export mathengine_handle_state]
def handleS (st : Store) (raw : String) : Store × String :=
  match Json.parse raw with
  | .error msg => (st, (Json.obj #[("jsonrpc", .str "2.0"), ("id", .null), ("error", .obj #[("code", .num "-32700"), ("message", .str msg)])]).render)
  | .ok req => let (st, r) := dispatch st req; (st, r.render)

/-- Stateless convenience (fresh store) for tests. -/
def handle (raw : String) : String := (handleS [] raw).2

end MathEngine
