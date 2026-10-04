import Proofs.SimpReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Rat.Floor
/-!
# `N` is certified: the interval holds the value, and the digits are within a unit of it

`N(a)` evaluates `a` over the rationals to an interval (`Ival.ieval`, `Interval.lean` in the engine)
and prints the most digits, up to 15, that the interval pins down (`Ival.certify`). Here:

- `ieval_sound`: the interval holds `a`'s real value (`evalR`), wherever the constants `e` and `π`
  have theirs;
- `certify_sound`: every number in the interval is within `u` of the decimal `v` shown;
- `cmdN_sound`: so the decimal `N` gives is within `u` of the exact value.

Each operation is proved separately: rounding outward (`lower_le`, `le_upper`), the arithmetic
(`mul_mem` by the corner products), `exp` by Taylor's theorem with remainder (`Real.exp_bound`) and
squaring, `sin` and `cos` by the remainder for `exp(iy)` (`Complex.exp_bound`) and doubling, and an
interval by the midpoint and the 1-Lipschitz bound (`Real.abs_sin_sub_sin_le`); `ln` by `exp`
(`Real.le_log_iff_exp_le`), `sqrt` by squaring, `π` by `Real.pi_gt_d20` and `Real.pi_lt_d20`.
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Ival

/-- `x` lies in the interval. -/
def Mem (a : I) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

/-! ## Rounding -/

theorem pow2_pos (k : ℤ) : (0 : ℚ) < pow2 k := by
  unfold pow2; split <;> positivity

theorem floorTo_le (k : ℤ) (x : ℚ) : floorTo k x ≤ x := by
  unfold floorTo
  dsimp only
  have hp := pow2_pos k
  have h : ((((x / pow2 k).num / ((x / pow2 k).den : ℤ) : ℤ) : ℚ)) ≤ x / pow2 k := by
    rw [← Rat.floor_def']; exact Int.floor_le _
  calc _ ≤ x / pow2 k * pow2 k := by gcongr
    _ = x := div_mul_cancel₀ x hp.ne'

theorem lower_le (x : ℚ) : lower x ≤ x := floorTo_le _ _
theorem le_upper (x : ℚ) : x ≤ upper x := by
  unfold upper; have := floorTo_le (keepExp x) (-x); linarith

theorem round_mem {a : I} {x : ℝ} (h : Mem a x) : Mem (round a) x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨le_trans ?_ h1, le_trans h2 ?_⟩
  · exact_mod_cast lower_le a.lo
  · exact_mod_cast le_upper a.hi

theorem point_mem (q : ℚ) : Mem (point q) (q : ℝ) := ⟨le_refl _, le_refl _⟩

/-! ## Arithmetic -/

theorem add_mem {a b : I} {x y : ℝ} (ha : Mem a x) (hb : Mem b y) : Mem (add a b) (x + y) := by
  apply round_mem
  constructor <;> push_cast <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem neg_mem {a : I} {x : ℝ} (ha : Mem a x) : Mem (neg a) (-x) := by
  constructor <;> simp only [neg] <;> push_cast <;> linarith [ha.1, ha.2]

/-- `t·y` for `t` between `a` and `b` lies between `a·y` and `b·y`. -/
theorem mul_between {a b t : ℝ} (h1 : a ≤ t) (h2 : t ≤ b) (y : ℝ) :
    min (a * y) (b * y) ≤ t * y ∧ t * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨min_le_of_left_le (mul_le_mul_of_nonneg_right h1 hy),
      le_max_of_le_right (mul_le_mul_of_nonneg_right h2 hy)⟩
  · exact ⟨min_le_of_right_le (mul_le_mul_of_nonpos_right h2 hy),
      le_max_of_le_left (mul_le_mul_of_nonpos_right h1 hy)⟩

theorem mul_mem {a b : I} {x y : ℝ} (ha : Mem a x) (hb : Mem b y) : Mem (mul a b) (x * y) := by
  apply round_mem
  obtain ⟨hx1, hx2⟩ := ha
  obtain ⟨hy1, hy2⟩ := hb
  have e1 := mul_between hx1 hx2 y
  have e2 := mul_between hy1 hy2 (a.lo : ℝ)
  have e3 := mul_between hy1 hy2 (a.hi : ℝ)
  simp only [mul_comm _ (a.lo : ℝ), mul_comm _ (a.hi : ℝ)] at e2 e3
  constructor <;> push_cast
  · exact le_trans (min_le_min e2.1 e3.1) e1.1
  · exact le_trans e1.2 (max_le_max e2.2 e3.2)

theorem inv_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : inv a = some b) : Mem b x⁻¹ := by
  unfold inv at h
  split at h
  · rename_i hs
    cases h
    apply round_mem
    obtain ⟨h1, h2⟩ := ha
    rcases hs with hs | hs
    · have hs' : (0 : ℝ) < a.lo := by exact_mod_cast hs
      have hx : 0 < x := lt_of_lt_of_le hs' h1
      constructor <;> push_cast
      · rw [one_div]; exact inv_anti₀ hx h2
      · rw [one_div]; exact inv_anti₀ hs' h1
    · have hs' : (a.hi : ℝ) < 0 := by exact_mod_cast hs
      have hx : x < 0 := lt_of_le_of_lt h2 hs'
      constructor <;> push_cast
      · rw [one_div]; exact (inv_le_inv_of_neg hs' hx).mpr h2
      · rw [one_div]; exact (inv_le_inv_of_neg hx (lt_of_le_of_lt h1 (lt_of_le_of_lt h2 hs'))).mpr h1
  · cases h

theorem npow_mem {a : I} {x : ℝ} (ha : Mem a x) : ∀ n : ℕ, Mem (npow a n) (x ^ n)
  | 0 => by simpa [npow] using point_mem 1
  | n + 1 => by rw [npow, pow_succ]; exact mul_mem (npow_mem ha n) ha

theorem abs_mem {a : I} {x : ℝ} (ha : Mem a x) : Mem (Ival.abs a) |x| := by
  obtain ⟨h1, h2⟩ := ha
  unfold Ival.abs
  split
  · rename_i h
    have : (0 : ℝ) ≤ a.lo := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩
  · split
    · rename_i _ h
      have : (a.hi : ℝ) ≤ 0 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; exact neg_mem ⟨h1, h2⟩
    · constructor <;> push_cast
      · exact abs_nonneg x
      · rcases le_total 0 x with hx | hx
        · rw [abs_of_nonneg hx]; exact le_max_of_le_right h2
        · rw [abs_of_nonpos hx]; exact le_max_of_le_left (by linarith)

theorem sign_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : Ival.sign a = some b) : Mem b (Real.sign x) := by
  obtain ⟨h1, h2⟩ := ha
  unfold Ival.sign at h
  split at h
  · rename_i hs; cases h
    have : (0 : ℝ) < a.lo := by exact_mod_cast hs
    rw [Real.sign_of_pos (by linarith)]; simpa using point_mem 1
  · split at h
    · rename_i _ hs; cases h
      have : (a.hi : ℝ) < 0 := by exact_mod_cast hs
      rw [Real.sign_of_neg (by linarith)]; simpa using point_mem (-1)
    · split at h
      · rename_i _ _ hs; cases h
        obtain ⟨hl, hh⟩ := hs
        have : x = 0 := by
          have e1 : (a.lo : ℝ) = 0 := by exact_mod_cast hl
          have e2 : (a.hi : ℝ) = 0 := by exact_mod_cast hh
          linarith
        rw [this, Real.sign_zero]; simpa using point_mem 0
      · cases h

theorem widen_mem {a : I} {x y r : ℝ} {q : ℚ} (ha : Mem a y) (hr : (q : ℝ) = r) (hxy : |x - y| ≤ r) :
    Mem (widen a q) x := by
  apply round_mem
  obtain ⟨h1, h2⟩ := ha
  rw [abs_le] at hxy
  constructor <;> push_cast <;> rw [hr] <;> linarith [hxy.1, hxy.2]

theorem point_mem' {q : ℚ} {x : ℝ} (h : (q : ℝ) = x) : Mem (point q) x := h ▸ point_mem q

/-! ## `exp` -/

theorem fact_eq : ∀ n : ℕ, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by rw [fact, Nat.factorial_succ, fact_eq n]

theorem rabs_cast (y : ℚ) : ((rabs y : ℚ) : ℝ) = |(y : ℝ)| := by
  unfold rabs
  split
  · rename_i h; have : (y : ℝ) < 0 := by exact_mod_cast h
    rw [abs_of_neg this]; push_cast; ring
  · rename_i h; have : (0 : ℝ) ≤ y := by exact_mod_cast not_lt.mp h
    rw [abs_of_nonneg this]

theorem expSum_cast (y : ℚ) : ∀ n : ℕ,
    ((expSum y n : ℚ) : ℝ) = ∑ m ∈ Finset.range n, (y : ℝ) ^ m / (m.factorial : ℝ)
  | 0 => by simp [expSum]
  | n + 1 => by rw [expSum, Finset.sum_range_succ, ← expSum_cast y n, fact_eq]; push_cast; ring

theorem remainder_cast (y : ℚ) (n : ℕ) :
    ((remainder y n : ℚ) : ℝ) = |(y : ℝ)| ^ n * ((n.succ : ℝ) / (n.factorial * n : ℝ)) := by
  unfold remainder
  push_cast
  rw [rabs_cast, fact_eq]
  ring

theorem two_pow_cast (k : ℕ) : ((((2 ^ k : ℕ) : ℚ)) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring

theorem sqN_mem : ∀ (k : ℕ) (a : I) (z : ℝ), Mem a (Real.exp z) → Mem (sqN k a) (Real.exp (z * 2 ^ k))
  | 0, a, z, h => by simpa [sqN] using h
  | k + 1, a, z, h => by
    rw [sqN]
    have h2 : Mem (mul a a) (Real.exp (2 * z)) := by
      rw [show 2 * z = z + z by ring, Real.exp_add]; exact mul_mem h h
    have := sqN_mem k _ _ h2
    rwa [show 2 * z * 2 ^ k = z * 2 ^ (k + 1) by ring] at this

theorem expPoint_mem {q : ℚ} {a : I} (h : expPoint q = some a) : Mem a (Real.exp q) := by
  unfold expPoint at h
  dsimp only at h
  split at h
  · rename_i hy
    cases h
    set k := halvings q
    set y : ℚ := q / ((2 ^ k : ℕ) : ℚ) with hydef
    have hy' : |(y : ℝ)| ≤ 1 := by rw [← rabs_cast]; exact_mod_cast hy
    have hb := Real.exp_bound hy' (n := terms) (by decide)
    rw [← expSum_cast, ← remainder_cast] at hb
    have base : Mem (round ⟨expSum y terms - remainder y terms, expSum y terms + remainder y terms⟩) (Real.exp y) := by
      apply round_mem
      rw [abs_le] at hb
      constructor <;> push_cast <;> linarith [hb.1, hb.2]
    have := sqN_mem k _ _ base
    have hq : (y : ℝ) * 2 ^ k = q := by
      rw [hydef]; push_cast; field_simp
    rwa [hq] at this
  · cases h

theorem expI_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : expI a = some b) : Mem b (Real.exp x) := by
  unfold expI at h
  cases hl : expPoint a.lo with
  | none => simp [hl] at h
  | some l =>
  cases hu : expPoint a.hi with
  | none => simp [hl, hu] at h
  | some u =>
  simp [hl, hu] at h
  subst h
  exact ⟨le_trans (expPoint_mem hl).1 (Real.exp_le_exp.mpr ha.1),
    le_trans (Real.exp_le_exp.mpr ha.2) (expPoint_mem hu).2⟩

/-! ## `sin`, `cos` -/

theorem I_pow_mod (m : ℕ) : Complex.I ^ m = Complex.I ^ (m % 4) := by
  conv_lhs => rw [← Nat.div_add_mod m 4, pow_add, pow_mul, Complex.I_pow_four, one_pow, one_mul]

theorem term_eq (y : ℝ) (n : ℕ) :
    ((y : ℂ) * Complex.I) ^ n / (n.factorial : ℂ) = (((y ^ n / n.factorial : ℝ)) : ℂ) * Complex.I ^ (n % 4) := by
  rw [mul_pow, I_pow_mod]; push_cast; ring

theorem trigSum_cast (y : ℚ) : ∀ n : ℕ,
    (∑ m ∈ Finset.range n, (((y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re = ((cosSum y n : ℚ) : ℝ) ∧
    (∑ m ∈ Finset.range n, (((y : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).im = ((sinSum y n : ℚ) : ℝ)
  | 0 => by simp [cosSum, sinSum]
  | n + 1 => by
    obtain ⟨ih1, ih2⟩ := trigSum_cast y n
    rw [Finset.sum_range_succ, Complex.add_re, Complex.add_im, ih1, ih2, term_eq,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul, cosSum, sinSum, fact_eq]
    have i3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases this with h | h | h | h
    · simp [h, show n % 2 = 0 by omega]
    · simp [h, show n % 2 = 1 by omega]
    · simp [h, show n % 2 = 0 by omega, Complex.I_sq]; ring
    · simp [h, show n % 2 = 1 by omega, i3]; ring

theorem trig_bound (y : ℚ) (hy : |(y : ℝ)| ≤ 1) :
    |Real.cos y - cosSum y terms| ≤ remainder y terms ∧ |Real.sin y - sinSum y terms| ≤ remainder y terms := by
  have hn : ‖((y : ℝ) : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hy
  have hb := Complex.exp_bound hn (n := terms) (by decide)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hb
  have hr : |(y : ℝ)| ^ terms * ((terms.succ : ℝ) * (terms.factorial * terms : ℝ)⁻¹) = remainder y terms := by
    rw [remainder_cast]; ring
  rw [hr] at hb
  obtain ⟨h1, h2⟩ := trigSum_cast y terms
  constructor
  · rw [← Complex.exp_ofReal_mul_I_re, ← h1, ← Complex.sub_re]
    exact le_trans (Complex.abs_re_le_norm _) hb
  · rw [← Complex.exp_ofReal_mul_I_im, ← h2, ← Complex.sub_im]
    exact le_trans (Complex.abs_im_le_norm _) hb

theorem dbl_mem : ∀ (k : ℕ) (s c : I) (z : ℝ), Mem s (Real.sin z) → Mem c (Real.cos z) →
    Mem (dbl k (s, c)).1 (Real.sin (z * 2 ^ k)) ∧ Mem (dbl k (s, c)).2 (Real.cos (z * 2 ^ k))
  | 0, s, c, z, hs, hc => by simpa [dbl] using And.intro hs hc
  | k + 1, s, c, z, hs, hc => by
    rw [dbl]
    have h2 : (((2 : ℚ) : ℝ)) = 2 := by norm_num
    have hs2 : Mem (mul (point 2) (mul s c)) (Real.sin (2 * z)) := by
      rw [Real.sin_two_mul, mul_assoc]; exact mul_mem (point_mem' h2) (mul_mem hs hc)
    have hc2 : Mem (add (mul (point 2) (mul c c)) (point (-1))) (Real.cos (2 * z)) := by
      rw [Real.cos_two_mul, sq, sub_eq_add_neg]
      exact add_mem (mul_mem (point_mem' h2) (mul_mem hc hc)) (point_mem' (by norm_num))
    have := dbl_mem k _ _ _ hs2 hc2
    rwa [show 2 * z * 2 ^ k = z * 2 ^ (k + 1) by ring] at this

theorem sinCosPoint_mem {q : ℚ} {s c : I} (h : sinCosPoint q = some (s, c)) :
    Mem s (Real.sin q) ∧ Mem c (Real.cos q) := by
  unfold sinCosPoint at h
  dsimp only at h
  split at h
  · rename_i hy
    simp only [Option.some.injEq] at h
    set k := halvings q
    set y : ℚ := q / ((2 ^ k : ℕ) : ℚ) with hydef
    have hy' : |(y : ℝ)| ≤ 1 := by rw [← rabs_cast]; exact_mod_cast hy
    obtain ⟨hcb, hsb⟩ := trig_bound y hy'
    rw [abs_le] at hcb hsb
    have bs : Mem (round ⟨sinSum y terms - remainder y terms, sinSum y terms + remainder y terms⟩) (Real.sin y) := by
      apply round_mem; constructor <;> push_cast <;> linarith [hsb.1, hsb.2]
    have bc : Mem (round ⟨cosSum y terms - remainder y terms, cosSum y terms + remainder y terms⟩) (Real.cos y) := by
      apply round_mem; constructor <;> push_cast <;> linarith [hcb.1, hcb.2]
    have := dbl_mem k _ _ _ bs bc
    have hq : (y : ℝ) * 2 ^ k = q := by
      rw [hydef]; push_cast; field_simp
    rw [hq, h] at this
    exact this
  · cases h

/-- Within the interval, a number is within its radius of its midpoint. -/
theorem near_mid {a : I} {x : ℝ} (ha : Mem a x) : |x - (mid a : ℝ)| ≤ (rad a : ℝ) := by
  obtain ⟨h1, h2⟩ := ha
  unfold mid rad; push_cast
  rw [abs_le]; constructor <;> linarith

theorem sinI_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : sinI a = some b) : Mem b (Real.sin x) := by
  unfold sinI at h
  cases hsc : sinCosPoint (mid a) with
  | none => simp [hsc] at h
  | some sc =>
  obtain ⟨s, c⟩ := sc
  simp [hsc] at h
  subst h
  exact widen_mem (sinCosPoint_mem hsc).1 rfl
    (le_trans (Real.abs_sin_sub_sin_le _ _) (near_mid ha))

theorem cosI_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : cosI a = some b) : Mem b (Real.cos x) := by
  unfold cosI at h
  cases hsc : sinCosPoint (mid a) with
  | none => simp [hsc] at h
  | some sc =>
  obtain ⟨s, c⟩ := sc
  simp [hsc] at h
  subst h
  exact widen_mem (sinCosPoint_mem hsc).2 rfl
    (le_trans (Real.abs_cos_sub_cos_le _ _) (near_mid ha))

/-! ## `ln`, `sqrt`, `π` -/

theorem lnPoint_mem {q : ℚ} {b : I} (h : lnPoint q = some b) : Mem b (Real.log q) := by
  unfold lnPoint at h
  dsimp only at h
  split at h
  · rename_i hq
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    split at h
    · rename_i ea eb hea heb
      split at h
      · rename_i hc
        cases h
        obtain ⟨h1, h2⟩ := hc
        have e1 := (expPoint_mem hea).2
        have e2 := (expPoint_mem heb).1
        have h1' : (ea.hi : ℝ) ≤ q := by exact_mod_cast h1
        have h2' : (q : ℝ) ≤ eb.lo := by exact_mod_cast h2
        exact ⟨(Real.le_log_iff_exp_le hq').mpr (le_trans e1 h1'),
          (Real.log_le_iff_le_exp hq').mpr (le_trans h2' e2)⟩
      · cases h
    · cases h
  · cases h

theorem lnI_mem {a b : I} {x : ℝ} (ha : Mem a x) (hpos : 0 < a.lo) (h : lnI a = some b) :
    Mem b (Real.log x) := by
  unfold lnI at h
  cases hl : lnPoint a.lo with
  | none => simp [hl] at h
  | some l =>
  cases hu : lnPoint a.hi with
  | none => simp [hl, hu] at h
  | some u =>
  simp [hl, hu] at h
  subst h
  have hp : (0 : ℝ) < a.lo := by exact_mod_cast hpos
  exact ⟨le_trans (lnPoint_mem hl).1 (Real.log_le_log hp ha.1),
    le_trans (Real.log_le_log (lt_of_lt_of_le hp ha.1) ha.2) (lnPoint_mem hu).2⟩

theorem sqrt_between {q a b : ℚ} (hq : 0 ≤ q) (h1 : a * a ≤ q) (h0 : 0 ≤ a) (h2 : q ≤ b * b)
    (h3 : 0 ≤ b) : Mem ⟨a, b⟩ (Real.sqrt q) := by
  have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
  have ha : (0 : ℝ) ≤ a := by exact_mod_cast h0
  have hb : (0 : ℝ) ≤ b := by exact_mod_cast h3
  have h1' : (a : ℝ) ^ 2 ≤ q := by rw [sq]; exact_mod_cast h1
  have h2' : (q : ℝ) ≤ (b : ℝ) ^ 2 := by rw [sq]; exact_mod_cast h2
  exact ⟨(Real.le_sqrt ha hq').mpr h1', (Real.sqrt_le_left hb).mpr h2'⟩

theorem sqrtPoint_mem {q : ℚ} {b : I} (h : sqrtPoint q = some b) : Mem b (Real.sqrt q) := by
  unfold sqrtPoint at h
  dsimp only at h
  split at h
  · rename_i hq; cases h; subst hq; simpa using point_mem 0
  · split at h
    · rename_i _ hq
      split at h
      · rename_i hc
        cases h
        obtain ⟨h1, h2, h3⟩ := hc
        exact sqrt_between hq.le h1 (le_max_left _ _) h2 h3
      · cases h
    · cases h

theorem sqrtI_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : sqrtI a = some b) : Mem b (Real.sqrt x) := by
  unfold sqrtI at h
  split at h
  · cases h
  · cases hl : sqrtPoint a.lo with
    | none => simp [hl] at h
    | some l =>
    cases hu : sqrtPoint a.hi with
    | none => simp [hl, hu] at h
    | some u =>
    simp [hl, hu] at h
    subst h
    exact ⟨le_trans (sqrtPoint_mem hl).1 (Real.sqrt_le_sqrt ha.1),
      le_trans (Real.sqrt_le_sqrt ha.2) (sqrtPoint_mem hu).2⟩

theorem piI_mem : Mem piI Real.pi := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor <;> simp only [piI] <;> push_cast <;> norm_num at h1 h2 ⊢ <;> linarith

/-! ## `arctan` -/

/-- Below `π/2` by the check `b < piI.lo / 2`. -/
theorem lt_pi_div_two_of {b : ℚ} (h : b < piI.lo / 2) : (b : ℝ) < Real.pi / 2 := by
  have hb : (b : ℝ) < (piI.lo : ℝ) / 2 := by exact_mod_cast h
  linarith [piI_mem.1]

theorem neg_pi_div_two_lt_of {a : ℚ} (h : -(piI.lo / 2) < a) : -(Real.pi / 2) < (a : ℝ) := by
  have ha : -((piI.lo : ℝ) / 2) < a := by exact_mod_cast h
  linarith [piI_mem.1]

/-- `tan t` from the intervals of `sin t` and `cos t`, for `cos t` of one sign. -/
theorem tan_mem {t : ℝ} {s c ic : I} (hs : Mem s (Real.sin t)) (hc : Mem c (Real.cos t))
    (hi : inv c = some ic) : Mem (mul s ic) (Real.tan t) := by
  rw [Real.tan_eq_sin_div_cos, div_eq_mul_inv]; exact mul_mem hs (inv_mem hc hi)

theorem atanCheck_mem {q a b : ℚ} {r : I} (h : atanCheck q a b = some r) : Mem r (Real.arctan q) := by
  unfold atanCheck at h
  split at h
  · rename_i hr
    obtain ⟨hlo, hab, hhi⟩ := hr
    have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
    split at h
    · rename_i sa ca sb cb ha hb
      split at h
      · rename_i ia ib hia hib
        split at h
        · rename_i hc
          cases h
          obtain ⟨h1, h2⟩ := hc
          have ta := (tan_mem (sinCosPoint_mem ha).1 (sinCosPoint_mem ha).2 hia).2
          have tb := (tan_mem (sinCosPoint_mem hb).1 (sinCosPoint_mem hb).2 hib).1
          have h1' : ((mul sa ia).hi : ℝ) ≤ q := by exact_mod_cast h1
          have h2' : (q : ℝ) ≤ (mul sb ib).lo := by exact_mod_cast h2
          have a1 := neg_pi_div_two_lt_of hlo
          have b2 := lt_pi_div_two_of hhi
          constructor
          · calc (a : ℝ) = Real.arctan (Real.tan a) := (Real.arctan_tan a1 (by linarith)).symm
              _ ≤ Real.arctan q := Real.arctan_mono (le_trans ta h1')
          · calc Real.arctan q ≤ Real.arctan (Real.tan b) := Real.arctan_mono (le_trans h2' tb)
              _ = b := Real.arctan_tan (by linarith) b2
        · cases h
      · cases h
    · cases h
  · cases h

theorem atanPoint_mem {q : ℚ} {b : I} (h : atanPoint q = some b) : Mem b (Real.arctan q) :=
  atanCheck_mem h

theorem atanI_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : atanI a = some b) : Mem b (Real.arctan x) := by
  unfold atanI at h
  cases hl : atanPoint a.lo with
  | none => simp [hl] at h
  | some l =>
  cases hu : atanPoint a.hi with
  | none => simp [hl, hu] at h
  | some u =>
  simp [hl, hu] at h
  subst h
  exact ⟨le_trans (atanPoint_mem hl).1 (Real.arctan_mono ha.1),
    le_trans (Real.arctan_mono ha.2) (atanPoint_mem hu).2⟩

/-! ## Powers and functions -/

theorem asInt_eq {a : I} {n : ℤ} {v : ℝ} (h : asInt a = some n) (hv : Mem a v) : v = n := by
  unfold asInt at h
  split at h
  · rename_i hc
    cases h
    obtain ⟨heq, hden⟩ := hc
    have hl : (a.lo : ℚ) = (a.lo.num : ℚ) := (Rat.coe_int_num_of_den_eq_one hden).symm
    obtain ⟨h1, h2⟩ := hv
    rw [← heq] at h2
    have : v = (a.lo : ℝ) := le_antisymm h2 h1
    rw [this, hl]; push_cast; rfl
  · cases h

theorem powI_mem {b e c : I} {x v : ℝ} (hb : Mem b x) (he : Mem e v) (h : powI b e = some c) :
    Mem c (x ^ v) := by
  unfold powI at h
  split at h
  · rename_i n hn
    have hv := asInt_eq hn he
    subst hv
    rw [Real.rpow_intCast]
    split at h
    · rename_i h0
      cases h
      have : (n : ℤ) = (n.toNat : ℤ) := (Int.toNat_of_nonneg h0).symm
      rw [this, zpow_natCast]
      exact npow_mem hb _
    · rename_i h0
      have : n = -((n.natAbs : ℕ) : ℤ) := by omega
      rw [this, zpow_neg, zpow_natCast]
      exact inv_mem (npow_mem hb _) h
  · split at h
    · rename_i _ hpos
      have hp : (0 : ℝ) < b.lo := by exact_mod_cast hpos
      have hx : 0 < x := lt_of_lt_of_le hp hb.1
      rw [Real.rpow_def_of_pos hx, mul_comm]
      cases hl : lnI b with
      | none => simp [hl] at h
      | some l =>
      simp [hl] at h
      exact expI_mem (mul_mem he (lnI_mem hb hpos hl)) h
    · cases h

theorem fnI_mem {f : String} {a b : I} {x : ℝ} (ha : Mem a x) (h : fnI f a = some b) :
    Mem b (applyFn f x) := by
  unfold fnI at h
  split at h
  · simpa using sinI_mem ha h
  · simpa using cosI_mem ha h
  · cases hs : sinI a with
    | none => simp [hs] at h
    | some sv =>
    cases hc : cosI a with
    | none => simp [hs, hc] at h
    | some cv =>
    cases hi : inv cv with
    | none => simp [hs, hc, hi] at h
    | some iv =>
    simp [hs, hc, hi] at h
    subst h
    simp only [applyFn, Real.tan_eq_sin_div_cos, div_eq_mul_inv]
    exact mul_mem (sinI_mem ha hs) (inv_mem (cosI_mem ha hc) hi)
  · simpa using expI_mem ha h
  · split at h
    · rename_i hpos; simpa using lnI_mem ha hpos h
    · cases h
  · split at h
    · rename_i hpos
      cases hl : lnI a with
      | none => simp [hl] at h
      | some lv =>
      cases ht : lnI (point 10) with
      | none => simp [hl, ht] at h
      | some tv =>
      cases hi : inv tv with
      | none => simp [hl, ht, hi] at h
      | some iv =>
      simp [hl, ht, hi] at h
      subst h
      simp only [applyFn, Real.logb, div_eq_mul_inv]
      exact mul_mem (lnI_mem ha hpos hl)
        (inv_mem (lnI_mem (point_mem' (by norm_num)) (by decide) ht) hi)
    · cases h
  · simpa using sqrtI_mem ha h
  · simpa using atanI_mem ha h
  · cases h; simpa using abs_mem ha
  · simpa using sign_mem ha h
  · cases h

/-! ## Terms -/

section
variable (ρ : EnvR) (hπ : ρ "π" = Real.pi) (he : ρ "e" = Real.exp 1)
include hπ he

mutual
/-- **The interval holds the value.** Where `ieval` gives an interval, the term's real value is in
it, at any point where the constants `π` and `e` have their values. -/
theorem ieval_sound : ∀ (e : Expr) (a : I), ieval e = some a → Mem a (evalR ρ e)
  | .num q, a, h => by simp only [ieval, Option.some.injEq] at h; subst h; exact point_mem _
  | .var x, a, h => by
    simp only [ieval] at h
    split at h
    · rename_i hx; subst hx; cases h; rw [evalR_var, hπ]; exact piI_mem
    · split at h
      · rename_i _ hx; subst hx; rw [evalR_var, he]
        simpa using expPoint_mem (q := 1) h
      · cases h
  | .add es, a, h => by rw [evalR_add]; exact ievalSum_sound es a h
  | .mul es, a, h => by rw [evalR_mul]; exact ievalProd_sound es a h
  | .pow b e, a, h => by
    simp only [ieval] at h
    cases hb : ieval b with
    | none => simp [hb] at h
    | some bv =>
    cases hev : ieval e with
    | none => simp [hb, hev] at h
    | some ev =>
    simp only [hb, hev, Option.bind_some] at h
    rw [evalR_pow]
    exact powI_mem (ieval_sound b bv hb) (ieval_sound e ev hev) h
  | .fn f [], a, h => by
    simp only [ieval] at h
    split at h
    · rename_i hf; subst hf; cases h; rw [evalR_fn₀, constR_pi]; exact piI_mem
    · cases h
  | .fn f [x], a, h => by
    simp only [ieval] at h
    cases hx : ieval x with
    | none => simp [hx] at h
    | some xv =>
    simp only [hx, Option.bind_some] at h
    rw [evalR_fn₁]
    exact fnI_mem (ieval_sound x xv hx) h
  | .fn _ (_ :: _ :: _), a, h => by simp [ieval] at h
  | .matrix _, a, h => by simp [ieval] at h
theorem ievalSum_sound : ∀ (es : List Expr) (a : I), ievalSum es = some a → Mem a (sumR ρ es)
  | [], a, h => by simp only [ievalSum, Option.some.injEq] at h; subst h; simpa [sumR] using point_mem 0
  | e :: es, a, h => by
    simp only [ievalSum] at h
    cases h1 : ieval e with
    | none => simp [h1] at h
    | some ev =>
    cases h2 : ievalSum es with
    | none => simp [h1, h2] at h
    | some sv =>
    simp [h1, h2] at h
    subst h
    simp only [sumR]
    exact add_mem (ieval_sound e ev h1) (ievalSum_sound es sv h2)
theorem ievalProd_sound : ∀ (es : List Expr) (a : I), ievalProd es = some a → Mem a (prodR ρ es)
  | [], a, h => by simp only [ievalProd, Option.some.injEq] at h; subst h; simpa [prodR] using point_mem 1
  | e :: es, a, h => by
    simp only [ievalProd] at h
    cases h1 : ieval e with
    | none => simp [h1] at h
    | some ev =>
    cases h2 : ievalProd es with
    | none => simp [h1, h2] at h
    | some sv =>
    simp [h1, h2] at h
    subst h
    simp only [prodR]
    exact mul_mem (ieval_sound e ev h1) (ievalProd_sound es sv h2)
end
end

/-! ## Digits -/

theorem tryDigits_sound {a : I} {p : ℕ} {v u : ℚ} (h : tryDigits a p = some (v, u)) :
    v - u ≤ a.lo ∧ a.hi ≤ v + u := by
  unfold tryDigits at h
  dsimp only at h
  split_ifs at h with h0 h1 h2 h3 <;> first
    | (cases h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; assumption)

/-- **The digits are within a unit of their last place.** Every number in the interval is within `u`
of the decimal `v` that `certify` picks. -/
theorem certify_sound {a : I} {v u : ℚ} {x : ℝ} (h : certify a = some (v, u)) (hx : Mem a x) :
    |x - v| ≤ u := by
  obtain ⟨h1, h2⟩ := hx
  unfold certify at h
  dsimp only at h
  split at h
  · rename_i vu hvu
    cases h
    obtain ⟨p, -, hp⟩ := List.mem_filterMap.mp (List.mem_of_mem_head? hvu)
    obtain ⟨c1, c2⟩ := tryDigits_sound hp
    have c1' : (v : ℝ) - u ≤ a.lo := by exact_mod_cast c1
    have c2' : (a.hi : ℝ) ≤ v + u := by exact_mod_cast c2
    rw [abs_le]; constructor <;> linarith
  · split at h
    · rename_i hz
      obtain ⟨hz1, hz2⟩ := hz
      split at h
      · rename_i hr
        cases h
        have : max (-a.lo) a.hi = 0 := hr
        have e1 : -a.lo ≤ 0 := this ▸ le_max_left _ _
        have e2 : a.hi ≤ 0 := this ▸ le_max_right _ _
        have e1' : (0 : ℝ) ≤ a.lo := by exact_mod_cast (neg_nonpos.mp e1)
        have e2' : (a.hi : ℝ) ≤ 0 := by exact_mod_cast e2
        push_cast; rw [abs_le]; constructor <;> linarith
      · split at h
        · rename_i j hj
          cases h
          have hr := List.find?_some hj
          simp only [decide_eq_true_eq] at hr
          have e1 : -a.lo ≤ pow10 j := le_trans (le_max_left _ _) hr
          have e2 : a.hi ≤ pow10 j := le_trans (le_max_right _ _) hr
          have e1' : -(a.lo : ℝ) ≤ pow10 j := by exact_mod_cast e1
          have e2' : (a.hi : ℝ) ≤ pow10 j := by exact_mod_cast e2
          push_cast; rw [abs_le]; constructor <;> linarith
        · cases h
    · cases h

/-- **`cmd.N`: the decimal is within `u` of the exact value.** -/
theorem cmdN_sound (ρ : EnvR) (hπ : ρ "π" = Real.pi) (he : ρ "e" = Real.exp 1) {e : Expr} {v u : ℚ}
    (h : (ieval e).bind certify = some (v, u)) : |evalR ρ e - v| ≤ u := by
  cases ha : ieval e with
  | none => simp [ha] at h
  | some a =>
  simp only [ha, Option.bind_some] at h
  exact certify_sound h (ieval_sound ρ hπ he e a ha)

end MathProofs
