import Proofs.Interval
import Proofs.Cx
/-!
# `N` over ℂ is certified: a rectangle holds the value, part by part

`Ival.cieval` (`Interval.lean` in the engine) evaluates a term over ℚ to a rectangle, an interval for
the real part and one for the imaginary part, and `N` prints each part's certified digits. Here
`cieval_sound` proves the rectangle holds the term's complex value (`evalC`, the principal branch),
and `cmdN_soundC` that each printed part is within its bound of the exact one.

The operations reduce to the real intervals of `Interval.lean` through their formulas on the parts:
`Complex.mul_re`, `Complex.inv_re` (with `normSq`), `Complex.exp_re`, `Complex.sin_eq`,
`Complex.cos_eq` (with `Real.cosh_eq`, `Real.sinh_eq`); a real argument to `ln` and `sqrt`, and a real
base under a real exponent, through `Complex.log_re`, `Complex.arg_ofReal_of_neg`,
`Complex.ofReal_cpow` and `Complex.ofReal_cpow_of_nonpos`.
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Ival


/-- `w` lies in the rectangle. -/
def MemC (z : Ival.C) (w : ℂ) : Prop := Mem z.1 w.re ∧ Mem z.2 w.im

theorem point0_mem : Mem (point 0) 0 := by simpa using point_mem 0

theorem creal_mem {a : I} {x : ℝ} (h : Mem a x) : MemC (creal a) (x : ℂ) := by
  refine ⟨?_, ?_⟩ <;> simp only [creal, Complex.ofReal_re, Complex.ofReal_im]
  · exact h
  · exact point0_mem

theorem cadd_mem {z w : Ival.C} {u v : ℂ} (hz : MemC z u) (hw : MemC w v) : MemC (cadd z w) (u + v) := by
  refine ⟨?_, ?_⟩ <;> simp only [cadd, Complex.add_re, Complex.add_im]
  · exact add_mem hz.1 hw.1
  · exact add_mem hz.2 hw.2

theorem cmul_mem {z w : Ival.C} {u v : ℂ} (hz : MemC z u) (hw : MemC w v) : MemC (cmul z w) (u * v) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, sub_eq_add_neg]
    exact add_mem (mul_mem hz.1 hw.1) (neg_mem (mul_mem hz.2 hw.2))
  · rw [Complex.mul_im]
    exact add_mem (mul_mem hz.1 hw.2) (mul_mem hz.2 hw.1)

theorem cinv_mem {z w : Ival.C} {u : ℂ} (hz : MemC z u) (h : cinv z = some w) : MemC w u⁻¹ := by
  unfold cinv at h
  cases hr : inv (add (mul z.1 z.1) (mul z.2 z.2)) with
  | none => simp [hr] at h
  | some r =>
    simp [hr] at h
    subst h
    have hs : Mem (add (mul z.1 z.1) (mul z.2 z.2)) (Complex.normSq u) := by
      rw [Complex.normSq_apply]; exact add_mem (mul_mem hz.1 hz.1) (mul_mem hz.2 hz.2)
    have hi := inv_mem hs hr
    refine ⟨?_, ?_⟩
    · rw [Complex.inv_re, div_eq_mul_inv]; exact mul_mem hz.1 hi
    · rw [Complex.inv_im, neg_div, div_eq_mul_inv]; exact neg_mem (mul_mem hz.2 hi)

theorem cnpow_mem {z : Ival.C} {u : ℂ} (hz : MemC z u) : ∀ n : ℕ, MemC (cnpow z n) (u ^ n)
  | 0 => by simp only [cnpow]; simpa using creal_mem (point_mem 1)
  | n + 1 => by rw [cnpow, pow_succ]; exact cmul_mem (cnpow_mem hz n) hz

theorem coshI_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : coshI a = some b) : Mem b (Real.cosh x) := by
  unfold coshI at h
  cases hp : expI a with
  | none => simp [hp] at h
  | some p =>
  cases hm : expI (neg a) with
  | none => simp [hp, hm] at h
  | some m =>
  simp [hp, hm] at h
  subst h
  rw [Real.cosh_eq, div_eq_inv_mul]
  exact mul_mem (point_mem' (by norm_num)) (add_mem (expI_mem ha hp) (expI_mem (neg_mem ha) hm))

theorem sinhI_mem {a b : I} {x : ℝ} (ha : Mem a x) (h : sinhI a = some b) : Mem b (Real.sinh x) := by
  unfold sinhI at h
  cases hp : expI a with
  | none => simp [hp] at h
  | some p =>
  cases hm : expI (neg a) with
  | none => simp [hp, hm] at h
  | some m =>
  simp [hp, hm] at h
  subst h
  rw [Real.sinh_eq, div_eq_inv_mul, sub_eq_add_neg]
  exact mul_mem (point_mem' (by norm_num)) (add_mem (expI_mem ha hp) (neg_mem (expI_mem (neg_mem ha) hm)))

theorem cexp_mem {z w : Ival.C} {u : ℂ} (hz : MemC z u) (h : cexp z = some w) : MemC w (Complex.exp u) := by
  unfold cexp at h
  cases he : expI z.1 with
  | none => simp [he] at h
  | some e =>
  cases hc : cosI z.2 with
  | none => simp [he, hc] at h
  | some c =>
  cases hs : sinI z.2 with
  | none => simp [he, hc, hs] at h
  | some s =>
  simp [he, hc, hs] at h
  subst h
  exact ⟨by rw [Complex.exp_re]; exact mul_mem (expI_mem hz.1 he) (cosI_mem hz.2 hc),
    by rw [Complex.exp_im]; exact mul_mem (expI_mem hz.1 he) (sinI_mem hz.2 hs)⟩

theorem csin_re (z : ℂ) : (Complex.sin z).re = Real.sin z.re * Real.cosh z.im := by
  rw [Complex.sin_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
theorem csin_im (z : ℂ) : (Complex.sin z).im = Real.cos z.re * Real.sinh z.im := by
  rw [Complex.sin_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
theorem ccos_re (z : ℂ) : (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
theorem ccos_im (z : ℂ) : (Complex.cos z).im = -(Real.sin z.re * Real.sinh z.im) := by
  rw [Complex.cos_eq]; simp [← Complex.ofReal_sin, ← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]

theorem csin_mem {z w : Ival.C} {u : ℂ} (hz : MemC z u) (h : csin z = some w) : MemC w (Complex.sin u) := by
  unfold csin at h
  cases hs : sinI z.1 with
  | none => simp [hs] at h
  | some s =>
  cases hc : cosI z.1 with
  | none => simp [hs, hc] at h
  | some c =>
  cases hch : coshI z.2 with
  | none => simp [hs, hc, hch] at h
  | some ch =>
  cases hsh : sinhI z.2 with
  | none => simp [hs, hc, hch, hsh] at h
  | some sh =>
  simp [hs, hc, hch, hsh] at h
  subst h
  exact ⟨by rw [csin_re]; exact mul_mem (sinI_mem hz.1 hs) (coshI_mem hz.2 hch),
    by rw [csin_im]; exact mul_mem (cosI_mem hz.1 hc) (sinhI_mem hz.2 hsh)⟩

theorem ccos_mem {z w : Ival.C} {u : ℂ} (hz : MemC z u) (h : ccos z = some w) : MemC w (Complex.cos u) := by
  unfold ccos at h
  cases hs : sinI z.1 with
  | none => simp [hs] at h
  | some s =>
  cases hc : cosI z.1 with
  | none => simp [hs, hc] at h
  | some c =>
  cases hch : coshI z.2 with
  | none => simp [hs, hc, hch] at h
  | some ch =>
  cases hsh : sinhI z.2 with
  | none => simp [hs, hc, hch, hsh] at h
  | some sh =>
  simp [hs, hc, hch, hsh] at h
  subst h
  exact ⟨by rw [ccos_re]; exact mul_mem (cosI_mem hz.1 hc) (coshI_mem hz.2 hch),
    by rw [ccos_im]; exact neg_mem (mul_mem (sinI_mem hz.1 hs) (sinhI_mem hz.2 hsh))⟩

/-- A rectangle whose imaginary interval is exactly `0` holds only real numbers. -/
theorem real_of_isReal {z : Ival.C} {u : ℂ} (hz : MemC z u) (h : isReal z = true) : u = (u.re : ℂ) := by
  simp only [isReal, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := hz.2.1; have h2 := hz.2.2
  rw [h.1] at h1; rw [h.2] at h2
  push_cast at h1 h2
  apply Complex.ext <;> simp; linarith

theorem ctan_mem {z s c ic : Ival.C} {u : ℂ} (hz : MemC z u) (hs : csin z = some s) (hc : ccos z = some c)
    (hi : cinv c = some ic) : MemC (cmul s ic) (Complex.tan u) := by
  rw [Complex.tan_eq_sin_div_cos, div_eq_mul_inv]
  exact cmul_mem (csin_mem hz hs) (cinv_mem (ccos_mem hz hc) hi)

theorem neg_lo_pos {a : I} (h : a.hi < 0) : 0 < (neg a).lo := by
  simp only [neg]; linarith

/-! ## Powers -/

/-- `|x|^y · e^(πiy)`: the principal value of a negative real to a real power. -/
theorem negRealPow_mem {x y : I} {w : Ival.C} {a b : ℝ} (hx : Mem x a) (hy : Mem y b) (ha : a < 0)
    (h : negRealPow x y = some w) : MemC w ((a : ℂ) ^ (b : ℂ)) := by
  unfold negRealPow at h
  cases hm : powI (neg x) y with
  | none => simp [hm] at h
  | some m =>
  cases hc : cosI (mul piI y) with
  | none => simp [hm, hc] at h
  | some c =>
  cases hs : sinI (mul piI y) with
  | none => simp [hm, hc, hs] at h
  | some s =>
  simp [hm, hc, hs] at h
  subst h
  have hθ := mul_mem piI_mem hy
  have hM := powI_mem (neg_mem hx) hy hm
  have key : (a : ℂ) ^ (b : ℂ) = (((-a) ^ b : ℝ) : ℂ) * Complex.exp (((Real.pi * b : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_cpow_of_nonpos ha.le, Complex.ofReal_cpow (by linarith)]
    push_cast; ring_nf
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]; exact mul_mem hM (cosI_mem hθ hc)
  · rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]; exact mul_mem hM (sinI_mem hθ hs)

theorem cpowI_mem {b e w : Ival.C} {u v : ℂ} (hb : MemC b u) (he : MemC e v) (h : cpowI b e = some w) :
    MemC w (u ^ v) := by
  unfold cpowI at h
  split at h
  · rename_i n hn hr
    have hv : v = (n : ℂ) := by
      rw [real_of_isReal he hr, asInt_eq hn he.1]; push_cast; rfl
    rw [hv, Complex.cpow_intCast]
    split at h
    · rename_i h0
      cases h
      have : (n : ℤ) = (n.toNat : ℤ) := (Int.toNat_of_nonneg h0).symm
      rw [this, zpow_natCast]
      exact cnpow_mem hb _
    · rename_i h0
      have : n = -((n.natAbs : ℕ) : ℤ) := by omega
      rw [this, zpow_neg, zpow_natCast]
      exact cinv_mem (cnpow_mem hb _) h
  · split at h
    · rename_i hr
      simp only [Bool.and_eq_true] at hr
      rw [real_of_isReal hb hr.1, real_of_isReal he hr.2]
      split at h
      · rename_i hpos
        have hp : (0 : ℝ) < b.1.lo := by exact_mod_cast hpos
        have hx : 0 < u.re := lt_of_lt_of_le hp hb.1.1
        cases hq : powI b.1 e.1 with
        | none => simp [hq] at h
        | some q =>
        simp [hq] at h
        subst h
        rw [← Complex.ofReal_cpow hx.le]
        exact creal_mem (powI_mem hb.1 he.1 hq)
      · split at h
        · rename_i _ hneg
          have hn : (b.1.hi : ℝ) < 0 := by exact_mod_cast hneg
          exact negRealPow_mem hb.1 he.1 (lt_of_le_of_lt hb.1.2 hn) h
        · cases h
    · cases h

/-! ## Functions -/

theorem cfnI_mem {f : String} {z w : Ival.C} {u : ℂ} (hz : MemC z u) (h : cfnI f z = some w) :
    MemC w (applyFnC f u) := by
  unfold cfnI at h
  split at h
  · simpa using cexp_mem hz h
  · simpa using csin_mem hz h
  · simpa using ccos_mem hz h
  · cases hs : csin z with
    | none => simp [hs] at h
    | some s =>
    cases hc : ccos z with
    | none => simp [hs, hc] at h
    | some c =>
    cases hi : cinv c with
    | none => simp [hs, hc, hi] at h
    | some ic =>
    simp [hs, hc, hi] at h
    subst h
    simpa using ctan_mem hz hs hc hi
  · cases hq : sqrtI (add (mul z.1 z.1) (mul z.2 z.2)) with
    | none => simp [hq] at h
    | some q =>
    simp [hq] at h
    subst h
    have hn : Mem (add (mul z.1 z.1) (mul z.2 z.2)) (Complex.normSq u) := by
      rw [Complex.normSq_apply]; exact add_mem (mul_mem hz.1 hz.1) (mul_mem hz.2 hz.2)
    rw [applyFnC_abs, Complex.norm_def]
    exact creal_mem (sqrtI_mem hn hq)
  · cases h
    rw [applyFnC_conj]
    exact ⟨by rw [Complex.conj_re]; exact hz.1, by rw [Complex.conj_im]; exact neg_mem hz.2⟩
  · cases h; rw [applyFnC_re]; exact creal_mem hz.1
  · cases h; rw [applyFnC_im]; exact creal_mem hz.2
  · -- ln of a real argument
    rw [applyFnC_ln]
    split at h
    · cases h
    · rename_i hr
      have hr : isReal z = true := by simpa using hr
      rw [real_of_isReal hz hr]
      split at h
      · rename_i hpos
        cases hl : lnI z.1 with
        | none => simp [hl] at h
        | some l =>
        simp [hl] at h
        subst h
        have hx : (0 : ℝ) < u.re := lt_of_lt_of_le (by exact_mod_cast hpos) hz.1.1
        rw [← Complex.ofReal_log hx.le]
        exact creal_mem (lnI_mem hz.1 hpos hl)
      · split at h
        · rename_i _ hneg
          cases hl : lnI (neg z.1) with
          | none => simp [hl] at h
          | some l =>
          simp [hl] at h
          subst h
          have hx : u.re < 0 := lt_of_le_of_lt hz.1.2 (by exact_mod_cast hneg)
          refine ⟨?_, ?_⟩
          · rw [Complex.log_re, Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx]
            exact lnI_mem (neg_mem hz.1) (neg_lo_pos hneg) hl
          · rw [Complex.log_im, Complex.arg_ofReal_of_neg hx]; exact piI_mem
        · cases h
  · -- sqrt of a real argument
    simp only [applyFnC]
    split at h
    · cases h
    · rename_i hr
      have hr : isReal z = true := by simpa using hr
      rw [real_of_isReal hz hr]
      split at h
      · rename_i hpos
        cases hq : sqrtI z.1 with
        | none => simp [hq] at h
        | some q =>
        simp [hq] at h
        subst h
        have hx : (0 : ℝ) ≤ u.re := le_trans (by exact_mod_cast hpos) hz.1.1
        have : ((u.re : ℝ) : ℂ) ^ ((1 : ℂ) / 2) = ((Real.sqrt u.re : ℝ) : ℂ) := by
          rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx]; push_cast; rfl
        rw [this]
        exact creal_mem (sqrtI_mem hz.1 hq)
      · split at h
        · rename_i _ hneg
          cases hq : sqrtI (neg z.1) with
          | none => simp [hq] at h
          | some q =>
          simp [hq] at h
          subst h
          have hx : u.re < 0 := lt_of_le_of_lt hz.1.2 (by exact_mod_cast hneg)
          have : ((u.re : ℝ) : ℂ) ^ ((1 : ℂ) / 2) = ((Real.sqrt (-u.re) : ℝ) : ℂ) * Complex.I := by
            rw [Complex.ofReal_cpow_of_nonpos hx.le, Real.sqrt_eq_rpow,
              show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) by push_cast; rfl,
              ← Complex.ofReal_neg, ← Complex.ofReal_cpow (by linarith)]
            congr 1
            rw [show (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℝ)) : ℂ) = (Real.pi / 2 : ℂ) * Complex.I by push_cast; ring]
            exact Complex.exp_pi_div_two_mul_I
          rw [this]
          refine ⟨?_, ?_⟩
          · simpa using point0_mem
          · simpa using sqrtI_mem (neg_mem hz.1) hq
        · cases h
  · cases h

/-! ## Terms -/

theorem i_mem : MemC (point 0, point 1) Complex.I :=
  ⟨by simpa using point0_mem, by simpa using point_mem 1⟩

section
variable (ρ : EnvC) (hπ : ρ "π" = (Real.pi : ℂ)) (he : ρ "e" = Complex.exp 1)
include hπ he

mutual
/-- **The rectangle holds the value.** Where `cieval` gives a rectangle, the term's complex value
(principal branch) is in it, at any point where the constants `π` and `e` have their values. -/
theorem cieval_sound : ∀ (e : Expr) (w : Ival.C), cieval e = some w → MemC w (evalC ρ e)
  | .num q, w, h => by
    simp only [cieval, Option.some.injEq] at h; subst h
    rw [evalC_num, ← Complex.ofReal_ratCast]; exact creal_mem (point_mem _)
  | .var x, w, h => by
    simp only [cieval] at h
    split at h
    · rename_i hx; subst hx; cases h; rw [evalC_var, hπ]; exact creal_mem piI_mem
    · split at h
      · rename_i _ hx; subst hx; rw [evalC_var, he]
        cases hp : expPoint 1 with
        | none => simp [hp] at h
        | some a =>
        simp [hp] at h
        subst h
        rw [← Complex.ofReal_one, ← Complex.ofReal_exp]
        exact creal_mem (by simpa using expPoint_mem (q := 1) hp)
      · cases h
  | .add es, w, h => by rw [evalC_add]; exact cievalSum_sound es w h
  | .mul es, w, h => by rw [evalC_mul]; exact cievalProd_sound es w h
  | .pow b e, w, h => by
    simp only [cieval] at h
    cases hb : cieval b with
    | none => simp [hb] at h
    | some bv =>
    cases hev : cieval e with
    | none => simp [hb, hev] at h
    | some ev =>
    simp only [hb, hev, Option.bind_some] at h
    rw [evalC_pow]
    exact cpowI_mem (cieval_sound b bv hb) (cieval_sound e ev hev) h
  | .fn f [], w, h => by
    simp only [cieval] at h
    split at h
    · rename_i hf; subst hf; cases h; rw [evalC_fn₀, constC_pi]; exact creal_mem piI_mem
    · split at h
      · rename_i _ hf; subst hf; cases h; rw [evalC_fn₀, constC_i]; exact i_mem
      · cases h
  | .fn f [x], w, h => by
    simp only [cieval] at h
    cases hx : cieval x with
    | none => simp [hx] at h
    | some xv =>
    simp only [hx, Option.bind_some] at h
    rw [evalC_fn₁]
    exact cfnI_mem (cieval_sound x xv hx) h
  | .fn _ (_ :: _ :: _), w, h => by simp [cieval] at h
  | .matrix _, w, h => by simp [cieval] at h
theorem cievalSum_sound : ∀ (es : List Expr) (w : Ival.C), cievalSum es = some w → MemC w (sumC ρ es)
  | [], w, h => by
    simp only [cievalSum, Option.some.injEq] at h; subst h; simpa using creal_mem point0_mem
  | e :: es, w, h => by
    simp only [cievalSum] at h
    cases h1 : cieval e with
    | none => simp [h1] at h
    | some ev =>
    cases h2 : cievalSum es with
    | none => simp [h1, h2] at h
    | some sv =>
    simp [h1, h2] at h
    subst h
    rw [sumC_cons]
    exact cadd_mem (cieval_sound e ev h1) (cievalSum_sound es sv h2)
theorem cievalProd_sound : ∀ (es : List Expr) (w : Ival.C), cievalProd es = some w → MemC w (prodC ρ es)
  | [], w, h => by
    simp only [cievalProd, Option.some.injEq] at h; subst h; simpa using creal_mem (point_mem 1)
  | e :: es, w, h => by
    simp only [cievalProd] at h
    cases h1 : cieval e with
    | none => simp [h1] at h
    | some ev =>
    cases h2 : cievalProd es with
    | none => simp [h1, h2] at h
    | some sv =>
    simp [h1, h2] at h
    subst h
    rw [prodC_cons]
    exact cmul_mem (cieval_sound e ev h1) (cievalProd_sound es sv h2)
end
end

/-! ## Digits -/

/-- **`cmd.N` over ℂ: each printed part is within its bound of the exact one.** -/
theorem cmdN_soundC (ρ : EnvC) (hπ : ρ "π" = (Real.pi : ℂ)) (he : ρ "e" = Complex.exp 1) {e : Expr}
    {vr ur vi ui : ℚ} (h : (cieval e).bind ccertify = some ((vr, ur), (vi, ui))) :
    |(evalC ρ e).re - vr| ≤ ur ∧ |(evalC ρ e).im - vi| ≤ ui := by
  cases hw : cieval e with
  | none => simp [hw] at h
  | some w =>
  simp only [hw, Option.bind_some, ccertify] at h
  cases h1 : certify w.1 with
  | none => simp [h1] at h
  | some p =>
  cases h2 : certify w.2 with
  | none => simp [h1, h2] at h
  | some q =>
  simp [h1, h2] at h
  obtain ⟨rfl, rfl⟩ := h
  have hm := cieval_sound ρ hπ he e w hw
  exact ⟨certify_sound h1 hm.1, certify_sound h2 hm.2⟩

end MathProofs
