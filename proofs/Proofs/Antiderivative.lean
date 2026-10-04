import Proofs.DerivRules
import Proofs.Integrate
/-!
# The antiderivative finder, rule by rule (M8)

`cmdIntegrate` accepts the finder's candidate only after differentiating it back to the integrand
(`cmdIntegrate_spec`, `integrate_deriv`). Here the finder's own rules are proved, so the steps it
shows carry a claim of their own. The claim of a result `r` for `∫ f dx` at a point `ρ` is
`AntiAt ρ x r.F f`: read as functions of `x`, `r.F` has derivative `f` at `ρ x` (`HasDerivAt`).

The finder is total (`anti` recurses on a depth bound) and each rule is a function of its
sub-results: `antiStep` takes the recursion as an argument. So each rule has a theorem of one shape
— if the sub-results are antiderivatives of the sub-integrands, so is the result, wherever the
rule's own conditions (`ICond`, read by `HoldsAt`) hold: `antiConst_sound`, `antiVar_sound`,
`antiSum_sound`, `antiConstMul_sound`, `antiPower_sound`, `antiExponential_sound`, `antiFn_sound`
(the table), `antiSecSq_sound`, `substitute_sound` (dividing by a linear coefficient),
`trigPower_sound` (the reduction formulas) and `antiExpPower_sound`. `anti_sound` puts them
together by induction on the depth: a result none of whose steps rests on the check (u-substitution,
integration by parts, the arctangent and arcsine forms, which build on the normalizer's outputs) is
an antiderivative wherever what its steps assume holds, with no check needed.

The conditions are necessary: `not_power_sound` (`∫ x⁻¹ dx = ln x` at `0`), `not_secSq_sound`
(`∫ sec² x dx = tan x` at `π/2`), `not_exponential_sound` (`∫ bˣ dx = bˣ/ln b` at `b = 1`),
`not_substitute_sound` (`∫ cos(kx) dx = sin(kx)/k` at `k = 0`) and `not_trigPower_sound`
(`∫ sin²(kx) dx` at `k = 0`).
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Anti

/-! ## What a result claims -/

/-- `F` is an antiderivative of `f` in `x` at the point `ρ`: read as functions of `x`, `F` has
derivative `f` at `ρ x`. -/
def AntiAt (ρ : EnvR) (x : String) (F f : Expr) : Prop := HasDerivAt (fx ρ x F) (evalD ρ f) (ρ x)

/-- What a finder condition says at the point `ρ`. -/
def HoldsAt (ρ : EnvR) : ICond → Prop
  | .pos u => 0 < evalD ρ u
  | .ne u => evalD ρ u ≠ 0
  | .cosPos u => 0 < Real.cos (evalD ρ u)
  | .cosNe u => Real.cos (evalD ρ u) ≠ 0
  | .inside u => -1 < evalD ρ u ∧ evalD ρ u < 1
  | .base b => 0 < evalD ρ b ∧ evalD ρ b ≠ 1
  | .notNegOne n => evalD ρ n ≠ -1

/-- A finder result for `∫ f dx` is sound at `ρ`: unless it rests on the check, it is an
antiderivative there wherever its conditions hold. -/
def Good (ρ : EnvR) (x : String) (f : Expr) (r : Found) : Prop :=
  r.checked = false → (∀ c ∈ r.conds, HoldsAt ρ c) → AntiAt ρ x r.F f

/-- The recursion a rule is given is sound at `ρ`. -/
def RecGood (ρ : EnvR) (x : String) (rec : Nat → Expr → Option Found) : Prop :=
  ∀ fuel g r, rec fuel g = some r → Good ρ x g r

/-! ## Plumbing -/

@[simp] theorem applyFn_tan' (y : ℝ) : applyFn "tan" y = Real.tan y := by simp [applyFn]

theorem evalD_eneg (ρ : EnvR) (a : Expr) : evalD ρ (Expr.neg a) = -evalD ρ a := by
  simp [Expr.neg]

theorem evalD_esub (ρ : EnvR) (a b : Expr) : evalD ρ (Expr.sub a b) = evalD ρ a - evalD ρ b := by
  simp [Expr.sub, Expr.neg]; ring

theorem evalD_ediv (ρ : EnvR) (a b : Expr) : evalD ρ (Expr.div a b) = evalD ρ a / evalD ρ b := by
  simp [Expr.div, Real.rpow_neg_one, div_eq_mul_inv]

theorem evalD_mulN' (ρ : EnvR) (es : List Expr) : evalD ρ (Expr.mulN es) = prodD ρ es := by
  match es with
  | [e] => simp [Expr.mulN]
  | [] => rfl
  | _ :: _ :: _ => rfl

theorem evalD_ofNat (ρ : EnvR) (n : ℕ) : evalD ρ (Expr.ofInt n) = (n : ℝ) := by
  rw [Expr.ofInt, evalD_intLit]; norm_cast

theorem evalD_powTwo (ρ : EnvR) (e : Expr) : evalD ρ (.pow e (Expr.ofInt 2)) = evalD ρ e ^ 2 := by
  rw [evalD_pow, Expr.ofInt, evalD_intLit]; norm_num

@[simp] theorem evalD_ofInt' (ρ : EnvR) (z : ℤ) : evalD ρ (Expr.ofInt z) = (z : ℝ) := by
  rw [Expr.ofInt, evalD_intLit]

@[simp] theorem Q_ofRat_val (r : ℚ) (b : Bool) : (Q.ofRat r b).val = r := rfl

@[simp] theorem mkRat_half : ((mkRat 1 2 : ℚ) : ℝ) = 2⁻¹ := by
  rw [Rat.mkRat_eq_div]; push_cast; ring

@[simp] theorem evalD_two (ρ : EnvR) : evalD ρ (Expr.ofInt 2) = 2 := by
  rw [Expr.ofInt, evalD_intLit]; norm_num

@[simp] theorem half_val : (((Q.ofRat (mkRat 1 2)).val : ℚ) : ℝ) = 2⁻¹ := by
  simp only [Q.ofRat]; rw [Rat.mkRat_eq_div]; push_cast; ring

theorem evalD_ratLit (ρ : EnvR) (r : ℚ) : evalD ρ (.num (Q.ofRat r)) = (r : ℝ) := rfl

theorem evalD_half (ρ : EnvR) : evalD ρ (.num (Q.ofRat (mkRat 1 2))) = 1 / 2 := by
  rw [evalD_ratLit, Rat.mkRat_eq_div]; push_cast; ring

theorem evalD_isOne {a : Expr} (h : a.isOne = true) (ρ : EnvR) : evalD ρ a = 1 := by
  cases a with
  | num q =>
    simp only [Expr.isOne, Q.isOne, beq_iff_eq] at h
    simp [h]
  | _ => simp [Expr.isOne] at h

theorem not_dep_iff {e : Expr} {x : String} : ¬ e.dependsOn x = true ↔ x ∉ e.freeVars := by
  simp [Expr.dependsOn]

theorem not_dep_mul {x : String} {cs : List Expr} (h : ∀ c ∈ cs, ¬ c.dependsOn x = true) :
    ¬ (Expr.mul cs).dependsOn x = true := by
  rw [not_dep_iff]; simp only [Expr.freeVars]; exact not_mem_freeVarsList h

theorem not_dep_mulN {x : String} {cs : List Expr} (h : ∀ c ∈ cs, ¬ c.dependsOn x = true) :
    ¬ (Expr.mulN cs).dependsOn x = true := by
  match cs, h with
  | [c], h => simpa [Expr.mulN] using h c (by simp)
  | [], h => exact not_dep_mul h
  | _ :: _ :: _, h => exact not_dep_mul h

theorem not_dep_num {x : String} (q : Q) : ¬ (Expr.num q).dependsOn x = true := by
  simp [Expr.dependsOn, Expr.freeVars]

/-- A term free of `x` has the same value wherever `x` is rebound. -/
theorem evalD_upd_const {ρ : EnvR} {x : String} {e : Expr} (h : ¬ e.dependsOn x = true) (t : ℝ) :
    evalD (upd ρ x t) e = evalD ρ e :=
  evalD_upd_not_free ρ x t (by simpa [Expr.dependsOn] using h)

theorem prodD_filter (ρ : EnvR) (p : Expr → Bool) : ∀ es : List Expr,
    prodD ρ es = prodD ρ (es.filter p) * prodD ρ (es.filter (fun a => !p a))
  | [] => by simp
  | e :: es => by
    rw [prodD_cons, prodD_filter ρ p es]
    cases hp : p e <;> simp [List.filter_cons, hp] <;> ring

theorem sumD_filter (ρ : EnvR) (p : Expr → Bool) : ∀ es : List Expr,
    sumD ρ es = sumD ρ (es.filter p) + sumD ρ (es.filter (fun a => !p a))
  | [] => by simp
  | e :: es => by
    rw [sumD_cons, sumD_filter ρ p es]
    cases hp : p e <;> simp [List.filter_cons, hp] <;> ring

theorem partition_spec {p : Expr → Bool} {es l r : List Expr} (h : es.partition p = (l, r)) :
    es.filter p = l ∧ es.filter (fun a => !p a) = r := by
  rw [List.partition_eq_filter_filter] at h
  simp only [Prod.mk.injEq] at h
  exact ⟨h.1, by simpa [Function.comp_def] using h.2⟩

theorem filter_not_dep {x : String} {es cs : List Expr}
    (h : es.filter (fun a => !a.dependsOn x) = cs) : ∀ c ∈ cs, ¬ c.dependsOn x = true := by
  intro c hc; rw [← h, List.mem_filter] at hc; simpa using hc.2

theorem mem_append_left' {c : ICond} {l₁ l₂ : List ICond} (h : c ∈ l₁) : c ∈ l₁ ++ l₂ :=
  List.mem_append.2 (Or.inl h)

theorem mem_append_right' {c : ICond} {l₁ l₂ : List ICond} (h : c ∈ l₂) : c ∈ l₁ ++ l₂ :=
  List.mem_append.2 (Or.inr h)

/-! ## The linear coefficient -/

/-- `coeffOfTerm` finds the derivative of `c·x`, a constant. -/
theorem coeffOfTerm_spec {x : String} {t a : Expr} (h : coeffOfTerm x t = some a) :
    ¬ a.dependsOn x = true ∧ ∀ ρ : EnvR, HasDerivAt (fx ρ x t) (evalD ρ a) (ρ x) := by
  unfold coeffOfTerm at h
  split at h
  · rename_i y
    split at h
    · rename_i hy
      cases h
      have hyx : y = x := by simpa using hy
      subst hyx
      refine ⟨not_dep_num _, fun ρ => ?_⟩
      have : fx ρ y (.var y) = id := by funext s; simp
      rw [this, evalD_one]; exact hasDerivAt_id _
    · cases h
  · rename_i es
    split at h
    · rename_i y cs hp
      split at h
      · rename_i hy
        cases h
        have hyx : y = x := by simpa using hy
        subst hyx
        obtain ⟨h1, h2⟩ := partition_spec hp
        have hcs := filter_not_dep h2
        refine ⟨not_dep_mulN hcs, fun ρ => ?_⟩
        have hf : fx ρ y (.mul es) = fun s => s * prodD ρ cs := by
          funext s
          show prodD (upd ρ y s) es = _
          rw [prodD_filter _ (fun a => a.dependsOn y) es, h1, h2,
            prodD_upd_not_free ρ y s (not_mem_freeVarsList hcs)]
          simp
        rw [hf, evalD_mulN']
        simpa using (hasDerivAt_id (ρ y)).mul_const (prodD ρ cs)
      · cases h
    · cases h
  · cases h

/-- **`linearCoeff` finds the slope of `u = a·x + b`**: `a` is free of `x` and is `u`'s derivative,
at every point. -/
theorem linearCoeff_spec {x : String} {u a : Expr} (h : linearCoeff x u = some a) :
    ¬ a.dependsOn x = true ∧ ∀ ρ : EnvR, HasDerivAt (fx ρ x u) (evalD ρ a) (ρ x) := by
  unfold linearCoeff at h
  split at h
  · rename_i es
    split at h
    · rename_i t others hp
      obtain ⟨ha, hd⟩ := coeffOfTerm_spec h
      obtain ⟨h1, h2⟩ := partition_spec hp
      have hcs := filter_not_dep h2
      refine ⟨ha, fun ρ => ?_⟩
      have hf : fx ρ x (.add es) = fun s => fx ρ x t s + sumD ρ others := by
        funext s
        show sumD (upd ρ x s) es = _
        rw [sumD_filter _ (fun a => a.dependsOn x) es, h1, h2,
          sumD_upd_not_free ρ x s (not_mem_freeVarsList hcs)]
        simp
      rw [hf]
      exact (hd ρ).add_const _
    · cases h
  · exact coeffOfTerm_spec h

/-! ## `int.linear-substitution` -/

/-- **`int.linear-substitution`**: if `G(u)` has derivative `g·a` (the chain rule through
`u = a·x + b`), then `G(u)/a` has derivative `g`, wherever `a ≠ 0` — which the step states unless
`a` is a nonzero numeral. -/
theorem substitute_sound {ρ : EnvR} {x : String} {f G a : Expr} {g : ℝ}
    (ha : ¬ a.dependsOn x = true) (hG : HasDerivAt (fx ρ x G) (g * evalD ρ a) (ρ x))
    (hc : ∀ c ∈ (Anti.substitute x f G a).2.2, HoldsAt ρ c) :
    HasDerivAt (fx ρ x (Anti.substitute x f G a).1) g (ρ x) := by
  by_cases h1 : a.isOne = true
  · simp only [Anti.substitute, h1, ite_true]
    simpa [evalD_isOne h1] using hG
  · simp only [Anti.substitute, h1, ite_false, Bool.false_eq_true] at hc ⊢
    have hA : evalD ρ a ≠ 0 := by
      unfold neCond at hc
      split at hc
      · rename_i q
        split at hc
        · exact hc (.ne _) (by simp)
        · rename_i hq
          simp only [Q.isZero, beq_iff_eq] at hq
          simpa using hq
      · exact hc (.ne _) (by simp)
    have hf : fx ρ x (Expr.div G a) = fun t => fx ρ x G t * (evalD ρ a)⁻¹ := by
      funext t; simp [evalD_ediv, evalD_upd_const ha t, div_eq_mul_inv]
    rw [hf]
    convert hG.mul_const (evalD ρ a)⁻¹ using 1
    field_simp

/-! ## The table -/

/-- **`int.table`**: each entry `G` has derivative `g(u)·u'` (the chain rule), where its condition
holds: `u > 0` for `ln`, `cos u > 0` for `tan`, `−1 < u < 1` for `arcsin` and `arccos`, nothing for
`sin`, `cos`, `exp`, `arctan`. -/
theorem table_sound {ρ : EnvR} {x g : String} {u G : Expr} {why : String} {cs : List ICond} {a' : ℝ}
    (h : table g u = some (G, why, cs)) (hu : HasDerivAt (fx ρ x u) a' (ρ x))
    (hc : ∀ c ∈ cs, HoldsAt ρ c) :
    HasDerivAt (fx ρ x G) (applyFn g (evalD ρ u) * a') (ρ x) := by
  unfold table at h
  split at h
  · -- sin
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    have hf : fx ρ x (Expr.neg (.fn "cos" [u])) = fun t => -Real.cos (fx ρ x u t) := by
      funext t; simp [evalD_eneg]
    rw [hf]
    convert hu.cos.neg using 1
    simp only [applyFn_sin, fx, upd_self]; ring
  · -- cos
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    have hf : fx ρ x (.fn "sin" [u]) = fun t => Real.sin (fx ρ x u t) := by funext t; simp
    rw [hf]
    convert hu.sin using 1
    simp only [applyFn_cos, fx, upd_self]
  · -- exp
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    have hf : fx ρ x (.fn "exp" [u]) = fun t => Real.exp (fx ρ x u t) := by funext t; simp
    rw [hf]
    convert hu.exp using 1
    simp only [applyFn_exp, fx, upd_self]
  · -- ln
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    have hpos : 0 < evalD ρ u := hc (.pos u) (by simp)
    have hf : fx ρ x (Expr.sub (.mul [u, .fn "ln" [u]]) u)
        = fun t => fx ρ x u t * Real.log (fx ρ x u t) - fx ρ x u t := by
      funext t; simp [evalD_esub]
    rw [hf]
    have hne : fx ρ x u (ρ x) ≠ 0 := by simpa [fx] using hpos.ne'
    convert (hu.mul (hu.log hne)).sub hu using 1
    simp only [applyFn_ln, fx, upd_self]
    field_simp
    ring
  · -- tan
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    have hcos : 0 < Real.cos (evalD ρ u) := hc (.cosPos u) (by simp)
    have hf : fx ρ x (Expr.neg (.fn "ln" [.fn "cos" [u]]))
        = fun t => -Real.log (Real.cos (fx ρ x u t)) := by
      funext t; simp [evalD_eneg]
    rw [hf]
    have hne : Real.cos (fx ρ x u (ρ x)) ≠ 0 := by simpa [fx] using hcos.ne'
    convert (hu.cos.log hne).neg using 1
    simp only [applyFn_tan', fx, upd_self, Real.tan_eq_sin_div_cos]
    ring
  · -- arctan
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    have hf : fx ρ x (Expr.sub (.mul [u, .fn "arctan" [u]])
          (.mul [.num (Q.ofRat (mkRat 1 2)), .fn "ln" [.add [Expr.one, .pow u (Expr.ofInt 2)]]]))
        = fun t => fx ρ x u t * Real.arctan (fx ρ x u t) - 1 / 2 * Real.log (1 + fx ρ x u t ^ 2) := by
      funext t; simp [evalD_esub, Real.rpow_two]
    rw [hf]
    have hne : 1 + fx ρ x u (ρ x) ^ 2 ≠ 0 := by positivity
    convert (hu.mul hu.arctan).sub ((((hu.pow 2).const_add 1).log hne).const_mul (1 / 2)) using 1
    simp only [applyFn_arctan, Pi.pow_apply, fx, upd_self]
    field_simp
    ring
  · -- arcsin
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    obtain ⟨h₁, h₂⟩ : -1 < evalD ρ u ∧ evalD ρ u < 1 := hc (.inside u) (by simp)
    have hf : fx ρ x (.add [.mul [u, .fn "arcsin" [u]],
          .pow (Expr.sub Expr.one (.pow u (Expr.ofInt 2))) (.num (Q.ofRat (mkRat 1 2)))])
        = fun t => fx ρ x u t * Real.arcsin (fx ρ x u t) + (1 - fx ρ x u t ^ 2) ^ (1 / 2 : ℝ) := by
      funext t; simp [evalD_esub, Real.rpow_two]
    rw [hf]
    have hU : fx ρ x u (ρ x) = evalD ρ u := fx_at ρ x u
    have harc : HasDerivAt (fun t => Real.arcsin (fx ρ x u t))
        (1 / Real.sqrt (1 - fx ρ x u (ρ x) ^ 2) * a') (ρ x) :=
      (Real.hasDerivAt_arcsin (by rw [hU]; exact h₁.ne') (by rw [hU]; exact h₂.ne)).comp (ρ x) hu
    have hne : 1 - fx ρ x u (ρ x) ^ 2 ≠ 0 := by
      rw [hU]; nlinarith
    have hsq := ((hu.pow 2).const_sub 1).rpow_const (p := 1 / 2) (Or.inl hne)
    convert (hu.mul harc).add hsq using 1
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num, rpow_neg_half_eq]
    simp only [applyFn_arcsin, Pi.pow_apply, fx, upd_self]
    ring
  · -- arccos
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    obtain ⟨h₁, h₂⟩ : -1 < evalD ρ u ∧ evalD ρ u < 1 := hc (.inside u) (by simp)
    have hf : fx ρ x (Expr.sub (.mul [u, .fn "arccos" [u]])
          (.pow (Expr.sub Expr.one (.pow u (Expr.ofInt 2))) (.num (Q.ofRat (mkRat 1 2)))))
        = fun t => fx ρ x u t * Real.arccos (fx ρ x u t) - (1 - fx ρ x u t ^ 2) ^ (1 / 2 : ℝ) := by
      funext t; simp [evalD_esub, Real.rpow_two]
    rw [hf]
    have hU : fx ρ x u (ρ x) = evalD ρ u := fx_at ρ x u
    have harc : HasDerivAt (fun t => Real.arccos (fx ρ x u t))
        (-(1 / Real.sqrt (1 - fx ρ x u (ρ x) ^ 2)) * a') (ρ x) :=
      (Real.hasDerivAt_arccos (by rw [hU]; exact h₁.ne') (by rw [hU]; exact h₂.ne)).comp (ρ x) hu
    have hne : 1 - fx ρ x u (ρ x) ^ 2 ≠ 0 := by
      rw [hU]; nlinarith
    have hsq := ((hu.pow 2).const_sub 1).rpow_const (p := 1 / 2) (Or.inl hne)
    convert (hu.mul harc).sub hsq using 1
    rw [show (1 / 2 : ℝ) - 1 = -1 / 2 by norm_num, rpow_neg_half_eq]
    simp only [applyFn_arccos, Pi.pow_apply, fx, upd_self]
    ring
  · cases h

/-! ## The power rule and the exponential -/

theorem evalD_of_isNumEq {n : Expr} {q : Q} (h : n.isNumEq q = true) (ρ : EnvR) :
    evalD ρ n = (q.val : ℝ) := by
  cases n with
  | num v =>
    simp only [Expr.isNumEq, Q.eq, beq_iff_eq] at h
    simp [h]
  | _ => simp [Expr.isNumEq] at h

/-- **`int.power`**: `∫ uⁿ du = uⁿ⁺¹/(n+1)` (`ln u` at `n = −1`), the chain rule through `u`, where
what it states holds: nothing for a natural numeral `n`, `u ≠ 0` for another integer, `u > 0`
otherwise, and `n ≠ −1` for a symbolic `n`. -/
theorem powerRule_sound {ρ : EnvR} {x : String} {u n G : Expr} {why : String} {cs : List ICond} {a' : ℝ}
    (h : powerRule u n = (G, why, cs)) (hn : ¬ n.dependsOn x = true)
    (hu : HasDerivAt (fx ρ x u) a' (ρ x)) (hc : ∀ c ∈ cs, HoldsAt ρ c) :
    HasDerivAt (fx ρ x G) (evalD ρ (.pow u n) * a') (ρ x) := by
  have hU : fx ρ x u (ρ x) = evalD ρ u := fx_at ρ x u
  unfold powerRule at h
  split at h
  · rename_i hm
    simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
    have hpos : 0 < evalD ρ u := hc (.pos u) (by simp)
    have hn1 : evalD ρ n = -1 := by
      rw [evalD_of_isNumEq hm]; simp [Q.minusOne, Q.ofInt]
    have hne : fx ρ x u (ρ x) ≠ 0 := by rw [hU]; exact hpos.ne'
    have hf : fx ρ x (.fn "ln" [u]) = fun t => Real.log (fx ρ x u t) := by funext t; simp
    rw [hf]
    convert hu.log hne using 1
    rw [evalD_pow, hn1, Real.rpow_neg_one, hU]
    ring
  · rename_i hm
    split at h
    · rename_i q
      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
      have hq : (q.val : ℝ) ≠ -1 := by
        intro hq
        apply hm
        simp only [Expr.isNumEq, Q.eq, Q.minusOne, Q.ofInt, beq_iff_eq]
        exact_mod_cast hq
      have hp : ((q.val : ℝ) + 1) ≠ 0 := by intro h0; apply hq; linarith
      have hcond : (q.val : ℝ) + 1 = 0 ∨ fx ρ x u (ρ x) ≠ 0 ∨ 1 ≤ (q.val : ℝ) + 1 := by
        right
        by_cases hnat : (q.isInt && !q.isNeg) = true
        · right
          simp only [Bool.and_eq_true, Bool.not_eq_true', Q.isNeg, decide_eq_false_iff_not, not_lt] at hnat
          have : (0 : ℚ) ≤ q.val := Rat.num_nonneg.mp hnat.2
          have : (0 : ℝ) ≤ (q.val : ℝ) := by exact_mod_cast this
          linarith
        · left
          rw [hU]
          simp only [hnat, Bool.false_eq_true, if_false] at hc
          split at hc
          · exact hc (.ne u) (by simp)
          · exact (hc (.pos u) (by simp)).ne'
      have hf : fx ρ x (.mul [.num (Q.one.div (q.add Q.one)), .pow u (.num (q.add Q.one))])
          = fun t => ((q.val : ℝ) + 1)⁻¹ * fx ρ x u t ^ ((q.val : ℝ) + 1) := by
        funext t
        simp [Q.div, Q.add, Q.one, Q.ofInt]
      rw [hf]
      convert (hasDerivAt_rpow_const' hu hcond).const_mul ((q.val : ℝ) + 1)⁻¹ using 1
      rw [evalD_pow, hU, show (q.val : ℝ) + 1 - 1 = q.val by ring]
      simp only [evalD_num]
      field_simp
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, -, rfl⟩ := h
      have hpos : 0 < evalD ρ u := hc (.pos u) (by simp)
      have hN : evalD ρ n ≠ -1 := hc (.notNegOne n) (by simp)
      set N := evalD ρ n with hNdef
      have hp : N + 1 ≠ 0 := by intro h0; apply hN; linarith
      have hcond : N + 1 = 0 ∨ fx ρ x u (ρ x) ≠ 0 ∨ 1 ≤ N + 1 := Or.inr (Or.inl (by rw [hU]; exact hpos.ne'))
      have hf : fx ρ x (.mul [.pow (.add [n, Expr.one]) Expr.minusOne, .pow u (.add [n, Expr.one])])
          = fun t => (N + 1)⁻¹ * fx ρ x u t ^ (N + 1) := by
        funext t
        simp [evalD_upd_const hn t, Real.rpow_neg_one, hNdef]
      rw [hf]
      convert (hasDerivAt_rpow_const' hu hcond).const_mul (N + 1)⁻¹ using 1
      rw [evalD_pow, hU, ← hNdef, show N + 1 - 1 = N by ring]
      field_simp

/-- **`int.exponential`**: `bᵘ/ln b` has derivative `bᵘ·u'`, for `b` free of `x`, where `b > 0` and
`b ≠ 1` — which the step states unless `b` is a numeral or `π`. -/
theorem exponential_sound {ρ : EnvR} {x : String} {b e : Expr} {a' : ℝ}
    (hb : ¬ b.dependsOn x = true) (he : HasDerivAt (fx ρ x e) a' (ρ x))
    (hc : ∀ c ∈ baseConds b, HoldsAt ρ c) :
    HasDerivAt (fx ρ x (Expr.div (.pow b e) (.fn "ln" [b]))) (evalD ρ (.pow b e) * a') (ρ x) := by
  have hB : 0 < evalD ρ b ∧ evalD ρ b ≠ 1 := by
    unfold baseConds at hc
    split at hc
    · rename_i q
      split at hc
      · exact hc (.base _) (by simp)
      · rename_i hq
        simp only [Bool.or_eq_true, Q.isNeg, Q.isZero, Q.isOne, decide_eq_true_eq, beq_iff_eq,
          not_or, not_lt] at hq
        obtain ⟨⟨h0, hz⟩, h1⟩ := hq
        have hq0 : (0 : ℚ) < q.val := lt_of_le_of_ne (Rat.num_nonneg.mp h0) (Ne.symm hz)
        refine ⟨by simpa using (show (0 : ℝ) < (q.val : ℝ) by exact_mod_cast hq0), ?_⟩
        simp only [evalD_num]
        exact_mod_cast h1
    · refine ⟨by simpa using Real.pi_pos, ?_⟩
      simp only [evalD_fn, fnD_nil, constR_pi]
      exact ne_of_gt (by linarith [Real.two_le_pi])
    · exact hc (.base _) (by simp)
  have hlog : Real.log (evalD ρ b) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hB.1 hB.2
  have hf : fx ρ x (Expr.div (.pow b e) (.fn "ln" [b]))
      = fun t => evalD ρ b ^ (fx ρ x e t) / Real.log (evalD ρ b) := by
    funext t; simp [evalD_ediv, evalD_upd_const hb t]
  rw [hf]
  convert (he.const_rpow hB.1).div_const (Real.log (evalD ρ b)) using 1
  simp only [evalD_pow, fx, upd_self]
  field_simp

/-! ## Powers of sine and cosine -/

theorem evalD_pw (ρ : EnvR) (b : Expr) (k : ℕ) : evalD ρ (pw b k) = evalD ρ b ^ k := by
  unfold pw
  split
  · subst_vars; simp
  · split
    · subst_vars; simp
    · rw [evalD_pow, evalD_ofNat]; exact Real.rpow_natCast _ _

theorem prodD_ones (ρ : EnvR) : ∀ {l : List Expr}, (∀ c ∈ l, c.isOne = true) → prodD ρ l = 1
  | [], _ => rfl
  | c :: l, h => by
    rw [prodD_cons, evalD_isOne (h c (by simp)), prodD_ones ρ (fun c' hc => h c' (by simp [hc])), one_mul]

theorem evalD_prodOf (ρ : EnvR) (fs : List Expr) : evalD ρ (prodOf fs) = prodD ρ fs := by
  have hsplit := prodD_filter ρ (fun c => !c.isOne) fs
  have hones : prodD ρ (fs.filter (fun a => !!a.isOne)) = 1 :=
    prodD_ones ρ (fun c hc => by simpa using (List.mem_filter.mp hc).2)
  rw [hones, mul_one] at hsplit
  rw [hsplit]
  unfold prodOf
  split
  · rename_i hnil; rw [hnil]; simp
  · exact evalD_mulN' ρ _

theorem evalD_powerOf (ρ : EnvR) (f : Expr) :
    (powerOf f).2 = 0 ∨ evalD ρ f = evalD ρ (powerOf f).1 ^ (powerOf f).2 := by
  unfold powerOf
  split
  · rename_i b q
    split
    · rename_i hq
      right
      simp only [Bool.and_eq_true, decide_eq_true_eq, Q.isInt, beq_iff_eq] at hq
      obtain ⟨hden, hge⟩ := hq
      rw [evalD_pow, evalD_num]
      have hcast : ((q.val : ℚ) : ℝ) = ((q.val.num.toNat : ℕ) : ℝ) := by
        rw [Rat.cast_def, hden]; push_cast; rw [div_one]
        exact_mod_cast (Int.toNat_of_nonneg (by omega)).symm
      rw [hcast]; exact Real.rpow_natCast _ _
    · left; rfl
  · right; simp

/-- **`trigPowers`** reads a product of powers of `sin u` and `cos u` as `sinᵐu · cosⁿu`. -/
theorem trigPowers_go (ρ : EnvR) : ∀ (fs : List Expr) (u? : Option Expr) (m n : ℕ) {u : Expr} {M N : ℕ},
    trigPowers.go u? m n fs = some (u, M, N) →
    (∀ v, u? = some v → v = u) ∧
    Real.sin (evalD ρ u) ^ m * Real.cos (evalD ρ u) ^ n * prodD ρ fs
      = Real.sin (evalD ρ u) ^ M * Real.cos (evalD ρ u) ^ N
  | [], u?, m, n, u, M, N, h => by
    simp only [trigPowers.go, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨v, hv, rfl, rfl, rfl⟩ := h
    refine ⟨fun w hw => by rw [hv] at hw; cases hw; rfl, by simp⟩
  | f :: fs, u?, m, n, u, M, N, h => by
    simp only [trigPowers.go] at h
    have hpf := evalD_powerOf ρ f
    rcases hpk : powerOf f with ⟨base, k⟩
    rw [hpk] at hpf
    simp only [hpk] at h hpf
    split at h
    · cases h
    · rename_i hk
      have hf : evalD ρ f = evalD ρ base ^ k := hpf.resolve_left hk
      split at h
      · rename_i v
        have hstep : ∀ {M' N' : ℕ}, trigPowers.go (some v) (m + k) n fs = some (u, M', N') →
            M' = M → N' = N → Real.sin (evalD ρ u) ^ m * Real.cos (evalD ρ u) ^ n * prodD ρ (f :: fs)
              = Real.sin (evalD ρ u) ^ M * Real.cos (evalD ρ u) ^ N ∧ v = u := by
          intro M' N' h' hM hN
          subst hM hN
          obtain ⟨hu, ih⟩ := trigPowers_go ρ fs (some v) (m + k) n h'
          have hvu : v = u := hu v rfl
          subst hvu
          refine ⟨?_, rfl⟩
          rw [prodD_cons, hf, ← ih]; simp only [evalD_fn, fnD_one, applyFn_sin]; ring
        split at h
        · rename_i w
          split at h
          · rename_i hsame
            obtain ⟨heq, hvu⟩ := hstep h rfl rfl
            subst hvu
            exact ⟨fun w' hw => by cases hw; exact Expr.beq_eq _ _ hsame, heq⟩
          · cases h
        · obtain ⟨heq, hvu⟩ := hstep (by simpa using h) rfl rfl
          exact ⟨(fun w' hw => by cases hw), heq⟩
      · rename_i v
        have hstep : ∀ {M' N' : ℕ}, trigPowers.go (some v) m (n + k) fs = some (u, M', N') →
            M' = M → N' = N → Real.sin (evalD ρ u) ^ m * Real.cos (evalD ρ u) ^ n * prodD ρ (f :: fs)
              = Real.sin (evalD ρ u) ^ M * Real.cos (evalD ρ u) ^ N ∧ v = u := by
          intro M' N' h' hM hN
          subst hM hN
          obtain ⟨hu, ih⟩ := trigPowers_go ρ fs (some v) m (n + k) h'
          have hvu : v = u := hu v rfl
          subst hvu
          refine ⟨?_, rfl⟩
          rw [prodD_cons, hf, ← ih]; simp only [evalD_fn, fnD_one, applyFn_cos]; ring
        split at h
        · rename_i w
          split at h
          · rename_i hsame
            obtain ⟨heq, hvu⟩ := hstep h rfl rfl
            subst hvu
            exact ⟨fun w' hw => by cases hw; exact Expr.beq_eq _ _ hsame, heq⟩
          · cases h
        · obtain ⟨heq, hvu⟩ := hstep (by simpa using h) rfl rfl
          exact ⟨(fun w' hw => by cases hw), heq⟩
      · cases h

theorem trigPowers_spec {es : List Expr} {u : Expr} {m n : ℕ} (h : trigPowers es = some (u, m, n)) (ρ : EnvR) :
    prodD ρ es = Real.sin (evalD ρ u) ^ m * Real.cos (evalD ρ u) ^ n := by
  have := (trigPowers_go ρ es none 0 0 h).2
  simpa using this

/-- The sine reduction formula, differentiated: `−sʲ⁺¹cⁿ⁺¹/(a(j+n+2)) + (j+1)/(j+n+2) ∫ sʲcⁿ` has
derivative `sʲ⁺²cⁿ`, where `u' = a ≠ 0`. -/
theorem hasDerivAt_sineReduce {U R : ℝ → ℝ} {a t : ℝ} (j n : ℕ) (hU : HasDerivAt U a t) (ha : a ≠ 0)
    (hR : HasDerivAt R (Real.sin (U t) ^ j * Real.cos (U t) ^ n) t) :
    HasDerivAt (fun s => -(Real.sin (U s) ^ (j + 1) * Real.cos (U s) ^ (n + 1)) / (a * ((j : ℝ) + 2 + n))
        + ((j : ℝ) + 1) / ((j : ℝ) + 2 + n) * R s)
      (Real.sin (U t) ^ (j + 2) * Real.cos (U t) ^ n) t := by
  have hT : (j : ℝ) + 2 + n ≠ 0 := by positivity
  have h1 := ((hU.sin.pow (j + 1)).mul (hU.cos.pow (n + 1))).neg.div_const (a * ((j : ℝ) + 2 + n))
  convert h1.add (hR.const_mul (((j : ℝ) + 1) / ((j : ℝ) + 2 + n))) using 1
  have hs := Real.sin_sq_add_cos_sq (U t)
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  field_simp
  push_cast
  linear_combination ((j : ℝ) + 1) * Real.sin (U t) ^ j * Real.cos (U t) ^ n * hs

/-- The cosine reduction formula, differentiated. -/
theorem hasDerivAt_cosineReduce {U R : ℝ → ℝ} {a t : ℝ} (m k : ℕ) (hU : HasDerivAt U a t) (ha : a ≠ 0)
    (hR : HasDerivAt R (Real.sin (U t) ^ m * Real.cos (U t) ^ k) t) :
    HasDerivAt (fun s => Real.sin (U s) ^ (m + 1) * Real.cos (U s) ^ (k + 1) / (a * ((m : ℝ) + (k + 2)))
        + ((k : ℝ) + 1) / ((m : ℝ) + (k + 2)) * R s)
      (Real.sin (U t) ^ m * Real.cos (U t) ^ (k + 2)) t := by
  have hT : (m : ℝ) + (k + 2) ≠ 0 := by positivity
  have h1 := ((hU.sin.pow (m + 1)).mul (hU.cos.pow (k + 1))).div_const (a * ((m : ℝ) + (k + 2)))
  convert h1.add (hR.const_mul (((k : ℝ) + 1) / ((m : ℝ) + (k + 2)))) using 1
  have hs := Real.sin_sq_add_cos_sq (U t)
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  field_simp
  push_cast
  linear_combination ((k : ℝ) + 1) * Real.sin (U t) ^ m * Real.cos (U t) ^ k * hs

/-- **`int.trig-power`**: the reduction formulas, given an antiderivative of the integrand left,
wherever the coefficient of `u` is nonzero — which the step states unless it is a numeral. -/
theorem trigPower_sound {ρ : EnvR} {x : String} {rec : Nat → Expr → Option Found} {fuel : Nat}
    {f u : Expr} {m n : ℕ} {r : Found} (hrec : RecGood ρ x rec)
    (hf : evalD ρ f = Real.sin (evalD ρ u) ^ m * Real.cos (evalD ρ u) ^ n)
    (h : trigPower rec fuel x f u m n = some r) : Good ρ x f r := by
  unfold trigPower at h
  cases ha : linearCoeff x u with
  | none => simp [ha] at h
  | some a =>
    cases ht : trigReduce u a m n with
    | none => simp [ha, ht] at h
    | some q =>
      obtain ⟨boundary, rest, coeff, why⟩ := q
      cases hR : rec fuel rest with
      | none => simp [ha, ht, hR] at h
      | some R =>
        simp only [ha, ht, hR, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        intro hch hc
        obtain ⟨hnd, hd⟩ := linearCoeff_spec ha
        have hA : evalD ρ a ≠ 0 := by
          unfold neCond at hc
          split at hc
          · rename_i q
            split at hc
            · exact hc (.ne _) (by simp)
            · rename_i hq
              simp only [Q.isZero, beq_iff_eq] at hq
              simpa using hq
          · exact hc (.ne _) (by simp)
        have hRg : AntiAt ρ x R.F rest := hrec _ _ _ hR hch (fun c hm => hc c (mem_append_right' hm))
        have hU : ∀ t, evalD (upd ρ x t) a = evalD ρ a := fun t => evalD_upd_const hnd t
        unfold trigReduce at ht
        split at ht
        · rename_i hm2
          simp only [Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl, rfl, -⟩ := ht
          obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
          have hRg' : HasDerivAt (fx ρ x R.F)
              (Real.sin (fx ρ x u (ρ x)) ^ j * Real.cos (fx ρ x u (ρ x)) ^ n) (ρ x) := by
            unfold AntiAt at hRg
            convert hRg using 1
            rw [evalD_prodOf]; simp [evalD_pw, fx_at]
          have key := hasDerivAt_sineReduce j n (hd ρ) hA hRg'
          show HasDerivAt (fx ρ x (.add [_, .mul [_, R.F]])) (evalD ρ f) (ρ x)
          convert key using 1
          · funext s
            simp [evalD_eneg, evalD_ediv, evalD_pw, evalD_ofNat, hU, Rat.mkRat_eq_div,
              show j + 2 - 1 = j + 1 by omega]
            push_cast
            ring
          · rw [hf]; simp [fx]
        · split at ht
          · rename_i hm2 hn2
            simp only [Option.some.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, rfl, rfl, -⟩ := ht
            obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
            have hRg' : HasDerivAt (fx ρ x R.F)
                (Real.sin (fx ρ x u (ρ x)) ^ m * Real.cos (fx ρ x u (ρ x)) ^ k) (ρ x) := by
              unfold AntiAt at hRg
              convert hRg using 1
              rw [evalD_prodOf]; simp [evalD_pw, fx_at]
            have key := hasDerivAt_cosineReduce m k (hd ρ) hA hRg'
            show HasDerivAt (fx ρ x (.add [_, .mul [_, R.F]])) (evalD ρ f) (ρ x)
            convert key using 1
            · funext s
              simp [evalD_ediv, evalD_pw, hU, Rat.mkRat_eq_div,
                show k + 2 - 1 = k + 1 by omega]
              try (push_cast; ring)
            · rw [hf]; simp [fx]
          · cases ht

/-! ## Each rule, as the finder applies it -/

/-- **`int.constant`**: `∫ c dx = c·x`. -/
theorem antiConst_sound {ρ : EnvR} {x : String} {f : Expr} (hf : ¬ f.dependsOn x = true) :
    Good ρ x f (antiConst x f) := by
  intro _ _
  show HasDerivAt (fx ρ x (.mul [f, .var x])) (evalD ρ f) (ρ x)
  have : fx ρ x (.mul [f, .var x]) = fun t => evalD ρ f * t := by
    funext t; simp [evalD_upd_const hf t]
  rw [this]
  simpa using (hasDerivAt_id (ρ x)).const_mul (evalD ρ f)

/-- **`int.variable`**: `∫ x dx = x²/2`. -/
theorem antiVar_sound {ρ : EnvR} {x y : String} (hf : (Expr.var y).dependsOn x = true) :
    Good ρ x (.var y) (antiVar x (.var y)) := by
  intro _ _
  have hy : x = y := by simpa [Expr.dependsOn, Expr.freeVars] using hf
  subst hy
  show HasDerivAt (fx ρ x (.mul [.num (Q.ofRat (mkRat 1 2)), .pow (.var x) (Expr.ofInt 2)])) (evalD ρ (.var x)) (ρ x)
  have : fx ρ x (.mul [.num (Q.ofRat (mkRat 1 2)), .pow (.var x) (Expr.ofInt 2)]) = fun t => 1 / 2 * t ^ 2 := by
    funext t; simp [evalD_half, evalD_powTwo]
  rw [this]
  convert (hasDerivAt_pow 2 (ρ x)).const_mul (1 / 2 : ℝ) using 1
  simp

theorem mapM_some {α β : Type} {g : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM g = some r → List.Forall₂ (fun a b => g a = some b) l r
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact List.Forall₂.nil
  | a :: l, r, h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact List.Forall₂.cons hb (mapM_some hbs)

theorem sum_forall₂ {ρ : EnvR} {x : String} {rec : Nat → Expr → Option Found} {fuel : Nat}
    (hrec : RecGood ρ x rec) : ∀ {es : List Expr} {parts : List Found},
    List.Forall₂ (fun e r => rec fuel e = some r) es parts →
    parts.any (·.checked) = false → (∀ c ∈ parts.flatMap (·.conds), HoldsAt ρ c) →
    HasDerivAt (fun t => sumD (upd ρ x t) (parts.map (·.F))) (sumD ρ es) (ρ x)
  | [], [], .nil, _, _ => by simpa using hasDerivAt_const (ρ x) (0 : ℝ)
  | e :: es, p :: ps, .cons h1 h2, hch, hc => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at hch
    have hp : AntiAt ρ x p.F e :=
      hrec fuel e p h1 hch.1 (fun c hm => hc c (by simp only [List.flatMap_cons]; exact mem_append_left' hm))
    have ih := sum_forall₂ hrec h2 hch.2
      (fun c hm => hc c (by simp only [List.flatMap_cons]; exact mem_append_right' hm))
    simp only [List.map_cons, sumD_cons]
    exact hp.add ih

/-- **`int.sum`**: the sum of antiderivatives of the summands is an antiderivative of the sum. -/
theorem antiSum_sound {ρ : EnvR} {x : String} {rec : Nat → Expr → Option Found} {fuel : Nat}
    {es : List Expr} {r : Found} (hrec : RecGood ρ x rec)
    (h : antiSum x rec fuel (.add es) es = some r) : Good ρ x (.add es) r := by
  unfold antiSum at h
  cases hm : es.mapM (rec fuel) with
  | none => simp [hm] at h
  | some parts =>
    simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    intro hch hc
    exact sum_forall₂ hrec (mapM_some hm) hch hc

/-- **`int.constant-multiple`**: the constant factors times an antiderivative of the rest. -/
theorem antiConstMul_sound {ρ : EnvR} {x : String} {rec : Nat → Expr → Option Found} {fuel : Nat}
    {es rest cs : List Expr} {r : Found} (hrec : RecGood ρ x rec)
    (hp : es.partition (·.dependsOn x) = (rest, cs))
    (h : antiConstMul x rec fuel (.mul es) rest cs = some r) : Good ρ x (.mul es) r := by
  unfold antiConstMul at h
  cases hm : rec fuel (Expr.mulN rest) with
  | none => simp [hm] at h
  | some r₀ =>
    simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    intro hch hc
    have h0 : AntiAt ρ x r₀.F (Expr.mulN rest) := hrec _ _ _ hm hch hc
    obtain ⟨h1, h2⟩ := partition_spec hp
    have hcs := filter_not_dep h2
    show HasDerivAt (fx ρ x (.mul (cs ++ [r₀.F]))) (evalD ρ (.mul es)) (ρ x)
    have hf : fx ρ x (.mul (cs ++ [r₀.F])) = fun t => prodD ρ cs * fx ρ x r₀.F t := by
      funext t
      simp only [fx, evalD_mul, prodD_append, prodD_cons, prodD_nil, mul_one,
        prodD_upd_not_free ρ x t (not_mem_freeVarsList hcs)]
    rw [hf]
    convert h0.const_mul (prodD ρ cs) using 1
    rw [evalD_mul, prodD_filter ρ (fun a => a.dependsOn x) es, h1, h2, evalD_mulN']
    ring

/-- A product of factors: only the reduction formulas carry a claim of their own; u-substitution
and integration by parts are marked `checked`. -/
theorem antiProduct_sound {ρ : EnvR} {x : String} {simp : Expr → Option Expr}
    {rec : Nat → Expr → Option Found} {fuel : Nat} {es : List Expr} {r : Found} (hrec : RecGood ρ x rec)
    (h : antiProduct simp x rec fuel (.mul es) es = some r) : Good ρ x (.mul es) r := by
  unfold antiProduct at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; intro hch; simp at hch
  · split at h
    · rename_i u m n ht
      exact trigPower_sound hrec (by rw [evalD_mul]; exact trigPowers_spec ht ρ) h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨r₀, -, rfl⟩ := h
      intro hch; simp at hch

/-- **`int.exp-power`**: `(eᵘ)ᵏ = eᵏᵘ` for every real `u` and `k` (`Real.exp_mul`), distributed
(`dist_soundD`): the integrand is unchanged, so an antiderivative of the new one is one of the old. -/
theorem antiExpPower_sound {ρ : EnvR} {x : String} {rec : Nat → Expr → Option Found} {fuel : Nat}
    {u e : Expr} {r : Found} (hrec : RecGood ρ x rec)
    (h : antiExpPower x rec fuel (.pow (.fn "exp" [u]) e) u e = some r) :
    Good ρ x (.pow (.fn "exp" [u]) e) r := by
  unfold antiExpPower at h
  cases hm : rec fuel (.fn "exp" [Expand.dist (.mul [e, u])]) with
  | none => simp [hm] at h
  | some r₀ =>
    simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    intro hch hc
    have h0 : AntiAt ρ x r₀.F (.fn "exp" [Expand.dist (.mul [e, u])]) := hrec _ _ _ hm hch hc
    have heq : evalD ρ (.pow (.fn "exp" [u]) e) = evalD ρ (.fn "exp" [Expand.dist (.mul [e, u])]) := by
      simp only [evalD_pow, evalD_fn, fnD_one, applyFn_exp, dist_soundD, evalD_mul, prodD_cons, prodD_nil]
      rw [← Real.exp_mul]; ring_nf
    show HasDerivAt _ (evalD ρ (.pow (.fn "exp" [u]) e)) _
    rw [heq]; exact h0

/-- **`int.table`** for `sec² u`, written `cos(u)^(-2)`: `tan u`, where `cos u ≠ 0`. -/
theorem antiSecSq_sound {ρ : EnvR} {x : String} {u e : Expr} {r : Found}
    (he : e.isNumEq (Q.ofInt (-2)) = true)
    (h : antiSecSq x (.pow (.fn "cos" [u]) e) u = some r) : Good ρ x (.pow (.fn "cos" [u]) e) r := by
  unfold antiSecSq at h
  cases ha : linearCoeff x u with
  | none => simp [ha] at h
  | some a =>
    simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    intro _ hc
    obtain ⟨hnd, hd⟩ := linearCoeff_spec ha
    have hcos : Real.cos (evalD ρ u) ≠ 0 := hc (.cosNe u) (by simp)
    have hU : fx ρ x u (ρ x) = evalD ρ u := fx_at ρ x u
    have htan : HasDerivAt (fun t => Real.tan (fx ρ x u t)) (1 / Real.cos (fx ρ x u (ρ x)) ^ 2 * evalD ρ a) (ρ x) :=
      (Real.hasDerivAt_tan (by rw [hU]; exact hcos)).comp (ρ x) (hd ρ)
    have hG : HasDerivAt (fx ρ x (.fn "tan" [u])) (evalD ρ (.pow (.fn "cos" [u]) e) * evalD ρ a) (ρ x) := by
      have hf : fx ρ x (.fn "tan" [u]) = fun t => Real.tan (fx ρ x u t) := by funext t; simp
      rw [hf]
      convert htan using 1
      rw [evalD_pow, evalD_of_isNumEq he, hU]
      simp only [evalD_fn, fnD_one, applyFn_cos, Q.ofInt]
      rw [show (((Rat.ofInt (-2) : ℚ)) : ℝ) = ((-2 : ℤ) : ℝ) by norm_num [Rat.ofInt_eq_cast], Real.rpow_intCast]
      simp [zpow_neg, div_eq_mul_inv]
    exact substitute_sound hnd hG (fun c hm => hc c (mem_append_right' hm))

/-- **`int.power`**, with the linear substitution. -/
theorem antiPower_sound {ρ : EnvR} {x : String} {b e : Expr} {r : Found} (he : ¬ e.dependsOn x = true)
    (h : antiPower x (.pow b e) b e = some r) : Good ρ x (.pow b e) r := by
  unfold antiPower at h
  cases ha : linearCoeff x b with
  | none => simp [ha] at h
  | some a =>
    simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    intro _ hc
    obtain ⟨hnd, hd⟩ := linearCoeff_spec ha
    have hG := powerRule_sound (ρ := ρ) (x := x) (u := b) (n := e) rfl he (hd ρ)
      (fun c hm => hc c (mem_append_left' hm))
    exact substitute_sound hnd hG (fun c hm => hc c (mem_append_right' hm))

/-- **`int.exponential`**, with the linear substitution. -/
theorem antiExponential_sound {ρ : EnvR} {x : String} {b e : Expr} {r : Found} (hb : ¬ b.dependsOn x = true)
    (h : antiExponential x (.pow b e) b e = some r) : Good ρ x (.pow b e) r := by
  unfold antiExponential at h
  cases ha : linearCoeff x e with
  | none => simp [ha] at h
  | some a =>
    simp only [ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    intro _ hc
    obtain ⟨hnd, hd⟩ := linearCoeff_spec ha
    have hG := exponential_sound hb (hd ρ) (fun c hm => hc c (mem_append_left' hm))
    exact substitute_sound hnd hG (fun c hm => hc c (mem_append_right' hm))

/-- **`int.table`**, with the linear substitution. -/
theorem antiFn_sound {ρ : EnvR} {x g : String} {u : Expr} {r : Found}
    (h : antiFn x (.fn g [u]) g u = some r) : Good ρ x (.fn g [u]) r := by
  unfold antiFn at h
  cases ht : table g u with
  | none => simp [ht] at h
  | some T =>
    obtain ⟨G, why, cs⟩ := T
    cases ha : linearCoeff x u with
    | none => simp [ht, ha] at h
    | some a =>
      simp only [ht, ha, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
      subst h
      intro _ hc
      obtain ⟨hnd, hd⟩ := linearCoeff_spec ha
      have hG := table_sound ht (hd ρ) (fun c hm => hc c (mem_append_left' hm))
      exact substitute_sound (g := applyFn g (evalD ρ u)) hnd hG (fun c hm => hc c (mem_append_right' hm))

/-- A power: `(eᵘ)ᵏ`, `sec² u`, a power of sine or cosine, `uⁿ`, or `bᵘ`; the arctangent and
arcsine forms are marked `checked`. -/
theorem antiPow_sound {ρ : EnvR} {x : String} {rec : Nat → Expr → Option Found} {fuel : Nat}
    {b e : Expr} {r : Found} (hrec : RecGood ρ x rec)
    (h : antiPow x rec fuel (.pow b e) b e = some r) : Good ρ x (.pow b e) r := by
  unfold antiPow at h
  split at h
  · rename_i he
    have he' : ¬ e.dependsOn x = true := by simpa using he
    split at h
    · exact antiExpPower_sound hrec h
    · split at h
      · rename_i hsec; exact antiSecSq_sound hsec h
      · split at h
        · rename_i u' m n ht
          exact trigPower_sound hrec (by simpa using trigPowers_spec ht ρ) h
        · cases h
    · split at h
      · rename_i u' m n ht
        exact trigPower_sound hrec (by simpa using trigPowers_spec ht ρ) h
      · cases h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; intro hch; simp at hch
      · exact antiPower_sound he' h
  · split at h
    · rename_i _ hb
      exact antiExponential_sound (by simpa using hb) h
    · cases h

/-- **One level of the finder is sound**, given that the recursion is. -/
theorem antiStep_sound {ρ : EnvR} {x : String} {simp : Expr → Option Expr}
    {rec : Nat → Expr → Option Found} {fuel : Nat} {f : Expr} {r : Found} (hrec : RecGood ρ x rec)
    (h : antiStep simp x rec fuel f = some r) : Good ρ x f r := by
  unfold antiStep at h
  split at h
  · rename_i hf
    simp only [Option.some.injEq] at h; subst h
    exact antiConst_sound (by simpa using hf)
  · rename_i hf
    have hf' : f.dependsOn x = true := by simpa using hf
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact antiVar_sound hf'
    · exact antiSum_sound hrec h
    · rename_i es
      split at h
      rename_i rest cs hp
      split at h
      · exact antiConstMul_sound hrec hp h
      · exact antiProduct_sound hrec h
    · exact antiPow_sound hrec h
    · exact antiFn_sound h
    · cases h

/-- **The finder is sound** (`anti_sound`): at any point `ρ`, a result that does not rest on the
check is an antiderivative there wherever what its steps assume holds. By induction on the depth
bound, from `antiStep_sound`. -/
theorem anti_sound (simp : Expr → Option Expr) (x : String) (ρ : EnvR) :
    ∀ (d fuel : Nat) (f : Expr) (r : Found), anti simp x d fuel f = some r → Good ρ x f r
  | 0, _, _, _, h => by simp [anti] at h
  | d + 1, fuel, f, r, h => by
    simp only [anti] at h
    exact antiStep_sound (fun fuel' g r' h' => anti_sound simp x ρ d fuel' g r' h') h

/-- **Where no step assumes anything and none rests on the check, the finder's candidate is an
antiderivative at every point**: the verified steps need no condition and no check. -/
theorem anti_sound_everywhere (simp : Expr → Option Expr) (x : String) {d fuel : Nat} {f : Expr}
    {r : Found} (h : anti simp x d fuel f = some r) (hch : r.checked = false) (hnil : r.conds = [])
    (ρ : EnvR) : AntiAt ρ x r.F f :=
  anti_sound simp x ρ d fuel f r h hch (by simp [hnil])

/-! ## The conditions are necessary -/

/-- **`int.power.assuming` needs its condition**: `∫ x⁻¹ dx = ln x` (what `powerRule` gives) fails at
`x = 0`, where `ln` has no derivative. -/
theorem not_power_sound :
    ¬ ∀ ρ : EnvR, AntiAt ρ "x" (powerRule (.var "x") Expr.minusOne).1 (.pow (.var "x") Expr.minusOne) := by
  intro hs
  have h := hs (fun _ => 0)
  have hG : (powerRule (.var "x") Expr.minusOne).1 = .fn "ln" [.var "x"] := by
    simp [powerRule, Expr.isNumEq, Expr.minusOne, Q.eq]
  rw [hG] at h
  unfold AntiAt at h
  have hf : fx (fun _ => 0) "x" (.fn "ln" [.var "x"]) = Real.log := by funext t; simp
  rw [hf] at h
  exact Real.differentiableAt_log_iff.mp h.differentiableAt (by simp)

/-- **`int.table.assuming` needs its condition**: `∫ sec² x dx = tan x` fails at `x = π/2`, where
`cos x = 0` and `tan` has no derivative. -/
theorem not_secSq_sound :
    ¬ ∀ ρ : EnvR, AntiAt ρ "x" (.fn "tan" [.var "x"]) (.pow (.fn "cos" [.var "x"]) (.num (Q.ofInt (-2)))) := by
  intro hs
  have h := hs (fun _ => Real.pi / 2)
  unfold AntiAt at h
  have hf : fx (fun _ => Real.pi / 2) "x" (.fn "tan" [.var "x"]) = Real.tan := by funext t; simp
  rw [hf] at h
  exact Real.differentiableAt_tan.mp h.differentiableAt (by simp)

/-- **`int.exponential.assuming` needs its condition**: `∫ bˣ dx = bˣ / ln b` fails at `b = 1`, where
`ln b = 0`: the candidate is `0` and the integrand `1`. -/
theorem not_exponential_sound :
    ¬ ∀ ρ : EnvR, AntiAt ρ "x" (Expr.div (.pow (.var "b") (.var "x")) (.fn "ln" [.var "b"]))
      (.pow (.var "b") (.var "x")) := by
  intro hs
  have h := hs (fun _ => 1)
  unfold AntiAt at h
  have hf : fx (fun _ => 1) "x" (Expr.div (.pow (.var "b") (.var "x")) (.fn "ln" [.var "b"]))
      = fun _ => 0 := by
    funext t; simp [evalD_ediv, upd]
  rw [hf] at h
  have := h.unique (hasDerivAt_const _ _)
  simp at this

/-- **`int.linear-substitution.assuming` needs its condition**: `∫ cos(kx) dx = sin(kx)/k` fails at
`k = 0`: the candidate is `0` and the integrand `1`. -/
theorem not_substitute_sound :
    ¬ ∀ ρ : EnvR, AntiAt ρ "x" (Expr.div (.fn "sin" [.mul [.var "k", .var "x"]]) (.var "k"))
      (.fn "cos" [.mul [.var "k", .var "x"]]) := by
  intro hs
  have h := hs (fun _ => 0)
  unfold AntiAt at h
  have hf : fx (fun _ => 0) "x" (Expr.div (.fn "sin" [.mul [.var "k", .var "x"]]) (.var "k"))
      = fun _ => 0 := by
    funext t; simp [evalD_ediv, upd]
  rw [hf] at h
  have := h.unique (hasDerivAt_const _ _)
  simp [upd] at this

/-- **`int.trig-power.assuming` needs its condition**: the reduction formula for `∫ sin²(kx) dx`
(what `trigPower` gives, with `∫ 1 dx = x`) fails at `k = 0`: the candidate is `x/2` and the
integrand `0`. -/
theorem not_trigPower_sound :
    ¬ ∀ ρ : EnvR, AntiAt ρ "x"
      (.add [Expr.neg (Expr.div (.mul [.fn "sin" [.mul [.var "k", .var "x"]], .fn "cos" [.mul [.var "k", .var "x"]]])
          (.mul [.var "k", Expr.ofInt 2])),
        .mul [.num (Q.ofRat (mkRat 1 2)), .mul [Expr.one, .var "x"]]])
      (.pow (.fn "sin" [.mul [.var "k", .var "x"]]) (Expr.ofInt 2)) := by
  intro hs
  have h := hs (fun _ => 0)
  unfold AntiAt at h
  have hf : fx (fun _ => 0) "x"
      (.add [Expr.neg (Expr.div (.mul [.fn "sin" [.mul [.var "k", .var "x"]], .fn "cos" [.mul [.var "k", .var "x"]]])
          (.mul [.var "k", Expr.ofInt 2])),
        .mul [.num (Q.ofRat (mkRat 1 2)), .mul [Expr.one, .var "x"]]])
      = fun t => 1 / 2 * t := by
    funext t; simp [evalD_eneg, evalD_ediv, evalD_half, upd]
  rw [hf] at h
  have := h.unique ((hasDerivAt_id (0 : ℝ)).const_mul (1 / 2 : ℝ))
  simp [evalD_powTwo, upd] at this

end MathProofs
end
