import Proofs.Deriv
import Proofs.SimpReal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
/-!
# The calculus rules, as the engine writes them

`Deriv.lean` proves the laws of differentiation for the shapes a textbook writes. Here each of the
four rules that need something is proved for exactly the term the engine produces, under exactly the
conditions its step states:

- `AssumeD ρ e` is what a step on `e = diff(body, x)` assumes at the point `ρ`, read off the same
  case analysis as the engine's `diffConds`: the parts it splits apart differentiable, and `u > 0`
  for `ln u` and for a power by a non-integer or symbolic exponent, `u ≠ 0` for a negative integer
  power, `cos u ≠ 0` for `tan u`, `b > 0` for `b^u` and for `f^g`.
- `diffSumAll_sound`, `diffProductAll_sound`, `diffPowerAll_sound`, `diffChainAll_sound`: under
  `AssumeD`, the step keeps the value (`evalD`).
- `smooth_differentiable`: a `smooth` term is differentiable everywhere, so where the engine's
  conditions list is empty, `AssumeD` holds at every point (`assumeD_of_conds_nil`) and the verified
  halves (`diff.sum`, …) are sound unconditionally (`diffSum_sound`, …); the `.assuming` halves are
  sound wherever what they state holds (`diffSumAssuming_sound_on`, …).
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Expr

/-! ## Smooth terms -/

theorem upd_apply (ρ : EnvR) (x y : String) (t : ℝ) : upd ρ x t y = if y = x then t else ρ y := rfl

theorem posNumeral_num {b : Expr} (h : posNumeral b = true) : ∃ q, b = .num q := by
  cases b with
  | num q => exact ⟨q, rfl⟩
  | _ => simp [posNumeral] at h

theorem posNumeral_pos {b : Expr} (h : posNumeral b = true) (ρ : EnvR) : 0 < evalD ρ b := by
  obtain ⟨q, rfl⟩ := posNumeral_num h
  simp only [posNumeral, Bool.and_eq_true, Bool.not_eq_true'] at h
  have hn : ¬ q.val.num < 0 := by simpa [Q.isNeg] using h.1
  have hz : q.val ≠ 0 := by simpa [Q.isZero] using h.2
  have : (0 : ℚ) < q.val := lt_of_le_of_ne (Rat.num_nonneg.mp (not_lt.mp hn)) (Ne.symm hz)
  simpa using (show (0 : ℝ) < (q.val : ℝ) by exact_mod_cast this)

mutual
  /-- **A `smooth` term is differentiable everywhere**, in each variable. -/
  theorem smooth_differentiable (x : String) : ∀ (e : Expr), smooth e = true →
      ∀ ρ, Differentiable ℝ (fun t => evalD (upd ρ x t) e)
    | .num q, _, ρ => by simp
    | .var y, _, ρ => by
      simp only [evalD_var, upd_apply]
      split
      · exact differentiable_id
      · exact differentiable_const _
    | .add es, h, ρ => by
      simp only [evalD_add]
      exact smoothList_sum x es (by simpa [smooth] using h) ρ
    | .mul es, h, ρ => by
      simp only [evalD_mul]
      exact smoothList_prod x es (by simpa [smooth] using h) ρ
    | .pow b e, h, ρ => by
      simp only [smooth, Bool.or_eq_true, Bool.and_eq_true] at h
      simp only [evalD_pow]
      rcases h with h | ⟨hb, he⟩
      · split at h
        · rename_i n
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨hint, hnn⟩, hb⟩ := h
          have hcast : (n.val : ℝ) = ((n.val.num.toNat : ℕ) : ℝ) := by
            have hd : n.val.den = 1 := by simpa [Q.isInt] using hint
            rw [Rat.cast_def, hd]; push_cast; rw [div_one]; exact_mod_cast (Int.toNat_of_nonneg hnn).symm
          simp only [evalD_num, hcast, Real.rpow_natCast]
          exact (smooth_differentiable x b hb ρ).pow _
        · cases h
      · have hp := posNumeral_pos hb ρ
        obtain ⟨q, rfl⟩ := posNumeral_num hb
        simp only [evalD_num] at hp ⊢
        intro t
        exact (differentiableAt_const _).rpow (smooth_differentiable x e he ρ t) hp.ne'
    | .fn f [u], h, ρ => by
      simp only [smooth, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨hf, hu⟩ := h
      have hd := smooth_differentiable x u hu ρ
      simp only [evalD_fn, fnD_one]
      rcases hf with ((rfl | rfl) | rfl) | rfl
      · simpa [applyFn] using hd.sin
      · simpa [applyFn] using hd.cos
      · simpa [applyFn] using hd.exp
      · simpa [applyFn] using hd.arctan
    | .fn f [], _, ρ => by simp
    | .fn f (_ :: _ :: _), h, _ => by simp [smooth] at h
    | .matrix _, h, _ => by simp [smooth] at h
  theorem smoothList_sum (x : String) : ∀ (es : List Expr), smoothList es = true →
      ∀ ρ, Differentiable ℝ (fun t => sumD (upd ρ x t) es)
    | [], _, ρ => by simp
    | e :: es, h, ρ => by
      simp only [smoothList, Bool.and_eq_true] at h
      simp only [sumD_cons]
      exact (smooth_differentiable x e h.1 ρ).add (smoothList_sum x es h.2 ρ)
  theorem smoothList_prod (x : String) : ∀ (es : List Expr), smoothList es = true →
      ∀ ρ, Differentiable ℝ (fun t => prodD (upd ρ x t) es)
    | [], _, ρ => by simp
    | e :: es, h, ρ => by
      simp only [smoothList, Bool.and_eq_true] at h
      simp only [prodD_cons]
      exact (smooth_differentiable x e h.1 ρ).mul (smoothList_prod x es h.2 ρ)
end

theorem smooth_diffAt {x : String} {e : Expr} (h : smooth e = true) (ρ : EnvR) : DiffAt ρ x e :=
  smooth_differentiable x e h ρ (ρ x)

theorem diffCond_nil {u : Expr} (h : diffCond u = []) : smooth u = true := by
  unfold diffCond at h; split at h
  · assumption
  · cases h

/-! ## What a step assumes -/

/-- The exponent condition of a power `b^n` with `n` free of `x`: none for a natural numeral, `b ≠ 0`
for another integer numeral, `b > 0` otherwise. -/
def ExpCond (ρ : EnvR) (b n : Expr) : Prop :=
  match n with
  | .num q => if q.isInt = true ∧ 0 ≤ q.val.num then True else if q.isInt = true then evalD ρ b ≠ 0 else 0 < evalD ρ b
  | _ => 0 < evalD ρ b

/-- What a calculus step on `e` assumes at `ρ`: the case analysis of `diffConds`, as propositions. -/
def AssumeD (ρ : EnvR) (e : Expr) : Prop :=
  match target e with
  | none => True
  | some (body, x) =>
    match body with
    | .add es => ∀ a ∈ es, DiffAt ρ x a
    | .mul es => ∀ a ∈ es, DiffAt ρ x a
    | .pow b n =>
      if b.dependsOn x = true ∧ n.dependsOn x = false then DiffAt ρ x b ∧ ExpCond ρ b n
      else if b.dependsOn x = false ∧ n.dependsOn x = true then 0 < evalD ρ b ∧ DiffAt ρ x n
      else 0 < evalD ρ b ∧ DiffAt ρ x b ∧ DiffAt ρ x n
    | .fn "tan" [u] => Real.cos (evalD ρ u) ≠ 0 ∧ DiffAt ρ x u
    | .fn "ln" [u] => 0 < evalD ρ u ∧ DiffAt ρ x u
    | .fn "arcsin" [u] => (-1 < evalD ρ u ∧ evalD ρ u < 1) ∧ DiffAt ρ x u
    | .fn "arccos" [u] => (-1 < evalD ρ u ∧ evalD ρ u < 1) ∧ DiffAt ρ x u
    | .fn _ [u] => DiffAt ρ x u
    | _ => True

theorem flatMap_diffCond_nil {es : List Expr} (h : es.flatMap diffCond = []) (x : String) (ρ : EnvR) :
    ∀ a ∈ es, DiffAt ρ x a := fun a ha =>
  smooth_diffAt (diffCond_nil (List.flatMap_eq_nil_iff.mp h a ha)) ρ

/-- **Where the engine's conditions list is empty, what the step assumes holds everywhere.** -/
theorem assumeD_of_conds_nil {e : Expr} (h : diffConds e = []) (ρ : EnvR) : AssumeD ρ e := by
  unfold AssumeD
  cases ht : target e with
  | none => trivial
  | some p =>
    obtain ⟨body, x⟩ := p
    simp only [diffConds, ht] at h
    dsimp only
    cases body with
    | add es => exact flatMap_diffCond_nil h x ρ
    | mul es => exact flatMap_diffCond_nil h x ρ
    | pow b n =>
      simp only at h ⊢
      by_cases h1 : b.dependsOn x = true ∧ n.dependsOn x = false
      · rw [if_pos h1]
        have hc : (b.dependsOn x && !n.dependsOn x) = true := by simp [h1.1, h1.2]
        rw [if_pos hc] at h
        obtain ⟨ha, hb⟩ := List.append_eq_nil_iff.mp h
        refine ⟨smooth_diffAt (diffCond_nil hb) ρ, ?_⟩
        cases n with
        | num q =>
          simp only [ExpCond]
          by_cases hq : q.isInt = true ∧ 0 ≤ q.val.num
          · rw [if_pos hq]; trivial
          · exfalso
            have hq' : (q.isInt && decide (0 ≤ q.val.num)) = false := by
              simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
              by_cases hi : q.isInt = true
              · exact Or.inr (fun h0 => hq ⟨hi, h0⟩)
              · exact Or.inl (by simpa using hi)
            simp only [hq', Bool.false_eq_true, ite_false] at ha
            split at ha <;> cases ha
        | _ => simp at ha
      · rw [if_neg h1]
        have hc : (b.dependsOn x && !n.dependsOn x) = false := by
          cases hb : b.dependsOn x <;> cases hn : n.dependsOn x <;> simp_all
        rw [if_neg (by simp [hc])] at h
        by_cases h2 : b.dependsOn x = false ∧ n.dependsOn x = true
        · rw [if_pos h2]
          have hc2 : (!b.dependsOn x && n.dependsOn x) = true := by simp [h2.1, h2.2]
          rw [if_pos hc2] at h
          obtain ⟨ha, hb⟩ := List.append_eq_nil_iff.mp h
          split at ha
          · rename_i hp; exact ⟨posNumeral_pos hp ρ, smooth_diffAt (diffCond_nil hb) ρ⟩
          · cases ha
        · rw [if_neg h2]
          have hc2 : (!b.dependsOn x && n.dependsOn x) = false := by
            cases hb : b.dependsOn x <;> cases hn : n.dependsOn x <;> simp_all
          rw [if_neg (by simp [hc2])] at h
          simp at h
    | fn f args =>
      cases args with
      | nil => simp
      | cons u rest =>
        cases rest with
        | cons _ _ => simp
        | nil =>
          by_cases ht : f = "tan"
          · subst ht; simp at h
          · by_cases hl : f = "ln"
            · subst hl; simp at h
            · by_cases has : f = "arcsin"
              · subst has; simp at h
              · by_cases hac : f = "arccos"
                · subst hac; simp at h
                · simp only [ht, hl, has, hac] at h ⊢
                  exact smooth_diffAt (diffCond_nil h) ρ
    | num q => trivial
    | var y => trivial
    | matrix rows => trivial

/-! ## The rules, as the engine writes them -/

theorem rule_target {name : String} {f : Expr × String → Option RuleResult} {e : Expr} {res : RuleResult}
    (h : (MathEngine.rule name f).apply e = some res) :
    ∃ body x, target e = some (body, x) ∧ e = .fn "diff" [body, .var x] ∧ f (body, x) = some res := by
  unfold MathEngine.rule at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨body, x⟩, hp, h⟩ := h
  exact ⟨body, x, hp, target_spec hp, h⟩

theorem fx_at (ρ : EnvR) (x : String) (u : Expr) : fx ρ x u (ρ x) = evalD ρ u := by simp [fx]

theorem evalD_D (ρ : EnvR) (f : Expr) (x : String) : evalD ρ (MathEngine.D f x) = D ρ x f := evalD_diff ρ f x

/-- **`diff.sum`, where every summand is differentiable.** -/
theorem diffSumAll_sound {e : Expr} {res : RuleResult} (h : diffSumAll.apply e = some res) (ρ : EnvR)
    (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result := by
  obtain ⟨body, x, ht, rfl, hf⟩ := rule_target h
  dsimp only at hf
  split at hf
  · rename_i a b es
    simp only [Option.some.injEq] at hf; subst hf
    simp only [AssumeD, ht] at hA
    rw [evalD_diff]
    exact diff_sum_sound ρ x hA
  · cases hf

/-- The derivative of a product, factor by factor. -/
def DProd (ρ : EnvR) (x : String) : List Expr → ℝ
  | [] => 0
  | f :: r => D ρ x f * prodD ρ r + evalD ρ f * DProd ρ x r

theorem hasDerivAt_prodD (ρ : EnvR) (x : String) : ∀ {fs : List Expr}, (∀ f ∈ fs, DiffAt ρ x f) →
    HasDerivAt (fun t => prodD (upd ρ x t) fs) (DProd ρ x fs) (ρ x)
  | [], _ => by simpa [DProd] using hasDerivAt_const (ρ x) (1 : ℝ)
  | f :: r, h => by
    have h1 : HasDerivAt (fx ρ x f) (D ρ x f) (ρ x) := (h f List.mem_cons_self).hasDerivAt
    have h2 := hasDerivAt_prodD ρ x (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have := h1.mul h2
    simp only [prodD_cons, DProd]
    convert this using 1
    simp only [fx_at, show prodD (upd ρ x (ρ x)) r = prodD ρ r by simp]

theorem sumD_prodTerms (ρ : EnvR) (x : String) : ∀ (acc rest : List Expr),
    sumD ρ (prodTerms x acc rest) = prodD ρ acc * DProd ρ x rest
  | acc, [] => by simp [prodTerms, DProd]
  | acc, f :: r => by
    simp only [prodTerms, sumD_cons, evalD_mul, prodD_cons, evalD_D, prodD_append, sumD_prodTerms ρ x _ r,
      DProd, prodD_nil]
    ring

/-- **`diff.product`, for any number of factors, where every factor is differentiable.** -/
theorem diffProductAll_sound {e : Expr} {res : RuleResult} (h : diffProductAll.apply e = some res) (ρ : EnvR)
    (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result := by
  obtain ⟨body, x, ht, rfl, hf⟩ := rule_target h
  dsimp only at hf
  split at hf
  · rename_i f g fs
    simp only [Option.some.injEq] at hf; subst hf
    simp only [AssumeD, ht] at hA
    rw [evalD_diff, evalD_add, sumD_prodTerms, prodD_nil, one_mul, D_eq]
    exact (hasDerivAt_prodD ρ x hA).deriv
  · cases hf

/-- **`diff.chain`**: `sin`, `cos`, `exp`, `arctan` where the inner function is differentiable; `tan`
where also `cos u ≠ 0`; `ln` where also `u > 0`; `arcsin` and `arccos` where also `-1 < u < 1`. -/
theorem diffChainAll_sound {e : Expr} {res : RuleResult} (h : diffChainAll.apply e = some res) (ρ : EnvR)
    (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result := by
  obtain ⟨body, x, ht, rfl, hf⟩ := rule_target h
  dsimp only at hf
  split at hf
  · rename_i f u
    split at hf
    · rename_i fprime law hout
      simp only [Option.some.injEq] at hf; subst hf
      simp only [AssumeD, ht] at hA
      -- the chain factor: `u'`, or nothing when `u` is `x` itself (`x' = 1`)
      have hinner : evalD ρ (.mul (fprime :: innerOf u x)) = evalD ρ fprime * D ρ x u := by
        unfold innerOf
        split
        · rename_i y
          split
          · rename_i hy
            have : y = x := by simpa using hy
            subst this
            rw [diff_variable_sound]; simp
          · simp [evalD_D]
        · simp [evalD_D]
      rw [evalD_diff, hinner, D_eq, fx_fn]
      unfold outerOf at hout
      split at hout
      · cases hout
        have hA' : DiffAt ρ x u := by simpa [AssumeD, ht] using hA
        have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hA'.hasDerivAt
        simp only [applyFn_sin]; rw [hd.sin.deriv]; simp [fx_at, applyFn]
      · cases hout
        have hA' : DiffAt ρ x u := by simpa [AssumeD, ht] using hA
        have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hA'.hasDerivAt
        simp only [applyFn_cos]; rw [hd.cos.deriv]
        simp [fx_at, applyFn, Expr.neg, evalD_minusOne]
      · cases hout
        simp only [AssumeD, ht] at hA
        have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hA.2.hasDerivAt
        have hc' : Real.cos (fx ρ x u (ρ x)) ≠ 0 := by rw [fx_at]; exact hA.1
        show deriv (Real.tan ∘ fx ρ x u) (ρ x) = _
        rw [((Real.hasDerivAt_tan hc').comp (ρ x) hd).deriv]
        simp only [fx_at, evalD_pow, evalD_fn, fnD_one, applyFn, evalD_num, Expr.ofInt, Q_val_ofInt]
        rw [show (((-2 : ℤ) : ℚ) : ℝ) = ((-2 : ℤ) : ℝ) by push_cast; rfl, Real.rpow_intCast]
        simp [zpow_neg, zpow_two, div_eq_mul_inv]
      · cases hout
        have hA' : DiffAt ρ x u := by simpa [AssumeD, ht] using hA
        have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hA'.hasDerivAt
        simp only [applyFn_exp]; rw [hd.exp.deriv]; simp [fx_at, applyFn]
      · cases hout
        simp only [AssumeD, ht] at hA
        have hd : HasDerivAt (fx ρ x u) (D ρ x u) (ρ x) := hA.2.hasDerivAt
        have hu' : fx ρ x u (ρ x) ≠ 0 := by rw [fx_at]; exact hA.1.ne'
        simp only [applyFn_ln]
        rw [(hd.log hu').deriv]
        simp only [fx_at, evalD_pow, evalD_minusOne, Real.rpow_neg_one]
        ring
      · cases hout
        have hA' : DiffAt ρ x u := by simpa [AssumeD, ht] using hA
        have h := diff_chain_arctan_sound ρ x hA'
        rw [D_eq, fx_fn] at h
        rw [h]; simp [evalD_mul]
      · cases hout
        simp only [AssumeD, ht] at hA
        have h := diff_chain_arcsin_sound ρ x hA.2 hA.1.1.ne' hA.1.2.ne
        rw [D_eq, fx_fn] at h
        rw [h]; simp [evalD_mul]
      · cases hout
        simp only [AssumeD, ht] at hA
        have h := diff_chain_arccos_sound ρ x hA.2 hA.1.1.ne' hA.1.2.ne
        rw [D_eq, fx_fn] at h
        rw [h]; simp [evalD_mul]
      · cases hout
    · cases hf
  · cases hf

/-- A power by an exponent `c` free of `x`: the derivative where the base is differentiable and
nonzero, or where `c ≥ 1`, or for `c = 0` (the power is constantly 1). -/
theorem hasDerivAt_rpow_const' {f : ℝ → ℝ} {f' c t : ℝ} (hf : HasDerivAt f f' t)
    (hc : c = 0 ∨ f t ≠ 0 ∨ 1 ≤ c) :
    HasDerivAt (fun s => f s ^ c) (f' * c * f t ^ (c - 1)) t := by
  rcases hc with rfl | hc
  · simpa using hasDerivAt_const t (1 : ℝ)
  · exact hf.rpow_const hc

/-- **`diff.power`**: `u^c` for `c` free of `x`, where `u` is differentiable and as `ExpCond` says;
`b^u` for `b` free of `x` and positive; `f^g` for a positive `f`. -/
theorem diffPowerAll_sound {e : Expr} {res : RuleResult} (h : diffPowerAll.apply e = some res) (ρ : EnvR)
    (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result := by
  obtain ⟨body, x, ht, rfl, hf⟩ := rule_target h
  dsimp only at hf
  split at hf
  swap; · cases hf
  rename_i b n
  simp only [AssumeD, ht] at hA
  rw [evalD_diff, D_eq]
  have hfun : fx ρ x (.pow b n) = fun t => fx ρ x b t ^ fx ρ x n t := rfl
  rw [hfun]
  split at hf
  · -- the exponent is free of `x`
    rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
    rw [if_pos hc] at hA
    obtain ⟨hdb, hE⟩ := hA
    have hn : fx ρ x n = fun _ => evalD ρ n := fx_const (by simp [hc.2])
    rw [hn]
    have hcond : evalD ρ n = 0 ∨ fx ρ x b (ρ x) ≠ 0 ∨ 1 ≤ evalD ρ n := by
      rw [fx_at]
      unfold ExpCond at hE
      split at hE
      · rename_i q
        simp only [evalD_num]
        split at hE
        · rename_i hq
          obtain ⟨hint, hnn⟩ := hq
          have hd : q.val.den = 1 := by simpa [Q.isInt] using hint
          have hv : (q.val : ℝ) = (q.val.num : ℝ) := by rw [Rat.cast_def, hd]; simp
          rw [hv]
          rcases lt_or_eq_of_le hnn with hlt | heq
          · right; right; exact_mod_cast hlt
          · left; rw [← heq]; simp
        · split at hE
          · exact Or.inr (Or.inl hE)
          · exact Or.inr (Or.inl hE.ne')
      · exact Or.inr (Or.inl hE.ne')
    have hd := hasDerivAt_rpow_const' hdb.hasDerivAt hcond
    rw [hd.deriv]
    split at hf
    · rename_i y
      split at hf
      · rename_i hy
        have : y = x := by simpa using hy
        subst this
        simp only [Option.some.injEq] at hf; subst hf
        have hdx : D ρ y (.var y) = 1 := by rw [diff_variable_sound]; simp
        simp only [evalD_mul, prodD_cons, prodD_nil, evalD_pow, evalD_add, sumD_cons, sumD_nil,
          evalD_minusOne, fx_at, ← D_eq, hdx]
        ring_nf
      · simp only [Option.some.injEq] at hf; subst hf
        simp only [evalD_mul, prodD_cons, prodD_nil, evalD_pow, evalD_add, sumD_cons, sumD_nil,
          evalD_minusOne, fx_at, evalD_D, ← D_eq]
        ring_nf
    · simp only [Option.some.injEq] at hf; subst hf
      simp only [evalD_mul, prodD_cons, prodD_nil, evalD_pow, evalD_add, sumD_cons, sumD_nil,
        evalD_minusOne, fx_at, evalD_D, ← D_eq]
      ring_nf
  · split at hf
    · -- the base is free of `x`: `b^u`
      rename_i hc0 hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc hc0
      have hnot : ¬ (b.dependsOn x = true ∧ n.dependsOn x = false) := by
        rintro ⟨h1, -⟩; rw [hc.1] at h1; cases h1
      rw [if_neg hnot, if_pos hc] at hA
      obtain ⟨hpos, hdn⟩ := hA
      have hb : fx ρ x b = fun _ => evalD ρ b := fx_const (by simp [hc.1])
      rw [hb]
      rw [(hdn.hasDerivAt.const_rpow hpos).deriv]
      simp only [Option.some.injEq] at hf; subst hf
      simp only [evalD_mul, prodD_cons, prodD_nil, evalD_pow, evalD_fn, fnD_one, applyFn_ln, fx_at, evalD_D, ← D_eq]
      ring
    · split at hf
      · -- both depend on `x`: `f^g = e^(g ln f)`
        rename_i hc0 hc1 hc
        simp only [Bool.and_eq_true] at hc
        have hnot : ¬ (b.dependsOn x = true ∧ n.dependsOn x = false) := by
          rintro ⟨-, h2⟩; rw [hc.2] at h2; cases h2
        have hnot2 : ¬ (b.dependsOn x = false ∧ n.dependsOn x = true) := by
          rintro ⟨h1, -⟩; rw [hc.1] at h1; cases h1
        rw [if_neg hnot, if_neg hnot2] at hA
        obtain ⟨hpos, hdb, hdn⟩ := hA
        have hpos' : 0 < fx ρ x b (ρ x) := by rw [fx_at]; exact hpos
        rw [(hdb.hasDerivAt.rpow hdn.hasDerivAt hpos').deriv]
        simp only [Option.some.injEq] at hf; subst hf
        simp only [evalD_mul, prodD_cons, prodD_nil, evalD_pow, evalD_fn, fnD_one, applyFn_ln, fx_at, evalD_D,
          evalD_add, sumD_cons, sumD_nil, Expr.div, evalD_minusOne, Real.rpow_neg_one, ← D_eq]
        rw [Real.rpow_sub_one hpos.ne']
        field_simp
        ring
      · cases hf

/-! ## The two halves -/

theorem verified_of_all {r : PlainRule}
    (hall : ∀ e res, r.apply e = some res → ∀ ρ, AssumeD ρ e → evalD ρ e = evalD ρ res.result)
    {e : Expr} {res : RuleResult} (h : (verifiedHalf r).apply e = some res) (ρ : EnvR) :
    evalD ρ e = evalD ρ res.result := by
  obtain ⟨h₀, hc⟩ := verifiedHalf_some h
  exact hall e res h₀ ρ (assumeD_of_conds_nil hc ρ)

theorem assuming_of_all {r : PlainRule} {n : String}
    (hall : ∀ e res, r.apply e = some res → ∀ ρ, AssumeD ρ e → evalD ρ e = evalD ρ res.result)
    {e : Expr} {res : RuleResult} (h : (assumingHalf r n).apply e = some res) (ρ : EnvR) (hA : AssumeD ρ e) :
    evalD ρ e = evalD ρ res.result := by
  obtain ⟨r₀, h₀, hres, -⟩ := assumingHalf_some h
  rw [hres]; exact hall e r₀ h₀ ρ hA

/-- **`diff.sum` is sound everywhere**: it fires only where every summand is smooth. -/
theorem diffSum_sound {e : Expr} {res : RuleResult} (h : diffSum.apply e = some res) (ρ : EnvR) :
    evalD ρ e = evalD ρ res.result := verified_of_all (fun _ _ h => diffSumAll_sound h) h ρ
/-- **`diff.sum.assuming` is sound where what it states holds.** -/
theorem diffSumAssuming_sound_on {e : Expr} {res : RuleResult} (h : diffSumAssuming.apply e = some res) (ρ : EnvR)
    (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result := assuming_of_all (fun _ _ h => diffSumAll_sound h) h ρ hA

theorem diffProduct_sound {e : Expr} {res : RuleResult} (h : diffProduct.apply e = some res) (ρ : EnvR) :
    evalD ρ e = evalD ρ res.result := verified_of_all (fun _ _ h => diffProductAll_sound h) h ρ
theorem diffProductAssuming_sound_on {e : Expr} {res : RuleResult} (h : diffProductAssuming.apply e = some res)
    (ρ : EnvR) (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result :=
  assuming_of_all (fun _ _ h => diffProductAll_sound h) h ρ hA

theorem diffPower_sound {e : Expr} {res : RuleResult} (h : diffPower.apply e = some res) (ρ : EnvR) :
    evalD ρ e = evalD ρ res.result := verified_of_all (fun _ _ h => diffPowerAll_sound h) h ρ
theorem diffPowerAssuming_sound_on {e : Expr} {res : RuleResult} (h : diffPowerAssuming.apply e = some res)
    (ρ : EnvR) (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result :=
  assuming_of_all (fun _ _ h => diffPowerAll_sound h) h ρ hA

theorem diffChain_sound {e : Expr} {res : RuleResult} (h : diffChain.apply e = some res) (ρ : EnvR) :
    evalD ρ e = evalD ρ res.result := verified_of_all (fun _ _ h => diffChainAll_sound h) h ρ
theorem diffChainAssuming_sound_on {e : Expr} {res : RuleResult} (h : diffChainAssuming.apply e = some res)
    (ρ : EnvR) (hA : AssumeD ρ e) : evalD ρ e = evalD ρ res.result :=
  assuming_of_all (fun _ _ h => diffChainAll_sound h) h ρ hA

end MathProofs
