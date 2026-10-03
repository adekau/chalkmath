import MathEngine.Rewriting
/-!
# Rewrite steps are rewrites, and the termination check is sound

`step` (`Rewriting.lean`) finds a redex and rewrites it. `step_sound`: the rule it names is one of
the system's, and the result is the term with an instance of the rule's left side, at the position
it names, replaced by the same instance of the right side; `normalize_chain` and `normalize_normal`:
`rewrite` shows a chain of such steps, ending, when it says so, at a normal form.

`terminates(R; …)` interprets every symbol as a linear function with coefficients of at least one
(`interpOf`) and checks every rule with `decreases`. `decreases_sound`: when the check passes, the
left side is worth more than the right for every value of the variables, so (`eval_subst`, and the
coefficients) for every instance of the rule in every context: `step_decreases`; when it fails, some
values make the left side worth no more (`decreases_complete`). A natural number
cannot decrease for ever, so no term rewrites for ever (`no_infinite_rewriting`).
-/
namespace MathEngine
namespace TRS

/-! ## Matching -/

/-- `τ` extends `σ`: whatever `σ` binds, `τ` binds the same way. -/
def Ext (σ τ : Subst) : Prop := ∀ x u, σ.lookup x = some u → τ.lookup x = some u

theorem Ext.refl (σ : Subst) : Ext σ σ := fun _ _ h => h

theorem Ext.trans {a b c : Subst} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  fun x u h => h2 x u (h1 x u h)

mutual
/-- A match extends the substitution it started from, and makes the pattern the term, under it and
under anything that extends it. -/
theorem matchT_sound : ∀ (σ : Subst) (p t : T) (σ' : Subst), matchT σ p t = some σ' →
    Ext σ σ' ∧ ∀ τ, Ext σ' τ → p.subst τ = t
  | σ, .v x, t, σ', h => by
    cases hl : σ.lookup x with
    | none =>
      simp only [matchT, hl, Option.some.injEq] at h
      subst h
      refine ⟨fun y u hy => ?_, fun τ hτ => ?_⟩
      · by_cases hyx : y = x
        · subst hyx; simp [hl] at hy
        · have e : (y == x) = false := by simp [hyx]
          simp [List.lookup, e, hy]
      · have := hτ x t (by simp [List.lookup])
        simp [T.subst, this]
    | some u =>
      simp only [matchT, hl] at h
      split at h
      · rename_i hu
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨Ext.refl _, fun τ hτ => ?_⟩
        simp [T.subst, hτ x u hl, eq_of_beq hu]
      · simp at h
  | σ, .f n as, .f m bs, σ', h => by
    simp only [matchT] at h
    split at h
    · rename_i hn
      obtain ⟨h1, h2⟩ := matchArgs_sound σ as bs σ' h
      refine ⟨h1, fun τ hτ => ?_⟩
      simp [T.subst, h2 τ hτ, eq_of_beq hn]
    · simp at h
  | σ, .f _ _, .v _, σ', h => by simp [matchT] at h
theorem matchArgs_sound : ∀ (σ : Subst) (as bs : List T) (σ' : Subst), matchArgs σ as bs = some σ' →
    Ext σ σ' ∧ ∀ τ, Ext σ' τ → T.substArgs τ as = bs
  | σ, [], [], σ', h => by
    simp only [matchArgs, Option.some.injEq] at h
    subst h
    exact ⟨Ext.refl _, fun _ _ => by simp [T.substArgs]⟩
  | σ, a :: as, b :: bs, σ', h => by
    simp only [matchArgs, Option.bind_eq_some_iff] at h
    obtain ⟨σ₁, h1, h2⟩ := h
    obtain ⟨e1, s1⟩ := matchT_sound σ a b σ₁ h1
    obtain ⟨e2, s2⟩ := matchArgs_sound σ₁ as bs σ' h2
    refine ⟨e1.trans e2, fun τ hτ => ?_⟩
    simp [T.substArgs, s1 τ (e2.trans hτ), s2 τ hτ]
  | σ, [], _ :: _, σ', h => by simp [matchArgs] at h
  | σ, _ :: _, [], σ', h => by simp [matchArgs] at h
end

/-- A redex found at the root is an instance of a rule's left side. -/
theorem rootRedex_sound {S : System} {t : T} {ρ : Rule} {σ : Subst} (h : rootRedex S t = some (ρ, σ)) :
    ρ ∈ S.rules ∧ ρ.lhs.subst σ = t := by
  unfold rootRedex at h
  obtain ⟨ρ', hmem, hf⟩ := List.exists_of_findSome?_eq_some h
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hf
  obtain ⟨σ', hm, rfl, rfl⟩ := hf
  exact ⟨hmem, (matchT_sound _ _ _ _ hm).2 σ' (Ext.refl _)⟩

/-! ## Steps -/

mutual
/-- A step rewrites an instance of one of the system's rules, at the position it names. -/
theorem step_sound {S : System} : ∀ (t : T) {ρ : Rule} {p : Pos} {t' : T}, step S t = some (ρ, p, t') →
    ρ ∈ S.rules ∧ ∃ σ, t.at? p = some (ρ.lhs.subst σ) ∧ t' = t.replace p (ρ.rhs.subst σ)
  | .v x, ρ, p, t', h => by
    simp only [step, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨ρ', σ, hr, rfl, rfl, rfl⟩ := h
    obtain ⟨hm, hl⟩ := rootRedex_sound hr
    exact ⟨hm, σ, by simp [T.at?, hl], by simp [T.replace]⟩
  | .f n as, ρ, p, t', h => by
    simp only [step] at h
    split at h
    · rename_i ρ' σ hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hm, hl⟩ := rootRedex_sound hr
      exact ⟨hm, σ, by simp [T.at?, hl], by simp [T.replace]⟩
    · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨ρ', p', as', ha, rfl, rfl, rfl⟩ := h
      obtain ⟨hm, j, q, σ, rfl, hat, rfl⟩ := stepArgs_sound as 0 ha
      exact ⟨hm, σ, by simpa [T.at?] using hat, by simp [T.replace]⟩
/-- A step in the arguments, counted from `i`: at argument `i + j`. -/
theorem stepArgs_sound {S : System} : ∀ (as : List T) (i : Nat) {ρ : Rule} {p : Pos} {as' : List T},
    stepArgs S as i = some (ρ, p, as') →
    ρ ∈ S.rules ∧ ∃ j q σ, p = (i + j) :: q ∧ T.atArgs as j q = some (ρ.lhs.subst σ) ∧
      as' = T.replaceArgs as j q (ρ.rhs.subst σ)
  | [], i, ρ, p, as', h => by simp [stepArgs] at h
  | a :: as, i, ρ, p, as', h => by
    simp only [stepArgs] at h
    split at h
    · rename_i ρ' p' a' ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨hm, σ, hat, rfl⟩ := step_sound a ha
      exact ⟨hm, 0, p', σ, by simp, by simpa [T.atArgs] using hat, by simp [T.replaceArgs]⟩
    · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨ρ', p', as'', ha, rfl, rfl, rfl⟩ := h
      obtain ⟨hm, j, q, σ, rfl, hat, rfl⟩ := stepArgs_sound as (i + 1) ha
      exact ⟨hm, j + 1, q, σ, by simp; omega, by simpa [T.atArgs] using hat, by simp [T.replaceArgs]⟩
end

/-- A chain of steps from `t` to `u`. -/
inductive Chain (S : System) : T → List (Rule × Pos × T) → T → Prop where
  | nil (t : T) : Chain S t [] t
  | cons {t t' u : T} {ρ : Rule} {p : Pos} {l : List (Rule × Pos × T)} :
      step S t = some (ρ, p, t') → Chain S t' l u → Chain S t ((ρ, p, t') :: l) u

theorem Chain.snoc {S : System} {t u u' : T} {ρ : Rule} {p : Pos} :
    ∀ {l : List (Rule × Pos × T)}, Chain S t l u → step S u = some (ρ, p, u') → Chain S t (l ++ [(ρ, p, u')]) u'
  | _, .nil _, h => .cons h (.nil _)
  | _, .cons h₁ c, h => .cons h₁ (c.snoc h)

theorem normalize_go {S : System} (t₀ : T) :
    ∀ (n : Nat) (t : T) (acc : List (Rule × Pos × T)), Chain S t₀ acc.reverse t →
      Chain S t₀ (normalize.go S t n acc).1 (normalize.go S t n acc).2.1 ∧
      ((normalize.go S t n acc).2.2 = true → step S (normalize.go S t n acc).2.1 = none)
  | 0, t, acc, c => by simp [normalize.go, c]
  | n + 1, t, acc, c => by
    unfold normalize.go
    split
    · rename_i h; exact ⟨c, fun _ => h⟩
    · rename_i ρ p t' h
      have c' : Chain S t₀ ((ρ, p, t') :: acc).reverse t' := by simpa using c.snoc h
      split
      · exact ⟨c', by simp⟩
      · exact normalize_go t₀ n t' _ c'

/-- `rewrite` shows a chain of steps from the term to its answer. -/
theorem normalize_chain (S : System) (t : T) (fuel : Nat) :
    Chain S t (normalize S t fuel).1 (normalize S t fuel).2.1 :=
  (normalize_go t fuel t [] (.nil t)).1

/-- When `rewrite` says it reached a normal form, no rule applies anywhere in it. -/
theorem normalize_normal (S : System) (t : T) (fuel : Nat) (h : (normalize S t fuel).2.2 = true) :
    step S (normalize S t fuel).2.1 = none :=
  (normalize_go t fuel t [] (.nil t)).2 h

/-! ## Interpretations -/

mutual
/-- A term's value under an interpretation, with its variables given values by `ρ`. -/
def eval (I : String → Nat → Interp) (ρ : String → Nat) : T → Nat
  | .v x => ρ x
  | .f n as => (I n as.length).const + evalArgs I ρ (I n as.length).coeffs as
def evalArgs (I : String → Nat → Interp) (ρ : String → Nat) : List Nat → List T → Nat
  | c :: cs, a :: as => c * eval I ρ a + evalArgs I ρ cs as
  | _, _ => 0
end

/-- A linear form's value. -/
def Lin.eval (L : Lin) (ρ : String → Nat) : Nat := L.const + (L.coef.map fun p => p.2 * ρ p.1).sum

theorem Lin.eval_add (a b : Lin) (ρ : String → Nat) : (a.add b).eval ρ = a.eval ρ + b.eval ρ := by
  simp only [Lin.add, Lin.eval, List.map_append, List.sum_append]; omega

theorem sum_scale (k : Nat) (ρ : String → Nat) :
    ∀ l : List (String × Nat), ((l.map fun (x, c) => (x, k * c)).map fun p => p.2 * ρ p.1).sum =
      k * (l.map fun p => p.2 * ρ p.1).sum
  | [] => by simp
  | (x, c) :: l => by
    simp only [List.map_cons, List.sum_cons, sum_scale k ρ l, Nat.mul_add, Nat.mul_assoc]

theorem Lin.eval_scale (k : Nat) (a : Lin) (ρ : String → Nat) : (a.scale k).eval ρ = k * a.eval ρ := by
  simp only [Lin.scale, Lin.eval, sum_scale, Nat.mul_add]

mutual
/-- `lin` computes the value as a linear form. -/
theorem lin_eval (I : String → Nat → Interp) (ρ : String → Nat) : ∀ t : T, (lin I t).eval ρ = eval I ρ t
  | .v x => by simp [lin, eval, Lin.eval]
  | .f n as => by
    simp only [lin, eval, Lin.eval_add, linArgs_eval I ρ _ as]
    simp [Lin.eval]; omega
theorem linArgs_eval (I : String → Nat → Interp) (ρ : String → Nat) :
    ∀ (cs : List Nat) (as : List T), (linArgs I cs as).eval ρ = evalArgs I ρ cs as
  | c :: cs, a :: as => by
    simp only [linArgs, evalArgs, Lin.eval_add, Lin.eval_scale, lin_eval I ρ a, linArgs_eval I ρ cs as]
  | [], _ => by simp [linArgs, evalArgs, Lin.eval]
  | _ :: _, [] => by simp [linArgs, evalArgs, Lin.eval]
end

/-- The values a substitution gives its variables. -/
def Subst.env (I : String → Nat → Interp) (ρ : String → Nat) (σ : Subst) (x : String) : Nat :=
  match σ.lookup x with
  | some u => eval I ρ u
  | none => ρ x

theorem length_substArgs (σ : Subst) : ∀ as : List T, (T.substArgs σ as).length = as.length
  | [] => rfl
  | _ :: as => by simp [T.substArgs, length_substArgs σ as]

mutual
/-- The substitution lemma: the value of an instance is the value of the pattern, with each variable
worth what the substitution puts there. -/
theorem eval_subst (I : String → Nat → Interp) (ρ : String → Nat) (σ : Subst) :
    ∀ t : T, eval I ρ (t.subst σ) = eval I (σ.env I ρ) t
  | .v x => by
    simp only [T.subst, eval, Subst.env]
    cases σ.lookup x <;> simp [eval]
  | .f n as => by
    simp only [T.subst, eval, length_substArgs, evalArgs_subst I ρ σ _ as]
theorem evalArgs_subst (I : String → Nat → Interp) (ρ : String → Nat) (σ : Subst) :
    ∀ (cs : List Nat) (as : List T), evalArgs I ρ cs (T.substArgs σ as) = evalArgs I (σ.env I ρ) cs as
  | c :: cs, a :: as => by
    simp only [T.substArgs, evalArgs, eval_subst I ρ σ a, evalArgs_subst I ρ σ cs as]
  | [], _ => by simp [evalArgs]
  | _ :: _, [] => by simp [T.substArgs, evalArgs]
end

/-! ## The check -/

/-- The coefficient of `x` in a list of entries. -/
def getL (l : List (String × Nat)) (x : String) : Nat := ((l.filter (·.1 == x)).map (·.2)).sum

theorem getL_nil (x : String) : getL [] x = 0 := rfl

theorem getL_cons (y : String) (c : Nat) (l : List (String × Nat)) (x : String) :
    getL ((y, c) :: l) x = (if y = x then c else 0) + getL l x := by
  by_cases h : y = x <;> simp [getL, h]

theorem sum_map_add {α : Type} (f g : α → Nat) :
    ∀ K : List α, (K.map fun x => f x + g x).sum = (K.map f).sum + (K.map g).sum
  | [] => rfl
  | x :: K => by simp only [List.map_cons, List.sum_cons, sum_map_add f g K]; omega

theorem sum_map_le {α : Type} (f g : α → Nat) :
    ∀ K : List α, (∀ x ∈ K, f x ≤ g x) → (K.map f).sum ≤ (K.map g).sum
  | [], _ => by simp
  | x :: K, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (sum_map_le f g K fun y hy => h y (by simp [hy]))

theorem sum_single_absent (y : String) (c : Nat) (ρ : String → Nat) :
    ∀ K : List String, y ∉ K → (K.map fun x => (if y = x then c else 0) * ρ x).sum = 0
  | [], _ => rfl
  | z :: K, h => by
    have hyz : y ≠ z := fun e => h (by simp [e])
    simp only [List.map_cons, List.sum_cons, hyz, ite_false, Nat.zero_mul, Nat.zero_add]
    exact sum_single_absent y c ρ K (fun m => h (by simp [m]))

theorem sum_single (y : String) (c : Nat) (ρ : String → Nat) :
    ∀ K : List String, K.Nodup → y ∈ K → (K.map fun x => (if y = x then c else 0) * ρ x).sum = c * ρ y
  | [], _, h => by simp at h
  | z :: K, hK, h => by
    rw [List.nodup_cons] at hK
    simp only [List.map_cons, List.sum_cons]
    by_cases hyz : y = z
    · subst hyz
      simp [sum_single_absent y c ρ K hK.1]
    · have : y ∈ K := by simpa [hyz] using h
      simp [hyz, sum_single y c ρ K hK.2 this]

theorem sum_single_le (y : String) (c : Nat) (ρ : String → Nat) (K : List String) (hK : K.Nodup) :
    (K.map fun x => (if y = x then c else 0) * ρ x).sum ≤ c * ρ y := by
  by_cases h : y ∈ K
  · rw [sum_single y c ρ K hK h]; exact Nat.le_refl _
  · rw [sum_single_absent y c ρ K h]; exact Nat.zero_le _

theorem sum_zero : ∀ K : List String, (K.map fun _ => (0 : Nat)).sum = 0
  | [] => rfl
  | _ :: K => by simp [sum_zero K]

/-- Grouping the entries by variable, over a list of the variables (each once): the same sum when the
list has them all, no more otherwise. -/
theorem sum_group (ρ : String → Nat) (K : List String) (hK : K.Nodup) :
    ∀ l : List (String × Nat), (∀ p ∈ l, p.1 ∈ K) →
      (l.map fun p => p.2 * ρ p.1).sum = (K.map fun x => getL l x * ρ x).sum
  | [], _ => by simp [getL_nil, sum_zero]
  | (y, c) :: l, h => by
    simp only [getL_cons, Nat.add_mul]
    rw [sum_map_add, sum_single y c ρ K hK (h (y, c) (by simp)),
      ← sum_group ρ K hK l (fun p hp => h p (by simp [hp]))]
    simp

theorem sum_group_le (ρ : String → Nat) (K : List String) (hK : K.Nodup) :
    ∀ l : List (String × Nat), (K.map fun x => getL l x * ρ x).sum ≤ (l.map fun p => p.2 * ρ p.1).sum
  | [] => by simp [getL_nil, sum_zero]
  | (y, c) :: l => by
    simp only [getL_cons, Nat.add_mul]
    rw [sum_map_add]
    have := sum_single_le y c ρ K hK
    have := sum_group_le ρ K hK l
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The distinct names of a list, each once (only for the proofs). -/
def dedup : List String → List String
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup {y : String} : ∀ {l : List String}, y ∈ dedup l ↔ y ∈ l
  | [] => by simp [dedup]
  | x :: xs => by
    have ih := @mem_dedup y xs
    unfold dedup
    split
    · rename_i h
      by_cases e : y = x
      · subst e; simp [h]
      · simp [ih, e]
    · simp [ih]

theorem nodup_dedup : ∀ l : List String, (dedup l).Nodup
  | [] => by simp [dedup]
  | x :: xs => by
    unfold dedup
    split
    · exact nodup_dedup xs
    · rename_i h; exact List.nodup_cons.2 ⟨h, nodup_dedup xs⟩

/-- `decreases` is sound: when it holds, the first form is worth more than the second, whatever
the variables are worth. -/
theorem decreases_sound {l r : Lin} (h : decreases l r = true) (ρ : String → Nat) : r.eval ρ < l.eval ρ := by
  simp only [decreases, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hc, hk⟩ := h
  let K := dedup (r.coef.map (·.1))
  have hK : K.Nodup := nodup_dedup _
  have cover : ∀ p ∈ r.coef, p.1 ∈ K := fun p hp => mem_dedup.2 (List.mem_map_of_mem hp)
  have pw : ∀ x ∈ K, getL r.coef x * ρ x ≤ getL l.coef x * ρ x := by
    intro x hx
    have hx' : x ∈ r.keys := by simpa [Lin.keys, List.mem_eraseDups] using mem_dedup.1 hx
    exact Nat.mul_le_mul_right _ (hk x hx')
  have e := sum_group ρ K hK r.coef cover
  have le := sum_map_le _ _ K pw
  have le2 := sum_group_le ρ K hK l.coef
  unfold Lin.eval
  omega

theorem sum_zero_env : ∀ l : List (String × Nat), (l.map fun p => p.2 * (fun _ => 0) p.1).sum = 0
  | [] => rfl
  | _ :: l => by simpa using sum_zero_env l

theorem sum_point (x : String) (N : Nat) : ∀ l : List (String × Nat),
    (l.map fun p => p.2 * (fun y => if y = x then N else 0) p.1).sum = getL l x * N
  | [] => by simp [getL_nil]
  | (y, c) :: l => by
    simp only [List.map_cons, List.sum_cons, sum_point x N l, getL_cons, Nat.add_mul]
    by_cases h : y = x <;> simp [h]

/-- And it is exact: when it fails, some values of the variables make the first form worth no more
than the second (all zero, or one variable large). -/
theorem decreases_complete {l r : Lin} (h : decreases l r = false) : ∃ ρ, l.eval ρ ≤ r.eval ρ := by
  simp only [decreases, Bool.and_eq_false_iff, decide_eq_false_iff_not, List.all_eq_false,
    Nat.not_lt] at h
  rcases h with hc | ⟨x, _, hx⟩
  · exact ⟨fun _ => 0, by simp only [Lin.eval, sum_zero_env]; omega⟩
  · refine ⟨fun y => if y = x then l.const + 1 else 0, ?_⟩
    simp only [Lin.eval, sum_point]
    have e1 : Lin.get l x = getL l.coef x := rfl
    have e2 : Lin.get r x = getL r.coef x := rfl
    rw [e1, e2] at hx
    have hx : getL l.coef x + 1 ≤ getL r.coef x := by simp at hx; omega
    have := Nat.mul_le_mul_right (l.const + 1) hx
    rw [Nat.succ_mul] at this
    omega

/-! ## Termination -/

/-- An interpretation fit for the check: a coefficient of at least one for every argument. -/
def Good (I : String → Nat → Interp) : Prop :=
  ∀ f n, (I f n).coeffs.length = n ∧ ∀ c ∈ (I f n).coeffs, 1 ≤ c

theorem sizeInterp_good (n : Nat) : (sizeInterp n).coeffs.length = n ∧ ∀ c ∈ (sizeInterp n).coeffs, 1 ≤ c := by
  simp [sizeInterp, List.mem_replicate]

/-- The interpretations `terminates` uses are fit for it. -/
theorem interpOf_good (given : List (String × Interp)) : Good (interpOf given) := by
  intro f n
  unfold interpOf
  split
  · split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, h.2⟩
    · exact sizeInterp_good n
  · exact sizeInterp_good n

section
variable {I : String → Nat → Interp} {S : System}

/-- Every rule's left side is worth more than its right side, under every assignment. -/
theorem rule_decreases (hS : ∀ r ∈ S.rules, decreases (lin I r.lhs) (lin I r.rhs) = true)
    {r : Rule} (hr : r ∈ S.rules) (ρ : String → Nat) : eval I ρ r.rhs < eval I ρ r.lhs := by
  have := decreases_sound (hS r hr) ρ
  rwa [lin_eval, lin_eval] at this

/-- And a rule that fails the check has an instance whose left side is worth no more than its right. -/
theorem rule_not_decreases {r : Rule} (h : decreases (lin I r.lhs) (lin I r.rhs) = false) :
    ∃ ρ, eval I ρ r.lhs ≤ eval I ρ r.rhs := by
  obtain ⟨ρ, hρ⟩ := decreases_complete h
  exact ⟨ρ, by rwa [lin_eval, lin_eval] at hρ⟩

theorem root_decreases (hS : ∀ r ∈ S.rules, decreases (lin I r.lhs) (lin I r.rhs) = true)
    {t : T} {r : Rule} {σ : Subst} (h : rootRedex S t = some (r, σ)) (ρ : String → Nat) :
    eval I ρ (r.rhs.subst σ) < eval I ρ t := by
  obtain ⟨hm, hl⟩ := rootRedex_sound h
  rw [← hl, eval_subst, eval_subst]
  exact rule_decreases hS hm _

mutual
/-- Every step lowers the term's value: the rule's instance is worth less, and every coefficient is
at least one, so the term around it is worth less too. -/
theorem step_decreases (hI : Good I) (hS : ∀ r ∈ S.rules, decreases (lin I r.lhs) (lin I r.rhs) = true) :
    ∀ (t : T) {r : Rule} {p : Pos} {t' : T}, step S t = some (r, p, t') → ∀ ρ, eval I ρ t' < eval I ρ t
  | .v x, r, p, t', h, ρ => by
    simp only [step, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨r', σ, hr, rfl, rfl, rfl⟩ := h
    exact root_decreases hS hr ρ
  | .f n as, r, p, t', h, ρ => by
    simp only [step] at h
    split at h
    · rename_i r' σ hr
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact root_decreases hS hr ρ
    · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨r', p', as', ha, rfl, rfl, rfl⟩ := h
      obtain ⟨hlen, hlt⟩ := stepArgs_decreases hI hS as 0 ha
      simp only [eval, hlen]
      have := hlt _ (hI n as.length).1 (hI n as.length).2 ρ
      omega
theorem stepArgs_decreases (hI : Good I) (hS : ∀ r ∈ S.rules, decreases (lin I r.lhs) (lin I r.rhs) = true) :
    ∀ (as : List T) (i : Nat) {r : Rule} {p : Pos} {as' : List T}, stepArgs S as i = some (r, p, as') →
      as'.length = as.length ∧ ∀ cs : List Nat, cs.length = as.length → (∀ c ∈ cs, 1 ≤ c) →
        ∀ ρ, evalArgs I ρ cs as' < evalArgs I ρ cs as
  | [], i, r, p, as', h => by simp [stepArgs] at h
  | a :: as, i, r, p, as', h => by
    simp only [stepArgs] at h
    split at h
    · rename_i r' p' a' ha
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨rfl, fun cs hl hc ρ => ?_⟩
      match cs, hl with
      | c :: cs, _ =>
        simp only [evalArgs]
        have h1 := step_decreases hI hS a ha ρ
        have h2 : 1 ≤ c := hc c (by simp)
        have : c * eval I ρ a' < c * eval I ρ a := Nat.mul_lt_mul_of_pos_left h1 h2
        omega
    · simp only [Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
      obtain ⟨r', p', as'', ha, rfl, rfl, rfl⟩ := h
      obtain ⟨hlen, hlt⟩ := stepArgs_decreases hI hS as (i + 1) ha
      refine ⟨by simp [hlen], fun cs hl hc ρ => ?_⟩
      match cs, hl with
      | c :: cs, hl =>
        simp only [evalArgs]
        have := hlt cs (by simpa using hl) (fun d hd => hc d (by simp [hd])) ρ
        omega
end

/-- When `terminates` says so, no term rewrites for ever: every step lowers a natural number, the
term's value with every variable worth zero. -/
theorem no_infinite_rewriting (hI : Good I)
    (hS : ∀ r ∈ S.rules, decreases (lin I r.lhs) (lin I r.rhs) = true) :
    ¬ ∃ f : Nat → T, ∀ k, ∃ r p, step S (f k) = some (r, p, f (k + 1)) := by
  rintro ⟨f, hf⟩
  have bound : ∀ k, eval I (fun _ => 0) (f k) + k ≤ eval I (fun _ => 0) (f 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨r, p, h⟩ := hf k
      have := step_decreases hI hS (f k) h (fun _ => 0)
      omega
  have := bound (eval I (fun _ => 0) (f 0) + 1)
  omega

end

end TRS
end MathEngine
