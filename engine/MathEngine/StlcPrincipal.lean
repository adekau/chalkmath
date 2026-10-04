import MathEngine.StlcProofs
/-!
# Inference finds the most general type

`infer:` (`Stlc.lean`) gives every unannotated binder, every application's result and every free
variable a type variable, collects an equation per application (`gen`), and solves the equations by
unification (`unify`). `StlcProofs.lean` proves the answer is a type of the term. This file proves it
is the most general one (Hindley's theorem, for the simply typed calculus): every way of typing the
term, whatever types its unannotated binders and its free variables are given, gives an instance of
the solved type, before its variables are named.

- `unify_most_general`: any substitution that solves the equations factors through the one
  unification found (`Agree`: applying the found one first changes nothing).
- `gen_complete`: any typing of the term gives a substitution that solves the equations and maps
  the generated type to the typing's type.
- `infer_principal`: together.
-/
namespace MathEngine
namespace Lam

/-- A substitution as a function on type variables. -/
def Ty.subst (θ : Nat → Ty) : Ty → Ty
  | .tvar n => θ n
  | .arrow a b => .arrow (a.subst θ) (b.subst θ)
  | .base s => .base s

/-- `σ`'s lookup as a function. -/
def TSubst.fn (σ : TSubst) (n : Nat) : Ty := (σ.lookup n).getD (.tvar n)

theorem Ty.apply_eq_subst (σ : TSubst) : ∀ T : Ty, T.apply σ = T.subst σ.fn
  | .tvar n => by simp [Ty.apply, Ty.subst, TSubst.fn]
  | .arrow a b => by simp [Ty.apply, Ty.subst, Ty.apply_eq_subst σ a, Ty.apply_eq_subst σ b]
  | .base s => by simp [Ty.apply, Ty.subst]

theorem Ty.subst_id : ∀ T : Ty, T.subst .tvar = T
  | .tvar _ => rfl
  | .arrow a b => by simp [Ty.subst, Ty.subst_id a, Ty.subst_id b]
  | .base _ => rfl

/-! ## Unification is most general -/

/-- `θ` agrees with `σ`: applying `σ` first changes nothing that `θ` does. -/
def Agree (σ : TSubst) (θ : Nat → Ty) : Prop := ∀ T : Ty, (T.apply σ).subst θ = T.subst θ

/-- It is enough to check the variables. -/
theorem agree_of_vars {σ : TSubst} {θ : Nat → Ty} (h : ∀ n, (σ.fn n).subst θ = θ n) : Agree σ θ := by
  intro T
  rw [Ty.apply_eq_subst]
  induction T with
  | tvar n => exact h n
  | arrow a b iha ihb => simp [Ty.subst, iha, ihb]
  | base _ => rfl

theorem agree_nil (θ : Nat → Ty) : Agree [] θ := agree_of_vars fun n => by simp [TSubst.fn, Ty.subst]

/-- Binding `n` to `u` keeps the agreement, when `θ` already makes them equal. -/
theorem agree_bind {σ : TSubst} {θ : Nat → Ty} {n : Nat} {u : Ty} (hσ : Agree σ θ) (hn : θ n = u.subst θ) :
    Agree ((n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)])) θ := by
  have h1 : Agree [(n, u)] θ := agree_of_vars fun m => by
    by_cases hm : m = n
    · subst hm; simp [TSubst.fn, List.lookup, hn]
    · have : (m == n) = false := by simp [hm]
      simp [TSubst.fn, List.lookup, this, Ty.subst]
  refine agree_of_vars fun m => ?_
  by_cases hm : m = n
  · subst hm; simp [TSubst.fn, List.lookup, hn]
  · have e : (m == n) = false := by simp [hm]
    have hl : List.lookup m (σ.map fun (m, v) => (m, v.apply [(n, u)])) = (σ.lookup m).map (·.apply [(n, u)]) := by
      clear e hm h1 hσ hn
      induction σ with
      | nil => rfl
      | cons p σ ih =>
        obtain ⟨k, v⟩ := p
        by_cases hk : m = k
        · subst hk; simp [List.lookup]
        · have : (m == k) = false := by simp [hk]
          simp [List.lookup, this, ih]
    have hv := hσ (.tvar m)
    simp only [Ty.apply_eq_subst, Ty.subst] at hv
    cases hσm : σ.lookup m with
    | none => simp [TSubst.fn, List.lookup, e, hl, hσm, Ty.subst]
    | some v =>
      simp only [TSubst.fn, List.lookup, e, hl, hσm, Option.map_some, Option.getD_some]
      rw [h1 v]
      simpa [TSubst.fn, hσm] using hv

theorem unify_go_most_general :
    ∀ (fuel : Nat) (eqs : List (Ty × Ty)) (σ : TSubst) (acc : Array (UStep × TSubst)) (σ' : TSubst)
      (acc' : Array (UStep × TSubst)) (θ : Nat → Ty),
      unify.go eqs σ acc fuel = .ok (σ', acc') → Agree σ θ →
      (∀ e ∈ eqs, e.1.subst θ = e.2.subst θ) → Agree σ' θ
  | fuel, [], σ, acc, σ', acc', θ, h, hσ, _ => by
    cases fuel <;> simp [unify.go] at h <;> (obtain ⟨rfl, -⟩ := h; exact hσ)
  | 0, _ :: _, σ, acc, σ', acc', θ, h, _, _ => by simp [unify.go] at h
  | fuel + 1, (s, t) :: rest, σ, acc, σ', acc', θ, h, hσ, he => by
    have hst : (s.apply σ).subst θ = (t.apply σ).subst θ := by
      rw [hσ, hσ]; exact he (s, t) (by simp)
    have hrest : ∀ e ∈ rest, e.1.subst θ = e.2.subst θ := fun e m => he e (by simp [m])
    simp only [unify.go] at h
    split at h
    · exact unify_go_most_general fuel rest σ acc σ' acc' θ h hσ hrest
    · split at h
      · rename_i _ _ n hs
        split at h
        · simp at h
        · rw [hs] at hst
          exact unify_go_most_general fuel rest _ _ σ' acc' θ h (agree_bind hσ hst) hrest
      · rename_i _ _ n ht _
        split at h
        · simp at h
        · rw [ht] at hst
          exact unify_go_most_general fuel rest _ _ σ' acc' θ h (agree_bind hσ hst.symm) hrest
      · rename_i _ _ a b c d hs ht
        rw [hs, ht] at hst
        simp only [Ty.subst, Ty.arrow.injEq] at hst
        refine unify_go_most_general fuel _ σ _ σ' acc' θ h hσ ?_
        intro e m
        simp only [List.mem_cons] at m
        rcases m with rfl | rfl | m
        · exact hst.1
        · exact hst.2
        · exact hrest e m
      · simp at h

/-- Unification is most general: a substitution that solves the equations agrees with the one
found, so every solution is an instance of it. -/
theorem unify_most_general {eqs : List (Ty × Ty)} {σ : TSubst} {moves : Array (UStep × TSubst)}
    (h : unify eqs = .ok (σ, moves)) (θ : Nat → Ty) (hθ : ∀ e ∈ eqs, e.1.subst θ = e.2.subst θ) :
    Agree σ θ :=
  unify_go_most_general _ eqs [] #[] σ moves θ h (agree_nil θ) hθ

/-! ## Unification is sound -/

theorem Ty.subst_congr {θ θ' : Nat → Ty} : ∀ {T : Ty}, (∀ k, T.occurs k = true → θ k = θ' k) → T.subst θ = T.subst θ'
  | .tvar n, h => by simp only [Ty.subst]; exact h n (by simp [Ty.occurs])
  | .arrow a b, h => by
    simp only [Ty.subst]
    rw [Ty.subst_congr (T := a) fun k hk => h k (by simp [Ty.occurs, hk]),
      Ty.subst_congr (T := b) fun k hk => h k (by simp [Ty.occurs, hk])]
  | .base _, _ => rfl

/-- A variable of `T.subst θ` comes from a variable of `T`. -/
theorem Ty.occurs_subst {θ : Nat → Ty} {k : Nat} : ∀ {T : Ty}, (T.subst θ).occurs k = true →
    ∃ j, T.occurs j = true ∧ (θ j).occurs k = true
  | .tvar n, h => ⟨n, by simp [Ty.occurs], h⟩
  | .arrow a b, h => by
    simp only [Ty.subst, Ty.occurs, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨j, hj, hk⟩ := Ty.occurs_subst h; exact ⟨j, by simp [Ty.occurs, hj], hk⟩
    · obtain ⟨j, hj, hk⟩ := Ty.occurs_subst h; exact ⟨j, by simp [Ty.occurs, hj], hk⟩
  | .base _, h => by simp [Ty.subst, Ty.occurs] at h

/-- No variable `σ` binds survives applying `σ`: a substitution in solved form. -/
def Solved (σ : TSubst) : Prop := ∀ m k, (σ.lookup k).isSome = true → (σ.fn m).occurs k = false

theorem solved_nil : Solved [] := fun _ _ h => by simp [List.lookup] at h

theorem solved_apply {σ : TSubst} (hσ : Solved σ) {k : Nat} (hk : (σ.lookup k).isSome = true) (T : Ty) :
    (T.apply σ).occurs k = false := by
  rw [Ty.apply_eq_subst]
  cases h : (T.subst σ.fn).occurs k with
  | false => rfl
  | true => obtain ⟨j, -, hj⟩ := Ty.occurs_subst h; rw [hσ j k hk] at hj; cases hj

/-- A solved substitution is idempotent. -/
theorem agree_self {σ : TSubst} (hσ : Solved σ) : Agree σ σ.fn := by
  refine agree_of_vars fun m => ?_
  conv => rhs; rw [← Ty.subst_id (σ.fn m)]
  refine Ty.subst_congr fun k hk => ?_
  cases hl : σ.lookup k with
  | none => simp [TSubst.fn, hl]
  | some v => have := hσ m k (by simp [hl]); rw [hk] at this; cases this

theorem lookup_bind (σ : TSubst) (n : Nat) (u : Ty) (m : Nat) :
    List.lookup m (σ.map fun (m, v) => (m, v.apply [(n, u)])) = (σ.lookup m).map (·.apply [(n, u)]) := by
  induction σ with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : m = k
    · subst hk; simp [List.lookup]
    · have : (m == k) = false := by simp [hk]
      simp [List.lookup, this, ih]

theorem fn_bind {σ : TSubst} {n : Nat} {u : Ty} (hn : (σ.lookup n).isSome = false) (m : Nat) :
    TSubst.fn ((n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)])) m =
      if m = n then u else (σ.fn m).apply [(n, u)] := by
  by_cases hm : m = n
  · subst hm; simp [TSubst.fn, List.lookup]
  · have e : (m == n) = false := by simp [hm]
    simp only [TSubst.fn, List.lookup, e, lookup_bind, hm, if_false]
    cases hl : σ.lookup m with
    | none => simp [Ty.apply, List.lookup, e]
    | some v => simp

theorem bind_isSome {σ : TSubst} {n : Nat} {u : Ty} {k : Nat}
    (h : (List.lookup k ((n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)]))).isSome = true) :
    k = n ∨ (σ.lookup k).isSome = true := by
  by_cases hk : k = n
  · exact .inl hk
  · have e : (k == n) = false := by simp [hk]
    simp only [List.lookup, e, lookup_bind, Option.isSome_map] at h
    exact .inr h

/-- Binding `n` to `u` keeps the substitution solved, when `u` is already `σ`-applied and does not
contain `n` (the occurs check). -/
theorem solved_bind {σ : TSubst} (hσ : Solved σ) {n : Nat} {u t : Ty} (hu : u = t.apply σ)
    (hocc : u.occurs n = false) (hn : (σ.lookup n).isSome = false) :
    Solved ((n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)])) := by
  have hu' : ∀ k, (k = n ∨ (σ.lookup k).isSome = true) → u.occurs k = false := by
    intro k hk
    rcases hk with rfl | hk
    · exact hocc
    · rw [hu]; exact solved_apply hσ hk t
  intro m k hk
  have hk := bind_isSome hk
  rw [fn_bind hn]
  split
  · exact hu' k hk
  · rename_i hm
    cases h : ((σ.fn m).apply [(n, u)]).occurs k with
    | false => rfl
    | true =>
      rw [Ty.apply_eq_subst] at h
      obtain ⟨j, hj, hjk⟩ := Ty.occurs_subst h
      by_cases hjn : j = n
      · subst hjn
        simp [TSubst.fn, List.lookup] at hjk
        rw [hu' k hk] at hjk; cases hjk
      · have e : (j == n) = false := by simp [hjn]
        simp [TSubst.fn, List.lookup, e, Ty.occurs] at hjk
        subst hjk
        rcases hk with rfl | hk
        · exact absurd rfl hjn
        · rw [hσ m j hk] at hj; cases hj

/-- After binding, applying `σ` first changes nothing the new substitution does. -/
theorem agree_bound {σ : TSubst} (hσ : Solved σ) {n : Nat} {u : Ty} (hn : (σ.lookup n).isSome = false) :
    Agree σ (TSubst.fn ((n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)]))) := by
  refine agree_of_vars fun m => ?_
  cases hl : σ.lookup m with
  | none =>
    have : σ.fn m = .tvar m := by simp [TSubst.fn, hl]
    rw [this]; rfl
  | some v =>
    have hmn : m ≠ n := by intro h; subst h; simp [hl] at hn
    rw [fn_bind hn m, if_neg hmn, Ty.apply_eq_subst]
    refine Ty.subst_congr fun k hk => ?_
    have hkσ : (σ.lookup k).isSome = false := by
      cases h : (σ.lookup k).isSome with
      | false => rfl
      | true => rw [hσ m k h] at hk; cases hk
    rw [fn_bind hn k]
    by_cases hkn : k = n
    · subst hkn; simp [TSubst.fn, List.lookup]
    · have e : (k == n) = false := by simp [hkn]
      have hk0 : σ.lookup k = none := by cases h : σ.lookup k <;> simp_all
      simp [hkn, hk0, Ty.apply, TSubst.fn, List.lookup, e]

theorem unify_go_sound :
    ∀ (fuel : Nat) (eqs : List (Ty × Ty)) (σ : TSubst) (acc : Array (UStep × TSubst)) (σ' : TSubst)
      (acc' : Array (UStep × TSubst)),
      unify.go eqs σ acc fuel = .ok (σ', acc') → Solved σ →
      Agree σ σ'.fn ∧ ∀ e ∈ eqs, e.1.subst σ'.fn = e.2.subst σ'.fn
  | fuel, [], σ, acc, σ', acc', h, hσ => by
    cases fuel <;> simp [unify.go] at h <;> (obtain ⟨rfl, -⟩ := h; exact ⟨agree_self hσ, by simp⟩)
  | 0, _ :: _, σ, acc, σ', acc', h, _ => by simp [unify.go] at h
  | fuel + 1, (s, t) :: rest, σ, acc, σ', acc', h, hσ => by
    simp only [unify.go] at h
    -- the equation holds once both sides agree after `σ`
    have close : Agree σ σ'.fn → (s.apply σ).subst σ'.fn = (t.apply σ).subst σ'.fn →
        s.subst σ'.fn = t.subst σ'.fn := fun ha he => by rw [← ha s, he, ha t]
    split at h
    · rename_i heq
      obtain ⟨ha, hr⟩ := unify_go_sound fuel rest σ acc σ' acc' h hσ
      refine ⟨ha, ?_⟩
      intro e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact close ha (by rw [heq])
      · exact hr e he
    · -- a variable on either side takes the other side's type
      have bindCase : ∀ (n : Nat) (u : Ty) (σ₁ : TSubst), s.apply σ = .tvar n ∨ t.apply σ = .tvar n →
          (u = t.apply σ ∨ u = s.apply σ) → (s.apply σ = .tvar n → u = t.apply σ) →
          (t.apply σ = .tvar n → u = s.apply σ) → u.occurs n = false →
          σ₁ = ((n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)])) →
          unify.go rest σ₁ (acc.push (.bind n u, σ₁)) fuel = .ok (σ', acc') →
          Agree σ σ'.fn ∧ ∀ e ∈ (s, t) :: rest, e.1.subst σ'.fn = e.2.subst σ'.fn := by
        intro n u σ₁ hvar hu hs ht hocc hσ₁ hgo
        have hn : (σ.lookup n).isSome = false := by
          cases h : (σ.lookup n).isSome with
          | false => rfl
          | true =>
            rcases hvar with hv | hv
            · have := solved_apply hσ h s; rw [hv] at this; simp [Ty.occurs] at this
            · have := solved_apply hσ h t; rw [hv] at this; simp [Ty.occurs] at this
        have hsol : Solved σ₁ := by
          rw [hσ₁]
          rcases hu with hu | hu
          · exact solved_bind hσ hu hocc hn
          · exact solved_bind hσ hu hocc hn
        obtain ⟨ha₁, hr⟩ := unify_go_sound fuel rest σ₁ _ σ' acc' hgo hsol
        have hb := agree_bound (u := u) hσ hn
        rw [← hσ₁] at hb
        have ha : Agree σ σ'.fn := fun T => by
          have h1 := ha₁ (T.apply σ)
          have h2 := ha₁ T
          rw [Ty.apply_eq_subst σ₁ (T.apply σ), hb T] at h1
          rw [Ty.apply_eq_subst σ₁ T] at h2
          rw [← h1, h2]
        -- `n` and `u` agree under the final substitution
        have hnu : (Ty.tvar n).subst σ'.fn = u.subst σ'.fn := by
          rw [← ha₁ (.tvar n), ← ha₁ u, hσ₁]
          have hu₁ : u.apply ((n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)])) = u := by
            rw [Ty.apply_eq_subst, ← hσ₁]
            conv => rhs; rw [← Ty.subst_id u]
            refine Ty.subst_congr fun k hk => ?_
            have hkσ : (σ.lookup k).isSome = false := by
              cases h : (σ.lookup k).isSome with
              | false => rfl
              | true =>
                rcases hu with hu | hu <;> (rw [hu] at hk; rw [solved_apply hσ h] at hk; cases hk)
            have hkn : k ≠ n := by intro e; subst e; rw [hocc] at hk; cases hk
            rw [hσ₁, fn_bind hn, if_neg hkn]
            have : σ.fn k = .tvar k := by
              simp only [TSubst.fn]; cases h : σ.lookup k <;> simp_all
            have e : (k == n) = false := by simp [hkn]
            simp [this, Ty.apply, List.lookup, e]
          simp only [Ty.apply, List.lookup, BEq.rfl, Option.getD_some, hu₁]
        refine ⟨ha, ?_⟩
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · apply close ha
          rcases hvar with hv | hv
          · rw [hv, hnu, hs hv]
          · rw [hv, hnu, ht hv]
        · exact hr e he
      split at h
      · rename_i _ _ n hs
        split at h
        · simp at h
        · rename_i hocc
          exact bindCase n _ _ (.inl hs) (.inl rfl) (fun _ => rfl)
            (fun ht => by rw [hs] at *; simp_all) (by simpa using hocc) rfl h
      · rename_i _ _ n ht hns
        split at h
        · simp at h
        · rename_i hocc
          exact bindCase n _ _ (.inr ht) (.inr rfl)
            (fun hs => absurd hs (hns n)) (fun _ => rfl) (by simpa using hocc) rfl h
      · rename_i _ _ a b c d hs ht
        obtain ⟨ha, hr⟩ := unify_go_sound fuel _ σ _ σ' acc' h hσ
        refine ⟨ha, ?_⟩
        intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · apply close ha
          rw [hs, ht]
          simp only [Ty.subst]
          rw [hr (a, c) (by simp), hr (b, d) (by simp)]
        · exact hr e (by simp [he])
      · simp at h

/-- **Unification is sound**: the substitution found solves every equation. With
`unify_most_general`, it is a most general unifier. -/
theorem unify_sound {eqs : List (Ty × Ty)} {σ : TSubst} {moves : Array (UStep × TSubst)}
    (h : unify eqs = .ok (σ, moves)) : ∀ e ∈ eqs, e.1.apply σ = e.2.apply σ := by
  intro e he
  rw [Ty.apply_eq_subst, Ty.apply_eq_subst]
  exact (unify_go_sound _ eqs [] #[] σ moves h solved_nil).2 e he

/-! ## Generation is complete -/

/-- Every type variable in `T` is below `k`. -/
def Ty.Below (k : Nat) : Ty → Prop
  | .tvar n => n < k
  | .arrow a b => a.Below k ∧ b.Below k
  | .base _ => True

theorem Ty.Below.mono {k k' : Nat} (hk : k ≤ k') : ∀ {T : Ty}, T.Below k → T.Below k'
  | .tvar _, h => Nat.lt_of_lt_of_le h hk
  | .arrow _ _, ⟨ha, hb⟩ => ⟨Ty.Below.mono hk ha, Ty.Below.mono hk hb⟩
  | .base _, _ => trivial

/-- Two substitutions that agree below `k` agree on a type below `k`. -/
theorem Ty.subst_below {k : Nat} {θ θ' : Nat → Ty} (h : ∀ n < k, θ' n = θ n) :
    ∀ {T : Ty}, T.Below k → T.subst θ' = T.subst θ
  | .tvar n, hT => h n hT
  | .arrow _ _, ⟨ha, hb⟩ => by simp [Ty.subst, Ty.subst_below h ha, Ty.subst_below h hb]
  | .base _, _ => rfl

/-- A type with no type variables: what the reader writes. -/
theorem Ty.subst_closed (θ : Nat → Ty) {T : Ty} (h : T.Below 0) : T.subst θ = T := by
  rw [Ty.subst_below (θ' := θ) (θ := .tvar) (fun n hn => absurd hn (Nat.not_lt_zero n)) h, Ty.subst_id]

/-- Every type written in the term has no type variables. -/
def ATerm.Closed : ATerm → Prop
  | .var _ => True
  | .lam _ (some A) e => A.Below 0 ∧ e.Closed
  | .lam _ none e => e.Closed
  | .app f a => f.Closed ∧ a.Closed

/-- `t'` is `t` with a type on every binder: the ones written, and any for the others. -/
inductive Fills : ATerm → ATerm → Prop where
  | var (x : String) : Fills (.var x) (.var x)
  | lamSome (x : String) (A : Ty) {e' e : ATerm} : Fills e' e → Fills (.lam x (some A) e') (.lam x (some A) e)
  | lamNone (x : String) (A : Ty) {e' e : ATerm} : Fills e' e → Fills (.lam x (some A) e') (.lam x none e)
  | app {f' f a' a : ATerm} : Fills f' f → Fills a' a → Fills (.app f' a') (.app f a)

/-- What generation keeps true of its state: the context, the free variables' types and the
equations use only type variables already made. -/
structure Inv (Γ : Ctx) (g : Gen) : Prop where
  ctx : ∀ x A, Γ.lookup x = some A → A.Below g.next
  frees : ∀ x A, g.frees.lookup x = some A → A.Below g.next
  eqs : ∀ e ∈ g.eqs, e.1.Below g.next ∧ e.2.Below g.next

theorem Inv.mono {Γ : Ctx} {g : Gen} {k : Nat} (h : Inv Γ g) (hk : g.next ≤ k) :
    (∀ x A, Γ.lookup x = some A → A.Below k) ∧ (∀ x A, g.frees.lookup x = some A → A.Below k) ∧
      (∀ e ∈ g.eqs, e.1.Below k ∧ e.2.Below k) :=
  ⟨fun x A hx => (h.ctx x A hx).mono hk, fun x A hx => (h.frees x A hx).mono hk,
    fun e he => ⟨(h.eqs e he).1.mono hk, (h.eqs e he).2.mono hk⟩⟩

theorem lookup_append_eq (l₁ l₂ : Ctx) (x : String) :
    (l₁ ++ l₂).lookup x = match l₁.lookup x with | some A => some A | none => l₂.lookup x := by
  induction l₁ with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨y, B⟩ := p
    by_cases h : x = y
    · subst h; simp [List.lookup]
    · have : (x == y) = false := by simp [h]
      simp [List.lookup, this, ih]

theorem lookup_cons_ne {x y : String} {A : Ty} {Γ : Ctx} (h : y ≠ x) : ((x, A) :: Γ).lookup y = Γ.lookup y := by
  have : (y == x) = false := by simp [h]
  simp [List.lookup, this]

/-- Generation only makes new type variables, and uses only the ones it has made. -/
theorem gen_wf : ∀ (t : ATerm) (Γ : Ctx) (g : Gen), Inv Γ g → t.Closed →
    g.next ≤ (gen Γ t g).2.next ∧ Inv Γ (gen Γ t g).2 ∧ (gen Γ t g).1.2.Below (gen Γ t g).2.next
  | .var x, Γ, g, hI, _ => by
    unfold gen
    split
    · rename_i T hT; exact ⟨Nat.le_refl _, hI, hI.ctx x T hT⟩
    · split
      · rename_i T hT; exact ⟨Nat.le_refl _, hI, hI.frees x T hT⟩
      · rename_i hT
        have m := hI.mono (Nat.le_succ g.next)
        refine ⟨Nat.le_succ _, ⟨m.1, fun y A hy => ?_, m.2.2⟩, Nat.lt_succ_self _⟩
        rw [lookup_append_eq] at hy
        split at hy
        · rename_i B hB; cases hy; exact m.2.1 y _ hB
        · by_cases hyx : y = x
          · subst hyx; simp [List.lookup] at hy; subst hy; exact Nat.lt_succ_self _
          · rw [lookup_cons_ne (Ne.symm (Ne.symm hyx))] at hy; simp [List.lookup] at hy
  | .lam x (some A) e, Γ, g, hI, ⟨hA, he⟩ => by
    have hI' : Inv ((x, A) :: Γ) g := ⟨fun y B hy => by
      by_cases hyx : y = x
      · subst hyx; simp [List.lookup] at hy; subst hy; exact hA.mono (Nat.zero_le _)
      · rw [lookup_cons_ne hyx] at hy; exact hI.ctx y B hy, hI.frees, hI.eqs⟩
    obtain ⟨h1, h2, h3⟩ := gen_wf e ((x, A) :: Γ) g hI' he
    refine ⟨h1, ⟨fun y B hy => (hI.ctx y B hy).mono h1, h2.frees, h2.eqs⟩, ⟨hA.mono (Nat.zero_le _), h3⟩⟩
  | .lam x none e, Γ, g, hI, he => by
    have m := hI.mono (Nat.le_succ g.next)
    have hI' : Inv ((x, .tvar g.next) :: Γ) { g with next := g.next + 1 } := ⟨fun y B hy => by
      by_cases hyx : y = x
      · subst hyx; simp [List.lookup] at hy; subst hy; exact Nat.lt_succ_self _
      · rw [lookup_cons_ne hyx] at hy; exact m.1 y B hy, m.2.1, m.2.2⟩
    obtain ⟨h1, h2, h3⟩ := gen_wf e _ _ hI' he
    have h1' : g.next + 1 ≤ _ := h1
    refine ⟨Nat.le_of_succ_le h1', ⟨fun y B hy => (hI.ctx y B hy).mono (Nat.le_of_succ_le h1'), h2.frees, h2.eqs⟩,
      ⟨Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h1', h3⟩⟩
  | .app f a, Γ, g, hI, ⟨hf, ha⟩ => by
    obtain ⟨f1, f2, f3⟩ := gen_wf f Γ g hI hf
    obtain ⟨a1, a2, a3⟩ := gen_wf a Γ _ f2 ha
    have m := a2.mono (Nat.le_succ (gen Γ a (gen Γ f g).2).2.next)
    refine ⟨Nat.le_trans f1 (Nat.le_trans a1 (Nat.le_succ _)), ⟨m.1, m.2.1, fun e he => ?_⟩, Nat.lt_succ_self _⟩
    have he' : e ∈ (gen Γ a (gen Γ f g).2).2.eqs ++ [((gen Γ f g).1.2, .arrow (gen Γ a (gen Γ f g).2).1.2 (.tvar (gen Γ a (gen Γ f g).2).2.next))] := he
    simp only [List.mem_append, List.mem_singleton] at he'
    rcases he' with he | rfl
    · exact m.2.2 e he
    · exact ⟨(f3.mono a1).mono (Nat.le_succ _), (a3.mono (Nat.le_succ _)), Nat.lt_succ_self _⟩

/-- `θ` with `k` sent to `T`. -/
def upd (θ : Nat → Ty) (k : Nat) (T : Ty) (n : Nat) : Ty := if n = k then T else θ n

theorem upd_below {θ : Nat → Ty} {k : Nat} {T : Ty} : ∀ n < k, upd θ k T n = θ n :=
  fun n hn => by simp [upd, Nat.ne_of_lt hn]

/-- Generation is complete: every typing of a filling of the term, in a context that matches the
generator's under `θ`, gives a `θ'` (agreeing with `θ` on the type variables made so far) that solves
every equation and maps the generated type to the typing's type. -/
theorem gen_complete : ∀ (t : ATerm) (Γ : Ctx) (g : Gen) (θ : Nat → Ty) (t' : ATerm) (Γ' : Ctx) (U : Ty)
    (D : String → Option Ty), Inv Γ g → t.Closed → Fills t' t → HasType Γ' t' U →
    (∀ x A, Γ.lookup x = some A → Γ'.lookup x = some (A.subst θ)) →
    (∀ x, Γ.lookup x = none → Γ'.lookup x = D x) →
    (∀ x A, g.frees.lookup x = some A → D x = some (A.subst θ)) →
    (∀ e ∈ g.eqs, e.1.subst θ = e.2.subst θ) →
    ∃ θ', (∀ n < g.next, θ' n = θ n) ∧ (gen Γ t g).1.2.subst θ' = U ∧
      (∀ x A, (gen Γ t g).2.frees.lookup x = some A → D x = some (A.subst θ')) ∧
      (∀ e ∈ (gen Γ t g).2.eqs, e.1.subst θ' = e.2.subst θ')
  | .var x, Γ, g, θ, t', Γ', U, D, hI, _, hf, hty, hc, hd, hfr, heq => by
    cases hf
    cases hty with
    | var hx =>
    unfold gen
    split
    · rename_i T hT
      refine ⟨θ, fun _ _ => rfl, ?_, hfr, heq⟩
      rw [hc x T hT] at hx; exact Option.some.inj hx
    · rename_i hT
      split
      · rename_i A hA
        refine ⟨θ, fun _ _ => rfl, ?_, hfr, heq⟩
        rw [hd x hT, hfr x A hA] at hx; exact Option.some.inj hx
      · rename_i hA
        refine ⟨upd θ g.next U, fun n hn => upd_below n hn, by simp [Ty.subst, upd], fun y A hy => ?_, fun e he => ?_⟩
        · rw [lookup_append_eq] at hy
          split at hy
          · rename_i B hB
            cases hy
            rw [Ty.subst_below upd_below (hI.frees y _ hB)]
            exact hfr y _ hB
          · by_cases hyx : y = x
            · subst hyx
              simp [List.lookup] at hy; subst hy
              rw [← hd y hT, hx]; simp [Ty.subst, upd]
            · rw [lookup_cons_ne (Ne.symm (Ne.symm hyx))] at hy; simp [List.lookup] at hy
        · rw [Ty.subst_below upd_below (hI.eqs e he).1, Ty.subst_below upd_below (hI.eqs e he).2]
          exact heq e he
  | .lam x (some A) e, Γ, g, θ, t', Γ', U, D, hI, ⟨hA, he⟩, hf, hty, hc, hd, hfr, heq => by
    cases hf with
    | lamSome _ _ hf' =>
    cases hty with
    | abs hty' =>
    have hI' : Inv ((x, A) :: Γ) g := ⟨fun y B hy => by
      by_cases hyx : y = x
      · subst hyx; simp [List.lookup] at hy; subst hy; exact hA.mono (Nat.zero_le _)
      · rw [lookup_cons_ne hyx] at hy; exact hI.ctx y B hy, hI.frees, hI.eqs⟩
    obtain ⟨θ', h1, h2, h3, h4⟩ := gen_complete e ((x, A) :: Γ) g θ _ _ _ D hI' he hf' hty'
      (fun y B hy => by
        by_cases hyx : y = x
        · subst hyx; simp [List.lookup] at hy ⊢; subst hy; rw [Ty.subst_closed θ hA]
        · rw [lookup_cons_ne hyx] at hy ⊢; exact hc y B hy)
      (fun y hy => by
        by_cases hyx : y = x
        · subst hyx; simp [List.lookup] at hy
        · rw [lookup_cons_ne hyx] at hy ⊢; exact hd y hy)
      hfr heq
    refine ⟨θ', h1, ?_, h3, h4⟩
    simp only [gen, Ty.subst, h2, Ty.subst_closed θ' hA]
  | .lam x none e, Γ, g, θ, t', Γ', U, D, hI, he, hf, hty, hc, hd, hfr, heq => by
    cases hf with
    | lamNone _ A hf' =>
    cases hty with
    | abs hty' =>
    have m := hI.mono (Nat.le_succ g.next)
    have hI' : Inv ((x, .tvar g.next) :: Γ) { g with next := g.next + 1 } := ⟨fun y B hy => by
      by_cases hyx : y = x
      · subst hyx; simp [List.lookup] at hy; subst hy; exact Nat.lt_succ_self _
      · rw [lookup_cons_ne hyx] at hy; exact m.1 y B hy, m.2.1, m.2.2⟩
    let θ₁ := upd θ g.next A
    obtain ⟨θ', h1, h2, h3, h4⟩ := gen_complete e _ _ θ₁ _ _ _ D hI' he hf' hty'
      (fun y B hy => by
        by_cases hyx : y = x
        · subst hyx; simp [List.lookup] at hy ⊢; subst hy; simp [Ty.subst, θ₁, upd]
        · rw [lookup_cons_ne hyx] at hy ⊢
          rw [Ty.subst_below upd_below (hI.ctx y B hy)]; exact hc y B hy)
      (fun y hy => by
        by_cases hyx : y = x
        · subst hyx; simp [List.lookup] at hy
        · rw [lookup_cons_ne hyx] at hy ⊢; exact hd y hy)
      (fun y B hy => by rw [Ty.subst_below upd_below (hI.frees y B hy)]; exact hfr y B hy)
      (fun e he => by
        rw [Ty.subst_below upd_below (hI.eqs e he).1, Ty.subst_below upd_below (hI.eqs e he).2]
        exact heq e he)
    refine ⟨θ', fun n hn => ?_, ?_, h3, h4⟩
    · rw [h1 n (Nat.lt_succ_of_lt hn)]; exact upd_below n hn
    · have : θ' g.next = A := by rw [h1 g.next (Nat.lt_succ_self _)]; simp [θ₁, upd]
      simp only [gen, Ty.subst, h2, this]
  | .app f a, Γ, g, θ, t', Γ', U, D, hI, ⟨hfc, hac⟩, hf, hty, hc, hd, hfr, heq => by
    cases hf with
    | app hff haf =>
    cases hty with
    | app htf hta =>
    obtain ⟨f1, f2, f3⟩ := gen_wf f Γ g hI hfc
    obtain ⟨a1, a2, a3⟩ := gen_wf a Γ _ f2 hac
    obtain ⟨θ₁, i1, i2, i3, i4⟩ := gen_complete f Γ g θ _ Γ' _ D hI hfc hff htf hc hd hfr heq
    obtain ⟨θ₂, j1, j2, j3, j4⟩ := gen_complete a Γ (gen Γ f g).2 θ₁ _ Γ' _ D f2 hac haf hta
      (fun y B hy => by rw [Ty.subst_below i1 (hI.ctx y B hy)]; exact hc y B hy) hd i3 i4
    let k := (gen Γ a (gen Γ f g).2).2.next
    refine ⟨upd θ₂ k U, fun n hn => ?_, by simp [gen, Ty.subst, upd, k], fun y B hy => ?_, fun e he => ?_⟩
    · rw [upd_below n (Nat.lt_of_lt_of_le hn (Nat.le_trans f1 a1)), j1 n (Nat.lt_of_lt_of_le hn f1), i1 n hn]
    · have hy' : (gen Γ a (gen Γ f g).2).2.frees.lookup y = some B := hy
      rw [Ty.subst_below upd_below (a2.frees y B hy')]; exact j3 y B hy'
    · have he' : e ∈ (gen Γ a (gen Γ f g).2).2.eqs ++ [((gen Γ f g).1.2, .arrow (gen Γ a (gen Γ f g).2).1.2 (.tvar k))] := he
      simp only [List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · rw [Ty.subst_below upd_below (a2.eqs e he').1, Ty.subst_below upd_below (a2.eqs e he').2]
        exact j4 e he'
      · simp only [Ty.subst]
        rw [Ty.subst_below upd_below (f3.mono a1), Ty.subst_below j1 f3, i2,
          Ty.subst_below upd_below a3, j2]
        simp [upd, k]

/-! ## Inference -/

theorem infer_spec {Γ : Ctx} {t : ATerm} {r : Inferred} (h : infer Γ t = .ok r) :
    r.initial = (gen Γ t {}).1.2 ∧ unify (gen Γ t {}).2.eqs = .ok (r.solved, r.moves) := by
  unfold infer at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i p hu
    obtain ⟨σ, moves⟩ := p
    simp only at h
    split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact ⟨rfl, hu⟩
      · cases h
    · cases h

/-- Hindley's theorem for the simply typed calculus: when `infer` succeeds, every typing of the term
(any types on its unannotated binders, any types for its free variables) has a type that is an
instance of the solved type, before its variables are named. -/
theorem infer_principal {Γ : Ctx} {t : ATerm} {r : Inferred} (h : infer Γ t = .ok r)
    (hΓ : ∀ x A, Γ.lookup x = some A → A.Below 0) (ht : t.Closed)
    {t' : ATerm} {Δ : Ctx} {U : Ty} (hf : Fills t' t) (hty : HasType (Γ ++ Δ) t' U) :
    ∃ θ, U = (r.initial.apply r.solved).subst θ := by
  obtain ⟨hi, hu⟩ := infer_spec h
  have hI : Inv Γ {} := ⟨hΓ, fun _ _ h => by simp [List.lookup] at h, fun _ h => by simp at h⟩
  obtain ⟨θ, -, h2, -, h4⟩ := gen_complete t Γ {} .tvar t' (Γ ++ Δ) U (fun x => (Γ ++ Δ).lookup x) hI ht hf hty
    (fun x A hx => by rw [lookup_append_eq, hx, Ty.subst_id])
    (fun _ _ => rfl) (fun _ _ h => by simp [List.lookup] at h) (fun _ h => by simp at h)
  refine ⟨θ, ?_⟩
  rw [unify_most_general hu θ h4, hi, h2]

end Lam
end MathEngine
