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
