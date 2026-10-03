import MathEngine.LambdaProofs
/-!
# Every λ-step is a β-step

The λ world reduces named terms, renaming bound variables where a substitution would capture. This
file proves that each step it takes is one β-reduction of the λ-calculus, with terms taken up to the
names of bound variables, which is to say as de Bruijn terms (`toDB`):

* `freshVar_not_mem`: a fresh name is fresh;
* `toDB_renameFor`: the α-step before a substitution keeps the term's de Bruijn form;
* `captureFree_renameFor`: after it, substituting captures nothing;
* `toDB_substRaw`: capture-free substitution is de Bruijn substitution (`DB.substAt`);
* `toDB_subst`: so capture-avoiding substitution is, and a contracted redex is the de Bruijn one;
* `betaStep_beta`, `cbnStep_beta`, `cbvStep_beta`, `appStep_beta`, `betaEtaStep_beta`: a step of
  normal order, call by name, call by value, applicative order, or a non-η step of `eta:`, is one
  step of `DB.Beta`, the β-reduction of de Bruijn terms anywhere in a term.

What stays outside: that each strategy picks the redex its name says (leftmost-outermost and so on) is
how the step functions are written, not a theorem here.
-/
namespace MathEngine
namespace Lam

/-! ## Fresh names -/

theorem foldl_max_ge (l : List String) (m : Nat) : m ≤ l.foldl (fun m s => max m s.length) m := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem length_le_foldl (l : List String) (m : Nat) : ∀ s ∈ l, s.length ≤ l.foldl (fun m s => max m s.length) m := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    intro s hs
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge _ _)
    · exact ih _ s hs

theorem length_le_longest {l : List String} {s : String} (h : s ∈ l) : s.length ≤ longest l :=
  length_le_foldl l 0 s h

theorem freshVar_go_not_mem (avoid : List String) (base : String) :
    ∀ n cand, freshVar.go avoid base cand n ∉ avoid := by
  intro n
  induction n with
  | zero =>
    intro cand
    simp only [freshVar.go]
    split
    · intro h
      have := length_le_longest h
      simp [String.length_append] at this
      omega
    · assumption
  | succ n ih =>
    intro cand
    simp only [freshVar.go]
    split
    · exact ih _
    · assumption

/-- A fresh name is fresh. -/
theorem freshVar_not_mem (avoid : List String) (base : String) : freshVar avoid base ∉ avoid :=
  freshVar_go_not_mem avoid base _ _


theorem idxOf?_cons' (a b : String) (l : List String) :
    (b :: l).idxOf? a = if b = a then some 0 else (l.idxOf? a).map (· + 1) := by
  simp [List.idxOf?, List.findIdx?_cons]

theorem idxOf?_append (a : String) (l₁ l₂ : List String) :
    (l₁ ++ l₂).idxOf? a = match l₁.idxOf? a with
      | some i => some i
      | none => (l₂.idxOf? a).map (· + l₁.length) := by
  induction l₁ with
  | nil => simp
  | cons b l ih =>
    rw [List.cons_append, idxOf?_cons', idxOf?_cons', ih]
    by_cases h : b = a
    · simp [h]
    · simp only [h, ite_false]
      cases l.idxOf? a <;> cases l₂.idxOf? a <;> simp <;> omega

theorem idxOf?_eq_none {a : String} {l : List String} : l.idxOf? a = none ↔ a ∉ l := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [idxOf?_cons']
    by_cases h : b = a
    · subst h; simp
    · simp only [h, ite_false, Option.map_eq_none_iff, ih, List.mem_cons, not_or]
      exact ⟨fun h' => ⟨fun e => h e.symm, h'⟩, fun h' => h'.2⟩

theorem idxOf?_lt {a : String} {l : List String} {i : Nat} (h : l.idxOf? a = some i) : i < l.length := by
  induction l generalizing i with
  | nil => simp at h
  | cons b l ih =>
    rw [idxOf?_cons'] at h
    split at h
    · cases h; simp
    · cases hh : l.idxOf? a with
      | none => rw [hh] at h; cases h
      | some j => rw [hh] at h; cases h; simp; exact ih hh

theorem occursFree_iff (z : String) : ∀ s : Term, occursFree z s = true ↔ z ∈ freeVars s
  | .var y => by simp [occursFree, freeVars]; exact eq_comm
  | .lam y e => by
    rw [mem_freeVars_lam]; simp only [occursFree, Bool.and_eq_true, bne_iff_ne, ne_eq]
    rw [occursFree_iff z e]; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, fun h => h1 h.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h2 h.symm, h1⟩
  | .app a b => by
    rw [mem_freeVars_app]; simp only [occursFree, Bool.or_eq_true]
    rw [occursFree_iff z a, occursFree_iff z b]


/-! ## De Bruijn substitution -/

/-- Lift the bound indices at or above `c` by `n`. -/
def DB.liftAt (c n : Nat) : DB → DB
  | .bvar i => if i < c then .bvar i else .bvar (i + n)
  | .free y => .free y
  | .lam b => .lam (liftAt (c + 1) n b)
  | .app f a => .app (liftAt c n f) (liftAt c n a)

/-- Put `u` (a term at the depth of the redex) for the index `k`, the indices above `k` closing up. -/
def DB.substAt (k : Nat) (u : DB) : DB → DB
  | .bvar i => if i < k then .bvar i else if i = k then u.liftAt 0 k else .bvar (i - 1)
  | .free y => .free y
  | .lam b => .lam (substAt (k + 1) u b)
  | .app f a => .app (substAt k u f) (substAt k u a)

/-- Lifting by one at `k` and then substituting at `k` changes nothing. -/
theorem DB.substAt_liftAt (u : DB) : ∀ (d : DB) (k : Nat), DB.substAt k u (DB.liftAt k 1 d) = d
  | .bvar i, k => by
    by_cases h : i < k
    · simp [DB.liftAt, DB.substAt, h]
    · simp [DB.liftAt, DB.substAt, h]
      have h1 : ¬ i + 1 < k := by omega
      have h2 : ¬ i + 1 = k := by omega
      simp [h1, h2]
  | .free y, k => rfl
  | .lam b, k => by simp [DB.liftAt, DB.substAt, DB.substAt_liftAt u b (k + 1)]
  | .app f a, k => by simp [DB.liftAt, DB.substAt, DB.substAt_liftAt u f k, DB.substAt_liftAt u a k]

/-- Binders put between a term and its context lift the term's outer indices, when none of their
names is free in it (`Γ` are the term's own binders above the point reached). -/
theorem toDB_insert (Δ ctx : List String) : ∀ (s : Term) (Γ : List String),
    (∀ z, z ∈ Δ → z ∉ Γ → occursFree z s = false) →
    toDB (Γ ++ Δ ++ ctx) s = DB.liftAt Γ.length Δ.length (toDB (Γ ++ ctx) s)
  | .var w, Γ, h => by
    simp only [toDB]
    rw [List.append_assoc, idxOf?_append w Γ (Δ ++ ctx), idxOf?_append w Γ ctx]
    cases hΓ : Γ.idxOf? w with
    | some i =>
      have := idxOf?_lt hΓ
      simp only [DB.liftAt]; simp [this]
    | none =>
      have hwΓ : w ∉ Γ := idxOf?_eq_none.mp hΓ
      have hwΔ : w ∉ Δ := fun hw => by have := h w hw hwΓ; simp [occursFree] at this
      simp only
      rw [idxOf?_append w Δ ctx, idxOf?_eq_none.mpr hwΔ]
      cases hc : ctx.idxOf? w with
      | none => simp [DB.liftAt]
      | some j =>
        simp only [Option.map_some, DB.liftAt]
        have : ¬ j + Γ.length < Γ.length := by omega
        simp only [this, ite_false]
        congr 1; omega
  | .lam y b, Γ, h => by
    simp only [toDB, DB.liftAt]
    have := toDB_insert Δ ctx b (y :: Γ) (fun z hz hzΓ => by
      have h1 := h z hz (fun hm => hzΓ (List.mem_cons_of_mem _ hm))
      have hzy : y ≠ z := fun e => hzΓ (e ▸ List.mem_cons_self)
      simpa [occursFree, hzy] using h1)
    simpa using this
  | .app f a, Γ, h => by
    simp only [toDB, DB.liftAt]
    rw [toDB_insert Δ ctx f Γ (fun z hz hzΓ => by have := h z hz hzΓ; simp [occursFree] at this; exact this.1),
        toDB_insert Δ ctx a Γ (fun z hz hzΓ => by have := h z hz hzΓ; simp [occursFree] at this; exact this.2)]

/-- `substRaw x s b` captures nothing: every binder of `b` with `x` free below it is named unlike the
free variables of `s` (`fv`), or is `x` itself (and stops the substitution). -/
def CaptureFree (x : String) (fv : List String) : Term → Prop
  | .var _ => True
  | .app f a => CaptureFree x fv f ∧ CaptureFree x fv a
  | .lam y b => y = x ∨ occursFree x b = false ∨ (y ∉ fv ∧ CaptureFree x fv b)

theorem substRaw_not_free (x : String) (s : Term) : ∀ b, occursFree x b = false → substRaw x s b = b
  | .var y, h => by
    simp only [occursFree, beq_eq_false_iff_ne, ne_eq] at h
    simp [substRaw, h]
  | .lam y b, h => by
    simp only [substRaw]
    split
    · rfl
    · rename_i hy
      simp only [occursFree, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
      rcases h with h | h
      · simp_all
      · rw [substRaw_not_free x s b h]
  | .app f a, h => by
    simp only [occursFree, Bool.or_eq_false_iff] at h
    simp [substRaw, substRaw_not_free x s f h.1, substRaw_not_free x s a h.2]

/-- Where `x` is not free, putting `u` for its index leaves the term as it is without `x` bound. -/
theorem toDB_not_free (x : String) (u : DB) (ctx Δ : List String) (b : Term) (h : occursFree x b = false) :
    DB.substAt Δ.length u (toDB (Δ ++ x :: ctx) b) = toDB (Δ ++ ctx) b := by
  have := toDB_insert [x] ctx b Δ (fun z hz _ => by simp at hz; subst hz; exact h)
  simp only [List.append_assoc, List.singleton_append, List.length_singleton] at this
  rw [this, DB.substAt_liftAt]

/-- Capture-free substitution is de Bruijn substitution: substituting `s` for `x` in `b`, under the
binders `Δ` (none named `x`, none free in `s`), is putting `s` for `x`'s index. -/
theorem toDB_substRaw (x : String) (s : Term) (ctx : List String) : ∀ (b : Term) (Δ : List String),
    x ∉ Δ → (∀ z ∈ Δ, z ∉ freeVars s) → CaptureFree x (freeVars s) b →
    toDB (Δ ++ ctx) (substRaw x s b) = DB.substAt Δ.length (toDB ctx s) (toDB (Δ ++ x :: ctx) b)
  | .var w, Δ, hx, hΔ, _ => by
    by_cases hw : w = x
    · subst hw
      have hs : substRaw w s (.var w) = s := by simp [substRaw]
      rw [hs]
      have hl := toDB_insert Δ ctx s [] (fun z hz _ => by
        cases hc : occursFree z s
        · rfl
        · exact absurd ((occursFree_iff z s).mp hc) (hΔ z hz))
      simp only [List.nil_append, List.length_nil] at hl
      rw [hl]
      simp only [toDB]
      rw [idxOf?_append, idxOf?_eq_none.mpr hx, idxOf?_cons']
      simp [DB.substAt]
    · have hs : substRaw x s (.var w) = .var w := by simp [substRaw, hw]
      rw [hs, toDB_not_free x (toDB ctx s) ctx Δ (.var w) (by simp [occursFree, hw])]
  | .lam y b, Δ, hx, hΔ, hcf => by
    by_cases hyx : y = x
    · subst hyx
      have hnf : occursFree y (.lam y b) = false := by simp [occursFree]
      rw [substRaw_not_free y s _ hnf, toDB_not_free y _ ctx Δ _ hnf]
    · simp only [CaptureFree] at hcf
      rcases hcf with h | h | ⟨hy, hcf⟩
      · exact absurd h hyx
      · have hnf : occursFree x (.lam y b) = false := by simp [occursFree, h]
        rw [substRaw_not_free x s _ hnf, toDB_not_free x _ ctx Δ _ hnf]
      · have hs : substRaw x s (.lam y b) = .lam y (substRaw x s b) := by simp [substRaw, hyx]
        rw [hs]
        simp only [toDB, DB.substAt]
        have ih := toDB_substRaw x s ctx b (y :: Δ)
          (by simp [hx]; exact fun e => hyx e.symm)
          (by intro z hz; rcases List.mem_cons.mp hz with rfl | hz; exact hy; exact hΔ z hz) hcf
        simpa using ih
  | .app f a, Δ, hx, hΔ, hcf => by
    simp only [CaptureFree] at hcf
    simp only [substRaw, toDB, DB.substAt]
    rw [toDB_substRaw x s ctx f Δ hx hΔ hcf.1, toDB_substRaw x s ctx a Δ hx hΔ hcf.2]

/-! ## Renaming before substitution -/

theorem lookup_mem {w v : String} : ∀ {ren : List (String × String)}, ren.lookup w = some v → (w, v) ∈ ren
  | [], h => by simp [List.lookup] at h
  | (a, b) :: ren, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hw; cases h; simp at hw; subst hw; simp
    · exact List.mem_cons_of_mem _ (lookup_mem h)

/-- What a variable is renamed to: a pair's second name, or itself. -/
theorem lookup_getD_mem (w : String) (ren : List (String × String)) :
    (ren.lookup w).getD w = w ∨ ((w, (ren.lookup w).getD w) ∈ ren) := by
  cases h : ren.lookup w with
  | none => simp
  | some v => right; simpa using lookup_mem h

/-- Renaming keeps where `x` is free: no binder is renamed to `x`, nor from it. -/
theorem occursFree_freshen (x : String) : ∀ (e : Term) (clash avoid : List String) (ren : List (String × String)),
    x ∈ avoid → (∀ p ∈ ren, p.1 = x ↔ p.2 = x) →
    occursFree x (freshen x clash avoid ren e) = occursFree x e
  | .var w, clash, avoid, ren, _, hren => by
    simp only [freshen, occursFree]
    rcases lookup_getD_mem w ren with h | h
    · rw [h]
    · have := hren _ h
      simp only at this
      by_cases hw : w = x
      · rw [this.mp hw]; simp [hw]
      · have hne : (ren.lookup w).getD w ≠ x := fun e => hw (this.mpr e)
        rw [beq_eq_false_iff_ne.mpr hne, beq_eq_false_iff_ne.mpr hw]
  | .app f a, clash, avoid, ren, hx, hren => by
    simp only [freshen, occursFree]
    rw [occursFree_freshen x f clash avoid ren hx hren, occursFree_freshen x a clash avoid ren hx hren]
  | .lam y b, clash, avoid, ren, hx, hren => by
    simp only [freshen]
    by_cases hyx : y = x
    · subst hyx; simp [occursFree]
    · simp only [beq_iff_eq, hyx, ite_false]
      generalize hy' : (if (clash.contains y && occursFree x b) = true then freshVar avoid y else y) = y'
      have hy'x : y' ≠ x := by
        rw [← hy']; split
        · exact fun e => freshVar_not_mem avoid y (e ▸ hx)
        · exact hyx
      simp only [occursFree]
      rw [show (y' != x) = true from bne_iff_ne.mpr hy'x, show (y != x) = true from bne_iff_ne.mpr hyx]
      simp only [Bool.true_and]
      exact occursFree_freshen x b clash (y' :: avoid) ((y, y') :: ren) (List.mem_cons_of_mem _ hx)
        (by intro p hp; rcases List.mem_cons.mp hp with rfl | hp
            · simp [hyx, hy'x]
            · exact hren p hp)

/-- Renaming keeps a term's de Bruijn form, so it is an α-step. `Γ` and `Γ'` are the binders above
before and after renaming; every name of the term (`N`) is looked up alike in both, a renamed one by
its new name, and a new name is none of `N`. -/
theorem toDB_freshen (x : String) (N : List String) : ∀ (e : Term) (clash avoid : List String)
    (ren : List (String × String)) (Γ Γ' : List String),
    (∀ w ∈ names e, w ∈ N) → (∀ w ∈ N, w ∈ avoid) → (∀ p ∈ ren, p.2 ∈ avoid) →
    (∀ p ∈ ren, p.2 = p.1 ∨ p.2 ∉ N) →
    (∀ w ∈ N, Γ'.idxOf? ((ren.lookup w).getD w) = Γ.idxOf? w ∧ (Γ.idxOf? w = none → (ren.lookup w).getD w = w)) →
    toDB Γ' (freshen x clash avoid ren e) = toDB Γ e
  | .var w, clash, avoid, ren, Γ, Γ', hN, _, _, _, hgood => by
    have ⟨h1, h2⟩ := hgood w (hN w (by simp [names]))
    simp only [freshen, toDB, h1]
    cases hc : Γ.idxOf? w with
    | some i => rfl
    | none => rw [h2 hc]
  | .app f a, clash, avoid, ren, Γ, Γ', hN, hNa, hren, hfresh, hgood => by
    simp only [freshen, toDB]
    rw [toDB_freshen x N f clash avoid ren Γ Γ' (fun w hw => hN w (by simp [names, hw])) hNa hren hfresh hgood,
        toDB_freshen x N a clash avoid ren Γ Γ' (fun w hw => hN w (by simp [names, hw])) hNa hren hfresh hgood]
  | .lam y b, clash, avoid, ren, Γ, Γ', hN, hNa, hren, hfresh, hgood => by
    have hyN : y ∈ N := hN y (by simp [names])
    have hbN : ∀ w ∈ names b, w ∈ N := fun w hw => hN w (by simp [names, hw])
    -- the binder's new name, and the facts about it the step needs
    have step : ∀ (y' : String) (clash' avoid' : List String),
        (y' = y ∨ y' ∉ avoid) → (∀ w ∈ N, w ∈ avoid') → y' ∈ avoid' → (∀ p ∈ ren, p.2 ∈ avoid') →
        toDB Γ' (.lam y' (freshen x clash' avoid' ((y, y') :: ren) b)) = toDB Γ (.lam y b) := by
      intro y' clash' avoid' hy' hNa' hy'a hrena
      simp only [toDB]
      congr 1
      apply toDB_freshen x N b clash' avoid' ((y, y') :: ren) (y :: Γ) (y' :: Γ') hbN hNa'
      · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
        · exact hy'a
        · exact hrena p hp
      · intro p hp; rcases List.mem_cons.mp hp with rfl | hp
        · rcases hy' with h | h
          · exact Or.inl h
          · exact Or.inr fun hn => h (hNa _ hn)
        · exact hfresh p hp
      · intro w hw
        by_cases hwy : y = w
        · subst hwy
          simp [List.lookup, idxOf?_cons']
        · have hl : ((y, y') :: ren).lookup w = ren.lookup w := by
            simp [List.lookup, show (w == y) = false from by simpa [beq_eq_false_iff_ne] using fun e => hwy e.symm]
          rw [hl]
          -- the variable's new name is not the binder's
          have hne : y' ≠ (ren.lookup w).getD w := by
            rcases lookup_getD_mem w ren with h | h
            · rw [h]
              rcases hy' with e | e
              · rw [e]; exact hwy
              · exact fun e' => e (e' ▸ hNa w hw)
            · rcases hy' with e | e
              · rw [e]
                rcases hfresh _ h with h' | h'
                · simp only at h'; rw [h']; exact hwy
                · exact fun e' => h' (e' ▸ hyN)
              · exact fun e' => e (e' ▸ hren _ h)
          have ⟨g1, g2⟩ := hgood w hw
          rw [idxOf?_cons', idxOf?_cons']
          simp only [hne, hwy, ite_false, g1]
          refine ⟨by first | rfl | trivial | simp, fun hn => g2 ?_⟩
          cases hc : Γ.idxOf? w with
          | none => rfl
          | some _ => rw [hc] at hn; cases hn
    simp only [freshen]
    by_cases hyx : y = x
    · subst hyx
      simp only [beq_self_eq_true, ite_true]
      exact step y [] avoid (Or.inl rfl) hNa (hNa y hyN) hren
    · simp only [beq_iff_eq, hyx, ite_false]
      generalize hy' : (if (clash.contains y && occursFree x b) = true then freshVar avoid y else y) = y'
      have hy'c : y' = y ∨ y' ∉ avoid := by
        rw [← hy']; split
        · exact Or.inr (freshVar_not_mem avoid y)
        · exact Or.inl rfl
      exact step y' clash (y' :: avoid) hy'c (fun w hw => List.mem_cons_of_mem _ (hNa w hw)) List.mem_cons_self
        (fun p hp => List.mem_cons_of_mem _ (hren p hp))

/-- After renaming, substituting captures nothing. -/
theorem captureFree_freshen (x : String) (fv : List String) : ∀ (e : Term) (clash avoid : List String)
    (ren : List (String × String)),
    (∀ z ∈ fv, z ≠ x → z ∈ clash) → x ∈ avoid → (∀ z ∈ clash, z ∈ avoid) →
    (∀ p ∈ ren, p.1 = x ↔ p.2 = x) →
    CaptureFree x fv (freshen x clash avoid ren e)
  | .var _, _, _, _, _, _, _, _ => trivial
  | .app f a, clash, avoid, ren, h1, h2, h3, h4 =>
    ⟨captureFree_freshen x fv f clash avoid ren h1 h2 h3 h4, captureFree_freshen x fv a clash avoid ren h1 h2 h3 h4⟩
  | .lam y b, clash, avoid, ren, h1, hx, h3, h4 => by
    simp only [freshen]
    by_cases hyx : y = x
    · subst hyx; simp [CaptureFree]
    · simp only [beq_iff_eq, hyx, ite_false]
      have hren' : ∀ y' : String, y' ≠ x → ∀ p ∈ (y, y') :: ren, (p.1 = x ↔ p.2 = x) := by
        intro y' hy' p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · simp [hyx, hy']
        · exact h4 p hp
      by_cases hc : (clash.contains y && occursFree x b) = true
      · simp only [hc, ite_true, CaptureFree]
        have hf := freshVar_not_mem avoid y
        have hfx : freshVar avoid y ≠ x := fun e => hf (e ▸ hx)
        refine Or.inr (Or.inr ⟨fun hm => hf (h3 _ (h1 _ hm hfx)), ?_⟩)
        exact captureFree_freshen x fv b clash _ _ h1 (List.mem_cons_of_mem _ hx)
          (fun z hz => List.mem_cons_of_mem _ (h3 z hz)) (hren' _ hfx)
      · have e : (if (clash.contains y && occursFree x b) = true then freshVar avoid y else y) = y := by
          split
          · exact absurd ‹_› hc
          · rfl
        rw [e]
        simp only [CaptureFree]
        simp only [Bool.and_eq_true, not_and] at hc
        by_cases hcy : clash.contains y = true
        · -- x is not free below: renaming keeps that
          have hnf : occursFree x b = false := by simpa using hc hcy
          refine Or.inr (Or.inl ?_)
          rw [occursFree_freshen x b clash (y :: avoid) ((y, y) :: ren) (List.mem_cons_of_mem _ hx) (hren' y hyx), hnf]
        · have hy : y ∉ fv := fun hm => hcy (by simpa using h1 y hm hyx)
          exact Or.inr (Or.inr ⟨hy, captureFree_freshen x fv b clash _ _ h1 (List.mem_cons_of_mem _ hx)
            (fun z hz => List.mem_cons_of_mem _ (h3 z hz)) (hren' y hyx)⟩)

theorem captureFree_of_only (x : String) (fv : List String) (h : ∀ z ∈ fv, z = x) :
    ∀ e : Term, CaptureFree x fv e
  | .var _ => trivial
  | .app f a => ⟨captureFree_of_only x fv h f, captureFree_of_only x fv h a⟩
  | .lam y b => by
    by_cases hyx : y = x
    · exact Or.inl hyx
    · exact Or.inr (Or.inr ⟨fun hm => hyx (h y hm), captureFree_of_only x fv h b⟩)

/-- The α-step before a substitution keeps the term's de Bruijn form. -/
theorem toDB_renameFor (x : String) (s e : Term) (Γ : List String) : toDB Γ (renameFor x s e) = toDB Γ e := by
  simp only [renameFor]
  split
  · rfl
  · exact toDB_freshen x (names e) e _ _ [] Γ Γ (fun w hw => hw)
      (fun w hw => List.mem_cons_of_mem _ (List.mem_append_right _ hw)) (by simp) (by simp)
      (fun w _ => by simp [List.lookup])

theorem captureFree_renameFor (x : String) (s e : Term) : CaptureFree x (freeVars s) (renameFor x s e) := by
  simp only [renameFor]
  split
  · rename_i h
    apply captureFree_of_only
    intro z hz
    apply Classical.byContradiction; intro hzx
    have hm : z ∈ (freeVars s).filter (· != x) := List.mem_filter.mpr ⟨hz, by simpa using hzx⟩
    rw [List.isEmpty_iff.mp h] at hm
    simp at hm
  · apply captureFree_freshen
    · intro z hz hzx; exact List.mem_filter.mpr ⟨hz, by simpa using hzx⟩
    · exact List.mem_cons_self
    · intro z hz; exact List.mem_cons_of_mem _ (List.mem_append_left _ hz)
    · simp

/-- Capture-avoiding substitution is de Bruijn substitution. -/
theorem toDB_subst (x : String) (s b : Term) (ctx : List String) :
    toDB ctx (subst x s b).1 = DB.substAt 0 (toDB ctx s) (toDB (x :: ctx) b) := by
  have := toDB_substRaw x s ctx (renameFor x s b) [] (by simp) (by simp) (captureFree_renameFor x s b)
  simp only [List.nil_append, List.length_nil] at this
  simp only [subst]
  rw [this, toDB_renameFor]

/-! ## Every step is a β-step -/

/-- One β-step of de Bruijn terms, anywhere in the term: the λ-calculus's reduction, with terms
taken up to the names of bound variables. -/
inductive DB.Beta : DB → DB → Prop where
  | red (b a : DB) : DB.Beta (.app (.lam b) a) (DB.substAt 0 a b)
  | appL {f f' : DB} (a : DB) : DB.Beta f f' → DB.Beta (.app f a) (.app f' a)
  | appR (f : DB) {a a' : DB} : DB.Beta a a' → DB.Beta (.app f a) (.app f a')
  | lam {b b' : DB} : DB.Beta b b' → DB.Beta (.lam b) (.lam b')

theorem beta_red (x : String) (b a : Term) (ctx : List String) :
    DB.Beta (toDB ctx (.app (.lam x b) a)) (toDB ctx (subst x a b).1) := by
  rw [toDB_subst]; exact DB.Beta.red _ _

/-- A normal-order step is a β-step. -/
theorem betaStep_beta : ∀ (t : Term) (ctx : List String) (t' : Term) (r : Bool),
    betaStep t = some (t', r) → DB.Beta (toDB ctx t) (toDB ctx t')
  | .var _, _, _, _, h => by simp [betaStep] at h
  | .lam x e, ctx, t', r, h => by
    rw [betaStep.eq_3, Option.map_eq_some_iff] at h
    obtain ⟨⟨e', r'⟩, he, hh⟩ := h
    simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
    exact DB.Beta.lam (betaStep_beta e (x :: ctx) e' r' he)
  | .app f a, ctx, t', r, h => by
    by_cases hf : ∃ x b, f = .lam x b
    · obtain ⟨x, b, rfl⟩ := hf
      rw [betaStep.eq_1] at h; cases h; exact beta_red x b a ctx
    · rw [betaStep.eq_2 f a (fun x b e => hf ⟨x, b, e⟩)] at h
      cases hfs : betaStep f with
      | some p =>
        obtain ⟨f', r'⟩ := p
        rw [hfs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact DB.Beta.appL _ (betaStep_beta f ctx f' r' hfs)
      | none =>
        rw [hfs, Option.map_eq_some_iff] at h
        obtain ⟨⟨a', r'⟩, ha, hh⟩ := h
        simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
        exact DB.Beta.appR _ (betaStep_beta a ctx a' r' ha)

/-- A call-by-name step is a β-step. -/
theorem cbnStep_beta : ∀ (t : Term) (ctx : List String) (t' : Term) (r : Bool),
    cbnStep t = some (t', r) → DB.Beta (toDB ctx t) (toDB ctx t')
  | .var _, _, _, _, h => by rw [cbnStep.eq_3 _ (by intros; contradiction) (by intros; contradiction)] at h; cases h
  | .lam _ _, _, _, _, h => by rw [cbnStep.eq_3 _ (by intros; contradiction) (by intros; contradiction)] at h; cases h
  | .app f a, ctx, t', r, h => by
    by_cases hf : ∃ x b, f = .lam x b
    · obtain ⟨x, b, rfl⟩ := hf
      rw [cbnStep.eq_1] at h; cases h; exact beta_red x b a ctx
    · rw [cbnStep.eq_2 f a (fun x b e => hf ⟨x, b, e⟩), Option.map_eq_some_iff] at h
      obtain ⟨⟨f', r'⟩, hfs, hh⟩ := h
      simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
      exact DB.Beta.appL _ (cbnStep_beta f ctx f' r' hfs)

/-- A call-by-value step is a β-step. -/
theorem cbvStep_beta : ∀ (t : Term) (ctx : List String) (t' : Term) (r : Bool),
    cbvStep t = some (t', r) → DB.Beta (toDB ctx t) (toDB ctx t')
  | .var _, _, _, _, h => by rw [cbvStep.eq_3 _ (by intros; contradiction) (by intros; contradiction)] at h; cases h
  | .lam _ _, _, _, _, h => by rw [cbvStep.eq_3 _ (by intros; contradiction) (by intros; contradiction)] at h; cases h
  | .app f a, ctx, t', r, h => by
    by_cases hf : ∃ x b, f = .lam x b
    · obtain ⟨x, b, rfl⟩ := hf
      rw [cbvStep.eq_1] at h
      split at h
      · cases h; exact beta_red x b a ctx
      · rw [Option.map_eq_some_iff] at h
        obtain ⟨⟨a', r'⟩, ha, hh⟩ := h
        simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
        exact DB.Beta.appR _ (cbvStep_beta a ctx a' r' ha)
    · rw [cbvStep.eq_2 f a (fun x b e => hf ⟨x, b, e⟩)] at h
      cases hfs : cbvStep f with
      | some p =>
        obtain ⟨f', r'⟩ := p
        rw [hfs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact DB.Beta.appL _ (cbvStep_beta f ctx f' r' hfs)
      | none =>
        rw [hfs, Option.map_eq_some_iff] at h
        obtain ⟨⟨a', r'⟩, ha, hh⟩ := h
        simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
        exact DB.Beta.appR _ (cbvStep_beta a ctx a' r' ha)

/-- An applicative-order step is a β-step. -/
theorem appStep_beta : ∀ (t : Term) (ctx : List String) (t' : Term) (r : Bool),
    appStep t = some (t', r) → DB.Beta (toDB ctx t) (toDB ctx t')
  | .var _, _, _, _, h => by rw [appStep.eq_1] at h; cases h
  | .lam x e, ctx, t', r, h => by
    rw [appStep.eq_2, Option.map_eq_some_iff] at h
    obtain ⟨⟨e', r'⟩, he, hh⟩ := h
    simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
    exact DB.Beta.lam (appStep_beta e (x :: ctx) e' r' he)
  | .app f a, ctx, t', r, h => by
    by_cases hf : ∃ x b, f = .lam x b
    · obtain ⟨x, b, rfl⟩ := hf
      rw [appStep.eq_3] at h
      cases hfs : appStep (.lam x b) with
      | some p =>
        obtain ⟨f', r'⟩ := p
        rw [hfs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact DB.Beta.appL _ (appStep_beta (.lam x b) ctx f' r' hfs)
      | none =>
        rw [hfs] at h
        cases has : appStep a with
        | some p =>
          obtain ⟨a', r'⟩ := p
          rw [has] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact DB.Beta.appR _ (appStep_beta a ctx a' r' has)
        | none =>
          rw [has] at h; cases h; exact beta_red x b a ctx
    · rw [appStep.eq_4 f a (fun x b e => hf ⟨x, b, e⟩)] at h
      cases hfs : appStep f with
      | some p =>
        obtain ⟨f', r'⟩ := p
        rw [hfs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact DB.Beta.appL _ (appStep_beta f ctx f' r' hfs)
      | none =>
        rw [hfs] at h
        cases has : appStep a with
        | some p =>
          obtain ⟨a', r'⟩ := p
          rw [has] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact DB.Beta.appR _ (appStep_beta a ctx a' r' has)
        | none => rw [has] at h; cases h

/-- A step of `eta:` that is not an η-step is a β-step. -/
theorem betaEtaStep_beta : ∀ (t : Term) (ctx : List String) (t' : Term) (k : StepKind),
    betaEtaStep t = some (t', k) → k ≠ .eta → DB.Beta (toDB ctx t) (toDB ctx t')
  | .var _, _, _, _, h, _ => by rw [betaEtaStep.eq_1] at h; cases h
  | .lam x e, ctx, t', k, h, hk => by
    rw [betaEtaStep.eq_2] at h
    split at h
    · cases h; exact absurd rfl hk
    · rw [Option.map_eq_some_iff] at h
      obtain ⟨⟨e', k'⟩, he, hh⟩ := h
      simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
      exact DB.Beta.lam (betaEtaStep_beta e (x :: ctx) e' k' he hk)
  | .app f a, ctx, t', k, h, hk => by
    by_cases hf : ∃ x b, f = .lam x b
    · obtain ⟨x, b, rfl⟩ := hf
      rw [betaEtaStep.eq_3] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact beta_red x b a ctx
    · rw [betaEtaStep.eq_4 f a (fun x b e => hf ⟨x, b, e⟩)] at h
      cases hfs : betaEtaStep f with
      | some p =>
        obtain ⟨f', k'⟩ := p
        rw [hfs] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact DB.Beta.appL _ (betaEtaStep_beta f ctx f' k' hfs hk)
      | none =>
        rw [hfs, Option.map_eq_some_iff] at h
        obtain ⟨⟨a', k'⟩, ha, hh⟩ := h
        simp only [Prod.mk.injEq] at hh; obtain ⟨rfl, rfl⟩ := hh
        exact DB.Beta.appR _ (betaEtaStep_beta a ctx a' k' ha hk)

end Lam
end MathEngine
