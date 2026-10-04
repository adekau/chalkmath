import MathEngine.RewritingProofs
/-!
# Joinable critical pairs make a system locally confluent

`critical(R)` (`Rewriting.lean`) says a rewriting system is locally confluent when every critical pair
it finds joins. This file proves that answer right.

A rewrite step (`Step`) is an instance of one of the system's rules, at some position, replaced by
the same instance of its right side; `step` takes one (`step_sound`), so `normalize`'s chains are
chains of steps (`chain_star`). Local confluence (`LocallyConfluent`) is that any two steps from one
term reach a common term again (`Joinable`).

- `unify` is Robinson's algorithm, written with well-founded recursion. When it returns `μ`, `μ`
  unifies the two terms and is most general: every unifier factors through it (`unify_mgu`); when it
  returns nothing, the terms have no unifier (`unify_none`).
- `critical` takes every pair of rules (a rule with itself too) and every non-variable position of the
  first one's left side, with the variables renamed apart (`apart_spec`), and records each pair the
  unifier gives (`mem_critical`).
- The critical pair lemma (`critical_pair_lemma`): if every critical pair is joinable, the system is
  locally confluent. Two steps at parallel positions commute; when one is below the other, either the
  inner one is inside the outer rule's left side, at a non-variable position, where it is an
  instance of a critical pair (and joinability is preserved by substitution and context), or below a
  variable of it, where rewriting every copy of that variable joins the two (`star_app_vars`).
- `critical_sound`: when `critical` finds every pair's two sides reaching one term, the system is
  locally confluent. A rule's right side has only variables of its left side (`parseSystem`
  checks it; `parseSystem_wellFormed`).
- `critical_refutes`: two different normal forms of one pair's sides refute confluence, as `step`
  finds a redex whenever there is one (`step_complete`); and Newman's lemma (`newman_lemma`) makes a
  locally confluent system with no infinite rewriting confluent.

Substitutions in the proofs are functions (`T.app`); a list substitution `σ` acts as `σ.fn`.
-/
namespace MathEngine
namespace TRS

/-! ## Substitutions as functions -/

mutual
/-- Apply a substitution given as a function. -/
def T.app (g : String → T) : T → T
  | .v x => g x
  | .f n as => .f n (T.appArgs g as)
def T.appArgs (g : String → T) : List T → List T
  | [] => []
  | a :: as => a.app g :: T.appArgs g as
end

/-- A list substitution as a function: unbound variables stay. -/
def Subst.fn (σ : Subst) (x : String) : T := (σ.lookup x).getD (.v x)

theorem appArgs_eq (g : String → T) : ∀ as : List T, T.appArgs g as = as.map (T.app g)
  | [] => rfl
  | a :: as => by simp [T.appArgs, appArgs_eq g as]

theorem substArgs_eq (σ : Subst) : ∀ as : List T, T.substArgs σ as = as.map (T.subst σ)
  | [] => rfl
  | a :: as => by simp [T.substArgs, substArgs_eq σ as]

theorem varsArgs_eq : ∀ as : List T, T.varsArgs as = as.flatMap T.vars
  | [] => rfl
  | a :: as => by simp [T.varsArgs, varsArgs_eq as]

theorem renameArgs_eq (k : String) : ∀ as : List T, T.renameArgs k as = as.map (T.rename k)
  | [] => rfl
  | a :: as => by simp [T.renameArgs, renameArgs_eq k as]

@[simp] theorem app_v (g : String → T) (x : String) : (T.v x).app g = g x := rfl

theorem app_f (g : String → T) (n : String) (as : List T) :
    (T.f n as).app g = .f n (as.map (T.app g)) := by
  simp [T.app, appArgs_eq]

mutual
theorem subst_eq_app (σ : Subst) : ∀ t : T, t.subst σ = t.app σ.fn
  | .v _ => rfl
  | .f n as => by simp only [T.subst, T.app, substArgs_eq_app σ as]
theorem substArgs_eq_app (σ : Subst) : ∀ as : List T, T.substArgs σ as = T.appArgs σ.fn as
  | [] => rfl
  | a :: as => by simp only [T.substArgs, T.appArgs, subst_eq_app σ a, substArgs_eq_app σ as]
end

mutual
theorem app_app (g h : String → T) : ∀ t : T, (t.app g).app h = t.app fun x => (g x).app h
  | .v _ => rfl
  | .f n as => by simp only [T.app, appArgs_app g h as]
theorem appArgs_app (g h : String → T) : ∀ as : List T,
    T.appArgs h (T.appArgs g as) = T.appArgs (fun x => (g x).app h) as
  | [] => rfl
  | a :: as => by simp only [T.appArgs, app_app g h a, appArgs_app g h as]
end

mutual
theorem app_congr {g h : String → T} : ∀ t : T, (∀ x ∈ t.vars, g x = h x) → t.app g = t.app h
  | .v x, e => e x (by simp [T.vars])
  | .f n as, e => by simp only [T.app, appArgs_congr as (by simpa [T.vars] using e)]
theorem appArgs_congr {g h : String → T} : ∀ as : List T, (∀ x ∈ T.varsArgs as, g x = h x) →
    T.appArgs g as = T.appArgs h as
  | [], _ => rfl
  | a :: as, e => by
    simp only [T.varsArgs, List.mem_append] at e
    simp only [T.appArgs, app_congr a (fun x hx => e x (.inl hx)), appArgs_congr as (fun x hx => e x (.inr hx))]
end

mutual
/-- Two substitutions that agree on a term agree on its variables. -/
theorem app_inj_vars {g h : String → T} : ∀ t : T, t.app g = t.app h → ∀ x ∈ t.vars, g x = h x
  | .v y, e, x, hx => by simp [T.vars] at hx; subst hx; exact e
  | .f n as, e, x, hx => by
    simp only [T.app, T.f.injEq, true_and] at e
    exact appArgs_inj_vars as e x (by simpa [T.vars] using hx)
theorem appArgs_inj_vars {g h : String → T} : ∀ as : List T, T.appArgs g as = T.appArgs h as →
    ∀ x ∈ T.varsArgs as, g x = h x
  | [], _, x, hx => by simp [T.varsArgs] at hx
  | a :: as, e, x, hx => by
    simp only [T.appArgs, List.cons.injEq] at e
    simp only [T.varsArgs, List.mem_append] at hx
    rcases hx with hx | hx
    · exact app_inj_vars a e.1 x hx
    · exact appArgs_inj_vars as e.2 x hx
end

theorem app_var : ∀ t : T, t.app T.v = t := by
  intro t
  have : ∀ t : T, t.app T.v = t.subst [] := fun t => by
    rw [subst_eq_app]; exact app_congr t fun x _ => rfl
  rw [this]
  exact subst_nil t
where
  subst_nil : ∀ t : T, t.subst [] = t
    | .v _ => rfl
    | .f n as => by simp only [T.subst, substArgs_nil as]
  substArgs_nil : ∀ as : List T, T.substArgs [] as = as
    | [] => rfl
    | a :: as => by simp only [T.substArgs, subst_nil a, substArgs_nil as]

theorem subst_nil (t : T) : t.subst [] = t := by
  rw [subst_eq_app]; exact (app_congr t fun _ _ => rfl).trans (app_var t)

mutual
theorem rename_eq_app (k : String) : ∀ t : T, t.rename k = t.app fun x => .v (x ++ k)
  | .v _ => rfl
  | .f n as => by simp only [T.rename, T.app, renameArgs_eq_app k as]
theorem renameArgs_eq_app (k : String) : ∀ as : List T,
    T.renameArgs k as = T.appArgs (fun x => .v (x ++ k)) as
  | [] => rfl
  | a :: as => by simp only [T.renameArgs, T.appArgs, rename_eq_app k a, renameArgs_eq_app k as]
end

/-- A renamed term, substituted: the substitution on the renamed variables. -/
theorem rename_app (k : String) (g : String → T) (t : T) :
    (t.rename k).app g = t.app fun x => g (x ++ k) := by
  rw [rename_eq_app, app_app]; rfl

mutual
theorem size_le_app {g : String → T} {x : String} : ∀ t : T, x ∈ t.vars → (g x).size ≤ (t.app g).size
  | .v y, h => by simp [T.vars] at h; subst h; exact Nat.le_refl _
  | .f n as, h => by
    have := sizeArgs_le_app (g := g) as (by simpa [T.vars] using h)
    simp only [T.app, T.size]; omega
theorem sizeArgs_le_app {g : String → T} {x : String} : ∀ as : List T, x ∈ T.varsArgs as →
    (g x).size ≤ T.sizeArgs (T.appArgs g as)
  | [], h => by simp [T.varsArgs] at h
  | a :: as, h => by
    simp only [T.varsArgs, List.mem_append] at h
    simp only [T.appArgs, T.sizeArgs]
    rcases h with h | h
    · have := size_le_app (g := g) a h; omega
    · have := sizeArgs_le_app (g := g) as h; omega
end

/-- A variable strictly inside a term is worth less than it, whatever the substitution: so `x` and a
term with `x` strictly inside have no unifier. -/
theorem size_lt_app {g : String → T} {x : String} {t : T} (h : x ∈ t.vars) (ne : t ≠ .v x) :
    (g x).size < (t.app g).size := by
  cases t with
  | v y => simp [T.vars] at h; subst h; exact absurd rfl ne
  | f n as =>
    have := sizeArgs_le_app (g := g) as (by simpa [T.vars] using h)
    simp only [T.app, T.size]; omega

/-! ## Positions -/

theorem atArgs_eq : ∀ (as : List T) (i : Nat) (p : Pos), T.atArgs as i p = as[i]?.bind (·.at? p)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: as, i + 1, p => by simp only [T.atArgs, atArgs_eq as i p]; rfl

theorem replaceArgs_eq : ∀ (as : List T) (i : Nat) (p : Pos) (u : T),
    T.replaceArgs as i p u = as.modify i (·.replace p u)
  | [], _, _, _ => by simp [T.replaceArgs]
  | _ :: _, 0, _, _ => rfl
  | a :: as, i + 1, p, u => by simp only [T.replaceArgs, replaceArgs_eq as i p u]; rfl

@[simp] theorem at?_nil (t : T) : t.at? [] = some t := by cases t <;> rfl

@[simp] theorem replace_nil (t u : T) : t.replace [] u = u := by cases t <;> rfl

theorem at?_f (n : String) (as : List T) (i : Nat) (p : Pos) :
    (T.f n as).at? (i :: p) = as[i]?.bind (·.at? p) := by
  simp only [T.at?, atArgs_eq]

@[simp] theorem at?_v (x : String) (i : Nat) (p : Pos) : (T.v x).at? (i :: p) = none := rfl

theorem replace_f (n : String) (as : List T) (i : Nat) (p : Pos) (u : T) :
    (T.f n as).replace (i :: p) u = .f n (as.modify i (·.replace p u)) := by
  simp only [T.replace, replaceArgs_eq]

/-- A subterm at a position, in a term with a position: a function application, with the
argument there. -/
theorem at?_cons {t s : T} {i : Nat} {p : Pos} (h : t.at? (i :: p) = some s) :
    ∃ n as a, t = .f n as ∧ as[i]? = some a ∧ a.at? p = some s := by
  cases t with
  | v x => simp at h
  | f n as =>
    rw [at?_f, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, hs⟩ := h
    exact ⟨n, as, a, rfl, ha, hs⟩

theorem at?_append : ∀ (p q : Pos) (t : T), t.at? (p ++ q) = (t.at? p).bind (·.at? q)
  | [], q, t => by simp
  | i :: p, q, .v x => by simp
  | i :: p, q, .f n as => by
    simp only [List.cons_append, at?_f]
    cases as[i]? with
    | none => rfl
    | some a => exact at?_append p q a

theorem at?_app {g : String → T} : ∀ (p : Pos) {t s : T}, t.at? p = some s →
    (t.app g).at? p = some (s.app g)
  | [], t, s, h => by simp at h; subst h; simp
  | i :: p, t, s, h => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    simp [app_f, at?_f, ha, at?_app p hs]

theorem replace_app {g : String → T} : ∀ (p : Pos) {t s : T} (u : T), t.at? p = some s →
    (t.replace p u).app g = (t.app g).replace p (u.app g)
  | [], t, s, u, _ => by simp
  | i :: p, t, s, u, h => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    simp only [replace_f, app_f, T.f.injEq, true_and]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_map, List.getElem?_modify]
    by_cases e : i = j
    · subst e; simp [ha, replace_app p u hs]
    · simp [e]

theorem at?_replace : ∀ (p : Pos) {t s : T} (u : T), t.at? p = some s → (t.replace p u).at? p = some u
  | [], t, s, u, _ => by simp
  | i :: p, t, s, u, h => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    simp [replace_f, at?_f, ha, at?_replace p u hs]

theorem replace_self : ∀ (p : Pos) {t s : T}, t.at? p = some s → t.replace p s = t
  | [], t, s, h => by simp at h; simp [h]
  | i :: p, t, s, h => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    simp only [replace_f, T.f.injEq, true_and]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_modify]
    by_cases e : i = j
    · subst e; simp [ha, replace_self p hs]
    · simp [e]

theorem replace_replace : ∀ (p : Pos) {t s : T} (u w : T), t.at? p = some s →
    (t.replace p u).replace p w = t.replace p w
  | [], t, s, u, w, _ => by simp
  | i :: p, t, s, u, w, h => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    simp only [replace_f, T.f.injEq, true_and, List.modify_modify_eq]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_modify]
    by_cases e : i = j
    · subst e; simp [ha, replace_replace p u w hs]
    · simp [e]

theorem replace_append : ∀ (p q : Pos) {t s : T} (u : T), t.at? p = some s →
    t.replace (p ++ q) u = t.replace p (s.replace q u)
  | [], q, t, s, u, h => by simp at h; simp [h]
  | i :: p, q, t, s, u, h => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    simp only [List.cons_append, replace_f, T.f.injEq, true_and]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_modify]
    by_cases e : i = j
    · subst e; simp [ha, replace_append p q u hs]
    · simp [e]

/-- Two positions: one is above the other, or they part at some argument. -/
theorem pos_cases : ∀ p q : Pos, (∃ r, q = p ++ r) ∨ (∃ r, p = q ++ r) ∨
    ∃ r i j p' q', i ≠ j ∧ p = r ++ i :: p' ∧ q = r ++ j :: q'
  | [], q => .inl ⟨q, rfl⟩
  | _ :: _, [] => .inr (.inl ⟨_, rfl⟩)
  | i :: p, j :: q => by
    by_cases e : i = j
    · subst e
      rcases pos_cases p q with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, k, l, p', q', ne, rfl, rfl⟩
      · exact .inl ⟨r, rfl⟩
      · exact .inr (.inl ⟨r, rfl⟩)
      · exact .inr (.inr ⟨i :: r, k, l, p', q', ne, rfl, rfl⟩)
    · exact .inr (.inr ⟨[], i, j, p, q, e, rfl, rfl⟩)

/-- Replacing at a position leaves a parallel one as it was. -/
theorem at?_replace_par {i j : Nat} (hij : i ≠ j) : ∀ (r : Pos) {t : T} (p q : Pos) (u : T),
    (t.replace (r ++ i :: p) u).at? (r ++ j :: q) = t.at? (r ++ j :: q)
  | [], .v x, p, q, u => by simp [T.replace]
  | [], .f n as, p, q, u => by
    simp [replace_f, at?_f, List.getElem?_modify_ne _ _ hij]
  | k :: r, .v x, p, q, u => by simp [T.replace]
  | k :: r, .f n as, p, q, u => by
    simp only [List.cons_append, replace_f, at?_f, List.getElem?_modify_eq]
    cases as[k]? with
    | none => rfl
    | some a => exact at?_replace_par hij r p q u

/-- Rewrites at parallel positions commute. -/
theorem replace_comm_par {i j : Nat} (hij : i ≠ j) : ∀ (r : Pos) (t : T) (p q : Pos) (u w : T),
    (t.replace (r ++ i :: p) u).replace (r ++ j :: q) w = (t.replace (r ++ j :: q) w).replace (r ++ i :: p) u
  | [], .v x, p, q, u, w => by simp [T.replace]
  | [], .f n as, p, q, u, w => by
    simp only [List.nil_append, replace_f, List.modify_modify_ne _ _ _ hij]
  | k :: r, .v x, p, q, u, w => by simp [T.replace]
  | k :: r, .f n as, p, q, u, w => by
    simp only [List.cons_append, replace_f, List.modify_modify_eq, T.f.injEq, true_and]
    congr 1
    funext a
    exact replace_comm_par hij r a p q u w

/-- A position in a substituted term is a non-variable position of the term, or is in what a
variable of the term was replaced with. -/
theorem at?_app_split {g : String → T} : ∀ (p : Pos) (t : T) {s : T}, (t.app g).at? p = some s →
    (∃ n as, t.at? p = some (.f n as)) ∨
      ∃ p₁ p₂ x, p = p₁ ++ p₂ ∧ t.at? p₁ = some (.v x) ∧ (g x).at? p₂ = some s
  | p, .v x, s, h => .inr ⟨[], p, x, rfl, rfl, h⟩
  | [], .f n as, s, _ => .inl ⟨n, as, rfl⟩
  | i :: p, .f n as, s, h => by
    rw [app_f, at?_f, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, hs⟩ := h
    rw [List.getElem?_map, Option.map_eq_some_iff] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    rcases at?_app_split p a hs with ⟨m, bs, h⟩ | ⟨p₁, p₂, x, rfl, h1, h2⟩
    · exact .inl ⟨m, bs, by simp [at?_f, ha, h]⟩
    · exact .inr ⟨i :: p₁, p₂, x, rfl, by simp [at?_f, ha, h1], h2⟩

theorem mem_positionsArgs {q : Pos} : ∀ (as : List T) (k i : Nat) {a : T}, as[i]? = some a →
    q ∈ a.positions → (k + i) :: q ∈ T.positionsArgs as k
  | [], _, _, _, h, _ => by simp at h
  | b :: as, k, 0, a, h, hq => by
    simp at h; subst h
    simp [T.positionsArgs, hq]
  | b :: as, k, i + 1, a, h, hq => by
    simp at h
    have := mem_positionsArgs as (k + 1) i h hq
    simp only [T.positionsArgs, List.mem_append]
    exact .inr (by rwa [show k + (i + 1) = k + 1 + i by omega])

/-- Every non-variable position is one `positions` lists. -/
theorem positions_complete : ∀ (p : Pos) {t : T} {n : String} {as : List T}, t.at? p = some (.f n as) →
    p ∈ t.positions
  | [], t, n, as, h => by simp at h; subst h; simp [T.positions]
  | i :: p, t, n, as, h => by
    obtain ⟨m, bs, a, rfl, ha, hs⟩ := at?_cons h
    simp only [T.positions, List.mem_cons]
    exact .inr (by simpa using mem_positionsArgs bs 0 i ha (positions_complete p hs))

theorem vars_at? : ∀ (p : Pos) {t s : T}, t.at? p = some s → ∀ x ∈ s.vars, x ∈ t.vars
  | [], t, s, h, x, hx => by simp at h; subst h; exact hx
  | i :: p, t, s, h, x, hx => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    simp only [T.vars, varsArgs_eq, List.mem_flatMap]
    exact ⟨a, List.mem_of_getElem? ha, vars_at? p hs x hx⟩

/-! ## Rewrite steps -/

/-- One rewrite step: an instance of one of the system's rules, at some position, replaced by the
same instance of its right side. -/
def Step (S : System) (t u : T) : Prop :=
  ∃ ρ ∈ S.rules, ∃ (p : Pos) (σ : Subst), t.at? p = some (ρ.lhs.subst σ) ∧ u = t.replace p (ρ.rhs.subst σ)

/-- Any number of steps. -/
inductive Star (S : System) : T → T → Prop where
  | refl (t : T) : Star S t t
  | head {t u w : T} : Step S t u → Star S u w → Star S t w

/-- Two terms that reach a common term. -/
def Joinable (S : System) (a b : T) : Prop := ∃ w, Star S a w ∧ Star S b w

/-- Any two steps from one term can be joined again. -/
def LocallyConfluent (S : System) : Prop := ∀ t a b, Step S t a → Step S t b → Joinable S a b

/-- Every variable of a rule's right side is one of its left side (`parseSystem` checks it). -/
def System.WellFormed (S : System) : Prop := ∀ ρ ∈ S.rules, ∀ x ∈ ρ.rhs.vars, x ∈ ρ.lhs.vars

theorem lookup_graph (g : String → T) {x : String} : ∀ {l : List String}, x ∈ l →
    (l.map fun y => (y, g y)).lookup x = some (g x)
  | y :: l, h => by
    by_cases e : x = y
    · subst e; simp
    · have : (x == y) = false := by simp [e]
      simp only [List.map_cons, List.lookup, this]
      exact lookup_graph g (by simpa [e] using h)

/-- A step, with the substitution given as a function. -/
theorem step_of_app {S : System} {ρ : Rule} (hρ : ρ ∈ S.rules) {t : T} {p : Pos} {g : String → T}
    (h : t.at? p = some (ρ.lhs.app g)) : Step S t (t.replace p (ρ.rhs.app g)) := by
  let σ : Subst := (ρ.lhs.vars ++ ρ.rhs.vars).map fun y => (y, g y)
  have hσ : ∀ x ∈ ρ.lhs.vars ++ ρ.rhs.vars, σ.fn x = g x := fun x hx => by
    simp only [Subst.fn, σ]; rw [lookup_graph g hx]; rfl
  have hl : ρ.lhs.subst σ = ρ.lhs.app g := by
    rw [subst_eq_app]; exact app_congr _ fun x hx => hσ x (by simp [hx])
  have hr : ρ.rhs.subst σ = ρ.rhs.app g := by
    rw [subst_eq_app]; exact app_congr _ fun x hx => hσ x (by simp [hx])
  exact ⟨ρ, hρ, p, σ, by rw [hl]; exact h, by rw [hr]⟩

theorem step_app {S : System} {t u : T} (h : Step S t u) (g : String → T) : Step S (t.app g) (u.app g) := by
  obtain ⟨ρ, hρ, p, σ, ht, rfl⟩ := h
  rw [subst_eq_app] at ht
  rw [subst_eq_app, replace_app p _ ht, app_app]
  exact step_of_app hρ (by rw [at?_app p ht, app_app])

theorem step_ctx {S : System} {a b : T} (h : Step S a b) {C s : T} {q : Pos} (hC : C.at? q = some s) :
    Step S (C.replace q a) (C.replace q b) := by
  obtain ⟨ρ, hρ, p, σ, ha, rfl⟩ := h
  have h1 : (C.replace q a).at? q = some a := at?_replace q a hC
  refine ⟨ρ, hρ, q ++ p, σ, ?_, ?_⟩
  · rw [at?_append, h1]; exact ha
  · rw [replace_append q p _ h1, replace_replace q _ _ hC]

theorem Star.single {S : System} {t u : T} (h : Step S t u) : Star S t u := .head h (.refl u)

theorem Star.trans {S : System} {t u w : T} : Star S t u → Star S u w → Star S t w
  | .refl _, h => h
  | .head h₁ h₂, h => .head h₁ (h₂.trans h)

theorem Star.app {S : System} {t u : T} (h : Star S t u) (g : String → T) : Star S (t.app g) (u.app g) := by
  induction h with
  | refl => exact .refl _
  | head h _ ih => exact .head (step_app h g) ih

theorem Star.ctx {S : System} {a b : T} (h : Star S a b) {C s : T} {q : Pos} (hC : C.at? q = some s) :
    Star S (C.replace q a) (C.replace q b) := by
  induction h with
  | refl => exact .refl _
  | head h _ ih => exact .head (step_ctx h hC) ih

theorem Joinable.refl {S : System} (t : T) : Joinable S t t := ⟨t, .refl t, .refl t⟩

theorem Joinable.symm {S : System} {a b : T} : Joinable S a b → Joinable S b a
  | ⟨w, ha, hb⟩ => ⟨w, hb, ha⟩

theorem Joinable.app {S : System} {a b : T} (h : Joinable S a b) (g : String → T) :
    Joinable S (a.app g) (b.app g) :=
  let ⟨w, ha, hb⟩ := h; ⟨w.app g, ha.app g, hb.app g⟩

theorem Joinable.subst {S : System} {a b : T} (h : Joinable S a b) (σ : Subst) :
    Joinable S (a.subst σ) (b.subst σ) := by
  rw [subst_eq_app, subst_eq_app]; exact h.app σ.fn

theorem Joinable.ctx {S : System} {a b : T} (h : Joinable S a b) {C s : T} {q : Pos} (hC : C.at? q = some s) :
    Joinable S (C.replace q a) (C.replace q b) :=
  let ⟨w, ha, hb⟩ := h; ⟨C.replace q w, ha.ctx hC, hb.ctx hC⟩

/-- Rewriting the arguments one by one. -/
theorem star_args {S : System} (n : String) : ∀ (pre l₁ l₂ : List T), l₁.length = l₂.length →
    (∀ (i : Nat) (a b : T), l₁[i]? = some a → l₂[i]? = some b → Star S a b) →
    Star S (.f n (pre ++ l₁)) (.f n (pre ++ l₂))
  | pre, [], [], _, _ => .refl _
  | pre, a :: l₁, b :: l₂, hl, h => by
    have hab : Star S a b := h 0 a b rfl rfl
    have hC : (T.f n (pre ++ a :: l₁)).at? [pre.length] = some a := by simp [at?_f]
    have h1 := hab.ctx hC
    rw [replace_self _ hC] at h1
    have e : (T.f n (pre ++ a :: l₁)).replace [pre.length] b = .f n ((pre ++ [b]) ++ l₁) := by
      rw [replace_f]
      congr 1
      apply List.ext_getElem?
      intro j
      rw [List.getElem?_modify]
      rcases Nat.lt_trichotomy j pre.length with hj | rfl | hj
      · simp [List.getElem?_append_left hj, Nat.ne_of_gt hj]
      · simp
      · have : pre.length ≠ j := Nat.ne_of_lt hj
        simp only [this, ite_false]
        rw [List.getElem?_append_right (Nat.le_of_lt hj), List.append_assoc,
          List.getElem?_append_right (Nat.le_of_lt hj)]
        obtain ⟨k, rfl⟩ : ∃ k, j = pre.length + 1 + k := ⟨j - pre.length - 1, by omega⟩
        simp [show pre.length + 1 + k - pre.length = k + 1 by omega]
    rw [e] at h1
    have h2 := star_args n (pre ++ [b]) l₁ l₂ (by simpa using hl) fun i a b h₁ h₂ => h (i + 1) a b h₁ h₂
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h1 h2
    exact h1.trans h2
  | _, [], _ :: _, hl, _ => by simp at hl
  | _, _ :: _, [], hl, _ => by simp at hl

mutual
/-- Rewriting what each variable is replaced with rewrites the substituted term. -/
theorem star_app_vars {S : System} {g g' : String → T} (hg : ∀ x, Star S (g x) (g' x)) :
    ∀ t : T, Star S (t.app g) (t.app g')
  | .v x => hg x
  | .f n as => by
    rw [app_f, app_f]
    have := star_args (S := S) n [] (as.map (T.app g)) (as.map (T.app g')) (by simp) fun i a b h₁ h₂ => by
      simp only [List.getElem?_map, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨c, hc, rfl⟩ := h₁
      obtain ⟨c', hc', rfl⟩ := h₂
      rw [hc] at hc'; cases hc'
      exact star_app_vars_args hg as c (List.mem_of_getElem? hc)
    simpa using this
theorem star_app_vars_args {S : System} {g g' : String → T} (hg : ∀ x, Star S (g x) (g' x)) :
    ∀ as : List T, ∀ a ∈ as, Star S (a.app g) (a.app g')
  | [], a, h => by simp at h
  | b :: as, a, h => by
    rcases List.mem_cons.1 h with e | h
    · rw [e]; exact star_app_vars hg b
    · exact star_app_vars_args hg as a h
end

/-- The same, with one position of the term already replaced. -/
theorem star_app_replace {S : System} {g g' : String → T} (hg : ∀ x, Star S (g x) (g' x)) :
    ∀ (p : Pos) {t s : T} (u : T), t.at? p = some s →
      Star S ((t.app g).replace p u) ((t.app g').replace p u)
  | [], t, s, u, _ => by simp; exact .refl u
  | i :: p, t, s, u, h => by
    obtain ⟨n, as, a, rfl, ha, hs⟩ := at?_cons h
    rw [app_f, app_f, replace_f, replace_f]
    have := star_args (S := S) n [] ((as.map (T.app g)).modify i (·.replace p u))
      ((as.map (T.app g')).modify i (·.replace p u)) (by simp) fun j b b' h₁ h₂ => by
        simp only [List.getElem?_modify, List.getElem?_map] at h₁ h₂
        by_cases e : i = j
        · subst e
          simp [ha] at h₁ h₂
          subst h₁; subst h₂
          exact star_app_replace hg p u hs
        · simp only [e, ite_false] at h₁ h₂
          cases hc : as[j]? with
          | none => simp [hc] at h₁
          | some c =>
            simp [hc] at h₁ h₂
            subst h₁; subst h₂
            exact star_app_vars hg c
    simpa using this

/-- `normalize`'s chains are chains of steps. -/
theorem chain_star {S : System} {t u : T} {l : List (Rule × Pos × T)} (h : Chain S t l u) : Star S t u := by
  induction h with
  | nil => exact .refl _
  | cons hs _ ih =>
    obtain ⟨hρ, σ, ht, rfl⟩ := step_sound _ hs
    exact .head ⟨_, hρ, _, σ, ht, rfl⟩ ih

/-! ## Unification -/

/-- `g` agrees with `σ`: what `σ` binds a variable to, `g` makes what it makes the variable. -/
def Agrees (g : String → T) (σ : Subst) : Prop := ∀ x u, σ.lookup x = some u → u.app g = g x

/-- `g` unifies every equation. -/
def Unifies (g : String → T) (eqs : List (T × T)) : Prop := ∀ e ∈ eqs, e.1.app g = e.2.app g

/-- What `unify` keeps: no variable bound appears in what is bound, nor in the equations left. -/
def Solved (σ : Subst) (eqs : List (T × T)) : Prop :=
  (∀ x u, σ.lookup x = some u → ∀ y ∈ u.vars, σ.lookup y = none) ∧ ∀ y ∈ eqsVars eqs, σ.lookup y = none

theorem unifies_cons {g : String → T} {s t : T} {rest : List (T × T)} :
    Unifies g ((s, t) :: rest) ↔ s.app g = t.app g ∧ Unifies g rest := by
  simp [Unifies]

theorem agrees_subst {g : String → T} {σ : Subst} (h : Agrees g σ) (t : T) : (t.subst σ).app g = t.app g := by
  rw [subst_eq_app, app_app]
  refine app_congr t fun x _ => ?_
  simp only [Subst.fn]
  cases hx : σ.lookup x with
  | none => rfl
  | some u => exact h x u hx

theorem lookup_map_snd (f : T → T) (z : String) : ∀ σ : Subst,
    (σ.map fun (y, w) => (y, f w)).lookup z = (σ.lookup z).map f
  | [] => rfl
  | (y, w) :: σ => by
    by_cases e : z = y
    · subst e; simp
    · have : (z == y) = false := by simp [e]
      simp only [List.map_cons, List.lookup, this]
      exact lookup_map_snd f z σ

theorem lookup_extend (x z : String) (u : T) (σ : Subst) :
    (extend x u σ).lookup z = if z = x then some u else (σ.lookup z).map (·.subst [(x, u)]) := by
  by_cases e : z = x
  · subst e; simp [extend]
  · have : (z == x) = false := by simp [e]
    simp only [extend, List.lookup, this, e, ite_false]
    exact lookup_map_snd _ z σ

theorem agrees_single {g : String → T} {x : String} {u : T} (h : u.app g = g x) : Agrees g [(x, u)] := by
  intro z w hz
  by_cases e : z = x
  · subst e; simp at hz; subst hz; exact h
  · have : (z == x) = false := by simp [e]
    simp [List.lookup, this] at hz

theorem agrees_extend {g : String → T} {x : String} {u : T} {σ : Subst} (hu : u.app g = g x)
    (h : Agrees g σ) : Agrees g (extend x u σ) := by
  intro z w hz
  rw [lookup_extend] at hz
  by_cases e : z = x
  · subst e; simp at hz; subst hz; exact hu
  · simp only [e, ↓reduceIte, Option.map_eq_some_iff] at hz
    obtain ⟨w', hw', rfl⟩ := hz
    rw [agrees_subst (agrees_single hu)]
    exact h z w' hw'

theorem agrees_of_extend {g : String → T} {x : String} {u : T} {σ : Subst} (hx : σ.lookup x = none)
    (h : Agrees g (extend x u σ)) : u.app g = g x ∧ Agrees g σ := by
  have hu : u.app g = g x := h x u (by simp [lookup_extend])
  refine ⟨hu, fun z w hz => ?_⟩
  have hzx : z ≠ x := by intro e; subst e; rw [hx] at hz; cases hz
  have := h z (w.subst [(x, u)]) (by simp [lookup_extend, hzx, hz])
  rwa [agrees_subst (agrees_single hu)] at this

theorem unifies_elim {g : String → T} {x : String} {u : T} (hu : u.app g = g x) :
    ∀ rest : List (T × T), Unifies g (elim x u rest) ↔ Unifies g rest
  | [] => by simp [Unifies, elim]
  | (a, b) :: rest => by
    have ih := unifies_elim hu rest
    simp only [elim, List.map_cons] at ih ⊢
    rw [unifies_cons, unifies_cons, ih, agrees_subst (agrees_single hu), agrees_subst (agrees_single hu)]

theorem lookup_extend_none {x y : String} {u : T} {σ : Subst} (hy : y ≠ x) (h : σ.lookup y = none) :
    (extend x u σ).lookup y = none := by
  simp [lookup_extend, hy, h]

theorem solved_extend {σ : Subst} {x : String} {u : T} {rest : List (T × T)}
    (hσ : ∀ z w, σ.lookup z = some w → ∀ y ∈ w.vars, σ.lookup y = none)
    (hu : ∀ y ∈ u.vars, σ.lookup y = none) (hux : x ∉ u.vars)
    (hr : ∀ y ∈ eqsVars rest, σ.lookup y = none) : Solved (extend x u σ) (elim x u rest) := by
  have hu' : ∀ y ∈ u.vars, (extend x u σ).lookup y = none := fun y hy =>
    lookup_extend_none (fun e => hux (e ▸ hy)) (hu y hy)
  refine ⟨fun z w hz y hy => ?_, fun y hy => ?_⟩
  · rw [lookup_extend] at hz
    by_cases e : z = x
    · simp only [e, ↓reduceIte, Option.some.injEq] at hz; subst hz; exact hu' y hy
    · simp only [e, ↓reduceIte, Option.map_eq_some_iff] at hz
      obtain ⟨w', hw', rfl⟩ := hz
      rcases mem_vars_subst1 w' hy with ⟨h1, h2⟩ | h1
      · exact lookup_extend_none h2 (hσ z w' hw' y h1)
      · exact hu' y h1
  · rcases mem_eqsVars_elim rest hy with ⟨h1, h2⟩ | h1
    · exact lookup_extend_none h2 (hr y h1)
    · exact hu' y h1

theorem solved_sub {σ : Subst} {eqs eqs' : List (T × T)} (h : Solved σ eqs)
    (sub : ∀ y ∈ eqsVars eqs', y ∈ eqsVars eqs) : Solved σ eqs' :=
  ⟨h.1, fun y hy => h.2 y (sub y hy)⟩

theorem agrees_self {σ : Subst} {eqs : List (T × T)} (h : Solved σ eqs) : Agrees σ.fn σ := by
  intro x u hx
  have : u.app σ.fn = u.app T.v := app_congr u fun y hy => by simp [Subst.fn, h.1 x u hx y hy]
  rw [this, app_var]
  simp [Subst.fn, hx]

theorem map_eq_of_zip {g : String → T} : ∀ (as bs : List T), as.length = bs.length →
    (∀ e ∈ as.zip bs, e.1.app g = e.2.app g) → as.map (T.app g) = bs.map (T.app g)
  | [], [], _, _ => rfl
  | a :: as, b :: bs, hl, h => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h
    simp [h.1, map_eq_of_zip as bs (by simpa using hl) h.2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem zip_of_map_eq {g : String → T} : ∀ (as bs : List T), as.map (T.app g) = bs.map (T.app g) →
    ∀ e ∈ as.zip bs, e.1.app g = e.2.app g
  | [], _, _, e, he => by simp at he
  | _ :: _, [], _, e, he => by simp at he
  | a :: as, b :: bs, h, e, he => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zip_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact zip_of_map_eq as bs h.2 e he

theorem sub_head_v {x : String} {u : T} {rest : List (T × T)} :
    ∀ y ∈ eqsVars rest, y ∈ eqsVars ((T.v x, u) :: rest) := fun y hy => by simp [eqsVars, hy]

theorem sub_head_f {s t : T} {rest : List (T × T)} :
    ∀ y ∈ eqsVars rest, y ∈ eqsVars ((s, t) :: rest) := fun y hy => by simp [eqsVars, hy]

/-- Binding `x` to `u` keeps what `unify` keeps, when `u` has no `x`. -/
theorem solved_bind {σ : Subst} {x : String} {u : T} {rest : List (T × T)}
    (h : Solved σ ((T.v x, u) :: rest)) (hux : ¬u.occurs x = true) :
    Solved (extend x u σ) (elim x u rest) ∧ σ.lookup x = none :=
  ⟨solved_extend h.1 (fun y hy => h.2 y (by simp [eqsVars, hy])) (by rwa [occurs_iff] at hux)
    (fun y hy => h.2 y (by simp [eqsVars, hy])), h.2 x (by simp [eqsVars, T.vars])⟩

theorem solved_flip {σ : Subst} {x : String} {u : T} {rest : List (T × T)}
    (h : Solved σ ((u, T.v x) :: rest)) : Solved σ ((T.v x, u) :: rest) :=
  solved_sub h fun y hy => by
    simp only [eqsVars, List.mem_append] at hy ⊢
    rcases hy with (hy | hy) | hy <;> simp [hy]

/-- When `unify` returns `μ`, `μ` unifies the equations and agrees with the substitution it started
from; and binds nothing it mentions. -/
theorem unify_sound : ∀ (eqs : List (T × T)) (σ : Subst), Solved σ eqs → ∀ μ, unify eqs σ = some μ →
    Solved μ [] ∧ Unifies μ.fn eqs ∧ Agrees μ.fn σ := by
  intro eqs σ
  induction eqs, σ using unify.induct with
  | case1 σ =>
    intro hs μ h
    simp only [unify, Option.some.injEq] at h; subst h
    exact ⟨⟨hs.1, by simp [eqsVars]⟩, by simp [Unifies], agrees_self hs⟩
  | case2 σ x rest ih =>
    intro hs μ h
    simp only [unify, ite_true] at h
    obtain ⟨h1, h2, h3⟩ := ih (solved_sub hs sub_head_v) μ h
    exact ⟨h1, unifies_cons.2 ⟨rfl, h2⟩, h3⟩
  | case3 σ x u rest hne hocc =>
    intro _ μ h
    simp [unify, hne, hocc] at h
  | case4 σ x u rest hne hocc ih =>
    intro hs μ h
    simp only [unify, hne, hocc, ite_false] at h
    obtain ⟨hs', hx⟩ := solved_bind hs hocc
    obtain ⟨h1, h2, h3⟩ := ih hs' μ h
    obtain ⟨hu, h4⟩ := agrees_of_extend hx h3
    exact ⟨h1, unifies_cons.2 ⟨hu.symm, (unifies_elim hu rest).1 h2⟩, h4⟩
  | case5 σ n as x rest hocc =>
    intro _ μ h
    simp [unify, hocc] at h
  | case6 σ n as x rest hocc ih =>
    intro hs μ h
    simp only [unify, hocc] at h
    obtain ⟨hs', hx⟩ := solved_bind (solved_flip hs) hocc
    obtain ⟨h1, h2, h3⟩ := ih hs' μ h
    obtain ⟨hu, h4⟩ := agrees_of_extend hx h3
    exact ⟨h1, unifies_cons.2 ⟨hu, (unifies_elim hu rest).1 h2⟩, h4⟩
  | case7 σ n as m bs rest heq ih =>
    intro hs μ h
    simp only [unify, heq, ite_true] at h
    obtain ⟨h1, h2, h3⟩ := ih (solved_sub hs sub_head_f) μ h
    exact ⟨h1, unifies_cons.2 ⟨by rw [heq], h2⟩, h3⟩
  | case8 σ n as m bs rest hne hcl =>
    intro _ μ h
    simp [unify, hne, hcl] at h
  | case9 σ n as m bs rest hne hcl ih =>
    intro hs μ h
    simp only [unify, hne, hcl, ite_false] at h
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hcl
    obtain ⟨hnm, hl⟩ := hcl
    have sub : ∀ y ∈ eqsVars (as.zip bs ++ rest), y ∈ eqsVars ((T.f n as, T.f m bs) :: rest) := by
      intro y hy
      rw [eqsVars_append, List.mem_append] at hy
      simp only [eqsVars, T.vars, List.mem_append]
      rcases hy with hy | hy
      · rcases mem_eqsVars_zip as bs hy with hy | hy <;> simp [hy]
      · simp [hy]
    obtain ⟨h1, h2, h3⟩ := ih (solved_sub hs sub) μ h
    refine ⟨h1, unifies_cons.2 ⟨?_, fun e he => h2 e (by simp [he])⟩, h3⟩
    rw [app_f, app_f, hnm, map_eq_of_zip as bs hl fun e he => h2 e (by simp [he])]

/-- `unify` finds a unifier whenever there is one, and every unifier agrees with it. -/
theorem unify_complete : ∀ (eqs : List (T × T)) (σ : Subst), Solved σ eqs → ∀ g, Unifies g eqs →
    Agrees g σ → ∃ μ, unify eqs σ = some μ ∧ Agrees g μ := by
  intro eqs σ
  induction eqs, σ using unify.induct with
  | case1 σ => intro _ g _ ha; exact ⟨σ, by simp [unify], ha⟩
  | case2 σ x rest ih =>
    intro hs g hu ha
    obtain ⟨μ, h1, h2⟩ := ih (solved_sub hs sub_head_v) g (unifies_cons.1 hu).2 ha
    exact ⟨μ, by simp [unify, h1], h2⟩
  | case3 σ x u rest hne hocc =>
    intro _ g hu _
    have := size_lt_app (g := g) ((occurs_iff u).1 hocc) (Ne.symm hne)
    rw [← (unifies_cons.1 hu).1] at this
    exact absurd this (Nat.lt_irrefl _)
  | case4 σ x u rest hne hocc ih =>
    intro hs g hu ha
    obtain ⟨hs', _⟩ := solved_bind hs hocc
    have h0 : u.app g = g x := (unifies_cons.1 hu).1.symm
    obtain ⟨μ, h1, h2⟩ := ih hs' g ((unifies_elim h0 rest).2 (unifies_cons.1 hu).2) (agrees_extend h0 ha)
    exact ⟨μ, by simp only [unify, hne, hocc, ite_false]; exact h1, h2⟩
  | case5 σ n as x rest hocc =>
    intro _ g hu _
    have := size_lt_app (g := g) ((occurs_iff _).1 hocc) (by simp)
    rw [(unifies_cons.1 hu).1] at this
    exact absurd this (Nat.lt_irrefl _)
  | case6 σ n as x rest hocc ih =>
    intro hs g hu ha
    obtain ⟨hs', _⟩ := solved_bind (solved_flip hs) hocc
    have h0 : (T.f n as).app g = g x := (unifies_cons.1 hu).1
    obtain ⟨μ, h1, h2⟩ := ih hs' g ((unifies_elim h0 rest).2 (unifies_cons.1 hu).2) (agrees_extend h0 ha)
    exact ⟨μ, by simp only [unify, hocc]; exact h1, h2⟩
  | case7 σ n as m bs rest heq ih =>
    intro hs g hu ha
    obtain ⟨μ, h1, h2⟩ := ih (solved_sub hs sub_head_f) g (unifies_cons.1 hu).2 ha
    exact ⟨μ, by simp only [unify, heq, ite_true]; exact h1, h2⟩
  | case8 σ n as m bs rest hne hcl =>
    intro _ g hu _
    have e := (unifies_cons.1 hu).1
    rw [app_f, app_f, T.f.injEq] at e
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hcl
    rcases hcl with h | h
    · exact absurd e.1 h
    · exact absurd (by simpa using congrArg List.length e.2) h
  | case9 σ n as m bs rest hne hcl ih =>
    intro hs g hu ha
    have e := (unifies_cons.1 hu).1
    rw [app_f, app_f, T.f.injEq] at e
    have sub : ∀ y ∈ eqsVars (as.zip bs ++ rest), y ∈ eqsVars ((T.f n as, T.f m bs) :: rest) := by
      intro y hy
      rw [eqsVars_append, List.mem_append] at hy
      simp only [eqsVars, T.vars, List.mem_append]
      rcases hy with hy | hy
      · rcases mem_eqsVars_zip as bs hy with hy | hy <;> simp [hy]
      · simp [hy]
    have hu' : Unifies g (as.zip bs ++ rest) := fun p hp => by
      rcases List.mem_append.1 hp with hp | hp
      · exact zip_of_map_eq as bs e.2 p hp
      · exact (unifies_cons.1 hu).2 p hp
    obtain ⟨μ, h1, h2⟩ := ih (solved_sub hs sub) g hu' ha
    exact ⟨μ, by simp only [unify, hne, hcl, ite_false]; exact h1, h2⟩

theorem solved_start (a b : T) : Solved [] [(a, b)] := ⟨by simp, by simp⟩

/-- The unifier `unify` returns unifies the two terms, and is most general: any unifier of the two is
the same after it. -/
theorem unify_mgu {a b : T} {μ : Subst} (h : unify [(a, b)] [] = some μ) :
    a.subst μ = b.subst μ ∧ ∀ g : String → T, a.app g = b.app g → ∀ t : T, (t.subst μ).app g = t.app g := by
  obtain ⟨_, h2, _⟩ := unify_sound _ _ (solved_start a b) μ h
  refine ⟨by rw [subst_eq_app, subst_eq_app]; exact h2 (a, b) (by simp), fun g hg t => ?_⟩
  obtain ⟨μ', h1, h2⟩ := unify_complete _ _ (solved_start a b) g (by simpa [Unifies] using hg)
    (fun _ _ h => by simp at h)
  rw [h] at h1; cases h1
  exact agrees_subst h2 t

/-- When `unify` returns nothing, the two terms have no unifier. -/
theorem unify_none {a b : T} (h : unify [(a, b)] [] = none) (g : String → T) : a.app g ≠ b.app g := by
  intro hg
  obtain ⟨μ, h1, _⟩ := unify_complete _ _ (solved_start a b) g (by simpa [Unifies] using hg)
    (fun _ _ h => by simp at h)
  rw [h] at h1; cases h1

/-! ## Critical pairs -/

theorem le_foldr_max {x : String} : ∀ {V : List String}, x ∈ V → x.length ≤ (V.map String.length).foldr max 0
  | y :: V, h => by
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_foldr_max h) (Nat.le_max_right _ _)

/-- `apart` renames apart: no variable of the first rule, primed once, is a variable of the second
with the suffix. -/
theorem apart_spec (V₁ V₂ : List String) : ∀ x ∈ V₁, ∀ y ∈ V₂, x ++ "'" ≠ y ++ apart V₁ V₂ := by
  intro x hx y hy
  unfold apart
  split
  · rename_i h
    simp only [List.all_eq_true, bne_iff_ne, ne_eq] at h
    exact h x hx y hy
  · intro e
    have := congrArg String.length e
    simp only [String.length_append, String.length_ofList, List.length_replicate] at this
    have h1 : "'".length = 1 := rfl
    have := le_foldr_max hx
    omega

/-- The renamed variables of two rules, apart, can be given any values. -/
theorem exists_apart_subst {V₁ V₂ : List String} {k : String} (hk : ∀ x ∈ V₁, ∀ y ∈ V₂, x ++ "'" ≠ y ++ k)
    (g₁ g₂ : String → T) :
    ∃ θ : String → T, (∀ x ∈ V₁, θ (x ++ "'") = g₁ x) ∧ ∀ y ∈ V₂, θ (y ++ k) = g₂ y := by
  refine ⟨fun z => match V₁.find? (fun x => x ++ "'" == z) with
    | some x => g₁ x
    | none => match V₂.find? (fun y => y ++ k == z) with
      | some y => g₂ y
      | none => .v z, fun x hx => ?_, fun y hy => ?_⟩
  · cases h : V₁.find? (fun x' => x' ++ "'" == x ++ "'") with
    | none => exact absurd (List.find?_eq_none.1 h x hx) (by simp)
    | some x' =>
      have := List.find?_some h
      simp only [beq_iff_eq, String.append_left_inj] at this
      subst this
      simp only [h]
  · have h1 : V₁.find? (fun x => x ++ "'" == y ++ k) = none :=
      List.find?_eq_none.2 fun x hx => by simpa using hk x hx y hy
    cases h : V₂.find? (fun y' => y' ++ k == y ++ k) with
    | none => exact absurd (List.find?_eq_none.1 h y hy) (by simp)
    | some y' =>
      have := List.find?_some h
      simp only [beq_iff_eq, String.append_left_inj] at this
      subst this
      simp only [h1, h]

/-- `tidy` only renames: some substitution takes its terms back. -/
theorem tidy_spec (ts : List T) : ∃ κ : Subst, (tidy ts).map (·.subst κ) = ts := by
  unfold tidy
  dsimp only
  split
  · rename_i h; exact ⟨_, h⟩
  · exact ⟨[], by simp [subst_nil]⟩

/-- `critical` records every overlap the unifier finds: of each rule on each, at each non-variable
position of the first one's left side (but the root, when the two are one rule). -/
theorem mem_critical {S : System} {i j : Nat} {ρ₁ ρ₂ : Rule} (h1 : S.rules[i]? = some ρ₁)
    (h2 : S.rules[j]? = some ρ₂) {p : Pos} (hp : p ∈ (ρ₁.lhs.rename "'").positions)
    (hne : ¬(p = [] ∧ i = j)) {sub : T} (hsub : (ρ₁.lhs.rename "'").at? p = some sub) {μ : Subst}
    (hu : unify [(sub, ρ₂.lhs.rename (apart (ρ₁.lhs.vars ++ ρ₁.rhs.vars) (ρ₂.lhs.vars ++ ρ₂.rhs.vars)))] [] = some μ) :
    ∃ c ∈ critical S, ∃ κ : Subst, c.left.subst κ = (ρ₁.rhs.rename "'").subst μ ∧
      c.right.subst κ = ((ρ₁.lhs.rename "'").replace p
        (ρ₂.rhs.rename (apart (ρ₁.lhs.vars ++ ρ₁.rhs.vars) (ρ₂.lhs.vars ++ ρ₂.rhs.vars)))).subst μ := by
  let k := apart (ρ₁.lhs.vars ++ ρ₁.rhs.vars) (ρ₂.lhs.vars ++ ρ₂.rhs.vars)
  let ts := [(ρ₁.lhs.rename "'").subst μ, (ρ₁.rhs.rename "'").subst μ,
    ((ρ₁.lhs.rename "'").replace p (ρ₂.rhs.rename k)).subst μ]
  obtain ⟨κ, hκ⟩ := tidy_spec ts
  have hlen : (tidy ts).length = 3 := by
    have := congrArg List.length hκ; simpa [ts] using this
  match ht : tidy ts, hlen with
  | [peak, left, right], _ =>
    rw [ht] at hκ
    simp only [List.map_cons, List.map_nil, List.cons.injEq, ts] at hκ
    refine ⟨⟨ρ₁, ρ₂, p, peak, left, right⟩, ?_, κ, hκ.2.1, hκ.2.2.1⟩
    simp only [critical, List.mem_flatMap]
    refine ⟨(ρ₁, i), List.mem_zipIdx_iff_getElem?.2 h1, (ρ₂, j), List.mem_zipIdx_iff_getElem?.2 h2, ?_⟩
    simp only [criticalOf, List.mem_filterMap]
    refine ⟨p, hp, ?_⟩
    have : (p.isEmpty && (i == j)) = false := by
      cases p with
      | nil => simpa using hne
      | cons _ _ => rfl
    simp only [this, Bool.false_eq_true, ↓reduceIte, hsub, hu]
    simp only [ts, k] at ht
    simp [ht]

/-- An overlap at the root of `ρ₁`'s left side: the two results join, when every critical pair does. -/
theorem root_joinable {S : System} (hS : S.WellFormed) (H : ∀ c ∈ critical S, Joinable S c.left c.right)
    {i j : Nat} {ρ₁ ρ₂ : Rule} (h1 : S.rules[i]? = some ρ₁) (h2 : S.rules[j]? = some ρ₂)
    {g₁ g₂ : String → T} {q : Pos} (hq : (ρ₁.lhs.app g₁).at? q = some (ρ₂.lhs.app g₂)) :
    Joinable S (ρ₁.rhs.app g₁) ((ρ₁.lhs.app g₁).replace q (ρ₂.rhs.app g₂)) := by
  have hρ₁ := List.mem_of_getElem? h1
  have hρ₂ := List.mem_of_getElem? h2
  rcases at?_app_split q ρ₁.lhs hq with ⟨n, as, hsub⟩ | ⟨q₁, q₂, x, rfl, hx, hq₂⟩
  · by_cases hroot : q = [] ∧ i = j
    · -- a rule on itself at the root: one instance, as the right side has only its left's variables
      obtain ⟨rfl, rfl⟩ := hroot
      rw [h1, Option.some.injEq] at h2
      subst h2
      simp only [at?_nil, Option.some.injEq] at hq
      have hr : ρ₁.rhs.app g₁ = ρ₁.rhs.app g₂ :=
        app_congr _ fun x hx => app_inj_vars _ hq x (hS ρ₁ hρ₁ x hx)
      simp only [replace_nil, hr]
      exact Joinable.refl _
    · -- a non-variable position: an instance of a critical pair
      let V₁ := ρ₁.lhs.vars ++ ρ₁.rhs.vars
      let V₂ := ρ₂.lhs.vars ++ ρ₂.rhs.vars
      obtain ⟨θ, hθ₁, hθ₂⟩ := exists_apart_subst (apart_spec V₁ V₂) g₁ g₂
      have e₁ : ∀ t : T, (∀ x ∈ t.vars, x ∈ V₁) → (t.rename "'").app θ = t.app g₁ := fun t ht => by
        rw [rename_app]; exact app_congr t fun x hx => hθ₁ x (ht x hx)
      have e₂ : ∀ t : T, (∀ x ∈ t.vars, x ∈ V₂) → (t.rename (apart V₁ V₂)).app θ = t.app g₂ := fun t ht => by
        rw [rename_app]; exact app_congr t fun x hx => hθ₂ x (ht x hx)
      have hsub' : (ρ₁.lhs.rename "'").at? q = some ((T.f n as).rename "'") := by
        rw [rename_eq_app, rename_eq_app]; exact at?_app q hsub
      have hpos : q ∈ (ρ₁.lhs.rename "'").positions :=
        positions_complete q (n := n) (as := T.renameArgs "'" as) (by rw [hsub']; rfl)
      have hunif : ((T.f n as).rename "'").app θ = (ρ₂.lhs.rename (apart V₁ V₂)).app θ := by
        rw [e₁ _ fun x hx => by simp [V₁, vars_at? q hsub x hx], e₂ _ fun x hx => by simp [V₂, hx]]
        have := at?_app (g := g₁) q hsub
        rw [hq, Option.some.injEq] at this
        exact this.symm
      cases hμ : unify [((T.f n as).rename "'", ρ₂.lhs.rename (apart V₁ V₂))] [] with
      | none => exact absurd hunif (unify_none hμ θ)
      | some μ =>
        have hmg := (unify_mgu hμ).2 θ hunif
        obtain ⟨c, hc, κ, hl, hr⟩ := mem_critical h1 h2 hpos hroot hsub' hμ
        have J := (H c hc).subst κ
        rw [hl, hr] at J
        have J' := J.app θ
        rw [hmg, hmg, replace_app q _ hsub', e₁ _ fun x hx => by simp [V₁, hx],
          e₁ _ fun x hx => by simp [V₁, hx], e₂ _ fun x hx => by simp [V₂, hx]] at J'
        exact J'
  · -- below a variable `x` of the left side: rewrite every copy of `x`
    have hx' : (ρ₁.lhs.app g₁).at? q₁ = some (g₁ x) := at?_app q₁ hx
    let w := (g₁ x).replace q₂ (ρ₂.rhs.app g₂)
    have hw : Step S (g₁ x) w := step_of_app hρ₂ hq₂
    let g₁' : String → T := fun y => if y = x then w else g₁ y
    have hg : ∀ y, Star S (g₁ y) (g₁' y) := fun y => by
      by_cases e : y = x
      · subst e; simp only [g₁', ↓reduceIte]; exact .single hw
      · simp only [g₁', e, ↓reduceIte]; exact .refl _
    refine ⟨ρ₁.rhs.app g₁', star_app_vars hg _, ?_⟩
    rw [replace_append q₁ q₂ _ hx']
    have s1 := star_app_replace hg q₁ w hx
    have hx'' : (ρ₁.lhs.app g₁').at? q₁ = some w := by
      have := at?_app (g := g₁') q₁ hx; simpa [g₁'] using this
    rw [replace_self q₁ hx''] at s1
    have s2 : Step S (ρ₁.lhs.app g₁') (ρ₁.rhs.app g₁') := by
      have := step_of_app (p := []) (t := ρ₁.lhs.app g₁') (g := g₁') hρ₁ (by simp)
      simpa using this
    exact s1.trans (.single s2)

/-- The critical pair lemma: when every critical pair is joinable, the system is locally
confluent. -/
theorem critical_pair_lemma {S : System} (hS : S.WellFormed)
    (H : ∀ c ∈ critical S, Joinable S c.left c.right) : LocallyConfluent S := by
  intro t a b ha hb
  obtain ⟨ρ₁, hρ₁, p₁, σ₁, ht₁, rfl⟩ := ha
  obtain ⟨ρ₂, hρ₂, p₂, σ₂, ht₂, rfl⟩ := hb
  obtain ⟨i, h1⟩ := List.getElem?_of_mem hρ₁
  obtain ⟨j, h2⟩ := List.getElem?_of_mem hρ₂
  rw [subst_eq_app] at ht₁ ht₂
  rw [subst_eq_app, subst_eq_app]
  rcases pos_cases p₁ p₂ with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, k, l, p', q', hkl, rfl, rfl⟩
  · rw [at?_append, ht₁] at ht₂
    rw [replace_append p₁ r _ ht₁]
    exact (root_joinable hS H h1 h2 ht₂).ctx ht₁
  · rw [at?_append, ht₂] at ht₁
    rw [replace_append p₂ r _ ht₂]
    exact ((root_joinable hS H h2 h1 ht₁).ctx ht₂).symm
  · -- parallel steps commute
    refine ⟨(t.replace (r ++ k :: p') (ρ₁.rhs.app σ₁.fn)).replace (r ++ l :: q') (ρ₂.rhs.app σ₂.fn),
      .single ?_, .single ?_⟩
    · exact step_of_app hρ₂ (by rw [at?_replace_par hkl]; exact ht₂)
    · rw [replace_comm_par hkl]
      exact step_of_app hρ₁ (by rw [at?_replace_par (Ne.symm hkl)]; exact ht₁)

/-- `critical(R)`'s "locally confluent": when both sides of every critical pair it finds rewrite to one
term, the system is locally confluent. -/
theorem critical_sound {S : System} (hS : S.WellFormed) (fuel : Nat)
    (h : ∀ c ∈ critical S, (normalize S c.left fuel).2.1 = (normalize S c.right fuel).2.1) :
    LocallyConfluent S :=
  critical_pair_lemma hS fun c hc => ⟨_, chain_star (normalize_chain S c.left fuel),
    by rw [h c hc]; exact chain_star (normalize_chain S c.right fuel)⟩

/-! ## Parsed systems are well formed -/

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem parseRule_wellFormed {k : Nat} {c : String} {ρ : Rule} (h : parseRule k c = .ok ρ) :
    ∀ x ∈ ρ.rhs.vars, x ∈ ρ.lhs.vars := by
  unfold parseRule at h
  split at h
  rename_i name body _
  split at h
  · rename_i l r _
    obtain ⟨lhs, -, h⟩ := bind_ok h
    obtain ⟨rhs, -, h⟩ := bind_ok h
    dsimp only at h
    have key : ∀ {β : Type} {e : String} {f : Unit → Except String β} {r : β},
        ((throw e : Except String Unit) >>= f) ≠ .ok r := fun h => nomatch h
    split at h
    · exact absurd h key
    · split at h
      · exact absurd h key
      · rename_i hx
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        intro x hxr
        simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq, Decidable.not_not,
          List.filter_eq_nil_iff] at hx
        simpa using hx x hxr
  · cases h

theorem mapM_ok {α : Type} {f : α → Except String Rule} {P : Rule → Prop} (hf : ∀ a ρ, f a = .ok ρ → P ρ) :
    ∀ (l : List α) (rs : List Rule), l.mapM f = .ok rs → ∀ ρ ∈ rs, P ρ
  | [], rs, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | a :: l, rs, h => by
    rw [List.mapM_cons] at h
    obtain ⟨ρ, h1, h⟩ := bind_ok h
    obtain ⟨rs', h2, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro ρ' hρ'
    rcases List.mem_cons.1 hρ' with rfl | hρ'
    · exact hf a _ h1
    · exact mapM_ok hf l rs' h2 ρ' hρ'

/-- Every system `rules(…)` makes is well formed: `parseRule` turns down a rule with a variable on the
right that is not on the left. -/
theorem parseSystem_wellFormed {body : String} {S : System} (h : parseSystem body = .ok S) : S.WellFormed := by
  unfold parseSystem at h
  dsimp only at h
  have key : ∀ {β : Type} {e : String} {f : Unit → Except String β} {r : β},
      ((throw e : Except String Unit) >>= f) ≠ .ok r := fun h => nomatch h
  split at h
  · exact absurd h key
  · obtain ⟨rules, h1, h⟩ := bind_ok h
    split at h
    · exact absurd h key
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact mapM_ok (fun _ _ h => parseRule_wellFormed h) _ rules h1

/-! ## Normal forms, confluence, and Newman's lemma -/

/-- No step leaves the term. -/
def Normal (S : System) (t : T) : Prop := ∀ u, ¬Step S t u

/-- Any two rewrites of one term, however long, can be joined again. -/
def Confluent (S : System) : Prop := ∀ t a b, Star S t a → Star S t b → Joinable S a b

mutual
/-- Matching finds every instance: when the pattern becomes the term under `g`, and `g` agrees with
what is bound already, the match succeeds and still agrees. -/
theorem matchT_complete {g : String → T} : ∀ (σ : Subst) (p : T),
    (∀ x u, σ.lookup x = some u → g x = u) →
    ∃ σ', matchT σ p (p.app g) = some σ' ∧ ∀ x u, σ'.lookup x = some u → g x = u
  | σ, .v x, hσ => by
    cases hl : σ.lookup x with
    | none =>
      refine ⟨(x, g x) :: σ, by simp [matchT, hl], fun y u hy => ?_⟩
      by_cases e : y = x
      · subst e; simp at hy; exact hy
      · have : (y == x) = false := by simp [e]
        simp only [List.lookup, this] at hy
        exact hσ y u hy
    | some u =>
      have := hσ x u hl
      exact ⟨σ, by simp [matchT, hl, this], hσ⟩
  | σ, .f n as, hσ => by
    obtain ⟨σ', h1, h2⟩ := matchArgs_complete σ as hσ
    exact ⟨σ', by simp only [T.app, matchT, beq_self_eq_true, ↓reduceIte]; exact h1, h2⟩
theorem matchArgs_complete {g : String → T} : ∀ (σ : Subst) (as : List T),
    (∀ x u, σ.lookup x = some u → g x = u) →
    ∃ σ', matchArgs σ as (T.appArgs g as) = some σ' ∧ ∀ x u, σ'.lookup x = some u → g x = u
  | σ, [], hσ => ⟨σ, rfl, hσ⟩
  | σ, a :: as, hσ => by
    obtain ⟨σ₁, h1, h2⟩ := matchT_complete σ a hσ
    obtain ⟨σ₂, h3, h4⟩ := matchArgs_complete σ₁ as h2
    exact ⟨σ₂, by simp [T.appArgs, matchArgs, h1, h3], h4⟩
end

/-- No rule matches at the root when `rootRedex` finds none. -/
theorem rootRedex_complete {S : System} {t : T} (h : rootRedex S t = none) :
    ∀ ρ ∈ S.rules, ∀ g : String → T, ρ.lhs.app g ≠ t := by
  intro ρ hρ g e
  unfold rootRedex at h
  have := List.findSome?_eq_none_iff.1 h ρ hρ
  obtain ⟨σ', h1, -⟩ := matchT_complete (g := g) [] ρ.lhs (by simp)
  rw [e] at h1
  simp [h1] at this

theorem stepArgs_none {S : System} : ∀ (as : List T) (k : Nat), stepArgs S as k = none →
    ∀ (j : Nat) (a : T), as[j]? = some a → step S a = none
  | [], _, _, j, a, ha => by simp at ha
  | b :: as, k, h, j, a, ha => by
    simp only [stepArgs] at h
    split at h
    · cases h
    · rename_i hb
      rw [Option.map_eq_none_iff] at h
      cases j with
      | zero => simp at ha; subst ha; exact hb
      | succ j => exact stepArgs_none as (k + 1) h j a (by simpa using ha)

/-- When `step` finds no redex, there is none: no rule applies anywhere in the term. -/
theorem step_complete {S : System} : ∀ (p : Pos) {t : T}, step S t = none →
    ∀ ρ ∈ S.rules, ∀ g : String → T, t.at? p ≠ some (ρ.lhs.app g)
  | [], .v x, h, ρ, hρ, g, e => by
    simp only [step, Option.map_eq_none_iff] at h
    simp only [at?_nil, Option.some.injEq] at e
    exact rootRedex_complete h ρ hρ g e.symm
  | [], .f n as, h, ρ, hρ, g, e => by
    simp only [step] at h
    split at h
    · cases h
    · rename_i hr
      simp only [at?_nil, Option.some.injEq] at e
      exact rootRedex_complete hr ρ hρ g e.symm
  | _ :: _, .v x, _, _, _, _, e => by simp at e
  | i :: p, .f n as, h, ρ, hρ, g, e => by
    simp only [step] at h
    split at h
    · cases h
    · rw [Option.map_eq_none_iff] at h
      rw [at?_f, Option.bind_eq_some_iff] at e
      obtain ⟨a, ha, e⟩ := e
      exact step_complete p (stepArgs_none as 0 h i a ha) ρ hρ g e

/-- A term `step` finds no redex in is a normal form. -/
theorem normal_of_step {S : System} {t : T} (h : step S t = none) : Normal S t := by
  rintro u ⟨ρ, hρ, p, σ, ht, -⟩
  rw [subst_eq_app] at ht
  exact step_complete p h ρ hρ σ.fn ht

theorem Star.normal {S : System} {t u : T} (h : Star S t u) (ht : Normal S t) : u = t := by
  cases h with
  | refl => rfl
  | head h _ => exact absurd h (ht _)

theorem mem_critical_rules {S : System} {c : Critical} (h : c ∈ critical S) :
    c.outer ∈ S.rules ∧ c.inner ∈ S.rules := by
  simp only [critical, List.mem_flatMap] at h
  obtain ⟨⟨ρ₁, i⟩, h1, ⟨ρ₂, j⟩, h2, h⟩ := h
  simp only [criticalOf, List.mem_filterMap] at h
  obtain ⟨p, -, h⟩ := h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · simp only [Option.some.injEq] at h
          subst h
          exact ⟨List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 h1),
            List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 h2)⟩
        · cases h

/-- `critical(R)`'s "not confluent": a pair that `critical` reports, checked with `isPeak`, whose sides
reach two different normal forms, shows one term with two normal forms, so the system is not
confluent. -/
theorem critical_refutes {S : System} {c : Critical} (hc : c ∈ critical S) (hp : c.isPeak = true)
    (fuel : Nat) (hl : (normalize S c.left fuel).2.2 = true) (hr : (normalize S c.right fuel).2.2 = true)
    (ne : (normalize S c.left fuel).2.1 ≠ (normalize S c.right fuel).2.1) : ¬Confluent S := by
  intro hC
  obtain ⟨ho, hi⟩ := mem_critical_rules hc
  obtain ⟨⟨σ₁, e₁, e₂⟩, ⟨σ₂, e₃, e₄⟩⟩ := isPeak_sound hp
  have s₁ : Step S c.peak c.left := ⟨c.outer, ho, [], σ₁, by simp [e₁], by simp [e₂]⟩
  have s₂ : Step S c.peak c.right := ⟨c.inner, hi, c.pos, σ₂, e₃, e₄⟩
  obtain ⟨w, h₁, h₂⟩ := hC c.peak _ _ (.head s₁ (chain_star (normalize_chain S c.left fuel)))
    (.head s₂ (chain_star (normalize_chain S c.right fuel)))
  have e₁ := h₁.normal (normal_of_step (normalize_normal S c.left fuel hl))
  have e₂ := h₂.normal (normal_of_step (normalize_normal S c.right fuel hr))
  exact ne (e₁.symm.trans e₂)

/-- Newman's lemma: a locally confluent system with no infinite rewriting is confluent. -/
theorem newman_lemma {S : System} (hwf : WellFounded fun u t => Step S t u) (hl : LocallyConfluent S) :
    Confluent S := by
  intro t
  induction t using hwf.induction with
  | _ t ih =>
    intro a b ha hb
    cases ha with
    | refl => exact ⟨b, hb, .refl b⟩
    | head ha₁ ha₂ =>
      cases hb with
      | refl => exact ⟨_, .refl _, .head ha₁ ha₂⟩
      | head hb₁ hb₂ =>
        obtain ⟨w, hw₁, hw₂⟩ := hl _ _ _ ha₁ hb₁
        obtain ⟨v, hv₁, hv₂⟩ := ih _ ha₁ _ _ ha₂ hw₁
        obtain ⟨v', hv₁', hv₂'⟩ := ih _ hb₁ _ _ (hw₂.trans hv₂) hb₂
        exact ⟨v', hv₁.trans hv₁', hv₂'⟩

end TRS
end MathEngine
