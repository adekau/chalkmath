import MathEngine.Relation
/-!
# What is proved about relations

- `transitiveFailure_none`: when the check finds no counterexample, the relation is transitive.
- `round_sub_transitive`: a round of transitive closure adds only pairs that every transitive relation
  containing the original has; so does every round after it (`transClosure_sub`), and the closure is
  inside every transitive relation containing the original.
- `stable_transitive`: when a round adds nothing, the relation is transitive. The closure stops
  exactly then (`transClosure` reports it), so it is the least transitive relation containing the
  original.
-/
namespace MathEngine
namespace Ord

/-- A relation (as its pair list) is transitive. -/
def Transitive (ps : List (String × String)) : Prop :=
  ∀ x y z, (x, y) ∈ ps → (y, z) ∈ ps → (x, z) ∈ ps

theorem Rel.has_iff (R : Rel) (x y : String) : R.has x y = true ↔ (x, y) ∈ R.pairs := by
  simp [Rel.has, List.contains_iff_mem]

theorem transitiveFailure_none (R : Rel) (h : transitiveFailure R = none) : Transitive R.pairs := by
  intro x y z hxy hyz
  unfold transitiveFailure at h
  have h1 := List.findSome?_eq_none_iff.mp h (x, y) hxy
  simp only [Option.map_eq_none_iff, List.find?_eq_none] at h1
  have h2 := h1 (y, z) hyz
  simp only [beq_self_eq_true, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at h2
  simpa [Rel.has_iff] using h2

/-- Every pair a round adds is in every transitive relation containing the original. -/
theorem round_sub_transitive (R : Rel) (T : List (String × String)) (hT : Transitive T)
    (hsub : ∀ p ∈ R.pairs, p ∈ T) : ∀ p ∈ R.round, p ∈ T := by
  intro p hp
  simp only [Rel.round, List.mem_flatMap, List.mem_filterMap] at hp
  obtain ⟨⟨a, b⟩, hab, ⟨c, d⟩, hcd, hsome⟩ := hp
  split at hsome
  · rename_i hcond
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    obtain ⟨hbc, _⟩ := hcond
    subst hbc
    cases hsome
    exact hT a b d (hsub _ hab) (hsub _ hcd)
  · cases hsome

/-- The closure, whatever its rounds, stays inside every transitive relation containing the original. -/
theorem transClosure_go_sub (T : List (String × String)) (hT : Transitive T) :
    ∀ (n : Nat) (R : Rel) (acc : List (List (String × String))), (∀ p ∈ R.pairs, p ∈ T) →
      ∀ p ∈ (transClosure.go n R acc).1.pairs, p ∈ T := by
  intro n
  induction n with
  | zero => intro R acc h; simpa [transClosure.go] using h
  | succ n ih =>
    intro R acc h
    simp only [transClosure.go]
    split
    · simpa using h
    · apply ih
      intro p hp
      simp only [List.mem_append] at hp
      rcases hp with hp | hp
      · exact h p hp
      · exact round_sub_transitive R T hT h p (List.mem_eraseDups.mp hp)

theorem transClosure_sub (R : Rel) (T : List (String × String)) (hT : Transitive T)
    (hsub : ∀ p ∈ R.pairs, p ∈ T) : ∀ p ∈ (transClosure R).1.pairs, p ∈ T :=
  transClosure_go_sub T hT _ R [] hsub

/-- A relation a round adds nothing to is transitive. -/
theorem stable_transitive (R : Rel) (h : R.round = []) : Transitive R.pairs := by
  intro x y z hxy hyz
  by_cases hxz : (x, z) ∈ R.pairs
  · exact hxz
  exfalso
  have : (x, z) ∈ R.round := by
    simp only [Rel.round, List.mem_flatMap, List.mem_filterMap]
    refine ⟨(x, y), hxy, (y, z), hyz, ?_⟩
    have : R.has x z = false := by
      cases hh : R.has x z
      · rfl
      · exact absurd ((Rel.has_iff R x z).mp hh) hxz
    simp [this]
  rw [h] at this
  simp at this

/-- The closure the engine returns is transitive whenever it reports it settled. -/
theorem transClosure_transitive : ∀ (n : Nat) (R : Rel) (acc : List (List (String × String))),
    (transClosure.go n R acc).2.2 = true → Transitive (transClosure.go n R acc).1.pairs := by
  intro n
  induction n with
  | zero => intro R acc h; simp only [transClosure.go, List.isEmpty_iff] at h ⊢; exact stable_transitive R h
  | succ n ih =>
    intro R acc h
    by_cases hemp : R.round.eraseDups.isEmpty = true
    · simp only [transClosure.go, hemp, if_true] at h ⊢
      simp only [List.isEmpty_iff] at hemp
      apply stable_transitive
      -- no new pair: the round adds nothing
      cases hr : R.round with
      | nil => rfl
      | cons p ps =>
        have : p ∈ R.round.eraseDups := List.mem_eraseDups.mpr (by rw [hr]; simp)
        rw [hemp] at this; simp at this
    · simp only [transClosure.go, hemp] at h ⊢
      exact ih _ _ h

end Ord
end MathEngine
