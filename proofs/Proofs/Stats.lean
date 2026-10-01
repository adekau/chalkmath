import Proofs.SimpReal
/-!
# Statistics over ℝ (and ℚ)

The `stat.*` rules (`engine/MathEngine/LinAlg.lean`) rewrite a statistic of a vector into a term;
here that term gets its meaning. `total` and `mean` are definitions, read as the list's sum and the
sum over the count. The variance is the one claim with content: the engine writes it in the
one-pass form `(Σxᵢ² − (Σxᵢ)²/n)/(n − 1)`, linear in `n`, and `variance_soundR` proves that equal to
the definition `Σ(xᵢ − x̄)²/(n − 1)`, the sample variance. `min`, `max` and `median` compare exact
rationals: the result is an entry and none is smaller (`minQ_spec`), or the middle of the entries
sorted (`medianQ_spec`).
-/
noncomputable section
namespace MathProofs
open MathEngine

theorem sumR_eq_list_sum (ρ : EnvR) : ∀ xs : List Expr, sumR ρ xs = (xs.map (evalR ρ)).sum
  | [] => rfl
  | x :: xs => by simp [sumR_eq_list_sum ρ xs]

/-- **`total`**: the value is the sum of the entries' values. -/
theorem total_soundR (ρ : EnvR) (xs : List Expr) : evalR ρ (totalOf xs) = (xs.map (evalR ρ)).sum := by
  simp [totalOf, sumR_eq_list_sum]

/-- **`mean`**: the value is the sum of the entries' values over their count. -/
theorem mean_soundR (ρ : EnvR) (xs : List Expr) :
    evalR ρ (meanOf xs) = (xs.map (evalR ρ)).sum / xs.length := by
  simp [meanOf, sumR_eq_list_sum, Q.ofRat]
  ring

/-- The sample variance of real numbers, by its definition: the squared deviations from the mean,
summed, over `n − 1`. -/
def sampleVariance (v : List ℝ) : ℝ :=
  (v.map fun x => (x - v.sum / v.length) ^ 2).sum / (v.length - 1)

/-- Σ(xᵢ − c)² = Σxᵢ² − 2cΣxᵢ + nc², for any `c`: the square expanded, term by term. -/
theorem sum_sq_sub (v : List ℝ) (c : ℝ) :
    (v.map fun x => (x - c) ^ 2).sum = (v.map (· ^ 2)).sum - 2 * c * v.sum + v.length * c ^ 2 := by
  induction v with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring

/-- The squared deviations from the mean sum to `Σxᵢ² − (Σxᵢ)²/n`. -/
theorem sum_sq_dev (v : List ℝ) :
    (v.map fun x => (x - v.sum / v.length) ^ 2).sum = (v.map (· ^ 2)).sum - v.sum ^ 2 / v.length := by
  by_cases hv : v = []
  · subst hv; simp
  have hn : (v.length : ℝ) ≠ 0 := by simpa using hv
  rw [sum_sq_sub]
  field_simp
  ring

/-- **`variance`**: the one-pass form the engine writes is the sample variance. -/
theorem variance_soundR (ρ : EnvR) (xs : List Expr) :
    evalR ρ (varianceOf xs) = sampleVariance (xs.map (evalR ρ)) := by
  rw [sampleVariance, sum_sq_dev]
  simp [varianceOf, sumR_eq_list_sum, Q.ofRat, List.map_map, Function.comp_def, Real.rpow_two]
  rcases (xs.length : ℝ).eq_or_ne 1 with h1 | h1
  · simp [h1]
  · have : (xs.length : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr h1
    field_simp
    ring

/-- **`stdev`**: the square root of the sample variance. -/
theorem stdev_soundR (ρ : EnvR) (xs : List Expr) :
    evalR ρ (stdevOf xs) = Real.sqrt (sampleVariance (xs.map (evalR ρ))) := by
  rw [stdevOf, evalR_pow, ← variance_soundR, Real.sqrt_eq_rpow]
  simp [Q.ofRat]

/-! ## Comparisons, over ℚ -/

theorem foldl_min (qs : List Q) : ∀ acc : Q,
    qs.foldl (fun m x => if x.val < m.val then x else m) acc ∈ acc :: qs ∧
      ∀ x ∈ acc :: qs, (qs.foldl (fun m x => if x.val < m.val then x else m) acc).val ≤ x.val := by
  induction qs with
  | nil => intro acc; simp
  | cons y ys ih =>
    intro acc
    obtain ⟨hmem, hle⟩ := ih (if y.val < acc.val then y else acc)
    simp only [List.foldl_cons]
    have ha : (if y.val < acc.val then y else acc) = y ∨ (if y.val < acc.val then y else acc) = acc := by
      split <;> simp
    refine ⟨?_, ?_⟩
    · rcases List.mem_cons.mp hmem with h | h
      · rcases ha with h' | h' <;> rw [h, h'] <;> simp
      · simp [h]
    · have hstep : (if y.val < acc.val then y else acc).val ≤ y.val ∧ (if y.val < acc.val then y else acc).val ≤ acc.val := by
        split
        · rename_i h; exact ⟨le_refl _, le_of_lt h⟩
        · rename_i h; exact ⟨le_of_not_gt h, le_refl _⟩
      have hhead := hle _ List.mem_cons_self
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact le_trans hhead hstep.2
      · exact le_trans hhead hstep.1
      · exact hle x (List.mem_cons_of_mem _ hx)

theorem foldl_max (qs : List Q) : ∀ acc : Q,
    qs.foldl (fun m x => if m.val < x.val then x else m) acc ∈ acc :: qs ∧
      ∀ x ∈ acc :: qs, x.val ≤ (qs.foldl (fun m x => if m.val < x.val then x else m) acc).val := by
  induction qs with
  | nil => intro acc; simp
  | cons y ys ih =>
    intro acc
    obtain ⟨hmem, hle⟩ := ih (if acc.val < y.val then y else acc)
    simp only [List.foldl_cons]
    have ha : (if acc.val < y.val then y else acc) = y ∨ (if acc.val < y.val then y else acc) = acc := by
      split <;> simp
    refine ⟨?_, ?_⟩
    · rcases List.mem_cons.mp hmem with h | h
      · rcases ha with h' | h' <;> rw [h, h'] <;> simp
      · simp [h]
    · have hstep : y.val ≤ (if acc.val < y.val then y else acc).val ∧ acc.val ≤ (if acc.val < y.val then y else acc).val := by
        split
        · rename_i h; exact ⟨le_refl _, le_of_lt h⟩
        · rename_i h; exact ⟨le_of_not_gt h, le_refl _⟩
      have hhead := hle _ List.mem_cons_self
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact le_trans hstep.2 hhead
      · exact le_trans hstep.1 hhead
      · exact hle x (List.mem_cons_of_mem _ hx)

/-- **`min`**: the result is an entry, and no entry is smaller. -/
theorem minQ_spec {qs : List Q} {m : Q} (h : minQ qs = some m) : m ∈ qs ∧ ∀ q ∈ qs, m.val ≤ q.val := by
  cases qs with
  | nil => simp [minQ] at h
  | cons q qs => simp only [minQ, Option.some.injEq] at h; subst h; exact foldl_min qs q

/-- **`max`**: the result is an entry, and no entry is larger. -/
theorem maxQ_spec {qs : List Q} {m : Q} (h : maxQ qs = some m) : m ∈ qs ∧ ∀ q ∈ qs, q.val ≤ m.val := by
  cases qs with
  | nil => simp [maxQ] at h
  | cons q qs => simp only [maxQ, Option.some.injEq] at h; subst h; exact foldl_max qs q

/-- **`median`**: the entries in a sorted order (a permutation of them, each at most the next), and
the result its middle entry, or the mean of its two middle entries. -/
theorem medianQ_spec {qs : List Q} {m : Q} (h : medianQ qs = some m) :
    ∃ s : List Q, s.Perm qs ∧ s.Pairwise (fun a b => a.val ≤ b.val) ∧
      ((qs.length % 2 = 1 ∧ s[qs.length / 2]? = some m) ∨
       (qs.length % 2 = 0 ∧ ∃ a b, s[qs.length / 2 - 1]? = some a ∧ s[qs.length / 2]? = some b ∧ m = (a + b) / Q.ofInt 2)) := by
  have hsorted : (sortQ qs).Pairwise (fun a b => decide (a.val ≤ b.val)) :=
    List.pairwise_mergeSort
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) qs
  refine ⟨sortQ qs, List.mergeSort_perm qs _, hsorted.imp (by simp), ?_⟩
  unfold medianQ at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · rename_i hodd; left; exact ⟨by simpa using hodd, h⟩
    · rename_i hz hodd
      right
      refine ⟨by simp at hz hodd; omega, ?_⟩
      split at h
      · rename_i a b ha hb
        simp only [Option.some.injEq] at h
        exact ⟨a, b, ha, hb, h.symm⟩
      · simp at h

end MathProofs
