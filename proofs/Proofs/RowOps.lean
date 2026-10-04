import Proofs.SimpReal
/-!
# Symbolic row operations keep the solution set, over ℝ

`rref` on a matrix with symbolic entries (`rrefSymbolic`, `LinAlg.lean`) records each row operation
as the exact operation on the entries (`swapRows`, `scaleRowExact`, `addRowExact`) followed by the
simplifier on the row it changed. Read at a point `ρ`, a matrix of expressions is a matrix of real
numbers (`valRows`), and a matrix is a homogeneous system, one equation `r · x = 0` per row, as for
the verified rational path (`LinQ.Sol`, `LinAlgQ.lean`). Here each exact operation is proved to keep
the solution set:

- `swapRows_soundR`: always;
- `scaleRowExact_soundR`: where the pivot is not zero, which the step states as its assumption;
- `addRowExact_soundR`: always (rows of one length, as a matrix literal's are).

The simplifier then rewrites the row's entries. Where it used only the rules that assume nothing, the
entries keep their value at every point (`normalizeSafe_sound`, `SimpAll.lean`) and the step is
`la.row-add.symbolic`; where it used one that assumes (`collectPowersAssuming_soundR_on`,
`functionAssuming_soundR_on`), the step says what it assumed and is `la.row-add.symbolic.assuming`.
-/
noncomputable section
namespace MathProofs
open MathEngine

/-- The linear form of a row at a point; a missing coefficient or coordinate counts as 0. -/
def dotR : List ℝ → List ℝ → ℝ
  | a :: as, x :: xs => a * x + dotR as xs
  | _, _ => 0

/-- `x` solves every equation of the matrix. -/
def SolR (m : List (List ℝ)) (x : List ℝ) : Prop := ∀ r ∈ m, dotR r x = 0

/-- A matrix of expressions read at `ρ`. -/
def valRows (ρ : EnvR) (rows : List (List Expr)) : List (List ℝ) := rows.map (·.map (evalR ρ))

theorem solR_iff (m : List (List ℝ)) (x : List ℝ) :
    SolR m x ↔ ∀ (k : ℕ) r, m[k]? = some r → dotR r x = 0 := by
  constructor
  · intro h k r hk; exact h r (List.mem_of_getElem? hk)
  · intro h r hr; obtain ⟨k, hk⟩ := List.getElem?_of_mem hr; exact h k r hk

/-- Changing one row keeps the solution set when, given the other equations, the new row's equation
holds exactly where the old one's does. -/
theorem solR_set {m : List (List ℝ)} {i : ℕ} {r r' : List ℝ} {x : List ℝ} (hi : m[i]? = some r)
    (h : (∀ k s, k ≠ i → m[k]? = some s → dotR s x = 0) → (dotR r' x = 0 ↔ dotR r x = 0)) :
    SolR (m.set i r') x ↔ SolR m x := by
  have hil : i < m.length := (List.getElem?_eq_some_iff.mp hi).1
  have get : ∀ k, (m.set i r')[k]? = if k = i then some r' else m[k]? := by
    intro k
    by_cases hk : k = i
    · subst hk; simp [List.getElem?_set_self hil]
    · simp [List.getElem?_set_ne (Ne.symm hk), hk]
  rw [solR_iff, solR_iff]
  constructor
  · intro H k s hk
    have others : ∀ k s, k ≠ i → m[k]? = some s → dotR s x = 0 := fun k s hne hks =>
      H k s (by rw [get, if_neg hne]; exact hks)
    by_cases hki : k = i
    · subst hki
      rw [hi] at hk
      cases hk
      exact (h others).mp (H k r' (by rw [get, if_pos rfl]))
    · exact others k s hki hk
  · intro H k s hk
    rw [get] at hk
    by_cases hki : k = i
    · rw [if_pos hki] at hk
      cases hk
      exact (h fun k s _ hks => H k s hks).mpr (H i r hi)
    · rw [if_neg hki] at hk
      exact H k s hk

/-- Exchanging two rows keeps the rows, so the solution set. -/
theorem solR_swap (m : List (List ℝ)) (i j : ℕ) (hi : i < m.length) (hj : j < m.length) (x : List ℝ) :
    SolR ((m.set i m[j]).set j m[i]) x ↔ SolR m x := by
  have mem : ∀ r, r ∈ (m.set i m[j]).set j m[i] ↔ r ∈ m := by
    intro r
    constructor
    · intro hr
      rcases List.mem_or_eq_of_mem_set hr with hr | rfl
      · rcases List.mem_or_eq_of_mem_set hr with hr | rfl
        · exact hr
        · exact List.getElem_mem hj
      · exact List.getElem_mem hi
    · intro hr
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
      have hl : ((m.set i m[j]).set j m[i]).length = m.length := by simp
      by_cases hki : k = i
      · subst hki
        have : ((m.set k m[j]).set j m[k])[j]'(by rw [hl]; exact hj) = m[k] := by simp
        have hm := List.getElem_mem (l := (m.set k m[j]).set j m[k]) (by rw [hl]; exact hj)
        rw [this] at hm; exact hm
      · by_cases hkj : k = j
        · subst hkj
          have : ((m.set i m[k]).set k m[i])[i]'(by rw [hl]; exact hi) = m[k] := by
            simp [List.getElem_set, Ne.symm hki, hki]
          have hm := List.getElem_mem (l := (m.set i m[k]).set k m[i]) (by rw [hl]; exact hi)
          rw [this] at hm; exact hm
        · have : ((m.set i m[j]).set j m[i])[k]'(by rw [hl]; exact hk) = m[k] := by
            simp [List.getElem_set, Ne.symm hki, Ne.symm hkj]
          have hm := List.getElem_mem (l := (m.set i m[j]).set j m[i]) (by rw [hl]; exact hk)
          rw [this] at hm; exact hm
  constructor
  · intro h r hr; exact h r ((mem r).mpr hr)
  · intro h r hr; exact h r ((mem r).mp hr)

theorem valRows_getElem? (ρ : EnvR) (rows : List (List Expr)) {i : ℕ} (hi : i < rows.length) :
    (valRows ρ rows)[i]? = some ((rows.getD i []).map (evalR ρ)) := by
  simp [valRows, List.getD_eq_getElem?_getD, hi]

theorem valRows_set (ρ : EnvR) (rows : List (List Expr)) (i : ℕ) (r : List Expr) :
    valRows ρ (rows.set i r) = (valRows ρ rows).set i (r.map (evalR ρ)) := by
  simp [valRows, List.map_set]

/-- **`la.row-swap.symbolic`.** Exchanging two rows keeps the solution set, at every point. -/
theorem swapRows_soundR (ρ : EnvR) (rows : List (List Expr)) {i j : ℕ} (hi : i < rows.length)
    (hj : j < rows.length) (x : List ℝ) :
    SolR (valRows ρ (swapRows rows i j)) x ↔ SolR (valRows ρ rows) x := by
  have hi' : i < (valRows ρ rows).length := by simpa [valRows] using hi
  have hj' : j < (valRows ρ rows).length := by simpa [valRows] using hj
  have : valRows ρ (swapRows rows i j) = ((valRows ρ rows).set i (valRows ρ rows)[j]).set j (valRows ρ rows)[i] := by
    simp [swapRows, valRows, List.map_set, List.getD_eq_getElem?_getD, hi, hj]
  rw [this]
  exact solR_swap _ i j hi' hj' x

theorem evalR_div (ρ : EnvR) (a p : Expr) : evalR ρ (Expr.div a p) = evalR ρ a * (evalR ρ p)⁻¹ := by
  simp [Expr.div, Expr.minusOne, prodR, Q.minusOne, Q_val_ofInt, Real.rpow_neg_one]

theorem evalR_sub_mul (ρ : EnvR) (a f b : Expr) :
    evalR ρ (Expr.sub a (.mul [f, b])) = evalR ρ a - evalR ρ f * evalR ρ b := by
  simp [Expr.sub, Expr.neg, Expr.minusOne, sumR, prodR, Q.minusOne, Q_val_ofInt]
  ring

theorem dotR_scale (ρ : EnvR) (p : Expr) :
    ∀ (r : List Expr) (x : List ℝ),
      dotR ((r.map fun a => Expr.div a p).map (evalR ρ)) x = (evalR ρ p)⁻¹ * dotR (r.map (evalR ρ)) x
  | [], x => by simp [dotR]
  | _ :: _, [] => by simp [dotR]
  | a :: r, y :: x => by
    simp only [List.map_cons, dotR, evalR_div, dotR_scale ρ p r x]
    ring

theorem dotR_addRow (ρ : EnvR) (f : Expr) :
    ∀ (ri rj : List Expr) (x : List ℝ), ri.length = rj.length →
      dotR (((ri.zip rj).map fun (a, b) => Expr.sub a (.mul [f, b])).map (evalR ρ)) x =
        dotR (ri.map (evalR ρ)) x - evalR ρ f * dotR (rj.map (evalR ρ)) x
  | [], [], x, _ => by simp [dotR]
  | _ :: _, _ :: _, [], _ => by simp [dotR]
  | a :: ri, b :: rj, y :: x, h => by
    simp only [List.zip_cons_cons, List.map_cons, dotR, evalR_sub_mul,
      dotR_addRow ρ f ri rj x (by simpa using h)]
    ring
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h

/-- **`la.row-scale.symbolic`.** Dividing a row by the pivot keeps the solution set wherever the
pivot is not zero. -/
theorem scaleRowExact_soundR (ρ : EnvR) (rows : List (List Expr)) {i : ℕ} (p : Expr)
    (hi : i < rows.length) (hp : evalR ρ p ≠ 0) (x : List ℝ) :
    SolR (valRows ρ (scaleRowExact rows i p)) x ↔ SolR (valRows ρ rows) x := by
  rw [scaleRowExact, valRows_set]
  refine solR_set (valRows_getElem? ρ rows hi) fun _ => ?_
  rw [dotR_scale]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero hp)
  · intro h; rw [h, mul_zero]

/-- **`la.row-add.symbolic`.** Subtracting a multiple of another row keeps the solution set, at every
point. -/
theorem addRowExact_soundR (ρ : EnvR) (rows : List (List Expr)) {i j : ℕ} (f : Expr) (hij : i ≠ j)
    (hi : i < rows.length) (hj : j < rows.length)
    (hlen : (rows.getD i []).length = (rows.getD j []).length) (x : List ℝ) :
    SolR (valRows ρ (addRowExact rows i j f)) x ↔ SolR (valRows ρ rows) x := by
  rw [addRowExact, valRows_set]
  refine solR_set (valRows_getElem? ρ rows hi) fun others => ?_
  rw [dotR_addRow ρ f _ _ x hlen, others j _ (Ne.symm hij) (valRows_getElem? ρ rows hj), mul_zero, sub_zero]

end MathProofs
