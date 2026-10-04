import Proofs.Expand
/-!
# `factor`: the answer agrees with the input wherever its denominator is not zero

`Factor.run` combines the normal form `e` over a common denominator `D` and keeps the combined form
`out` only if `out · D` and `e · D`, each normalized, expanded and normalized, are the same term.
`factor_run_sound` reads that as `out = a` at every point where the checker's normalizations hold and
`D ≠ 0`. The condition is needed: `factor(1/x + 1)` is `(x + 1)/x`, and at `x = 0` the two differ
(`not_factor_at_zero`, with Lean's `1/0 = 0`: the input is 1 and the answer 0). Expanding the answer
again gives the input's value back under the same conditions (`expand_factor_sound`), but not, in
general, its term.
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Expr

theorem sumR_mulDen (ρ : EnvR) (den : Expr) : ∀ l : List Expr,
    sumR ρ (l.map fun t => mulN (unMul t ++ unMul den)) = sumR ρ l * evalR ρ den
  | [] => by simp
  | t :: l => by
    simp only [List.map_cons, sumR_cons, evalR_mulN, prodR_append, prodR_unMul, sumR_mulDen ρ den l]
    ring

/-- **`cmd.factor`'s claim.** Where the normalizations the check ran preserve the value at `ρ`, and
the denominator is not zero there, the answer is the input. -/
theorem factor_run_sound (norm : Expr → Except String Expr) {a out den : Expr}
    (h : Factor.run norm a = .ok (out, true, den)) (ρ : EnvR)
    (hn : ∀ x y, norm x = .ok y → evalR ρ x = evalR ρ y) (hD : evalR ρ den ≠ 0) :
    evalR ρ out = evalR ρ a := by
  unfold Factor.run at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i e he
    rcases hc : Factor.combineParts ((unAdd e).map Factor.termOf) with ⟨out₀, numer₀, den₀⟩
    simp only [hc] at h
    split at h
    · cases h
    · rename_i l₁ hl₁
      split at h
      · cases h
      · rename_i lhs hlhs
        split at h
        · cases h
        · rename_i r₁ hr₁
          split at h
          · cases h
          · rename_i rhs hrhs
            split at h
            · rename_i heq
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -, rfl⟩ := h
              have hlr := Expr.equal_eq heq
              subst hlr
              -- both sides, times `D`, have the same value
              have hL : evalR ρ lhs = evalR ρ a * evalR ρ den₀ := by
                rw [← hn _ _ hlhs, dist_sound, ← hn _ _ hl₁, evalR_addN, sumR_mulDen, sumR_unAdd,
                  ← hn _ _ he, dist_sound]
              have hR : evalR ρ lhs = evalR ρ out₀ * evalR ρ den₀ := by
                rw [← hn _ _ hrhs, dist_sound, ← hn _ _ hr₁, evalR_mulN, prodR_append, prodR_unMul,
                  prodR_unMul]
              exact mul_right_cancel₀ hD (hR.symm.trans hL)
            · cases h

/-- **`expand` undoes `factor`, up to value.** `cmd.expand` distributes (`Expand.dist`) and the
pipeline collects; doing that to `factor`'s answer gives back the input's value, under the same
conditions as `factor_run_sound`. Not its term: `expand` leaves a negative power of a sum as it is, so
`expand(factor(e))` keeps everything over `D` where `e` had terms over parts of it. -/
theorem expand_factor_sound (norm : Expr → Except String Expr) {a out den r : Expr}
    (h : Factor.run norm a = .ok (out, true, den)) (ρ : EnvR)
    (hn : ∀ x y, norm x = .ok y → evalR ρ x = evalR ρ y) (hD : evalR ρ den ≠ 0)
    (hr : norm (Expand.dist out) = .ok r) :
    evalR ρ r = evalR ρ a := by
  rw [← hn _ _ hr, dist_sound, factor_run_sound norm h ρ hn hD]

/-- The condition is needed: `factor(1/x + 1)` is `(x + 1)/x` (`engine/Tests`), and at `x = 0`, where
the denominator is zero, the input is 1 and the answer 0. -/
theorem not_factor_at_zero :
    evalR (fun _ => 0) (.add [.pow (.var "x") (.num (Q.ofInt (-1))), Expr.one]) ≠
      evalR (fun _ => 0) (.mul [.add [.var "x", Expr.one], .pow (.var "x") (.num (Q.ofInt (-1)))]) := by
  simp [Q.ofInt, Expr.one, Q.one]

end MathProofs
end
