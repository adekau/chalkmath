import MathEngine.Stlc
/-!
# The type checker is sound

`HasType Γ t T` is the simply typed λ-calculus's typing relation, one constructor per rule:

    (Var)  x : T ∈ Γ  ⟹  Γ ⊢ x : T
    (→I)   Γ, x : A ⊢ e : B  ⟹  Γ ⊢ λx:A. e : A → B
    (→E)   Γ ⊢ f : A → B  and  Γ ⊢ a : A  ⟹  Γ ⊢ f a : B

`check_sound`: whatever type the checker returns, the term has it. So the `stlc.*` steps a `type:`
cell shows are verified, and so is the type `infer:` reports, since inference ends by running the
checker on the term annotated with its answer. (That the answer is the *most general* type is
Hindley's theorem, not proved here.)
-/
namespace MathEngine
namespace Lam

inductive HasType : Ctx → ATerm → Ty → Prop where
  | var {Γ x T} : Γ.lookup x = some T → HasType Γ (.var x) T
  | abs {Γ x A e B} : HasType ((x, A) :: Γ) e B → HasType Γ (.lam x (some A) e) (.arrow A B)
  | app {Γ f a A B} : HasType Γ f (.arrow A B) → HasType Γ a A → HasType Γ (.app f a) B

theorem check_sound : ∀ (t : ATerm) (Γ : Ctx) (d : Deriv) (T : Ty),
    check Γ t = .ok (d, T) → HasType Γ t T
  | .var x, Γ, d, T, h => by
    unfold check at h
    split at h
    · rename_i T' hT
      cases h
      exact .var hT
    · cases h
  | .lam x none e, Γ, d, T, h => by
    unfold check at h; cases h
  | .lam x (some A) e, Γ, d, T, h => by
    unfold check at h
    split at h
    · rename_i d' B he
      cases h
      exact .abs (check_sound e _ d' B he)
    · cases h
  | .app f a, Γ, d, T, h => by
    unfold check at h
    split at h
    · cases h
    · rename_i df F hf
      split at h
      · cases h
      · rename_i da A' ha
        split at h
        · rename_i A B
          split at h
          · rename_i hA
            cases h
            subst hA
            exact .app (check_sound f _ df _ hf) (check_sound a _ da _ ha)
          · cases h
        · cases h

/-- The checker's types are unique: a term has at most one type in a context. -/
theorem HasType.unique {Γ : Ctx} {t : ATerm} {T U : Ty} (h₁ : HasType Γ t T) (h₂ : HasType Γ t U) : T = U := by
  induction h₁ generalizing U with
  | var h => cases h₂ with | var h' => rw [h] at h'; exact Option.some.inj h'
  | abs _ ih => cases h₂ with | abs h' => rw [ih h']
  | app _ _ ihf _ => cases h₂ with | app hf' _ => cases ihf hf'; rfl

end Lam
end MathEngine
