import Proofs.Fourier
/-!
# A cell means its source, with the session's names bound

Before a cell is normalized, the session's `let` bindings are substituted into it (`substitute`,
`Session.evaluateCell`), so the derivation's input is the source with each bound name replaced by
the term it was bound to. `substitute_soundR` (and `substitute_soundC` over ℂ) say that is the
source's meaning where each name has its binding's value: the substitution is all at once, and
there are no binders in the scalar language to capture anything.
-/
noncomputable section
namespace MathProofs
open MathEngine

/-- The environment where each bound name has its binding's value. -/
def bindR (ρ : EnvR) (bs : List (String × Expr)) : EnvR := fun y =>
  match bs.lookup y with
  | some v => evalR ρ v
  | none => ρ y

def bindC (ρ : EnvC) (bs : List (String × Expr)) : EnvC := fun y =>
  match bs.lookup y with
  | some v => evalC ρ v
  | none => ρ y

mutual
  /-- **Substitution is evaluation in the bound environment**, over ℝ. -/
  theorem substitute_soundR (ρ : EnvR) (bs : List (String × Expr)) :
      ∀ e : Expr, evalR ρ (substitute bs e) = evalR (bindR ρ bs) e
    | .num _ => rfl
    | .var y => by
      simp only [substitute, evalR_var, bindR]
      cases bs.lookup y <;> rfl
    | .add es => by simp only [substitute, evalR_add]; exact substituteList_sumR ρ bs es
    | .mul es => by simp only [substitute, evalR_mul]; exact substituteList_prodR ρ bs es
    | .pow b e => by simp only [substitute, evalR_pow, substitute_soundR ρ bs b, substitute_soundR ρ bs e]
    | .fn f es => by
      simp only [substitute]
      match es with
      | [] => rfl
      | [a] => simp only [substituteList, evalR_fn₁, substitute_soundR ρ bs a]
      | _ :: _ :: _ => simp [substituteList, evalR]
    | .matrix _ => rfl
  theorem substituteList_sumR (ρ : EnvR) (bs : List (String × Expr)) :
      ∀ es : List Expr, sumR ρ (substituteList bs es) = sumR (bindR ρ bs) es
    | [] => rfl
    | e :: es => by simp only [substituteList, sumR_cons, substitute_soundR ρ bs e, substituteList_sumR ρ bs es]
  theorem substituteList_prodR (ρ : EnvR) (bs : List (String × Expr)) :
      ∀ es : List Expr, prodR ρ (substituteList bs es) = prodR (bindR ρ bs) es
    | [] => rfl
    | e :: es => by simp only [substituteList, prodR_cons, substitute_soundR ρ bs e, substituteList_prodR ρ bs es]
end

mutual
  /-- **Substitution is evaluation in the bound environment**, over ℂ. -/
  theorem substitute_soundC (ρ : EnvC) (bs : List (String × Expr)) :
      ∀ e : Expr, evalC ρ (substitute bs e) = evalC (bindC ρ bs) e
    | .num _ => rfl
    | .var y => by
      simp only [substitute, evalC_var, bindC]
      cases bs.lookup y <;> rfl
    | .add es => by simp only [substitute, evalC_add]; exact substituteList_sumC ρ bs es
    | .mul es => by simp only [substitute, evalC_mul]; exact substituteList_prodC ρ bs es
    | .pow b e => by simp only [substitute, evalC_pow, substitute_soundC ρ bs b, substitute_soundC ρ bs e]
    | .fn f es => by
      simp only [substitute]
      match es with
      | [] => rfl
      | [a] => simp only [substituteList, evalC_fn₁, substitute_soundC ρ bs a]
      | _ :: _ :: _ => simp [substituteList, evalC]
    | .matrix _ => rfl
  theorem substituteList_sumC (ρ : EnvC) (bs : List (String × Expr)) :
      ∀ es : List Expr, sumC ρ (substituteList bs es) = sumC (bindC ρ bs) es
    | [] => rfl
    | e :: es => by simp only [substituteList, sumC_cons, substitute_soundC ρ bs e, substituteList_sumC ρ bs es]
  theorem substituteList_prodC (ρ : EnvC) (bs : List (String × Expr)) :
      ∀ es : List Expr, prodC ρ (substituteList bs es) = prodC (bindC ρ bs) es
    | [] => rfl
    | e :: es => by simp only [substituteList, prodC_cons, substitute_soundC ρ bs e, substituteList_prodC ρ bs es]
end

end MathProofs
end
