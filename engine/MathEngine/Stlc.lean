import MathEngine.Lambda
/-!
# The simply typed λ-calculus

`type: Γ ⊢ t` checks a term whose every binder has a type, building the derivation tree with the three
rules (Var, →I, →E); `StlcProofs.lean` proves that a tree the checker returns is a typing
derivation. `infer: Γ ⊢ t` finds a type for a term whose binders need not be annotated: every missing
type and every application's result gets a type variable, each application gives an equation, and the
equations are solved one at a time by unification (Robinson's, with the occurs check, which is what
rejects `λx. x x`). What inference finds is not taken on trust: the term, annotated with the solution,
goes back through the checker. `StlcPrincipal.lean` proves it the most general type.
-/
namespace MathEngine
namespace Lam

/-- A typing derivation: the rule, the judgment `Γ ⊢ t : T`, and the derivations of its premises. -/
inductive Deriv where
  | node (rule : String) (Γ : Ctx) (t : ATerm) (T : Ty) (premises : List Deriv)
  deriving Inhabited

def Ty.text (T : Ty) : String := T.toExpr.toText
def ATerm.text (t : ATerm) : String := t.toExpr.toText

/-- Check `t` in `Γ`: its type and the derivation, or why it has none. -/
def check (Γ : Ctx) : ATerm → Except String (Deriv × Ty)
  | .var x =>
    match Γ.lookup x with
    | some T => .ok (.node "var" Γ (.var x) T [], T)
    | none => .error s!"{x} is free and has no type: give it one in the context, as in `{x} : A ⊢ …`"
  | .lam x none _ => .error s!"the binder {x} has no type: write λ{x}:A. … (or ask `infer:` to find one)"
  | .lam x (some A) e =>
    match check ((x, A) :: Γ) e with
    | .ok (d, B) => .ok (.node "abs" Γ (.lam x (some A) e) (.arrow A B) [d], .arrow A B)
    | .error m => .error m
  | .app f a =>
    match check Γ f with
    | .error m => .error m
    | .ok (df, F) =>
      match check Γ a with
      | .error m => .error m
      | .ok (da, A') =>
        match F with
        | .arrow A B =>
          if A = A' then .ok (.node "app" Γ (.app f a) B [df, da], B)
          else .error s!"{f.text} expects an argument of type {A.text}, but {a.text} has type {A'.text}"
        | _ => .error s!"{f.text} has type {F.text}, not a function type, so it cannot be applied"

/-! ## Inference -/

structure Gen where
  next : Nat := 0
  /-- One equation per application, in the order they were made. -/
  eqs : List (Ty × Ty) := []
  /-- The free variables not in the context, each given a type variable. -/
  frees : Ctx := []

/-- Annotate every binder (a type variable where none is written) and collect the equations, from
the state `g` (the next type variable, the equations so far, the free variables' types). -/
def gen (Γ : Ctx) : ATerm → Gen → (ATerm × Ty) × Gen
  | .var x, g =>
    match Γ.lookup x with
    | some T => ((.var x, T), g)
    | none =>
      match g.frees.lookup x with
      | some T => ((.var x, T), g)
      | none => ((.var x, .tvar g.next), { g with next := g.next + 1, frees := g.frees ++ [(x, .tvar g.next)] })
  | .lam x (some A) e, g =>
    let ((e', B), g') := gen ((x, A) :: Γ) e g
    ((.lam x (some A) e', .arrow A B), g')
  | .lam x none e, g =>
    let A := Ty.tvar g.next
    let ((e', B), g') := gen ((x, A) :: Γ) e { g with next := g.next + 1 }
    ((.lam x (some A) e', .arrow A B), g')
  | .app f a, g =>
    let ((f', F), g₁) := gen Γ f g
    let ((a', A), g₂) := gen Γ a g₁
    let B := Ty.tvar g₂.next
    ((.app f' a', B), { g₂ with next := g₂.next + 1, eqs := g₂.eqs ++ [(F, .arrow A B)] })

/-- A substitution of types for type variables, kept idempotent. -/
abbrev TSubst := List (Nat × Ty)

def Ty.apply (σ : TSubst) : Ty → Ty
  | .tvar n => (σ.lookup n).getD (.tvar n)
  | .arrow a b => .arrow (a.apply σ) (b.apply σ)
  | T => T

def Ty.occurs (n : Nat) : Ty → Bool
  | .tvar m => m == n
  | .arrow a b => a.occurs n || b.occurs n
  | .base _ => false

/-- One move of unification. -/
inductive UStep where
  /-- Both sides are arrows: their parts must be equal. -/
  | split (s t : Ty)
  /-- A variable takes a type. -/
  | bind (n : Nat) (t : Ty)
  deriving Inhabited

/-- Solve the equations one at a time, recording each move and the substitution after it. -/
def unify (eqs : List (Ty × Ty)) : Except String (TSubst × Array (UStep × TSubst)) :=
  go eqs [] #[] 10000
where
  go : List (Ty × Ty) → TSubst → Array (UStep × TSubst) → Nat → Except String (TSubst × Array (UStep × TSubst))
    | [], σ, acc, _ => .ok (σ, acc)
    | _, _, _, 0 => .error "unification did not finish"
    | (s, t) :: rest, σ, acc, fuel + 1 =>
      let s := s.apply σ
      let t := t.apply σ
      if s = t then go rest σ acc fuel else
      let bindVar (n : Nat) (u : Ty) :=
        if u.occurs n then
          .error s!"occurs check: {(Ty.tvar n).text} = {u.text} has no solution ({(Ty.tvar n).text} would have to contain itself), so the term has no simple type"
        else
          let σ := (n, u) :: σ.map fun (m, v) => (m, v.apply [(n, u)])
          go rest σ (acc.push (.bind n u, σ)) fuel
      match s, t with
      | .tvar n, u => bindVar n u
      | u, .tvar n => bindVar n u
      | .arrow a b, .arrow c d => go ((a, c) :: (b, d) :: rest) σ (acc.push (.split s t, σ)) fuel
      | _, _ => .error s!"cannot unify {s.text} with {t.text}, so the term has no simple type"

def Ty.tvars : Ty → List Nat
  | .tvar n => [n]
  | .arrow a b => (a.tvars ++ b.tvars).eraseDups
  | .base _ => []

def Ty.bases : Ty → List String
  | .base s => [s]
  | .arrow a b => a.bases ++ b.bases
  | .tvar _ => []

def ATerm.mapTypes (f : Ty → Ty) : ATerm → ATerm
  | .var x => .var x
  | .lam x T e => .lam x (T.map f) (e.mapTypes f)
  | .app a b => .app (a.mapTypes f) (b.mapTypes f)

def ATerm.types : ATerm → List Ty
  | .var _ => []
  | .lam _ T e => T.toList ++ e.types
  | .app a b => a.types ++ b.types

/-- Name type variables: the `n`-th by the list, a base type from then on. -/
def Ty.rename (r : List (Nat × String)) : Ty → Ty
  | .tvar n => match r.lookup n with | some s => .base s | none => .tvar n
  | .arrow a b => .arrow (a.rename r) (b.rename r)
  | T => T

structure Inferred where
  /-- The term with every binder annotated by a type variable, as the equations were made. -/
  generated : ATerm
  /-- Its type before solving, and the equations. -/
  initial : Ty
  eqs : List (Ty × Ty)
  /-- Unification's moves, each with the substitution after it. -/
  moves : Array (UStep × TSubst)
  solved : TSubst
  /-- The answer, its variables named α, β, …: the type, the free variables' types, the annotated
  term, and its derivation. -/
  type : Ty
  frees : Ctx
  annotated : ATerm
  deriv : Deriv

def infer (Γ : Ctx) (t : ATerm) : Except String Inferred := do
  let ((gt, T0), g) := gen Γ t {}
  let eqs := g.eqs
  let (σ, moves) ← unify eqs
  let T := T0.apply σ
  let frees := g.frees.map fun (x, A) => (x, A.apply σ)
  let annotated := gt.mapTypes (·.apply σ)
  -- name the variables left in order of appearance, avoiding the base types already in use
  let order := (T.tvars ++ (frees.map (·.2.tvars)).flatten ++ (annotated.types.map Ty.tvars).flatten).eraseDups
  let used := (Γ.map (·.2.bases)).flatten ++ (t.types.map Ty.bases).flatten
  let names := (greekNames ++ (List.range order.length).map (fun i => "α" ++ toString (i + 1))).filter (!used.contains ·)
  let r := order.zip names
  let T := T.rename r
  let frees := frees.map fun (x, A) => (x, A.rename r)
  let annotated := annotated.mapTypes (·.rename r)
  -- the answer is checked, not trusted
  match check (Γ ++ frees.reverse) annotated with
  | .ok (d, T') =>
    if T' = T then pure ⟨gt, T0, eqs, moves, σ, T, frees, annotated, d⟩
    else throw s!"internal: inference found {T.text} but the checker found {T'.text}"
  | .error m => throw s!"internal: the inferred annotation does not check: {m}"
where
  greekNames : List String := ["α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "μ", "ν", "ξ", "ρ", "σ", "φ", "χ", "ψ", "ω"]

/-- Two types alike up to renaming their variables (every name is taken as a variable): the shapes
match and the names correspond one to one. -/
def alikeUpToNames (a b : Ty) : Bool :=
  go a b [] |>.isSome
where
  go : Ty → Ty → List (String × String) → Option (List (String × String))
    | .base x, .base y, m =>
      match m.lookup x, (m.map fun (p, q) => (q, p)).lookup y with
      | some y', _ => if y' == y then some m else none
      | none, some _ => none
      | none, none => some ((x, y) :: m)
    | .arrow a b, .arrow c d, m => (go a c m).bind (go b d ·)
    | .tvar n, .tvar k, m => if n == k then some m else none
    | _, _, _ => none

end Lam
end MathEngine
