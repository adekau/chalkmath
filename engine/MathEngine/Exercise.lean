import MathEngine.Session
/-!
# Exercises: is the reader's answer the expected one?

An exercise is a cell whose source is the *question* (`diff(x^2·sin x, x)`): its value, computed
by the pipeline like any cell's, is the expected answer, and its derivation is the worked solution.
The reader's answer is equivalent to it when both reduce to the same normal form, as two λ-terms
are β-equivalent when they reduce to the same normal form:

- **Expressions.** Both are normalized by the pipeline, then put in the canonical form the
  integration check compares in (`Expand.identNorm`, `Expand.dist`, normalized again: products
  distributed, `cos² = 1 − sin²` and `(eᵘ)ᵏ = eᵏᵘ` applied, all proved sound), and compared
  structurally. Equal canonical forms mean equal values wherever the steps shown are sound; the
  converse is not claimed (`sin²x + cos²x` against `1` is decided, other identities may not be),
  so "not equivalent" is "not shown equivalent".
- **λ-terms.** Both are reduced to β-normal form and compared up to α (their de Bruijn terms).

An answer that does the work itself (`diff(…)` typed back as the answer to a `diff` question, or the
question retyped) is refused: an answer may call only the elementary functions and the functions the
question does not.
A λ answer must already be a normal form. Nothing is bound and nothing is numbered: an exercise is
not an evaluation of the notebook, so `%` and `In[n]` are untouched.
-/
namespace MathEngine
open Expr

/-- Functions an answer may always use: they are part of how an answer is written, not work done. -/
def answerFns : List String :=
  ["sin", "cos", "tan", "sec", "csc", "cot", "arcsin", "arccos", "arctan", "sinh", "cosh", "tanh",
   "exp", "ln", "log", "sqrt", "abs", "conj", "re", "im"]

/-- The function names a term calls (λ-terms' `λ` and `@` heads included; they are filtered by the caller). -/
partial def fnNames : Expr → List String
  | .fn f es => f :: (es.flatMap fnNames)
  | e => (children e).flatMap fnNames

/-- What an answer was compared as: its value and the canonical form both sides were put in. -/
structure Compared where
  value : Expr
  canon : Expr

/-- The result of checking: the expected answer with its worked solution and, when an answer was
given, how it compares. -/
structure CheckResult where
  expected : Expr
  derivation : Derivation
  lambda : Bool
  /-- The expected answer's canonical form (what an answer is compared against). -/
  expectedCanon : Expr
  /-- The answer: its value and canonical form, or why it could not be compared. -/
  given : Option (Except (String × String × Option (Nat × Nat)) Compared)
  equivalent : Bool

private abbrev Err := String × String × Option (Nat × Nat)

/-- Normalize with the notebook pipeline. -/
private def norm (e : Expr) : Except String (Expr × Array Step) :=
  match (normalizeT pipelineRules pipelineOrdered e).run #[] with
  | (.error msg, _) => .error msg
  | (.ok out, steps) => .ok (out, steps)

/-- The canonical form answers are compared in (the integration check's). -/
def canonical (e : Expr) : Except String Expr :=
  (norm (Expand.dist (Expand.identNorm e))).map (·.1)

/-- An expression source, parsed and with the session's names in it; `let` is refused. -/
private def prepare (s : Session) (src : String) : Except Err (Expr × Expr) := do
  match parseStmt src (s.fns.map (·.1)) with
  | .error e => throw ("syntax", e.message, some (e.start, e.stop))
  | .ok (.«let» _ _ _) => throw ("params", "an exercise compares expressions; a let has no value to compare", none)
  | .ok (.expr v) =>
    match s.resolveOuts v with
    | .error msg => throw ("eval", msg, none)
    | .ok v => pure (v, substitute s.env (substituteFns s.fns v))

/-- The reader's expression answer, compared in canonical form; `forbidden` are the functions that
would do the question's work. -/
private def compareExpr (s : Session) (question : Expr) (forbidden : List String) (src : String) : Except Err Compared := do
  let (parsed, input) ← prepare s src
  if equal parsed question then throw ("answer", "that is the question itself: write its value", none)
  match (fnNames parsed).find? forbidden.contains with
  | some f => throw ("answer", s!"the answer may not use {f}: write the result, not the work", none)
  | none => pure ()
  let value ← match norm input with
    | .ok (v, _) => pure v
    | .error msg => throw ("eval", msg, none)
  match canonical value with
  | .ok c => pure ⟨value, c⟩
  | .error msg => throw ("eval", msg, none)

/-- A λ source, its definitions unfolded, reduced to normal form. -/
private def reduceLam (s : Session) (src : String) : Except Err (Lam.Term × Lam.Term × List (Lam.Term × Bool)) := do
  match Lam.parseStmt src with
  | .error msg => throw ("syntax", msg, none)
  | .ok (some _, _) => throw ("params", "an exercise compares λ-terms; a definition has no value to compare", none)
  | .ok (none, t) =>
    let expanded := Lam.expandDefs (lambdaDefs s) t
    let (out, trace, normal) := Lam.reduce expanded
    if !normal then throw ("eval", s!"λ: no normal form after {Lam.maxSteps} β-steps", none)
    pure (t, out, trace)

/-- Check an exercise: evaluate the question (recorded as `cellId`, so its work can be fetched and
explained, but neither bound nor numbered), and compare the answer, if one is given. -/
def checkAnswer (s : Session) (cellId question : String) (answer : Option String) :
    Session × Except Err CheckResult :=
  if isLambdaCell s question then
    match Lam.parseStmt question with
    | .ok (some _, _) => (s, .error ("params", "an exercise compares λ-terms; a definition has no value to compare", none))
    | _ =>
    match lambdaCell s cellId question with
    | (s, .error e) => (s, .error e)
    | (s, .ok res) =>
      let expCanon := Lam.dbToExpr (Lam.toDB [] res.output)
      let given : Option (Except Err Compared) := answer.map fun a =>
        match reduceLam s a with
        | .error e => .error e
        | .ok (_, aout, atrace) =>
          if !atrace.isEmpty then .error ("answer", "the answer still has a redex: reduce it to normal form", none)
          else .ok ⟨Lam.toExpr aout, Lam.dbToExpr (Lam.toDB [] aout)⟩
      let eq := match given with | some (.ok c) => equal c.canon expCanon | _ => false
      (s, .ok ⟨Lam.toExpr res.output, res.derivation, true, expCanon, given, eq⟩)
  else
    match prepare s question with
    | .error e => (s, .error e)
    | .ok (parsed, _) =>
      match evaluateCell s cellId question with
      | (s, .error e) => (s, .error e)
      | (s, .ok (_, output, d)) =>
        match canonical output with
        | .error msg => (s, .error ("eval", msg, none))
        | .ok expCanon =>
          let forbidden := (fnNames parsed).filter (!answerFns.contains ·)
          let given := answer.map (compareExpr s parsed forbidden)
          let eq := match given with | some (.ok c) => equal c.canon expCanon | _ => false
          (s, .ok ⟨output, d, false, expCanon, given, eq⟩)

end MathEngine
