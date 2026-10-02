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

/-! ## Logic and relations -/

/-- A logic exercise. The answer is a formula; what it must be depends on the question:
- `nnf(φ)`, `cnf(φ)`, `dnf(φ)`: equivalent to `φ` and in that form;
- `sat(φ)` (`falsify(φ)`): any satisfiable formula that implies `φ` (`¬φ`) — an assignment written as
  a conjunction of literals is one — or `⊥` when there is none;
- `taut`, `equiv`, and a formula without variables: `⊤` or `⊥`;
- a formula in variables: an equivalent one.
Equivalence is decided by truth table, so a "not equivalent" here is definite. -/
def checkLogic (s : Session) (cellId question : String) (answer : Option String) :
    Session × Except Err CheckResult :=
  match Logic.parseStmt question with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok (.cmd (some _) _ _) | .ok (.fm (some _) _) => (s, .error ("params", "an exercise compares values; a let has no value to compare", none))
  | .ok stmt =>
  match logicCell s cellId question with
  | (s, .error e) => (s, .error e)
  | (s, .ok res) =>
    let prep (f : Logic.Fm) := Logic.expand s.formulas f
    -- what the answer is held to
    let mode : String × Option Logic.Fm := match stmt with
      | .cmd _ h [f] => if ["nnf", "cnf", "dnf"].contains h then (h, some (prep f)) else if h == "sat" || h == "falsify" then (h, some (prep f)) else ("bool", none)
      | .cmd _ _ _ => ("bool", none)
      | .fm _ f => let f := prep f; if f.isProp && !f.vars.isEmpty then ("formula", some f) else ("bool", none)
    let expectedBool : Bool := match res.value with | .fn "⊤" [] => true | _ => false
    let compare (a : Logic.Fm) : Except Err (Compared × Bool) := do
      let shown : Compared := ⟨a.toExpr, a.toExpr⟩
      let equivTo (e : Logic.Fm) : Except Err Bool := do
        let vs := (Logic.Fm.and a e).vars
        if vs.length > Logic.maxVars then throw ("answer", s!"more than {Logic.maxVars} variables", none)
        return (Logic.findRow vs fun σ => a.eval σ != e.eval σ).isNone
      if !a.isProp then throw ("answer", "the answer must be a formula of propositional logic", none)
      match mode with
      | ("bool", _) =>
        if !a.vars.isEmpty then throw ("answer", "the answer is ⊤ or ⊥ (true or false)", none)
        return (shown, a.eval (fun _ => false) == expectedBool)
      | ("sat", some f) | ("falsify", some f) =>
        let target := if mode.1 == "sat" then f else .not f
        let vs := (Logic.Fm.and a target).vars
        let aSat := (Logic.findRow vs fun σ => a.eval σ).isSome
        if !aSat then return (shown, res.value matches .fn "⊥" [])
        return (shown, (Logic.findRow vs fun σ => a.eval σ && !target.eval σ).isNone)
      | (h, some f) =>
        let target := if ["nnf", "cnf", "dnf"].contains h then (Logic.toNormal h f).1 else f
        if ["nnf", "cnf", "dnf"].contains h && !Logic.hasShape h a then
          throw ("answer", s!"the answer must be in {h.toUpper}{if h == "cnf" then ": a conjunction of clauses, each a disjunction of literals" else if h == "dnf" then ": a disjunction of terms, each a conjunction of literals" else ": negations on variables only, no → or ↔"}", none)
        return (shown, ← equivTo target)
      | _ => return (shown, false)
    let given : Option (Except Err (Compared × Bool)) := answer.map fun a =>
      match Logic.parseFormula a with
      | .error msg => .error ("syntax", msg, none)
      | .ok f => compare (prep f)
    let eq := match given with | some (.ok (_, b)) => b | _ => false
    (s, .ok ⟨res.value, res.derivation, false, res.value, given.map (·.map (·.1)), eq⟩)

/-- An order-world value, as something answers can be compared with: `kind` and a canonical form
(elements by their canonical key, so a pair or a set element compares whatever its spacing). -/
private def orderCanon : Expr → String × List String
  | .var "true" => ("bool", ["true"])
  | .var "false" => ("bool", ["false"])
  | .fn "rel" [_, .fn "set" ps] => ("pairs", (ps.map fun p => match p with | .fn "pair" [a, b] => s!"{Ord.elemKey a.toText},{Ord.elemKey b.toText}" | e => e.toText).mergeSort)
  | .fn "set" xs =>
    if !xs.isEmpty && xs.all (fun x => x matches .fn "set" _) then
      ("partition", (xs.map fun x => match x with | .fn "set" ys => ",".intercalate (ys.map (Ord.elemKey ·.toText)).mergeSort | e => e.toText).mergeSort)
    else ("set", (xs.map (Ord.elemKey ·.toText)).mergeSort)
  | e => ("element", [Ord.elemKey e.toText])

/-- The items of a list written with or without its outer braces: `{a, b}` or `a, b`. -/
private def topItems (s : String) : List String :=
  let items := (Ord.splitTop s).map (·.trimAscii.copy) |>.filter (· != "")
  match items with
  | [one] => if one.startsWith "{" && one.endsWith "}" then (Ord.splitTop ((one.drop 1).dropEnd 1).copy).map (·.trimAscii.copy) |>.filter (· != "") else items
  | _ => items

/-- Parse an answer to an order-world question as the kind of value expected. -/
private def parseOrderAnswer (kind : String) (src : String) : Option (List String) :=
  let s := src.trimAscii.copy
  match kind with
  | "bool" => match s.toLower with | "true" | "⊤" => some ["true"] | "false" | "⊥" => some ["false"] | _ => none
  | "pairs" =>
    let strip (t : String) := (t.replace "{" "").replace "}" "" |>.replace "(" "" |>.replace ")" "" |>.trimAscii.copy
    if (s.splitOn "->").length > 1 || (s.splitOn "→").length > 1 then
      let ps := (strip s).splitOn "," |>.map fun p => (p.replace "→" "->").splitOn "->" |>.map (·.trimAscii.copy)
      if ps.all (·.length == 2) then some (ps.map (fun p => s!"{Ord.elemKey p[0]!},{Ord.elemKey p[1]!}")).mergeSort else none
    else
      -- (a, b), (c, d): the brackets pair them
      let groups := ((s.replace "{" "").replace "}" "").splitOn "(" |>.map (fun g => (g.splitOn ")").headD "") |>.map (·.trimAscii.copy) |>.filter (· != "")
      let ps := groups.map fun g => (g.splitOn ",").map (·.trimAscii.copy)
      if !ps.isEmpty && ps.all (·.length == 2) then some (ps.map (fun p => s!"{Ord.elemKey p[0]!},{Ord.elemKey p[1]!}")).mergeSort else if s == "{}" then some [] else none
  | "partition" =>
    -- {a, b}, {c} or {{a, b}, {c}}: each class a set
    let classes := topItems s
    if classes.all (fun c => c.startsWith "{" && c.endsWith "}") then
      some (classes.map fun c => ",".intercalate ((Ord.splitTop ((c.drop 1).dropEnd 1).copy).map (·.trimAscii.copy) |>.filter (· != "") |>.map Ord.elemKey).mergeSort).mergeSort
    else none
  | "set" => some ((topItems s).map Ord.elemKey).mergeSort
  | _ => some [Ord.elemKey s]

/-- A parsed order-world answer as a value, to show. -/
private def orderAnswerExpr (kind : String) (got : List String) : Expr :=
  let parts (g : String) := (g.splitOn ",").filter (· != "")
  match kind with
  | "bool" => .var (got.headD "false")
  | "pairs" => .fn "set" (got.map fun p => match parts p with | [a, b] => Ord.pairExpr (a, b) | _ => .var p)
  | "partition" => .fn "set" (got.map fun g => Ord.setExpr (parts g))
  | "set" => Ord.setExpr got
  | _ => Ord.elemExpr (got.headD "")

/-- An order-world exercise (posets and relations): the answer, written as a value of the kind the
question has (`true`/`false`, pairs `a->b, b->c` or `(a, b), (b, c)`, classes `{a, b}, {c}`, a set, an
element), is compared with the question's value as a set. -/
def checkOrder (s : Session) (cellId question : String) (answer : Option String) :
    Session × Except Err CheckResult :=
  match Ord.parseStmt question with
  | .ok (some _, _, _) => (s, .error ("params", "an exercise compares values; a let has no value to compare", none))
  | _ =>
  match orderCell s cellId question with
  | (s, .error e) => (s, .error e)
  | (s, .ok res) =>
    let (kind, want) := orderCanon res.value
    let given : Option (Except Err (Compared × Bool)) := answer.map fun a =>
      if Ord.isOrderSource a then .error ("answer", "write the value itself, not the command that computes it", none) else
      match parseOrderAnswer kind a with
      | none => .error ("answer", match kind with
          | "bool" => "the answer is true or false"
          | "pairs" => "write the relation's pairs: a->b, b->c (or (a, b), (b, c))"
          | _ => "write the value", none)
      | some got =>
        let shown := orderAnswerExpr kind got
        .ok (⟨shown, shown⟩, got.eraseDups == want.eraseDups)
    let eq := match given with | some (.ok (_, b)) => b | _ => false
    (s, .ok ⟨res.value, res.derivation, false, res.value, given.map (·.map (·.1)), eq⟩)

/-- Check an exercise: evaluate the question (recorded as `cellId`, so its work can be fetched and
explained, but neither bound nor numbered), and compare the answer, if one is given. -/
def checkAnswer (s : Session) (cellId question : String) (answer : Option String) :
    Session × Except Err CheckResult :=
  if Ord.isOrderSource question then checkOrder s cellId question answer else
  if Logic.isLogicSource question then checkLogic s cellId question answer else
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
