import MathEngine.Nested
import MathEngine.Exercise
import MathEngine.Json
import MathEngine.Wire
import MathEngine.Print
/-!
# Worlds

A world is a language the notebook speaks beside algebra: the λ-calculus, finite order theory,
logic, transition systems. Each has its own grammar and evaluator (`Session.lean` and the modules it
imports); this file is where they are registered, once, as a list of `World` records, and where the
one reply builder turns what any of them produced into the wire's JSON.

A record says what the world is called, which cell sources are its (`claims`, in the order of
`worlds`; `precedes` lets a world take a source before the others look, as a λ-command does when it
holds a connective), what it binds (`binds`, `holds`), how it evaluates a cell and checks an
exercise, and its lexicon — the command names, keywords and glyphs its grammar reads — which
`engine.capabilities` publishes so the notebook and the visual editor need no copy of their own.

Algebra is the last world in the list and claims every source the others do not.
-/
namespace MathEngine
open Json

/-- An error a cell's evaluation reports: a code, a message, and the span of the source it points at. -/
abbrev WorldErr := String × String × Option (Nat × Nat)

/-- What a world's cell produced, in the shape every world shares. -/
structure WorldResult where
  /-- The name the cell bound, if it bound one. -/
  name : Option String := none
  /-- For a function definition: its parameters. -/
  params : List String := []
  value : Expr
  derivation : Derivation
  /-- A one-line note beside the answer, sent only when neither the answer nor the work says it. -/
  summary : Option String := none
  /-- Visual specs (`ARCHITECTURE.md` §5), each `{kind, data}`. -/
  visuals : Array Json := #[]
  /-- The world's own fields on the reply (`renderedDeBruijn`, `reading`, `semantics`, `warnings`). -/
  extras : Array (String × Json) := #[]
  /-- The derivation's steps carry their de Bruijn view (λ-cells). -/
  lambda : Bool := false

structure World where
  /-- The reply's `kind`. -/
  id : String
  /-- How the notebook names the world to a reader. -/
  label : String
  /-- The commands this world reads, written `name(…)` (the λ-calculus's are written `name:`). -/
  commands : List String := []
  /-- Words its grammar reserves (`when`, `do`, `forall`); the editor ends a product at them. -/
  keywords : List String := []
  /-- The operators and constants its grammar reads that algebra's does not (`∧`, `->`, `:=`). -/
  glyphs : List String := []
  /-- Other names it gives a cell: the λ library, the logic predicates. -/
  names : List String := []
  /-- What claims a source for this world beyond its commands: a glyph anywhere in it, or a word at
  its head (`forall`). The notebook labels a cell by these before the engine has read it. -/
  markers : List String := []
  /-- This source is the world's before any other is asked. -/
  precedes : String → Bool := fun _ => false
  /-- This source is the world's. -/
  claims : Session → String → Bool
  /-- The name a source would bind, by its syntax (`let n =`, a λ-cell's `n :=`). -/
  binds : String → Option String
  /-- The world holds a binding of this name. -/
  holds : Session → String → Bool
  evaluate : Session → String → String → Session × Except WorldErr WorldResult
  check : Session → String → String → Option String → Session × Except WorldErr CheckResult

/-! ## The wire -/

def Rendered.toJson (e : Expr) (paths : Bool) : Json :=
  .obj #[("text", .str e.toText), ("latex", .str (e.toLatex paths))]

/-- A derivation on the wire; a λ-cell's steps also carry their de Bruijn view (`afterDeBruijn`). -/
def derivationJson (d : Derivation) (paths lambda : Bool) : Json :=
  if !lambda then d.toJson paths else
  let steps := (d.steps.zip (lambdaDbSteps d)).map fun (stp, db) =>
    match stp.toJson paths with
    | .obj fields => Json.obj (fields.push ("afterDeBruijn", Rendered.toJson db false))
    | j => j
  .obj #[("input", d.input.toJson), ("steps", .arr steps), ("output", d.output.toJson)]

/-- The work in a reply, with `showWork`: the derivation, or with `outline` only its outline —
each step's rule, explanation and path, without the terms, which are what make the derivation of a
big term large. `engine.steps` sends the derivation itself when it is wanted. -/
def workFields (params : Json) (d : Derivation) (lambda := false) : Array (String × Json) :=
  if !params.getBool "showWork" then #[] else
  let paths := params.getBool "paths"
  let work := if params.getBool "outline" then ("outline", d.outlineJson) else ("derivation", derivationJson d paths lambda)
  #[work, ("inputRendered", Rendered.toJson d.input paths)]

def errorJson (code msg : String) (span : Option (Nat × Nat) := none) : Json :=
  let err := #[("code", .str code), ("message", .str msg)]
  let err := match span with
    | some (s, e) => err.push ("span", .obj #[("start", .num (toString s)), ("end", .num (toString e))])
    | none => err
  .obj #[("ok", .bool false), ("error", .obj err)]

/-- A visual spec: its kind and its data. -/
def visual (kind : String) (data : Array (String × Json)) : Json :=
  .obj #[("kind", .str kind), ("data", .obj data)]

private def pairs (ps : List (String × String)) : Json := .arr (ps.map fun (a, b) => Json.arr #[.str a, .str b]).toArray
private def strs (xs : List String) : Json := .arr (xs.map Json.str).toArray

/-- One reply for every world: `ok`, `kind`, the value and its rendering, the note, the visuals, the
world's own fields, the work, and what was bound. -/
def worldReply (w : World) (params : Json) (res : WorldResult) : Json :=
  let paths := params.getBool "paths"
  let r := #[("ok", .bool true), ("value", res.value.toJson), ("rendered", Rendered.toJson res.value paths), ("kind", .str w.id)]
  let r := match res.summary with | some t => r.push ("summary", .str t) | none => r
  let r := if res.visuals.isEmpty then r else r.push ("visuals", .arr res.visuals)
  let r := r ++ res.extras
  let r := r ++ workFields params res.derivation res.lambda
  let r := match res.name with
    | some n => let r := r.push ("bound", .arr #[.str n]); if res.params.isEmpty then r else r.push ("params", strs res.params)
    | none => r
  .obj r

/-! ## The λ-calculus -/

/-- A context as a judgment shows it: each variable once (the innermost binding), outermost first. -/
def ctxShown (Γ : Lam.Ctx) : Lam.Ctx :=
  (Γ.foldl (fun acc (x, T) => if acc.any (·.1 == x) then acc else acc ++ [(x, T)]) []).reverse

/-- The contexts of a derivation's judgments, root first, each once. -/
partial def typingCtxs : Lam.Deriv → List Lam.Ctx
  | .node _ Γ _ _ ps => (ctxShown Γ :: (ps.map typingCtxs).flatten).eraseDups

/-- A typing derivation as a tree for the notebook: each node its judgment `Γ ⊢ t : T`, its rule,
and its premises. When writing the contexts out would make a judgment long, each context is named
(Γ₁, Γ₂, …, each by the one it extends) and the names are explained in a legend. -/
def typingTreeVisual (d : Lam.Deriv) : Json :=
  let tex (e : Expr) := e.toLatex false
  let entryL (x : String) (A : Lam.Ty) := s!"{tex (.var x)} : {tex A.toExpr}"
  let entryT (x : String) (A : Lam.Ty) := s!"{x} : {A.text}"
  let full (Γ : Lam.Ctx) (f : String → Lam.Ty → String) := ", ".intercalate (Γ.map fun (x, A) => f x A)
  let ctxs := (typingCtxs d).filter (!·.isEmpty)
  let long := ctxs.any fun Γ => (full Γ entryT).length > 28
  let named : List (Lam.Ctx × Nat) := if long then ctxs.zip (List.range' 1 ctxs.length) else []
  let ctxL (Γ : Lam.Ctx) := match named.lookup Γ with
    | some k => s!"\\Gamma_\{{k}}"
    | none => full Γ entryL
  -- a context named by the longest named one it extends
  let legend := named.map fun (Γ, k) =>
    let base := (named.filter fun (Δ, j) => j < k && Δ.length < Γ.length && Γ.take Δ.length == Δ).foldl
      (fun best (Δ, j) => match best with | some (B, _) => if Δ.length > B.length then some (Δ, j) else best | none => some (Δ, j)) none
    let (rest, prefL, prefT) := match base with
      | some (Δ, j) => (Γ.drop Δ.length, s!"\\Gamma_\{{j}}, ", s!"Γ{j}, ")
      | none => (Γ, "", "")
    Json.obj #[("latex", .str (s!"\\Gamma_\{{k}} = " ++ prefL ++ full rest entryL)), ("text", .str (s!"Γ{k} = " ++ prefT ++ full rest entryT))]
  let rec node : Lam.Deriv → Json
    | .node rule Γ t T ps =>
      let Γ := ctxShown Γ
      let latex := (if Γ.isEmpty then "" else ctxL Γ ++ " ") ++ "\\vdash " ++ tex t.toExpr ++ " : " ++ tex T.toExpr
      let text := (if Γ.isEmpty then "" else full Γ entryT ++ " ") ++ "⊢ " ++ t.text ++ " : " ++ T.text
      let label := match rule with | "var" => "Var" | "abs" => "→I" | "app" => "→E" | r => r
      .obj #[("rule", .str label), ("latex", .str latex), ("text", .str text), ("premises", .arr (ps.attach.map fun ⟨p, _⟩ => node p).toArray)]
  .obj #[("root", node d), ("legend", .arr legend.toArray)]

/-- A λ-cell's `n := …` binds `n`. -/
def lambdaBinds (src : String) : Option String :=
  match src.splitOn ":=" with
  | [n, _] => let n := n.trimAsciiEnd.copy.trimAsciiStart.copy; if Lam.isName n then some n else none
  | _ => none

def lambdaWorld : World where
  id := "lambda"
  label := "λ-calculus"
  commands := Lam.commandWords
  names := Lam.churchDefs.map (·.1)
  glyphs := ["λ", "\\", ".", ":=", "->", "→", "⊢", "|-", ":"]
  markers := ["λ", "\\", ":="]
  -- a λ-command (`type: f : A → B ⊢ f`) may hold a connective or a call; it is the λ-world's first
  precedes := fun src => (Lam.commandHead src).isSome
  claims := isLambdaCell
  binds := lambdaBinds
  holds := fun s n => s.lambdas.any (·.1 == n)
  evaluate := fun s cellId src =>
    let (s, r) := lambdaCell s cellId src
    (s, r.map fun res =>
      let db := match res.term with | some t => Lam.dbToExpr (Lam.toDB [] t) | none => res.value
      let extras := #[("renderedDeBruijn", Rendered.toJson db false)]
      let extras := match res.reading with | some t => extras.push ("reading", .str t) | none => extras
      { name := res.name, value := res.value, derivation := res.derivation, extras, lambda := true,
        visuals := match res.tree with
          | some d => #[.obj #[("kind", .str "typing.tree"), ("data", typingTreeVisual d)]]
          | none => #[] })
  check := checkLambda

/-! ## Finite order theory, relations and algebra -/

/-- The Hasse diagram of a poset: each element with its height, and the covers. -/
def hasseData (P : Ord.Poset) : Array (String × Json) :=
  let hs := Ord.heights P
  #[("nodes", .arr (P.elems.map fun x => Json.obj #[("name", .str x), ("height", .num (toString (hs.getD x 0)))]).toArray),
    ("covers", pairs (Ord.hasse P))]

def orderWorld : World where
  id := "poset"
  label := "Order theory"
  commands := Ord.commands
  glyphs := ["<", "->", "=", "|", "..", "{", "}"]
  claims := fun _ src => Ord.isOrderSource src
  binds := fun src => (Sys.splitLet src).1
  holds := fun s n => s.posets.any (·.1 == n) || s.pmaps.any (·.1 == n) || s.rels.any (·.1 == n) || s.ops.any (·.1 == n) || s.ctxs.any (·.1 == n)
  evaluate := fun s cellId src =>
    let (s, r) := orderCellN s cellId src
    (s, r.map fun res =>
      let visuals : Array Json :=
        (match res.poset with
          | some P => #[visual "order.hasse" (hasseData P)]
          | none => #[]) ++
        (match res.graph with
          | some (R, bad, added) => #[visual "relation.digraph" #[
              ("nodes", strs R.elems), ("edges", pairs R.pairs), ("bad", pairs bad), ("added", pairs added)]]
          | none => #[]) ++
        (match res.table with
          | some (o, marks) => #[visual "algebra.optable" #[
              ("elems", strs o.elems), ("rows", .arr (o.rows.map strs).toArray), ("marks", pairs marks)]]
          | none => #[]) ++
        (match res.context with
          | some C => #[visual "context.table" #[
              ("objects", strs C.objs), ("attributes", strs C.attrs),
              ("has", .arr (C.objs.map fun o => Json.arr (C.attrs.map fun a => Json.bool (C.has o a)).toArray).toArray)]]
          | none => #[])
      -- `hasse` stays on the reply for one release, for a notebook that predates the visual
      let extras := match res.poset with | some P => #[("hasse", Json.obj (hasseData P))] | none => #[]
      { name := res.name, value := res.value, derivation := res.derivation, summary := res.summary, visuals, extras })
  check := checkOrder

/-! ## Logic -/

def logicWorld : World where
  id := "logic"
  label := "Logic"
  commands := Logic.commands
  keywords := Logic.wordGlyph.map (·.1)
  names := ["prime", "even", "odd"]
  glyphs := ["∧", "∨", "¬", "→", "↔", "⊤", "⊥", "∀", "∃", "∈", "≤", "≥", "≠", "<->", "->", "=>", "&&", "/\\", "||", "\\/", "<=", ">=", "!=", "==", "!", "~", "..", ","]
  markers := ["¬", "∧", "∨", "→", "↔", "⊤", "⊥", "∀", "∃", "<->", "->", "&&", "||", "forall", "exists"]
  claims := fun _ src => Logic.isLogicSource src
  binds := fun src => (Sys.splitLet src).1
  holds := fun s n => s.formulas.any (·.1 == n)
  evaluate := fun s cellId src =>
    let (s, r) := logicCell s cellId src
    (s, r.map fun res =>
      { name := res.name, value := res.value, derivation := res.derivation,
        visuals := match res.table with
          | some (vs, rows) =>
            let formula := match res.derivation.input with | .fn "truthtable" [f] => f | e => e
            #[visual "logic.truthtable" #[
              ("vars", strs vs), ("formula", Rendered.toJson formula false),
              ("rows", .arr (rows.map fun row => Json.arr (row.map Json.bool).toArray).toArray)]]
          | none => #[] })
  check := checkLogic

/-! ## Transition systems, replicas and rewriting -/

def systemWorld : World where
  id := "system"
  label := "Transition systems"
  commands := Sys.commands
  keywords := ["var", "in", "init", "action", "when", "do", "fair", "strong"]
  glyphs := [":=", "<-", "->", "∧", "∨", "¬", "=", "≠", "<", ">", "≤", "≥", "..", ";", ":", "\n"]
  claims := fun _ src => Sys.isSystemSource src
  binds := fun src => (Sys.splitLet src).1
  holds := fun s n => s.systems.any (·.1 == n) || s.trss.any (·.1 == n)
  evaluate := fun s cellId src =>
    let (s, r) := systemCellN s cellId src
    (s, r.map fun res =>
      let graph : Array Json := match res.graph with
        | some (R, bad, added) =>
          let layers : Array (String × Json) := if res.layers.isEmpty then #[] else #[("layers", .arr (res.layers.map fun n => Json.num (toString n)).toArray)]
          -- each arrow's actions, in the order of `edges`
          let labels : Array (String × Json) := if res.edgeLabels.length != R.pairs.length then #[] else #[("labels", strs res.edgeLabels)]
          -- where each step of the work is on the graph: the transition it takes, or the state it is at
          let mark (st : Step) : Json :=
            match Sys.labelOfStateExpr st.before, Sys.labelOfStateExpr st.after with
            | some b, some a =>
              if R.pairs.contains (b, a) then .obj #[("edge", .arr #[.str b, .str a])]
              else if R.elems.contains a then .obj #[("node", .str a)] else .null
            | _, some a => if R.elems.contains a then .obj #[("node", .str a)] else .null
            | some b, _ => if R.elems.contains b then .obj #[("node", .str b)] else .null
            | none, none => .null
          let marks := res.derivation.steps.map mark
          let stepsField : Array (String × Json) := if marks.all (fun | .null => true | _ => false) then #[] else #[("steps", .arr marks)]
          #[visual "relation.digraph" (#[("nodes", strs R.elems), ("edges", pairs R.pairs), ("bad", pairs bad), ("added", pairs added)] ++ layers ++ labels ++ stepsField)]
        | none => #[]
      let spacetime : Array Json := match res.spacetime with
        | some (D, evOf) =>
          let ev (e : Rep.DEvent) : Json := .obj #[("lane", .str e.lane), ("label", .str e.label), ("state", .str e.state)]
          #[visual "replicas.spacetime" #[
            ("lanes", strs D.lanes), ("events", .arr (D.events.map ev)),
            ("messages", .arr (D.messages.map fun (a, b) => Json.arr #[.num (toString a), .num (toString b)]).toArray),
            ("steps", .arr (evOf.map fun es => Json.arr (es.map fun i => Json.num (toString i)).toArray))]]
        | none => #[]
      { name := res.name, value := res.value, derivation := res.derivation, summary := res.summary, visuals := graph ++ spacetime })
  check := checkSystem

/-! ## Algebra, the last word -/

/-- The warning for a free `e`: the letter is a variable, not Euler's number `ℯ`. -/
def eWarning : String :=
  "e here is a variable, not Euler's number: e^x is not exp(x) and does not simplify like it (only N gives e Euler's value). For the constant, type \\e (it shows as ℯ), or write exp(x)."

/-- Warnings about a cell's input (after the session's bindings are substituted), not counting the
parameters a function definition binds. -/
def inputWarnings (input : Expr) (params : List String) : List String :=
  let fv := Expr.freeVars input
  let eW := if fv.contains "e" && !params.contains "e" then [eWarning] else []
  -- `1.5e3` lexes as `1.5` then the name `e3`, an implicit product: the engine has no exponent notation
  let sci := fv.filter fun v => v.length ≥ 2 && v.front == 'e' && (v.drop 1).all Char.isDigit && !params.contains v
  eW ++ sci.map fun v => s!"`{v}` is a variable here, so `1.5{v}` is `1.5 · {v}`: for scientific notation write `*10^{v.drop 1}`."

/-- `let f(x, y) = …`: the function a source defines. -/
def letFnName (src : String) : Option String :=
  let t := src.trimAsciiStart.copy
  if !t.startsWith "let " then none else
  let cs := (t.drop 4).trimAsciiStart.copy.toList
  let w := cs.takeWhile fun c => c.isAlphanum || c == '_' || c == '\''
  match (cs.drop w.length).dropWhile (· == ' ') with
  | '(' :: _ => if w.isEmpty then none else some (String.ofList w)
  | _ => none

def mathWorld : World where
  id := "math"
  label := "Algebra"
  commands := builtinFunctions
  claims := fun _ _ => true
  binds := fun src => match letFnName src with | some f => some f | none => (Sys.splitLet src).1
  holds := fun s n => s.env.any (·.1 == n) || s.fns.any (·.1 == n)
  evaluate := fun s cellId src =>
    let (s, r) := evaluateCell s cellId src
    (s, r.map fun (stmt, out, d) =>
      let sem := if mentionsI d.input || mentionsI out then "complex" else "real"
      let (name, ps) := match stmt with | .«let» n ps _ => (some n, ps) | _ => (none, [])
      let warnings := inputWarnings d.input ps
      let extras := #[("semantics", Json.str sem)]
      let extras := if warnings.isEmpty then extras else extras.push ("warnings", .arr (warnings.map .str).toArray)
      { name, params := ps, value := out, derivation := d, extras })
  check := checkMath

/-! ## The list -/

/-- Every world, in the order they are asked: a λ-term is asked for last among the worlds, since its
test (a known name at the head, or a `:=`) is the loosest, and algebra claims whatever is left. -/
def worlds : List World := [systemWorld, orderWorld, logicWorld, lambdaWorld, mathWorld]

/-- The world a source belongs to: the one that takes it before the others, else the first that
claims it. Always some, since algebra claims everything. -/
def worldFor (s : Session) (src : String) : World :=
  match worlds.find? (·.precedes src) with
  | some w => w
  | none => (worlds.find? (·.claims s src)).getD mathWorld

/-- The names of the worlds' values on the wire (`Expr.fn` heads the printer and the readers give a
meaning to) and the commands: a function may not be named after one, since `f(…)` would be read as
that command or that value. -/
def reservedFnNames : List String :=
  ["set", "pair", "rel", "poset", "hasse", "covers", "range", "List", "All", "span", "part", "λ", "λ:", "@", "%prev", "%out", "truthtable"]
  ++ (worlds.flatMap (·.commands)).eraseDups

/-- Evaluate a source in its world. A name bound in another world is unbound first, so `let F = p ∧ q`
then `let F = system(…)` leaves one `F`; a name the same world holds is left to that world's
rebinding, which may refer to the old value (`let C = product(C, C)`). A function may not take a
command's or a wire value's name. -/
def evaluateIn (s : Session) (cellId src : String) : World × Session × Except WorldErr WorldResult :=
  let w := worldFor s src
  match letFnName src with
  | some f =>
    if reservedFnNames.contains f then
      (w, s, .error ("syntax", s!"`{f}` is a command's name: a function cannot be called that", none))
    else go w
  | none => go w
where
  go (w : World) : World × Session × Except WorldErr WorldResult :=
    let s' := match w.binds src with
      | some n => if worlds.any fun v => v.id != w.id && v.holds s n then s.unbind n else s
      | none => s
    match w.evaluate s' cellId src with
    | (s'', .ok r) => (w, s'', .ok r)
    | (_, .error e) => (w, s, .error e)

/-- Check an exercise in the question's world. -/
def checkAnswer (s : Session) (cellId question : String) (answer : Option String) : Session × Except WorldErr CheckResult :=
  (worldFor s question).check s cellId question answer

/-- The worlds as `engine.capabilities` publishes them: each one's id, label and lexicon, so the
notebook and the visual editor read the command names, keywords and glyphs from the engine. -/
def worldsJson : Json :=
  .arr (worlds.map fun w => Json.obj #[
    ("id", .str w.id), ("label", .str w.label), ("commands", strs w.commands), ("keywords", strs w.keywords),
    ("glyphs", strs w.glyphs), ("names", strs w.names), ("markers", strs w.markers)]).toArray

end MathEngine
