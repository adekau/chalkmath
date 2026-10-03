import MathEngine.Session
/-!
# Nested calls in the order and systems worlds

Their commands take names: `product(C4, C4)` after `let C4 = chain(4)`. A call written inside
another, `product(chain(4), chain(4))`, is taken out before parsing: each inner call is evaluated as
`let chain_1 = chain(4)`, and its name put where it was. The outer cell's derivation starts with a
step per inner call, carrying that call's own derivation, and the names are forgotten afterwards.
This is a rewriting of the source, so whatever a command proves about its named arguments holds
unchanged.
-/
namespace MathEngine

/-- Split a command's argument text at its top-level `,` and `;`, keeping each separator. -/
def topPieces (s : String) : List (String × String) :=
  go s.toList 0 [] []
where
  go : List Char → Nat → List Char → List (String × String) → List (String × String)
    | [], _, cur, acc => (acc ++ [(String.ofList cur.reverse, "")])
    | c :: cs, d, cur, acc =>
      if (c == ',' || c == ';') && d == 0 then go cs d [] (acc ++ [(String.ofList cur.reverse, String.singleton c)])
      else if c == '(' || c == '{' || c == '[' then go cs (d + 1) (c :: cur) acc
      else if c == ')' || c == '}' || c == ']' then go cs (d - 1) (c :: cur) acc
      else go cs d (c :: cur) acc

/-- Is `t` one call `h(…)`, its parentheses closing at the very end? -/
def isWholeCall (t : String) (h : String) : Bool :=
  let rest := (t.drop h.length).trimAscii.copy.toList
  match rest with
  | '(' :: _ =>
    let rec close : List Char → Nat → Bool
      | [], _ => false
      | c :: cs, d =>
        if c == '(' then close cs (d + 1)
        else if c == ')' then (if d == 1 then cs.isEmpty else close cs (d - 1))
        else close cs d
    close rest 0
  | _ => false

/-- Take the nested calls out of a source: the bindings to make first, innermost first, and the
source with their names in place. `next` numbers the names. -/
partial def unnest (cmds : List String) (src : String) (next : Nat := 1) : List (String × String) × String × Nat :=
  let (name, t) := Sys.splitLet src
  let h := Sys.headOf t
  if !isWholeCall t h then ([], src, next) else
  match Sys.argsOf t h with
  | .error _ => ([], src, next)
  | .ok inner =>
    let (binds, pieces, next) := (topPieces inner).foldl (fun (binds, out, next) (p, sep) =>
        let tp := p.trimAscii.copy
        let ih := Sys.headOf tp
        if !ih.isEmpty && cmds.contains ih && isWholeCall tp ih then
          let (deeper, tp', next) := unnest cmds tp next
          let n := s!"{ih}_{next}"
          (binds ++ deeper ++ [(n, tp')], out ++ [n ++ sep], next + 1)
        else (binds, out ++ [p ++ sep], next)) ([], [], next)
    if binds.isEmpty then ([], src, next) else
    let call := s!"{h}({String.join (pieces.map fun p => if p.endsWith "," || p.endsWith ";" then p ++ " " else p)})"
    (binds, (match name with | some n => s!"let {n} = {call}" | none => call), next)

/-- Forget the names an unnesting bound. -/
def Session.forget (s : Session) (ns : List String) (cells : List String) : Session :=
  let keep {α} (l : List (String × α)) := l.filter (!ns.contains ·.1)
  { s with posets := keep s.posets, pmaps := keep s.pmaps, rels := keep s.rels, ops := keep s.ops,
           ctxs := keep s.ctxs, systems := keep s.systems, trss := keep s.trss, cells := s.cells.filter (!cells.contains ·.1) }

/-- Evaluate a cell of a world whose commands take names, with its nested calls taken out first. The
inner calls' derivations come back as steps to put in front of the outer one's. -/
def withNested {R : Type} (cmds : List String) (rule : String)
    (cell : Session → String → String → Session × Except (String × String × Option (Nat × Nat)) R)
    (derivOf : R → Derivation) (valueOf : R → Expr)
    (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (R × Array Step) :=
  let (binds, outer, _) := unnest cmds source
  if binds.isEmpty then
    match cell s cellId source with
    | (s, .ok r) => (s, .ok (r, #[]))
    | (s, .error e) => (s, .error e)
  else
    let ids := binds.map fun (n, _) => s!"{cellId}/{n}"
    let names := binds.map (·.1)
    let run : Except (String × String × Option (Nat × Nat)) (Session × Array Step) :=
      binds.foldlM (init := (s, (#[] : Array Step))) fun (s, steps) (n, inner) =>
      match cell s s!"{cellId}/{n}" s!"let {n} = {inner}" with
      | (s, .ok r) =>
        let d := derivOf r
        .ok (s, steps.push ⟨rule, s!"First the inner call {inner}, named {n} here.", [], d.input, valueOf r, some d⟩)
      | (_, .error (code, msg, _)) => .error (code, s!"in {inner}: {msg}", none)
    match run with
    | .error e => (s, .error e)
    | .ok (s', steps) =>
      match cell s' cellId outer with
      -- a binding keeps its inner values (a map may refer to its posets by name); a question forgets them
      | (s'', .ok r) => (if (Sys.splitLet source).1.isSome then s'' else s''.forget names ids, .ok (r, steps))
      | (_, .error e) => (s, .error e)

/-- Put the inner calls' steps in front of a cell's derivation, in the reply and in the session (where
`engine.steps` and `engine.explain` read it). -/
def Session.prependSteps (s : Session) (cellId : String) (steps : Array Step) : Session :=
  if steps.isEmpty then s else
  { s with cells := s.cells.map fun (id, c) =>
      if id == cellId then (id, { c with derivation := { c.derivation with steps := steps ++ c.derivation.steps } }) else (id, c) }

/-- An order-world cell, nested calls allowed. -/
def orderCellN (s : Session) (cellId source : String) : Session × Except (String × String × Option (Nat × Nat)) OrdResult :=
  match withNested Ord.commands "order.inner" orderCell (·.derivation) (·.value) s cellId source with
  | (s, .ok (r, steps)) => (s.prependSteps cellId steps, .ok { r with derivation := { r.derivation with steps := steps ++ r.derivation.steps } })
  | (s, .error e) => (s, .error e)

/-- A systems-world cell, nested calls allowed (an order command inside, too: `system` names its
values, not posets, so only systems commands nest here). -/
def systemCellN (s : Session) (cellId source : String) : Session × Except (String × String × Option (Nat × Nat)) SysResult :=
  match withNested Sys.commands "sys.inner" systemCell (·.derivation) (·.value) s cellId source with
  | (s, .ok (r, steps)) => (s.prependSteps cellId steps, .ok { r with derivation := { r.derivation with steps := steps ++ r.derivation.steps } })
  | (s, .error e) => (s, .error e)

end MathEngine
