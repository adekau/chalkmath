import MathEngine.Logic
import MathEngine.Relation
/-!
# The systems world: finite transition systems

A fifth world: a system is finitely many variables, each with a finite domain (a range of integers,
a set of names, or the booleans), an initial condition, and guarded actions that update variables
simultaneously. Everything here is a decision on the finite graph of reachable states:

- **Reachability** by breadth-first search, so a reachable state comes with a shortest trace;
- **invariants**, refuted by the shortest trace to a state that breaks them;
- **inductive invariants**, refuted by a counterexample to induction: a state, reachable or not, that
  satisfies the formula and has a successor that does not;
- **deadlocks** (reachable states with no enabled action), with the trace to one;
- **CTL** formulas `EF`, `AF`, `EG`, `AG`, `EX`, `AX` of a state predicate, computed as least and
  greatest fixed points on the lattice of state sets, each iteration of the Kleene chain a step;
- **liveness under weak fairness**, refuted by a lasso: a path to a cycle that avoids the goal
  forever while every fair action is either taken or disabled somewhere on it;
- **refinement**: a concrete system's steps, mapped through an abstraction, are steps or stutters of
  the abstract one.

Guards and initial conditions are logic-world formulas whose atoms compare expressions over the
variables; updates are `x := e`. A system's text may run over several lines.
-/
namespace MathEngine
namespace Sys

/-- A variable's value: an integer, or a name (`idle`, `true`). -/
inductive Val where
  | int (n : Int)
  | sym (s : String)
  deriving BEq, Hashable, Inhabited, Repr

def Val.toString : Val → String
  | .int n => s!"{n}"
  | .sym s => s
instance : ToString Val := ⟨Val.toString⟩

def Val.toExpr : Val → Expr
  | .int n => .num (Q.ofInt n)
  | .sym s => .var s

structure Var where
  name : String
  dom : List Val
  deriving Inhabited

structure Action where
  name : String
  guard : Logic.Fm
  updates : List (String × Expr)
  /-- Weakly fair: if it stays enabled it is eventually taken. -/
  fair : Bool
  /-- Strongly fair: if it is enabled again and again it is eventually taken. -/
  strong : Bool := false
  deriving Inhabited

structure System where
  vars : List Var
  init : Logic.Fm
  actions : List Action
  deriving Inhabited

/-- A state: one value per variable, in the system's order. -/
abbrev State := List Val

/-- The names that are values: every name in some variable's domain. -/
def System.syms (S : System) : List String :=
  S.vars.flatMap fun v => v.dom.filterMap fun x => match x with | .sym s => some s | _ => none

def System.env (S : System) (s : State) (x : String) : Option Val := ((S.vars.map (·.name)).zip s).lookup x

/-! ## Evaluation -/

/-- The functions an expression may call: `mod`, `div`, `max`, `min`, `abs`. -/
def fns : List String := ["mod", "div", "max", "min", "abs"]

partial def evalExpr (syms : List String) (σ : String → Option Val) : Expr → Except String Val
  | .num q => if q.val.den == 1 then .ok (.int q.val.num) else .error s!"{q.val} is not an integer"
  | .var v => match σ v with
    | some x => .ok x
    | none => if syms.contains v || v == "true" || v == "false" then .ok (.sym v) else .error s!"{v} is not a variable or a value of one"
  | .add xs => do
    let vs ← xs.mapM (evalExpr syms σ)
    let ns ← vs.mapM fun v => match v with | .int n => pure n | .sym s => throw s!"cannot add {s}"
    return .int (ns.foldl (· + ·) 0)
  | .mul xs => do
    let vs ← xs.mapM (evalExpr syms σ)
    let ns ← vs.mapM fun v => match v with | .int n => pure n | .sym s => throw s!"cannot multiply {s}"
    return .int (ns.foldl (· * ·) 1)
  | .pow b e => do
    match ← evalExpr syms σ b, ← evalExpr syms σ e with
    | .int x, .int k => if k < 0 then throw "a negative power is not an integer; write div(a, b) for division" else return .int (x ^ k.toNat)
    | _, _ => throw "powers are of integers"
  | .fn f [a, b] => do
    match f, ← evalExpr syms σ a, ← evalExpr syms σ b with
    | "mod", .int x, .int y => if y == 0 then throw "mod by 0" else return .int (x % y)
    | "div", .int x, .int y => if y == 0 then throw "div by 0" else return .int (x / y)
    | "max", .int x, .int y => return .int (max x y)
    | "min", .int x, .int y => return .int (min x y)
    | f, _, _ => throw s!"{f}: not a function of two integers here"
  | .fn "abs" [a] => do
    match ← evalExpr syms σ a with
    | .int x => return .int x.natAbs
    | _ => throw "abs of a name"
  | e => .error s!"{e.toText} is not an expression over the variables"

def asInt : Val → Except String Int
  | .int n => .ok n
  | .sym s => .error s!"{s} is not a number"

partial def evalFm (syms : List String) (σ : String → Option Val) : Logic.Fm → Except String Bool
  | .var x => match σ x with
    | some (.sym "true") => .ok true
    | some (.sym "false") => .ok false
    | some v => .error s!"{x} is {v}, not true or false"
    | none => .error s!"{x} is not a variable"
  | .tt => .ok true
  | .ff => .ok false
  | .not a => return !(← evalFm syms σ a)
  | .and a b => return (← evalFm syms σ a) && (← evalFm syms σ b)
  | .or a b => return (← evalFm syms σ a) || (← evalFm syms σ b)
  | .imp a b => return !(← evalFm syms σ a) || (← evalFm syms σ b)
  | .iff a b => return (← evalFm syms σ a) == (← evalFm syms σ b)
  | .cmp op l r => do
    let a ← evalExpr syms σ l
    let b ← evalExpr syms σ r
    match op with
    | "=" => return a == b
    | "≠" => return a != b
    | _ =>
      let x ← asInt a
      let y ← asInt b
      match op with
      | "<" => return decide (x < y)
      | "≤" => return decide (x ≤ y)
      | ">" => return decide (x > y)
      | "≥" => return decide (x ≥ y)
      | "∣" => return (if x == 0 then y == 0 else y % x == 0)
      | o => throw s!"unknown comparison {o}"
  | .pred p args => do
    let ns ← args.mapM fun e => do asInt (← evalExpr syms σ e)
    match p, ns with
    | "even", [n] => return n % 2 == 0
    | "odd", [n] => return n % 2 != 0
    | "prime", [n] => return n ≥ 2 && (List.range (n.toNat - 2)).all fun k => n.toNat % (k + 2) != 0
    | p, _ => throw s!"{p}: wrong arguments"
  | .all x d body => do
    let vs ← domVals d
    vs.allM fun v => evalFm syms (fun y => if y == x then some v else σ y) body
  | .ex x d body => do
    let vs ← domVals d
    vs.anyM fun v => evalFm syms (fun y => if y == x then some v else σ y) body
where
  domVals : Logic.Dom → Except String (List Val)
    | .range lo hi => do
      let a ← asInt (← evalExpr syms σ lo)
      let b ← asInt (← evalExpr syms σ hi)
      return (List.range ((b - a + 1).toNat)).map fun (k : Nat) => .int (a + (k : Int))
    | .list xs => xs.mapM (evalExpr syms σ)

/-! ## Parsing -/

/-- Split at the top-level separators (`;` and line breaks), dropping empty pieces. -/
def clauses (s : String) : List String :=
  let rec go : List Char → Nat → List Char → List String → List String
    | [], _, cur, acc => (String.ofList cur.reverse :: acc).reverse
    | c :: cs, d, cur, acc =>
      if (c == ';' || c == '\n') && d == 0 then go cs d [] (String.ofList cur.reverse :: acc)
      else if c == '(' || c == '{' || c == '[' then go cs (d + 1) (c :: cur) acc
      else if c == ')' || c == '}' || c == ']' then go cs (d - 1) (c :: cur) acc
      else go cs d (c :: cur) acc
  (go s.toList 0 [] []).map (·.trimAscii.copy) |>.filter (· != "")

/-- A value as written in a domain: an integer or a name. -/
def parseVal (s : String) : Val :=
  let t := s.trimAscii.copy
  match t.toInt? with | some n => .int n | none => .sym t

/-- A domain: `lo..hi`, `{a, b, c}`, or `bool`. -/
def parseDomain (s : String) : Except String (List Val) := do
  let t := s.trimAscii.copy
  if t == "bool" then return [.sym "false", .sym "true"]
  if t.startsWith "{" && t.endsWith "}" then
    let items := (((t.drop 1).dropEnd 1).copy.splitOn ",").map (·.trimAscii.copy) |>.filter (· != "")
    if items.isEmpty then throw "an empty domain"
    return items.map parseVal
  match t.splitOn ".." with
  | [a, b] => match a.trimAscii.copy.toInt?, b.trimAscii.copy.toInt? with
    | some x, some y => if y < x then throw s!"{t} is empty" else return (List.range ((y - x + 1).toNat)).map fun (k : Nat) => .int (x + (k : Int))
    | _, _ => throw s!"{t}: a range is two integers, lo..hi"
  | _ => throw s!"{t} is not a domain: write lo..hi, {"{"}a, b, c{"}"} or bool"

/-- The text after the first occurrence of `word` (as a separate word), and before it. -/
def splitWord (s : String) (word : String) : Option (String × String) :=
  match s.splitOn s!" {word} " with
  | a :: rest@(_ :: _) => some (a.trimAscii.copy, (s!" {word} ".intercalate rest).trimAscii.copy)
  | _ => none

def parseExprText (t : String) : Except String Expr :=
  match parse t.trimAscii.copy fns with
  | .ok e => .ok e
  | .error e => .error s!"{t.trimAscii}: {e.message}"

def parseUpdates (t : String) : Except String (List (String × Expr)) :=
  (Logic.splitCommas t.toList).mapM fun u => do
    let u := String.ofList u
    match u.splitOn ":=" with
    | [x, e] => return (x.trimAscii.copy, ← parseExprText e)
    | _ => throw s!"{u.trimAscii}: an update is x := expression"

/-- `[[strong] fair] action NAME [when GUARD] do UPDATES`. -/
def parseAction (t : String) : Except String Action := do
  let (strong, t) := if t.startsWith "strong " then (true, (t.drop 7).trimAscii.copy) else (false, t)
  let (fair, t) := if t.startsWith "fair " then (true, (t.drop 5).trimAscii.copy) else (false, t)
  if strong && !fair then throw "write strong fair action"
  let t := (t.drop 7).trimAscii.copy
  let (head, upd) ← match splitWord (" " ++ t) "do" with
    | some (h, u) => pure (h, u)
    | none => throw s!"action {t}: write action NAME when GUARD do x := …"
  let (name, guard) ← match splitWord (" " ++ head ++ " ") "when" with
    | some (n, g) => pure (n, ← Logic.parseFormula g)
    | none => pure (head.trimAscii.copy, Logic.Fm.tt)
  if name.isEmpty then throw "an action needs a name"
  return ⟨name, guard, ← parseUpdates upd, fair, strong⟩

/-- The body of `system(…)`: `var` declarations, one `init`, and actions, separated by `;` or line
breaks. -/
def parseSystem (body : String) : Except String System := do
  let mut vars : Array Var := #[]
  let mut init : Option Logic.Fm := none
  let mut actions : Array Action := #[]
  for c in clauses body do
    if c.startsWith "var " then
      match (c.drop 4).copy.splitOn " in " with
      | [names, dom] =>
        let d ← parseDomain dom
        for n in (names.splitOn ",").map (·.trimAscii.copy) do
          if n.isEmpty then throw "a variable needs a name"
          vars := vars.push ⟨n, d⟩
      | _ => throw s!"{c}: write var x in 0..3"
    else if c.startsWith "init " then
      if init.isSome then throw "one init condition (join conditions with ∧)"
      init := some (← Logic.parseFormula (c.drop 5).copy)
    else if c.startsWith "action " || c.startsWith "fair action " || c.startsWith "strong fair action " then
      actions := actions.push (← parseAction c)
    else throw s!"{c}: a system is var, init and action lines"
  if vars.isEmpty then throw "a system needs at least one var"
  let names := vars.toList.map (·.name)
  if names.eraseDups.length != names.length then throw "a variable is declared twice"
  for a in actions do
    for (x, _) in a.updates do
      if !names.contains x then throw s!"action {a.name} updates {x}, which is not a variable"
  return ⟨vars.toList, init.getD .tt, actions.toList⟩

/-! ## The state graph -/

/-- Every assignment of values to the variables, if there are not too many. -/
def System.allStates (S : System) (limit : Nat := 20000) : Except String (List State) := do
  let n := S.vars.foldl (fun acc v => acc * v.dom.length) 1
  if n > limit then throw s!"{n} states in all is more than {limit}"
  return S.vars.foldr (fun v acc => v.dom.flatMap fun x => acc.map (x :: ·)) [[]]

def System.holds (S : System) (φ : Logic.Fm) (s : State) : Except String Bool := evalFm S.syms (S.env s) φ

def System.initStates (S : System) : Except String (List State) := do
  (← S.allStates).filterM (S.holds S.init)

/-- The actions enabled in `s`, each with the state it leads to (updates are simultaneous), or why
it leaves a variable's domain. -/
def System.successorsE (S : System) (s : State) : Except String (List (String × Except String State)) :=
  S.actions.filterMapM fun a => do
    if !(← S.holds a.guard s) then return none
    let vals ← a.updates.mapM fun (x, e) => do return (x, ← evalExpr S.syms (S.env s) e)
    let t : Except String State := (S.vars.zip s).mapM fun (v, old) => do
      match vals.lookup v.name with
      | none => pure old
      | some new =>
        if v.dom.contains new then pure new
        else throw s!"action {a.name} sets {v.name} to {new}, outside its domain"
    return some (a.name, t)

/-- The actions enabled in `s` and the states they lead to; leaving a domain is an error. -/
def System.successors (S : System) (s : State) : Except String (List (String × State)) := do
  (← S.successorsE s).mapM fun (a, t) => do return (a, ← t)

/-- The reachable states, breadth first: the states, the edges `(from, action, to)` by index, and
each state's BFS parent (for shortest traces). -/
structure Graph where
  states : Array State
  edges : List (Nat × String × Nat)
  parent : Array (Option (Nat × String))
  inits : List Nat

def System.explore (S : System) (limit : Nat := 5000) : Except String Graph := do
  let inits ← S.initStates
  if inits.isEmpty then throw "no initial state satisfies init"
  let mut states : Array State := #[]
  let mut index : Std.HashMap State Nat := {}
  let mut parent : Array (Option (Nat × String)) := #[]
  for s in inits do
    if !index.contains s then
      index := index.insert s states.size
      states := states.push s
      parent := parent.push none
  let mut edges : Array (Nat × String × Nat) := #[]
  let mut i := 0
  -- states grow as the search goes; each is expanded once
  for _ in [0:limit + 1] do
    if i ≥ states.size then break
    let s := states[i]!
    for (a, t) in ← S.successors s do
      match index.get? t with
      | some j => edges := edges.push (i, a, j)
      | none =>
        if states.size ≥ limit then throw s!"more than {limit} reachable states"
        index := index.insert t states.size
        edges := edges.push (i, a, states.size)
        states := states.push t
        parent := parent.push (some (i, a))
    i := i + 1
  return ⟨states, edges.toList, parent, (inits.filterMap index.get?)⟩

/-- The path from an initial state to state `j`, as `(action, state)` steps after the first state. -/
def Graph.pathTo (G : Graph) (j : Nat) : Nat × List (String × Nat) := Id.run do
  let mut cur := j
  let mut acc : List (String × Nat) := []
  for _ in [0:G.states.size] do
    match G.parent[cur]! with
    | none => break
    | some (p, a) =>
      acc := (a, cur) :: acc
      cur := p
  return (cur, acc)

/-- An action as the steps that take it describe it: its name, its guard, its updates. -/
def Action.describe (a : Action) : String :=
  let upd := ", ".intercalate (a.updates.map fun (x, e) => s!"{x} := {e.toText}")
  let guard := if a.guard matches .tt then "" else s!" ({(a.guard.toExpr).toText} holds)"
  s!"{a.name}{guard}: {upd}"

/-! ## Encoding for the wire -/

/-- A state as a formula: `x = 1 ∧ y = busy`. -/
def System.stateExpr (S : System) (s : State) : Expr :=
  let eqs := (S.vars.zip s).map fun (v, x) => Expr.fn "=" [.var v.name, x.toExpr]
  match eqs with
  | [] => .var "⊤"
  | e :: es => es.foldl (fun acc e => .fn "∧" [acc, e]) e

/-- A state's short label, for the graph: `(1, busy)`. -/
def stateLabel (s : State) : String :=
  match s with
  | [x] => x.toString
  | _ => "(" ++ ", ".intercalate (s.map Val.toString) ++ ")"

/-- The label of a state written as a formula, `x = 1 ∧ y = busy` (as `System.stateExpr` writes it),
in `stateLabel`'s form: how a step of the work is found on the graph. -/
def labelOfStateExpr (e : Expr) : Option String :=
  let rec eqs : Expr → Option (List Expr)
    | .fn "∧" [a, b] => do pure ((← eqs a) ++ (← eqs b))
    | .fn "=" [.var _, v] => some [v]
    | _ => none
  match eqs e with
  | some [v] => some v.toText
  | some vs => some ("(" ++ ", ".intercalate (vs.map Expr.toText) ++ ")")
  | none => none

def stateSet (G : Graph) (xs : List Nat) : Expr := .fn "set" (xs.map fun i => .var (stateLabel G.states[i]!))

/-- The graph as a relation, for the notebook's drawing. -/
def Graph.rel (G : Graph) : Ord.Rel :=
  Ord.Rel.of (G.states.toList.map stateLabel) (G.edges.map fun (i, _, j) => (stateLabel G.states[i]!, stateLabel G.states[j]!))

/-! ## Fixed points on state sets (CTL) -/

/-- `pre∃ Z`: the states with some successor in `Z`; `pre∀ Z`: those all of whose successors are in
`Z` (a state with no successor is in it vacuously). -/
def Graph.preE (G : Graph) (Z : List Nat) : List Nat :=
  (List.range G.states.size).filter fun i => G.edges.any fun (a, _, b) => a == i && Z.contains b
def Graph.preA (G : Graph) (Z : List Nat) : List Nat :=
  (List.range G.states.size).filter fun i => G.edges.all fun (a, _, b) => a != i || Z.contains b

/-- Iterate `f` from `start` until it stops changing (at most `n + 1` rounds on `n` states); the
chain of sets. -/
def iterateSets (n : Nat) (f : List Nat → List Nat) (start : List Nat) : List (List Nat) := Id.run do
  let mut chain := [start]
  let mut cur := start
  for _ in [0:n + 2] do
    let nxt := f cur
    if nxt.length == cur.length && nxt.all cur.contains then break
    chain := chain ++ [nxt]
    cur := nxt
  return chain

end Sys
end MathEngine
