import MathEngine.Integrate
import MathEngine.Print
import MathEngine.Json
/-!
# Backpropagation: reverse-mode differentiation on a computation graph

`backprop(f, [x₁, …, xₙ], [a₁, …, aₙ])` reads `f` as a **computation graph**: a node for each
variable and each operation, an operation's node pointing at the nodes it reads (a subterm written
twice is one node, read twice). It then makes two passes:

* the **forward pass** gives each node its value at the point `xᵢ = aᵢ`, from the inputs up;
* the **backward pass** gives each node its gradient `∂f/∂n`, from the output down: the output's is
  `1`, and a node's is the sum, over the nodes that read it, of their gradient times the local
  derivative `∂p/∂n` — the chain rule, with each product formed once and shared by everything below.

The gradients of `x₁ … xₙ` are the answer, as a row vector. The passes are in IEEE-754 double
precision and are not proved; the answer is **checked**: `diff` differentiates `f` by its rules, which
the rule statuses vouch for, and its derivatives evaluated at the point must agree with the backward
pass to within `10⁻⁹` (relatively), or the command refuses. Every other free variable of `f` must be
bound in the session (it is put in first) or be one of the `xᵢ`.

The session-level command (`Session.evaluateCell`) is not a pipeline rule: it runs on a whole cell,
like `plot`, so `PipelineOrder.lean` has nothing to say about it.
-/
namespace MathEngine
namespace AD
open Expr

/-- A node of the graph: the subterm it computes and, for each of that subterm's children, the node
that computes it, or `none` for a constant (a child with no free variable). A variable has no
children. -/
structure Node where
  term : Expr
  kids : List (Option Nat)
  deriving Inhabited

/-- The graph of `e`, its nodes in an order where every node comes after the nodes it reads, and
the index of `e`'s own node. A subterm already in the graph is not added again. -/
partial def build (e : Expr) (g : Array Node) : Except String (Nat × Array Node) := do
  match g.findIdx? (fun n => equal n.term e) with
  | some i => return (i, g)
  | none =>
    match e with
    | .var _ => return (g.size, g.push ⟨e, []⟩)
    | .matrix _ => throw "backprop: the function must be a number, not a matrix"
    | .num _ => throw "backprop: the function is a constant"
    | _ =>
      let mut g := g
      let mut kids : Array (Option Nat) := #[]
      for c in children e do
        if c.freeVars.isEmpty then kids := kids.push none
        else
          let (i, g') ← build c g
          g := g'
          kids := kids.push (some i)
      return (g.size, g.push ⟨e, kids.toList⟩)

/-- The term as the graph reads it: a factor `1` left out (`1/u` parses as `1 · u⁻¹`), so a node is
not repeated by a product that does nothing. -/
partial def tidy : Expr → Expr
  | .mul es =>
    match (es.map tidy).filter (fun e => !equal e (.num (Q.ofInt 1))) with
    | [] => .num (Q.ofInt 1)
    | [e] => e
    | es => .mul es
  | e => withChildren e ((children e).map tidy)

/-- A number for an explanation: four significant digits. -/
def short (x : Float) : String :=
  match Q.ofFloat x with
  | some q => (Expr.num (Q.roundSig q 4)).toLatex
  | none => toString x

/-- `short`, in parentheses when negative, for a factor of a product. -/
def factor (x : Float) : String := if x < 0 then s!"({short x})" else short x

/-- The local derivative of a node with respect to its `j`-th child, from the children's values
`cs` and the node's own value `v`. -/
def local? (t : Expr) (cs : List Float) (v : Float) (j : Nat) : Except String Float :=
  let c := cs.getD j 0
  match t with
  | .add _ => .ok 1
  | .mul _ => .ok ((cs.eraseIdx j).foldl (· * ·) 1)
  | .pow _ _ =>
    let b := cs.getD 0 0
    let k := cs.getD 1 0
    if j == 0 then .ok (k * Float.pow b (k - 1))
    else if b > 0 then .ok (v * Float.log b)
    else .error "backprop: a variable exponent needs a positive base"
  | .fn "exp" [_] => .ok v
  | .fn "ln" [_] => .ok (1 / c)
  | .fn "sin" [_] => .ok (Float.cos c)
  | .fn "cos" [_] => .ok (-Float.sin c)
  | .fn "tan" [_] => .ok (1 / (Float.cos c * Float.cos c))
  | .fn "sqrt" [_] => .ok (1 / (2 * v))
  | .fn "arctan" [_] => .ok (1 / (1 + c * c))
  | .fn f _ => .error s!"backprop: no local derivative for {f} (it reads +, ·, powers, exp, ln, sin, cos, tan, sqrt and arctan)"
  | _ => .ok 0

/-- An arrow of the graph: from the node read to the node reading it, with the local derivative. -/
structure Edge where
  src : Nat
  dst : Nat
  local_ : Float

structure Result where
  vars : List String
  nodes : Array Node
  root : Nat
  values : Array Float
  grads : Array Float
  edges : Array Edge
  /-- The listed variables' gradients, in order. -/
  gradient : List Float

/-- The two passes over the graph of `f` at the point `vars = vals`. -/
def run (f : Expr) (vars : List String) (vals : List Float) : Except String Result := do
  let (root, nodes) ← build f #[]
  let env := vars.zip vals
  -- forward: each node from the nodes it reads (a constant child is evaluated on its own)
  let mut values : Array Float := #[]
  let mut edges : Array Edge := #[]
  for n in nodes do
    let v ← match n.term with
      | .var x =>
        match env.lookup x with
        | some a => pure a
        | none => throw s!"backprop: {x} has no value (list it with the variables, or bind it with let)"
      | t => evalNumeric env t
    if !v.isFinite then throw s!"backprop: {n.term.toText} is not finite at the point"
    values := values.push v
  -- local derivatives, one per child that is a node
  for i in [0:nodes.size] do
    let n := nodes[i]!
    let cs ← ((children n.term).zip n.kids).mapM fun (c, k) => match k with
      | some j => pure values[j]!
      | none => evalNumeric env c
    for (k, j) in n.kids.zipIdx do
      if let some src := k then
        edges := edges.push ⟨src, i, ← local? n.term cs values[i]! j⟩
  -- backward: the output's gradient is 1; a node's is the sum over its readers, from the top down
  let mut grads : Array Float := Array.replicate nodes.size 0
  grads := grads.set! root 1
  for i' in [0:nodes.size] do
    let i := nodes.size - 1 - i'
    for e in edges do
      if e.dst == i then grads := grads.set! e.src (grads[e.src]! + grads[i]! * e.local_)
  let gradient := vars.map fun x => match nodes.findIdx? (fun n => equal n.term (.var x)) with
    | some i => grads[i]!
    | none => 0
  return { vars, nodes, root, values, grads, edges, gradient }

/-- What a node does, for the picture: a variable's name, or its operation, with a constant it
reads written in (`×2`, `+1`, `^2`). -/
def opLabel (n : Node) : String :=
  let consts := ((children n.term).zip n.kids).filterMap fun (c, k) => if k.isNone then some c else none
  let cs := " ".intercalate (consts.map fun c => c.toLatex)
  match n.term with
  | .var x => (Expr.var x).toLatex
  | .add _ => if consts.isEmpty then "+" else s!"+\\,{cs}"
  | .mul _ => if consts.isEmpty then "\\times" else s!"\\times {cs}"
  | .pow _ (.num k) => if k == Q.ofInt (-1) then "1/\\square" else s!"\\square^\{{(Expr.num k).toLatex}}"
  | .pow _ _ => "\\square^\\square"
  | .fn f _ => s!"\\operatorname\{{f}}"
  | _ => "?"

/-- The term of node `i` with the nodes it reads written as their values: what the forward pass
computes there. -/
def withValues (r : Result) (i : Nat) : Expr :=
  let n := r.nodes[i]!
  let kids := ((children n.term).zip n.kids).map fun (c, k) => match k with
    | some j => match Q.ofFloat r.values[j]! with | some q => Expr.num (Q.roundSig q 4) | none => c
    | none => c
  withChildren n.term kids

/-- A list argument: `[a, b, …]` (a row, or a column), or one entry. -/
def listArg : Expr → List Expr
  | .matrix [row] => row
  | .matrix rows => if rows.all (·.length == 1) then rows.filterMap List.head? else rows.flatten
  | e => [e]

def usage := "backprop takes a function, the variables, and their values: backprop(f, [x, y], [1, 2])"

/-- The variables and values of a call, and the function. -/
def readCall : Expr → Except String (Expr × List String × List Float × List Expr)
  | .fn "backprop" [f, vs, as] => do
    let vars ← (listArg vs).mapM fun | .var x => pure x | e => throw s!"backprop: {e.toText} is not a variable"
    let vals ← (listArg as).mapM fun a => match evalNumeric [] a with
      | .ok v => pure v
      | .error _ => throw s!"backprop: the value {a.toText} is not a number"
    if vars.length != vals.length then throw s!"backprop: {vars.length} {if vars.length == 1 then "variable" else "variables"} but {vals.length} {if vals.length == 1 then "value" else "values"}"
    if vars.isEmpty then throw usage
    return (f, vars, vals, listArg as)
  | _ => throw usage

def numE (x : Float) : Expr := match Q.ofFloat x with | some q => .num q | none => .num (Q.ofInt 0)
def rowE (xs : List Float) : Expr := .matrix [xs.map numE]

/-- `backprop(…)`, on the call with the session's names put in: the gradient, and the work — the
forward pass, the backward pass, and the check against `diff` (`Integrate.normCell`, the notebook's
pipeline). -/
def evaluate (call : Expr) : Except String (Result × Expr × Derivation) := do
  let (f, vars, vals, exact) ← readCall call
  let f := tidy f
  let r ← run f vars vals
  let env := vars.zip vals
  let st (rule text : String) (before after : Expr) (sub : Option Derivation := none) : Step := ⟨rule, text, [], before, after, sub⟩
  let tex (e : Expr) := e.toLatex
  -- forward: the inputs, then each operation in order
  let fwd : Array Step := (r.nodes.zipIdx).map fun (n, i) =>
    match n.term with
    | .var x => st "ad.forward" s!"Input: ${tex (.var x)} = {short r.values[i]!}$." n.term (numE r.values[i]!)
    | t => st "ad.forward" s!"${tex t}$ from the values it reads: ${tex (withValues r i)} = {short r.values[i]!}$." t (numE r.values[i]!)
  let ops := r.nodes.size - (r.nodes.filter fun n => match n.term with | .var _ => true | _ => false).size
  let out := numE r.values[r.root]!
  let forward := st "ad.forward" s!"Forward pass: the graph has {ops} operations; from the inputs up, each gets its value from the values it reads. The output is ${short r.values[r.root]!}$." call out (some ⟨call, fwd, out⟩)
  -- backward: each node but the output, from the top down, with the products that make its gradient
  let bwd : Array Step := ((List.range r.nodes.size).reverse.filter (· != r.root)).toArray.map fun i =>
    let t := r.nodes[i]!.term
    let readers := r.edges.filter (·.src == i)
    let terms := " + ".intercalate (readers.toList.map fun e => s!"{factor r.grads[e.dst]!} \\cdot {factor e.local_}")
    let many := if readers.size > 1 then s!", summed over the {readers.size} places that read it" else ""
    st "ad.backward" s!"$\\partial f / \\partial ({tex t}) = {terms} = {short r.grads[i]!}$: the gradient of what reads it times the local derivative{many}." t (numE r.grads[i]!)
  let grad := rowE r.gradient
  let backward := st "ad.backward" "Backward pass: the output's gradient is $1$. From the output down, a node's gradient is the sum, over the nodes that read it, of their gradient times the local derivative: the chain rule, with each product formed once and shared by every node below it." out grad (some ⟨out, bwd, grad⟩)
  -- the check: diff's derivatives, by its rules, evaluated at the point
  let mut symbolic : List Expr := []
  for (x, g) in vars.zip r.gradient do
    match (normCell (Expr.fn "diff" [f, .var x])).1 with
    | .error m => throw s!"backprop: could not check against diff: {m}"
    | .ok d =>
      let v ← match evalNumeric env d with
        | .ok v => pure v
        | .error m => throw s!"backprop: could not evaluate diff's derivative: {m}"
      if (v - g).abs > 1e-9 * (max 1 v.abs) then
        throw s!"backprop: the backward pass gives {g} for {x} but diff gives {v} (please report this)"
      symbolic := symbolic ++ [d]
  -- exactly, where diff's derivative at the point is a rational number
  let exactAt (d : Expr) (g : Float) : Expr := match (normCell (substitute (vars.zip exact) d)).1 with
    | .ok (.num q) => if q.approx then numE g else .num q
    | _ => numE g
  let grad : Expr := .matrix [(symbolic.zip r.gradient).map fun (d, g) => exactAt d g]
  let check := st "ad.check" s!"Checked against `diff`: differentiated symbolically by its rules and evaluated at the point, each derivative agrees with the backward pass to within $10^\{-9}$. Where it is a rational number exactly, that is the answer; otherwise the backward pass's, in double precision." (.matrix [symbolic]) grad
  return (r, grad, ⟨call, #[forward, backward, check], grad⟩)

/-- The `calculus.graph` visual: each node with what it does, its term, its value and its gradient,
and each arrow with its local derivative. -/
def graphJson (r : Result) : Json :=
  let txt (x : Float) := match Q.ofFloat x with | some q => (Expr.num (Q.roundSig q 4)).toText | none => toString x
  let node (n : Node) (i : Nat) : Json := .obj #[
    ("label", .str (opLabel n)), ("text", .str n.term.toText), ("latex", .str n.term.toLatex),
    ("value", .str (txt r.values[i]!)), ("grad", .str (txt r.grads[i]!)),
    ("input", .bool (match n.term with | .var x => r.vars.contains x | _ => false)), ("output", .bool (i == r.root))]
  .obj #[("nodes", .arr ((r.nodes.zipIdx).map fun (n, i) => node n i)),
    ("edges", .arr (r.edges.map fun e => Json.arr #[.num (toString e.src), .num (toString e.dst), .str (txt e.local_)]))]

/-- The visuals of a cell whose input is a `backprop` call. -/
def visuals (input : Expr) : Array Json :=
  match input with
  | .fn "backprop" _ =>
    match evaluate input with
    | .ok (r, _, _) => #[.obj #[("kind", .str "calculus.graph"), ("data", graphJson r)]]
    | .error _ => #[]
  | _ => #[]

end AD
end MathEngine
