import MathEngine.Integrate
import MathEngine.Origin
import MathEngine.Parser
import MathEngine.Lambda
import MathEngine.Poset
import MathEngine.Relation
import MathEngine.Fourier
import MathEngine.Logic
/-!
# Sessions, commands and the evaluation pipeline

A session is one notebook: `let` bindings plus each cell's output and derivation (for
`engine.explain`). Notebook commands are rules too: they fire on `fn` nodes with reserved names.
The combined pipeline and its rule set live in `Pipeline.lean`; cells are normalized by `normalizeT`
(Terminate.lean), whose termination is the theorem `pipelineOrdered` (PipelineOrder.lean) — no step budget.
-/
namespace MathEngine
open Expr

structure Cell where
  output : Expr
  derivation : Derivation
  /-- A λ-cell: its steps carry the de Bruijn view too (`lambdaDbSteps`). -/
  lambda : Bool := false

structure Session where
  env : List (String × Expr) := []
  /-- `let f(x, y) = …` definitions, by name. -/
  fns : List (String × FnDef) := []
  /-- λ-cell definitions (`name := term`), by name; the Church library sits behind them. -/
  lambdas : List (String × Lam.Term) := []
  /-- Order-world values: posets and maps on them, by name. -/
  posets : List (String × Ord.Poset) := []
  pmaps : List (String × Ord.PMap) := []
  /-- Relations (order world) bound by `let`, by name. -/
  rels : List (String × Ord.Rel) := []
  /-- Logic-world formulas bound by `let`, by name. -/
  formulas : List (String × Logic.Fm) := []
  cells : List (String × Cell) := []
  /-- Outputs by evaluation number, for `%`, `%%` and `%n`; `nextOut` is the number the next
  evaluation gets (every evaluation takes one, error or not, like Mathematica's `In[n]`). -/
  outs : List (Nat × Expr) := []
  nextOut : Nat := 1

/-- Number an evaluation and remember its output, if it had one. Returns the label. -/
def Session.tick (s : Session) (out : Option Expr) : Session × Nat :=
  let n := s.nextOut
  ({ s with nextOut := n + 1, outs := match out with | some e => (n, e) :: s.outs | none => s.outs }, n)

/-- Replace `%`, `%%`, `%n` (parsed as `%prev k` / `%out n`) by the outputs they name. -/
partial def Session.resolveOuts (s : Session) : Expr → Except String Expr
  | .fn "%prev" [.num k] =>
    let k := k.val.num.toNat
    if k ≥ s.nextOut then .error (if k == 1 then "% refers to the previous output, and there is none yet" else s!"{String.mk (List.replicate k '%')} refers to output {s.nextOut - k}, which does not exist")
    else match s.outs.lookup (s.nextOut - k) with
      | some e => .ok e
      | none => .error s!"Out[{s.nextOut - k}] has no value (that evaluation failed)"
  | .fn "%out" [.num n] =>
    match s.outs.lookup n.val.num.toNat with
    | some e => .ok e
    | none => .error s!"Out[{n.toText}] is not defined"
  | e => do pure (withChildren e (← (children e).mapM s.resolveOuts))

/-- All sessions the engine knows about, keyed by `sessionId`. Threaded through `handle` by the host. -/
abbrev Store := List (String × Session)

def Store.get (st : Store) (id : String) : Session := (st.lookup id).getD {}
def Store.set (st : Store) (id : String) (s : Session) : Store := (id, s) :: st.filter (·.1 != id)
def Store.reset (st : Store) (id : String) : Store := st.filter (·.1 != id)

/-- Evaluate one cell: parse, substitute the session's bindings, normalize with a trace, record the
cell. Returns the updated session and either an error or the output with its derivation. -/
def evaluateCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Stmt × Expr × Derivation) :=
  match parseStmt source (s.fns.map (·.1)) with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    -- a function's parameters are bound by the definition, not by the session
    let params := match stmt with | .«let» _ ps _ => ps | _ => []
    let env := s.env.filter fun (x, _) => !params.contains x
    match s.resolveOuts stmt.value with
    | .error msg => (s, .error ("eval", msg, none))
    | .ok value =>
    let input := substitute env (substituteFns s.fns value)
    match (normalizeT pipelineRules pipelineOrdered input).run #[] with
    | (.error msg, _) => (s, .error ("eval", msg, none))
    | (.ok output, steps) =>
      let d : Derivation := ⟨input, steps, output⟩
      let s := { s with cells := (cellId, { output, derivation := d }) :: s.cells.filter (·.1 != cellId) }
      let s := match stmt with
        | .«let» name [] _ => { s with env := (name, output) :: s.env.filter (·.1 != name) }
        | .«let» name ps _ => { s with fns := (name, (ps, output)) :: s.fns.filter (·.1 != name) }
        | _ => s
      (s, .ok (stmt, output, d))

/-- The de Bruijn view of each step's result in a λ-cell's derivation, in step order. The steps
store the encoded term; decode it. -/
def lambdaDbSteps (d : Derivation) : Array Expr :=
  d.steps.map fun st => Lam.dbToExpr (Lam.toDB [] ((Lam.ofExpr st.after).getD (.var "?")))

/-- What a λ-cell produced. -/
structure LamResult where
  name : Option String
  input : Lam.Term
  output : Lam.Term
  derivation : Derivation
  /-- The de Bruijn view of each step's result, in step order. -/
  dbSteps : Array Expr
  reading : Option String

/-- The names a λ-cell may use: the session's definitions, then the Church library. -/
def lambdaDefs (s : Session) : List (String × Lam.Term) := s.lambdas ++ Lam.churchDefs

/-- Is the source a λ-cell for this session? -/
def isLambdaCell (s : Session) (source : String) : Bool :=
  Lam.isLambdaSource source ((lambdaDefs s).map (·.1))

/-- Evaluate a λ-cell: unfold definitions (one δ-step), then reduce in normal order, one β-step at
a time, every step recorded with its de Bruijn view. A term without a normal form after
`Lam.maxSteps` steps is refused — the one budget in the engine, since the question is undecidable. -/
def lambdaCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) LamResult :=
  match Lam.parseStmt source with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok (name, t) =>
    let expanded := Lam.expandDefs (lambdaDefs s) t
    let (out, trace, normal) := Lam.reduce expanded
    if !normal then
      (s, .error ("eval", s!"λ: no normal form after {Lam.maxSteps} β-steps; the term had become {(Lam.toExpr out).toText}", none))
    else
      let δ : Array Step := if expanded != t then
          #[⟨"lambda.delta", "δ: unfold the definitions used (the session's, then the Church library's).", [], Lam.toExpr t, Lam.toExpr expanded, none⟩]
        else #[]
      let (steps, _) := trace.foldl (fun (acc, prev) (t', renamed) =>
          let step : Step := if renamed then
              ⟨"lambda.alpha-beta", "α then β: a binder of the body was renamed so the argument's free variables are not captured, then the leftmost-outermost redex $(\\lambda x.\\, b)\\ a$ contracted to $b[x := a]$.", [], Lam.toExpr prev, Lam.toExpr t', none⟩
            else ⟨"lambda.beta", "β: the leftmost-outermost redex $(\\lambda x.\\, b)\\ a$ contracts to $b[x := a]$.", [], Lam.toExpr prev, Lam.toExpr t', none⟩
          (acc.push step, t')) (δ, expanded)
      let d : Derivation := ⟨Lam.toExpr t, steps, Lam.toExpr out⟩
      let dbSteps := lambdaDbSteps d
      let reading := match Lam.readChurch out with
        | some n => some s!"the Church numeral {n}"
        | none => match Lam.readBool out with
          | some true => some "the Church boolean true"
          | some false => some "the Church boolean false"
          | none => none
      let s := { s with cells := (cellId, ⟨Lam.toExpr out, d, true⟩) :: s.cells.filter (·.1 != cellId) }
      let s := match name with
        | some n => { s with lambdas := (n, out) :: s.lambdas.filter (·.1 != n) }
        | none => s
      (s, .ok ⟨name, t, out, d, dbSteps, reading⟩)

/-- What an order-world cell produced: a value (encoded), the derivation, and the poset to draw. -/
structure OrdResult where
  name : Option String
  value : Expr
  derivation : Derivation
  poset : Option Ord.Poset
  summary : String
  /-- A relation to draw as a directed graph: its elements and pairs, the pairs that show a property
  failing, and the pairs a closure added. -/
  graph : Option (Ord.Rel × List (String × String) × List (String × String)) := none

/-- Evaluate an order-world cell. -/
def orderCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) OrdResult :=
  match Ord.parseStmt source with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok (name, head, args) =>
    let least := head != "gfp"
    let head := if head == "sup" then "join" else if head == "inf" then "meet" else if head == "gfp" then "lfp" else head
    let braces (xs : List String) : String := "{" ++ ", ".intercalate xs ++ "}"
    let err (msg : String) : Session × Except (String × String × Option (Nat × Nat)) OrdResult := (s, .error ("eval", msg, none))
    let getP (a : Ord.Arg) : Except String Ord.Poset := match a with
      | .elem n => match s.posets.lookup n with | some P => .ok P | none => .error s!"'{n}' is not a poset"
      | _ => .error "expected the name of a poset"
    let getR (a : Ord.Arg) : Except String Ord.Rel := match a with
      | .elem n => match s.rels.lookup n, s.posets.lookup n with
        | some R, _ => .ok R
        | none, some P => .ok (Ord.Rel.of P.elems P.le)
        | none, none => .error s!"'{n}' is not a relation"
      | _ => .error "expected the name of a relation"
    let relExpr' := Ord.relExpr
    let getF (a : Ord.Arg) : Except String Ord.PMap := match a with
      | .elem n => match s.pmaps.lookup n with | some f => .ok f | none => .error s!"'{n}' is not a map"
      | _ => .error "expected the name of a map"
    -- an element of `P`, written as a name or, for a subsets poset, as a set literal
    let getE (P : Ord.Poset) (a : Ord.Arg) : Except String String := match a with
      | .elem x => if P.elems.contains x then .ok x else .error s!"'{x}' is not an element of the poset"
      | .set xs =>
        -- a subsets-poset element is written `{a,b}`; match the literal as a set, whatever the order
        let key := xs.eraseDups
        let members (e : String) : List String := (((e.replace "{" "").replace "}" "").splitOn ",").filter (· != "")
        match P.elems.find? fun e => e.startsWith "{" && (members e).length == key.length && key.all ((members e).contains ·) with
        | some e => .ok e
        | none => .error ("{" ++ ",".intercalate xs ++ "} is not an element of the poset")
      | _ => .error "expected an element"
    let getS (P : Ord.Poset) (a : Ord.Arg) : Except String (List String) := match a with
      | .set xs => xs.mapM fun x => getE P (.elem x)
      | .elem x => (getE P (.elem x)).map ([·])
      | _ => .error "expected a set of elements"
    let step (rule text : String) (before after : Expr) : Step := ⟨rule, text, [], before, after, none⟩
    let done (value : Expr) (steps : Array Step) (P : Option Ord.Poset) (summary : String) (bindP : Option Ord.Poset := none) (bindF : Option Ord.PMap := none)
        (bindR : Option Ord.Rel := none) (graph : Option (Ord.Rel × List (String × String) × List (String × String)) := none) :
        Session × Except (String × String × Option (Nat × Nat)) OrdResult :=
      -- the derivation starts where the first step does, so the echo shows the question, not the answer
      let input := match steps[0]? with | some st => st.before | none => value
      let d : Derivation := ⟨input, steps, value⟩
      let s := { s with cells := (cellId, { output := value, derivation := d }) :: s.cells.filter (·.1 != cellId) }
      let s := match name, bindP with
        | some n, some P => { s with posets := (n, P) :: s.posets.filter (·.1 != n) }
        | _, _ => s
      let s := match name, bindF with
        | some n, some f => { s with pmaps := (n, f) :: s.pmaps.filter (·.1 != n) }
        | _, _ => s
      let s := match name, bindR with
        | some n, some R => { s with rels := (n, R) :: s.rels.filter (·.1 != n) }
        | _, _ => s
      (s, .ok ⟨name, value, d, P, summary, graph⟩)
    let withPoset (P : Ord.Poset) (steps : Array Step) (what : String) :=
      done (Ord.posetExpr P) steps (some P) what (bindP := some P)
    let bool (b : Bool) : Expr := .var (if b then "true" else "false")
    match head, args with
    | "poset", [.set xs, .rels ps] | "poset", [.set xs, .rels ps, _] =>
      match Ord.mk xs ps with
      | .error msg => err msg
      | .ok P => withPoset P #[step "order.closure" "The order is the reflexive-transitive closure of the relation given; reflexivity, antisymmetry and transitivity were checked." (Ord.setExpr xs) (Ord.posetExpr P)] s!"a poset with {P.elems.length} elements"
    | "poset", [.set xs] =>
      match Ord.mk xs [] with
      | .error msg => err msg
      | .ok P => withPoset P #[] "an antichain"
    | "divisors", [.elem n] =>
      match n.toNat? with
      | none => err "divisors takes a number"
      | some n => match Ord.divisors n with
        | .error msg => err msg
        | .ok P => withPoset P #[step "order.divisors" s!"The divisors of {n} ordered by divisibility: $a \\le b$ iff $a \\mid b$." (.num (Q.ofInt n)) (Ord.posetExpr P)] s!"the divisors of {n} under divisibility"
    | "subsets", [.set xs] =>
      let P := Ord.subsets xs
      withPoset P #[step "order.subsets" "All subsets ordered by inclusion." (Ord.setExpr xs) (Ord.posetExpr P)] s!"the {P.elems.length} subsets of a {xs.eraseDups.length}-element set under inclusion"
    | "chain", [.elem n] =>
      match n.toNat? with
      | none => err "chain takes a number"
      | some n => withPoset (Ord.chain n) #[] s!"the chain of {n} elements"
    | "map", [.elem pn, .maps ps] =>
      match getP (.elem pn) with
      | .error msg => err msg
      | .ok P =>
        match ps.find? fun (a, b) => !P.elems.contains a || !P.elems.contains b with
        | some (a, b) => err s!"{a} -> {b} mentions an element outside the poset"
        | none =>
          let f : Ord.PMap := ⟨ps⟩
          let value := Ord.setExpr (ps.map fun (a, b) => s!"{a}↦{b}")
          done value #[] none s!"a map on {pn} ({ps.length} explicit values; other elements are fixed)" (bindF := some f)
    | "hasse", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P =>
        let cov := Ord.hasse P
        withPoset P #[step "order.covers" "The Hasse diagram draws exactly the covers: $x \\lessdot y$ iff $x < y$ with nothing strictly between (order.covers_spec)." (Ord.setExpr P.elems) (.fn "hasse" (cov.map fun (a, b) => .fn "covers" [Ord.elemExpr a, Ord.elemExpr b]))] s!"{cov.length} covers"
    | "join", [p, a, b] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getE P a, getE P b with
        | .ok x, .ok y =>
          let ubs := Ord.upperBounds P [x, y]
          let s1 := step "order.upper-bounds" s!"The upper bounds of ${x}$ and ${y}$: every element above both." (Ord.setExpr [x, y]) (Ord.setExpr ubs)
          match Ord.sup P [x, y] with
          | some j => done (Ord.elemExpr j) #[s1, step "order.least" "The least of them is below every other upper bound (order.sup_spec): the join." (Ord.setExpr ubs) (Ord.elemExpr j)] none s!"{x} ∨ {y} = {j}"
          | none => err (s!"{x} and {y} have no join: the upper bounds " ++ braces ubs ++ " have no least element")
        | .error m, _ | _, .error m => err m
    | "meet", [p, a, b] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getE P a, getE P b with
        | .ok x, .ok y =>
          let lbs := Ord.lowerBounds P [x, y]
          let s1 := step "order.lower-bounds" s!"The lower bounds of ${x}$ and ${y}$: every element below both." (Ord.setExpr [x, y]) (Ord.setExpr lbs)
          match Ord.inf P [x, y] with
          | some m => done (Ord.elemExpr m) #[s1, step "order.greatest" "The greatest of them is above every other lower bound: the meet." (Ord.setExpr lbs) (Ord.elemExpr m)] none s!"{x} ∧ {y} = {m}"
          | none => err (s!"{x} and {y} have no meet: the lower bounds " ++ braces lbs ++ " have no greatest element")
        | .error m, _ | _, .error m => err m
    | "upper", [p, xs] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getS P xs with
        | .ok ys => done (Ord.setExpr (Ord.upperBounds P ys)) #[] none "upper bounds"
        | .error m => err m
    | "lower", [p, xs] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getS P xs with
        | .ok ys => done (Ord.setExpr (Ord.lowerBounds P ys)) #[] none "lower bounds"
        | .error m => err m
    | "lattice", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match Ord.latticeFailure P with
        | none => done (bool true) #[step "order.lattice" "Every pair has a join and a meet: a lattice." (Ord.setExpr P.elems) (bool true)] none "a lattice"
        | some (x, y, what) => done (bool false) #[step "order.lattice" s!"${x}$ and ${y}$ have no {what}: not a lattice." (Ord.setExpr [x, y]) (bool false)] none s!"not a lattice: {x}, {y} have no {what}"
    | "top", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match Ord.top P with
        | some t => done (Ord.elemExpr t) #[] none s!"⊤ = {t}"
        | none => err ("no top: the maximal elements are " ++ braces (Ord.maximal P))
    | "bottom", [p] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match Ord.bottom P with
        | some b => done (Ord.elemExpr b) #[] none s!"⊥ = {b}"
        | none => err ("no bottom: the minimal elements are " ++ braces (Ord.minimal P))
    | "maximal", [p] => match getP p with | .error m => err m | .ok P => done (Ord.setExpr (Ord.maximal P)) #[] none "maximal elements"
    | "minimal", [p] => match getP p with | .error m => err m | .ok P => done (Ord.setExpr (Ord.minimal P)) #[] none "minimal elements"
    | "le", [p, a, b] =>
      match getP p with
      | .error msg => err msg
      | .ok P => match getE P a, getE P b with
        | .ok x, .ok y =>
          if P.rel x y then
            -- a chain of covers from x to y, found greedily (any path in the Hasse diagram is one)
            let rec path (fuel : Nat) (cur : String) (acc : List String) : List String :=
              match fuel with
              | 0 => acc.reverse
              | f + 1 => if cur == y then acc.reverse else
                match P.elems.find? fun z => Ord.covers P cur z && P.rel z y with
                | some z => path f z (z :: acc)
                | none => acc.reverse
            let chain := path P.elems.length x [x]
            let steps := (chain.zip chain.tail).toArray.map fun (u, v) =>
              step "order.cover" s!"${u} \\lessdot {v}$: a cover in the Hasse diagram; by transitivity ${x} \\le {v}$." (Ord.elemExpr u) (Ord.elemExpr v)
            done (bool true) steps none s!"{x} ≤ {y}"
          else done (bool false) #[step "order.incomparable" s!"${x} \\le {y}$ is not in the order (and there is no chain of covers from ${x}$ to ${y}$)." (Ord.elemExpr x) (bool false)] none s!"{x} ≰ {y}"
        | .error m, _ | _, .error m => err m
    | "monotone", [p, f] =>
      match getP p, getF f with
      | .ok P, .ok F => match Ord.monotoneFailure P F with
        | none => done (bool true) #[step "order.monotone" "For every $x \\le y$, $f(x) \\le f(y)$: monotone." (Ord.setExpr P.elems) (bool true)] none "monotone"
        | some (x, y) => done (bool false) #[step "order.monotone" s!"${x} \\le {y}$ but $f({x}) = {F.apply x} \\not\\le f({y}) = {F.apply y}$: not monotone." (Ord.setExpr [x, y]) (bool false)] none s!"not monotone at {x} ≤ {y}"
      | .error m, _ | _, .error m => err m
    | "lfp", [p, f] =>
      match getP p, getF f with
      | .ok P, .ok F =>
        match (if least then Ord.bottom P else Ord.top P), Ord.monotoneFailure P F with
        | none, _ => err s!"the poset has no {if least then "bottom" else "top"} to start from"
        | _, some (x, y) => err s!"f is not monotone ({x} ≤ {y} but f({x}) ≰ f({y})), so the iteration need not reach a fixed point"
        | some start, none =>
          let chain := Ord.iterate P F start
          let last := chain.getLastD start
          if F.apply last != last then err "the iteration did not stabilize (it should on a finite poset with a monotone map)" else
          let steps := (chain.zip chain.tail).toArray.map fun (u, v) =>
            step "order.iterate" s!"$f({u}) = {v}$; the chain from ${start}$ climbs, since $f$ is monotone." (Ord.elemExpr u) (Ord.elemExpr v)
          let steps := steps.push (step "order.fixed" (if least then s!"$f({last}) = {last}$: a fixed point, and below every fixed point (order.iter_le_fixed): the least." else s!"$f({last}) = {last}$: a fixed point, and above every fixed point: the greatest.") (Ord.elemExpr last) (Ord.elemExpr last))
          done (Ord.elemExpr last) steps none s!"{if least then "lfp" else "gfp"} = {last}"
      | .error m, _ | _, .error m => err m
    | "fixpoints", [p, f] =>
      match getP p, getF f with
      | .ok P, .ok F => done (Ord.setExpr (Ord.fixedPoints P F)) #[] none "fixed points"
      | .error m, _ | _, .error m => err m
    -- relations: a relation's own name, or a poset's (its order, as a relation)
    | "rel", (.set xs) :: rest =>
      let ps := match rest with | [.maps ps] => ps | _ => []
      match ps.find? fun (a, b) => !xs.contains a || !xs.contains b with
      | some (a, b) => err s!"{a} -> {b} mentions an element outside the set"
      | none =>
        let R := Ord.Rel.of xs ps
        done (Ord.relExpr R) #[] none s!"a relation on {R.elems.length} element{if R.elems.length == 1 then "" else "s"} with {R.pairs.length} pair{if R.pairs.length == 1 then "" else "s"}" (bindR := some R) (graph := some (R, [], []))
    | "kernel", [.set xs, .maps ps] =>
      let R := Ord.kernel xs ps
      done (Ord.relExpr R) #[step "rel.kernel" "Related when they have the same label: an equivalence relation (reflexive, symmetric and transitive, since equality of labels is)." (Ord.setExpr xs) (Ord.relExpr R)] none
        s!"same label: {R.classes.length} class{if R.classes.length == 1 then "" else "es"}" (bindR := some R) (graph := some (R, [], []))
    | "reflexive", [r] | "symmetric", [r] | "antisymmetric", [r] | "transitive", [r] | "equivalence", [r] | "preorder", [r] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        let props := match head with
          | "equivalence" => ["reflexive", "symmetric", "transitive"]
          | "preorder" => ["reflexive", "transitive"]
          | p => [p]
        -- the first property that fails, its witness as text and as the pairs to mark
        let fail (p : String) : Option (String × List (String × String)) := match p with
          | "reflexive" => (Ord.reflexiveFailure R).map fun x => (s!"${x} \\mathrel\{R} {x}$ fails", [(x, x)])
          | "symmetric" => (Ord.symmetricFailure R).map fun (x, y) => (s!"${x} \\mathrel\{R} {y}$ but not ${y} \\mathrel\{R} {x}$", [(x, y)])
          | "antisymmetric" => (Ord.antisymmetricFailure R).map fun (x, y) => (s!"${x} \\mathrel\{R} {y}$ and ${y} \\mathrel\{R} {x}$ with ${x} \\ne {y}$", [(x, y), (y, x)])
          | _ => (Ord.transitiveFailure R).map fun (x, y, z) => (s!"${x} \\mathrel\{R} {y}$ and ${y} \\mathrel\{R} {z}$ but not ${x} \\mathrel\{R} {z}$", [(x, y), (y, z)])
        match props.findSome? fun p => (fail p).map (p, ·) with
        | some (p, why, bad) =>
          done (bool false) #[step s!"rel.{p}" s!"Not {p}: {why}." (relExpr' R) (bool false)] none s!"not {p}" (graph := some (R, bad, []))
        | none =>
          done (bool true) #[step s!"rel.{props.getLast!}" s!"{", ".intercalate props |>.capitalize}: every {if props.length > 1 then "condition" else "case"} checked." (relExpr' R) (bool true)] none head (graph := some (R, [], []))
    | "closure", [r, .elem kind] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        let reflAdd := Ord.reflClosureAdds R
        let symmAdd (R : Ord.Rel) := Ord.symmClosureAdds R
        let addPairs (R : Ord.Rel) (ps : List (String × String)) : Ord.Rel := ⟨R.elems, R.pairs ++ ps⟩
        let pairsText (ps : List (String × String)) := ", ".intercalate (ps.map fun (a, b) => s!"({a}, {b})")
        let trans (R : Ord.Rel) : Except String (Ord.Rel × Array Step) :=
          let (T, rounds, stable) := Ord.transClosure R
          if !stable then .error "the transitive closure did not settle (please report this)" else
          let (_, steps) := rounds.foldl (fun (cur, acc) add =>
            let nxt := addPairs cur add
            (nxt, acc.push (step "rel.transitive-closure" s!"Each pair forced by two that chain ($a \\mathrel\{R} b$ and $b \\mathrel\{R} c$ give $a \\mathrel\{R} c$): {pairsText add}." (relExpr' cur) (relExpr' nxt)))) (R, #[])
          .ok (T, steps)
        let finish (T : Ord.Rel) (steps : Array Step) := done (relExpr' T) steps none s!"{kind} closure: {T.pairs.length - R.pairs.length} pair{if T.pairs.length - R.pairs.length == 1 then "" else "s"} added" (bindR := some T)
          (graph := some (T, [], T.pairs.filter fun (a, b) => !R.has a b))
        match kind with
        | "reflexive" =>
          let T := addPairs R reflAdd
          finish T (if reflAdd.isEmpty then #[] else #[step "rel.reflexive-closure" s!"Each element related to itself: {pairsText reflAdd}." (relExpr' R) (relExpr' T)])
        | "symmetric" =>
          let add := symmAdd R
          let T := addPairs R add
          finish T (if add.isEmpty then #[] else #[step "rel.symmetric-closure" s!"Each pair turned round: {pairsText add}." (relExpr' R) (relExpr' T)])
        | "transitive" => match trans R with | .ok (T, st) => finish T st | .error m => err m
        | "equivalence" =>
          let R1 := addPairs R reflAdd
          let a2 := symmAdd R1
          let R2 := addPairs R1 a2
          match trans R2 with
          | .error m => err m
          | .ok (T, st) =>
            let s0 := if reflAdd.isEmpty then #[] else #[step "rel.reflexive-closure" s!"Each element related to itself: {pairsText reflAdd}." (relExpr' R) (relExpr' R1)]
            let s1 := if a2.isEmpty then #[] else #[step "rel.symmetric-closure" s!"Each pair turned round: {pairsText a2}." (relExpr' R1) (relExpr' R2)]
            finish T (s0 ++ s1 ++ st)
        | k => err s!"closure: {k} is not reflexive, symmetric, transitive or equivalence"
    | "classes", [r] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        match (Ord.reflexiveFailure R).map (fun _ => "reflexive") <|> (Ord.symmetricFailure R).map (fun _ => "symmetric") <|> (Ord.transitiveFailure R).map (fun _ => "transitive") with
        | some p => err s!"classes are for equivalence relations, and this one is not {p} (closure(R, equivalence) makes it one)"
        | none =>
          let cs := R.classes
          done (Ord.partitionExpr cs) #[step "rel.classes" "Each element's class is everything related to it; for an equivalence relation the classes partition the set." (relExpr' R) (Ord.partitionExpr cs)] none s!"{cs.length} class{if cs.length == 1 then "" else "es"}" (graph := some (R, [], []))
    | "finer", [r, t] =>
      match getR r, getR t with
      | .ok R, .ok T =>
        match Ord.finerFailure R T with
        | none => done (bool true) #[step "rel.finer" "Every pair of the first is a pair of the second: finer (for equivalences, each class of the first lies inside a class of the second)." (relExpr' R) (bool true)] none "finer"
        | some (x, y) => done (bool false) #[step "rel.finer" s!"${x}$ and ${y}$ are related by the first but not by the second: not finer." (relExpr' R) (bool false)] none s!"not finer: ({x}, {y})" (graph := some (R, [(x, y)], []))
      | .error m, _ | _, .error m => err m
    | "wellfounded", [r] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        match Ord.findCycle R with
        | none => done (bool true) #[step "rel.wellfounded" "No cycle: on a finite set every chain of steps stops, so the relation is well-founded." (relExpr' R) (bool true)] none "well-founded" (graph := some (R, [], []))
        | some c =>
          let edges := c.zip c.tail
          done (bool false) #[step "rel.wellfounded" s!"A cycle: {" → ".intercalate c}; following it never stops." (relExpr' R) (bool false)] none s!"not well-founded: {" → ".intercalate c}" (graph := some (R, edges, []))
    | "measure", [r, .maps ps] =>
      match getR r with
      | .error m => err m
      | .ok R =>
        let m (x : String) : Option Int := (ps.lookup x).bind fun v => (if v.startsWith "-" then (v.drop 1).toNat?.map (- ·) else v.toNat?.map Int.ofNat)
        match R.elems.find? fun x => (m x).isNone with
        | some x => err s!"measure: no number for {x}"
        | none =>
          match Ord.measureFailure R m with
          | none => done (bool true) #[step "rel.measure" "The measure goes down along every step, and a natural number cannot go down forever: well-founded." (relExpr' R) (bool true)] none "the measure decreases along every step"
          | some (x, y) => done (bool false) #[step "rel.measure" s!"The step ${x} \\to {y}$ does not decrease the measure ({(m x).getD 0} to {(m y).getD 0})." (relExpr' R) (bool false)] none s!"not decreasing at {x} → {y}" (graph := some (R, [(x, y)], []))
    | h, _ => err s!"{h}: wrong arguments (see the reference)"

/-- What a logic cell produced: its value (a formula, a truth value, or an assignment written as a
conjunction of literals), its derivation, a one-line summary, and for `truthtable` the table. -/
structure LogicResult where
  name : Option String
  value : Expr
  derivation : Derivation
  summary : String
  /-- The variables, then one row per assignment: the variables' values and the formula's. -/
  table : Option (List String × List (List Bool)) := none

/-- A number from an expression of a logic cell: its bound variables (`env`) and the session's names
put in, then the pipeline. -/
def logicNum (s : Session) (env : List (String × Q)) (e : Expr) : Option Q :=
  let e := substitute s.env (substituteFns s.fns (substitute (env.map fun (x, q) => (x, .num q)) e))
  match (normalizeT pipelineRules pipelineOrdered e).run #[] with
  | (.ok (.num q), _) => some q
  | _ => none

/-- Evaluate a logic cell. -/
def logicCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) LogicResult :=
  match Logic.parseStmt source with
  | .error msg => (s, .error ("syntax", msg, none))
  | .ok stmt =>
    let err (msg : String) : Session × Except (String × String × Option (Nat × Nat)) LogicResult := (s, .error ("eval", msg, none))
    let prep (f : Logic.Fm) : Logic.Fm := Logic.expand s.formulas f
    let tv (b : Bool) : Logic.Fm := if b then .tt else .ff
    let step (rule text : String) (before after : Expr) : Step := ⟨rule, text, [], before, after, none⟩
    let done (name : Option String) (input : Expr) (value : Logic.Fm) (steps : Array Step) (summary : String)
        (table : Option (List String × List (List Bool)) := none) :
        Session × Except (String × String × Option (Nat × Nat)) LogicResult :=
      let out := value.toExpr
      let d : Derivation := ⟨input, steps, out⟩
      let s := { s with cells := (cellId, { output := out, derivation := d }) :: s.cells.filter (·.1 != cellId) }
      let s := match name with
        | some n => { s with formulas := (n, value) :: s.formulas.filter (·.1 != n) }
        | none => s
      (s, .ok ⟨name, out, d, summary, table⟩)
    -- a propositional formula with at most `limit` variables, for the truth-table commands
    let propOnly (f : Logic.Fm) (what : String) (limit := Logic.maxVars) : Except String (List String) :=
      if !f.isProp then .error s!"{what} is for propositional formulas; {f.toText} has arithmetic or quantifiers in it (write it on its own to evaluate it)"
      else if f.vars.length > limit then .error s!"{what}: {f.vars.length} variables, more than {limit}"
      else .ok f.vars
    let num := logicNum s
    match stmt with
    | .fm name f =>
      let f := prep f
      if f.isProp && !f.vars.isEmpty then
        done name f.toExpr f #[] s!"a formula in {", ".intercalate f.vars}"
      else if f.isProp then
        let b := f.eval (fun _ => false)
        done name f.toExpr (tv b) #[step "logic.evaluate" "A formula with no variables has one value, read off its connectives' truth tables." f.toExpr (tv b).toExpr] (if b then "true" else "false")
      else
        match Logic.decide num [] f, Logic.decidingElement num f with
        | .error m, _ | _, .error m => err m
        | .ok b, .ok el =>
          let why := match el, f with
            | some (x, v), .all _ _ body => s!"Not for every ${x}$: at ${x} = {v.toText}$, ${(Logic.instantiate x (.num v) body).toExpr.toLatex}$ is false."
            | some (x, v), .ex _ _ body => s!"A witness: at ${x} = {v.toText}$, ${(Logic.instantiate x (.num v) body).toExpr.toLatex}$ holds."
            | none, .all x _ _ => s!"Every ${x}$ of the domain was checked: the body holds for each."
            | none, .ex x _ _ => s!"Every ${x}$ of the domain was checked: the body holds for none."
            | _, _ => "Each atom evaluated, then the connectives."
          let summary := match el with
            | some (x, v) => s!"{if b then "true" else "false"} ({x} = {v.toText})"
            | none => if b then "true" else "false"
          done name f.toExpr (tv b) #[step "logic.bounded" why f.toExpr (tv b).toExpr] summary
    | .cmd name head args =>
      let args := args.map prep
      match head, args with
      | "truthtable", [f] =>
        match propOnly f "truthtable" 8 with
        | .error m => err m
        | .ok vs =>
          let rows := (Logic.rows vs).map fun r => r ++ [f.eval (Logic.assignment vs r)]
          let k := (rows.filter fun r => r.getLastD false).length
          done name (.fn "truthtable" [f.toExpr]) f #[] s!"true in {k} of {rows.length} rows" (some (vs, rows))
      | "taut", [f] =>
        match propOnly f "taut" with
        | .error m => err m
        | .ok vs =>
          match Logic.findRow vs (fun σ => !f.eval σ) with
          | none => done name (.fn "taut" [f.toExpr]) .tt #[step "logic.truthtable" s!"True in every one of the {(Logic.rows vs).length} rows of its truth table: a tautology." f.toExpr Logic.Fm.tt.toExpr] "a tautology"
          | some r => done name (.fn "taut" [f.toExpr]) .ff #[step "logic.truthtable" s!"False when {Logic.rowText vs r}: not a tautology." f.toExpr Logic.Fm.ff.toExpr] s!"false when {Logic.rowText vs r}"
      | "sat", [f] | "falsify", [f] =>
        match propOnly f head with
        | .error m => err m
        | .ok vs =>
          let want := head == "sat"
          match Logic.findRow vs (fun σ => f.eval σ == want) with
          | some r =>
            let lit := Logic.literals vs r
            done name (.fn head [f.toExpr]) lit #[step "logic.truthtable" s!"The first row of its truth table where it is {if want then "true" else "false"}: {Logic.rowText vs r}." f.toExpr lit.toExpr] s!"{if want then "satisfied" else "falsified"} by {Logic.rowText vs r}"
          | none => done name (.fn head [f.toExpr]) .ff #[step "logic.truthtable" s!"{if want then "False" else "True"} in every row: {if want then "unsatisfiable" else "a tautology"}, so no assignment does it (⊥: none)." f.toExpr Logic.Fm.ff.toExpr] (if want then "unsatisfiable" else "a tautology: nothing falsifies it")
      | "equiv", [f, g] =>
        match propOnly (.and f g) "equiv" with
        | .error m => err m
        | .ok vs =>
          match Logic.findRow vs (fun σ => f.eval σ != g.eval σ) with
          | none => done name (.fn "equiv" [f.toExpr, g.toExpr]) .tt #[step "logic.truthtable" s!"The same value in each of the {(Logic.rows vs).length} rows: equivalent." (.fn "equiv" [f.toExpr, g.toExpr]) Logic.Fm.tt.toExpr] "equivalent"
          | some r => done name (.fn "equiv" [f.toExpr, g.toExpr]) .ff #[step "logic.truthtable" s!"They differ when {Logic.rowText vs r}: the first is {f.eval (Logic.assignment vs r)}, the second {g.eval (Logic.assignment vs r)}." (.fn "equiv" [f.toExpr, g.toExpr]) Logic.Fm.ff.toExpr] s!"not equivalent: they differ when {Logic.rowText vs r}"
      | "nnf", [f] | "cnf", [f] | "dnf", [f] =>
        if !f.isProp then err s!"{head} is for propositional formulas; {f.toText} has arithmetic or quantifiers in it" else
        let (r, steps) := Logic.toNormal head f
        if !Logic.hasShape head r then err s!"{head}: the result {r.toText} is not in {head.toUpper} (please report this)" else
        done name f.toExpr r steps s!"{head.toUpper}: {steps.size} step{if steps.size == 1 then "" else "s"}"
      | h, _ => err s!"{h}: wrong arguments (see the reference)"

/-- A sampled plot: the variable, the range, and one series per function — its normalized term and
`(t, y)` pairs (`none` where it has no finite value). A `parametric` series is a complex-valued
curve: its pairs are `(re, im)`, drawn in the plane. -/
structure PlotSeries where
  term : Expr
  points : Array (Float × Option Float)
  parametric : Bool := false

structure Plot where
  var : String
  from_ : Float
  to : Float
  series : Array PlotSeries
  /-- `epicycles`/`dft` only: the rotating terms `(k, c_k)` as numbers, each with its exact term when
  there is one. -/
  terms : Array (Int × CF × Option Expr) := #[]

/-- The curves a plot argument names: a list `[f, g, …]` (which the parser reads as a one-row
matrix; a column is accepted too) is one curve per entry, a scalar is one curve, and a genuine
matrix is none. -/
def plotFns : Expr → Option (List Expr)
  | .matrix [row] => some row
  | .matrix rows => if rows.all (·.length == 1) then some (rows.filterMap List.head?) else none
  | e => some [e]

/-- A list of points for `dft`: complex numbers, or `[x, y]` pairs, in a row or a column. -/
def samplePoints (e : Expr) : Except String (Array CF) := do
  let entries ← match e with
    | .matrix [row] => pure row
    | .matrix rows =>
      if rows.all (·.length == 1) then pure (rows.filterMap List.head?)
      else if rows.all (·.length == 2) then pure (rows.map fun r => .add [r[0]!, .mul [r[1]!, iE]])
      else throw "dft: give the points as complex numbers [z₁, z₂, …] or as pairs [x₁, y₁; x₂, y₂; …]"
    | _ => throw "dft takes a list of points"
  let pts ← entries.mapM fun z => match evalNumericC [] z with
    | .ok v => pure v
    | .error m => throw s!"dft: {m}"
  pure pts.toArray

private def sampleReal (x : String) (lo hi : Float) (n : Nat) (g : Expr) : Array (Float × Option Float) :=
  (Array.range n).map fun i =>
    let t := lo + (hi - lo) * i.toFloat / (n - 1).toFloat
    (t, (evalNumeric [(x, t)] g).toOption.filter fun v => v.isFinite)

private def sampleComplex (x : String) (lo hi : Float) (n : Nat) (g : Expr) : Array (Float × Option Float) :=
  (Array.range n).map fun i =>
    let t := lo + (hi - lo) * i.toFloat / (n - 1).toFloat
    match (evalNumericC [(x, t)] g).toOption.filter CF.isFinite with
    | some z => (z.re, some z.im)
    | none => (0, none)

/-- `plot(f, x, from, to[, n])`, `plot([f, g, …], x, from, to[, n])`, `epicycles(f, t[, n])` and
`dft(points[, modes])`: simplify the function (or the list, entrywise) under the session — so
derivatives and session functions plot as what they are — record the cell like any other, and
sample. A curve that mentions `i` is complex-valued and is drawn in the plane (`parametric`).
`epicycles` reads the `(k, c_k)` off a finite Fourier sum and samples the curve over `[0, 2π]`;
`dft` computes the coefficients of sample points numerically, keeps the `modes` largest, and does
the same. Sampling and the DFT are presentation: the derivation shown is the term's. -/
def plotCell (s : Session) (cellId source : String) :
    Session × Except (String × String × Option (Nat × Nat)) (Expr × Expr × Derivation × Plot) :=
  match parseStmt source (s.fns.map (·.1)) with
  | .error e => (s, .error ("syntax", e.message, some (e.start, e.stop)))
  | .ok stmt =>
    let bad := (s, .error ("eval", "plot takes a function, a variable, and the range: plot(f, x, from, to); epicycles(f, t); dft(points)", none))
    match s.resolveOuts stmt.value with
    | .error msg => (s, .error ("eval", msg, none))
    | .ok value =>
    let num (e : Expr) : Option Float := (evalNumeric [] (substitute s.env (substituteFns s.fns e))).toOption
    -- normalize a term under the session, record the cell, and hand back the derivation
    let record (x : String) (f : Expr) : Session × Except String (Expr × Derivation) :=
      let input := substitute (s.env.filter (·.1 != x)) (substituteFns s.fns f)
      match (normalizeT pipelineRules pipelineOrdered input).run #[] with
      | (.error msg, _) => (s, .error msg)
      | (.ok output, steps) =>
        let d : Derivation := ⟨input, steps, output⟩
        ({ s with cells := (cellId, { output, derivation := d }) :: s.cells.filter (·.1 != cellId) }, .ok (output, d))
    let samples (rest : List Expr) (dflt : Nat) : Nat := match rest with
      | [.num k] => min 4000 (max 2 k.val.num.toNat)
      | _ => dflt
    match value with
    | .fn "plot" (f :: .var x :: a :: b :: rest) =>
      match num a, num b with
      | some lo, some hi =>
        let n := samples rest 300
        match record x f with
        | (s, .error msg) => (s, .error ("eval", msg, none))
        | (s, .ok (output, d)) =>
          match plotFns output with
          | none => (s, .error ("eval", "plot: give one function or a list [f, g, …], not a matrix", none))
          | some fns =>
            let series := fns.toArray.map fun g =>
              if mentionsI g then ⟨g, sampleComplex x lo hi n g, true⟩ else ⟨g, sampleReal x lo hi n g, false⟩
            (s, .ok (f, output, d, ⟨x, lo, hi, series, #[]⟩))
      | _, _ => (s, .error ("eval", "plot: the range must evaluate to numbers", none))
    | .fn "epicycles" (f :: .var t :: rest) =>
      match record t f with
      | (s, .error msg) => (s, .error ("eval", msg, none))
      | (s, .ok (output, d)) =>
        -- distribute first (the pipeline never does): 2i/π·(e^{−it} − e^{it}) is two terms, not one
        match fourierTerms output t <|> fourierTerms (Expand.dist output) t with
        | none => (s, .error ("eval", s!"epicycles: {output.toText} is not a finite sum of terms c·exp(i·k·{t}) with integer k", none))
        | some fts =>
          match fts.mapM fun ft => (evalNumericC [] ft.coeff).toOption.map fun c => (ft.k, c, some ft.coeff) with
          | none => (s, .error ("eval", "epicycles: a coefficient could not be evaluated numerically (unbound variable?)", none))
          | some terms =>
            -- slow, big circles first: by |k|, then k
            let terms := terms.toArray.qsort fun (k₁, _, _) (k₂, _, _) => k₁.natAbs < k₂.natAbs || (k₁.natAbs == k₂.natAbs && k₁ < k₂)
            let n := samples rest 400
            let trace := (epicycleTrace (terms.map fun (k, c, _) => (k, c)) n).map fun (x, y) => (x, some y)
            (s, .ok (f, output, d, ⟨t, 0, 2 * 3.141592653589793, #[⟨output, trace, true⟩], terms⟩))
    -- `epicycles(points[, modes])` — a list of points instead of a Fourier sum — is `dft`
    | .fn "dft" (p :: rest) | .fn "epicycles" (p :: rest) =>
      match samplePoints (substitute s.env (substituteFns s.fns p)) with
      | .error msg => (s, .error ("eval", msg, none))
      | .ok pts =>
        let all := dft pts
        let modes := match rest with | [.num k] => k.val.num.toNat | _ => all.size
        -- keep the `modes` largest coefficients (an approximation; all of them reproduce the samples exactly)
        let sorted := all.qsort fun (_, a) (_, b) => a.abs > b.abs
        let kept := (sorted.extract 0 (min modes sorted.size)).qsort fun (k₁, _) (k₂, _) => k₁.natAbs < k₂.natAbs || (k₁.natAbs == k₂.natAbs && k₁ < k₂)
        let n := max 400 pts.size
        let trace := (epicycleTrace kept n).map fun (x, y) => (x, some y)
        let terms := kept.map fun (k, c) => (k, c, (none : Option Expr))
        let d : Derivation := ⟨value, #[], value⟩
        let s := { s with cells := (cellId, { output := value, derivation := d }) :: s.cells.filter (·.1 != cellId) }
        (s, .ok (p, value, d, ⟨"t", 0, 2 * 3.141592653589793, #[⟨value, trace, true⟩], terms⟩))
    | _ => bad

def isPrefix : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefix as bs

/-- Which of a cell's terms a path refers to. -/
inductive TermRef where
  | input
  | output
  | step (n : Nat)

/-- The subterm at `path` in the chosen term, and the steps that produced it with how (M6 origin
tracking, `Origin.lean`). Steps come back in derivation order, each once; the relations carry the
finer story (a step can both create a node and copy one of its parts). -/
def explainCell (s : Session) (cellId : String) (path : Path) (ref : TermRef := .output) :
    Except String (Expr × Array Step × List (Nat × Relation)) :=
  match s.cells.lookup cellId with
  | none => .error s!"unknown cell {cellId}"
  | some cell =>
    let d := cell.derivation
    let (term, k) : Expr × Nat := match ref with
      | .input => (d.input, 0)
      | .output => (cell.output, d.steps.size)
      | .step n => ((d.steps[n]?.map (·.after)).getD cell.output, n)
    match term.at? path with
    | none => .error s!"bad path {path}"
    | some sub =>
      let infos := d.steps.map fun st => ({ before := st.before, after := st.after, path := st.path } : StepInfo)
      let rels := match ref with
        | .input => []
        | _ => trace infos cell.output k path
      -- one relation per step: created beats copied beats contains
      let rank : Relation → Nat | .created => 0 | .copied => 1 | .contains => 2
      let indices := (rels.map (·.1)).eraseDups.mergeSort (· ≤ ·)
      let best := indices.map fun i =>
        let rs := (rels.filter (·.1 == i)).map (·.2)
        (i, rs.foldl (fun b r => if rank r < rank b then r else b) .contains)
      let steps := best.filterMap fun (i, _) => d.steps[i]?
      .ok (sub, steps.toArray, best)

end MathEngine
