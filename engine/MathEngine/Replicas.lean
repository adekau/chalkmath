import MathEngine.Systems
/-!
# Replicas: a CRDT simulated in the notebook

`replicas(type; a, b, c; events…)` runs a state-based CRDT on named replicas through a schedule:
local updates (`a: inc`, `b: add x`), immediate syncs (`a -> b`: `b` merges `a`'s state), and
messages in flight (`m := a` copies `a`'s state now; `b <- m` delivers the copy later, and may deliver
it twice, or after newer ones). Each event is a step, and the run ends by saying whether the replicas
converged. The notebook draws it as a space-time diagram: a lane per replica, an arrow per message.

Every type here is one data structure: a vector of naturals, merged by the pointwise maximum.
- G-counter: an entry per replica, its increments. Reads the sum.
- PN-counter: two G-counters, increments then decrements. Reads the difference.
- G-set: a bit per element ever added. Reads the elements whose bit is set.
- 2P-set: an added bit and a removed bit per element. Reads added and not removed.
- OR-set: an added bit and a removed bit per *tag*, each add making a tag of its own; a remove
  removes the tags of that element the replica has seen. Reads the elements with a tag added and not
  removed: a concurrent add survives a remove.
- LWW-register: one entry, the key of the latest write, `timestamp · R + replica` (the replica breaks
  ties). Reads the value written with that key.

So `merge` is one function, and `ReplicasProofs` proves it a join (commutative, associative,
idempotent) and every update an inflation: what makes the replicas converge, whatever the order,
duplication or delay of the messages.
-/
namespace MathEngine
namespace Rep

/-- A replica's state. -/
abbrev Vec := List Nat

/-- Merge two states: the pointwise maximum. -/
def merge (a b : Vec) : Vec := List.zipWith max a b

/-- Add one to entry `i`. -/
def bump (v : Vec) (i : Nat) : Vec := v.modify i (· + 1)

/-- Raise entry `i` to at least `k`. -/
def raise (v : Vec) (i k : Nat) : Vec := v.modify i (max · k)

inductive Kind where
  | gcounter | pncounter | gset | twopset | orset | lww
  deriving BEq, Repr, Inhabited

def Kind.ofName : String → Option Kind
  | "gcounter" => some .gcounter
  | "pncounter" => some .pncounter
  | "gset" => some .gset
  | "twopset" => some .twopset
  | "orset" => some .orset
  | "lww" => some .lww
  | _ => none

def Kind.title : Kind → String
  | .gcounter => "G-counter" | .pncounter => "PN-counter" | .gset => "G-set"
  | .twopset => "2P-set" | .orset => "OR-set" | .lww => "LWW-register"

/-- The operations a type has, for an error that says which. -/
def Kind.ops : Kind → List String
  | .gcounter => ["inc"] | .pncounter => ["inc", "dec"] | .gset => ["add x"]
  | .twopset | .orset => ["add x", "remove x"] | .lww => ["write v", "write v @ t"]

/-- An event of the schedule. -/
inductive Ev where
  /-- `r: op arg` — a local update. -/
  | op (r name : String) (arg : Option String) (ts : Option Nat)
  /-- `r -> s` — `s` merges `r`'s state now. -/
  | sync (r s : String)
  /-- `m := r` — a message holding `r`'s state now. -/
  | snap (m r : String)
  /-- `s <- m` — `s` merges the message `m`. -/
  | deliver (s m : String)
  deriving Repr, Inhabited

def isName (s : String) : Bool := !s.isEmpty && s.all fun c => c.isAlphanum || c == '_' || c == '\''

/-- One event, as written. -/
def parseEv (c : String) : Except String Ev := do
  let c := c.trimAscii.copy
  let two (sep : String) : Option (String × String) :=
    match c.splitOn sep with
    | [a, b] => some (a.trimAscii.copy, b.trimAscii.copy)
    | _ => none
  if let some (m, r) := two ":=" then
    if isName m && isName r then return .snap m r else throw s!"write a message as m := replica, not '{c}'"
  if let some (s, m) := two "<-" then
    if isName s && isName m then return .deliver s m else throw s!"write a delivery as replica <- m, not '{c}'"
  if let some (r, s) := two "->" then
    if isName r && isName s then return .sync r s else throw s!"write a sync as replica -> replica, not '{c}'"
  match two ":" with
  | some (r, rest) =>
    if !isName r then throw s!"'{r}' is not a replica's name"
    let (rest, ts) ← match rest.splitOn "@" with
      | [a, t] => match t.trimAscii.copy.toNat? with
        | some n => pure (a.trimAscii.copy, some n)
        | none => throw s!"a timestamp is a number, not '{t.trimAscii}'"
      | _ => pure (rest, none)
    match (rest.splitOn " ").filter (· != "") with
    | [name] => return .op r name none ts
    | [name, arg] => return .op r name (some arg) ts
    | _ => throw s!"write an update as replica: op, or replica: op argument, not '{c}'"
  | none => throw s!"'{c}' is not an event: write a: inc, a -> b, m := a, or b <- m"

/-- A simulation's layout: the replicas, and the elements, tags and writes the schedule mentions. -/
structure Layout where
  kind : Kind
  replicas : List String
  /-- Set elements, in order of first mention. -/
  elems : List String := []
  /-- OR-set tags: the element, and the tag's name (`x@a1`: `a`'s first add). -/
  tags : List (String × String) := []
  /-- LWW writes: the key (timestamp · R + replica + 1) and the value. -/
  writes : List (Nat × String) := []

def Layout.width (L : Layout) : Nat :=
  match L.kind with
  | .gcounter => L.replicas.length
  | .pncounter => 2 * L.replicas.length
  | .gset => L.elems.length
  | .twopset => 2 * L.elems.length
  | .orset => 2 * L.tags.length
  | .lww => 1

def idx (l : List String) (x : String) : Nat := (l.idxOf? x).getD 0

/-- The layout, from a scan of the schedule: elements and tags in order, writes with their keys. -/
def layout (kind : Kind) (replicas : List String) (evs : List Ev) : Layout := Id.run do
  let mut L : Layout := { kind, replicas }
  let mut adds : List (String × Nat) := []
  let mut k := 0
  for e in evs do
    k := k + 1
    match e with
    | .op r name (some x) ts =>
      if name == "add" || name == "remove" then
        if !L.elems.contains x then L := { L with elems := L.elems ++ [x] }
      if name == "add" && kind == .orset then
        let n := (adds.lookup r).getD 0 + 1
        adds := (r, n) :: adds.filter (·.1 != r)
        L := { L with tags := L.tags ++ [(x, s!"{x}@{r}{n}")] }
      if name == "write" then
        let t := ts.getD k
        L := { L with writes := L.writes ++ [(t * replicas.length + idx replicas r + 1, x)] }
    | _ => pure ()
  return L

/-- Apply a local update. `tagNo` counts the OR-set adds so far (to find this add's tag), `k` is the
event's number (an LWW write's default timestamp). -/
def update (L : Layout) (v : Vec) (r name : String) (arg : Option String) (ts : Option Nat) (tagNo k : Nat) :
    Except String Vec := do
  let ri := idx L.replicas r
  let R := L.replicas.length
  let bad : String := s!"a {L.kind.title} has {", ".intercalate L.kind.ops}, not '{name}{(arg.map (" " ++ ·)).getD ""}'"
  match L.kind, name, arg with
  | .gcounter, "inc", none => pure (bump v ri)
  | .pncounter, "inc", none => pure (bump v ri)
  | .pncounter, "dec", none => pure (bump v (R + ri))
  | .gset, "add", some x => pure (raise v (idx L.elems x) 1)
  | .twopset, "add", some x => pure (raise v (idx L.elems x) 1)
  | .twopset, "remove", some x =>
    let i := idx L.elems x
    if v.getD i 0 == 0 then throw s!"{r} cannot remove {x}: a 2P-set removes only what the replica has added" else
    pure (raise v (L.elems.length + i) 1)
  | .orset, "add", some _ => pure (raise v tagNo 1)
  | .orset, "remove", some x =>
    -- remove the tags of x this replica has seen: the observed adds
    let T := L.tags.length
    let seen := (List.range T).filter fun i => (L.tags.getD i ("", "")).1 == x && v.getD i 0 == 1
    pure (seen.foldl (fun v i => raise v (T + i) 1) v)
  | .lww, "write", some x =>
    let key := (ts.getD k) * R + ri + 1
    let _ := x
    pure (raise v 0 key)
  | _, _, _ => throw bad

/-- What a state reads as. -/
def read (L : Layout) (v : Vec) : Expr :=
  let R := L.replicas.length
  let sumRange (a b : Nat) : Nat := ((List.range (b - a)).map fun i => v.getD (a + i) 0).foldl (· + ·) 0
  match L.kind with
  | .gcounter => .num (Q.ofInt (Int.ofNat (sumRange 0 R)))
  | .pncounter => .num (Q.ofInt (Int.ofNat (sumRange 0 R) - Int.ofNat (sumRange R (2 * R))))
  | .gset => Ord.setExpr ((List.range L.elems.length).filter (v.getD · 0 == 1) |>.map (L.elems.getD · ""))
  | .twopset =>
    let E := L.elems.length
    Ord.setExpr ((List.range E).filter (fun i => v.getD i 0 == 1 && v.getD (E + i) 0 == 0) |>.map (L.elems.getD · ""))
  | .orset =>
    let T := L.tags.length
    let live := (List.range T).filter fun i => v.getD i 0 == 1 && v.getD (T + i) 0 == 0
    Ord.setExpr ((live.map fun i => (L.tags.getD i ("", "")).1).eraseDups)
  | .lww => match L.writes.lookup (v.getD 0 0) with
    | some x => .var x
    | none => .var "⊥"

/-- A state as the work shows it. -/
def stateExpr (L : Layout) (v : Vec) : Expr :=
  let R := L.replicas.length
  let entries (off : Nat) := L.replicas.zipIdx.map fun (r, i) => s!"{r}↦{v.getD (off + i) 0}"
  let bits (names : List String) (off : Nat) := (List.range names.length).filter (fun i => v.getD (off + i) 0 == 1) |>.map (names.getD · "")
  match L.kind with
  | .gcounter => Ord.setExpr (entries 0)
  | .pncounter => .fn "pair" [Ord.setExpr (entries 0), Ord.setExpr (entries R)]
  | .gset => Ord.setExpr (bits L.elems 0)
  | .twopset => .fn "pair" [Ord.setExpr (bits L.elems 0), Ord.setExpr (bits L.elems L.elems.length)]
  | .orset =>
    let names := L.tags.map (·.2)
    .fn "pair" [Ord.setExpr (bits names 0), Ord.setExpr (bits names names.length)]
  | .lww =>
    let key := v.getD 0 0
    if key == 0 then .var "⊥" else
    match L.writes.lookup key with
    | some x => .var s!"{x}@{(key - 1) / R}"
    | none => .var "?"

/-- An event of the space-time diagram: its lane, a label, and the state after it. -/
structure DEvent where
  lane : String
  label : String
  state : String

/-- The diagram: the lanes, the events in order (each its own column), and the messages as arrows
from one event to another. -/
structure Diagram where
  lanes : List String
  events : Array DEvent
  messages : List (Nat × Nat)

structure Run where
  layout : Layout
  /-- Each step: its rule, explanation, before and after, and the diagram's events it made. -/
  steps : Array (String × String × Expr × Expr × List Nat)
  states : List (String × Vec)
  diagram : Diagram

/-- Run the schedule. -/
def run (kind : Kind) (replicas : List String) (evs : List Ev) : Except String Run := do
  let L := layout kind replicas evs
  let zero : Vec := List.replicate L.width 0
  let mut states : List (String × Vec) := replicas.map (·, zero)
  let mut msgs : List (String × Vec × Nat) := []   -- message, its state, its event in the diagram
  let mut steps : Array (String × String × Expr × Expr × List Nat) := #[]
  let mut events : Array DEvent := #[]
  let mut arrows : List (Nat × Nat) := []
  let mut tagNo := 0
  let mut k := 0
  let get (states : List (String × Vec)) (r : String) : Except String Vec :=
    match states.lookup r with
    | some v => pure v
    | none => throw s!"'{r}' is not one of the replicas ({", ".intercalate replicas})"
  let txt (v : Vec) : String := (stateExpr L v).toText
  for e in evs do
    k := k + 1
    match e with
    | .op r name arg ts =>
      let v ← get states r
      let v' ← update L v r name arg ts tagNo k
      if kind == .orset && name == "add" then tagNo := tagNo + 1
      states := states.map fun (q, w) => if q == r then (q, v') else (q, w)
      let what := s!"{name}{(arg.map (" " ++ ·)).getD ""}{(ts.map (s!" @ {·}")).getD ""}"
      steps := steps.push ("crdt.update", s!"{r}: {what}, a local update. It only raises entries of {r}'s state.", stateExpr L v, stateExpr L v', [events.size])
      events := events.push ⟨r, what, txt v'⟩
    | .sync r s =>
      let v ← get states r
      let w ← get states s
      let w' := merge w v
      states := states.map fun (q, u) => if q == s then (q, w') else (q, u)
      steps := steps.push ("crdt.merge", s!"{s} merges {r}'s state: the entrywise maximum, a join.", stateExpr L w, stateExpr L w', [events.size, events.size + 1])
      events := events.push ⟨r, s!"→ {s}", txt v⟩
      events := events.push ⟨s, s!"← {r}", txt w'⟩
      arrows := (events.size - 2, events.size - 1) :: arrows
    | .snap m r =>
      let v ← get states r
      msgs := (m, v, events.size) :: msgs.filter (·.1 != m)
      steps := steps.push ("crdt.send", s!"{m} holds a copy of {r}'s state, in flight until it is delivered.", stateExpr L v, .fn "=" [.var m, stateExpr L v], [events.size])
      events := events.push ⟨r, s!"{m} :=", txt v⟩
    | .deliver s m =>
      let (mv, src) ← match msgs.find? (·.1 == m) with
        | some (_, mv, i) => pure (mv, i)
        | none => throw s!"no message '{m}' has been sent (write {m} := replica first)"
      let w ← get states s
      let w' := merge w mv
      states := states.map fun (q, u) => if q == s then (q, w') else (q, u)
      steps := steps.push ("crdt.merge", s!"{s} merges the message {m}: the entrywise maximum, a join. Delivering it again, or after a newer state, changes nothing more.", stateExpr L w, stateExpr L w', [events.size])
      events := events.push ⟨s, s!"← {m}", txt w'⟩
      arrows := (src, events.size - 1) :: arrows
  return ⟨L, steps, states, ⟨replicas, events, arrows.reverse⟩⟩

/-- Parse a `replicas(…)` body: the type, the replicas, then the events. -/
def parse (body : String) : Except String (Kind × List String × List Ev) := do
  match Sys.clauses body with
  | ty :: rs :: evs =>
    let kind ← match Kind.ofName ty with
      | some k => pure k
      | none => throw s!"'{ty}' is not a CRDT here: gcounter, pncounter, gset, twopset, orset or lww"
    let replicas := (rs.splitOn ",").map (·.trimAscii.copy) |>.filter (· != "")
    if replicas.isEmpty || !replicas.all isName then throw "name the replicas after the type: replicas(gcounter; a, b; …)"
    if replicas.eraseDups.length != replicas.length then throw "a replica is named twice"
    let evs ← evs.mapM parseEv
    pure (kind, replicas, evs)
  | _ => throw "write replicas(type; a, b, …; events…)"

/-- The run as the cell answers it: each replica's reading, and whether they converged. -/
def summary (r : Run) : Expr × Bool :=
  let value := Expr.fn "set" (r.states.map fun (q, v) => .fn "↦" [.var q, read r.layout v])
  let same := match r.states with
    | [] => true
    | (_, v) :: rest => rest.all (·.2 == v)
  (value, same)

end Rep
end MathEngine
