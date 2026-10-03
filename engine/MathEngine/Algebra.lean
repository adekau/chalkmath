import MathEngine.Relation
/-!
# Finite algebra, in the order world

A lattice can be read two ways: as an order with joins and meets, or as a set with operations that
obey laws. This file is the second reading, on finite sets, and the bridges between the two.

- **Operation tables** (`Op`): a binary operation on a finite set, given by its table. Its laws are
  decided over every pair or triple, and a failure names the elements: associativity, commutativity,
  idempotence (together, a semilattice), an identity element. `fold` combines a list left to right.
- **From an operation to an order and back**: a semilattice orders its set by `x ≤ y ⇔ x · y = y`
  (`Op.order`), and a lattice's join and meet are operations (`joinOp`, `meetOp`).
  `AlgebraProofs.lean` proves that the order a semilattice induces is a partial order in which the
  operation is the join.
- **Lattice properties**: distributivity, with the triple that breaks it (M₃ and N₅ are the
  witnesses every non-distributive lattice contains), complements, Boolean lattices.
- **Building and comparing orders**: products (pairs ordered componentwise, elements written
  `(x, y)`); maps between two posets, monotone or not; Galois connections; closure operators.
- **Formal concept analysis**: a context (objects, attributes, which object has which) and its
  concepts, ordered by extent: always a complete lattice.
- **Information flow**: a labelling of variables by a lattice of security classes, and the flows
  that go down it (Denning).
-/
namespace MathEngine
namespace Ord

/-! ## Element names

Elements are strings. A product's elements are pairs `(x, y)`; a powerset's are sets `{a,b}`. What a
reader types may differ from the stored name in spacing and in the order of a set's members, so
names are compared by a canonical key. -/

/-- A name's canonical key: spaces dropped, a set's members sorted. -/
partial def elemKey (s : String) : String :=
  let t := (s.toList.filter (!·.isWhitespace))
  let t := String.ofList t
  if t.startsWith "{" && t.endsWith "}" then
    let inner := (t.drop 1).dropEnd 1 |>.copy
    let ms := if inner.isEmpty then [] else (splitTop inner).map elemKey
    "{" ++ ",".intercalate (ms.mergeSort (· ≤ ·)) ++ "}"
  else if t.startsWith "(" && t.endsWith ")" then
    let inner := (t.drop 1).dropEnd 1 |>.copy
    "(" ++ ",".intercalate ((splitTop inner).map elemKey) ++ ")"
  else t

/-- The stored element a typed name refers to. -/
def findElem (elems : List String) (typed : String) : Option String :=
  if elems.contains typed then some typed else
  let k := elemKey typed
  elems.find? (elemKey · == k)

def pairName (x y : String) : String := s!"({x}, {y})"
def setName (xs : List String) : String := "{" ++ ",".intercalate xs ++ "}"

/-! ## Operation tables -/

/-- A binary operation on a finite set, by its table: `((x, y), x · y)`. -/
structure Op where
  elems : List String
  table : List ((String × String) × String)
  deriving Inhabited

def Op.ap (o : Op) (x y : String) : String := (o.table.lookup (x, y)).getD x

/-- The table from its rows: row `i`, column `j` is `elems[i] · elems[j]`. -/
def Op.ofRows (elems : List String) (rows : List (List String)) : Except String Op := do
  if elems.eraseDups.length != elems.length then throw "the set lists an element twice"
  if rows.length != elems.length then
    throw s!"the table has {rows.length} row{if rows.length == 1 then "" else "s"}, and the set has {elems.length} elements"
  if let some (r, x) := (rows.zip elems).find? (fun (r, _) => r.length != elems.length) then
    throw s!"row {x} has {r.length} entr{if r.length == 1 then "y" else "ies"}, and it needs {elems.length}"
  let rows ← rows.mapM fun r => r.mapM fun v => match findElem elems v with
    | some e => pure e
    | none => throw s!"{v} in the table is not in the set"
  pure ⟨elems, (elems.zip rows).flatMap fun (x, r) => (elems.zip r).map fun (y, v) => ((x, y), v)⟩

def Op.rows (o : Op) : List (List String) := o.elems.map fun x => o.elems.map fun y => o.ap x y

def allPairs (xs : List String) : List (String × String) := xs.flatMap fun x => xs.map (x, ·)
def allTriples (xs : List String) : List (String × String × String) :=
  xs.flatMap fun x => xs.flatMap fun y => xs.map fun z => (x, y, z)

/-- `(x · y) · z ≠ x · (y · z)`, if anywhere. -/
def assocFailure (o : Op) : Option (String × String × String) :=
  (allTriples o.elems).find? fun (x, y, z) => o.ap (o.ap x y) z != o.ap x (o.ap y z)
/-- `x · y ≠ y · x`, if anywhere. -/
def commFailure (o : Op) : Option (String × String) :=
  (allPairs o.elems).find? fun (x, y) => o.ap x y != o.ap y x
/-- `x · x ≠ x`, if anywhere. -/
def idemFailure (o : Op) : Option String := o.elems.find? fun x => o.ap x x != x
/-- An element `e` with `e · x = x = x · e` for every `x`. -/
def Op.identity (o : Op) : Option String := o.elems.find? fun e => o.elems.all fun x => o.ap e x == x && o.ap x e == x

/-- The order a semilattice induces: `x ≤ y` when `x · y = y` (the operation is the join). -/
def Op.order (o : Op) : Poset := Poset.of o.elems ((allPairs o.elems).filter fun (x, y) => o.ap x y == y)

/-- A lattice's join as an operation, if every pair has one. -/
def joinOp (P : Poset) : Option Op :=
  ((allPairs P.elems).mapM fun (x, y) => (sup P [x, y]).map ((x, y), ·)).map (⟨P.elems, ·⟩)
def meetOp (P : Poset) : Option Op :=
  ((allPairs P.elems).mapM fun (x, y) => (inf P [x, y]).map ((x, y), ·)).map (⟨P.elems, ·⟩)

/-! ## Lattice properties -/

/-- `x ∧ (y ∨ z) ≠ (x ∧ y) ∨ (x ∧ z)`, if anywhere (`J` the join, `M` the meet). -/
def distribFailure (J M : Op) : Option (String × String × String) :=
  (allTriples J.elems).find? fun (x, y, z) => M.ap x (J.ap y z) != J.ap (M.ap x y) (M.ap x z)

/-- The complements of `x`: the `y` with `x ∨ y = ⊤` and `x ∧ y = ⊥`. -/
def complementsOf (J M : Op) (top bot x : String) : List String :=
  J.elems.filter fun y => J.ap x y == top && M.ap x y == bot

/-! ## Products, maps, Galois connections, closure operators -/

/-- The product order: pairs, `(a, c) ≤ (b, d)` when `a ≤ b` and `c ≤ d`. -/
def product (P Q : Poset) : Poset :=
  Poset.of (P.elems.flatMap fun x => Q.elems.map (pairName x ·))
    (P.le.flatMap fun (a, b) => Q.le.map fun (c, d) => (pairName a c, pairName b d))

/-- A pair `x ≤ y` of `P` with `f x ≰ f y` in `Q`, if any. -/
def monotoneFailure2 (P Q : Poset) (f : PMap) : Option (String × String) :=
  P.le.find? fun (x, y) => !Q.rel (f.apply x) (f.apply y)

/-- `f : P → Q` and `g : Q → P` form a Galois connection when `f x ≤ y ⇔ x ≤ g y`; a pair where the
two sides disagree, if any. -/
def galoisFailure (P Q : Poset) (f g : PMap) : Option (String × String) :=
  (P.elems.flatMap fun x => Q.elems.map (x, ·)).find? fun (x, y) => Q.rel (f.apply x) y != P.rel x (g.apply y)

/-- Why `f` is not a closure operator on `P`: not extensive (`x ≰ f x`), not monotone, or not
idempotent (`f (f x) ≠ f x`), with the elements. -/
def closureOpFailure (P : Poset) (f : PMap) : Option (String × String × String) :=
  match P.elems.find? fun x => !P.rel x (f.apply x) with
  | some x => some ("extensive", x, x)
  | none => match monotoneFailure P f with
    | some (x, y) => some ("monotone", x, y)
    | none => (P.elems.find? fun x => f.apply (f.apply x) != f.apply x).map fun x => ("idempotent", x, x)

/-! ## Formal concept analysis -/

/-- A formal context: objects, attributes, and which object has which attribute. -/
structure Ctx where
  objs : List String
  attrs : List String
  inc : List (String × String)
  deriving Inhabited

def Ctx.has (C : Ctx) (o a : String) : Bool := C.inc.contains (o, a)
/-- The objects having every attribute in `as`. -/
def Ctx.extentOf (C : Ctx) (as : List String) : List String := C.objs.filter fun o => as.all (C.has o ·)
/-- The attributes every object in `os` has. -/
def Ctx.intentOf (C : Ctx) (os : List String) : List String := C.attrs.filter fun a => os.all (C.has · a)

/-- Every concept's extent: the intersections of attribute extents (all objects for none). -/
def Ctx.extents (C : Ctx) : List (List String) :=
  C.attrs.foldl (fun acc a =>
    let e := C.extentOf [a]
    acc ++ ((acc.map (·.filter (e.contains ·))).filter (fun x => !acc.contains x)).eraseDups) [C.objs]

/-- The concepts `(extent, intent)`, ordered by inclusion of extents: the concept lattice. -/
def Ctx.concepts (C : Ctx) : List (List String × List String) :=
  C.extents.map fun e => (e, C.intentOf e)

def conceptName (c : List String × List String) : String := pairName (setName c.1) (setName c.2)

def Ctx.lattice (C : Ctx) : Poset :=
  let cs := C.concepts
  Poset.of (cs.map conceptName)
    (cs.flatMap fun a => cs.filterMap fun b => if a.1.all (b.1.contains ·) then some (conceptName a, conceptName b) else none)

/-! ## Information flow -/

/-- A flow `x → y` (of the relation `R`) from a higher class to a lower one, if any: `λ x ≰ λ y`. -/
def flowFailure (P : Poset) (label : String → String) (R : Rel) : Option (String × String) :=
  R.pairs.find? fun (x, y) => !P.rel (label x) (label y)

/-! ## Encoding for the wire -/

/-- An operation as its table, a matrix of elements. -/
def opExpr (o : Op) : Expr := .matrix (o.rows.map (·.map elemExpr))

end Ord
end MathEngine
