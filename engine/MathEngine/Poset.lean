import MathEngine.Print
import Std.Data.HashSet
import Std.Data.HashMap
/-!
# The order-theory world: finite posets

A third little language in the engine: finite partial orders given by their elements and a
relation, with the vocabulary of the order-theory book — Hasse diagrams (covers), upper and lower
bounds, join and meet, lattices, top and bottom, monotone maps given as tables, and least and
greatest fixed points of monotone maps computed by iterating from ⊥ and ⊤ (the Kleene chain, which
is the derivation shown). Everything is a decision over lists, and `PosetProofs.lean` proves the
decisions right: the partial-order check, the covers, join as the least upper bound, and that the
iteration from ⊥ stops at the least fixed point.

Values are encoded into `Expr` for the wire (`fn "set" [...]`, elements as `var`/`num`), so the
notebook's machinery applies; the notebook draws the Hasse diagram from the covers.

A command's arguments are names, elements, sets, tables and relation lists. A command call may stand
for a name, `product(chain(2), chain(3))`: `Nested.lean` evaluates it first and puts a name in its
place, before this parser sees the cell.
-/
namespace MathEngine
namespace Ord

/-- A finite poset: its elements (each once) and its order as a list of pairs, reflexive and
transitively closed by construction (`mk`). -/
structure Poset where
  elems : List String
  le : List (String × String)
  /-- `le` as a hash set, built once. `covers` over every triple of a 128-element powerset makes
  millions of lookups, and a list scan of the 2187-pair order per lookup made `subsets` of seven
  elements take minutes; `leSet_eq` keeps the proofs on the list. -/
  leSet : Std.HashSet (String × String)
  leSet_eq : leSet = Std.HashSet.ofList le

/-- The one way to build a poset: the set is computed from the list. -/
def Poset.of (elems : List String) (le : List (String × String)) : Poset :=
  ⟨elems, le, Std.HashSet.ofList le, rfl⟩

instance : Inhabited Poset := ⟨Poset.of [] []⟩

def Poset.rel (P : Poset) (x y : String) : Bool := P.leSet.contains (x, y)

/-- `rel` decides membership in `le`: what the proofs use. -/
theorem Poset.rel_eq (P : Poset) (x y : String) : P.rel x y = P.le.contains (x, y) := by
  rw [Poset.rel, P.leSet_eq, Std.HashSet.contains_ofList]
def Poset.lt (P : Poset) (x y : String) : Bool := P.rel x y && x != y

/-- Reflexive-transitive closure of `gen` over `elems` (a fixed number of rounds suffices). -/
def closure (elems : List String) (gen : List (String × String)) : List (String × String) :=
  let refl := elems.map fun x => (x, x)
  let start := (refl ++ gen).eraseDups
  go elems.length start
where
  go : Nat → List (String × String) → List (String × String)
    | 0, r => r
    | n + 1, r =>
      let r' := (r ++ r.flatMap fun (a, b) => r.filterMap fun (c, d) => if b == c then some (a, d) else none).eraseDups
      if r'.length == r.length then r else go n r'

/-- Reflexive, antisymmetric, transitive over `elems`; the witness of a failure otherwise. -/
def checkPartialOrder (P : Poset) : Option String :=
  if let some x := P.elems.find? (fun x => !P.rel x x) then some s!"not reflexive: {x} ≤ {x} fails" else
  if let some (x, y) := P.le.find? (fun (x, y) => x != y && P.rel y x) then some s!"not antisymmetric: {x} ≤ {y} and {y} ≤ {x} with {x} ≠ {y}" else
  if let some ((x, y), (_, z)) := (P.le.flatMap fun p => P.le.map fun q => (p, q)).find? (fun ((x, y), (y', z)) => y == y' && !P.rel x z)
    then some s!"not transitive: {x} ≤ {y} ≤ {z} but not {x} ≤ {z}" else
  none

/-- Build a poset from a generating relation, or report why it is not a partial order. -/
def mk (elems : List String) (gen : List (String × String)) : Except String Poset :=
  let elems := elems.eraseDups
  if let some (x, y) := gen.find? (fun (x, y) => !elems.contains x || !elems.contains y) then
    .error s!"{x} < {y} mentions an element outside the set"
  else
    let P : Poset := Poset.of elems (closure elems gen)
    match checkPartialOrder P with
    | some why => .error s!"not a partial order: {why}"
    | none => .ok P

/-- `x ⋖ y`: `x < y` with nothing strictly between — the edges of the Hasse diagram. -/
def covers (P : Poset) (x y : String) : Bool :=
  P.lt x y && !P.elems.any fun z => P.lt x z && P.lt z y

def hasse (P : Poset) : List (String × String) :=
  P.elems.flatMap fun x => P.elems.filterMap fun y => if covers P x y then some (x, y) else none

/-- The height of every element — the length of the longest chain below it, for the drawing's
layers — by relaxing along the covers `|elems|` times: the longest chain has fewer edges than that.
(The recursive definition, longest chain below each element below, walked every chain of the
powerset of seven elements: 47 000 of them under the top alone.) -/
def heights (P : Poset) : Std.HashMap String Nat :=
  let cov := hasse P
  let init : Std.HashMap String Nat := P.elems.foldl (fun m x => m.insert x 0) {}
  (List.range P.elems.length).foldl (fun m _ =>
    cov.foldl (fun m (a, b) => let h := m.getD a 0 + 1; if h > m.getD b 0 then m.insert b h else m) m) init

def upperBounds (P : Poset) (xs : List String) : List String :=
  P.elems.filter fun u => xs.all fun x => P.rel x u
def lowerBounds (P : Poset) (xs : List String) : List String :=
  P.elems.filter fun l => xs.all fun x => P.rel l x

/-- The least upper bound of `xs`, if there is one. -/
def sup (P : Poset) (xs : List String) : Option String :=
  let ubs := upperBounds P xs
  ubs.find? fun u => ubs.all fun v => P.rel u v
def inf (P : Poset) (xs : List String) : Option String :=
  let lbs := lowerBounds P xs
  lbs.find? fun l => lbs.all fun m => P.rel m l

def top (P : Poset) : Option String := P.elems.find? fun t => P.elems.all fun x => P.rel x t
def bottom (P : Poset) : Option String := P.elems.find? fun b => P.elems.all fun x => P.rel b x

/-- A pair without a join or without a meet, if any: the witness that this is not a lattice. -/
def latticeFailure (P : Poset) : Option (String × String × String) :=
  (P.elems.flatMap fun x => P.elems.map fun y => (x, y)).findSome? fun (x, y) =>
    if (sup P [x, y]).isNone then some (x, y, "join") else if (inf P [x, y]).isNone then some (x, y, "meet") else none

/-- Maximal and minimal elements. -/
def maximal (P : Poset) : List String := P.elems.filter fun x => !P.elems.any fun y => P.lt x y
def minimal (P : Poset) : List String := P.elems.filter fun x => !P.elems.any fun y => P.lt y x

/-- The divisors of `n` under divisibility. -/
def divisors (n : Nat) : Except String Poset :=
  if n = 0 then .error "divisors(0) is not finite" else
  let ds := (List.range (n + 1)).filter fun d => d > 0 && n % d == 0
  let elems := ds.map toString
  .ok (Poset.of elems (ds.flatMap fun a => ds.filterMap fun b => if b % a == 0 then some (toString a, toString b) else none))

/-- All subsets of a finite set under inclusion, written `{a,b}`. -/
def subsets (xs : List String) : Poset :=
  let xs := xs.eraseDups
  let pw := xs.foldr (fun x acc => acc ++ acc.map (x :: ·)) [[]]
  let name (s : List String) : String := "{" ++ ",".intercalate (xs.filter (s.contains ·)) ++ "}"
  Poset.of (pw.map name) (pw.flatMap fun a => pw.filterMap fun b => if a.all (b.contains ·) then some (name a, name b) else none)

/-- The chain `0 < 1 < … < n-1`. -/
def chain (n : Nat) : Poset :=
  let es := (List.range n).map toString
  Poset.of es ((List.range n).flatMap fun a => (List.range n).filterMap fun b => if a ≤ b then some (toString a, toString b) else none)

/-! ## Maps -/

/-- A map on a poset, as a table. -/
structure PMap where
  table : List (String × String)
  deriving Repr, Inhabited

def PMap.apply (f : PMap) (x : String) : String := (f.table.lookup x).getD x

/-- A pair `x ≤ y` with `f x ≰ f y`, if any. -/
def monotoneFailure (P : Poset) (f : PMap) : Option (String × String) :=
  P.le.find? fun (x, y) => !P.rel (f.apply x) (f.apply y)

/-- Iterate `f` from `start` until it stops changing (at most `|P|` steps are needed on a finite
chain); the chain itself is returned. -/
def iterate (P : Poset) (f : PMap) (start : String) : List String := go P.elems.length start [start]
where
  go : Nat → String → List String → List String
    | 0, _, acc => acc.reverse
    | n + 1, x, acc =>
      let y := f.apply x
      if y == x then acc.reverse else go n y (y :: acc)

def fixedPoints (P : Poset) (f : PMap) : List String := P.elems.filter fun x => f.apply x == x

/-! ## Encoding for the wire -/

/-- Split at the commas not inside brackets or braces. -/
def splitTop (s : String) : List String :=
  let rec go : List Char → Nat → List Char → List String → List String
    | [], _, cur, acc => (String.ofList cur.reverse :: acc).reverse
    | c :: cs, d, cur, acc =>
      if c == ',' && d == 0 then go cs d [] (String.ofList cur.reverse :: acc)
      else if c == '(' || c == '{' then go cs (d + 1) (c :: cur) acc
      else if c == ')' || c == '}' then go cs (d - 1) (c :: cur) acc
      else go cs d (c :: cur) acc
  go s.toList 0 [] []

/-- An element as a value: a number, a pair `(x, y)` (a product's elements), or a name. -/
partial def elemExpr (x : String) : Expr :=
  if x.startsWith "(" && x.endsWith ")" then
    match splitTop ((x.drop 1).dropEnd 1).copy with
    | [a, b] => .fn "pair" [elemExpr a.trimAscii.copy, elemExpr b.trimAscii.copy]
    | _ => .var x
  else match x.toNat? with | some n => .num (Q.ofInt n) | none => .var x
def setExpr (xs : List String) : Expr := .fn "set" (xs.map elemExpr)
def posetExpr (P : Poset) : Expr := .fn "poset" [setExpr P.elems, .fn "hasse" (hasse P |>.map fun (a, b) => .fn "covers" [elemExpr a, elemExpr b])]

end Ord
end MathEngine

/-! ## Statements: the order-world's own little parser -/

namespace MathEngine
namespace Ord

inductive Tok where
  | ident (s : String) | lp | rp | lb | rb | lsq | rsq | comma | semi | lt | arrow | eq | eof
  deriving Repr, BEq, Inhabited

partial def lex (src : String) : Except String (List Tok) := go src.toList []
where
  go : List Char → List Tok → Except String (List Tok)
    | [], acc => .ok (acc.reverse ++ [.eof])
    | c :: cs, acc =>
      if c.isWhitespace then go cs acc
      else if c == '(' then go cs (.lp :: acc) else if c == ')' then go cs (.rp :: acc)
      else if c == '{' then go cs (.lb :: acc) else if c == '}' then go cs (.rb :: acc)
      else if c == '[' then go cs (.lsq :: acc) else if c == ']' then go cs (.rsq :: acc)
      else if c == ',' then go cs (.comma :: acc) else if c == ';' then go cs (.semi :: acc)
      else if c == '<' || c == '≤' then go cs (.lt :: acc)
      else if c == '=' then go cs (.eq :: acc)
      else if c == '↦' || c == '→' then go cs (.arrow :: acc)
      else if c == '-' then match cs with | '>' :: r => go r (.arrow :: acc) | _ => .error "expected '->'"
      else if c.isAlphanum || c == '_' then
        let ds := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_' || d == '\''
        go ((c :: cs).drop ds.length) (.ident (String.ofList ds) :: acc)
      else .error s!"unexpected character '{c}' in an order-world cell"

/-- One argument of an order command. -/
inductive Arg where
  | elem (x : String)
  | set (xs : List String)
  | rels (ps : List (String × String))      -- a<b, c<d
  | maps (ps : List (String × String))      -- a->b, c->d
  | table (rows : List (List String))       -- [a, b; b, b]: an operation's table, row by row
  deriving Repr, Inhabited

/-- `head(arg; arg, …)`: arguments separated by commas, relation lists by `;` or commas after the
first `<`/`->`. An element is a name, a pair `(x, y)` (a product's), or a set `{a, b}` (a powerset's).
Returns the head, the arguments, and the tokens left. -/
partial def parseCall : List Tok → Except String (String × List Arg × List Tok)
  | .ident head :: .lp :: ts => do
    let (args, ts) ← args ts []
    pure (head, args, ts)
  | _ => throw "expected a command: name(…)"
where
  element : List Tok → Except String (String × List Tok)
    | .ident x :: ts => pure (x, ts)
    | .lp :: ts => do
      let (a, ts) ← element ts
      match ts with
      | .comma :: ts =>
        let (b, ts) ← element ts
        match ts with
        | .rp :: ts => pure (s!"({a}, {b})", ts)
        | _ => throw "expected ')' to close a pair (x, y)"
      | _ => throw "expected ',' in a pair (x, y)"
    | .lb :: ts => do
      let (xs, ts) ← setBody ts []
      pure ("{" ++ ",".intercalate xs ++ "}", ts)
    | _ => throw "expected an element or a set"
  setBody : List Tok → List String → Except String (List String × List Tok)
    | .rb :: ts, acc => pure (acc.reverse, ts)
    | ts, acc => do
      let (x, ts) ← element ts
      match ts with
      | .comma :: ts => setBody ts (x :: acc)
      | .rb :: ts => pure ((x :: acc).reverse, ts)
      | _ => throw "expected '}' or ',' in a set"
  rows : List Tok → List String → List (List String) → Except String (List (List String) × List Tok)
    | .rsq :: ts, [], acc => pure (acc.reverse, ts)
    | ts, cur, acc => do
      let (x, ts) ← element ts
      match ts with
      | .comma :: ts => rows ts (x :: cur) acc
      | .semi :: ts => rows ts [] ((x :: cur).reverse :: acc)
      | .rsq :: ts => pure (((x :: cur).reverse :: acc).reverse, ts)
      | _ => throw "expected ',', ';' or ']' in a table"
  argument : List Tok → Except String (Arg × List Tok)
    | .lb :: ts => do
      let (xs, ts) ← setBody ts []
      pure (.set xs, ts)
    | .lsq :: ts => do
      let (rs, ts) ← rows ts [] []
      pure (.table rs, ts)
    | ts => do
      let (x, ts) ← element ts
      pure (.elem x, ts)
  args : List Tok → List Arg → Except String (List Arg × List Tok)
    | .rp :: ts, acc => pure (acc.reverse, ts)
    | ts, acc => do
      let (a, ts) ← argument ts
      let x := match a with | .elem x => x | .set xs => "{" ++ ",".intercalate xs ++ "}" | _ => ""
      match ts with
      | .lt :: ts =>
        let (y, ts) ← element ts
        let (ps, ts) ← pairs .lt ts [(x, y)]
        args ts (.rels ps :: acc)
      | .arrow :: ts =>
        let (y, ts) ← element ts
        let (ps, ts) ← pairs .arrow ts [(x, y)]
        args ts (.maps ps :: acc)
      | .comma :: ts | .semi :: ts => args ts (a :: acc)
      | .rp :: ts => pure ((a :: acc).reverse, ts)
      | _ => throw "expected ',' or ')' after an argument"
  /-- More pairs `x sep y` after the first, until the list ends (at `)`, or at a separator followed
  by something that is not a pair). -/
  pairs (sep : Tok) : List Tok → List (String × String) → Except String (List (String × String) × List Tok)
    | .rp :: ts, acc => pure (acc.reverse, .rp :: ts)
    | d :: ts, acc =>
      if d == .comma || d == .semi then
        match element ts with
        | .ok (x, t :: rest) =>
          if t == sep then do
            let (y, rest) ← element rest
            pairs sep rest ((x, y) :: acc)
          else if t == .lt || t == .arrow then throw "mixed relation list"
          else pure (acc.reverse, d :: ts)
        | _ => pure (acc.reverse, d :: ts)
      else throw "expected the next pair, ',' or ')'"
    | [], _ => throw "expected ')'"

/-- `[let name =] head(args)`. -/
def parseStmt (src : String) : Except String (Option String × String × List Arg) := do
  let toks ← lex src
  match toks with
  | .ident "let" :: .ident n :: .eq :: ts => do
    let (h, as, rest) ← parseCall ts
    if rest != [.eof] then throw "unexpected input after the command"
    pure (some n, h, as)
  | ts => do
    let (h, as, rest) ← parseCall ts
    if rest != [.eof] then throw "unexpected input after the command"
    pure (none, h, as)

def commands : List String :=
  ["poset", "divisors", "subsets", "chain", "map", "hasse", "join", "meet", "sup", "inf", "upper", "lower",
   "lattice", "top", "bottom", "le", "maximal", "minimal", "monotone", "lfp", "gfp", "fixpoints",
   -- relations (Relation.lean)
   "rel", "kernel", "reflexive", "symmetric", "antisymmetric", "transitive", "equivalence", "preorder",
   "closure", "classes", "finer", "wellfounded", "measure",
   -- finite algebra (Algebra.lean)
   "op", "joinop", "meetop", "table", "associative", "commutative", "idempotent", "semilattice", "identity", "fold", "order",
   "distributive", "complement", "complemented", "boolean", "product", "galois", "closureop", "context", "concepts", "secure",
   -- happens-before
   "events", "clocks", "concurrent"]

/-- Is this an order-world cell? Its command (after an optional `let name =`) is one of ours. -/
def isOrderSource (src : String) : Bool :=
  match lex src with
  | .ok (.ident "let" :: .ident _ :: .eq :: .ident h :: .lp :: _) => commands.contains h
  | .ok (.ident h :: .lp :: _) => commands.contains h
  | _ => false

end Ord
end MathEngine
