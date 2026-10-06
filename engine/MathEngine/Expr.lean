import MathEngine.Q
/-!
# Expression syntax

Node for node the same tree as the protocol's `WireExpr` (`Wire.lean` serializes to it). No subtraction/division/negation constructors — fewer cases in every proof:
`a - b` is `add [a, mul [-1, b]]`, `a / b` is `mul [a, pow b (-1)]`, `-a` is `mul [-1, a]`.
The printer recovers the human notation.
-/
namespace MathEngine

inductive Expr where
  | num    : Q → Expr
  | var    : String → Expr
  | add    : List Expr → Expr
  | mul    : List Expr → Expr
  | pow    : Expr → Expr → Expr
  | fn     : String → List Expr → Expr
  | matrix : List (List Expr) → Expr
  deriving Repr, Inhabited

/-- A path from the root to a subterm: child indices. `[]` is the root. -/
abbrev Path := List Nat

namespace Expr

def zero : Expr := .num Q.zero
def one : Expr := .num Q.one
def minusOne : Expr := .num Q.minusOne
def ofInt (n : Int) : Expr := .num (Q.ofInt n)
def neg (a : Expr) : Expr := .mul [minusOne, a]
def sub (a b : Expr) : Expr := .add [a, neg b]
def div (a b : Expr) : Expr := .mul [a, .pow b minusOne]
/-- `add` with the reference's convention: a one-element sum is that element. -/
def addN : List Expr → Expr | [e] => e | es => .add es
def mulN : List Expr → Expr | [e] => e | es => .mul es

def isNum : Expr → Bool | .num _ => true | _ => false
def isNumEq (e : Expr) (q : Q) : Bool := match e with | .num v => v.eq q | _ => false
def isZero (e : Expr) : Bool := match e with | .num v => v.isZero | _ => false
def isOne (e : Expr) : Bool := match e with | .num v => v.isOne | _ => false
def isMatrix : Expr → Bool | .matrix _ => true | _ => false

/-- Children in path order. A matrix's children are its entries, row-major. -/
def children : Expr → List Expr
  | .num _ | .var _ => []
  | .add es | .mul es | .fn _ es => es
  | .pow b e => [b, e]
  | .matrix rows => rows.flatten

/-- Cut `cs` into rows of the same lengths as `rows` (the inverse of `List.flatten` for that shape). -/
def regroup : List (List Expr) → List Expr → List (List Expr)
  | [], _ => []
  | r :: rs, cs => cs.take r.length :: regroup rs (cs.drop r.length)

theorem flatten_regroup (rows : List (List Expr)) (cs : List Expr) (h : cs.length = rows.flatten.length) :
    (regroup rows cs).flatten = cs := by
  induction rows generalizing cs with
  | nil => simp at h; simp [regroup, h]
  | cons r rs ih =>
    simp only [List.flatten_cons, List.length_append] at h
    simp only [regroup, List.flatten_cons]
    rw [ih (cs.drop r.length) (by rw [List.length_drop]; omega), List.take_append_drop]

/-- Rebuild a node around new children (same count and order as `children`). -/
def withChildren (e : Expr) (cs : List Expr) : Expr :=
  match e with
  | .num _ | .var _ => e
  | .add _ => .add cs
  | .mul _ => .mul cs
  | .fn f _ => .fn f cs
  | .pow _ _ => match cs with | [b, x] => .pow b x | _ => e
  | .matrix rows => .matrix (regroup rows cs)

theorem children_withChildren (e : Expr) (cs : List Expr) (h : cs.length = (children e).length) :
    children (withChildren e cs) = cs := by
  cases e with
  | pow b x =>
    simp only [children, List.length_cons, List.length_nil] at h
    match cs, h with
    | [b', x'], _ => rfl
  | matrix rows => simp only [withChildren, children] at h ⊢; exact flatten_regroup rows cs h
  | _ => simp_all [withChildren, children]

def at? (e : Expr) : Path → Option Expr
  | [] => some e
  | i :: rest => do let c ← (children e)[i]?; c.at? rest

mutual
  /-- Number of nodes. -/
  def size : Expr → Nat
    | .num _ | .var _ => 1
    | .add es | .mul es | .fn _ es => 1 + sizeList es
    | .pow b e => 1 + b.size + e.size
    | .matrix rows => 1 + sizeRows rows
  def sizeList : List Expr → Nat
    | [] => 0
    | e :: es => e.size + sizeList es
  def sizeRows : List (List Expr) → Nat
    | [] => 0
    | r :: rs => sizeList r + sizeRows rs
end

theorem sizeList_append (l₁ l₂ : List Expr) : sizeList (l₁ ++ l₂) = sizeList l₁ + sizeList l₂ := by
  induction l₁ with
  | nil => simp [sizeList]
  | cons e es ih => simp [sizeList, ih]; omega

theorem sizeRows_flatten (rows : List (List Expr)) : sizeRows rows = sizeList rows.flatten := by
  induction rows with
  | nil => simp [sizeRows, sizeList]
  | cons r rs ih => simp [sizeRows, sizeList_append, ih]

theorem size_eq (e : Expr) : size e = 1 + sizeList (children e) := by
  cases e <;> simp [size, children, sizeList, sizeRows_flatten] <;> omega

theorem size_pos (e : Expr) : 0 < size e := by rw [size_eq]; omega
theorem sizeList_children_lt (e : Expr) : sizeList (children e) < size e := by rw [size_eq]; omega

theorem size_le_sizeList {a : Expr} : ∀ {l : List Expr}, a ∈ l → size a ≤ sizeList l
  | _ :: _, .head _ => by simp [sizeList]
  | _ :: _, .tail _ h => by have := size_le_sizeList h; simp [sizeList]; omega

theorem sizeList_le_sizeRows {r : List Expr} : ∀ {rows : List (List Expr)}, r ∈ rows → sizeList r ≤ sizeRows rows
  | _ :: _, .head _ => by simp [sizeRows]
  | _ :: _, .tail _ h => by have := sizeList_le_sizeRows h; simp [sizeRows]; omega

def freeVars : Expr → List String
  | .num _ => []
  | .var x => [x]
  | .add es | .mul es | .fn _ es => freeVarsList es
  | .pow b e => freeVars b ++ freeVars e
  | .matrix rows => freeVarsRows rows
where
  freeVarsList : List Expr → List String
    | [] => []
    | e :: es => freeVars e ++ freeVarsList es
  freeVarsRows : List (List Expr) → List String
    | [] => []
    | r :: rs => freeVarsList r ++ freeVarsRows rs

/-- `freeVars e ++ acc`, built from the right: a variable is consed onto what follows it, so a
product the parser left-nested fifty thousand deep (`x*x*…*x`) takes time linear in it, where
`freeVars` copies the list of the left operand at every level. `freeVars` stays the definition the
proofs use (`freeVarsAcc_eq`); the compiled code takes this one (`freeVars_eq_freeVarsImpl`). -/
def freeVarsAcc : Expr → List String → List String
  | .num _, acc => acc
  | .var x, acc => x :: acc
  | .add es, acc | .mul es, acc | .fn _ es, acc => freeVarsListAcc es acc
  | .pow b e, acc => freeVarsAcc b (freeVarsAcc e acc)
  | .matrix rows, acc => freeVarsRowsAcc rows acc
where
  freeVarsListAcc : List Expr → List String → List String
    | [], acc => acc
    | e :: es, acc => freeVarsAcc e (freeVarsListAcc es acc)
  freeVarsRowsAcc : List (List Expr) → List String → List String
    | [], acc => acc
    | r :: rs, acc => freeVarsListAcc r (freeVarsRowsAcc rs acc)

theorem freeVarsAcc_eq : ∀ (e : Expr) (acc : List String), freeVarsAcc e acc = freeVars e ++ acc
  | .num _, acc => by simp [freeVarsAcc, freeVars]
  | .var x, acc => by simp [freeVarsAcc, freeVars]
  | .add es, acc => by simp [freeVarsAcc, freeVars, freeVarsListAcc_eq es acc]
  | .mul es, acc => by simp [freeVarsAcc, freeVars, freeVarsListAcc_eq es acc]
  | .fn _ es, acc => by simp [freeVarsAcc, freeVars, freeVarsListAcc_eq es acc]
  | .pow b e, acc => by simp [freeVarsAcc, freeVars, freeVarsAcc_eq b, freeVarsAcc_eq e]
  | .matrix rows, acc => by simp [freeVarsAcc, freeVars, freeVarsRowsAcc_eq rows acc]
where
  freeVarsListAcc_eq : ∀ (es : List Expr) (acc : List String),
      freeVarsAcc.freeVarsListAcc es acc = freeVars.freeVarsList es ++ acc
    | [], acc => by simp [freeVarsAcc.freeVarsListAcc, freeVars.freeVarsList]
    | e :: es, acc => by
      simp [freeVarsAcc.freeVarsListAcc, freeVars.freeVarsList, freeVarsAcc_eq e, freeVarsListAcc_eq es acc]
  freeVarsRowsAcc_eq : ∀ (rows : List (List Expr)) (acc : List String),
      freeVarsAcc.freeVarsRowsAcc rows acc = freeVars.freeVarsRows rows ++ acc
    | [], acc => by simp [freeVarsAcc.freeVarsRowsAcc, freeVars.freeVarsRows]
    | r :: rs, acc => by
      simp [freeVarsAcc.freeVarsRowsAcc, freeVars.freeVarsRows, freeVarsListAcc_eq r, freeVarsRowsAcc_eq rs acc]

/-- `freeVars` as the compiled code computes it. -/
def freeVarsImpl (e : Expr) : List String := freeVarsAcc e []

@[csimp] theorem freeVars_eq_freeVarsImpl : @freeVars = @freeVarsImpl := by
  funext e; simp [freeVarsImpl, freeVarsAcc_eq]

def dependsOn (e : Expr) (x : String) : Bool := (freeVars e).contains x

/-- Numbers first, then variables, then compound terms — `KIND_RANK` in `ast.ts`. -/
def kindRank : Expr → Nat
  | .num _ => 0 | .fn _ [] => 1 | .var _ => 2 | .pow _ _ => 3 | .fn _ _ => 4 | .mul _ => 5 | .add _ => 6 | .matrix _ => 7

/-- A total order on expressions (the canonical argument order). -/
partial def compare (a b : Expr) : Ordering :=
  match Ord.compare (kindRank a) (kindRank b) with
  | .eq =>
    match a, b with
    | .num p, .num q => p.cmp q
    | .var x, .var y => Ord.compare x y
    | .pow b1 e1, .pow b2 e2 => (compare b1 b2).then (compare e1 e2)
    | .fn f xs, .fn g ys => (Ord.compare f g).then (compareList xs ys)
    | .add xs, .add ys | .mul xs, .mul ys => compareList xs ys
    | .matrix r1, .matrix r2 => compareList r1.flatten r2.flatten
    | _, _ => .eq
  | o => o
where
  compareList : List Expr → List Expr → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | x :: xs, y :: ys => (compare x y).then (compareList xs ys)

mutual
  /-- Structural equality. Written out (rather than derived) so that `beq_eq` can be proved. -/
  def beq : Expr → Expr → Bool
    | .num p, .num q => p == q
    | .var x, .var y => x == y
    | .add xs, .add ys => beqList xs ys
    | .mul xs, .mul ys => beqList xs ys
    | .pow a b, .pow c d => beq a c && beq b d
    | .fn f xs, .fn g ys => f == g && beqList xs ys
    | .matrix r, .matrix s => beqRows r s
    | _, _ => false
  def beqList : List Expr → List Expr → Bool
    | [], [] => true
    | x :: xs, y :: ys => beq x y && beqList xs ys
    | _, _ => false
  def beqRows : List (List Expr) → List (List Expr) → Bool
    | [], [] => true
    | r :: rs, s :: ss => beqList r s && beqRows rs ss
    | _, _ => false
end

/-- Elementwise lifting of a relation on expressions to argument lists. Used to say "these children
were each rewritten soundly", which is the induction hypothesis every congruence proof needs. -/
def RelList (R : Expr → Expr → Prop) : List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ RelList R as bs
  | _, _ => False

theorem RelList_length {R : Expr → Expr → Prop} : ∀ {as bs : List Expr}, RelList R as bs → as.length = bs.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, ⟨_, h⟩ => by simp [RelList_length h]

theorem RelList_refl {R : Expr → Expr → Prop} (h : ∀ e, R e e) : ∀ l : List Expr, RelList R l l
  | [] => trivial
  | e :: es => ⟨h e, RelList_refl h es⟩

mutual
  theorem beq_eq : ∀ a b : Expr, beq a b = true → a = b
    | .num p, b, h => by cases b <;> simp [beq] at h; rw [h]
    | .var x, b, h => by cases b <;> simp [beq] at h; rw [h]
    | .add xs, b, h => by cases b <;> simp [beq] at h; rw [beqList_eq xs _ h]
    | .mul xs, b, h => by cases b <;> simp [beq] at h; rw [beqList_eq xs _ h]
    | .pow a₁ a₂, b, h => by cases b <;> simp [beq] at h; rw [beq_eq a₁ _ h.1, beq_eq a₂ _ h.2]
    | .fn f xs, b, h => by cases b <;> simp [beq] at h; rw [h.1, beqList_eq xs _ h.2]
    | .matrix r, b, h => by cases b <;> simp [beq] at h; rw [beqRows_eq r _ h]
  theorem beqList_eq : ∀ xs ys : List Expr, beqList xs ys = true → xs = ys
    | [], ys, h => by cases ys <;> simp [beqList] at h; rfl
    | x :: xs, ys, h => by
      cases ys with
      | nil => simp [beqList] at h
      | cons y ys => simp [beqList] at h; rw [beq_eq x y h.1, beqList_eq xs ys h.2]
  theorem beqRows_eq : ∀ rs ss : List (List Expr), beqRows rs ss = true → rs = ss
    | [], ss, h => by cases ss <;> simp [beqRows] at h; rfl
    | r :: rs, ss, h => by
      cases ss with
      | nil => simp [beqRows] at h
      | cons s ss => simp [beqRows] at h; rw [beqList_eq r s h.1, beqRows_eq rs ss h.2]
end

mutual
  theorem beq_refl : ∀ a : Expr, beq a a = true
    | .num p => by simp [beq]
    | .var x => by simp [beq]
    | .add xs => by simp [beq, beqList_refl xs]
    | .mul xs => by simp [beq, beqList_refl xs]
    | .pow a b => by simp [beq, beq_refl a, beq_refl b]
    | .fn f xs => by simp [beq, beqList_refl xs]
    | .matrix r => by simp [beq, beqRows_refl r]
  theorem beqList_refl : ∀ xs : List Expr, beqList xs xs = true
    | [] => rfl
    | x :: xs => by simp [beqList, beq_refl x, beqList_refl xs]
  theorem beqRows_refl : ∀ rs : List (List Expr), beqRows rs rs = true
    | [] => rfl
    | r :: rs => by simp [beqRows, beqList_refl r, beqRows_refl rs]
end

/-! ### One and the same object compares equal in one step

The rewriter compares a node with its canonical form at every level (`normAtT`), and the two share
every child the rewriter did not rebuild. A structural walk cost such a comparison the size of the
subterm, so a term `d` deep paid for its size `d` times over. `beqR` asks `withPtrEq` first: one
and the same object compares equal at once, and only what differs is walked. `withPtrEq` wants
the reflexivity of what it shortcuts, so `beqR` carries that proof along. It is `beq` itself
(`beq_eq_beqImpl`), and the compiled code takes it in `beq`'s place. -/
mutual
  def beqR (a b : Expr) : {r : Bool // a = b → r = true} :=
    let node : Unit → {r : Bool // a = b → r = true} := fun _ =>
      match a with
      | .num p => match b with
        | .num q => ⟨p == q, fun h => by cases h; simp⟩
        | .var _ | .add _ | .mul _ | .pow _ _ | .fn _ _ | .matrix _ => ⟨false, nofun⟩
      | .var x => match b with
        | .var y => ⟨x == y, fun h => by cases h; simp⟩
        | .num _ | .add _ | .mul _ | .pow _ _ | .fn _ _ | .matrix _ => ⟨false, nofun⟩
      | .add xs => match b with
        | .add ys => let r := beqRList xs ys; ⟨r.1, fun h => r.2 (Expr.add.inj h)⟩
        | .num _ | .var _ | .mul _ | .pow _ _ | .fn _ _ | .matrix _ => ⟨false, nofun⟩
      | .mul xs => match b with
        | .mul ys => let r := beqRList xs ys; ⟨r.1, fun h => r.2 (Expr.mul.inj h)⟩
        | .num _ | .var _ | .add _ | .pow _ _ | .fn _ _ | .matrix _ => ⟨false, nofun⟩
      | .pow a₁ a₂ => match b with
        | .pow b₁ b₂ =>
          let r₁ := beqR a₁ b₁
          let r₂ := beqR a₂ b₂
          ⟨r₁.1 && r₂.1, fun h => by cases h; simp [r₁.2 rfl, r₂.2 rfl]⟩
        | .num _ | .var _ | .add _ | .mul _ | .fn _ _ | .matrix _ => ⟨false, nofun⟩
      | .fn f xs => match b with
        | .fn g ys => let r := beqRList xs ys; ⟨f == g && r.1, fun h => by cases h; simp [r.2 rfl]⟩
        | .num _ | .var _ | .add _ | .mul _ | .pow _ _ | .matrix _ => ⟨false, nofun⟩
      | .matrix rs => match b with
        | .matrix ss => let r := beqRRows rs ss; ⟨r.1, fun h => r.2 (Expr.matrix.inj h)⟩
        | .num _ | .var _ | .add _ | .mul _ | .pow _ _ | .fn _ _ => ⟨false, nofun⟩
    ⟨withPtrEq a b (fun u => (node u).1) (fun h => (node ()).2 h), fun h => (node ()).2 h⟩
  def beqRList (xs ys : List Expr) : {r : Bool // xs = ys → r = true} :=
    match xs, ys with
    | [], [] => ⟨true, fun _ => rfl⟩
    | x :: xs, y :: ys =>
      let r := beqR x y
      let rs := beqRList xs ys
      ⟨r.1 && rs.1, fun h => by cases h; simp [r.2 rfl, rs.2 rfl]⟩
    | [], _ :: _ | _ :: _, [] => ⟨false, nofun⟩
  def beqRRows (rs ss : List (List Expr)) : {r : Bool // rs = ss → r = true} :=
    match rs, ss with
    | [], [] => ⟨true, fun _ => rfl⟩
    | r :: rs, s :: ss =>
      let q := beqRList r s
      let qs := beqRRows rs ss
      ⟨q.1 && qs.1, fun h => by cases h; simp [q.2 rfl, qs.2 rfl]⟩
    | [], _ :: _ | _ :: _, [] => ⟨false, nofun⟩
end

mutual
  theorem beqR_eq : ∀ a b : Expr, (beqR a b).1 = true → a = b
    | .num p, b, h => by cases b <;> simp [beqR, withPtrEq] at h; rw [h]
    | .var x, b, h => by cases b <;> simp [beqR, withPtrEq] at h; rw [h]
    | .add xs, b, h => by cases b <;> simp [beqR, withPtrEq] at h; rw [beqRList_eq xs _ h]
    | .mul xs, b, h => by cases b <;> simp [beqR, withPtrEq] at h; rw [beqRList_eq xs _ h]
    | .pow a₁ a₂, b, h => by cases b <;> simp [beqR, withPtrEq] at h; rw [beqR_eq a₁ _ h.1, beqR_eq a₂ _ h.2]
    | .fn f xs, b, h => by cases b <;> simp [beqR, withPtrEq] at h; rw [h.1, beqRList_eq xs _ h.2]
    | .matrix r, b, h => by cases b <;> simp [beqR, withPtrEq] at h; rw [beqRRows_eq r _ h]
  theorem beqRList_eq : ∀ xs ys : List Expr, (beqRList xs ys).1 = true → xs = ys
    | [], ys, h => by cases ys <;> simp [beqRList] at h; rfl
    | x :: xs, ys, h => by
      cases ys with
      | nil => simp [beqRList] at h
      | cons y ys => simp [beqRList] at h; rw [beqR_eq x y h.1, beqRList_eq xs ys h.2]
  theorem beqRRows_eq : ∀ rs ss : List (List Expr), (beqRRows rs ss).1 = true → rs = ss
    | [], ss, h => by cases ss <;> simp [beqRRows] at h; rfl
    | r :: rs, ss, h => by
      cases ss with
      | nil => simp [beqRRows] at h
      | cons s ss => simp [beqRRows] at h; rw [beqRList_eq r s h.1, beqRRows_eq rs ss h.2]
end

/-- `beq` as the compiled code runs it. -/
def beqImpl (a b : Expr) : Bool := (beqR a b).1

@[csimp] theorem beq_eq_beqImpl : @beq = @beqImpl := by
  funext a b
  by_cases h : a = b
  · subst h; rw [beq_refl]; exact ((beqR a a).2 rfl).symm
  · have h1 : beq a b = false := by
      cases hb : beq a b with
      | true => exact absurd (beq_eq a b hb) h
      | false => rfl
    have h2 : beqImpl a b = false := by
      cases hb : beqImpl a b with
      | true => exact absurd (beqR_eq a b hb) h
      | false => rfl
    rw [h1, h2]

instance : BEq Expr := ⟨beq⟩
def equal (a b : Expr) : Bool := beq a b

theorem equal_eq {a b : Expr} (h : equal a b = true) : a = b := beq_eq a b h

/-- Remove the first element satisfying `p`. Unlike `List.erase` this needs no lawful `BEq`. -/
def removeFirst (p : Expr → Bool) : List Expr → List Expr
  | [] => []
  | a :: as => if p a then as else a :: removeFirst p as

theorem perm_find?_removeFirst (p : Expr → Bool) : ∀ (l : List Expr) (f : Expr),
    l.find? p = some f → l.Perm (f :: removeFirst p l)
  | [], f, h => by simp at h
  | a :: as, f, h => by
    by_cases hp : p a = true
    · simp [List.find?_cons_of_pos hp] at h; subst h; simp [removeFirst, hp]
    · rw [List.find?_cons_of_neg hp] at h
      simp only [removeFirst, hp, Bool.false_eq_true, ↓reduceIte]
      exact (List.Perm.cons a (perm_find?_removeFirst p as f h)).trans (List.Perm.swap f a _)

end Expr
end MathEngine
