-- From adekau/lean4learning (crdt/Crdt.lean, the companion to "From Propagators to Replicas"),
-- ported from Lean 4.28 to the notebook's 4.34: two Decidable instances in Chapter 10 are built
-- explicitly (4.34's instance search no longer finds them through the book's TotalOrder instances),
-- and the deprecation and class-reducibility notices 4.34 raises on 4.28 code are switched off.
-- scripts/notebooks/mk-courses.mjs splits it into the lessons of the CRDT course.
set_option linter.deprecated false
set_option warn.classDefReducibility false

/- ============================================================
   Crdt.lean
   Companion to "From Propagators to Replicas:
   Conflict-Free Replicated Data Types in Lean 4"
   (sequel to "From Zero to Propagators")

   Series rules: zero dependencies beyond the prelude,
   zero `sorry`, compiles with a bare `lean Crdt.lean`
   (toolchain leanprover/lean4:v4.28.0).

   Namespaces follow the book's chapters:
     Crdt.Order      — Ch 2   the merge discipline
     Crdt.Intro      — Ch 1   divergence demos
     Crdt.GCounter   — Ch 3   grow-only counter
     Crdt.PNCounter  — Ch 4   increment/decrement counter
     Crdt.SList      — Ch 5   sorted duplicate-free lists
     Crdt.GSet/TwoPSet — Ch 5 grow-only and two-phase sets
     Crdt.LWW        — Ch 6   last-writer-wins registers
     Crdt.ORSet      — Ch 7   observed-remove set, addWins
     Crdt.Perm/MSet  — Ch 8   permutations, quotients, multisets
     Crdt.SEC        — Ch 8   strong eventual consistency
     Crdt.Delivery   — Ch 9   trace semantics, gossip driver
     Crdt.VV         — Ch 10  version vectors
     Crdt.OpBased    — Ch 11  operation-based CRDTs
     Crdt.Capstone   — Ch 12  a replicated shopping list
     Crdt.Limits     — Ch 13  what CRDTs cannot do
     Crdt.Solutions  — App B  compiled exercise solutions
   ============================================================ -/

namespace Crdt

/- ============================================================
   Crdt.Order — Chapter 2: The Merge Discipline
   The same classes as the predecessor book, re-derived, not
   imported: a bounded join-semilattice is the discipline every
   replica obeys.
   ============================================================ -/

namespace Order

/-- A partial order: reflexive, antisymmetric, transitive.
    (Identical to the predecessor's class, so muscle memory transfers.) -/
class PartialOrder (α : Type) [LE α] where
  le_refl               : ∀ (a : α), a ≤ a
  le_antisymm {a b : α} : a ≤ b → b ≤ a → a = b
  le_trans {a b c : α}  : a ≤ b → b ≤ c → a ≤ c

/-- A bounded join-semilattice: every pair has a least upper bound `sup`,
    and there is a least element `bot`. The state space of every
    state-based CRDT in this book is one of these. -/
class BoundedJoinSemilattice (α : Type) extends LE α, PartialOrder α where
  sup : α → α → α
  bot : α
  le_sup_left   : ∀ (a b : α), a ≤ sup a b
  le_sup_right  : ∀ (a b : α), b ≤ sup a b
  sup_le        : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c
  bot_le        : ∀ (a : α), bot ≤ a

end Order

open Order

infixl:65 " ⊔ " => Order.BoundedJoinSemilattice.sup
notation  "⊥"   => Order.BoundedJoinSemilattice.bot
/-- The information order. `a ⊑ b` is notation for `a ≤ b`, read
    "b knows at least as much as a". -/
infix:50  " ⊑ "  => LE.le

namespace Order

open PartialOrder BoundedJoinSemilattice

variable {α : Type} [BoundedJoinSemilattice α]

/- ── The ACI toolkit ─────────────────────────────────────────
   Commutativity, associativity, idempotence: one law per
   network sin (reordering, batching, duplication).           -/

theorem sup_comm (a b : α) : a ⊔ b = b ⊔ a := by
  apply le_antisymm
  · exact sup_le a b (b ⊔ a) (le_sup_right b a) (le_sup_left b a)
  · exact sup_le b a (a ⊔ b) (le_sup_right a b) (le_sup_left a b)

theorem sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · exact le_sup_left a (b ⊔ c)
      · exact le_trans (le_sup_left b c) (le_sup_right a (b ⊔ c))
    · exact le_trans (le_sup_right b c) (le_sup_right a (b ⊔ c))
  · apply sup_le
    · exact le_trans (le_sup_left a b) (le_sup_left (a ⊔ b) c)
    · apply sup_le
      · exact le_trans (le_sup_right a b) (le_sup_left (a ⊔ b) c)
      · exact le_sup_right (a ⊔ b) c

theorem sup_idem (a : α) : a ⊔ a = a := by
  apply le_antisymm
  · exact sup_le a a a (le_refl a) (le_refl a)
  · exact le_sup_left a a

theorem sup_bot_left (a : α) : ⊥ ⊔ a = a := by
  apply le_antisymm
  · exact sup_le ⊥ a a (bot_le a) (le_refl a)
  · exact le_sup_right ⊥ a

theorem sup_bot_right (a : α) : a ⊔ ⊥ = a := by
  rw [sup_comm]; exact sup_bot_left a

/-- The order is recoverable from the join: `a ⊑ b` exactly when
    merging `a` into `b` tells `b` nothing new. -/
theorem le_iff_sup_eq {a b : α} : a ⊑ b ↔ a ⊔ b = b := by
  constructor
  · intro h
    apply le_antisymm
    · exact sup_le a b b h (le_refl b)
    · exact le_sup_right a b
  · intro h
    rw [← h]
    exact le_sup_left a b

theorem sup_mono {a b c d : α} (h₁ : a ⊑ c) (h₂ : b ⊑ d) :
    a ⊔ b ⊑ c ⊔ d :=
  sup_le a b (c ⊔ d)
    (le_trans h₁ (le_sup_left c d))
    (le_trans h₂ (le_sup_right c d))

/-- An update function may only move a replica's state upward:
    it can add information, never retract it. -/
def Inflationary (f : α → α) : Prop := ∀ s, s ⊑ f s

/-- Merging any value in is an inflationary update — the propagator
    cell's `write` and the replica's `merge` in one lemma. -/
theorem sup_inflationary_left (v : α) : Inflationary (fun s => s ⊔ v) :=
  fun s => le_sup_left s v

/-- Monotone maps, carried over from the predecessor. -/
structure Monotone {α β : Type} [LE α] [LE β]
    [PartialOrder α] [PartialOrder β] (f : α → β) : Prop where
  map_le : ∀ (a b : α), a ≤ b → f a ≤ f b

/- ── The product semilattice ─────────────────────────────────
   Pair two replicable states and the pair is replicable:
   composition is free. Load-bearing for the PN-Counter (Ch 4),
   the 2P-Set (Ch 5), the OR-Set (Ch 7) and the capstone (Ch 12). -/

instance {α β : Type} [LE α] [LE β] : LE (α × β) where
  le p q := p.1 ≤ q.1 ∧ p.2 ≤ q.2

instance {α β : Type} [LE α] [LE β] [PartialOrder α] [PartialOrder β] :
    PartialOrder (α × β) where
  le_refl p := ⟨le_refl p.1, le_refl p.2⟩
  le_antisymm {p q} h₁ h₂ := by
    cases p; cases q
    have e₁ := le_antisymm h₁.1 h₂.1
    have e₂ := le_antisymm h₁.2 h₂.2
    simp_all
  le_trans h₁ h₂ := ⟨le_trans h₁.1 h₂.1, le_trans h₁.2 h₂.2⟩

instance {α β : Type}
    [BoundedJoinSemilattice α] [BoundedJoinSemilattice β] :
    BoundedJoinSemilattice (α × β) where
  sup p q := (p.1 ⊔ q.1, p.2 ⊔ q.2)
  bot := (⊥, ⊥)
  le_sup_left p q := ⟨le_sup_left p.1 q.1, le_sup_left p.2 q.2⟩
  le_sup_right p q := ⟨le_sup_right p.1 q.1, le_sup_right p.2 q.2⟩
  sup_le p q r h₁ h₂ :=
    ⟨sup_le p.1 q.1 r.1 h₁.1 h₂.1, sup_le p.2 q.2 r.2 h₁.2 h₂.2⟩
  bot_le p := ⟨bot_le p.1, bot_le p.2⟩

end Order

/- ============================================================
   The propagator machinery, re-derived from the predecessor.
   A cell accumulates partial information by joining; in Ch 2 we
   re-read the same code as a *replica*, and in Ch 12 the capstone
   runs replicas as cells with a network attached.
   ============================================================ -/

structure Cell (α : Type) where
  ref : IO.Ref α

def Cell.new {α} [BoundedJoinSemilattice α] : IO (Cell α) := do
  let r ← IO.mkRef (⊥ : α)
  return { ref := r }

def Cell.read {α} (c : Cell α) : IO α :=
  c.ref.get

/-- Writing is merging: `c ← c ⊔ v`. Returns whether anything changed. -/
def Cell.write {α} [BoundedJoinSemilattice α] [DecidableEq α]
    (c : Cell α) (v : α) : IO Bool := do
  let old ← c.ref.get
  let merged := old ⊔ v
  if merged = old then
    return false
  else
    c.ref.set merged
    return true

abbrev PropStep := IO Bool

def runToFixpoint (steps : Array PropStep) : IO Unit := do
  let mut changed := true
  while changed do
    changed := false
    for step in steps do
      let c ← step
      if c then changed := true

/- The flat lattice over Nat, exactly as in the predecessor:
   unknown ⊑ known n ⊑ conflict. -/

inductive FlatNat where
  | unknown         : FlatNat
  | known (n : Nat) : FlatNat
  | conflict        : FlatNat
  deriving Repr, DecidableEq

instance : ToString FlatNat where
  toString a := match a with
    | .unknown  => "unknown"
    | .known n  => toString n
    | .conflict => "conflict"

def FlatNat.le (a b : FlatNat) : Prop :=
  match a, b with
    | .unknown , _         => True
    | _        , .conflict => True
    | .known m , .known n  => m = n
    | .conflict, .unknown  => False
    | .conflict, .known _  => False
    | .known _ , .unknown  => False

instance : LE FlatNat := ⟨FlatNat.le⟩

instance : Order.PartialOrder FlatNat where
  le_refl := by
    intro a
    cases a <;> trivial
  le_antisymm := by
    intro a b hab hba
    cases a <;> cases b <;> simp_all [LE.le, FlatNat.le]
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [LE.le, FlatNat.le]

instance : BoundedJoinSemilattice FlatNat where
  bot         := .unknown
  sup a b     := match a, b with
    | .unknown, x         => x
    | x       , .unknown  => x
    | .known m, .known n  => if m = n then .known m else .conflict
    | _       , _         => .conflict
  bot_le      := by
    intro a
    cases a <;> simp [LE.le, FlatNat.le]
  le_sup_left := by
    intro a b
    cases a <;> cases b <;> simp_all [LE.le, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [h]
  le_sup_right := by
    intro a b
    cases a <;> cases b <;> simp_all [LE.le, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [h]
  sup_le      := by
    intro a b c hac hbc
    cases a <;> cases b <;> cases c <;> simp_all [LE.le, FlatNat.le]
    rename_i m n
    by_cases h : m = n <;> simp [h]

def FlatNat.add (x y : FlatNat) : FlatNat :=
  match x, y with
    | .known a  , .known b  => .known (a + b)
    | .conflict , _         => .conflict
    | _         , .conflict => .conflict
    | _         , _         => .unknown

def addProp (cx cy csum : Cell FlatNat) : PropStep := do
  let x ← cx.read
  let y ← cy.read
  csum.write (FlatNat.add x y)

/-- The predecessor's example, replayed: a propagator network
    computing a sum inside one process. -/
def propagatorReplay : IO Unit := do
  let cx ← Cell.new (α := FlatNat)
  let cy ← Cell.new (α := FlatNat)
  let cs ← Cell.new (α := FlatNat)
  let _ ← cx.write (.known 3)
  let _ ← cy.write (.known 7)
  runToFixpoint #[addProp cx cy cs]
  IO.println s!"sum is {← cs.read}"

#eval propagatorReplay

/-- The same code, new reading: two *replicas* of one FlatNat cell.
    Each hears a (consistent) observation, then each merges the
    other's state — in different orders, twice. They agree. -/
def replicaReplay : IO Unit := do
  let a ← Cell.new (α := FlatNat)   -- replica A
  let b ← Cell.new (α := FlatNat)   -- replica B
  let _ ← a.write (.known 42)       -- A hears the value
  -- gossip, sloppily: B pulls from A, A pulls from B, B pulls again
  let _ ← b.write (← a.read)
  let _ ← a.write (← b.read)
  let _ ← b.write (← a.read)        -- duplicate delivery: harmless
  IO.println s!"replica A holds {← a.read}, replica B holds {← b.read}"

#eval replicaReplay

/- ============================================================
   Crdt.Intro — Chapter 1: Replicas, Conflicts, and the Price
   of Coordination
   ============================================================ -/

namespace Intro

/-- A naive replicated counter: the state is the count. -/
abbrev NaiveCounter := Nat

def incr (c : NaiveCounter) : NaiveCounter := c + 1

/-- The "obvious" sync strategy: take the other replica's value.
    (Overwrite; a.k.a. naive last-write-wins.) -/
def overwrite (_mine theirs : NaiveCounter) : NaiveCounter := theirs

/-- Two replicas, three increments, one sync. The truth is 3. -/
def divergenceDemo : List (String × Nat) :=
  let a0 : NaiveCounter := 0
  let b0 : NaiveCounter := 0
  let a1 := incr (incr a0)      -- A observes two increments  → 2
  let b1 := incr b0             -- B observes one increment   → 1
  let bSynced := overwrite b1 a1  -- B pulls from A: B's increment is gone
  let aSynced := overwrite a1 bSynced
  [("replica A", a1), ("replica B", b1),
   ("B after sync", bSynced), ("A after sync", aSynced),
   ("ground truth", 3)]

#eval divergenceDemo

/-- Refuted: "last write wins is a merge strategy for free".
    The interleaving above loses B's increment: both replicas end
    at 2 although three increments happened. -/
theorem overwrite_loses_an_update :
    (overwrite (incr 0) (incr (incr 0))) ≠ 3 := by decide

/-- Refuted (Exercise 1.3): overwrite-merge is not even commutative,
    so replicas that sync in different directions disagree. -/
theorem overwrite_not_comm :
    ¬ (∀ a b : NaiveCounter, overwrite a b = overwrite b a) :=
  fun h => absurd (h 1 2) (by decide)

example : overwrite 1 2 ≠ overwrite 2 1 := by decide

end Intro

/- ============================================================
   Crdt.GCounter — Chapter 3: Counting Without Coordination
   ============================================================ -/

/- Two refutations first; they derive the design.

   Refuted: "a distributed counter is a Nat with merge = max".
   Both replicas increment once from 0; the merge remembers one event. -/
theorem max_undercounts : Nat.max (0 + 1) (0 + 1) ≠ 2 := by decide

/- Refuted: "then use merge = (+)".
   Addition is not idempotent, so a duplicated delivery double-counts:
   a replica holding 1 that receives its own state again jumps to 2. -/
theorem add_overcounts : 1 + 1 ≠ (1 : Nat) := by decide

/-- The G-Counter: remember one tally *per replica*.
    An indexed family — your first dependent-indexed carrier. -/
def GCounter (R : Nat) : Type := Fin R → Nat

namespace GCounter

open Order.PartialOrder Order.BoundedJoinSemilattice

variable {R : Nat}

instance : LE (GCounter R) := ⟨fun g h => ∀ i, g i ≤ h i⟩

instance : Order.PartialOrder (GCounter R) where
  le_refl g i        := Nat.le_refl (g i)
  le_antisymm h₁ h₂  := funext fun i => Nat.le_antisymm (h₁ i) (h₂ i)
  le_trans h₁ h₂ i   := Nat.le_trans (h₁ i) (h₂ i)

instance : BoundedJoinSemilattice (GCounter R) where
  sup g h            := fun i => Nat.max (g i) (h i)
  bot                := fun _ => 0
  le_sup_left g h i  := Nat.le_max_left (g i) (h i)
  le_sup_right g h i := Nat.le_max_right (g i) (h i)
  sup_le _ _ _ h₁ h₂ := fun i => Nat.max_le.mpr ⟨h₁ i, h₂ i⟩
  bot_le g i         := Nat.zero_le (g i)

/-- Replica `i` increments: bump exactly your own slot. -/
def increment (i : Fin R) (g : GCounter R) : GCounter R :=
  fun j => if j = i then g j + 1 else g j

/-- The query: total of all per-replica tallies. -/
def value (g : GCounter R) : Nat :=
  (List.finRange R).foldl (fun acc i => acc + g i) 0

/-- Render the state for the interludes. -/
def toList (g : GCounter R) : List Nat :=
  (List.finRange R).map g

theorem increment_inflationary (i : Fin R) :
    Order.Inflationary (increment i) := by
  intro g j
  by_cases h : j = i <;> simp [increment, h]

theorem increment_monotone {g h : GCounter R} (i : Fin R) (hle : g ⊑ h) :
    increment i g ⊑ increment i h := by
  intro j
  by_cases hj : j = i <;> simp [increment, hj] <;> exact hle _

/-- Merging can only help: an increment survives any merge. -/
theorem increment_le_sup (i : Fin R) (g h : GCounter R) :
    increment i g ⊑ increment i g ⊔ h :=
  le_sup_left (increment i g) h

/- ── Fold helpers (generic; reused in Chapters 8, 9, 11) ──── -/

theorem foldl_add_shift {ι : Type} (f : ι → Nat) :
    ∀ (l : List ι) (a : Nat),
      l.foldl (fun acc j => acc + f j) (a + 1)
        = l.foldl (fun acc j => acc + f j) a + 1
  | [], _ => rfl
  | j :: t, a => by
      rw [List.foldl_cons, List.foldl_cons, Nat.add_right_comm]
      exact foldl_add_shift f t (a + f j)

theorem foldl_add_congr {ι : Type} {f g : ι → Nat} :
    ∀ (l : List ι), (∀ j ∈ l, f j = g j) → ∀ (a : Nat),
      l.foldl (fun acc j => acc + f j) a
        = l.foldl (fun acc j => acc + g j) a
  | [], _, _ => rfl
  | j :: t, h, a => by
      rw [List.foldl_cons, List.foldl_cons, h j List.mem_cons_self]
      exact foldl_add_congr t (fun k hk => h k (List.mem_cons_of_mem _ hk)) _

theorem foldl_add_le {ι : Type} {f g : ι → Nat} (h : ∀ j, f j ≤ g j) :
    ∀ (l : List ι) {a b : Nat}, a ≤ b →
      l.foldl (fun acc j => acc + f j) a ≤ l.foldl (fun acc j => acc + g j) b
  | [], _, _, hab => hab
  | j :: t, a, b, hab => by
      rw [List.foldl_cons, List.foldl_cons]
      exact foldl_add_le h t (Nat.add_le_add hab (h j))

/-- Bump one slot of the summand and the sum grows by exactly one.
    Proved by induction on `R` via `finRange_succ` — no Nodup needed. -/
theorem foldl_add_bump (n : Nat) :
    ∀ (f g : Fin n → Nat) (i : Fin n),
      (∀ j, j ≠ i → f j = g j) → f i = g i + 1 → ∀ (a : Nat),
      (List.finRange n).foldl (fun acc j => acc + f j) a
        = (List.finRange n).foldl (fun acc j => acc + g j) a + 1 := by
  induction n with
  | zero => intro _ _ i; exact i.elim0
  | succ n ih =>
      intro f g i hne hbump a
      rw [List.finRange_succ, List.foldl_cons, List.foldl_cons,
          List.foldl_map, List.foldl_map]
      cases i using Fin.cases with
      | zero =>
          rw [hbump, ← Nat.add_assoc]
          calc (List.finRange n).foldl (fun acc j => acc + f j.succ) (a + g 0 + 1)
              = (List.finRange n).foldl (fun acc j => acc + f j.succ) (a + g 0) + 1 :=
                foldl_add_shift _ _ _
            _ = (List.finRange n).foldl (fun acc j => acc + g j.succ) (a + g 0) + 1 := by
                rw [foldl_add_congr (List.finRange n)
                      (fun j _ => hne j.succ (Fin.succ_ne_zero j))]
      | succ i' =>
          rw [hne 0 (Ne.symm (Fin.succ_ne_zero i'))]
          exact ih (fun (j : Fin n) => f j.succ) (fun (j : Fin n) => g j.succ) i'
            (fun j hj => hne j.succ (fun hc => hj (Fin.succ_inj.mp hc)))
            hbump (a + g 0)

/-- The G-Counter counts: every increment raises the value by exactly one,
    no matter which replica performed it. -/
theorem value_increment (i : Fin R) (g : GCounter R) :
    value (increment i g) = value g + 1 :=
  foldl_add_bump R (increment i g) g i
    (fun j hj => by simp [increment, hj])
    (by simp [increment]) 0

/-- The G-Counter's query happens to be monotone.
    (Chapter 4 shows this is a coincidence, not a law.) -/
theorem value_le_value_of_le {g h : GCounter R} (hle : g ⊑ h) :
    value g ≤ value h :=
  foldl_add_le hle (List.finRange R) (Nat.le_refl 0)

theorem value_bot : value (⊥ : GCounter R) = 0 := by
  have h : ∀ (l : List (Fin R)) (a : Nat),
      l.foldl (fun acc i => acc + (⊥ : GCounter R) i) a = a := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons j t ih => intro a; rw [List.foldl_cons]; exact ih _
  exact h _ 0

/-- Interlude: three replicas, out-of-order and duplicated merges. -/
def interlude : List (String × List Nat × Nat) :=
  let gA := increment 0 (increment 0 (⊥ : GCounter 3))  -- A increments twice
  let gB := increment 1 (⊥ : GCounter 3)                 -- B increments once
  let gC := increment 2 (⊥ : GCounter 3)                 -- C increments once
  let atA := (gA ⊔ gB) ⊔ (gC ⊔ gB)   -- B delivered twice
  let atB := gC ⊔ (gA ⊔ (gB ⊔ gA))   -- another order, A delivered twice
  let atC := (gB ⊔ gC) ⊔ gA          -- a third order
  [ ("replica A", toList atA, value atA),
    ("replica B", toList atB, value atB),
    ("replica C", toList atC, value atC) ]

#eval interlude

end GCounter

/- ============================================================
   Crdt.PNCounter — Chapter 4: Decrements and the
   Query/State Split
   ============================================================ -/

/-- Two G-Counters: increments land in `P` (first), decrements in `N`
    (second). State only ever grows; the *query* subtracts. -/
abbrev PNCounter (R : Nat) := GCounter R × GCounter R

namespace PNCounter

open Order.PartialOrder Order.BoundedJoinSemilattice

variable {R : Nat}

def incr (i : Fin R) (p : PNCounter R) : PNCounter R :=
  (GCounter.increment i p.1, p.2)

def decr (i : Fin R) (p : PNCounter R) : PNCounter R :=
  (p.1, GCounter.increment i p.2)

def value (p : PNCounter R) : Int :=
  (GCounter.value p.1 : Int) - (GCounter.value p.2 : Int)

theorem incr_inflationary (i : Fin R) : Order.Inflationary (incr (R := R) i) :=
  fun p => ⟨GCounter.increment_inflationary i p.1, le_refl p.2⟩

/-- Even a decrement moves the *state* upward. -/
theorem decr_inflationary (i : Fin R) : Order.Inflationary (decr (R := R) i) :=
  fun p => ⟨le_refl p.1, GCounter.increment_inflationary i p.2⟩

/-- A decrement lowers the value while the state strictly grows. -/
theorem value_decr (i : Fin R) (p : PNCounter R) :
    value (decr i p) = value p - 1 := by
  show (GCounter.value p.1 : Int) - (GCounter.value (GCounter.increment i p.2) : Int)
      = (GCounter.value p.1 : Int) - (GCounter.value p.2 : Int) - 1
  rw [GCounter.value_increment]
  omega

/-- Refuted: "the CRDT's value is monotone".
    States only grow; reports may fall. The lattice disciplines what is
    *remembered*, not what is *reported*. -/
theorem value_not_monotone :
    ¬ (∀ (p q : PNCounter 1), p ⊑ q → value p ≤ value q) := by
  intro h
  have hle : (⊥ : PNCounter 1) ⊑ (⊥, GCounter.increment 0 ⊥) :=
    ⟨bot_le _, bot_le _⟩
  exact absurd (h _ _ hle) (by decide)

/-- Refuted: the value of a merge is not the max (nor min, nor either
    argument) of the values — value is a *projection*, not a lattice map. -/
theorem value_merge_ne_max :
    let p : PNCounter 1 := incr 0 ⊥
    let q : PNCounter 1 := decr 0 ⊥
    value (p ⊔ q) ≠ max (value p) (value q) := by decide

theorem value_bot : value (⊥ : PNCounter R) = 0 := by
  show (GCounter.value (⊥ : GCounter R) : Int) - (GCounter.value (⊥ : GCounter R) : Int) = 0
  rw [GCounter.value_bot]
  decide

/-- Interlude: concurrent increments and decrements at two replicas,
    merged both ways. -/
def interlude : List (String × Int) :=
  let atA := incr 0 (incr 0 (⊥ : PNCounter 2))  -- A: +2
  let atB := decr 1 (incr 1 (⊥ : PNCounter 2))  -- B: +1 then −1
  [ ("A alone", value atA),
    ("B alone", value atB),
    ("A ⊔ B", value (atA ⊔ atB)),
    ("B ⊔ A", value (atB ⊔ atA)),
    ("(A ⊔ B) ⊔ B", value ((atA ⊔ atB) ⊔ atB)) ]

#eval interlude

end PNCounter

/- ============================================================
   Crdt.SList — Chapter 5: Sets That Only Grow
   Finite sets as strictly sorted lists. Strict sortedness gives
   duplicate-freeness for free, and — crucially — a *canonical*
   representation: same members, same list. That canonicity is
   what antisymmetry of ⊑ (and hence the semilattice) rests on.
   ============================================================ -/

/-- A decidable total order on the element type. `Nat` is the running
    example; lexicographic products arrive in Chapter 6 and pay off in
    Chapter 7. `≼`/`≺` are the *element* order — not to be confused
    with the information order `⊑` on states. -/
class TotalOrder (α : Type) where
  le : α → α → Prop
  deq : DecidableEq α
  decLe : (a b : α) → Decidable (le a b)
  le_refl : ∀ (a : α), le a a
  le_antisymm : ∀ {a b : α}, le a b → le b a → a = b
  le_trans : ∀ {a b c : α}, le a b → le b c → le a c
  le_total : ∀ (a b : α), le a b ∨ le b a

attribute [instance] TotalOrder.deq TotalOrder.decLe

infix:55 " ≼ " => TotalOrder.le

/-- Strictly below. -/
abbrev TotalOrder.lt {α : Type} [TotalOrder α] (a b : α) : Prop :=
  a ≼ b ∧ a ≠ b

infix:55 " ≺ " => TotalOrder.lt

namespace TotalOrder

variable {α : Type} [TotalOrder α]

theorem le_of_lt {a b : α} (h : a ≺ b) : a ≼ b := h.1

theorem lt_irrefl (a : α) : ¬ a ≺ a := fun h => h.2 rfl

theorem lt_of_not_le {a b : α} (h : ¬ a ≼ b) : b ≺ a := by
  constructor
  · exact (le_total a b).resolve_left h
  · intro he
    subst he
    exact h (le_refl b)

theorem not_le_of_lt {a b : α} (h : a ≺ b) : ¬ b ≼ a :=
  fun hba => h.2 (le_antisymm h.1 hba)

theorem lt_trans {a b c : α} (h₁ : a ≺ b) (h₂ : b ≺ c) : a ≺ c := by
  refine ⟨le_trans h₁.1 h₂.1, fun he => ?_⟩
  subst he
  exact h₂.2 (le_antisymm h₂.1 h₁.1)

theorem lt_of_lt_of_le {a b c : α} (h₁ : a ≺ b) (h₂ : b ≼ c) : a ≺ c := by
  refine ⟨le_trans h₁.1 h₂, fun he => ?_⟩
  subst he
  exact h₁.2 (le_antisymm h₁.1 h₂)

instance : TotalOrder Nat where
  le          := Nat.le
  deq         := inferInstance
  decLe       := Nat.decLe
  le_refl     := Nat.le_refl
  le_antisymm := Nat.le_antisymm
  le_trans    := Nat.le_trans
  le_total    := Nat.le_total

end TotalOrder

namespace SList

open TotalOrder

variable {α : Type} [TotalOrder α]

/-- Strictly ascending — sorted *and* duplicate-free in one predicate. -/
inductive Sorted : List α → Prop where
  | nil : Sorted []
  | single (a : α) : Sorted [a]
  | cons {a b : α} {l : List α} (hab : a ≺ b) (h : Sorted (b :: l)) :
      Sorted (a :: b :: l)

theorem sorted_tail {a : α} {l : List α} (h : Sorted (a :: l)) : Sorted l := by
  cases h with
  | single => exact .nil
  | cons _ h => exact h

/-- In a sorted list the head is strictly below everything in the tail. -/
theorem sorted_head_lt {a : α} {l : List α} :
    Sorted (a :: l) → ∀ x ∈ l, a ≺ x := by
  induction l generalizing a with
  | nil => intro _ x hx; cases hx
  | cons b t ih =>
      intro h x hx
      cases h with
      | cons hab hbt =>
          cases List.mem_cons.mp hx with
          | inl he => subst he; exact hab
          | inr ht => exact lt_trans hab (ih hbt x ht)

/-- The head of a sorted list is its minimum. -/
theorem sorted_head_le {a : α} {l : List α}
    (h : Sorted (a :: l)) : ∀ x ∈ a :: l, a ≼ x := by
  intro x hx
  cases List.mem_cons.mp hx with
  | inl he => subst he; exact le_refl x
  | inr ht => exact le_of_lt (sorted_head_lt h x ht)

theorem sorted_cons_of_lt {a : α} {l : List α}
    (hl : Sorted l) (h : ∀ x ∈ l, a ≺ x) : Sorted (a :: l) := by
  cases l with
  | nil => exact .single a
  | cons b t => exact .cons (h b List.mem_cons_self) hl

/-- Ordered insert, skipping duplicates. Structural recursion, so every
    counterexample in this chapter runs under `decide`. -/
def insertS (x : α) : List α → List α
  | [] => [x]
  | a :: l =>
      if x = a then a :: l
      else if x ≼ a then x :: a :: l
      else a :: insertS x l

theorem mem_insertS {x y : α} : ∀ {l : List α},
    x ∈ insertS y l ↔ x = y ∨ x ∈ l
  | [] => by simp [insertS]
  | a :: t => by
      by_cases h₁ : y = a
      · subst h₁
        have hins : insertS y (y :: t) = y :: t := by simp [insertS]
        rw [hins]
        constructor
        · exact Or.inr
        · intro h
          exact h.elim (fun he => List.mem_cons.mpr (Or.inl he)) id
      · by_cases h₂ : y ≼ a
        · simp only [insertS, if_neg h₁, if_pos h₂]
          exact List.mem_cons
        · simp only [insertS, if_neg h₁, if_neg h₂, List.mem_cons,
                     mem_insertS (l := t)]
          constructor
          · intro h
            cases h with
            | inl he => exact Or.inr (Or.inl he)
            | inr hm =>
                cases hm with
                | inl he => exact Or.inl he
                | inr ht => exact Or.inr (Or.inr ht)
          · intro h
            cases h with
            | inl he => exact Or.inr (Or.inl he)
            | inr hm =>
                cases hm with
                | inl he => exact Or.inl he
                | inr ht => exact Or.inr (Or.inr ht)

theorem sorted_insertS {y : α} : ∀ {l : List α},
    Sorted l → Sorted (insertS y l)
  | [], _ => .single y
  | a :: t, h => by
      by_cases h₁ : y = a
      · simpa [insertS, if_pos h₁] using h
      · by_cases h₂ : y ≼ a
        · simp only [insertS, if_neg h₁, if_pos h₂]
          exact .cons ⟨h₂, h₁⟩ h
        · simp only [insertS, if_neg h₁, if_neg h₂]
          have hay : a ≺ y := lt_of_not_le h₂
          apply sorted_cons_of_lt (sorted_insertS (sorted_tail h))
          intro x hx
          cases mem_insertS.mp hx with
          | inl he => subst he; exact hay
          | inr ht => exact sorted_head_lt h x ht

/-- Union of raw lists: insert everything from `l` into `m`. -/
def unionL (l m : List α) : List α := l.foldr insertS m

theorem mem_unionL {x : α} : ∀ {l m : List α},
    x ∈ unionL l m ↔ x ∈ l ∨ x ∈ m
  | [], m => by simp [unionL]
  | a :: t, m => by
      simp only [unionL, List.foldr_cons]
      rw [show (List.foldr insertS m t) = unionL t m from rfl] at *
      simp only [mem_insertS, mem_unionL (l := t), List.mem_cons, or_assoc]

theorem sorted_unionL {l m : List α} (hm : Sorted m) : Sorted (unionL l m) := by
  induction l with
  | nil => exact hm
  | cons a t ih => exact sorted_insertS ih

/-- Keep the members satisfying `p`; sortedness survives. -/
theorem sorted_filter (p : α → Bool) :
    ∀ {l : List α}, Sorted l → Sorted (List.filter p l)
  | [], _ => .nil
  | a :: t, h => by
      by_cases hp : p a
      · rw [List.filter_cons_of_pos hp]
        apply sorted_cons_of_lt (sorted_filter p (sorted_tail h))
        intro x hx
        exact sorted_head_lt h x (List.mem_filter.mp hx).1
      · rw [List.filter_cons_of_neg hp]
        exact sorted_filter p (sorted_tail h)

/-- **The workhorse.** Two sorted, duplicate-free lists with the same
    members are the same list: sortedness makes the representation
    canonical, and canonicity is what the merge algebra stands on. -/
theorem sorted_ext : ∀ {l₁ l₂ : List α}, Sorted l₁ → Sorted l₂ →
    (∀ x, x ∈ l₁ ↔ x ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => by cases (h b).mpr List.mem_cons_self
  | a :: _, [], _, _, h => by cases (h a).mp List.mem_cons_self
  | a :: t₁, b :: t₂, h₁, h₂, h => by
      have hab : a = b := by
        have ha₂ : a ∈ b :: t₂ := (h a).mp List.mem_cons_self
        have hb₁ : b ∈ a :: t₁ := (h b).mpr List.mem_cons_self
        exact le_antisymm (sorted_head_le h₁ b hb₁) (sorted_head_le h₂ a ha₂)
      subst hab
      have htails : ∀ x, x ∈ t₁ ↔ x ∈ t₂ := by
        intro x
        constructor
        · intro hx
          have hne : x ≠ a :=
            fun he => lt_irrefl a (he ▸ sorted_head_lt h₁ x hx)
          cases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem a hx)) with
          | inl he => exact absurd he hne
          | inr hm => exact hm
        · intro hx
          have hne : x ≠ a :=
            fun he => lt_irrefl a (he ▸ sorted_head_lt h₂ x hx)
          cases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem a hx)) with
          | inl he => exact absurd he hne
          | inr hm => exact hm
      rw [sorted_ext (sorted_tail h₁) (sorted_tail h₂) htails]

end SList

/-- A finite set: a strictly sorted list plus the proof that it is one. -/
structure SList (α : Type) [TotalOrder α] where
  val : List α
  sorted : SList.Sorted val

namespace SList

open TotalOrder Order.PartialOrder Order.BoundedJoinSemilattice

variable {α : Type} [TotalOrder α]

instance : Membership α (SList α) := ⟨fun s x => x ∈ s.val⟩

theorem mem_def {x : α} {s : SList α} : x ∈ s ↔ x ∈ s.val := Iff.rfl

instance {x : α} {s : SList α} : Decidable (x ∈ s) :=
  inferInstanceAs (Decidable (x ∈ s.val))

/-- Same value, same set — the `Sorted` proof is irrelevant. -/
theorem val_inj {s t : SList α} (h : s.val = t.val) : s = t := by
  cases s; cases t; cases h; rfl

/-- Same members, same set. The `sorted_ext` payoff. -/
theorem ext_mem {s t : SList α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  val_inj (sorted_ext s.sorted t.sorted h)

instance : DecidableEq (SList α) := fun s t =>
  if h : s.val = t.val then isTrue (val_inj h)
  else isFalse (fun he => h (congrArg SList.val he))

def empty : SList α := ⟨[], .nil⟩

def insert (x : α) (s : SList α) : SList α :=
  ⟨insertS x s.val, sorted_insertS s.sorted⟩

def union (s t : SList α) : SList α :=
  ⟨unionL s.val t.val, sorted_unionL t.sorted⟩

def filter (p : α → Bool) (s : SList α) : SList α :=
  ⟨s.val.filter p, sorted_filter p s.sorted⟩

def size (s : SList α) : Nat := s.val.length

@[simp] theorem mem_insert {x y : α} {s : SList α} :
    x ∈ insert y s ↔ x = y ∨ x ∈ s := mem_insertS

@[simp] theorem mem_union {x : α} {s t : SList α} :
    x ∈ union s t ↔ x ∈ s ∨ x ∈ t := mem_unionL

@[simp] theorem mem_filter {x : α} {p : α → Bool} {s : SList α} :
    x ∈ filter p s ↔ x ∈ s ∧ p x := List.mem_filter

@[simp] theorem not_mem_empty (x : α) : ¬ x ∈ (empty : SList α) := by
  intro h
  cases h

/- The information order: subset. Antisymmetry is exactly `ext_mem`,
   which is exactly `sorted_ext` — canonicity is load-bearing. -/

instance : LE (SList α) := ⟨fun s t => ∀ x ∈ s, x ∈ t⟩

theorem le_def {s t : SList α} : s ⊑ t ↔ ∀ x ∈ s, x ∈ t := Iff.rfl

instance {s t : SList α} : Decidable (s ⊑ t) :=
  List.decidableBAll (· ∈ t.val) s.val

instance : Order.PartialOrder (SList α) where
  le_refl _ _ hx := hx
  le_antisymm h₁ h₂ := ext_mem fun x => ⟨h₁ x, h₂ x⟩
  le_trans h₁ h₂ x hx := h₂ x (h₁ x hx)

instance : BoundedJoinSemilattice (SList α) where
  sup := union
  bot := empty
  le_sup_left _ _ _ hx := mem_union.mpr (Or.inl hx)
  le_sup_right _ _ _ hx := mem_union.mpr (Or.inr hx)
  sup_le _ _ _ h₁ h₂ x hx :=
    match mem_union.mp hx with
    | Or.inl hs => h₁ x hs
    | Or.inr ht => h₂ x ht
  bot_le _ x hx := absurd hx (not_mem_empty x)

/- ACI for union now falls out of the generic algebra — the same three
   laws, reached by a set-theoretic route. -/

theorem union_comm (s t : SList α) : union s t = union t s :=
  Order.sup_comm s t

theorem union_assoc (s t u : SList α) :
    union (union s t) u = union s (union t u) :=
  Order.sup_assoc s t u

theorem union_idem (s : SList α) : union s s = s :=
  Order.sup_idem s

/-- Build a set from any list — the canonical form of its members. -/
def ofList (l : List α) : SList α := ⟨unionL l [], sorted_unionL .nil⟩

@[simp] theorem mem_ofList {x : α} {l : List α} : x ∈ ofList l ↔ x ∈ l := by
  show x ∈ unionL l [] ↔ x ∈ l
  rw [mem_unionL]
  simp

end SList

/- ============================================================
   Crdt.GSet and Crdt.TwoPSet — Chapter 5 continued
   ============================================================ -/

/-- The grow-only set over `Nat`: an `SList` read as a CRDT.
    Update = insert (inflationary), merge = union, query = membership. -/
abbrev GSet := SList Nat

namespace GSet

open Order.BoundedJoinSemilattice

def add (x : Nat) (s : GSet) : GSet := SList.insert x s

theorem add_inflationary (x : Nat) : Order.Inflationary (add x) :=
  fun _ _ hy => SList.mem_insert.mpr (Or.inr hy)

/-- Refuted: "remove-by-deletion is monotone". Deleting moves *down*
    the lattice, and a merge with any peer that still holds the element
    resurrects it. -/
def naiveRemove (x : Nat) (s : GSet) : GSet := SList.filter (· != x) s

theorem naiveRemove_not_inflationary :
    ¬ (add 1 (⊥ : GSet) ⊑ naiveRemove 1 (add 1 (⊥ : GSet))) := by decide

theorem naiveRemove_resurrects :
    1 ∈ (naiveRemove 1 (add 1 (⊥ : GSet)) ⊔ add 1 (⊥ : GSet)) := by decide

end GSet

/-- The two-phase set: a grow-only set of adds and a grow-only set of
    tombstones. Removal *adds* a tombstone — states only grow. -/
abbrev TwoPSet := GSet × GSet

namespace TwoPSet

open Order.PartialOrder Order.BoundedJoinSemilattice

def adds (s : TwoPSet) : GSet := s.1
def tombs (s : TwoPSet) : GSet := s.2

def add (x : Nat) (s : TwoPSet) : TwoPSet := (SList.insert x s.1, s.2)

def remove (x : Nat) (s : TwoPSet) : TwoPSet := (s.1, SList.insert x s.2)

/-- Membership: added and not tombstoned. -/
def mem (x : Nat) (s : TwoPSet) : Prop := x ∈ s.1 ∧ ¬ x ∈ s.2

instance {x : Nat} {s : TwoPSet} : Decidable (mem x s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Removal is inflationary *on state* — the tombstone is information. -/
theorem remove_inflationary (x : Nat) : Order.Inflationary (remove x) :=
  fun s => ⟨le_refl s.1, fun _ hy => SList.mem_insert.mpr (Or.inr hy)⟩

/-- Refuted: "the 2P-Set supports re-adding". Add, remove, add again:
    membership stays false — the tombstone outvotes every later add.
    This cliffhanger is resolved by the OR-Set (Chapter 7). -/
theorem no_readd :
    ¬ mem 1 (add 1 (remove 1 (add 1 (⊥ : TwoPSet)))) := by decide

/-- ... even though the element is in `adds` twice over. -/
theorem readd_recorded :
    1 ∈ adds (add 1 (remove 1 (add 1 (⊥ : TwoPSet)))) := by decide

/-- Interlude: the 2P-Set converges regardless of merge order — it just
    converges to "removed wins, forever". -/
def interlude : List (String × Bool) :=
  let atA := add 3 (add 1 (⊥ : TwoPSet))       -- A adds 1, 3
  let atB := remove 1 (add 1 (⊥ : TwoPSet))    -- B adds 1 then removes it
  [ ("1 ∈ A ⊔ B", decide (mem 1 (atA ⊔ atB))),
    ("1 ∈ B ⊔ A", decide (mem 1 (atB ⊔ atA))),
    ("3 ∈ A ⊔ B", decide (mem 3 (atA ⊔ atB))),
    ("re-add at A ⊔ B", decide (mem 1 (add 1 (atA ⊔ atB)))) ]

#eval interlude

end TwoPSet

/- ============================================================
   Crdt.LWW — Chapter 6: Last Writer Wins
   Overwrite semantics recovered lawfully: reify time into the
   state so that merge can order writes.
   ============================================================ -/

namespace LWW

open TotalOrder Order.PartialOrder Order.BoundedJoinSemilattice

/- Refuted: "LWW merge with bare timestamps is commutative".
   On a tie, whoever is the left argument wins — replicas that merge
   in opposite directions disagree forever. -/

/-- A naive timestamped write `(timestamp, value)` merged by
    timestamp alone. -/
def naiveMerge (a b : Nat × Nat) : Nat × Nat :=
  if a.1 < b.1 then b else a

theorem naive_tie_breaks_comm :
    naiveMerge (3, 10) (3, 20) ≠ naiveMerge (3, 20) (3, 10) := by decide

end LWW

/- The fix: totalize the order. First, more `TotalOrder` instances —
   proved once, reused for stamps here and for tags in Chapter 7. -/

namespace TotalOrder

instance : TotalOrder Bool where
  le a b := (!a || b) = true
  deq := inferInstance
  decLe _ _ := inferInstanceAs (Decidable (_ = true))
  le_refl := by intro a; cases a <;> simp
  le_antisymm := by intro a b h₁ h₂; cases a <;> cases b <;> simp_all
  le_trans := by intro a b c h₁ h₂; cases a <;> cases b <;> cases c <;> simp_all
  le_total := by intro a b; cases a <;> cases b <;> simp

instance {n : Nat} : TotalOrder (Fin n) where
  le a b := a.val ≤ b.val
  deq := inferInstance
  decLe a b := Nat.decLe a.val b.val
  le_refl a := Nat.le_refl a.val
  le_antisymm h₁ h₂ := Fin.ext (Nat.le_antisymm h₁ h₂)
  le_trans := Nat.le_trans
  le_total a b := Nat.le_total a.val b.val

/-- The lexicographic order on pairs: compare firsts, tie-break on
    seconds. Total because ties in the first coordinate are *equalities*
    (that is what antisymmetry buys). -/
instance instTotalOrderProd {α β : Type} [TotalOrder α] [TotalOrder β] :
    TotalOrder (α × β) where
  le p q := p.1 ≺ q.1 ∨ (p.1 = q.1 ∧ p.2 ≼ q.2)
  deq := inferInstance
  decLe _ _ := inferInstanceAs (Decidable (_ ∨ _))
  le_refl p := Or.inr ⟨rfl, le_refl p.2⟩
  le_antisymm {p q} h₁ h₂ := by
    rcases h₁ with h₁ | ⟨he₁, hle₁⟩
    · rcases h₂ with h₂ | ⟨he₂, _⟩
      · exact absurd h₂.1 (not_le_of_lt h₁)
      · rw [he₂] at h₁
        exact absurd h₁ (lt_irrefl _)
    · rcases h₂ with h₂ | ⟨_, hle₂⟩
      · rw [he₁] at h₂
        exact absurd h₂ (lt_irrefl _)
      · cases p; cases q
        simp_all
        exact le_antisymm hle₁ hle₂
  le_trans {p q r} h₁ h₂ := by
    rcases h₁ with h₁ | ⟨he₁, hle₁⟩
    · rcases h₂ with h₂ | ⟨he₂, _⟩
      · exact Or.inl (lt_trans h₁ h₂)
      · exact Or.inl (he₂ ▸ h₁)
    · rcases h₂ with h₂ | ⟨he₂, hle₂⟩
      · exact Or.inl (he₁ ▸ h₂)
      · exact Or.inr ⟨he₁.trans he₂, le_trans hle₁ hle₂⟩
  le_total p q := by
    by_cases he : p.1 = q.1
    · rcases le_total p.2 q.2 with h | h
      · exact Or.inl (Or.inr ⟨he, h⟩)
      · exact Or.inr (Or.inr ⟨he.symm, h⟩)
    · rcases le_total p.1 q.1 with h | h
      · exact Or.inl (Or.inl ⟨h, he⟩)
      · exact Or.inr (Or.inl ⟨h, fun hc => he hc.symm⟩)

/- ── max of a total order, abstractly ────────────────────────
   The "prove the abstract lemma once" move: ACI for max-by-order
   is one proof, instantiated for stamps in this chapter and reused
   by every LWW-like design. -/

variable {α : Type} [TotalOrder α]

/-- The larger of two elements. -/
def maxo (a b : α) : α := if a ≼ b then b else a

theorem le_maxo_left (a b : α) : a ≼ maxo a b := by
  unfold maxo; split
  · assumption
  · exact le_refl a

theorem le_maxo_right (a b : α) : b ≼ maxo a b := by
  unfold maxo; split
  · exact le_refl b
  · rename_i h
    exact le_of_lt (lt_of_not_le h)

theorem maxo_le {a b c : α} (h₁ : a ≼ c) (h₂ : b ≼ c) : maxo a b ≼ c := by
  unfold maxo; split <;> assumption

theorem maxo_idem (a : α) : maxo a a = a := by
  simp [maxo]

theorem maxo_comm (a b : α) : maxo a b = maxo b a := by
  unfold maxo
  by_cases h₁ : a ≼ b <;> by_cases h₂ : b ≼ a <;> simp [h₁, h₂]
  · exact le_antisymm h₂ h₁
  · exact absurd ((le_total a b).resolve_left h₁) h₂

theorem maxo_assoc (a b c : α) : maxo (maxo a b) c = maxo a (maxo b c) := by
  by_cases h₁ : a ≼ b <;> by_cases h₂ : b ≼ c
  · simp [maxo, h₁, h₂, le_trans h₁ h₂]
  · simp [maxo, h₁, h₂]
  · simp [maxo, h₁, h₂]
  · have hcb : c ≺ b := lt_of_not_le h₂
    have hba : b ≺ a := lt_of_not_le h₁
    have hca : ¬ a ≼ c := not_le_of_lt (lt_trans hcb hba)
    simp [maxo, h₁, h₂, hca]

end TotalOrder

namespace LWW

open TotalOrder Order.PartialOrder Order.BoundedJoinSemilattice

/-- A stamp: `(timestamp, replicaId)`, ordered lexicographically.
    Replica ids are distinct, so stamps of concurrently coexisting
    writes never tie. -/
abbrev Stamp (R : Nat) := Nat × Fin R

/-- A write: a stamp plus the written value. The whole payload is
    ordered lexicographically — the value-level tiebreak is unreachable
    in real executions (stamps are unique per write) and exists to make
    the algebra total on the carrier. -/
abbrev Write (R : Nat) (α : Type) [TotalOrder α] := Stamp R × α

/- ── The Option lattice over any total order ─────────────────
   `none` is "never written" (the bottom); merge is max-by-order.
   Proved once, generically; the LWW register is an instance. -/

/-- "Never written" is below everything; two writes compare by order. -/
def leO {α : Type} [TotalOrder α] : Option α → Option α → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => a ≼ b

instance {α : Type} [TotalOrder α] : LE (Option α) := ⟨leO⟩

/-- Merging two optional writes: the larger one wins. -/
def mergeO {α : Type} [TotalOrder α] : Option α → Option α → Option α
  | none, y => y
  | x, none => x
  | some a, some b => some (maxo a b)

instance {α : Type} [TotalOrder α] : Order.PartialOrder (Option α) where
  le_refl x := by
    cases x with
    | none => trivial
    | some a => exact TotalOrder.le_refl a
  le_antisymm {x y} h₁ h₂ := by
    cases x with
    | none =>
        cases y with
        | none => rfl
        | some b => exact False.elim h₂
    | some a =>
        cases y with
        | none => exact False.elim h₁
        | some b => exact congrArg some (TotalOrder.le_antisymm h₁ h₂)
  le_trans {x y z} h₁ h₂ := by
    cases x with
    | none => trivial
    | some a =>
        cases y with
        | none => exact False.elim h₁
        | some b =>
            cases z with
            | none => exact False.elim h₂
            | some c => exact TotalOrder.le_trans h₁ h₂

instance {α : Type} [TotalOrder α] : BoundedJoinSemilattice (Option α) where
  sup := mergeO
  bot := none
  le_sup_left x y := by
    cases x with
    | none => trivial
    | some a =>
        cases y with
        | none => exact TotalOrder.le_refl a
        | some b => exact le_maxo_left a b
  le_sup_right x y := by
    cases y with
    | none => cases x <;> trivial
    | some b =>
        cases x with
        | none => exact TotalOrder.le_refl b
        | some a => exact le_maxo_right a b
  sup_le x y z h₁ h₂ := by
    cases x with
    | none =>
        cases y with
        | none => trivial
        | some b => exact h₂
    | some a =>
        cases y with
        | none => exact h₁
        | some b =>
            cases z with
            | none => exact False.elim h₁
            | some c => exact maxo_le h₁ h₂
  bot_le x := by cases x <;> trivial

/-- The LWW register: an optional stamped write, merged by taking the
    lexicographically larger one. -/
abbrev LWWReg (R : Nat) (α : Type) [TotalOrder α] := Option (Write R α)

/-- Write at replica `i`, logical time `t`. Merging (not overwriting!)
    keeps the update inflationary even if `t` is stale. -/
def write {R : Nat} {α : Type} [TotalOrder α]
    (t : Nat) (i : Fin R) (v : α) (r : LWWReg R α) : LWWReg R α :=
  r ⊔ some ((t, i), v)

/-- The observable value. -/
def read {R : Nat} {α : Type} [TotalOrder α] (r : LWWReg R α) : Option α :=
  r.map (·.2)

theorem write_inflationary {R : Nat} {α : Type} [TotalOrder α]
    (t : Nat) (i : Fin R) (v : α) :
    Order.Inflationary (write (R := R) t i v) :=
  fun r => le_sup_left r (some ((t, i), v))

/- The three ACI laws, now theorems about the register — reached by a
   third route (linear-order max), same algebra. Stated for the generic
   Option lattice; the register inherits them. -/

theorem merge_comm {α : Type} [TotalOrder α] (x y : Option α) :
    x ⊔ y = y ⊔ x := Order.sup_comm x y

theorem merge_assoc {α : Type} [TotalOrder α] (x y z : Option α) :
    x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := Order.sup_assoc x y z

theorem merge_idem {α : Type} [TotalOrder α] (x : Option α) :
    x ⊔ x = x := Order.sup_idem x

/-- The tie that broke `naiveMerge`, resolved: same timestamp, distinct
    replicas, both merge orders give the same winner. -/
theorem tie_resolved :
    (write 3 (0 : Fin 2) 10 ⊥ ⊔ write 3 1 20 ⊥)
      = (write 3 1 20 ⊥ ⊔ write 3 (0 : Fin 2) 10 ⊥) := by decide

/-- Interlude demo: reads after out-of-order, duplicated merges. -/
def interlude : List (String × Option Nat) :=
  let w₁ : LWWReg 2 Nat := write 1 0 100 ⊥   -- replica 0 writes 100 at t=1
  let w₂ : LWWReg 2 Nat := write 2 1 200 ⊥   -- replica 1 writes 200 at t=2
  let w₃ : LWWReg 2 Nat := write 2 0 150 ⊥   -- replica 0 writes 150 at t=2 (tie!)
  [ ("read (w₁ ⊔ w₂)", read (w₁ ⊔ w₂)),
    ("read (w₂ ⊔ w₁)", read (w₂ ⊔ w₁)),
    ("read (w₂ ⊔ w₃)  -- t=2 tie, replica 1 wins", read (w₂ ⊔ w₃)),
    ("read (w₃ ⊔ w₂)", read (w₃ ⊔ w₂)),
    ("read ((w₁ ⊔ w₂) ⊔ w₂)", read ((w₁ ⊔ w₂) ⊔ w₂)) ]

#eval interlude

end LWW

/- ── The pointwise function lattice ───────────────────────────
   States indexed by keys: if the per-key state is a semilattice, the
   whole map is, key by key. (Requires a semilattice codomain, so it
   never collides with the hand-built `GCounter` instance — `Nat`
   itself is not a `BoundedJoinSemilattice` here.) -/

namespace Order

instance instFunLE {ι α : Type} [BoundedJoinSemilattice α] : LE (ι → α) :=
  ⟨fun f g => ∀ i, f i ≤ g i⟩

instance instFunPartialOrder {ι α : Type} [BoundedJoinSemilattice α] :
    PartialOrder (ι → α) where
  le_refl f i := PartialOrder.le_refl (f i)
  le_antisymm h₁ h₂ := funext fun i => PartialOrder.le_antisymm (h₁ i) (h₂ i)
  le_trans h₁ h₂ i := PartialOrder.le_trans (h₁ i) (h₂ i)

instance instFunBJS {ι α : Type} [BoundedJoinSemilattice α] :
    BoundedJoinSemilattice (ι → α) where
  sup f g := fun i => f i ⊔ g i
  bot := fun _ => ⊥
  le_sup_left f g i := BoundedJoinSemilattice.le_sup_left (f i) (g i)
  le_sup_right f g i := BoundedJoinSemilattice.le_sup_right (f i) (g i)
  sup_le f g h h₁ h₂ i := BoundedJoinSemilattice.sup_le (f i) (g i) (h i) (h₁ i) (h₂ i)
  bot_le f i := BoundedJoinSemilattice.bot_le (f i)

end Order

namespace LWW

open TotalOrder Order.PartialOrder Order.BoundedJoinSemilattice

/-- The LWW-Element-Set: one Boolean LWW register per element.
    `true` = "last word was add", `false` = "last word was remove". -/
abbrev LWWElementSet (R : Nat) := Nat → LWWReg R Bool

namespace LWWElementSet

variable {R : Nat}

def stampWrite (e : Nat) (t : Nat) (i : Fin R) (b : Bool)
    (s : LWWElementSet R) : LWWElementSet R :=
  fun e' => if e' = e then write t i b (s e') else s e'

def add (e t : Nat) (i : Fin R) (s : LWWElementSet R) : LWWElementSet R :=
  stampWrite e t i true s

def remove (e t : Nat) (i : Fin R) (s : LWWElementSet R) : LWWElementSet R :=
  stampWrite e t i false s

def mem (e : Nat) (s : LWWElementSet R) : Bool :=
  match s e with
  | some (_, b) => b
  | none => false

theorem stampWrite_inflationary (e t : Nat) (i : Fin R) (b : Bool) :
    Order.Inflationary (stampWrite e t i b) := by
  intro s e'
  by_cases h : e' = e <;> simp [stampWrite, h]
  · exact write_inflationary t i b (s e)
  · exact le_refl (s e')

/-- Merging maps merges each element's register — by definition. -/
theorem mem_merge (e : Nat) (s t : LWWElementSet R) :
    mem e (s ⊔ t) = mem e (fun e' => s e' ⊔ t e') := rfl

/-- Interlude: concurrent add and remove of the same element resolve
    by stamp, identically at every replica. -/
def interlude : List (String × Bool) :=
  let s₀ : LWWElementSet 2 := ⊥
  let atA := add 1 1 0 (add 7 1 0 s₀)          -- A adds 1 and 7 at t=1
  let atB := remove 1 2 1 s₀                    -- B removes 1 at t=2
  [ ("1 ∈ A ⊔ B", mem 1 (atA ⊔ atB)),
    ("1 ∈ B ⊔ A", mem 1 (atB ⊔ atA)),
    ("7 ∈ A ⊔ B", mem 7 (atA ⊔ atB)),
    ("re-add 1 at t=3", mem 1 (add 1 3 0 (atA ⊔ atB))) ]

#eval interlude

end LWWElementSet

end LWW

/- ============================================================
   Crdt.ORSet — Chapter 7: The OR-Set. Add Wins.
   Fix the 2P-Set's no-re-add and the LWW-Set's arbitration with
   *unique tags*: every add mints a fresh tag; remove tombstones
   only the tags it has observed. A later add carries a tag no
   tombstone covers.
   ============================================================ -/

namespace ORSet

/-- A tag: `(replica, sequence number)` — never minted twice. -/
abbrev Tag (R : Nat) := Fin R × Nat

/-- An element paired with the tag of the add that produced it.
    Lex-ordered, so the sorted-list machinery of Chapter 5 applies
    unchanged. -/
abbrev ETag (R : Nat) := Nat × Tag R

end ORSet

/-- Observed-remove set: tagged adds, tombstoned tags, and a per-replica
    tag counter (a G-Counter — Chapter 3 pays rent again). -/
structure ORSet (R : Nat) where
  adds  : SList (ORSet.ETag R)
  tombs : SList (ORSet.ETag R)
  ctr   : GCounter R

namespace ORSet

open Order.PartialOrder Order.BoundedJoinSemilattice

variable {R : Nat}

/- The semilattice is componentwise — three known lattices glued. -/

instance : LE (ORSet R) :=
  ⟨fun s t => s.adds ⊑ t.adds ∧ s.tombs ⊑ t.tombs ∧ s.ctr ⊑ t.ctr⟩

instance : Order.PartialOrder (ORSet R) where
  le_refl s := ⟨le_refl s.adds, le_refl s.tombs, le_refl s.ctr⟩
  le_antisymm {s t} h₁ h₂ := by
    have e₁ := le_antisymm h₁.1 h₂.1
    have e₂ := le_antisymm h₁.2.1 h₂.2.1
    have e₃ := le_antisymm h₁.2.2 h₂.2.2
    cases s; cases t
    simp_all
  le_trans h₁ h₂ :=
    ⟨le_trans h₁.1 h₂.1, le_trans h₁.2.1 h₂.2.1, le_trans h₁.2.2 h₂.2.2⟩

instance : BoundedJoinSemilattice (ORSet R) where
  sup s t := ⟨s.adds ⊔ t.adds, s.tombs ⊔ t.tombs, s.ctr ⊔ t.ctr⟩
  bot := ⟨⊥, ⊥, ⊥⟩
  le_sup_left s t :=
    ⟨le_sup_left s.adds t.adds, le_sup_left s.tombs t.tombs,
     le_sup_left s.ctr t.ctr⟩
  le_sup_right s t :=
    ⟨le_sup_right s.adds t.adds, le_sup_right s.tombs t.tombs,
     le_sup_right s.ctr t.ctr⟩
  sup_le s t u h₁ h₂ :=
    ⟨sup_le s.adds t.adds u.adds h₁.1 h₂.1,
     sup_le s.tombs t.tombs u.tombs h₁.2.1 h₂.2.1,
     sup_le s.ctr t.ctr u.ctr h₁.2.2 h₂.2.2⟩
  bot_le s := ⟨bot_le s.adds, bot_le s.tombs, bot_le s.ctr⟩

@[simp] theorem sup_adds (s t : ORSet R) : (s ⊔ t).adds = s.adds ⊔ t.adds := rfl
@[simp] theorem sup_tombs (s t : ORSet R) : (s ⊔ t).tombs = s.tombs ⊔ t.tombs := rfl
@[simp] theorem sup_ctr (s t : ORSet R) : (s ⊔ t).ctr = s.ctr ⊔ t.ctr := rfl

/-- Add at replica `i`: mint the fresh tag `(i, ctr i)`, record the
    tagged add, and burn the tag by bumping the counter. -/
def add (i : Fin R) (e : Nat) (s : ORSet R) : ORSet R :=
  { adds  := SList.insert (e, i, s.ctr i) s.adds
    tombs := s.tombs
    ctr   := GCounter.increment i s.ctr }

/-- Remove: tombstone every *observed* tag for `e` — and only those. -/
def remove (e : Nat) (s : ORSet R) : ORSet R :=
  { adds  := s.adds
    tombs := s.tombs ⊔ SList.filter (fun p => p.1 == e) s.adds
    ctr   := s.ctr }

/-- Membership: some tagged add of `e` survives untombstoned. -/
def mem (e : Nat) (s : ORSet R) : Prop :=
  ∃ t : Tag R, (e, t) ∈ s.adds ∧ ¬ (e, t) ∈ s.tombs

theorem mem_iff_bex {e : Nat} {s : ORSet R} :
    mem e s ↔ ∃ p ∈ s.adds.val, p.1 = e ∧ ¬ p ∈ s.tombs := by
  constructor
  · intro ⟨t, hin, hnt⟩
    exact ⟨(e, t), hin, rfl, hnt⟩
  · intro ⟨p, hin, he, hnt⟩
    obtain ⟨e', t⟩ := p
    cases he
    exact ⟨t, hin, hnt⟩

instance {e : Nat} {s : ORSet R} : Decidable (mem e s) :=
  decidable_of_iff _ mem_iff_bex.symm

theorem add_inflationary (i : Fin R) (e : Nat) :
    Order.Inflationary (add i e) :=
  fun s => ⟨fun _ hx => SList.mem_insert.mpr (Or.inr hx),
            le_refl s.tombs,
            GCounter.increment_inflationary i s.ctr⟩

theorem remove_inflationary (e : Nat) :
    Order.Inflationary (remove (R := R) e) :=
  fun s => ⟨le_refl s.adds,
            le_sup_left s.tombs _,
            le_refl s.ctr⟩

/- ── The freshness invariant ─────────────────────────────────
   (i) tombstones only ever cover *observed* adds, and
   (ii) the counter dominates every locally recorded tag.
   Preserved by add, remove, and merge — the reader's first
   inductive-invariant proof, the style Chapters 8–9 run on. -/

structure Wf (s : ORSet R) : Prop where
  tombs_sub : ∀ p ∈ s.tombs, p ∈ s.adds
  ctr_dom   : ∀ p ∈ s.adds, p.2.2 < s.ctr p.2.1

theorem wf_bot : Wf (⊥ : ORSet R) where
  tombs_sub _ hp := absurd hp (SList.not_mem_empty _)
  ctr_dom _ hp := absurd hp (SList.not_mem_empty _)

theorem wf_add {s : ORSet R} (h : Wf s) (i : Fin R) (e : Nat) :
    Wf (add i e s) where
  tombs_sub p hp :=
    SList.mem_insert.mpr (Or.inr (h.tombs_sub p hp))
  ctr_dom p hp := by
    cases SList.mem_insert.mp hp with
    | inl he =>
        subst he
        simp [add, GCounter.increment]
    | inr hm =>
        have hd := h.ctr_dom p hm
        show p.2.2 < GCounter.increment i s.ctr p.2.1
        by_cases hpi : p.2.1 = i
        · rw [hpi] at hd ⊢
          simp [GCounter.increment]
          omega
        · simp [GCounter.increment, hpi]
          exact hd

theorem wf_remove {s : ORSet R} (h : Wf s) (e : Nat) :
    Wf (remove e s) where
  tombs_sub p hp := by
    cases SList.mem_union.mp hp with
    | inl ht => exact h.tombs_sub p ht
    | inr hf => exact (SList.mem_filter.mp hf).1
  ctr_dom := h.ctr_dom

theorem wf_merge {s t : ORSet R} (hs : Wf s) (ht : Wf t) :
    Wf (s ⊔ t) where
  tombs_sub p hp := by
    rw [sup_tombs] at hp
    rw [sup_adds]
    cases SList.mem_union.mp hp with
    | inl h => exact SList.mem_union.mpr (Or.inl (hs.tombs_sub p h))
    | inr h => exact SList.mem_union.mpr (Or.inr (ht.tombs_sub p h))
  ctr_dom p hp := by
    rw [sup_adds] at hp
    show p.2.2 < Nat.max (s.ctr p.2.1) (t.ctr p.2.1)
    cases SList.mem_union.mp hp with
    | inl h => exact Nat.lt_of_lt_of_le (hs.ctr_dom p h) (Nat.le_max_left _ _)
    | inr h => exact Nat.lt_of_lt_of_le (ht.ctr_dom p h) (Nat.le_max_right _ _)

/-- A replica's view of *someone else's* counter never overtakes the
    owner's own view — and merging peers preserves that. This is why
    the freshness hypothesis of `addWins` holds along real executions. -/
theorem ctr_view_merge {sA sB sC : ORSet R} (i : Fin R)
    (hB : sB.ctr i ≤ sA.ctr i) (hC : sC.ctr i ≤ sA.ctr i) :
    (sB ⊔ sC).ctr i ≤ sA.ctr i := by
  show Nat.max (sB.ctr i) (sC.ctr i) ≤ sA.ctr i
  exact Nat.max_le.mpr ⟨hB, hC⟩

/-- **Add wins.** Replica `i` adds `e` to its state `sA`; concurrently a
    peer removes `e` from its state `sB`. If `sB`'s view of `i`'s counter
    is no fresher than `i`'s own (true in every real execution), then
    after merging, `e` is a member: no tombstone can cover a tag that
    had not been minted when the remove happened. -/
theorem addWins {sA sB : ORSet R} (i : Fin R) (e : Nat)
    (hA : Wf sA) (hB : Wf sB)
    (hfresh : sB.ctr i ≤ sA.ctr i) :
    mem e (add i e sA ⊔ remove e sB) := by
  refine ⟨(i, sA.ctr i), ?_, ?_⟩
  · -- the fresh tagged add is in the merged adds
    rw [sup_adds]
    exact SList.mem_union.mpr (Or.inl (SList.mem_insert.mpr (Or.inl rfl)))
  · -- and no tombstone covers it
    intro htomb
    rw [sup_tombs] at htomb
    cases SList.mem_union.mp htomb with
    | inl hin =>
        -- a tombstone at A itself: then A had recorded tag (i, ctr i),
        -- contradicting counter dominance
        have := hA.ctr_dom _ (hA.tombs_sub _ hin)
        exact Nat.lt_irrefl _ this
    | inr hin =>
        -- a tombstone from B's remove: B had observed tag (i, ctr A i),
        -- contradicting B's view being no fresher than A's own
        have hadds : (e, i, sA.ctr i) ∈ sB.adds := by
          cases SList.mem_union.mp hin with
          | inl ht => exact hB.tombs_sub _ ht
          | inr hf => exact (SList.mem_filter.mp hf).1
        have hlt := hB.ctr_dom _ hadds
        simp at hlt
        omega

/-- Refuted: "tags can be reused". An add that recycles a tag can be
    deleted by a remove that happened *before* it. -/
def badAdd (i : Fin R) (k : Nat) (e : Nat) (s : ORSet R) : ORSet R :=
  { s with adds := SList.insert (e, i, k) s.adds }

theorem tag_reuse_bites :
    -- A adds 1 with tag (0,0); B (having seen it) removes 1;
    -- A "re-adds" 1 reusing tag (0,0); the merge has no member 1:
    -- B's old remove killed A's later add.
    let s₁ : ORSet 2 := badAdd 0 0 1 ⊥
    let atB := remove 1 s₁
    let atA := badAdd 0 0 1 s₁
    ¬ mem 1 (atA ⊔ atB) := by decide

/-- Interlude: the add/remove/re-add trace that broke the 2P-Set,
    now passing, plus a duplicated-delivery run. -/
def interlude : List (String × Bool) :=
  let s₀ : ORSet 2 := ⊥
  let s₁ := add 0 1 s₀            -- A adds 1 (tag (0,0))
  let s₂ := remove 1 s₁           -- A removes 1
  let s₃ := add 0 1 s₂            -- A re-adds 1 (fresh tag (0,1))
  let atB := remove 1 s₁          -- concurrently, B (having seen s₁) removes 1
  [ ("1 ∈ s₁ (added)", decide (mem 1 s₁)),
    ("1 ∈ s₂ (removed)", decide (mem 1 s₂)),
    ("1 ∈ s₃ (re-added!)", decide (mem 1 s₃)),
    ("1 ∈ s₃ ⊔ B's remove (add wins)", decide (mem 1 (s₃ ⊔ atB))),
    ("1 ∈ (s₃ ⊔ atB) ⊔ atB (duplicate delivery)",
      decide (mem 1 ((s₃ ⊔ atB) ⊔ atB))) ]

#eval interlude

/-- Tombstones never shrink: garbage is real (Exercise fodder; see
    Chapter 13 for the coordination irony). -/
theorem tombs_monotone {s t : ORSet R} (h : s ⊑ t) :
    s.tombs ⊑ t.tombs := h.2.1

end ORSet

/- ============================================================
   Crdt.Perm and Crdt.MSet — Chapter 8: Multisets, Folds, and
   the Main Theorem.
   What a replica has received is a *multiset* of updates: order
   must not matter. A multiset is a quotient of lists by
   permutation — the reader's first quotient type.
   ============================================================ -/

/-- Permutation of lists, hand-rolled (the stdlib has `List.Perm`;
    series rule: understand every axiom, so we build our own). -/
inductive Perm {α : Type} : List α → List α → Prop where
  | nil : Perm [] []
  | cons (x : α) {l₁ l₂ : List α} (h : Perm l₁ l₂) : Perm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : Perm (x :: y :: l) (y :: x :: l)
  | trans {l₁ l₂ l₃ : List α} (h₁ : Perm l₁ l₂) (h₂ : Perm l₂ l₃) :
      Perm l₁ l₃

namespace Perm

variable {α : Type}

theorem refl : ∀ (l : List α), Perm l l
  | [] => .nil
  | x :: t => .cons x (refl t)

theorem symm {l₁ l₂ : List α} (h : Perm l₁ l₂) : Perm l₂ l₁ := by
  induction h with
  | nil => exact .nil
  | cons x _ ih => exact .cons x ih
  | swap x y l => exact .swap y x l
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

/-- Permutation preserves membership (so it preserves the *set* of
    updates — only arrangement is forgotten). -/
theorem mem_iff {l₁ l₂ : List α} (h : Perm l₁ l₂) (x : α) :
    x ∈ l₁ ↔ x ∈ l₂ := by
  induction h with
  | nil => exact Iff.rfl
  | cons y _ ih => simp [List.mem_cons, ih]
  | swap y z l =>
      simp only [List.mem_cons]
      constructor
      · intro h
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · intro h
        rcases h with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Perm

/-- Lists-up-to-permutation form a setoid; `≈` now means `Perm`. -/
instance permSetoid (α : Type) : Setoid (List α) where
  r := Perm
  iseqv := ⟨Perm.refl, Perm.symm, Perm.trans⟩

/- ── Warm-up: the integers as a quotient of ℕ × ℕ ─────────────
   Every quotient move the multiset needs — `Quotient.mk`, `lift`,
   `sound`, `ind` — in the smallest interesting example first. -/

namespace IntPairs

/-- A "pre-integer": the pair `(p, n)` intends the difference `p − n`. -/
def PreInt := Nat × Nat

/-- Same intended difference (stated without subtraction). -/
def eqv (a b : PreInt) : Prop := a.1 + b.2 = b.1 + a.2

instance preIntSetoid : Setoid PreInt where
  r := eqv
  iseqv := {
    refl := fun _ => rfl
    symm := fun {a b} h => by
      have h' : a.1 + b.2 = b.1 + a.2 := h
      show b.1 + a.2 = a.1 + b.2
      omega
    trans := fun {a b c} h₁ h₂ => by
      have h₁' : a.1 + b.2 = b.1 + a.2 := h₁
      have h₂' : b.1 + c.2 = c.1 + b.2 := h₂
      show a.1 + c.2 = c.1 + a.2
      omega }

/-- The integers: pre-integers, with intent made real by quotienting. -/
def MyInt := Quotient preIntSetoid

def mk (p n : Nat) : MyInt := Quotient.mk preIntSetoid (p, n)

/-- `(3,5)` and `(10,12)` are *different pairs* but the *same* `MyInt`:
    equality of quotients is `Quotient.sound` of relatedness. -/
example : mk 3 5 = mk 10 12 := Quotient.sound (rfl : 3 + 12 = 10 + 5)

/-- To define a function out of a quotient, define it on representatives
    and *prove it respects the relation* — that proof is the toll
    `Quotient.lift` charges. -/
def toInt : MyInt → Int :=
  Quotient.lift (fun a : PreInt => (a.1 : Int) - a.2)
    (fun a b h => by
      have h' : a.1 + b.2 = b.1 + a.2 := h
      show (a.1 : Int) - a.2 = (b.1 : Int) - b.2
      omega)

def neg : MyInt → MyInt :=
  Quotient.lift (fun a : PreInt => mk a.2 a.1)
    (fun a b h => Quotient.sound (by
      have h' : a.1 + b.2 = b.1 + a.2 := h
      show a.2 + b.1 = b.2 + a.1
      omega))

/-- To prove things about all quotient values, `Quotient.ind` hands you
    a representative. -/
theorem toInt_neg (q : MyInt) : toInt (neg q) = - toInt q := by
  induction q using Quotient.ind with
  | _ a =>
      show (a.2 : Int) - a.1 = -((a.1 : Int) - a.2)
      omega

#eval toInt (mk 3 5)              -- -2
#eval toInt (neg (mk 3 5))        -- 2

end IntPairs

/-- A finite multiset: lists up to permutation. -/
def MSet (σ : Type) : Type := Quotient (permSetoid σ)

namespace MSet

def ofList {σ : Type} (l : List σ) : MSet σ :=
  Quotient.mk (permSetoid σ) l

/-- Different lists, same multiset. -/
example : ofList [1, 2] = ofList [2, 1] :=
  Quotient.sound (.swap 1 2 [])

end MSet

/- ============================================================
   Crdt.SEC — Chapter 8 continued: the main theorem.
   ============================================================ -/

namespace SEC

open Order.PartialOrder Order.BoundedJoinSemilattice

variable {σ : Type} [BoundedJoinSemilattice σ]

/-- A replica's state is the join of everything it has received,
    folded starting from ⊥. -/
def foldJoin (l : List σ) : σ := l.foldl (· ⊔ ·) ⊥

/-- The same fold from an arbitrary seed. Generalizing the accumulator
    is what makes every lemma below go through by induction. -/
def foldJoinFrom (a : σ) (l : List σ) : σ := l.foldl (· ⊔ ·) a

theorem foldJoin_def (l : List σ) : foldJoin l = foldJoinFrom ⊥ l := rfl

/-- The seed only grows. -/
theorem le_foldJoinFrom (l : List σ) : ∀ (a : σ), a ⊑ foldJoinFrom a l := by
  induction l with
  | nil => intro a; exact le_refl a
  | cons x t ih => intro a; exact le_trans (le_sup_left a x) (ih (a ⊔ x))

/-- Every delivered update is below the fold: the fold is an upper
    bound of the list. -/
theorem le_foldJoinFrom_of_mem {x : σ} {l : List σ} (hx : x ∈ l) :
    ∀ (a : σ), x ⊑ foldJoinFrom a l := by
  induction l with
  | nil => cases hx
  | cons y t ih =>
      intro a
      cases List.mem_cons.mp hx with
      | inl he =>
          subst he
          exact le_trans (le_sup_right a x) (le_foldJoinFrom t (a ⊔ x))
      | inr hm => exact ih hm (a ⊔ y)

/-- ... and the *least* one over the seed: fold = lub of seed and list. -/
theorem foldJoinFrom_le {c : σ} {l : List σ} : ∀ {a : σ},
    a ⊑ c → (∀ x ∈ l, x ⊑ c) → foldJoinFrom a l ⊑ c := by
  induction l with
  | nil => intro a ha _; exact ha
  | cons y t ih =>
      intro a ha hl
      exact ih (sup_le a y c ha (hl y List.mem_cons_self))
        (fun x hx => hl x (List.mem_cons_of_mem y hx))

/-- The seed pulls out of the fold as one more join. -/
theorem foldJoinFrom_eq_sup (a : σ) (l : List σ) :
    foldJoinFrom a l = a ⊔ foldJoin l := by
  apply le_antisymm
  · apply foldJoinFrom_le
    · exact le_sup_left a (foldJoin l)
    · intro x hx
      exact le_trans (le_foldJoinFrom_of_mem hx ⊥) (le_sup_right a (foldJoin l))
  · apply sup_le
    · exact le_foldJoinFrom l a
    · exact foldJoinFrom_le (bot_le (foldJoinFrom a l))
        (fun x hx => le_foldJoinFrom_of_mem hx a)

/-- One more delivery is one more join. -/
theorem foldJoin_cons (x : σ) (l : List σ) :
    foldJoin (x :: l) = x ⊔ foldJoin l := by
  show foldJoinFrom (⊥ ⊔ x) l = x ⊔ foldJoin l
  rw [sup_bot_left, foldJoinFrom_eq_sup]

/-- Batching is free: delivering a peer's whole log at once is the same
    as joining with the peer's state. Gossip is join-propagation. -/
theorem foldJoin_append (l₁ l₂ : List σ) :
    foldJoin (l₁ ++ l₂) = foldJoin l₁ ⊔ foldJoin l₂ := by
  show (l₁ ++ l₂).foldl (· ⊔ ·) ⊥ = foldJoin l₁ ⊔ foldJoin l₂
  rw [List.foldl_append]
  exact foldJoinFrom_eq_sup (foldJoin l₁) l₂

/-- **The keystone.** Same members — any order, any multiplicities —
    same fold. Not proved by list surgery: both folds are least upper
    bounds of the same set, so antisymmetry finishes it. -/
theorem foldJoin_eq_of_same_mems {l₁ l₂ : List σ}
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : foldJoin l₁ = foldJoin l₂ := by
  apply le_antisymm
  · exact foldJoinFrom_le (bot_le _)
      (fun x hx => le_foldJoinFrom_of_mem ((h x).mp hx) ⊥)
  · exact foldJoinFrom_le (bot_le _)
      (fun x hx => le_foldJoinFrom_of_mem ((h x).mpr hx) ⊥)

/-- Reordering is absorbed (direct proof by induction on the
    permutation — the shape `Quotient.lift` will ask for). -/
theorem foldJoinFrom_perm {l₁ l₂ : List σ} (h : Perm l₁ l₂) :
    ∀ (a : σ), foldJoinFrom a l₁ = foldJoinFrom a l₂ := by
  induction h with
  | nil => intro _; rfl
  | cons x _ ih => intro a; exact ih (a ⊔ x)
  | swap x y l =>
      intro a
      show foldJoinFrom (a ⊔ x ⊔ y) l = foldJoinFrom (a ⊔ y ⊔ x) l
      rw [sup_assoc, sup_assoc, sup_comm x y]
  | trans _ _ ih₁ ih₂ => intro a; exact (ih₁ a).trans (ih₂ a)

theorem foldJoin_perm {l₁ l₂ : List σ} (h : Perm l₁ l₂) :
    foldJoin l₁ = foldJoin l₂ :=
  foldJoinFrom_perm h ⊥

/-- Duplication is absorbed: idempotence, on duty. -/
theorem foldJoin_dup (x : σ) (l : List σ) :
    foldJoin (x :: x :: l) = foldJoin (x :: l) := by
  show foldJoinFrom (⊥ ⊔ x ⊔ x) l = foldJoinFrom (⊥ ⊔ x) l
  rw [sup_assoc, sup_idem]

/-- Refuted: "commutativity and associativity alone suffice".
    Drop idempotence — `(Nat, +)` is commutative and associative —
    and one duplicated delivery double-counts. -/
theorem comm_assoc_not_enough :
    [1].foldl (· + ·) 0 ≠ [1, 1].foldl (· + ·) 0 := by decide

end SEC

namespace MSet

open SEC

/-- The fold descends to multisets: `Quotient.lift` demands exactly
    `foldJoin_perm`, and Chapter 8 has already paid it. -/
def foldJoin {σ : Type} [BoundedJoinSemilattice σ] : MSet σ → σ :=
  Quotient.lift SEC.foldJoin (fun _ _ h => SEC.foldJoin_perm h)

theorem foldJoin_mk {σ : Type} [BoundedJoinSemilattice σ] (l : List σ) :
    foldJoin (ofList l) = SEC.foldJoin l := rfl

end MSet

namespace SEC

open Order.PartialOrder Order.BoundedJoinSemilattice

variable {σ : Type} [BoundedJoinSemilattice σ]

/-- A replica, abstracted to what it has received. -/
structure Replica (σ : Type) [BoundedJoinSemilattice σ] where
  delivered : List σ

def Replica.state (r : Replica σ) : σ := foldJoin r.delivered

/-- Two replicas have received the same *set* of updates — in any
    order, with any multiplicities ≥ 1. -/
def SameDeliveredSet (r₁ r₂ : Replica σ) : Prop :=
  ∀ x, x ∈ r₁.delivered ↔ x ∈ r₂.delivered

/-- **Strong eventual consistency, state-based.** Replicas that have
    heard the same news hold the same state — no matter who told them,
    how often, or in what order. -/
theorem sec_state_based {r₁ r₂ : Replica σ}
    (h : SameDeliveredSet r₁ r₂) : r₁.state = r₂.state :=
  foldJoin_eq_of_same_mems h

/-- Interlude: three G-Set update streams folded in wildly different
    orders and multiplicities. -/
def interlude : List (String × List Nat) :=
  let u₁ : GSet := GSet.add 1 ⊥
  let u₂ : GSet := GSet.add 2 ⊥
  let u₃ : GSet := GSet.add 3 ⊥
  let r₁ : Replica GSet := ⟨[u₁, u₂, u₃]⟩
  let r₂ : Replica GSet := ⟨[u₃, u₁, u₂, u₂, u₁]⟩
  let r₃ : Replica GSet := ⟨[u₂, u₂, u₃, u₃, u₁, u₃]⟩
  [ ("replica 1", r₁.state.val),
    ("replica 2", r₂.state.val),
    ("replica 3", r₃.state.val) ]

#eval interlude

end SEC

/- ============================================================
   Crdt.Delivery — Chapter 9: Gossip, Duplication, and
   Reordering. The algebra meets an operational model.
   ============================================================ -/

namespace Delivery

open Order.PartialOrder Order.BoundedJoinSemilattice

variable {R : Nat} {σ : Type} [BoundedJoinSemilattice σ]

/-- A snapshot of the whole system: each replica's state, the (ghost)
    log of updates it has incorporated, and the messages in flight.
    A message carries a state and the log that produced it. -/
structure Config (R : Nat) (σ : Type) where
  states : Fin R → σ
  seen   : Fin R → List σ
  msgs   : List (Fin R × σ × List σ)

/-- The empty system. -/
def init (R : Nat) (σ : Type) [BoundedJoinSemilattice σ] : Config R σ :=
  { states := fun _ => ⊥, seen := fun _ => [], msgs := [] }

def applyUpdate (c : Config R σ) (r : Fin R) (v : σ) : Config R σ :=
  { states := fun j => if j = r then c.states j ⊔ v else c.states j
    seen   := fun j => if j = r then v :: c.seen j else c.seen j
    msgs   := c.msgs }

def applySend (c : Config R σ) (r r' : Fin R) : Config R σ :=
  { c with msgs := (r', c.states r, c.seen r) :: c.msgs }

def applyDeliver (c : Config R σ) (r : Fin R) (p : σ × List σ) : Config R σ :=
  { states := fun j => if j = r then c.states j ⊔ p.1 else c.states j
    seen   := fun j => if j = r then p.2 ++ c.seen j else c.seen j
    msgs   := c.msgs }

/-- The network's honest contract. `deliver` picks *any* in-flight
    message (reordering) and leaves it in flight (duplication); a
    message that is never picked is lost. At-least-once, unordered. -/
inductive Step : Config R σ → Config R σ → Prop where
  | update (c : Config R σ) (r : Fin R) (v : σ) :
      Step c (applyUpdate c r v)
  | send (c : Config R σ) (r r' : Fin R) :
      Step c (applySend c r r')
  | deliver (c : Config R σ) (r : Fin R) (p : σ × List σ)
      (h : (r, p) ∈ c.msgs) :
      Step c (applyDeliver c r p)

/-- Zero or more steps. -/
inductive Reachable : Config R σ → Config R σ → Prop where
  | refl (c : Config R σ) : Reachable c c
  | tail {c₁ c₂ c₃ : Config R σ} (h : Reachable c₁ c₂) (hs : Step c₂ c₃) :
      Reachable c₁ c₃

/-- The inductive invariant: every replica's state is the fold of its
    log, and every in-flight message is honest about its own. -/
def Coherent (c : Config R σ) : Prop :=
  (∀ r, c.states r = SEC.foldJoin (c.seen r)) ∧
  (∀ m ∈ c.msgs, m.2.1 = SEC.foldJoin m.2.2)

theorem coherent_init : Coherent (init R σ) :=
  ⟨fun _ => rfl, fun _ hm => absurd hm (by intro h; cases h)⟩

/-- Every step preserves coherence — one case per event. -/
theorem coherent_step {c₁ c₂ : Config R σ} (h : Step c₁ c₂)
    (hc : Coherent c₁) : Coherent c₂ := by
  cases h with
  | update r v =>
      refine ⟨fun j => ?_, hc.2⟩
      show (if j = r then c₁.states j ⊔ v else c₁.states j)
          = SEC.foldJoin (if j = r then v :: c₁.seen j else c₁.seen j)
      by_cases hj : j = r <;> simp [hj]
      · rw [hc.1 r, SEC.foldJoin_cons, Order.sup_comm]
      · exact hc.1 j
  | send r r' =>
      refine ⟨hc.1, fun m hm => ?_⟩
      cases List.mem_cons.mp hm with
      | inl he => subst he; exact hc.1 r
      | inr hm' => exact hc.2 m hm'
  | deliver r p hp =>
      refine ⟨fun j => ?_, hc.2⟩
      show (if j = r then c₁.states j ⊔ p.1 else c₁.states j)
          = SEC.foldJoin (if j = r then p.2 ++ c₁.seen j else c₁.seen j)
      by_cases hj : j = r <;> simp [hj]
      · rw [hc.1 r, SEC.foldJoin_append, hc.2 (r, p) hp, Order.sup_comm]
      · exact hc.1 j

theorem coherent_reachable {c₁ c₂ : Config R σ} (h : Reachable c₁ c₂)
    (hc : Coherent c₁) : Coherent c₂ := by
  induction h with
  | refl => exact hc
  | tail _ hs ih => exact coherent_step hs ih

/-- "Everything anyone has incorporated, everyone has" — the quiescent,
    all-delivered endpoint of an execution. -/
def AllShared (c : Config R σ) : Prop :=
  ∀ (r r' : Fin R), ∀ x ∈ c.seen r, x ∈ c.seen r'

/-- **Eventual delivery ⇒ convergence.** Along any execution from the
    empty system — updates, sends, deliveries in any order, duplicated
    and dropped at the network's whim — once every update has reached
    every replica, all replicas hold *equal* state. Chapter 8's theorem,
    now wearing an operational harness. -/
theorem converged_of_allShared {c : Config R σ}
    (hr : Reachable (init R σ) c) (h : AllShared c) :
    ∀ (r r' : Fin R), c.states r = c.states r' := by
  intro r r'
  have hc := coherent_reachable hr coherent_init
  rw [hc.1 r, hc.1 r']
  exact SEC.foldJoin_eq_of_same_mems (fun x => ⟨h r r' x, h r' r x⟩)

end Delivery

/- ── An executable anti-entropy driver ────────────────────────
   The predecessor's `runToFixpoint` ran on fuel — an IOU. Here the
   debt is paid: gossip rounds terminate because a natural-number
   measure (how many updates are still missing somewhere) strictly
   decreases. Well-founded recursion, where it *is* the lesson.     -/

namespace Delivery

variable {R : Nat} {σ : Type} [DecidableEq σ]

/-- Executable network view: the set of updates ever issued, and each
    replica's log. -/
structure Net (R : Nat) (σ : Type) where
  issued : List σ
  logs : Fin R → List σ

/-- How many issued updates replica `r` still lacks. -/
def missing (n : Net R σ) (r : Fin R) : Nat :=
  (n.issued.filter (fun u => !decide (u ∈ n.logs r))).length

/-- The termination measure: total lacks, summed over replicas. -/
def cost (n : Net R σ) : Nat :=
  (List.finRange R).foldl (fun acc r => acc + missing n r) 0

/-- Does `p` know an issued update that `q` lacks? -/
def needsFrom (n : Net R σ) (p q : Fin R) : Bool :=
  n.issued.any (fun u => decide (u ∈ n.logs p) && !decide (u ∈ n.logs q))

def allPairs (R : Nat) : List (Fin R × Fin R) :=
  (List.finRange R).flatMap (fun p => (List.finRange R).map (fun q => (p, q)))

def findPairAux (n : Net R σ) : List (Fin R × Fin R) → Option (Fin R × Fin R)
  | [] => none
  | pq :: rest =>
      if needsFrom n pq.1 pq.2 then some pq else findPairAux n rest

/-- Scan for a productive exchange; `none` means quiescent. -/
def findPair (n : Net R σ) : Option (Fin R × Fin R) :=
  findPairAux n (allPairs R)

/-- One anti-entropy exchange: `q` merges `p`'s whole log.
    (Batching is free — Chapter 8's `foldJoin_append`.) -/
def exchange (p q : Fin R) (n : Net R σ) : Net R σ :=
  { n with logs := fun r => if r = q then n.logs p ++ n.logs r else n.logs r }

theorem findPairAux_spec {n : Net R σ} :
    ∀ {l : List (Fin R × Fin R)} {pq : Fin R × Fin R},
      findPairAux n l = some pq → needsFrom n pq.1 pq.2 = true
  | [], _, h => by cases h
  | x :: rest, pq, h => by
      by_cases hx : needsFrom n x.1 x.2 = true
      · simp [findPairAux, hx] at h
        subst h
        exact hx
      · simp [findPairAux, hx] at h
        exact findPairAux_spec h

theorem findPairAux_none {n : Net R σ} :
    ∀ {l : List (Fin R × Fin R)}, findPairAux n l = none →
      ∀ pq ∈ l, needsFrom n pq.1 pq.2 = false
  | [], _, _, hpq => absurd hpq (by intro h; cases h)
  | x :: rest, h, pq, hpq => by
      by_cases hx : needsFrom n x.1 x.2 = true
      · simp [findPairAux, hx] at h
      · simp [findPairAux, hx] at h
        cases List.mem_cons.mp hpq with
        | inl he =>
            subst he
            exact Bool.eq_false_iff.mpr hx
        | inr hm => exact findPairAux_none h pq hm

theorem mem_allPairs {R : Nat} (p q : Fin R) : (p, q) ∈ allPairs R := by
  unfold allPairs
  rw [List.mem_flatMap]
  exact ⟨p, List.mem_finRange p, List.mem_map.mpr ⟨q, List.mem_finRange q, rfl⟩⟩

theorem needsFrom_iff {n : Net R σ} {p q : Fin R} :
    needsFrom n p q = true
      ↔ ∃ u ∈ n.issued, u ∈ n.logs p ∧ ¬ u ∈ n.logs q := by
  simp [needsFrom, List.any_eq_true]

/- Filter arithmetic for the measure. -/

theorem filter_length_mono {α : Type} {p q : α → Bool}
    (h : ∀ x, p x = true → q x = true) :
    ∀ (l : List α), (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl 0
  | x :: t => by
      by_cases hp : p x = true
      · rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos (h x hp)]
        exact Nat.succ_le_succ (filter_length_mono h t)
      · rw [List.filter_cons_of_neg hp]
        by_cases hq : q x = true
        · rw [List.filter_cons_of_pos hq]
          exact Nat.le_succ_of_le (filter_length_mono h t)
        · rw [List.filter_cons_of_neg hq]
          exact filter_length_mono h t

theorem filter_length_strict {α : Type} {p q : α → Bool}
    (himp : ∀ x, p x = true → q x = true) :
    ∀ {l : List α} {u : α}, u ∈ l → q u = true → p u = false →
      (l.filter p).length < (l.filter q).length := by
  intro l
  induction l with
  | nil => intro u hu _ _; cases hu
  | cons x t ih =>
      intro u hu hq hp
      cases List.mem_cons.mp hu with
      | inl he =>
          subst he
          rw [List.filter_cons_of_neg (by simp [hp]), List.filter_cons_of_pos hq]
          exact Nat.lt_succ_of_le (filter_length_mono himp t)
      | inr hm =>
          by_cases hpx : p x = true
          · rw [List.filter_cons_of_pos hpx, List.filter_cons_of_pos (himp x hpx)]
            exact Nat.succ_lt_succ (ih hm hq hp)
          · rw [List.filter_cons_of_neg hpx]
            by_cases hqx : q x = true
            · rw [List.filter_cons_of_pos hqx]
              exact Nat.lt_succ_of_le (Nat.le_of_lt (ih hm hq hp))
            · rw [List.filter_cons_of_neg hqx]
              exact ih hm hq hp

/- Sum arithmetic for the measure (seed-generalized, as always). -/

theorem foldl_add_lt_of_seed {ι : Type} {f g : ι → Nat}
    (h : ∀ j, f j ≤ g j) :
    ∀ (l : List ι) {a b : Nat}, a < b →
      l.foldl (fun acc j => acc + f j) a < l.foldl (fun acc j => acc + g j) b
  | [], _, _, hab => hab
  | j :: t, a, b, hab => by
      rw [List.foldl_cons, List.foldl_cons]
      exact foldl_add_lt_of_seed h t (by have := h j; omega)

theorem foldl_add_strict (n : Nat) :
    ∀ (f g : Fin n → Nat) (i : Fin n), (∀ j, f j ≤ g j) → f i < g i →
      ∀ {a b : Nat}, a ≤ b →
      (List.finRange n).foldl (fun acc j => acc + f j) a
        < (List.finRange n).foldl (fun acc j => acc + g j) b := by
  induction n with
  | zero => intro _ _ i; exact i.elim0
  | succ n ih =>
      intro f g i hle hlt a b hab
      rw [List.finRange_succ, List.foldl_cons, List.foldl_cons,
          List.foldl_map, List.foldl_map]
      cases i using Fin.cases with
      | zero =>
          exact foldl_add_lt_of_seed (fun (j : Fin n) => hle j.succ) _
            (by have := hlt; omega)
      | succ i' =>
          exact ih (fun (j : Fin n) => f j.succ) (fun (j : Fin n) => g j.succ) i'
            (fun j => hle j.succ) hlt (by have := hle 0; omega)

/-- After an exchange, nobody lacks more than before. -/
theorem missing_exchange_le (n : Net R σ) (p q r : Fin R) :
    missing (exchange p q n) r ≤ missing n r := by
  unfold missing exchange
  by_cases hr : r = q
  · subst hr
    apply filter_length_mono
    intro x hx
    simp at hx ⊢
    exact fun hxq => (hx.2 hxq).elim
  · simp only [if_neg hr]
    exact Nat.le_refl _

/-- ... and the receiver of a productive exchange lacks strictly less. -/
theorem missing_exchange_lt {n : Net R σ} {p q : Fin R} {u : σ}
    (hu : u ∈ n.issued) (hup : u ∈ n.logs p) (huq : ¬ u ∈ n.logs q) :
    missing (exchange p q n) q < missing n q := by
  unfold missing exchange
  refine filter_length_strict ?_ hu ?_ ?_
  · intro x hx
    simp at hx ⊢
    exact hx.2
  · simp [huq]
  · simp [List.mem_append, hup]

/-- A productive exchange strictly shrinks the measure. -/
theorem cost_exchange_lt {n : Net R σ} {p q : Fin R}
    (h : needsFrom n p q = true) : cost (exchange p q n) < cost n := by
  obtain ⟨u, hu, hup, huq⟩ := needsFrom_iff.mp h
  unfold cost
  exact foldl_add_strict R _ _ q (missing_exchange_le n p q)
    (missing_exchange_lt hu hup huq) (Nat.le_refl 0)

/-- **The driver.** Exchange while a productive pair exists. Lean
    accepts the recursion because `cost` strictly decreases — the
    predecessor's fuel, paid off. -/
def gossipUntilQuiescent (n : Net R σ) : Net R σ :=
  match _h : findPair n with
  | none => n
  | some pq => gossipUntilQuiescent (exchange pq.1 pq.2 n)
termination_by cost n
decreasing_by
  exact cost_exchange_lt (findPairAux_spec _h)

/-- Quiescence means fully shared: every issued update known anywhere
    is known everywhere. -/
theorem quiescent_shares {n : Net R σ} (h : findPair n = none) :
    ∀ (p q : Fin R), ∀ u ∈ n.issued, u ∈ n.logs p → u ∈ n.logs q := by
  intro p q u hu hup
  by_cases huq : u ∈ n.logs q
  · exact huq
  · exfalso
    have hfalse := findPairAux_none h (p, q) (mem_allPairs p q)
    have htrue : needsFrom n p q = true := needsFrom_iff.mpr ⟨u, hu, hup, huq⟩
    rw [htrue] at hfalse
    cases hfalse

/- ── Interlude: an adversarial network, simulated ────────────
   A seeded generator drops, duplicates, and reorders exchanges;
   the verified driver then finishes the anti-entropy. Different
   seeds, same final states.                                    -/

/-- A linear congruential generator: cheap, deterministic chaos. -/
def lcgNext (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- Four replicas; each initially knows only its own updates. -/
def demoNet : Net 4 GSet :=
  let u (k : Nat) : GSet := GSet.add k ⊥
  { issued := [u 1, u 2, u 3, u 4, u 10, u 20]
    logs := fun r =>
      if r = 0 then [u 1, u 10]
      else if r = 1 then [u 2, u 20]
      else if r = 2 then [u 3]
      else [u 4] }

/-- `fuel` random exchange attempts: some dropped, some duplicated,
    directions and targets scrambled by the seed. -/
def randomGossip : Nat → Nat → Net 4 GSet → Net 4 GSet
  | 0, _, n => n
  | fuel + 1, seed, n =>
      let s₁ := lcgNext seed
      let s₂ := lcgNext s₁
      let s₃ := lcgNext s₂
      let p : Fin 4 := ⟨s₁ % 4, Nat.mod_lt _ (by omega)⟩
      let q : Fin 4 := ⟨s₂ % 4, Nat.mod_lt _ (by omega)⟩
      let n₁ := if s₃ % 3 = 0 then n else exchange p q n      -- drop 1 in 3
      let n₂ := if s₃ % 5 = 0 then exchange p q n₁ else n₁    -- duplicate 1 in 5
      randomGossip fuel s₃ n₂

def renderNet (n : Net 4 GSet) : List (List Nat) :=
  (List.finRange 4).map (fun r => (SEC.foldJoin (n.logs r)).val)

/-- Chaos first, verified anti-entropy after: for any seed, the driver
    quiesces and all replicas agree. -/
def simulate (seed : Nat) : List (List Nat) × List (List Nat) :=
  let chaotic := randomGossip 12 seed demoNet
  (renderNet chaotic, renderNet (gossipUntilQuiescent chaotic))

#eval simulate 1
#eval simulate 42
#eval simulate 2026

end Delivery

/- ============================================================
   Crdt.VV — Chapter 10: Time Without Clocks
   The version vector is *literally* the G-Counter carrier with the
   same pointwise-max merge — shared code, new reading: `v ⊑ w`
   means "w has seen everything v has seen". A CRDT about CRDTs.
   ============================================================ -/

namespace GCounter

/-- The information order on `Fin R → Nat` is decidable — needed to
    `decide` concurrency facts in Chapter 10. -/
instance {R : Nat} {g h : GCounter R} : Decidable (g ⊑ h) :=
  @Nat.decidableForallFin R (fun i => g i ≤ h i) (fun i => Nat.decLe (g i) (h i))

end GCounter

/-- A version vector: how many events of each replica have been seen. -/
abbrev VV (R : Nat) := GCounter R

namespace VV

open Order.PartialOrder Order.BoundedJoinSemilattice

variable {R : Nat}

/-- Replica `i` performs an event: tick its own entry.
    (`tick` *is* `increment`; the meaning changed, not the code.) -/
def tick (i : Fin R) (v : VV R) : VV R := GCounter.increment i v

theorem tick_inflationary (i : Fin R) : Order.Inflationary (tick (R := R) i) :=
  GCounter.increment_inflationary i

/-- Causal order: `v` happened before `w` when `w` has seen everything
    `v` has, and more. -/
def happensBefore (v w : VV R) : Prop := v ⊑ w ∧ v ≠ w

/-- Neither saw the other: genuinely concurrent. -/
def Concurrent (v w : VV R) : Prop := ¬ v ⊑ w ∧ ¬ w ⊑ v

instance {v w : VV R} : Decidable (Concurrent v w) :=
  inferInstanceAs (Decidable (¬ _ ∧ ¬ _))

theorem vv_le_iff {v w : VV R} : v ⊑ w ↔ ∀ i, v i ≤ w i := Iff.rfl

theorem happensBefore_irrefl (v : VV R) : ¬ happensBefore v v :=
  fun h => h.2 rfl

theorem happensBefore_trans {u v w : VV R}
    (h₁ : happensBefore u v) (h₂ : happensBefore v w) :
    happensBefore u w := by
  refine ⟨le_trans h₁.1 h₂.1, fun he => ?_⟩
  subst he
  exact h₂.2 (le_antisymm h₂.1 h₁.1)

theorem concurrent_symm {v w : VV R} (h : Concurrent v w) :
    Concurrent w v := ⟨h.2, h.1⟩

theorem concurrent_irrefl (v : VV R) : ¬ Concurrent v v :=
  fun h => h.1 (le_refl v)

/-- Refuted: "version vectors totally order events". Two ticks at
    different replicas are comparable in neither direction. Concurrency
    is not a failure to know; it is a fact about the world. -/
theorem ticks_concurrent :
    Concurrent (tick 0 (⊥ : VV 2)) (tick 1 (⊥ : VV 2)) := by decide

/-- Merging version vectors is joining causal histories. -/
theorem merge_seen_left (v w : VV R) : v ⊑ v ⊔ w := le_sup_left v w

/-- Causal delivery: replica `recv` may apply the message stamped `s`
    from replica `i` when it is the very next event of `i` and every
    other dependency is already seen. -/
def deliverable (i : Fin R) (s recv : VV R) : Prop :=
  s i = recv i + 1 ∧ ∀ j, j ≠ i → s j ≤ recv j

instance {i : Fin R} {s recv : VV R} : Decidable (deliverable i s recv) :=
  @instDecidableAnd _ _ (Nat.decEq _ _) (@Nat.decidableForallFin R (fun j => j ≠ i → s j ≤ recv j)
    (fun j => match Nat.decEq j.val i.val, Nat.decLe (s j) (recv j) with
      | isTrue hv, _ => isTrue (fun hne => absurd (Fin.ext hv) hne)
      | isFalse _, isTrue hle => isTrue (fun _ => hle)
      | isFalse hv, isFalse hle => isFalse (fun h => hle (h (fun he => hv (congrArg Fin.val he))))))

/-- Interlude: causal facts, decided. -/
def interlude : List (String × Bool) :=
  let vA := tick 0 (tick 0 (⊥ : VV 3))        -- A ticked twice
  let vB := tick 1 (tick 0 (⊥ : VV 3))        -- B ticked after seeing A's first
  [ ("A's first tick ⊑ vB", decide ((GCounter.increment 0 (⊥ : VV 3)) ⊑ vB)),
    ("vA concurrent with vB", decide (Concurrent vA vB)),
    ("vA ⊔ vB dominates both", decide (vA ⊑ vA ⊔ vB ∧ vB ⊑ vA ⊔ vB)),
    ("deliverable: B's msg at A", decide (deliverable 1 vB (tick 0 (tick 0 (⊥ : VV 3))))) ]

#eval interlude

end VV

/- ============================================================
   Crdt.OpBased — Chapter 11: Op-Based CRDTs and the
   Correspondence. Ship operations, not states; the burden moves
   from the algebra to the transport.
   ============================================================ -/

namespace OpBased

open Order.PartialOrder Order.BoundedJoinSemilattice

/-- An operation-based CRDT (simplified to the fully-commutative case,
    which is all the counter needs): local state, an interpreter for
    operations, and the law that operations commute. -/
structure OpCRDT (Op σ : Type) where
  init  : σ
  apply : Op → σ → σ
  comm  : ∀ (o₁ o₂ : Op) (s : σ),
    apply o₁ (apply o₂ s) = apply o₂ (apply o₁ s)

/-- Replay a log of received operations. -/
def applyLog {Op σ : Type} (c : OpCRDT Op σ) (log : List Op) (s : σ) : σ :=
  log.foldl (fun s o => c.apply o s) s

/-- Commutativity absorbs reordering (but *nothing* absorbs
    duplication — see the refutation below). -/
theorem applyLog_perm {Op σ : Type} (c : OpCRDT Op σ) {l₁ l₂ : List Op}
    (h : Perm l₁ l₂) : ∀ s, applyLog c l₁ s = applyLog c l₂ s := by
  induction h with
  | nil => intro _; rfl
  | cons x _ ih => intro s; exact ih (c.apply x s)
  | swap x y l =>
      intro s
      show applyLog c l (c.apply y (c.apply x s))
          = applyLog c l (c.apply x (c.apply y s))
      rw [c.comm]
  | trans _ _ ih₁ ih₂ => intro s; exact (ih₁ s).trans (ih₂ s)

/-- The op-based G-Counter: an operation is "increment at replica i". -/
def opCounter (R : Nat) : OpCRDT (Fin R) (GCounter R) where
  init := ⊥
  apply := GCounter.increment
  comm o₁ o₂ s := by
    funext j
    by_cases h₁ : j = o₁ <;> by_cases h₂ : j = o₂
    · subst h₁; subst h₂; rfl
    · subst h₁; simp [GCounter.increment, h₂]
    · subst h₂; simp [GCounter.increment, h₁]
    · simp [GCounter.increment, h₁, h₂]

/-- The state each replica would *ship* after each operation. -/
def statesAlong {Op σ : Type} (c : OpCRDT Op σ) : List Op → σ → List σ
  | [], _ => []
  | o :: log, s =>
      let s' := c.apply o s
      s' :: statesAlong c log s'

/-- **The correspondence, for inflationary interpreters.** Folding the
    stream of shipped states by join replays the op log exactly: the
    state-based and op-based readings of the same history agree. -/
theorem foldJoin_statesAlong {Op σ : Type} [BoundedJoinSemilattice σ]
    (c : OpCRDT Op σ) (hinf : ∀ o, Order.Inflationary (c.apply o)) :
    ∀ (log : List Op) (s : σ),
      SEC.foldJoinFrom s (statesAlong c log s) = applyLog c log s
  | [], _ => rfl
  | o :: log, s => by
      show SEC.foldJoinFrom (s ⊔ c.apply o s) (statesAlong c log (c.apply o s))
          = applyLog c log (c.apply o s)
      rw [Order.le_iff_sup_eq.mp (hinf o s)]
      exact foldJoin_statesAlong c hinf log (c.apply o s)

/-- Instantiated at the G-Counter: op-log replay = join of state deltas. -/
theorem opGCounter_simulates (R : Nat) (log : List (Fin R)) :
    SEC.foldJoin (statesAlong (opCounter R) log ⊥)
      = applyLog (opCounter R) log ⊥ :=
  foldJoin_statesAlong (opCounter R) GCounter.increment_inflationary log ⊥

/-- Refuted: "the op-based counter tolerates at-least-once delivery".
    A duplicated increment op counts twice; the algebra has no
    idempotence to hide behind. -/
theorem op_dup_overcounts :
    GCounter.value (applyLog (opCounter 1) [0, 0] ⊥)
      ≠ GCounter.value (applyLog (opCounter 1) [0] ⊥) := by decide

/-- A tiny op-based set, to break in two ways. -/
inductive SetOp where
  | add (e : Nat)
  | remove (e : Nat)

def applySetOp : SetOp → GSet → GSet
  | .add e, s => SList.insert e s
  | .remove e, s => SList.filter (· != e) s

/-- Refuted: "op-based OR-style sets tolerate duplicated delivery".
    Add, remove, re-add; then the network redelivers the old remove:
    the re-add dies. Exactly-once (or causal tagging) is load-bearing. -/
theorem op_set_dup_kills_readd :
    let exactlyOnce := [SetOp.add 1, .remove 1, .add 1]
    let withDup := [SetOp.add 1, .remove 1, .add 1, .remove 1]
    (1 ∈ withDup.foldl (fun s o => applySetOp o s) (⊥ : GSet))
      ≠ (1 ∈ exactlyOnce.foldl (fun s o => applySetOp o s) (⊥ : GSet)) := by
  decide

/-- ... and add/remove of the same element do not commute, so op-based
    sets also need causal delivery, not just dup-suppression. -/
theorem setops_not_comm :
    applySetOp (.add 1) (applySetOp (.remove 1) (⊥ : GSet))
      ≠ applySetOp (.remove 1) (applySetOp (.add 1) (⊥ : GSet)) := by decide

end OpBased

/- ============================================================
   Crdt.Capstone — Chapter 12: A Replicated Store
   A collaborative shopping list: an OR-Set of items with a
   PN-Counter of quantities per item. Composition is free — that
   is the capstone's actual theorem.
   ============================================================ -/

namespace Capstone

open Order.PartialOrder Order.BoundedJoinSemilattice

/-- The store. Every part is a semilattice we already built, so the
    whole is one, with no new proofs: product of OR-Set and a pointwise
    map of PN-Counters. -/
abbrev Store (R : Nat) := ORSet R × (Nat → PNCounter R)

variable {R : Nat}

def addItem (i : Fin R) (item : Nat) (s : Store R) : Store R :=
  (ORSet.add i item s.1, s.2)

def removeItem (item : Nat) (s : Store R) : Store R :=
  (ORSet.remove item s.1, s.2)

def incrByAt (i : Fin R) : Nat → PNCounter R → PNCounter R
  | 0, p => p
  | k + 1, p => PNCounter.incr i (incrByAt i k p)

def addQty (i : Fin R) (item qty : Nat) (s : Store R) : Store R :=
  (s.1, fun e => if e = item then incrByAt i qty (s.2 e) else s.2 e)

def hasItem (item : Nat) (s : Store R) : Prop := ORSet.mem item s.1

instance {item : Nat} {s : Store R} : Decidable (hasItem item s) :=
  inferInstanceAs (Decidable (ORSet.mem item s.1))

def itemQty (item : Nat) (s : Store R) : Int := PNCounter.value (s.2 item)

def render (probe : List Nat) (s : Store R) : List (Nat × Bool × Int) :=
  probe.map (fun e => (e, decide (hasItem e s), itemQty e s))

/-- **The capstone theorem, in one line.** Strong eventual consistency
    for the whole composed store is `sec_state_based` instantiated at
    `Store` — the entire book is in how little there is to do here. -/
theorem sec_store {r₁ r₂ : SEC.Replica (Store R)}
    (h : SEC.SameDeliveredSet r₁ r₂) : r₁.state = r₂.state :=
  SEC.sec_state_based (σ := Store R) h

/- ── The IO harness: replicas as cells with a network attached ── -/

structure Node (R : Nat) where
  id : Fin R
  ref : IO.Ref (Store R)

def Node.new (i : Fin R) : IO (Node R) := do
  return ⟨i, ← IO.mkRef (⊥ : Store R)⟩

def Node.edit (n : Node R) (f : Store R → Store R) : IO Unit :=
  n.ref.modify f

/-- Anti-entropy: `dst` merges `src`'s state. Just a join. -/
def Node.pull (dst src : Node R) : IO Unit := do
  let s ← src.ref.get
  dst.ref.modify (· ⊔ s)

/-- Fixed local edit scripts (bread = 1, milk = 2, eggs = 3):
    Alice puts bread ×2; Bob puts milk ×1 and adds-then-removes eggs;
    Carol also puts bread (concurrently with Alice!) and bumps it ×1. -/
def localEdits (alice bob carol : Node 3) : IO Unit := do
  alice.edit (fun s => addQty 0 1 2 (addItem 0 1 s))
  bob.edit (addItem 1 3)      -- Bob adds eggs ...
  bob.edit (removeItem 3)     -- ... and thinks better of it
  bob.edit (fun s => addQty 1 2 1 (addItem 1 2 s))
  carol.edit (fun s => addQty 2 1 1 (addItem 2 1 s))

/-- Run one delivery schedule: local edits, then the schedule's merges
    (duplicated, reordered, self-merges — whatever it says), then one
    final full anti-entropy sweep so that every update reaches everyone. -/
def runSchedule (name : String) (sched : List (Nat × Nat)) : IO Unit := do
  let alice ← Node.new 0
  let bob   ← Node.new 1
  let carol ← Node.new 2
  let node (k : Nat) : Node 3 :=
    if k % 3 = 0 then alice else if k % 3 = 1 then bob else carol
  localEdits alice bob carol
  for (src, dst) in sched do
    (node dst).pull (node src)
  -- the sweep: two full rounds of everyone-pulls-everyone
  for _ in [0, 1] do
    for src in [0, 1, 2] do
      for dst in [0, 1, 2] do
        (node dst).pull (node src)
  let sA ← alice.ref.get
  let sB ← bob.ref.get
  let sC ← carol.ref.get
  IO.println s!"{name}:"
  IO.println s!"  alice: {render [1, 2, 3] sA}"
  IO.println s!"  bob:   {render [1, 2, 3] sB}"
  IO.println s!"  carol: {render [1, 2, 3] sC}"

/-- Three adversarial schedules, identical final states. -/
def demoConvergence : IO Unit := do
  runSchedule "schedule A (orderly)" [(0, 1), (1, 2), (2, 0)]
  runSchedule "schedule B (reversed, duplicated)"
    [(2, 1), (2, 1), (1, 0), (1, 0), (0, 2)]
  runSchedule "schedule C (chaotic, self-merges)"
    [(1, 1), (2, 0), (0, 0), (1, 2), (2, 1), (2, 1), (0, 2)]

#eval demoConvergence

end Capstone

/- ============================================================
   Crdt.Limits — Chapter 13: What CRDTs Cannot Do
   ============================================================ -/

namespace Limits

/-- Refuted: "there is a merge for non-negative bank accounts".
    Suppose a merge that is duplicate-safe (idempotent) and honors
    both replicas' withdrawals from a shared initial balance of 100.
    Two concurrent withdrawals of 80 force `merge 20 20` to be both
    `20` (idempotence) and `-60` (honoring both). No such function
    exists — availability under partition cannot preserve "balance
    never goes negative" while accepting every withdrawal. -/
theorem no_bank_merge :
    ¬ ∃ merge : Int → Int → Int,
        (∀ a, merge a a = a) ∧
        (∀ x y : Nat, x ≤ 100 → y ≤ 100 →
          merge (100 - (x : Int)) (100 - (y : Int))
            = 100 - (x : Int) - (y : Int)) := by
  intro ⟨merge, hidem, hboth⟩
  have h₂ := hboth 80 80 (by omega) (by omega)
  have he : (100 : Int) - (80 : Nat) = 20 := by decide
  rw [he, hidem 20] at h₂
  exact absurd h₂ (by decide)

/-- The PN-Counter happily goes negative: convergence is not
    correctness. (The Chapter 4 `clampedValue` exercise hid the
    problem; it did not solve it.) -/
theorem pn_goes_negative :
    PNCounter.value (PNCounter.decr 0 (⊥ : PNCounter 1)) < 0 := by decide

end Limits

/- ============================================================
   Crdt.Solutions — Appendix B: solutions with a single definitive
   answer, compiled here so they can never rot. Exercises whose
   solution is a main-text theorem are cited, not repeated; open-ended
   and long-fuse (★★★) exercises get hints in the appendix prose only.
   ============================================================ -/

namespace Solutions

open Order.PartialOrder Order.BoundedJoinSemilattice

/- Exercise 3.1 — increments commute (any indices, even equal ones). -/
theorem increment_comm {R : Nat} (i j : Fin R) (g : GCounter R) :
    GCounter.increment i (GCounter.increment j g)
      = GCounter.increment j (GCounter.increment i g) :=
  (OpBased.opCounter R).comm i j g

/- Exercise 3.2 — the executable list-backed G-Counter agrees with the
   functional model: rendering the merge is zipping the renders. -/
theorem zipWith_map_map {α β : Type} (f : β → β → β) (g h : α → β) :
    ∀ (l : List α),
      List.zipWith f (l.map g) (l.map h) = l.map (fun i => f (g i) (h i))
  | [] => rfl
  | x :: t => by
      simp only [List.map_cons, List.zipWith_cons_cons]
      rw [zipWith_map_map f g h t]

theorem toList_sup {R : Nat} (g h : GCounter R) :
    GCounter.toList (g ⊔ h)
      = List.zipWith Nat.max (GCounter.toList g) (GCounter.toList h) :=
  (zipWith_map_map Nat.max g h (List.finRange R)).symm

/- Exercise 3.3 — a merge's value is at most the sum of values ... -/
theorem foldl_add_pair {ι : Type} (f g : ι → Nat) :
    ∀ (l : List ι) (a b : Nat),
      l.foldl (fun acc i => acc + (f i + g i)) (a + b)
        = l.foldl (fun acc i => acc + f i) a
            + l.foldl (fun acc i => acc + g i) b
  | [], _, _ => rfl
  | x :: t, a, b => by
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons,
          show a + b + (f x + g x) = (a + f x) + (b + g x) by omega]
      exact foldl_add_pair f g t (a + f x) (b + g x)

theorem value_sup_le {R : Nat} (g h : GCounter R) :
    GCounter.value (g ⊔ h) ≤ GCounter.value g + GCounter.value h := by
  have hle : ∀ i : Fin R, (g ⊔ h) i ≤ g i + h i := fun i =>
    Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  calc GCounter.value (g ⊔ h)
      ≤ (List.finRange R).foldl (fun acc i => acc + (g i + h i)) 0 :=
        GCounter.foldl_add_le hle _ (Nat.le_refl 0)
    _ = GCounter.value g + GCounter.value h := foldl_add_pair g h _ 0 0

/- ... and strictly less as soon as the summands overlap. -/
example :
    GCounter.value
        (GCounter.increment 0 (⊥ : GCounter 1) ⊔ GCounter.increment 0 ⊥)
      < GCounter.value (GCounter.increment 0 (⊥ : GCounter 1))
          + GCounter.value (GCounter.increment 0 (⊥ : GCounter 1)) := by
  decide

/- Exercise 4.2 — a clamped query hides the negative truth (a seed for
   Chapter 13). -/
def clampedValue {R : Nat} (p : PNCounter R) : Nat :=
  (PNCounter.value p).toNat

example : clampedValue (PNCounter.decr 0 (⊥ : PNCounter 1)) = 0 := by decide
example : PNCounter.value (PNCounter.decr 0 (⊥ : PNCounter 1)) < 0 := by decide

/- Exercise 5.2 — `size` is monotone on G-Sets. The lemma is the
   sorted-lists pigeonhole: a sorted duplicate-free sublist is shorter. -/
theorem sorted_subset_length {α : Type} [TotalOrder α] :
    ∀ {l₁ l₂ : List α}, SList.Sorted l₁ → SList.Sorted l₂ →
      (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _, _ => Nat.zero_le _
  | a :: _, [], _, _, h => absurd (h a List.mem_cons_self) (by intro hx; cases hx)
  | a :: t₁, b :: t₂, h₁, h₂, h => by
      have hab : b ≼ a := SList.sorted_head_le h₂ a (h a List.mem_cons_self)
      by_cases he : a = b
      · subst he
        apply Nat.succ_le_succ
        apply sorted_subset_length (SList.sorted_tail h₁) (SList.sorted_tail h₂)
        intro x hx
        have hax : a ≺ x := SList.sorted_head_lt h₁ x hx
        cases List.mem_cons.mp (h x (List.mem_cons_of_mem a hx)) with
        | inl hxa => exact absurd (hxa ▸ hax) (TotalOrder.lt_irrefl a)
        | inr hm => exact hm
      · have hba : b ≺ a := ⟨hab, fun hc => he hc.symm⟩
        have hsub : ∀ x ∈ a :: t₁, x ∈ t₂ := by
          intro x hx
          have hbx : b ≺ x :=
            TotalOrder.lt_of_lt_of_le hba (SList.sorted_head_le h₁ x hx)
          cases List.mem_cons.mp (h x hx) with
          | inl hxb => exact absurd (hxb ▸ hbx) (TotalOrder.lt_irrefl b)
          | inr hm => exact hm
        have hlen := sorted_subset_length h₁ (SList.sorted_tail h₂) hsub
        simp only [List.length_cons] at *
        omega

theorem size_monotone {s t : GSet} (h : s ⊑ t) :
    SList.size s ≤ SList.size t :=
  sorted_subset_length s.sorted t.sorted h

/- Exercise 6.2 — three replicas, tied naive timestamps: grouping one
   merge differently changes the answer. -/
example :
    LWW.naiveMerge (LWW.naiveMerge (3, 1) (3, 2)) (3, 3)
      ≠ LWW.naiveMerge (LWW.naiveMerge (3, 2) (3, 1)) (3, 3) := by decide

/- Exercise 6.1 — the never-written register is the identity of merge. -/
theorem lww_merge_bot {R : Nat} (x : LWW.LWWReg R Nat) : ⊥ ⊔ x = x :=
  Order.sup_bot_left x

/- Exercise 7.2 — tombstones only ever accumulate (the cost is real). -/
theorem orset_tombs_size_monotone {R : Nat} {s t : ORSet R} (h : s ⊑ t) :
    SList.size s.tombs ≤ SList.size t.tombs :=
  sorted_subset_length s.tombs.sorted t.tombs.sorted h.2.1

/- Exercise 8.2 — multiset union is well-defined: `Quotient.lift₂`
   demands congruence of append under permutation. -/
theorem perm_append_right {α : Type} (m : List α) {l₁ l₂ : List α}
    (h : Perm l₁ l₂) : Perm (l₁ ++ m) (l₂ ++ m) := by
  induction h with
  | nil => exact Perm.refl m
  | cons x _ ih => exact .cons x ih
  | swap x y l => exact .swap x y (l ++ m)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem perm_append_left {α : Type} (m : List α) {l₁ l₂ : List α}
    (h : Perm l₁ l₂) : Perm (m ++ l₁) (m ++ l₂) := by
  induction m with
  | nil => exact h
  | cons x t ih => exact .cons x ih

def msetUnion {α : Type} : MSet α → MSet α → MSet α :=
  Quotient.lift₂ (fun l₁ l₂ => MSet.ofList (l₁ ++ l₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound
      (.trans (perm_append_right _ h₁) (perm_append_left _ h₂)))

example : msetUnion (MSet.ofList [1, 2]) (MSet.ofList [3])
    = MSet.ofList [1, 2, 3] := rfl

/- Exercise 9.2 — `seen` is monotone along `Reachable`: replicas never
   forget. -/
theorem seen_monotone {R : Nat} {σ : Type} [BoundedJoinSemilattice σ]
    {c₁ c₂ : Delivery.Config R σ} (h : Delivery.Reachable c₁ c₂)
    (r : Fin R) : ∀ x ∈ c₁.seen r, x ∈ c₂.seen r := by
  induction h with
  | refl => intro _ hx; exact hx
  | tail _ hs ih =>
      intro x hx
      have hx₂ := ih x hx
      cases hs with
      | update r' v =>
          show x ∈ (if r = r' then v :: _ else _)
          by_cases hr : r = r'
          · subst hr; simp; exact Or.inr hx₂
          · simp [hr]; exact hx₂
      | send r' r'' => exact hx₂
      | deliver r' p hp =>
          show x ∈ (if r = r' then p.2 ++ _ else _)
          by_cases hr : r = r'
          · subst hr; simp; exact Or.inr hx₂
          · simp [hr]; exact hx₂

/- Exercise 10.2 — the merged version vector is the least upper bound
   of the causal histories. -/
theorem vv_merge_lub {R : Nat} {v w u : VV R} (hv : v ⊑ u) (hw : w ⊑ u) :
    v ⊔ w ⊑ u :=
  sup_le v w u hv hw

/- Exercise 11.1 — the op-based PN-Counter: an operation is a signed
   increment; everything commutes. -/
def opPNCounter (R : Nat) : OpBased.OpCRDT (Bool × Fin R) (PNCounter R) where
  init := ⊥
  apply o p :=
    if o.1 then (GCounter.increment o.2 p.1, p.2)
    else (p.1, GCounter.increment o.2 p.2)
  comm o₁ o₂ s := by
    by_cases h₁ : o₁.1 <;> by_cases h₂ : o₂.1 <;> simp [h₁, h₂]
    · rw [increment_comm]
    · rw [increment_comm]

end Solutions

/- ============================================================
   Axiom audit — every headline theorem, `#print axioms`.
   Result: nothing beyond `propext` (propositional extensionality,
   used through `funext`/`ext`-style reasoning) and `Quot.sound`
   (quotients, Chapter 8; also inside core `simp` lemmas about
   lists). `Classical.choice` appears nowhere: the entire chain,
   `sec_state_based` included, is constructive.
   ============================================================ -/

#print axioms Order.sup_comm
#print axioms Order.sup_assoc
#print axioms GCounter.value_increment
#print axioms PNCounter.value_not_monotone
#print axioms SList.sorted_ext
#print axioms TotalOrder.maxo_assoc
#print axioms TwoPSet.no_readd
#print axioms ORSet.addWins
#print axioms SEC.foldJoin_eq_of_same_mems
#print axioms SEC.foldJoin_perm
#print axioms MSet.foldJoin
#print axioms SEC.sec_state_based
#print axioms Delivery.converged_of_allShared
#print axioms Delivery.gossipUntilQuiescent
#print axioms Delivery.quiescent_shares
#print axioms VV.ticks_concurrent
#print axioms OpBased.opGCounter_simulates
#print axioms Capstone.sec_store
#print axioms Limits.no_bank_merge

end Crdt
