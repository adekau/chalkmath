import MathEngine.Expr
/-!
# Provenance-carrying rewriting, with termination as a proof obligation

A `Rule` looks at one node and either rewrites it (returning the new node and *why* the rewrite
is valid) or declines. `normalize` applies rules innermost-first to a fixed point and records
every firing as a `Step`: the whole term before and after, and the path where it fired.

**Termination.** The reference engine hides termination behind a 10 000-step budget. Here it is
a proof obligation: a `Rule` carries a proof that its result is strictly smaller than its input
under a *weighted node count* (`measure`), and `normalize` recurses by well-founded recursion on
`(measure e, size e)`. Nothing is `partial`. The weights are a parameter (`Weights`): each rule
set chooses weights that make its rules decrease, and proves it once per rule. The argument only
needs two facts about the measure, both proved below for every weight assignment:

* it is *additive*, so replacing children by smaller children makes the parent smaller
  (`measure_withChildren`), and
* it is invariant under reordering arguments (`measure_canon`), so canonical ordering can happen
  silently inside the loop without being a rule.

The notebook pipeline needs a different argument (rules that duplicate subterms): see `Order.lean`
and `Terminate.lean`. There is no fuel-based rewriter any more.
-/
namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Derivations: the "show work" data model (mirrors `Step`/`Derivation` in the protocol)
-- ---------------------------------------------------------------------------

mutual
  structure Step where
    rule : String
    explanation : String
    path : Path
    before : Expr
    after : Expr
    sub : Option Derivation := none
  structure Derivation where
    input : Expr
    steps : Array Step
    output : Expr
end

instance : Inhabited Derivation := ⟨⟨default, #[], default⟩⟩
instance : Inhabited Step := ⟨⟨"", "", [], default, default, none⟩⟩

structure RuleResult where
  result : Expr
  explanation : String
  /-- Steps taken inside this rewrite (e.g. the row operations behind an `rref` command). -/
  sub : Option Derivation := none
  /-- A rule may refuse the whole evaluation (the reference throws, e.g. on a dimension mismatch).
  The tiered rewriter (`normalizeT`) honours this. A verified rule sets it only where mathematics
  leaves the term undefined and its semantics would answer anyway (`simp.power` on `0^(-1)`, which
  `Rat` makes `0`); its value is still what the theorem says, so the proofs do not mention it. -/
  error : Option String := none

-- ---------------------------------------------------------------------------
-- The measure
-- ---------------------------------------------------------------------------

/-- Node weights. A weight depends only on the node's head, never on its children (`head`), and
is at least 1 (`pos`), which is what makes the weighted node count a strict subterm order. -/
structure Weights where
  w : Expr → Nat
  pos : ∀ e, 1 ≤ w e
  head : ∀ e cs, w (withChildren e cs) = w e

/-- Every node weighs 1: plain `size`. -/
def unitWeights : Weights where
  w _ := 1
  pos _ := Nat.le_refl 1
  head _ _ := rfl

mutual
  /-- Weighted node count. -/
  def measure (W : Weights) : Expr → Nat
    | .num q => W.w (.num q)
    | .var x => W.w (.var x)
    | .add es => W.w (.add es) + measureList W es
    | .mul es => W.w (.mul es) + measureList W es
    | .pow b e => W.w (.pow b e) + measure W b + measure W e
    | .fn f es => W.w (.fn f es) + measureList W es
    | .matrix rows => W.w (.matrix rows) + measureRows W rows
  def measureList (W : Weights) : List Expr → Nat
    | [] => 0
    | e :: es => measure W e + measureList W es
  def measureRows (W : Weights) : List (List Expr) → Nat
    | [] => 0
    | r :: rs => measureList W r + measureRows W rs
end

theorem measureList_append (W : Weights) (l₁ l₂ : List Expr) :
    measureList W (l₁ ++ l₂) = measureList W l₁ + measureList W l₂ := by
  induction l₁ with
  | nil => simp [measureList]
  | cons e es ih => simp [measureList, ih]; omega

theorem measureRows_flatten (W : Weights) (rows : List (List Expr)) :
    measureRows W rows = measureList W rows.flatten := by
  induction rows with
  | nil => simp [measureRows, measureList]
  | cons r rs ih => simp [measureRows, measureList_append, ih]

/-- The measure is the head weight plus the children's measures. -/
theorem measure_eq (W : Weights) (e : Expr) : measure W e = W.w e + measureList W (children e) := by
  cases e <;> simp [measure, children, measureList, measureRows_flatten] <;> omega

theorem measureList_perm (W : Weights) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) :
    measureList W l₁ = measureList W l₂ := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [measureList, ih]
  | swap => simp [measureList]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem measureList_take_drop (W : Weights) (n : Nat) (l : List Expr) :
    measureList W (l.take n) + measureList W (l.drop n) = measureList W l := by
  rw [← measureList_append, List.take_append_drop]

/-- Rebuilding a node from children: the measure is the head weight plus the new children's. -/
theorem measure_withChildren (W : Weights) (e : Expr) (cs : List Expr)
    (hlen : cs.length = (children e).length) :
    measure W (withChildren e cs) = W.w e + measureList W cs := by
  rw [measure_eq, W.head, children_withChildren e cs hlen]

theorem measureList_children_lt (W : Weights) (e : Expr) : measureList W (children e) < measure W e := by
  rw [measure_eq]; have := W.pos e; omega

-- ---------------------------------------------------------------------------
-- Rules
-- ---------------------------------------------------------------------------

/-- A rewrite rule with its termination obligation under the weights `W`. -/
structure Rule (W : Weights) where
  name : String
  /-- Silent rules still fire but leave no `Step` (canonical reordering, flattening). -/
  silent : Bool := false
  apply : Expr → Option RuleResult
  decreasing : ∀ e r, apply e = some r → measure W r.result < measure W e

/-- First applicable rule, with the evidence that it applied. -/
def fire (rules : List (Rule W)) (e : Expr) : Option {p : Rule W × RuleResult // p.1.apply e = some p.2} :=
  match rules with
  | [] => none
  | r :: rs =>
    match h : r.apply e with
    | some res => some ⟨(r, res), h⟩
    | none => fire rs e

theorem fire_mem (rules : List (Rule W)) (e : Expr) (p) (h : fire rules e = some p) : p.1.1 ∈ rules := by
  induction rules with
  | nil => simp [fire] at h
  | cons r rs ih =>
    simp only [fire] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

-- ---------------------------------------------------------------------------
-- Canonical argument order (silent, measure-preserving)
-- ---------------------------------------------------------------------------

/-- Total degree in all variables, for ordering sums the way people write them (`x^3 + 3x^2 + 3x + 1`). -/
partial def degree : Expr → Rat
  | .num _ => 0
  | .var _ => 1
  | .pow b (.num q) => degree b * q.val
  | .pow b _ => degree b
  | .mul es => es.foldl (fun d a => d + degree a) 0
  | .add es => es.foldl (fun d a => max d (degree a)) 0
  | .fn _ _ | .matrix _ => 0

/-- `c * rest` with numeric `c`; a term without a coefficient is `1 * itself`. -/
def coeffRest : Expr → Q × Expr
  | .num q => (q, Expr.one)
  | .mul (.num q :: rest) => (q, mulN rest)
  | e => (Q.one, e)

def cmpRat (a b : Rat) : Ordering := if a < b then .lt else if a == b then .eq else .gt
def leMul (a b : Expr) : Bool := compare a b != Ordering.gt
/-- Does `i` occur in a term? (Also `ComplexRules.mentionsI`, which imports this file.) -/
partial def hasI : Expr → Bool
  | .fn "i" [] => true
  | e => (children e).any hasI

/-- The rank of a summand's rest for sums: as `kindRank`, except that a term mentioning `i` sorts
after everything real, so a Gaussian numeral reads `a + b·i` and Euler's formula reads
`cos θ + i·sin θ`. -/
def sumRank (r : Expr) : Nat := if hasI r then 0 else kindRank r + 1

/-- Sums: highest degree first, constants last, otherwise the structural order. -/
def leAdd (a b : Expr) : Bool :=
  let ra := (coeffRest a).2
  let rb := (coeffRest b).2
  let o := (cmpRat (degree rb) (degree ra)).then
    ((Ord.compare (sumRank rb) (sumRank ra)).then ((compare ra rb).then (compare a b)))
  o != Ordering.gt

/-- Sort the arguments of a sum or product; other nodes are unchanged. Products containing a matrix
are not commutative and are left in place (the reference gets this by trying `la.mul` before its sort rule). -/
def canon : Expr → Expr
  | .add es => .add (es.mergeSort leAdd)
  | .mul es => if es.any isMatrix then .mul es else .mul (es.mergeSort leMul)
  | e => e

theorem measure_canon (W : Weights) (e : Expr) : measure W (canon e) = measure W e := by
  cases e with
  | add es =>
    have hw : W.w (.add (es.mergeSort leAdd)) = W.w (.add es) := W.head (.add es) _
    simp only [canon, measure, hw, measureList_perm W (List.mergeSort_perm es leAdd)]
  | mul es =>
    have hw : W.w (.mul (es.mergeSort leMul)) = W.w (.mul es) := W.head (.mul es) _
    simp only [canon]
    split
    · rfl
    · simp only [measure, hw, measureList_perm W (List.mergeSort_perm es leMul)]
  | _ => rfl

-- ---------------------------------------------------------------------------
-- The rewriter
-- ---------------------------------------------------------------------------

/-- A firing as recorded during normalization: only the local result. Whole-term `before`/`after`
are reconstructed afterwards by replaying the rewriter's tape from the input (`buildSteps`). -/
structure RawStep where
  rule : String
  silent : Bool
  explanation : String
  after : Expr
  sub : Option Derivation

/-- The rewriter's tape: its moves between nodes, and its firings at the node in focus. A firing is
recorded without its path, and the replay follows the moves with a zipper, so a firing costs the
rewriter and the replay the same at any depth; a path per firing, walked from the root at each,
cost a chain of silent firings (`√(√(…√x))`) its depth squared. -/
inductive Record where
  /-- into the first child of the node in focus -/
  | down
  /-- to the next sibling -/
  | next
  /-- back to the parent -/
  | up
  /-- a firing at the node in focus, which it replaces -/
  | fire (s : RawStep)

/-- Lexicographic order on pairs of naturals, in the form the termination proofs need. -/
theorem lex_of_le {a a' b b' : Nat} (h₁ : a ≤ a') (h₂ : a = a' → b < b') :
    Prod.Lex (· < ·) (· < ·) (a, b) (a', b') := by
  rcases Nat.lt_or_eq_of_le h₁ with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ (h₂ rfl)

/-- Same for triples: `normAt` and `normChildren` share one well-founded order
`(measure, size, phase)` where the phase separates "at a node" (0) from "in its children" (1). -/
theorem lex3 {a a' b b' c c' : Nat} (h₁ : a ≤ a') (h₂ : a = a' → b ≤ b') (h₃ : a = a' → b = b' → c < c') :
    Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)) (a, b, c) (a', b', c') := by
  rcases Nat.lt_or_eq_of_le h₁ with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ (lex_of_le (h₂ rfl) (h₃ rfl))

mutual
  /-- Normalize the subterm `e` in focus: children first, then rules at the node until none
  applies, re-normalizing after each firing. Returns the result and the tape so far, together with
  the fact that the result is no heavier than the input. -/
  def normAt (rules : List (Rule W)) (e : Expr) (acc : Array Record) :
      {r : Expr × Array Record // measure W r.1 ≤ measure W e} :=
    match normChildren rules (children e) 0 acc with
    | ⟨(cs, acc₀), hcs⟩ =>
      let e₀ := withChildren e cs
      let e₁ := canon e₀
      -- canonical order is silent but must be replayed, or later snapshots would not line up
      let acc₁ := if equal e₁ e₀ then acc₀ else acc₀.push (.fire ⟨"simp.sort", true, "commutativity", e₁, none⟩)
      have h₁ : measure W e₁ ≤ measure W e := by
        have hm : measureList W cs ≤ measureList W (children e) := hcs.2
        simp only [e₁, e₀]; rw [measure_canon, measure_withChildren W e cs hcs.1, measure_eq W e]; omega
      match hf : fire rules e₁ with
      | none => ⟨(e₁, acc₁), h₁⟩
      | some ⟨(rule, res), hr⟩ =>
        have hdec : measure W res.result < measure W e := Nat.lt_of_lt_of_le (rule.decreasing e₁ res hr) h₁
        let acc₂ := acc₁.push (.fire ⟨rule.name, rule.silent, res.explanation, res.result, res.sub⟩)
        match normAt rules res.result acc₂ with
        | ⟨r, hr'⟩ => ⟨r, Nat.le_of_lt (Nat.lt_of_le_of_lt hr' hdec)⟩
  termination_by (measure W e, size e, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ (measureList_children_lt W e)
    · exact Prod.Lex.left _ _ hdec

  /-- The children from index `i` on: a move into the first, to each next one, and back out. -/
  def normChildren (rules : List (Rule W)) (cs : List Expr) (i : Nat) (acc : Array Record) :
      {r : List Expr × Array Record // r.1.length = cs.length ∧ measureList W r.1 ≤ measureList W cs} :=
    match cs with
    | [] => ⟨([], if i = 0 then acc else acc.push .up), by simp [measureList]⟩
    | c :: cs' =>
      match normAt rules c (acc.push (if i = 0 then .down else .next)) with
      | ⟨(c', acc₁), hc⟩ =>
        match normChildren rules cs' (i + 1) acc₁ with
        | ⟨(cs'', acc₂), hcs⟩ =>
          ⟨(c' :: cs'', acc₂), by
            have hc' : measure W c' ≤ measure W c := hc
            have hl : cs''.length = cs'.length := hcs.1
            have hm : measureList W cs'' ≤ measureList W cs' := hcs.2
            simp only [measureList, List.length_cons]; omega⟩
  termination_by (measureList W cs, sizeList cs, 1)
  decreasing_by
    · exact lex3 (by simp only [measureList]; omega) (fun _ => by simp only [sizeList]; omega) (fun _ _ => Nat.zero_lt_one)
    · exact lex3 (by simp only [measureList]; omega) (fun _ => by simp only [sizeList]; omega)
        (fun _ h => by simp only [sizeList] at h; have := size_pos c; omega)
end

/-- Replace the subterm at `path`. -/
def replaceAt (e : Expr) (path : Path) (new : Expr) : Expr :=
  match path with
  | [] => new
  | i :: rest =>
    let cs := children e
    match cs[i]? with
    | some c => withChildren e (cs.set i (replaceAt c rest new))
    | none => e

/-- Where entry `k` (row-major) of a matrix with these rows sits, in words. -/
def entryName (rows : List (List Expr)) (k : Nat) : String :=
  let cols := (rows.head?.map List.length).getD 1
  if rows.length ≤ 1 || cols ≤ 1 then s!"entry {k + 1}"
  else s!"row {k / cols + 1}, column {k % cols + 1}"

/-! ## Replaying the tape

The replay keeps the term as a zipper: the subterm in focus and, innermost first, the nodes above
it, each with the siblings on either side of the focus. A move costs what it moves (a node's
children list is rebuilt once, on the way out), a silent firing replaces the focus, and only a
visible firing, which needs its path and the whole term before and after, pays for its depth. -/

namespace Replay

/-- A node the replay is inside. Its own children are not read; the focus's siblings are kept on
either side of it, nearest first on the left. `mat` is the depth of the innermost matrix literal at
or above this node, for grouping the firings inside a matrix's entries. -/
structure Frame where
  node : Expr
  left : List Expr
  right : List Expr
  idx : Nat
  mat : Option Nat

/-- The node a frame holds, with the focus back among its children. -/
def Frame.close (f : Frame) (focus : Expr) : Expr := withChildren f.node (f.left.reverseAux (focus :: f.right))

structure Zipper where
  focus : Expr
  frames : List Frame

namespace Zipper

def depth (z : Zipper) : Nat := z.frames.length

/-- The path of the focus, root first. -/
def path (z : Zipper) : Path := z.frames.foldl (fun acc f => f.idx :: acc) []

/-- The innermost matrix literal the focus is strictly inside, by depth. -/
def enclosingMatrix (z : Zipper) : Option Nat := z.frames.head?.bind (·.mat)

def down (z : Zipper) : Zipper :=
  match children z.focus with
  | [] => z
  | c :: cs =>
    let mat := if z.focus.isMatrix then some z.depth else z.enclosingMatrix
    { focus := c, frames := { node := z.focus, left := [], right := cs, idx := 0, mat } :: z.frames }

def next (z : Zipper) : Zipper :=
  match z.frames with
  | f :: fs =>
    match f.right with
    | c :: cs => { focus := c, frames := { f with left := z.focus :: f.left, right := cs, idx := f.idx + 1 } :: fs }
    | [] => z
  | [] => z

def up (z : Zipper) : Zipper :=
  match z.frames with
  | f :: fs => { focus := f.close z.focus, frames := fs }
  | [] => z

/-- The node `n` levels above the focus, rebuilt. -/
def above (z : Zipper) (n : Nat) : Expr := (z.frames.take n).foldl (fun e f => f.close e) z.focus

/-- The whole term. -/
def whole (z : Zipper) : Expr := z.frames.foldl (fun e f => f.close e) z.focus

end Zipper

/-- A run of firings strictly inside one matrix's entries, gathered as they come. The rewriter
normalizes a node's children one after another, so a matrix's entries are rewritten in a run; when
the run rewrites two entries or more, it becomes one step, `la.entrywise`, whose nested derivation
holds each entry's steps with the entry alone as the term (path relative to it), the matrix around
it left out. That keeps the derivation of an entrywise computation linear in the matrix's size, where
one step per entry with the whole matrix before and after would be quadratic, and it reads as a
textbook writes it: `2A = [2·50, 2·1; …] = [100, 2; …]`, with the arithmetic of each entry below.
A run that touches one entry only stays what it was: its steps, each with the whole term. -/
structure Run where
  /-- the matrix sits this many frames down -/
  depth : Nat
  /-- the whole term before the run -/
  before : Expr
  /-- the matrix before the run -/
  m : Expr
  /-- the entries a visible firing touched: marked, not `eraseDups`, which made a firing per entry of
  a 100 × 100 matrix a square of the entries -/
  marks : Array Bool
  /-- the entries' visible steps, each with the entry alone as its term -/
  subs : Array Step
  /-- the same steps with the whole term, for a run that touches fewer than two entries -/
  plain : Array Step

/-- The run as steps, with the matrix now in focus. -/
def Run.commit (out : Array Step) (r : Run) (z : Zipper) : Array Step :=
  let touched := r.marks.foldl (fun n b => if b then n + 1 else n) 0
  if touched < 2 then out ++ r.plain else
  let total := r.marks.size
  let rows := match r.m with | .matrix rows => rows | _ => []
  let what := if rows.length ≤ 1 || ((rows.head?.map List.length).getD 1) ≤ 1 then "list" else "matrix"
  let which := if touched == total then s!"every entry of the {what} is worked out on its own"
    else s!"{touched} of the {what}'s {total} entries are worked out, each on its own"
  let n := r.subs.size
  out.push { rule := "la.entrywise", explanation := s!"Entry by entry: {which}; the {n} steps are nested below.",
             path := z.path, before := r.before, after := z.whole, sub := some ⟨r.m, r.subs, z.focus⟩ }

/-- The run, ended if the focus is its matrix: a move away from the matrix, or a firing at it, is
where its steps are written. -/
def leaving (out : Array Step) (z : Zipper) : Option Run → Array Step × Option Run
  | some r => if z.depth ≤ r.depth then (r.commit out z, none) else (out, some r)
  | none => (out, none)

/-- One record of the tape: the steps so far, the term, and the run being gathered. -/
def record : Array Step × Zipper × Option Run → Record → Array Step × Zipper × Option Run
  | (out, z, run), .down => let (out, run) := leaving out z run; (out, z.down, run)
  | (out, z, run), .next => let (out, run) := leaving out z run; (out, z.next, run)
  | (out, z, run), .up => let (out, run) := leaving out z run; (out, z.up, run)
  | (out, z, run), .fire s =>
    -- a firing strictly inside a matrix starts a run
    let (out, run) := leaving out z run
    let run := run <|> z.enclosingMatrix.map fun d =>
      let m := z.above (z.depth - d)
      { depth := d, before := z.whole, m, marks := Array.replicate (children m).length false, subs := #[], plain := #[] }
    let z' := { z with focus := s.after }
    match run with
    | some r =>
      -- the frame holding the matrix, and the entry's own path below it
      let inside := z.depth - r.depth - 1
      let k := (z.frames[inside]?.map (·.idx)).getD 0
      if s.silent then (out, z', some r) else
      let rel := (z.frames.take inside).foldl (fun acc f => f.idx :: acc) []
      let rows := match r.m with | .matrix rows => rows | _ => []
      let why := if s.explanation.endsWith "." then s.explanation.dropRight 1 else s.explanation
      let sub : Step := { rule := s.rule, explanation := s!"{why} ({entryName rows k}).", path := rel,
                          before := z.above inside, after := z'.above inside, sub := s.sub }
      let plain : Step := { rule := s.rule, explanation := s.explanation, path := z.path,
                            before := z.whole, after := z'.whole, sub := s.sub }
      let r := { r with marks := r.marks.set! k true, subs := r.subs.push sub, plain := r.plain.push plain }
      (out, z', some r)
    | none =>
      if s.silent then (out, z', none) else
      (out.push { rule := s.rule, explanation := s.explanation, path := z.path, before := z.whole, after := z'.whole, sub := s.sub }, z', none)

end Replay

/-- Replay the tape from `input`, producing steps with whole-term `before`/`after`. A run of
firings inside one matrix's entries becomes one `la.entrywise` step (`Replay.Run`). -/
def buildSteps (input : Expr) (tape : Array Record) : Array Step × Expr :=
  let (out, z, run) := tape.foldl Replay.record (#[], ⟨input, []⟩, none)
  -- a run still open at the end is the root's: the moves out of every other node closed theirs
  let out := match run with | some r => r.commit out z | none => out
  (out, z.whole)

abbrev TraceM := StateM (Array Step)

/-- Rewrite `e` to a normal form under `rules`, appending the steps to the trace. The result is the
normalizer's own (the replay in `buildSteps` reconstructs the same term for the step snapshots). -/
def normalize (rules : List (Rule W)) (e : Expr) : TraceM Expr := do
  let ⟨(out, tape), _⟩ := normAt rules e #[]
  let (steps, _) := buildSteps e tape
  modify (· ++ steps)
  pure out

theorem normalize_run (rules : List (Rule W)) (e : Expr) (s : Array Step) :
    ((normalize rules e).run' s) = (normAt rules e #[]).1.1 := by
  simp only [normalize, StateT.run', bind, StateT.bind, modify, pure, StateT.pure, MonadStateOf.modifyGet, StateT.modifyGet, Id.run]
  rfl

/-- Rewrite and package the whole derivation. -/
def derive (rules : List (Rule W)) (e : Expr) : Derivation :=
  let (out, steps) := (normalize rules e).run #[]
  ⟨e, steps, out⟩

-- ---------------------------------------------------------------------------
-- Plain rules: a rule without a bundled proof, for the tiered rewriter of `Terminate.lean`
-- ---------------------------------------------------------------------------

structure PlainRule where
  name : String
  silent : Bool := false
  apply : Expr → Option RuleResult

def fireP (rules : List PlainRule) (e : Expr) : Option (PlainRule × RuleResult) :=
  match rules with
  | [] => none
  | r :: rs => match r.apply e with | some res => some (r, res) | none => fireP rs e

/-- A verified rule, forgetting its proof. -/
def Rule.toPlain (r : Rule W) : PlainRule := { name := r.name, silent := r.silent, apply := r.apply }

end MathEngine
