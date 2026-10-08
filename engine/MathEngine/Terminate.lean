import MathEngine.Order
/-!
# The pipeline rewriter: innermost normalization under the tiered ordering

`normalizeT` is `normalize` (Rewrite.lean) for rule sets whose termination argument is the tiered
ordering `μ` of `Order.lean` rather than one additive measure. Two things differ:

* **The obligation is conditional.** An `Ordered` rule set proves that each rule decreases `μ`
  *when the children of the node it fires on are already normal* (`ChildrenNormal`). Rules that
  duplicate subterms (the product rule, substitution) only decrease `μ` because nothing reducible
  is inside what they duplicate, and it is the rewriter's innermost strategy — children first, then
  the node — that makes the hypothesis true at every firing. The proof is carried in the result type:
  `normAtT` returns its output together with `μ output ≤ μ input` and `Normal output`, and the
  recursive call after a firing uses exactly those facts.
* **Rules may refuse.** A refusal (`RuleResult.error`) stops normalization with that message, as
  the old fuel-based rewriter did; nothing is proven about the term in that case, and nothing needs to be.

Nothing here is `partial`, and there is no step budget: the recursion is well-founded on
`(μ e, phase, remaining children)`.
-/
namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Normal forms
-- ---------------------------------------------------------------------------

/-- No rule in `rules` fires at the root of `e` (refusals count as firing). -/
def NoFire (rules : List PlainRule) (e : Expr) : Prop := ∀ r ∈ rules, r.apply e = none

/-- No rule fires anywhere in `e`. -/
inductive Normal (rules : List PlainRule) : Expr → Prop
  | mk (e : Expr) (h : NoFire rules e) (hc : ∀ c ∈ children e, Normal rules c) : Normal rules e

theorem Normal.noFire {rules : List PlainRule} {e : Expr} (h : Normal rules e) : NoFire rules e := by
  cases h; assumption

theorem Normal.children {rules : List PlainRule} {e : Expr} (h : Normal rules e) : ∀ c ∈ children e, Normal rules c := by
  cases h; assumption

/-- Every child is normal: the hypothesis a rule's decrease proof may assume. -/
def ChildrenNormal (rules : List PlainRule) (e : Expr) : Prop := ∀ c ∈ children e, Normal rules c

theorem Normal.childrenNormal {rules : List PlainRule} {e : Expr} (h : Normal rules e) : ChildrenNormal rules e :=
  h.children

/-- A rule set with its termination proof under `μ`. -/
structure Ordered (rules : List PlainRule) : Prop where
  decreasing : ∀ r ∈ rules, ∀ e res, ChildrenNormal rules e → r.apply e = some res → res.error = none →
    MuLt (μ res.result) (μ e)

theorem fireP_spec (rules : List PlainRule) (e : Expr) : ∀ {r res}, fireP rules e = some (r, res) →
    r ∈ rules ∧ r.apply e = some res := by
  induction rules with
  | nil => intro _ _ h; simp [fireP] at h
  | cons r' rs ih =>
    intro r res h
    simp only [fireP] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨List.mem_cons_self, ‹_›⟩
    · obtain ⟨hm, ha⟩ := ih h; exact ⟨List.mem_cons_of_mem _ hm, ha⟩

theorem noFire_of_fireP_none (rules : List PlainRule) (e : Expr) (h : fireP rules e = none) : NoFire rules e := by
  induction rules with
  | nil => intro r hr; simp at hr
  | cons r' rs ih =>
    intro r hr
    simp only [fireP] at h
    split at h
    · simp at h
    · rcases List.mem_cons.mp hr with rfl | hm
      · assumption
      · exact ih h r hm

-- ---------------------------------------------------------------------------
-- μ is monotone in the children (lexicographically)
-- ---------------------------------------------------------------------------

theorem Expr.RelList.imp {R S : Expr → Expr → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l l' : List Expr}, RelList R l l' → RelList S l l'
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h₁, h₂⟩ => ⟨h _ _ h₁, Expr.RelList.imp h h₂⟩

theorem Expr.RelList.and {R S : Expr → Expr → Prop} :
    ∀ {l l' : List Expr}, RelList R l l' → RelList S l l' → RelList (fun a b => R a b ∧ S a b) l l'
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h₁, h₂⟩, ⟨g₁, g₂⟩ => ⟨⟨h₁, g₁⟩, Expr.RelList.and h₂ g₂⟩

theorem Expr.RelList.mem_right {R : Expr → Expr → Prop} :
    ∀ {l l' : List Expr}, RelList R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | _ :: _, _ :: _, ⟨h₁, h₂⟩, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h₁⟩
    · obtain ⟨b, hb, hr⟩ := Expr.RelList.mem_right h₂ a ha; exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem ML.le_of_rel : ∀ {cs' cs : List Expr}, RelList (fun a b => M a ≤ M b) cs' cs → ML cs' ≤ ML cs
  | [], [], _ => Nat.le_refl _
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp only [ML]; have := ML.le_of_rel hs; omega

theorem ML.eq_of_rel : ∀ {cs' cs : List Expr}, RelList (fun a b => M a ≤ M b) cs' cs → ML cs' = ML cs →
    RelList (fun a b => M a = M b) cs' cs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩, heq => by
    simp only [ML] at heq; have := ML.le_of_rel hs
    exact ⟨by omega, ML.eq_of_rel hs (by omega)⟩

theorem sizeList_le_of_rel : ∀ {cs' cs : List Expr}, RelList (fun a b => size a ≤ size b) cs' cs →
    sizeList cs' ≤ sizeList cs
  | [], [], _ => Nat.le_refl _
  | _ :: _, _ :: _, ⟨h, hs⟩ => by simp only [sizeList]; have := sizeList_le_of_rel hs; omega

theorem sizeList_eq_of_rel : ∀ {cs' cs : List Expr}, RelList (fun a b => size a ≤ size b) cs' cs →
    sizeList cs' = sizeList cs → RelList (fun a b => size a = size b) cs' cs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h, hs⟩, he => by
    simp only [sizeList] at he
    have := sizeList_le_of_rel hs
    exact ⟨by omega, sizeList_eq_of_rel hs (by omega)⟩

/-- `M` of a rebuilt node, monotone in the children. -/
theorem M.withChildren_le (e : Expr) {cs' cs : List Expr} (hlen : cs.length = (children e).length)
    (h : RelList (fun a b => M a ≤ M b) cs' cs) :
    M (withChildren e cs') ≤ M (withChildren e cs) := by
  have hlen' := RelList_length h
  cases e with
  | num _ | var _ => exact Nat.le_refl _
  | add _ =>
    simp only [withChildren]
    cases cs with
    | nil => cases cs' with | nil => exact Nat.le_refl _ | cons => simp at hlen'
    | cons c cs => cases cs' with
      | nil => simp at hlen'
      | cons c' cs' => rw [M.add_cons, M.add_cons]; exact ML.le_of_rel h
  | mul _ => simp only [withChildren, M.mul, hlen']; have := ML.le_of_rel h; omega
  | pow _ _ =>
    simp only [children, List.length_cons, List.length_nil] at hlen
    match cs, cs', hlen, hlen', h with
    | [b, x], [b', x'], _, _, ⟨hb, hx, _⟩ =>
      simp only [withChildren, M.pow]
      have := Nat.mul_le_mul (Nat.add_le_add_right hb 1) hx
      omega
  | fn f _ =>
    simp only [withChildren]
    by_cases hd : f = "diff" ∧ cs.length = 2
    · obtain ⟨rfl, hl⟩ := hd
      match cs, cs', hl, hlen', h with
      | [g, t], [g', t'], _, _, ⟨hg, ht, _⟩ =>
        rw [M.diff, M.diff]
        have := Nat.pow_le_pow_right (n := 3) (by decide) (Nat.add_le_add_right hg 3)
        omega
    · rw [M.fn f cs hd, M.fn f cs' (by rw [hlen']; exact hd)]
      have := ML.le_of_rel h; omega
  | matrix rows =>
    simp only [withChildren, M.matrix, MR.flatten]
    simp only [children] at hlen
    rw [flatten_regroup rows cs hlen, flatten_regroup rows cs' (hlen'.trans hlen)]
    have := ML.le_of_rel h; omega

/-- ... and strictly monotone: equal `M` on the rebuilt nodes forces equal `M` on every child. -/
theorem M.withChildren_eq (e : Expr) {cs' cs : List Expr} (hlen : cs.length = (children e).length)
    (h : RelList (fun a b => M a ≤ M b) cs' cs) (heq : M (withChildren e cs') = M (withChildren e cs)) :
    RelList (fun a b => M a = M b) cs' cs := by
  have hlen' := RelList_length h
  cases e with
  | num _ | var _ =>
    simp only [children, List.length_nil] at hlen
    match cs, cs', hlen, hlen' with
    | [], [], _, _ => trivial
  | add _ =>
    simp only [withChildren] at heq
    cases cs with
    | nil => cases cs' with | nil => trivial | cons => simp at hlen'
    | cons c cs => cases cs' with
      | nil => simp at hlen'
      | cons c' cs' => rw [M.add_cons, M.add_cons] at heq; exact ML.eq_of_rel h heq
  | mul _ => simp only [withChildren, M.mul, hlen'] at heq; exact ML.eq_of_rel h (by omega)
  | pow _ _ =>
    simp only [children, List.length_cons, List.length_nil] at hlen
    match cs, cs', hlen, hlen', h with
    | [b, x], [b', x'], _, _, ⟨hb, hx, _⟩ =>
      simp only [withChildren, M.pow] at heq
      have h1 := M.pos b; have h2 := M.pos x; have h3 := M.pos b'; have h4 := M.pos x'
      have p1 : 1 * 1 ≤ (M b' + 1) * M x' := Nat.mul_le_mul (by omega) h4
      have p2 : 1 * 1 ≤ (M b + 1) * M x := Nat.mul_le_mul (by omega) h2
      have heq' : (M b' + 1) * M x' = (M b + 1) * M x := by omega
      refine ⟨?_, ?_, trivial⟩
      · rcases Nat.lt_or_eq_of_le hb with hlt | hlt
        · exfalso
          have : (M b' + 1) * M x' ≤ (M b' + 1) * M x := Nat.mul_le_mul_left _ hx
          have : (M b' + 1) * M x < (M b + 1) * M x := Nat.mul_lt_mul_of_lt_of_le (by omega) (Nat.le_refl _) h2
          omega
        · exact hlt
      · rcases Nat.lt_or_eq_of_le hx with hlt | hlt
        · exfalso
          have : (M b' + 1) * M x' < (M b' + 1) * M x := Nat.mul_lt_mul_of_le_of_lt (Nat.le_refl _) hlt (by omega)
          have : (M b' + 1) * M x ≤ (M b + 1) * M x := Nat.mul_le_mul_right _ (by omega)
          omega
        · exact hlt
  | fn f _ =>
    simp only [withChildren] at heq
    by_cases hd : f = "diff" ∧ cs.length = 2
    · obtain ⟨rfl, hl⟩ := hd
      match cs, cs', hl, hlen', h with
      | [g, t], [g', t'], _, _, ⟨hg, ht, _⟩ =>
        rw [M.diff, M.diff] at heq
        refine ⟨?_, ?_, trivial⟩
        · rcases Nat.lt_or_eq_of_le hg with hlt | hlt
          · exfalso; have := Nat.pow_lt_pow_right (a := 3) (by decide) (Nat.add_lt_add_right hlt 3); omega
          · exact hlt
        · have := Nat.pow_le_pow_right (n := 3) (by decide) (Nat.add_le_add_right hg 3); omega
    · rw [M.fn f cs hd, M.fn f cs' (by rw [hlen']; exact hd)] at heq
      exact ML.eq_of_rel h (by omega)
  | matrix rows =>
    simp only [withChildren, M.matrix, MR.flatten] at heq
    simp only [children] at hlen
    rw [flatten_regroup rows cs hlen, flatten_regroup rows cs' (hlen'.trans hlen)] at heq
    exact ML.eq_of_rel h (by omega)

theorem size_withChildren (e : Expr) (cs : List Expr) (hlen : cs.length = (children e).length) :
    size (withChildren e cs) = 1 + sizeList cs := by
  rw [size_eq, children_withChildren e cs hlen]

/-- Replacing the children by lexicographically smaller-or-equal ones makes the node
lexicographically smaller-or-equal. Tier by tier: a strict decrease in the first tier where some
child decreases; before that tier every child is equal. -/
theorem μ_withChildren_le (e : Expr) {cs' cs : List Expr} (hlen : cs.length = (children e).length)
    (h : RelList (fun a b => MuLe (μ a) (μ b)) cs' cs) :
    MuLe (μ (withChildren e cs')) (μ (withChildren e cs)) := by
  have hlen' := RelList_length h
  have hlen'' : cs'.length = (children e).length := hlen'.trans hlen
  have hE := fun (a b : Expr) (hab : MuLe (μ a) (μ b)) => (MuLe.elim hab)
  simp only [μ] at hE
  -- tier 1
  have t1 : RelList (fun a b => cmdCount a ≤ cmdCount b) cs' cs := h.imp fun a b hab => (hE a b hab).1
  have lit3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs →
      litOwn (withChildren e cs') ≤ litOwn (withChildren e cs) := by
    intro t3
    simp only [litOwn, hasLit_withChildren e cs hlen, hasLit_withChildren e cs' hlen'']
    split
    · split
      · exact Nat.le_refl _
      · rename_i h1 h2
        exfalso; apply h2
        rw [Bool.or_eq_true] at h1 ⊢
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · right
          rw [hasLitList_iff] at h1 ⊢
          obtain ⟨a, ha, hl⟩ := h1
          obtain ⟨b, hb, hab⟩ := Expr.RelList.mem_right t3 a ha
          refine ⟨b, hb, hasLit_of_count_pos ?_⟩
          have hc : 0 < count litOwn a := by rw [count_eq]; simp only [litOwn, hl, ↓reduceIte]; omega
          exact Nat.lt_of_lt_of_le hc hab
    · exact Nat.zero_le _
  simp only [μ, cmdCount, d3Count, litCount, numCount, count_withChildren cmdOwn_head e _ hlen,
    count_withChildren cmdOwn_head e _ hlen'', count_withChildren d3Own_head e _ hlen,
    count_withChildren d3Own_head e _ hlen'', count_withChildren numOwn_head e _ hlen,
    count_withChildren numOwn_head e _ hlen'',
    count_eq (e := withChildren e cs), count_eq (e := withChildren e cs'),
    children_withChildren e cs hlen, children_withChildren e cs' hlen'',
    size_withChildren e _ hlen, size_withChildren e _ hlen'']
  refine muLe_of (Nat.add_le_add_left (countList_le_of_rel _ t1) _) ?_ ?_ ?_ ?_ ?_
  · intro e1
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    exact Nat.add_le_add_left (countList_le_of_rel _ t2) _
  · intro e1 e2
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    have e2' := countList_eq_of_rel _ t2 (by omega)
    have t3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs :=
      ((h.and e1').and e2').imp fun a b ⟨⟨hab, hc⟩, hd⟩ => (hE a b hab).2.2.1 hc hd
    exact Nat.add_le_add (lit3 t3) (countList_le_of_rel _ t3)
  · intro e1 e2 e3
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    have e2' := countList_eq_of_rel _ t2 (by omega)
    have t3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs :=
      ((h.and e1').and e2').imp fun a b ⟨⟨hab, hc⟩, hd⟩ => (hE a b hab).2.2.1 hc hd
    have e3' := countList_eq_of_rel _ t3 (by have := lit3 t3; have := countList_le_of_rel _ t3; omega)
    have t4 : RelList (fun a b => M a ≤ M b) cs' cs :=
      (((h.and e1').and e2').and e3').imp fun a b ⟨⟨⟨hab, hc⟩, hd⟩, hl⟩ => (hE a b hab).2.2.2.1 hc hd hl
    exact M.withChildren_le e hlen t4
  · intro e1 e2 e3 e4
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    have e2' := countList_eq_of_rel _ t2 (by omega)
    have t3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs :=
      ((h.and e1').and e2').imp fun a b ⟨⟨hab, hc⟩, hd⟩ => (hE a b hab).2.2.1 hc hd
    have e3' := countList_eq_of_rel _ t3 (by have := lit3 t3; have := countList_le_of_rel _ t3; omega)
    have t4 : RelList (fun a b => M a ≤ M b) cs' cs :=
      (((h.and e1').and e2').and e3').imp fun a b ⟨⟨⟨hab, hc⟩, hd⟩, hl⟩ => (hE a b hab).2.2.2.1 hc hd hl
    have e4' := M.withChildren_eq e hlen t4 e4
    have t5 : RelList (fun a b => size a ≤ size b) cs' cs :=
      ((((h.and e1').and e2').and e3').and e4').imp fun a b ⟨⟨⟨⟨hab, hc⟩, hd⟩, hl⟩, hm⟩ =>
        (hE a b hab).2.2.2.2.1 hc hd hl hm
    exact Nat.add_le_add_left (sizeList_le_of_rel t5) _
  · intro e1 e2 e3 e4 e5
    have e1' := countList_eq_of_rel _ t1 (by omega)
    have t2 : RelList (fun a b => d3Count a ≤ d3Count b) cs' cs :=
      (h.and e1').imp fun a b ⟨hab, hc⟩ => (hE a b hab).2.1 hc
    have e2' := countList_eq_of_rel _ t2 (by omega)
    have t3 : RelList (fun a b => litCount a ≤ litCount b) cs' cs :=
      ((h.and e1').and e2').imp fun a b ⟨⟨hab, hc⟩, hd⟩ => (hE a b hab).2.2.1 hc hd
    have e3' := countList_eq_of_rel _ t3 (by have := lit3 t3; have := countList_le_of_rel _ t3; omega)
    have t4 : RelList (fun a b => M a ≤ M b) cs' cs :=
      (((h.and e1').and e2').and e3').imp fun a b ⟨⟨⟨hab, hc⟩, hd⟩, hl⟩ => (hE a b hab).2.2.2.1 hc hd hl
    have e4' := M.withChildren_eq e hlen t4 e4
    have t5 : RelList (fun a b => size a ≤ size b) cs' cs :=
      ((((h.and e1').and e2').and e3').and e4').imp fun a b ⟨⟨⟨⟨hab, hc⟩, hd⟩, hl⟩, hm⟩ =>
        (hE a b hab).2.2.2.2.1 hc hd hl hm
    have e5' := sizeList_eq_of_rel t5 (by omega)
    have t6 : RelList (fun a b => numCount a ≤ numCount b) cs' cs :=
      (((((h.and e1').and e2').and e3').and e4').and e5').imp fun a b ⟨⟨⟨⟨⟨hab, hc⟩, hd⟩, hl⟩, hm⟩, hs⟩ =>
        (hE a b hab).2.2.2.2.2 hc hd hl hm hs
    exact Nat.add_le_add_left (countList_le_of_rel _ t6) _

theorem children_canon_perm (e : Expr) : (children (canon e)).Perm (children e) := by
  cases e with
  | add es => exact List.mergeSort_perm es leAdd
  | mul es =>
    simp only [canon]; split
    · exact List.Perm.refl _
    · exact List.mergeSort_perm es leMul
  | _ => exact List.Perm.refl _

-- ---------------------------------------------------------------------------
-- Chains: a sum of sums, or a product of products, opened in one step
-- ---------------------------------------------------------------------------

/-! A chain is a sum with a sum among its terms, or a product with a product among its factors:
`x*x*…*x` as the parser reads it, `((x·x)·x)·…`, or `-…-x`, `-1·(-1·(…))`, or a sum a rule builds
(the parser opens the sums it reads, `openSpine`). Normalized innermost, a chain is worked at every
level, each level a step whose path is as long as the chain is deep, and a product of `n` distinct
factors is flattened, sorted and searched `n` times over. So before the rewriter descends into a
chain, it opens the whole chain at once:
`simp.flatten` (associativity), all the way down, as one silent step. It decreases `μ` on any term,
normal children or not (`openChain_lt`): the counting tiers are unchanged, `M` does not grow, and
`size` drops. A chain with a matrix literal in it is left to the rules, which leave a node with a
literal among its children to the matrix rules (`scalarOnly`). -/

mutual
  /-- The summands of `e`, `add` nodes opened all the way down, in order, before `acc`. -/
  def addArgs : Expr → List Expr → List Expr
    | .add es, acc => addArgsList es acc
    | e, acc => e :: acc
  def addArgsList : List Expr → List Expr → List Expr
    | [], acc => acc
    | e :: es, acc => addArgs e (addArgsList es acc)
end

mutual
  /-- The factors of `e`, `mul` nodes opened all the way down, in order, before `acc`. -/
  def mulArgs : Expr → List Expr → List Expr
    | .mul es, acc => mulArgsList es acc
    | e, acc => e :: acc
  def mulArgsList : List Expr → List Expr → List Expr
    | [], acc => acc
    | e :: es, acc => mulArgs e (mulArgsList es acc)
end

def isAddNode : Expr → Bool | .add _ => true | _ => false
def isMulNode : Expr → Bool | .mul _ => true | _ => false

/-- A chain opened: a sum with a sum among its terms, or a product with a product among its factors,
without a matrix literal anywhere in it. -/
def openChain : Expr → Option Expr
  | .add es =>
    if es.any isAddNode && !hasLitList es then
      let l := addArgsList es []
      if l.isEmpty then none else some (.add l)
    else none
  | .mul es => if es.any isMulNode && !hasLitList es then some (.mul (mulArgsList es [])) else none
  | _ => none

section chains

theorem M_add_ne_nil' {es : List Expr} (h : es ≠ []) : M (.add es) = ML es := by
  cases es with
  | nil => exact absurd rfl h
  | cons e es => rw [M.add_cons, ML.cons]

mutual
  theorem countList_addArgs (own : Expr → Nat) (h0 : ∀ xs, own (.add xs) = 0) :
      ∀ (e : Expr) (acc : List Expr), countList own (addArgs e acc) = count own e + countList own acc
    | .add es, acc => by rw [addArgs, countList_addArgsList own h0 es acc, count, h0]; omega
    | .num _, _ | .var _, _ | .mul _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by simp [addArgs, countList]
  theorem countList_addArgsList (own : Expr → Nat) (h0 : ∀ xs, own (.add xs) = 0) :
      ∀ (es acc : List Expr), countList own (addArgsList es acc) = countList own es + countList own acc
    | [], acc => by simp [addArgsList, countList]
    | e :: es, acc => by
      rw [addArgsList, countList_addArgs own h0 e, countList_addArgsList own h0 es acc, countList]; omega
end

mutual
  theorem countList_mulArgs (own : Expr → Nat) (h0 : ∀ xs, own (.mul xs) = 0) :
      ∀ (e : Expr) (acc : List Expr), countList own (mulArgs e acc) = count own e + countList own acc
    | .mul es, acc => by rw [mulArgs, countList_mulArgsList own h0 es acc, count, h0]; omega
    | .num _, _ | .var _, _ | .add _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by simp [mulArgs, countList]
  theorem countList_mulArgsList (own : Expr → Nat) (h0 : ∀ xs, own (.mul xs) = 0) :
      ∀ (es acc : List Expr), countList own (mulArgsList es acc) = countList own es + countList own acc
    | [], acc => by simp [mulArgsList, countList]
    | e :: es, acc => by
      rw [mulArgsList, countList_mulArgs own h0 e, countList_mulArgsList own h0 es acc, countList]; omega
end

mutual
  theorem hasLitList_addArgs : ∀ (e : Expr) (acc : List Expr),
      hasLitList (addArgs e acc) = (hasLit e || hasLitList acc)
    | .add es, acc => by rw [addArgs, hasLitList_addArgsList es acc, hasLit]
    | .num _, _ | .var _, _ | .mul _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by simp [addArgs, hasLitList]
  theorem hasLitList_addArgsList : ∀ (es acc : List Expr),
      hasLitList (addArgsList es acc) = (hasLitList es || hasLitList acc)
    | [], acc => by simp [addArgsList, hasLitList]
    | e :: es, acc => by
      rw [addArgsList, hasLitList_addArgs e, hasLitList_addArgsList es acc, hasLitList, Bool.or_assoc]
end

mutual
  theorem hasLitList_mulArgs : ∀ (e : Expr) (acc : List Expr),
      hasLitList (mulArgs e acc) = (hasLit e || hasLitList acc)
    | .mul es, acc => by rw [mulArgs, hasLitList_mulArgsList es acc, hasLit]
    | .num _, _ | .var _, _ | .add _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by simp [mulArgs, hasLitList]
  theorem hasLitList_mulArgsList : ∀ (es acc : List Expr),
      hasLitList (mulArgsList es acc) = (hasLitList es || hasLitList acc)
    | [], acc => by simp [mulArgsList, hasLitList]
    | e :: es, acc => by
      rw [mulArgsList, hasLitList_mulArgs e, hasLitList_mulArgsList es acc, hasLitList, Bool.or_assoc]
end

-- Opening a chain never adds weight (`M (add xs) ≥ ML xs`, and a product's node costs more than
-- its factors), and each node opened is one fewer.
mutual
  theorem addArgs_le : ∀ (e : Expr) (acc : List Expr),
      ML (addArgs e acc) ≤ M e + ML acc ∧ sizeList (addArgs e acc) ≤ size e + sizeList acc ∧
        (isAddNode e = true → sizeList (addArgs e acc) < size e + sizeList acc)
    | .add es, acc => by
      have ih := addArgsList_le es acc
      have hM : ML es ≤ M (.add es) := by cases es <;> simp [M.add_nil, M.add_cons, ML]
      rw [addArgs, size]; refine ⟨by omega, by omega, fun _ => by omega⟩
    | .num _, _ | .var _, _ | .mul _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by
      simp [addArgs, ML, sizeList, isAddNode]
  theorem addArgsList_le : ∀ (es acc : List Expr),
      ML (addArgsList es acc) ≤ ML es + ML acc ∧ sizeList (addArgsList es acc) ≤ sizeList es + sizeList acc ∧
        (es.any isAddNode = true → sizeList (addArgsList es acc) < sizeList es + sizeList acc)
    | [], acc => by simp [addArgsList, ML, sizeList]
    | e :: es, acc => by
      have ih := addArgsList_le es acc
      have he := addArgs_le e (addArgsList es acc)
      rw [addArgsList, ML, sizeList]
      refine ⟨by omega, by omega, fun h => ?_⟩
      rw [List.any_cons, Bool.or_eq_true] at h
      rcases h with h | h
      · have := he.2.2 h; omega
      · have := ih.2.2 h; omega
end

mutual
  theorem mulArgs_le : ∀ (e : Expr) (acc : List Expr),
      ML (mulArgs e acc) + 2 * (mulArgs e acc).length ≤ M e + 2 + ML acc + 2 * acc.length ∧
      sizeList (mulArgs e acc) ≤ size e + sizeList acc ∧
        (isMulNode e = true → sizeList (mulArgs e acc) < size e + sizeList acc)
    | .mul es, acc => by
      have ih := mulArgsList_le es acc
      rw [mulArgs, size, M.mul]; refine ⟨by omega, by omega, fun _ => by omega⟩
    | .num _, _ | .var _, _ | .add _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by
      simp [mulArgs, ML, sizeList, isMulNode]; omega
  theorem mulArgsList_le : ∀ (es acc : List Expr),
      ML (mulArgsList es acc) + 2 * (mulArgsList es acc).length ≤ ML es + 2 * es.length + ML acc + 2 * acc.length ∧
      sizeList (mulArgsList es acc) ≤ sizeList es + sizeList acc ∧
        (es.any isMulNode = true → sizeList (mulArgsList es acc) < sizeList es + sizeList acc)
    | [], acc => by simp [mulArgsList, ML, sizeList]
    | e :: es, acc => by
      have ih := mulArgsList_le es acc
      have he := mulArgs_le e (mulArgsList es acc)
      rw [mulArgsList, ML, sizeList, List.length_cons]
      refine ⟨by omega, by omega, fun h => ?_⟩
      rw [List.any_cons, Bool.or_eq_true] at h
      rcases h with h | h
      · have := he.2.2 h; omega
      · have := ih.2.2 h; omega
end

theorem count_litOwn_of_not_hasLit {e : Expr} (h : hasLit e = false) : count litOwn e = 0 := by
  cases hc : count litOwn e with
  | zero => rfl
  | succ n => have := hasLit_of_count_pos (e := e) (by omega); simp [h] at this

/-- Opening a chain decreases `μ`, whatever the children: the step needs no `ChildrenNormal`. -/
theorem openChain_lt {e e' : Expr} (h : openChain e = some e') : MuLt (μ e') (μ e) := by
  cases e with
  | add es =>
    simp only [openChain] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      split at h
      · cases h
      · rename_i hl
        cases h
        have hl : addArgsList es [] ≠ [] := by simpa using hl
        have hne : es ≠ [] := by cases es <;> simp_all
        have hle := addArgsList_le es []
        have hs := hle.2.2 hc.1
        simp only [ML.nil, sizeList, Nat.add_zero] at hle hs
        have hlit : hasLit (.add (addArgsList es [])) = false := by
          simp [hasLit, hasLitList_addArgsList, hc.2, hasLitList]
        simp only [μ, cmdCount, d3Count, litCount]
        rw [count_litOwn_of_not_hasLit hlit, count_litOwn_of_not_hasLit (e := .add es) (by simp [hasLit, hc.2])]
        simp only [count, countList_addArgsList cmdOwn (fun _ => rfl), countList_addArgsList d3Own (fun _ => rfl),
          M_add_ne_nil' hne, M_add_ne_nil' hl, size, cmdOwn, d3Own, countList]
        exact muLt_of (by omega) (fun _ => by omega) (fun _ _ => by omega) (fun _ _ _ => hle.1)
          (fun _ _ _ _ => by omega) (fun _ _ _ _ h5 => by omega)
    · cases h
  | mul es =>
    simp only [openChain] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      cases h
      have hle := mulArgsList_le es []
      have hs := hle.2.2 hc.1
      simp only [ML.nil, sizeList, Nat.add_zero, List.length_nil, Nat.mul_zero] at hle hs
      have hlit : hasLit (.mul (mulArgsList es [])) = false := by
        simp [hasLit, hasLitList_mulArgsList, hc.2, hasLitList]
      simp only [μ, cmdCount, d3Count, litCount]
      rw [count_litOwn_of_not_hasLit hlit, count_litOwn_of_not_hasLit (e := .mul es) (by simp [hasLit, hc.2])]
      simp only [count, countList_mulArgsList cmdOwn (fun _ => rfl), countList_mulArgsList d3Own (fun _ => rfl),
        M.mul, size, cmdOwn, d3Own, countList]
      exact muLt_of (by omega) (fun _ => by omega) (fun _ _ => by omega) (fun _ _ _ => by omega)
        (fun _ _ _ _ => by omega) (fun _ _ _ _ h5 => by omega)
    · cases h
  | _ => simp [openChain] at h

end chains

-- ---------------------------------------------------------------------------
-- The rewriter
-- ---------------------------------------------------------------------------

structure TState where
  tape : Array Record := #[]
  error : Option String := none

/-- What `normAtT` promises about its result: no heavier than the input, and normal unless a rule
refused. -/
def Promise (rules : List PlainRule) (e : Expr) (st : TState) (r : Expr × TState) : Prop :=
  MuLe (μ r.1) (μ e) ∧ (r.2.error = none → Normal rules r.1) ∧ (r.2.error = none → st.error = none)

def PromiseList (rules : List PlainRule) (cs : List Expr) (st : TState) (r : List Expr × TState) : Prop :=
  RelList (fun a b => MuLe (μ a) (μ b)) r.1 cs ∧ (r.2.error = none → ∀ c ∈ r.1, Normal rules c) ∧
    (r.2.error = none → st.error = none)

/-! The rewriter records a tape (`Record`, Rewrite.lean): its moves into, along and out of a node's
children, and its firings; a firing carries no path, so no node costs its depth. `buildSteps`
replays the tape from the input to give each visible step its path and whole-term snapshots.

A rule's result is normalized again from the top, and a result is mostly made of the children of
the node the rule fired on, which are already normal (`ChildrenNormal` is the hypothesis the firing
needed). Walking them again would cost every firing the size of its node: `√(√(…√x))` fires a
silent `simp.sqrt` at every level, so that was quadratic in the depth. So the recursive call after
a firing carries those children as terms known to be normal (`known`, with the proof), and
`normChildrenT` returns a child of a result that is `equal` to one of them as it is. `equal` runs
as `beqFast` (Expr.lean), so a shared child is recognised by its pointer; the terms a rule builds
share the children it was given, and a known term it does not share is told apart at the first
difference. -/
mutual
  def normAtT (rules : List PlainRule) (ord : Ordered rules) (e : Expr) (known : List Expr)
      (hkn : ∀ k ∈ known, Normal rules k) (st : TState) :
      {r : Expr × TState // Promise rules e st r} :=
    -- a chain is opened before its children are worked (`openChain`)
    match hoc : openChain e with
    | some e' =>
      have hlt : MuLt (μ e') (μ e) := openChain_lt hoc
      let st' : TState := { st with tape := st.tape.push (.fire ⟨"simp.flatten", true, "associativity", e', none⟩) }
      match normAtT rules ord e' known hkn st' with
      | ⟨r, hr⟩ => ⟨r, hr.1.trans (Or.inl hlt), hr.2.1, hr.2.2⟩
    | none =>
    match normChildrenT rules ord e (children e) (fun _ h => h) known hkn 0 st with
    | ⟨(cs, st₀), hcs⟩ =>
      have hlen : cs.length = (children e).length := RelList_length hcs.1
      let e₀ := withChildren e cs
      let e₁ := canon e₀
      let st₁ := if equal e₁ e₀ then st₀ else { st₀ with tape := st₀.tape.push (.fire ⟨"simp.sort", true, "commutativity", e₁, none⟩) }
      have hst₁ : st₁.error = st₀.error := by simp only [st₁]; split <;> rfl
      have h₁ : MuLe (μ e₁) (μ e) := by
        have := μ_withChildren_le e (cs' := cs) (cs := children e) rfl hcs.1
        rw [withChildren_children'] at this
        simp only [e₁, μ_canon]; exact this
      have hnorm : st₀.error = none → ChildrenNormal rules e₁ := fun herr c hc => by
        have hc' := (children_canon_perm e₀).mem_iff.mp hc
        rw [children_withChildren e cs hlen] at hc'
        exact hcs.2.1 herr c hc'
      if herr : st₁.error.isSome then
        ⟨(e₁, st₁), h₁, fun h => by have h' : st₁.error = none := h; simp [h'] at herr,
          fun h => by have h' : st₁.error = none := h; simp [h'] at herr⟩ else
      match hf : fireP rules e₁ with
      | none => ⟨(e₁, st₁), h₁, fun h => ⟨e₁, noFire_of_fireP_none rules e₁ hf, hnorm (hst₁ ▸ h)⟩,
          fun h => hcs.2.2 (hst₁ ▸ h)⟩
      | some (rule, res) =>
        if hres : res.error.isSome then
          ⟨(e₁, { st₁ with error := res.error }), h₁, fun h => by have h' : res.error = none := h; simp [h'] at hres,
            fun h => by have h' : res.error = none := h; simp [h'] at hres⟩ else
        have hnone : st₀.error = none := by
          rw [← hst₁]; cases h : st₁.error with | none => rfl | some => simp [h] at herr
        have hdec : MuLt (μ res.result) (μ e₁) :=
          ord.decreasing rule (fireP_spec rules e₁ hf).1 e₁ res (hnorm hnone) (fireP_spec rules e₁ hf).2
            (by cases h : res.error with | none => rfl | some => simp [h] at hres)
        let st₂ : TState := { st₁ with tape := st₁.tape.push (.fire ⟨rule.name, rule.silent, res.explanation, res.result, res.sub⟩) }
        have hst₂ : st₂.error = st₀.error := hst₁
        -- the result is worked with the children it was built from known to be normal
        match normAtT rules ord res.result cs (hcs.2.1 hnone) st₂ with
        | ⟨r, hr⟩ => ⟨r, hr.1.trans (Or.inl (hdec.trans_le h₁)), hr.2.1, fun h => hcs.2.2 (hst₂ ▸ hr.2.2 h)⟩
  termination_by (μ e, 1, 0)
  decreasing_by
    · exact Prod.Lex.left _ _ hlt
    · exact Prod.Lex.right _ (Prod.Lex.left _ _ Nat.zero_lt_one)
    · exact Prod.Lex.left _ _ (hdec.trans_le h₁)

  /-- The children from index `i` on: a move into the first, to each next one, and back out. -/
  def normChildrenT (rules : List PlainRule) (ord : Ordered rules) (parent : Expr) (cs : List Expr)
      (hsub : ∀ c ∈ cs, c ∈ children parent) (known : List Expr) (hkn : ∀ k ∈ known, Normal rules k)
      (i : Nat) (st : TState) :
      {r : List Expr × TState // PromiseList rules cs st r} :=
    match cs with
    | [] =>
      let st' : TState := if i = 0 then st else { st with tape := st.tape.push .up }
      have hst' : st'.error = st.error := by simp only [st']; split <;> rfl
      ⟨([], st'), trivial, fun _ _ h => by simp at h, fun h => hst' ▸ h⟩
    | c :: cs' =>
      let st' : TState := { st with tape := st.tape.push (if i = 0 then .down else .next) }
      have hst' : st'.error = st.error := rfl
      match hk : known.find? (equal c) with
      | some k =>
        -- `c` is a known normal term: left as it is, no firings inside
        have hck : c = k := beq_eq c k (by simpa [equal] using List.find?_some hk)
        have hnc : Normal rules c := hck ▸ hkn k (List.mem_of_find?_eq_some hk)
        match normChildrenT rules ord parent cs' (fun d hd => hsub d (List.mem_cons_of_mem _ hd)) known hkn (i + 1) st' with
        | ⟨(cs'', st₂), hcs⟩ =>
          ⟨(c :: cs'', st₂), ⟨Or.inr rfl, hcs.1⟩, fun herr d hd => by
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hnc
            · exact hcs.2.1 herr d hd, fun herr => hst' ▸ hcs.2.2 herr⟩
      | none =>
      match normAtT rules ord c known hkn st' with
      | ⟨(c', st₁), hc⟩ =>
        match normChildrenT rules ord parent cs' (fun d hd => hsub d (List.mem_cons_of_mem _ hd)) known hkn (i + 1) st₁ with
        | ⟨(cs'', st₂), hcs⟩ =>
          ⟨(c' :: cs'', st₂), ⟨hc.1, hcs.1⟩, fun herr d hd => by
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hc.2.1 (hcs.2.2 herr)
            · exact hcs.2.1 herr d hd, fun herr => hst' ▸ hc.2.2 (hcs.2.2 herr)⟩
  termination_by (μ parent, 0, cs.length)
  decreasing_by
    · exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self _))
    · exact Prod.Lex.left _ _ (μ_child_lt (hsub c List.mem_cons_self))
    · exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.lt_succ_self _))
end

/-- Normalize under an ordered rule set. Fails only if a rule refused. -/
def normalizeT (rules : List PlainRule) (ord : Ordered rules) (e : Expr) : TraceM (Except String Expr) := do
  let ⟨(out, st), _⟩ := normAtT rules ord e [] (fun _ h => by simp at h) {}
  match st.error with
  | some msg => pure (.error msg)
  | none =>
    let (steps, _) := buildSteps e st.tape
    modify (· ++ steps)
    pure (.ok out)

end MathEngine
