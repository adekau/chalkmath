import MathEngine.Systems
/-!
# What is proved about fair runs

`eventually(S, φ)` asks whether every fair run of a system reaches φ. The systems world answers with
something checked (`Sys.Fair.check*`, `Systems.lean`), and each check is proved here against the
meaning of a fair run over the graph's edges (which `System.explore_edges` proves are exactly the
system's steps between reachable states):

- `checkLasso_spec`: a lasso that checks is a fair infinite run from an initial state that never
  reaches φ, so the answer `false` is right.
- `checkDead_spec`: a path that checks is a run from an initial state that stops at a deadlock without
  reaching φ, so the answer `false` is right.
- `checkTrue_spec`: a certificate that checks means every fair infinite run from an initial state
  reaches φ, and so does every run that stops at a deadlock, so the answer `true` is right.

A run is a pair of functions `ℕ → ℕ`, its states and the actions it takes. It is fair when every weakly
fair action that is enabled from some point on is taken again and again, and every strongly fair
action that is enabled again and again is taken again and again (`IsFair`).

The certificate for `true` is a list of nodes, each with a rank and a helpful action per state
(`Node`). `noFair` is the heart of it: along a run that stays in a node's set the rank never rises, so
from some point it is level; there the helpful action is the same at every state and never taken. A
weakly fair helpful action is enabled all along, so the run is unfair. A strongly fair one is then
enabled only finitely often, so the run ends up in the later node holding the states where it is
disabled, and that node's own certificate rules the run out, by induction on the nodes.
-/
namespace MathEngine
namespace Sys
namespace Fair

section
variable (G : Graph)

/-- An infinite run: states `s`, and at each step the action `l` taken along an edge. -/
def IsRun (s l : Nat → Nat) : Prop := ∀ i, (s i, l i, s (i + 1)) ∈ G.edges

/-- Weakly fair actions enabled from some point on are taken again and again; strongly fair ones
enabled again and again are taken again and again. -/
def IsFair (s l : Nat → Nat) : Prop :=
  (∀ a ∈ G.weak, ∀ i, ∃ j, i ≤ j ∧ (G.en a (s j) = false ∨ l j = a)) ∧
  (∀ a ∈ G.strong, (∀ i, ∃ j, i ≤ j ∧ G.en a (s j) = true) → ∀ i, ∃ j, i ≤ j ∧ l j = a)

/-- No step from `x`. -/
def Dead (x : Nat) : Prop := ∀ a y, (x, a, y) ∉ G.edges
end

theorem le_rec {M : Nat} {P : Nat → Prop} (h0 : P M) (hs : ∀ k, M ≤ k → P k → P (k + 1)) :
    ∀ k, M ≤ k → P k := by
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction d with
  | zero => exact h0
  | succ d ih => exact hs _ (Nat.le_add_right _ _) (ih (Nat.le_add_right _ _))

/-- A sequence of naturals that never rises from `N` on is constant from some point. -/
theorem eventually_const (f : Nat → Nat) (N : Nat) (h : ∀ k, N ≤ k → f (k + 1) ≤ f k) :
    ∃ M, N ≤ M ∧ ∀ k, M ≤ k → f k = f M := by
  have mono : ∀ M, N ≤ M → ∀ k, M ≤ k → f k ≤ f M := by
    intro M hM
    exact le_rec (Nat.le_refl _) fun k hk ih => Nat.le_trans (h k (Nat.le_trans hM hk)) ih
  suffices ∀ v M, N ≤ M → f M ≤ v → ∃ M', N ≤ M' ∧ ∀ k, M' ≤ k → f k = f M' from
    this _ N (Nat.le_refl _) (Nat.le_refl _)
  intro v
  induction v with
  | zero => exact fun M hM hv => ⟨M, hM, fun k hk => by have := mono M hM k hk; omega⟩
  | succ v ih =>
    intro M hM hv
    by_cases hc : ∀ k, M ≤ k → f k = f M
    · exact ⟨M, hM, hc⟩
    · have ⟨k, hk, hne⟩ : ∃ k, M ≤ k ∧ f k ≠ f M :=
        Classical.byContradiction fun hn => hc fun k hk =>
          Classical.byContradiction fun hne => hn ⟨k, hk, hne⟩
      have := mono M hM k hk
      exact ih k (Nat.le_trans hM hk) (by omega)

theorem edgeOk_le {nd : Node} {x a y : Nat} (h : edgeOk nd (x, a, y) = true) (hx : nd.mem x = true)
    (hy : nd.mem y = true) : nd.rank y ≤ nd.rank x := by
  simp only [edgeOk, hx, hy, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h.1

theorem edgeOk_level {nd : Node} {x a y : Nat} (h : edgeOk nd (x, a, y) = true) (hx : nd.mem x = true)
    (hy : nd.mem y = true) (he : nd.rank y = nd.rank x) :
    ∃ b c, nd.help x = some (b, c) ∧ a ≠ b ∧ nd.help y = nd.help x := by
  simp only [edgeOk, hx, hy, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq, he, ne_eq, not_true_eq_false, decide_false] at h
  obtain ⟨_, h⟩ := h
  revert h
  cases hh : nd.help x with
  | none => simp
  | some p =>
    obtain ⟨b, c⟩ := p
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    intro ⟨hab, hy⟩
    exact ⟨b, c, rfl, hab, hy⟩

theorem mem_edges_lt {G : Graph} (hR : inRange G = true) {e : Nat × Nat × Nat} (he : e ∈ G.edges) :
    e.1 < G.n ∧ e.2.2 < G.n := by
  simp only [inRange, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hR
  exact hR e he

/-- No fair run stays, from some point on, in the set of a node of a certificate that checks. -/
theorem noFair {G : Graph} {nodes : List Node} (hc : checkNodes G nodes = true) (i : Nat) (nd : Node)
    (hi : nodes[i]? = some nd) (s l : Nat → Nat) (hr : IsRun G s l) (hf : IsFair G s l) (N : Nat)
    (hN : ∀ k, N ≤ k → nd.mem (s k) = true) : False := by
  have hc' := hc
  simp only [checkNodes, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc'
  obtain ⟨hR, hall⟩ := hc'
  have hil : i < nodes.length := (List.getElem?_eq_some_iff.mp hi).1
  have hnd := hall i hil
  rw [hi] at hnd
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hnd
  obtain ⟨hE, hS⟩ := hnd
  have rank_le : ∀ k, N ≤ k → nd.rank (s (k + 1)) ≤ nd.rank (s k) := fun k hk =>
    edgeOk_le (hE _ (hr k)) (hN k hk) (hN (k + 1) (by omega))
  obtain ⟨M, hNM, hM⟩ := eventually_const (fun k => nd.rank (s k)) N rank_le
  have level : ∀ k, M ≤ k → ∃ b c, nd.help (s k) = some (b, c) ∧ l k ≠ b ∧
      nd.help (s (k + 1)) = nd.help (s k) := fun k hk =>
    edgeOk_level (hE _ (hr k)) (hN k (by omega)) (hN (k + 1) (by omega))
      (by rw [hM (k + 1) (by omega), hM k hk])
  have const : ∀ k, M ≤ k → nd.help (s k) = nd.help (s M) := by
    refine le_rec rfl fun k hk ih => ?_
    obtain ⟨_, _, _, _, h⟩ := level k hk
    rw [h, ih]
  obtain ⟨a, c, hac, -, -⟩ := level M (Nat.le_refl _)
  have notTaken : ∀ k, M ≤ k → l k ≠ a := by
    intro k hk
    obtain ⟨b, c', hb, hlb, -⟩ := level k hk
    rw [const k hk, hac] at hb
    cases hb
    exact hlb
  have st : ∀ k, M ≤ k → stateOk G nodes i nd (s k) = true := fun k _ =>
    hS _ (mem_edges_lt hR (hr k)).1
  have help : ∀ k, M ≤ k → nd.help (s k) = some (a, c) := fun k hk => by rw [const k hk, hac]
  cases c with
  | none =>
    have hen : ∀ k, M ≤ k → a ∈ G.weak ∧ G.en a (s k) = true := by
      intro k hk
      have := st k hk
      simp only [stateOk, hN k (by omega), help k hk, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        List.contains_iff_mem] at this
      exact this
    obtain ⟨j, hj, hj'⟩ := hf.1 a (hen M (Nat.le_refl _)).1 M
    rcases hj' with h | h
    · rw [(hen j hj).2] at h; cases h
    · exact notTaken j hj h
  | some j =>
    have hst : ∀ k, M ≤ k → a ∈ G.strong ∧ i < j ∧
        (G.en a (s k) = true ∨ (match nodes[j]? with | some c => c.mem (s k) | none => false) = true) := by
      intro k hk
      have := st k hk
      simp only [stateOk, hN k (by omega), help k hk, Bool.not_true, Bool.false_or, Bool.and_eq_true,
        Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    have ⟨haS, hij, _⟩ := hst M (Nat.le_refl _)
    by_cases hinf : ∀ i', ∃ j', i' ≤ j' ∧ G.en a (s j') = true
    · obtain ⟨j', hj', hl⟩ := hf.2 a haS hinf M
      exact notTaken j' hj' hl
    · have ⟨i0, hi0⟩ : ∃ i0, ∀ j', i0 ≤ j' → G.en a (s j') = false :=
        Classical.byContradiction fun hn => hinf fun i' =>
          Classical.byContradiction fun hn' => hn ⟨i', fun j' hj' => by
            cases h : G.en a (s j') with
            | false => rfl
            | true => exact absurd ⟨j', hj', h⟩ hn'⟩
      have inChild : ∀ k, max M i0 ≤ k → (match nodes[j]? with | some c => c.mem (s k) | none => false) = true := by
        intro k hk
        rcases (hst k (by omega)).2.2 with h | h
        · rw [hi0 k (by omega)] at h; cases h
        · exact h
      cases hj : nodes[j]? with
      | none =>
        have := inChild (max M i0) (Nat.le_refl _)
        rw [hj] at this; cases this
      | some ch =>
        have hjl : j < nodes.length := (List.getElem?_eq_some_iff.mp hj).1
        exact noFair hc j ch hj s l hr hf (max M i0) fun k hk => by
          have := inChild k hk
          rw [hj] at this
          exact this
termination_by nodes.length - i
decreasing_by omega

/-- Where the certificate checks, every fair run from an initial state reaches φ, and so does every run
that stops at a deadlock. -/
theorem checkTrue_spec {G : Graph} {inits : List Nat} {good : Nat → Bool} {nodes : List Node}
    (h : checkTrue G inits good nodes = true) :
    (∀ s l, s 0 ∈ inits → IsRun G s l → IsFair G s l → ∃ i, good (s i) = true) ∧
    (∀ (f : Nat → Nat) (j : Nat), f 0 ∈ inits → (∀ i, i < j → ∃ a, (f i, a, f (i + 1)) ∈ G.edges) →
      Dead G (f j) → ∃ i, i ≤ j ∧ good (f i) = true) := by
  simp only [checkTrue, Bool.and_eq_true] at h
  obtain ⟨⟨hc, hin⟩, h⟩ := h
  simp only [List.all_eq_true, decide_eq_true_eq] at hin
  cases htop : nodes[0]? with
  | none => simp [htop] at h
  | some top =>
    rw [htop] at h
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      List.mem_range, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hinit, hclosed⟩, hlive⟩ := h
    have hR : inRange G = true := by
      simp only [checkNodes, Bool.and_eq_true] at hc; exact hc.1
    -- a run that is never good stays in the first node's set
    have stays : ∀ (f : Nat → Nat) (j : Nat), f 0 ∈ inits →
        (∀ i, i < j → ∃ a, (f i, a, f (i + 1)) ∈ G.edges) → (∀ i, i ≤ j → good (f i) = false) →
        ∀ i, i ≤ j → top.mem (f i) = true := by
      intro f j h0 hstep hbad i hi
      induction i with
      | zero =>
        rcases hinit (f 0) h0 with h | h
        · rw [hbad 0 (Nat.zero_le _)] at h; cases h
        · exact h
      | succ i ih =>
        obtain ⟨a, he⟩ := hstep i (by omega)
        rcases hclosed _ he with (h | h) | h
        · rw [ih (by omega)] at h; cases h
        · rw [hbad (i + 1) hi] at h; cases h
        · exact h
    refine ⟨fun s l h0 hr hf => ?_, fun f j h0 hstep hdead => ?_⟩
    · refine Classical.byContradiction fun hn => ?_
      have hbad : ∀ i, good (s i) = false := fun i => by
        cases hg : good (s i) with
        | false => rfl
        | true => exact absurd ⟨i, hg⟩ hn
      exact noFair hc 0 top htop s l hr hf 0 fun k _ =>
        stays s k h0 (fun i _ => ⟨l i, hr i⟩) (fun i _ => hbad i) k (Nat.le_refl _)
    · refine Classical.byContradiction fun hn => ?_
      have hbad : ∀ i, i ≤ j → good (f i) = false := fun i hi => by
        cases hg : good (f i) with
        | false => rfl
        | true => exact absurd ⟨i, hi, hg⟩ hn
      have hm := stays f j h0 hstep hbad j (Nat.le_refl _)
      have hlt : f j < G.n := by
        cases j with
        | zero =>
          exact hin _ h0
        | succ j =>
          obtain ⟨a, he⟩ := hstep j (by omega)
          exact (mem_edges_lt hR he).2
      obtain ⟨e, he, hex⟩ := (hlive (f j) hlt).resolve_left (by rw [hm]; decide)
      obtain ⟨x, a, y⟩ := e
      simp only at hex
      subst hex
      exact hdead a y he

theorem getD_lt {α : Type} {l : List α} {i : Nat} (h : i < l.length) (d : α) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- Past the stem, the lasso's edges come round the cycle: the `i`th is one checked, below
`pre.length + cyc.length`, and so is the one after it. -/
theorem lassoAt_reduce {pre cyc : List (Nat × Nat × Nat)} (hp : 0 < cyc.length) (i : Nat) :
    ∃ i', i' < pre.length + cyc.length ∧ lassoAt pre cyc i = lassoAt pre cyc i' ∧
      lassoAt pre cyc (i + 1) = lassoAt pre cyc (i' + 1) := by
  by_cases hi : i < pre.length
  · exact ⟨i, by omega, rfl, rfl⟩
  · refine ⟨pre.length + (i - pre.length) % cyc.length, by have := Nat.mod_lt (i - pre.length) hp; omega, ?_, ?_⟩
    · simp only [lassoAt, hi, ite_false, Nat.not_lt.mpr (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, Nat.mod_mod]
    · have h1 : ¬ i + 1 < pre.length := by omega
      have h2 : ¬ pre.length + (i - pre.length) % cyc.length + 1 < pre.length := by omega
      simp only [lassoAt, h1, h2, ite_false]
      congr 1
      rw [show pre.length + (i - pre.length) % cyc.length + 1 - pre.length = (i - pre.length) % cyc.length + 1 by omega,
        Nat.mod_add_mod, show i + 1 - pre.length = i - pre.length + 1 by omega]

/-- Every edge of the cycle comes round again past any point. -/
theorem lassoAt_again {pre cyc : List (Nat × Nat × Nat)} {k : Nat} (hk : k < cyc.length) (i : Nat) :
    ∃ j, i ≤ j ∧ lassoAt pre cyc j = cyc[k] := by
  refine ⟨pre.length + cyc.length * i + k, ?_, ?_⟩
  · have : i ≤ cyc.length * i := Nat.le_mul_of_pos_left i (by omega)
    omega
  · simp only [lassoAt, show ¬ pre.length + cyc.length * i + k < pre.length by omega, ite_false,
      show pre.length + cyc.length * i + k - pre.length = cyc.length * i + k by omega, Nat.mul_add_mod,
      Nat.mod_eq_of_lt hk, getD_lt hk]

/-- Past the stem, the lasso is on the cycle. -/
theorem lassoAt_mem {pre cyc : List (Nat × Nat × Nat)} (hp : 0 < cyc.length) {j : Nat}
    (hj : pre.length ≤ j) : lassoAt pre cyc j ∈ cyc := by
  have hl := Nat.mod_lt (j - pre.length) hp
  simp only [lassoAt, show ¬ j < pre.length by omega, ite_false, getD_lt hl]
  exact List.getElem_mem hl

/-- A lasso that checks is a fair run from an initial state that never reaches φ. -/
theorem checkLasso_spec {G : Graph} {inits : List Nat} {good : Nat → Bool} {pre cyc : List (Nat × Nat × Nat)}
    (h : checkLasso G inits good pre cyc = true) :
    ∃ s l, s 0 ∈ inits ∧ IsRun G s l ∧ IsFair G s l ∧ ∀ i, good (s i) = false := by
  simp only [checkLasso, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.contains_iff_mem, List.all_eq_true, List.mem_range, beq_iff_eq, List.any_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hne, h0⟩, hpath⟩, hweak⟩, hstrong⟩ := h
  have hp : 0 < cyc.length := List.length_pos_iff.mpr hne
  let E := lassoAt pre cyc
  refine ⟨fun i => (E i).1, fun i => (E i).2.1, h0, fun i => ?_, ⟨fun a ha i => ?_, fun a ha hinf i => ?_⟩, fun i => ?_⟩
  · obtain ⟨i', hi', h1, h2⟩ := lassoAt_reduce (pre := pre) hp i
    obtain ⟨⟨hm, hc⟩, -⟩ := hpath i' hi'
    show ((E i).1, (E i).2.1, (E (i + 1)).1) ∈ G.edges
    simp only [E, h1, h2, ← hc]
    exact hm
  · obtain ⟨e, he, hea⟩ := hweak a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    obtain ⟨j, hj, hjk⟩ := lassoAt_again (pre := pre) hk i
    refine ⟨j, hj, ?_⟩
    simp only [E, hjk]
    exact hea.symm
  · rcases hstrong a ha with ⟨e, he, hea⟩ | hoff
    · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
      obtain ⟨j, hj, hjk⟩ := lassoAt_again (pre := pre) hk i
      exact ⟨j, hj, by simp only [E, hjk]; exact hea⟩
    · obtain ⟨j, hj, hen⟩ := hinf pre.length
      have := hoff _ (lassoAt_mem hp hj)
      simp only [E] at hen
      rw [hen] at this
      cases this
  · obtain ⟨i', hi', h1, -⟩ := lassoAt_reduce (pre := pre) hp i
    show good (E i).1 = false
    simp only [E, h1]
    exact (hpath i' hi').2

/-- A path that checks is a run from an initial state that stops at a deadlock without reaching φ. -/
theorem checkDead_spec {G : Graph} {inits : List Nat} {good : Nat → Bool} {path : List (Nat × Nat × Nat)}
    {x : Nat} (h : checkDead G inits good path x = true) :
    ∃ (f : Nat → Nat) (j : Nat), f 0 ∈ inits ∧ (∀ i, i < j → ∃ a, (f i, a, f (i + 1)) ∈ G.edges) ∧
      Dead G (f j) ∧ ∀ i, i ≤ j → good (f i) = false := by
  simp only [checkDead, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem, List.all_eq_true,
    List.mem_range, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨h0, hx⟩, hdead⟩, hpath⟩ := h
  have hfj : deadAt path x path.length = x := by simp [deadAt]
  refine ⟨deadAt path x, path.length, h0, fun i hi => ⟨(path.getD i (0, 0, 0)).2.1, ?_⟩, ?_, fun i hi => ?_⟩
  · obtain ⟨⟨hm, hc⟩, -⟩ := hpath i hi
    have : deadAt path x i = (path.getD i (0, 0, 0)).1 := by simp [deadAt, hi]
    rw [this, ← hc]
    exact hm
  · intro a y hm
    rw [hfj] at hm
    exact hdead _ hm rfl
  · rcases Nat.lt_or_ge i path.length with hi' | hi'
    · have : deadAt path x i = (path.getD i (0, 0, 0)).1 := by simp [deadAt, hi']
      rw [this]
      exact (hpath i hi').2
    · rw [show i = path.length by omega, hfj]
      exact hx

end Fair
end Sys
end MathEngine
