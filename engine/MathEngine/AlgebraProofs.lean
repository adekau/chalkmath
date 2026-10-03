import MathEngine.Algebra
/-!
# What is proved about finite algebra

- **The checks decide the laws.** When a search finds no failure, the law holds for every element of
  the set: associativity (`assocFailure_none`), commutativity (`commFailure_none`), idempotence
  (`idemFailure_none`), distributivity (`distribFailure_none`), the Galois condition
  (`galoisFailure_none`), the three closure-operator conditions (`closureOpFailure_none`), monotonicity
  between two posets (`monotoneFailure2_none`), and "no flow down" (`flowFailure_none`).
- **A semilattice is an order** (`semilattice_order`): for an associative, commutative, idempotent
  operation closed on its set (a table's entries are checked to be in the set when it is made),
  `x ≤ y ⇔ x · y = y` is reflexive, antisymmetric and transitive, and `x · y` is the least upper bound
  of `x` and `y`. So `order` draws a partial order in which the operation is the join.
-/
namespace MathEngine
namespace Ord

theorem mem_allPairs {xs : List String} {x y : String} : (x, y) ∈ allPairs xs ↔ x ∈ xs ∧ y ∈ xs := by
  simp [allPairs]

theorem mem_allTriples {xs : List String} {x y z : String} :
    (x, y, z) ∈ allTriples xs ↔ x ∈ xs ∧ y ∈ xs ∧ z ∈ xs := by
  simp only [allTriples, List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, rfl, rfl⟩
    exact ⟨ha, hb, hc⟩
  · rintro ⟨hx, hy, hz⟩
    exact ⟨x, hx, y, hy, z, hz, rfl, rfl, rfl⟩

/-! ## The laws of an operation -/

theorem assocFailure_none (o : Op) (h : assocFailure o = none) :
    ∀ x ∈ o.elems, ∀ y ∈ o.elems, ∀ z ∈ o.elems, o.ap (o.ap x y) z = o.ap x (o.ap y z) := by
  intro x hx y hy z hz
  have := List.find?_eq_none.mp h (x, y, z) (mem_allTriples.mpr ⟨hx, hy, hz⟩)
  simpa using this

theorem commFailure_none (o : Op) (h : commFailure o = none) :
    ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y = o.ap y x := by
  intro x hx y hy
  have := List.find?_eq_none.mp h (x, y) (mem_allPairs.mpr ⟨hx, hy⟩)
  simpa using this

theorem idemFailure_none (o : Op) (h : idemFailure o = none) : ∀ x ∈ o.elems, o.ap x x = x := by
  intro x hx
  have := List.find?_eq_none.mp h x hx
  simpa using this

/-- An operation whose table stays in its set, with the three laws on it. -/
structure IsSemilattice (o : Op) : Prop where
  closed : ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y ∈ o.elems
  assoc : ∀ x ∈ o.elems, ∀ y ∈ o.elems, ∀ z ∈ o.elems, o.ap (o.ap x y) z = o.ap x (o.ap y z)
  comm : ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y = o.ap y x
  idem : ∀ x ∈ o.elems, o.ap x x = x

/-- The three searches finding nothing, on a closed table, make a semilattice. -/
theorem isSemilattice_of_none (o : Op) (hc : ∀ x ∈ o.elems, ∀ y ∈ o.elems, o.ap x y ∈ o.elems)
    (ha : assocFailure o = none) (hm : commFailure o = none) (hi : idemFailure o = none) : IsSemilattice o :=
  ⟨hc, assocFailure_none o ha, commFailure_none o hm, idemFailure_none o hi⟩

theorem order_rel (o : Op) (x y : String) :
    o.order.rel x y = true ↔ x ∈ o.elems ∧ y ∈ o.elems ∧ o.ap x y = y := by
  rw [Poset.rel_eq, List.contains_iff_mem]
  simp only [Op.order, Poset.of, List.mem_filter, mem_allPairs, beq_iff_eq, and_assoc]

/-- The order of a semilattice: a partial order in which `x · y` is the join. -/
theorem semilattice_order (o : Op) (hs : IsSemilattice o) :
    (∀ x ∈ o.elems, o.order.rel x x = true) ∧
    (∀ x y, o.order.rel x y = true → o.order.rel y x = true → x = y) ∧
    (∀ x y z, o.order.rel x y = true → o.order.rel y z = true → o.order.rel x z = true) ∧
    (∀ x ∈ o.elems, ∀ y ∈ o.elems, o.order.rel x (o.ap x y) = true ∧ o.order.rel y (o.ap x y) = true ∧
      ∀ u, o.order.rel x u = true → o.order.rel y u = true → o.order.rel (o.ap x y) u = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (order_rel o x x).mpr ⟨hx, hx, hs.idem x hx⟩
  · intro x y hxy hyx
    obtain ⟨hx, hy, e1⟩ := (order_rel o x y).mp hxy
    obtain ⟨_, _, e2⟩ := (order_rel o y x).mp hyx
    rw [← e2, hs.comm y hy x hx, e1]
  · intro x y z hxy hyz
    obtain ⟨hx, hy, e1⟩ := (order_rel o x y).mp hxy
    obtain ⟨_, hz, e2⟩ := (order_rel o y z).mp hyz
    refine (order_rel o x z).mpr ⟨hx, hz, ?_⟩
    rw [← e2, ← hs.assoc x hx y hy z hz, e1]
  · intro x hx y hy
    have hxy := hs.closed x hx y hy
    refine ⟨?_, ?_, ?_⟩
    · refine (order_rel o x (o.ap x y)).mpr ⟨hx, hxy, ?_⟩
      rw [← hs.assoc x hx x hx y hy, hs.idem x hx]
    · refine (order_rel o y (o.ap x y)).mpr ⟨hy, hxy, ?_⟩
      rw [hs.comm x hx y hy, ← hs.assoc y hy y hy x hx, hs.idem y hy]
    · intro u hxu hyu
      obtain ⟨_, hu, e1⟩ := (order_rel o x u).mp hxu
      obtain ⟨_, _, e2⟩ := (order_rel o y u).mp hyu
      refine (order_rel o (o.ap x y) u).mpr ⟨hxy, hu, ?_⟩
      rw [hs.assoc x hx y hy u hu, e2, e1]

/-! ## Lattice properties, maps, connections -/

theorem distribFailure_none (J M : Op) (h : distribFailure J M = none) :
    ∀ x ∈ J.elems, ∀ y ∈ J.elems, ∀ z ∈ J.elems, M.ap x (J.ap y z) = J.ap (M.ap x y) (M.ap x z) := by
  intro x hx y hy z hz
  have := List.find?_eq_none.mp h (x, y, z) (mem_allTriples.mpr ⟨hx, hy, hz⟩)
  simpa using this

theorem monotoneFailure2_none (P Q : Poset) (f : PMap) (h : monotoneFailure2 P Q f = none) :
    ∀ x y, (x, y) ∈ P.le → Q.rel (f.apply x) (f.apply y) = true := by
  intro x y hxy
  have := List.find?_eq_none.mp h (x, y) hxy
  simpa using this

theorem galoisFailure_none (P Q : Poset) (f g : PMap) (h : galoisFailure P Q f g = none) :
    ∀ x ∈ P.elems, ∀ y ∈ Q.elems, (Q.rel (f.apply x) y = true ↔ P.rel x (g.apply y) = true) := by
  intro x hx y hy
  have := List.find?_eq_none.mp h (x, y) (by simp [hx, hy])
  simp only [bne_iff_ne, ne_eq, Decidable.not_not] at this
  rw [this]

theorem closureOpFailure_none (P : Poset) (f : PMap) (h : closureOpFailure P f = none) :
    (∀ x ∈ P.elems, P.rel x (f.apply x) = true) ∧
    (∀ x y, (x, y) ∈ P.le → P.rel (f.apply x) (f.apply y) = true) ∧
    (∀ x ∈ P.elems, f.apply (f.apply x) = f.apply x) := by
  unfold closureOpFailure at h
  split at h
  · cases h
  · rename_i hext
    split at h
    · cases h
    · rename_i hmono
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        have := List.find?_eq_none.mp hext x hx
        simpa using this
      · intro x y hxy
        have := List.find?_eq_none.mp hmono (x, y) hxy
        simpa using this
      · intro x hx
        simp only [Option.map_eq_none_iff] at h
        have := List.find?_eq_none.mp h x hx
        simpa using this

theorem flowFailure_none (P : Poset) (label : String → String) (R : Rel) (h : flowFailure P label R = none) :
    ∀ x y, (x, y) ∈ R.pairs → P.rel (label x) (label y) = true := by
  intro x y hxy
  have := List.find?_eq_none.mp h (x, y) hxy
  simpa using this

end Ord
end MathEngine
