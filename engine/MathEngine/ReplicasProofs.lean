import MathEngine.Replicas
/-!
# The replicas' merge is a join, and their updates inflations

Every CRDT of `Replicas.lean` is a vector of naturals merged by the entrywise maximum. `merge` is
commutative, associative and idempotent (a join of the entrywise order), and every update only
raises entries (`update_inflation`: merging the old state into the new one changes nothing). So the
state a replica reaches is the join of the updates it has received, in whatever order, with whatever
duplicates: the replicas that have received the same updates are in the same state.
-/
namespace MathEngine
namespace Rep

theorem merge_comm : ∀ a b : Vec, merge a b = merge b a
  | [], [] | [], _ :: _ | _ :: _, [] => rfl
  | x :: a, y :: b => by simp [merge, List.zipWith_cons_cons, Nat.max_comm x y]; exact merge_comm a b

theorem merge_assoc : ∀ a b c : Vec, merge (merge a b) c = merge a (merge b c)
  | [], _, _ => rfl
  | _ :: _, [], _ => by simp [merge]
  | _ :: _, _ :: _, [] => by simp [merge]
  | x :: a, y :: b, z :: c => by
    simp only [merge, List.zipWith_cons_cons, Nat.max_assoc]
    exact congrArg _ (merge_assoc a b c)

theorem merge_idem : ∀ a : Vec, merge a a = a
  | [] => rfl
  | x :: a => by simp only [merge, List.zipWith_cons_cons, Nat.max_self]; exact congrArg _ (merge_idem a)

/-- Raising one entry by `f` (that never lowers it) is an inflation. -/
theorem merge_modify (f : Nat → Nat) (hf : ∀ n, n ≤ f n) : ∀ (v : Vec) (i : Nat), merge v (v.modify i f) = v.modify i f
  | [], _ => by simp [merge]
  | x :: v, 0 => by
    simp only [List.modify_zero_cons, merge, List.zipWith_cons_cons, Nat.max_eq_right (hf x)]
    exact congrArg _ (merge_idem v)
  | x :: v, i + 1 => by
    simp only [List.modify_succ_cons, merge, List.zipWith_cons_cons, Nat.max_self]
    exact congrArg _ (merge_modify f hf v i)

theorem merge_bump (v : Vec) (i : Nat) : merge v (bump v i) = bump v i :=
  merge_modify (· + 1) (fun n => Nat.le_succ n) v i

theorem merge_raise (v : Vec) (i k : Nat) : merge v (raise v i k) = raise v i k :=
  merge_modify (max · k) (fun n => Nat.le_max_left n k) v i

/-- Inflations compose. -/
theorem merge_trans {u v w : Vec} (h1 : merge u v = v) (h2 : merge v w = w) : merge u w = w := by
  rw [← h2, ← merge_assoc, h1]

-- the same simp set closes every case, each using part of it
set_option linter.unusedSimpArgs false in
/-- Every update only raises entries: merging the old state into the new one changes nothing. -/
theorem update_inflation (L : Layout) (v : Vec) (r name : String) (arg : Option String) (ts : Option Nat)
    (tagNo k : Nat) (v' : Vec) (h : update L v r name arg ts tagNo k = .ok v') : merge v v' = v' := by
  unfold update at h
  split at h <;> (try simp only [pure, Except.pure, Except.ok.injEq] at h) <;> (try subst h)
  all_goals first
    | exact merge_bump _ _
    | exact merge_raise _ _ _
    | skip
  · -- a 2P-set remove: present, then raised
    split at h
    · cases h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact merge_raise _ _ _
  · -- an OR-set remove: the seen tags raised, one after another
    generalize (List.filter _ _) = seen
    induction seen generalizing v with
    | nil => exact merge_idem v
    | cons i rest ih =>
      simp only [List.foldl_cons]
      exact merge_trans (merge_raise v _ 1) (ih _)
  · cases h

end Rep
end MathEngine
