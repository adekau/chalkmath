import MathEngine.Logic
/-!
# What is proved about the logic world

- **Every normal-form pass keeps the formula's value**, under every assignment: eliminating `→` and
  `↔` (`arrows_sound`), pushing negations in (`nnf_sound`), simplifying constants (`consts_sound`),
  distributing (`distrib_sound`, `normal_sound`); so `nnf`, `cnf` and `dnf` do (`toNormal_sound`).
  The laws each step names are the Bool identities these proofs go through.
- **Truth tables decide.** A formula's value depends only on its variables (`eval_congr`); every
  assignment to them is a row (`rows_complete`); so a formula true in every row is true under every
  assignment (`taut_sound`), and one false in every row is false under every assignment
  (`unsat_sound`). A row the engine returns as a witness is one (`findRow_spec`).
-/
namespace MathEngine
namespace Logic
open Fm

/-! ## The passes keep the value -/

theorem arrows_sound (σ : String → Bool) (f : Fm) : ∀ (ctx : Fm → Fm) (path : Path),
    (arrows ctx path f).1.eval σ = f.eval σ := by
  induction f with
  | not a ih => intro ctx path; simp [arrows, eval, ih]
  | and a b iha ihb => intro ctx path; simp [arrows, eval, iha, ihb]
  | or a b iha ihb => intro ctx path; simp [arrows, eval, iha, ihb]
  | imp a b iha ihb => intro ctx path; simp [arrows, eval, iha, ihb]
  | iff a b iha ihb =>
    intro ctx path
    simp only [arrows, eval, iha, ihb]
    cases a.eval σ <;> cases b.eval σ <;> rfl
  | _ => intro ctx path; simp [arrows]

theorem nnf_sound (σ : String → Bool) (f : Fm) : ∀ (neg : Bool) (ctx : Fm → Fm) (path : Path),
    (nnf neg ctx path f).1.eval σ = (if neg then !f.eval σ else f.eval σ) := by
  induction f with
  | not a ih => intro neg ctx path; cases neg <;> simp [nnf, eval, ih]
  | and a b iha ihb => intro neg ctx path; cases neg <;> simp [nnf, eval, iha, ihb]
  | or a b iha ihb => intro neg ctx path; cases neg <;> simp [nnf, eval, iha, ihb]
  | tt => intro neg ctx path; cases neg <;> simp [nnf, eval]
  | ff => intro neg ctx path; cases neg <;> simp [nnf, eval]
  | _ => intro neg ctx path; cases neg <;> simp [nnf, eval]

theorem consts_sound (σ : String → Bool) (f : Fm) : ∀ (ctx : Fm → Fm) (path : Path),
    (consts ctx path f).1.eval σ = f.eval σ := by
  induction f with
  | and a b iha ihb =>
    intro ctx path
    simp only [consts]
    generalize ha : consts (fun x => ctx (.and x b)) (path ++ [0]) a = ra
    obtain ⟨a', s1⟩ := ra
    generalize hb : consts (fun x => ctx (.and a' x)) (path ++ [1]) b = rb
    obtain ⟨b', s2⟩ := rb
    have ea : a'.eval σ = a.eval σ := by have := iha (fun x => ctx (.and x b)) (path ++ [0]); rw [ha] at this; exact this
    have eb : b'.eval σ = b.eval σ := by have := ihb (fun x => ctx (.and a' x)) (path ++ [1]); rw [hb] at this; exact this
    simp only [eval, ← ea, ← eb]
    split <;> simp_all [eval]
  | or a b iha ihb =>
    intro ctx path
    simp only [consts]
    generalize ha : consts (fun x => ctx (.or x b)) (path ++ [0]) a = ra
    obtain ⟨a', s1⟩ := ra
    generalize hb : consts (fun x => ctx (.or a' x)) (path ++ [1]) b = rb
    obtain ⟨b', s2⟩ := rb
    have ea : a'.eval σ = a.eval σ := by have := iha (fun x => ctx (.or x b)) (path ++ [0]); rw [ha] at this; exact this
    have eb : b'.eval σ = b.eval σ := by have := ihb (fun x => ctx (.or a' x)) (path ++ [1]); rw [hb] at this; exact this
    simp only [eval, ← ea, ← eb]
    split <;> simp_all [eval]
  | _ => intro ctx path; simp [consts]

private theorem outer_eval (σ : String → Bool) (cnf : Bool) (x y : Fm) :
    (outerOp cnf x y).eval σ = if cnf then (x.eval σ || y.eval σ) else (x.eval σ && y.eval σ) := by
  cases cnf <;> simp [outerOp, eval]
private theorem inner_eval (σ : String → Bool) (cnf : Bool) (x y : Fm) :
    (innerOp cnf x y).eval σ = if cnf then (x.eval σ && y.eval σ) else (x.eval σ || y.eval σ) := by
  cases cnf <;> simp [innerOp, eval]

theorem distribR_sound (σ : String → Bool) (cnf : Bool) (a b : Fm) : ∀ (ctx : Fm → Fm) (path : Path),
    (distribR cnf ctx path a b).1.eval σ = (outerOp cnf a b).eval σ := by
  induction b with
  | and b1 b2 ih1 ih2 =>
    intro ctx path
    cases cnf
    · simp [distribR]
    · simp only [distribR, if_true]
      simp only [inner_eval, outer_eval, ih1, ih2, eval, if_true]
      cases a.eval σ <;> cases b1.eval σ <;> cases b2.eval σ <;> rfl
  | or b1 b2 ih1 ih2 =>
    intro ctx path
    cases cnf
    · simp only [distribR, Bool.not_false, if_true]
      simp only [inner_eval, outer_eval, ih1, ih2, eval, Bool.false_eq_true, if_false]
      cases a.eval σ <;> cases b1.eval σ <;> cases b2.eval σ <;> rfl
    · simp [distribR]
  | _ => intro ctx path; simp [distribR]

theorem distrib_sound (σ : String → Bool) (cnf : Bool) (a : Fm) : ∀ (b : Fm) (ctx : Fm → Fm) (path : Path),
    (distrib cnf ctx path a b).1.eval σ = (outerOp cnf a b).eval σ := by
  induction a with
  | and a1 a2 ih1 ih2 =>
    intro b ctx path
    cases cnf
    · simp [distrib, distribR_sound]
    · simp only [distrib, if_true]
      simp only [inner_eval, outer_eval, ih1, ih2, eval, if_true]
      cases a1.eval σ <;> cases a2.eval σ <;> cases b.eval σ <;> rfl
  | or a1 a2 ih1 ih2 =>
    intro b ctx path
    cases cnf
    · simp only [distrib, Bool.not_false, if_true]
      simp only [inner_eval, outer_eval, ih1, ih2, eval, Bool.false_eq_true, if_false]
      cases a1.eval σ <;> cases a2.eval σ <;> cases b.eval σ <;> rfl
    · simp [distrib, distribR_sound]
  | _ => intro b ctx path; simp [distrib, distribR_sound]

theorem normal_sound (σ : String → Bool) (cnf : Bool) (f : Fm) : ∀ (ctx : Fm → Fm) (path : Path),
    (normal cnf ctx path f).1.eval σ = f.eval σ := by
  induction f with
  | and a b iha ihb =>
    intro ctx path
    cases cnf
    · simp [normal, distrib_sound, outer_eval, eval, iha, ihb]
    · simp [normal, eval, iha, ihb]
  | or a b iha ihb =>
    intro ctx path
    cases cnf
    · simp [normal, eval, iha, ihb]
    · simp [normal, distrib_sound, outer_eval, eval, iha, ihb]
  | _ => intro ctx path; simp [normal]

/-- `nnf`, `cnf` and `dnf` keep the formula's value under every assignment. -/
theorem toNormal_sound (σ : String → Bool) (target : String) (f : Fm) :
    (toNormal target f).1.eval σ = f.eval σ := by
  unfold toNormal
  split <;> simp [normal_sound, consts_sound, nnf_sound, arrows_sound]

/-! ## Truth tables decide -/

/-- A formula's value depends only on its variables. -/
theorem eval_congr (σ τ : String → Bool) (f : Fm) (h : ∀ x ∈ f.vars, σ x = τ x) : f.eval σ = f.eval τ := by
  induction f with
  | var x => simp [eval]; exact h x (by simp [vars])
  | not a ih => simp [eval, ih (by simpa [vars] using h)]
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb | iff a b iha ihb =>
    have ha : ∀ x ∈ a.vars, σ x = τ x := fun x hx => h x (by simp [vars, List.mem_eraseDups, hx])
    have hb : ∀ x ∈ b.vars, σ x = τ x := fun x hx => h x (by simp [vars, List.mem_eraseDups, hx])
    simp [eval, iha ha, ihb hb]
  | _ => rfl

/-- Every list of truth values as long as `vs` is a row. -/
theorem mem_rows (vs : List String) : ∀ (bs : List Bool), bs.length = vs.length → bs ∈ rows vs := by
  induction vs with
  | nil => intro bs h; cases bs <;> simp_all [rows]
  | cons v vs ih =>
    intro bs h
    cases bs with
    | nil => simp at h
    | cons b bs =>
      have hl : bs.length = vs.length := by simpa using h
      cases b <;> simp [rows, ih bs hl]

private theorem lookup_zip_map (σ : String → Bool) (vs : List String) (x : String) (hx : x ∈ vs) :
    (vs.zip (vs.map σ)).lookup x = some (σ x) := by
  induction vs with
  | nil => simp at hx
  | cons v vs ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
    by_cases hv : x = v
    · subst hv; simp
    · have : (x == v) = false := by simpa using hv
      simp [this, ih (by simpa [hv] using hx)]

/-- Every assignment agrees on `vs` with some row's. -/
theorem rows_complete (vs : List String) (σ : String → Bool) :
    ∃ r ∈ rows vs, ∀ x ∈ vs, assignment vs r x = σ x :=
  ⟨vs.map σ, mem_rows vs _ (by simp), fun x hx => by simp [assignment, lookup_zip_map σ vs x hx]⟩

/-- No row falsifies `f` (its variables `vs`): then nothing does. -/
theorem taut_sound (f : Fm) (h : findRow f.vars (fun σ => !f.eval σ) = none) (σ : String → Bool) :
    f.eval σ = true := by
  obtain ⟨r, hr, hagree⟩ := rows_complete f.vars σ
  have hr' := (List.find?_eq_none.mp h) r hr
  rw [eval_congr σ (assignment f.vars r) f (fun x hx => (hagree x hx).symm)]
  simpa using hr'

/-- No row satisfies `f`: then nothing does. -/
theorem unsat_sound (f : Fm) (h : findRow f.vars (fun σ => f.eval σ == true) = none) (σ : String → Bool) :
    f.eval σ = false := by
  obtain ⟨r, hr, hagree⟩ := rows_complete f.vars σ
  have hr' := (List.find?_eq_none.mp h) r hr
  rw [eval_congr σ (assignment f.vars r) f (fun x hx => (hagree x hx).symm)]
  simpa using hr'

/-- A row the engine returns as a witness is one. -/
theorem findRow_spec (vs : List String) (p : (String → Bool) → Bool) (r : List Bool)
    (h : findRow vs p = some r) : p (assignment vs r) = true := by
  unfold findRow at h
  exact List.find?_some (p := fun r => p (assignment vs r)) h

end Logic
end MathEngine
