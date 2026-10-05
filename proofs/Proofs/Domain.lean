import Proofs.SimpAll
/-!
# Where a term is defined, and steps that keep it so

`evalR` is total: it gives every term a real number, using Mathlib's conventions where ordinary
mathematics leaves a term undefined (`Real.log x = log |x|`, `x / 0 = 0`, a negative base under a
fractional power is a junk value). A rule proved against `evalR` alone can therefore change the domain
of what it rewrites without anyone noticing: `ln(x²) = 2 ln x` holds for every real `x` in `evalR`,
yet `ln(x²)` is defined at `x = −2` and `2 ln x` is not.

`Def ρ e` says `e` is defined at the point `ρ` in the ordinary sense: logarithms of positive numbers,
square roots of non-negative ones, `tan` away from its poles, `x^y` for `x > 0`, for an integer `y`
(with `x ≠ 0` when `y < 0`), or for `x = 0` and `y > 0`; no unknown functions, commands or matrices.

`DomEq e e'` asks of a step what a reader asks of an answer: wherever the input is defined, so is the
output, with the same value. It is a `Congruence` (`domCongruence`), so the fold of `RewriteSound`
applies to it as to `SemEqR`, and a rule is domain-sound when it is ℝ-sound and keeps definedness
(`RuleSoundD`). Every rule the simplifier runs without an assumption is (`simpRulesSafe_soundD`), so
normalizing keeps the domain (`normalizeSafe_soundD`); the rule that broke it, `ln(b^p) = p ln b`
for an even `p`, is now `simp.function.assuming` and says `b > 0`.
-/
noncomputable section
namespace MathProofs
open MathEngine MathEngine.Expr

/-- `x ^ y` is defined: a positive base, an integer exponent (a nonzero base if it is negative), or
the base 0 under a positive exponent. -/
def PowOK (x y : ℝ) : Prop := 0 < x ∨ (∃ n : ℤ, y = n ∧ (x ≠ 0 ∨ 0 ≤ n)) ∨ (x = 0 ∧ 0 < y)

/-- Where each function is defined. -/
def FnOK (f : String) (x : ℝ) : Prop :=
  if f = "ln" ∨ f = "log" then 0 < x
  else if f = "sqrt" then 0 ≤ x
  else if f = "tan" then Real.cos x ≠ 0
  else f = "sin" ∨ f = "cos" ∨ f = "exp" ∨ f = "abs" ∨ f = "sign"

mutual
  /-- `e` is defined at `ρ`. -/
  def Def (ρ : EnvR) : Expr → Prop
    | .num _ => True
    | .var _ => True
    | .add es => DefList ρ es
    | .mul es => DefList ρ es
    | .pow b e => Def ρ b ∧ Def ρ e ∧ PowOK (evalR ρ b) (evalR ρ e)
    | .fn f [] => f = "π"
    | .fn f [a] => Def ρ a ∧ FnOK f (evalR ρ a)
    | .fn _ (_ :: _ :: _) => False
    | .matrix _ => False
  def DefList (ρ : EnvR) : List Expr → Prop
    | [] => True
    | e :: es => Def ρ e ∧ DefList ρ es
end

@[simp] theorem Def_num (ρ : EnvR) (q : Q) : Def ρ (.num q) := trivial
@[simp] theorem Def_var (ρ : EnvR) (x : String) : Def ρ (.var x) := trivial
@[simp] theorem Def_add (ρ : EnvR) (es : List Expr) : Def ρ (.add es) ↔ DefList ρ es := by simp [Def]
@[simp] theorem Def_mul (ρ : EnvR) (es : List Expr) : Def ρ (.mul es) ↔ DefList ρ es := by simp [Def]
@[simp] theorem Def_pow (ρ : EnvR) (b e : Expr) :
    Def ρ (.pow b e) ↔ Def ρ b ∧ Def ρ e ∧ PowOK (evalR ρ b) (evalR ρ e) := by simp [Def]
@[simp] theorem Def_fn₁ (ρ : EnvR) (f : String) (a : Expr) :
    Def ρ (.fn f [a]) ↔ Def ρ a ∧ FnOK f (evalR ρ a) := by simp [Def]

theorem DefList_iff (ρ : EnvR) : ∀ es : List Expr, DefList ρ es ↔ ∀ e ∈ es, Def ρ e
  | [] => by simp [DefList]
  | e :: es => by simp [DefList, DefList_iff ρ es]

theorem DefList_perm (ρ : EnvR) {l₁ l₂ : List Expr} (h : l₁.Perm l₂) : DefList ρ l₁ ↔ DefList ρ l₂ := by
  rw [DefList_iff, DefList_iff]
  exact ⟨fun H e he => H e (h.mem_iff.mpr he), fun H e he => H e (h.mem_iff.mp he)⟩

theorem DefList_sub (ρ : EnvR) {l₁ l₂ : List Expr} (hsub : ∀ e ∈ l₂, e ∈ l₁) (h : DefList ρ l₁) :
    DefList ρ l₂ := by
  rw [DefList_iff] at h ⊢; exact fun e he => h e (hsub e he)

@[simp] theorem Def_zero (ρ : EnvR) : Def ρ Expr.zero := trivial
@[simp] theorem Def_one (ρ : EnvR) : Def ρ Expr.one := trivial

theorem Def_addN (ρ : EnvR) : ∀ l : List Expr, DefList ρ l → Def ρ (Expr.addN l)
  | [e], h => h.1
  | [], _ => by simp [Expr.addN, DefList]
  | _ :: _ :: _, h => by simpa [Expr.addN] using h

theorem Def_mulN (ρ : EnvR) : ∀ l : List Expr, DefList ρ l → Def ρ (Expr.mulN l)
  | [e], h => h.1
  | [], _ => by simp [Expr.mulN, DefList]
  | _ :: _ :: _, h => by simpa [Expr.mulN] using h

/-! ## Steps that keep the domain -/

/-- Wherever `e` is defined, `e'` is, with the same value. -/
def DomEq (e e' : Expr) : Prop := SemEqR e e' ∧ ∀ ρ, Def ρ e → Def ρ e'

theorem DomEq.refl (e : Expr) : DomEq e e := ⟨SemEqR.refl e, fun _ h => h⟩

theorem DomEq.trans {a b c : Expr} (h₁ : DomEq a b) (h₂ : DomEq b c) : DomEq a c :=
  ⟨SemEqR.trans h₁.1 h₂.1, fun ρ h => h₂.2 ρ (h₁.2 ρ h)⟩

theorem RelList_mono {R S : Expr → Expr → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {as bs : List Expr}, RelList R as bs → RelList S as bs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h, t⟩ => ⟨hRS _ _ h, RelList_mono hRS t⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem DefList_congr (ρ : EnvR) : ∀ {as bs : List Expr}, RelList DomEq as bs → DefList ρ as → DefList ρ bs
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, ⟨h, t⟩, ⟨ha, hs⟩ => ⟨h.2 ρ ha, DefList_congr ρ t hs⟩
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

private theorem list_eq_two' {α : Type*} : ∀ {l : List α}, l.length = 2 → ∃ a b, l = [a, b]
  | [a, b], _ => ⟨a, b, rfl⟩

theorem DomEq.congr (e : Expr) (cs : List Expr) (h : RelList DomEq (children e) cs) :
    DomEq e (withChildren e cs) := by
  refine ⟨SemEqR.congr e cs (RelList_mono (fun _ _ h => h.1) h), fun ρ hd => ?_⟩
  have hlen : (children e).length = cs.length := RelList_length h
  cases e with
  | num q => cases cs with | nil => exact hd | cons _ _ => simp [children] at hlen
  | var x => cases cs with | nil => exact hd | cons _ _ => simp [children] at hlen
  | add es => simpa [withChildren] using DefList_congr ρ h (by simpa [children] using hd)
  | mul es => simpa [withChildren] using DefList_congr ρ h (by simpa [children] using hd)
  | matrix rows => simp [Def] at hd
  | pow b x =>
    obtain ⟨b', x', rfl⟩ := list_eq_two' (by simpa [children] using hlen.symm)
    obtain ⟨hb, hx, -⟩ := h
    simp only [withChildren, Def_pow] at hd ⊢
    obtain ⟨d1, d2, d3⟩ := hd
    exact ⟨hb.2 ρ d1, hx.2 ρ d2, by rw [← hb.1 ρ, ← hx.1 ρ]; exact d3⟩
  | fn f es =>
    simp only [children] at hlen
    cases es with
    | nil => cases cs with
      | nil => exact hd
      | cons _ _ => simp at hlen
    | cons a rest =>
      cases cs with
      | nil => simp at hlen
      | cons a' rest' =>
        cases rest with
        | nil =>
          cases rest' with
          | nil =>
            obtain ⟨ha, -⟩ := h
            simp only [withChildren, Def_fn₁] at hd ⊢
            exact ⟨ha.2 ρ hd.1, by rw [← ha.1 ρ]; exact hd.2⟩
          | cons _ _ => simp at hlen
        | cons _ _ => simp [Def] at hd

theorem DomEq.canon (e : Expr) : DomEq e (canon e) := by
  refine ⟨SemEqR.canon e, fun ρ hd => ?_⟩
  cases e with
  | add es =>
    simp only [MathEngine.canon, Def_add] at hd ⊢
    exact (DefList_perm ρ (List.mergeSort_perm es _)).mpr hd
  | mul es =>
    simp only [MathEngine.canon]
    split
    · exact hd
    · simp only [Def_mul] at hd ⊢
      exact (DefList_perm ρ (List.mergeSort_perm es _)).mpr hd
  | _ => exact hd

/-- The domain-keeping semantics as a `Congruence`, so `normalize_sound_for` applies. -/
def domCongruence : Congruence where
  rel := DomEq
  refl := DomEq.refl
  trans := DomEq.trans
  congr := DomEq.congr
  canon := DomEq.canon

/-- A rule keeps the domain: ℝ-sound, and defined wherever its input is. -/
abbrev RuleSoundD (r : Rule simpW) : Prop := RuleSoundFor domCongruence r

theorem RuleSoundD.of {r : Rule simpW} (hR : RuleSoundR r)
    (hD : ∀ e res, r.apply e = some res → ∀ ρ, Def ρ e → Def ρ res.result) : RuleSoundD r :=
  fun e res h => ⟨hR e res h, hD e res h⟩

/-! ## The simplifier's rules keep the domain -/

theorem Def_unAdd (ρ : EnvR) {e : Expr} (h : Def ρ e) : ∀ x ∈ unAdd e, Def ρ x := by
  cases e <;> simp_all [unAdd, DefList_iff]

theorem Def_unMul (ρ : EnvR) {e : Expr} (h : Def ρ e) : ∀ x ∈ unMul e, Def ρ x := by
  cases e <;> simp_all [unMul, DefList_iff]

mutual
  theorem DefList_addArgs (ρ : EnvR) : ∀ (e : Expr) (acc : List Expr),
      DefList ρ (addArgs e acc) ↔ Def ρ e ∧ DefList ρ acc
    | .add es, acc => by rw [addArgs, DefList_addArgsList ρ es acc, Def_add]
    | .num _, _ | .var _, _ | .mul _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by simp [addArgs, DefList]
  theorem DefList_addArgsList (ρ : EnvR) : ∀ (es acc : List Expr),
      DefList ρ (addArgsList es acc) ↔ DefList ρ es ∧ DefList ρ acc
    | [], acc => by simp [addArgsList, DefList]
    | e :: es, acc => by
      rw [addArgsList, DefList_addArgs ρ e, DefList_addArgsList ρ es acc]; simp only [DefList, and_assoc]
end

mutual
  theorem DefList_mulArgs (ρ : EnvR) : ∀ (e : Expr) (acc : List Expr),
      DefList ρ (mulArgs e acc) ↔ Def ρ e ∧ DefList ρ acc
    | .mul es, acc => by rw [mulArgs, DefList_mulArgsList ρ es acc, Def_mul]
    | .num _, _ | .var _, _ | .add _, _ | .pow _ _, _ | .fn _ _, _ | .matrix _, _ => by simp [mulArgs, DefList]
  theorem DefList_mulArgsList (ρ : EnvR) : ∀ (es acc : List Expr),
      DefList ρ (mulArgsList es acc) ↔ DefList ρ es ∧ DefList ρ acc
    | [], acc => by simp [mulArgsList, DefList]
    | e :: es, acc => by
      rw [mulArgsList, DefList_mulArgs ρ e, DefList_mulArgsList ρ es acc]; simp only [DefList, and_assoc]
end

/-- Opening a chain (`openChain`) keeps the domain: a sum or product of the same terms. -/
theorem openChain_def {e e' : Expr} (h : openChain e = some e') (ρ : EnvR) : Def ρ e' ↔ Def ρ e := by
  cases e <;> simp only [openChain, reduceCtorEq] at h
  · split at h
    · split at h
      · cases h
      · cases h; simp [DefList_addArgsList, DefList]
    · cases h
  · split at h
    · cases h; simp [DefList_mulArgsList, DefList]
    · cases h

theorem flatten_soundD : RuleSoundD flatten := RuleSoundD.of flatten_soundR fun e res h ρ hd => by
  cases e <;> simp only [flatten, flattenApply, reduceCtorEq] at h
  · split at h
    · cases h
      simp only [Def_add, DefList_iff, List.mem_flatMap] at hd ⊢
      rintro x ⟨y, hy, hx⟩
      exact Def_unAdd ρ (hd y hy) x hx
    · cases h
  · split at h
    · cases h
      simp only [Def_mul, DefList_iff, List.mem_flatMap] at hd ⊢
      rintro x ⟨y, hy, hx⟩
      exact Def_unMul ρ (hd y hy) x hx
    · cases h

theorem filter_sub (p : Expr → Bool) (l : List Expr) : ∀ e ∈ l.filter p, e ∈ l :=
  fun _ he => (List.mem_filter.mp he).1

theorem identity_soundD : RuleSoundD identity := RuleSoundD.of identity_soundR fun e res h ρ hd => by
  cases e with
  | add es =>
    match es, h with
    | [], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | [a], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simpa [DefList] using hd
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h
      · cases h; exact Def_addN ρ _ (DefList_sub ρ (filter_sub _ _) (by simpa using hd))
      · cases h
  | mul es =>
    match es, h with
    | [], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simp
    | [a], h => simp only [identity, identityApply, Option.some.injEq] at h; subst h; simpa [DefList] using hd
    | x :: y :: rest, h =>
      simp only [identity, identityApply] at h
      split at h
      · cases h; simp
      · split at h
        · cases h; exact Def_mulN ρ _ (DefList_sub ρ (filter_sub _ _) (by simpa using hd))
        · cases h
  | _ => simp [identity, identityApply] at h

theorem foldConstants_soundD : RuleSoundD foldConstants := RuleSoundD.of foldConstants_soundR fun e res h ρ hd => by
  cases e <;> simp only [foldConstants, foldApply, reduceCtorEq] at h
  · split at h
    · cases h
      refine Def_addN ρ _ ⟨trivial, DefList_sub ρ (filter_sub _ _) (by simpa using hd)⟩
    · cases h
  · split at h
    · cases h
      refine Def_mulN ρ _ ⟨trivial, DefList_sub ρ (filter_sub _ _) (by simpa using hd)⟩
    · cases h

theorem removeFirst_sub (p : Expr → Bool) : ∀ (l : List Expr), ∀ e ∈ removeFirst p l, e ∈ l
  | [], e, he => by simp [removeFirst] at he
  | a :: as, e, he => by
    simp only [removeFirst] at he
    split at he
    · exact List.mem_cons_of_mem _ he
    · rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (removeFirst_sub p as e he)

theorem Def_coeffRest (ρ : EnvR) {e : Expr} (h : Def ρ e) : Def ρ (coeffRest e).2 := by
  unfold coeffRest
  split
  · simp
  · rename_i q rest
    simp only [Def_mul, DefList] at h
    exact Def_mulN ρ _ h.2
  · exact h

theorem mergeTerms_def (ρ : EnvR) (es l : List Expr) (t : Expr) (h : mergeTerms es = some (l, t))
    (hd : DefList ρ es) : DefList ρ l := by
  simp only [mergeTerms, Option.map_eq_some_iff] at h
  obtain ⟨⟨u, e, fs, others⟩, hg, hl⟩ := h
  simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨hperm, he, -, -, -⟩ := termGroup_spec hg
  have hd' := (DefList_iff ρ _).mp ((DefList_perm ρ hperm).mp hd)
  have hu : Def ρ u := he ▸ Def_coeffRest ρ (hd' e List.mem_cons_self)
  exact ⟨⟨trivial, hu, trivial⟩, (DefList_iff ρ others).mpr fun x hx => hd' x (by simp [hx])⟩

theorem collectTerms_soundD : RuleSoundD collectTerms := RuleSoundD.of collectTerms_soundR fun e res h ρ hd => by
  cases e <;> simp only [collectTerms, collectTermsApply, reduceCtorEq] at h
  rename_i es
  split at h
  · rename_i l t hm
    cases h
    simpa using mergeTerms_def ρ es l t hm (by simpa using hd)
  · cases h

/-! ## Powers -/

/-- An integer power is defined at a nonzero base, or for a non-negative exponent. -/
theorem powOK_int (x : ℝ) (m : ℤ) : PowOK x m ↔ x ≠ 0 ∨ 0 ≤ m := by
  unfold PowOK
  constructor
  · rintro (h | ⟨k, hk, h⟩ | ⟨-, hm⟩)
    · exact Or.inl h.ne'
    · have : m = k := by exact_mod_cast hk
      subst this; exact h
    · exact Or.inr (by exact_mod_cast hm.le)
  · rintro (h | h)
    · exact Or.inr (Or.inl ⟨m, rfl, Or.inl h⟩)
    · exact Or.inr (Or.inl ⟨m, rfl, Or.inr h⟩)

theorem powNumeric_num {p q : Q} {r : RuleResult} (h : powNumeric p q = some r) : ∃ c, r.result = .num c := by
  unfold powNumeric at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · split at h
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · cases h
    · cases h

theorem powerRules_soundD : RuleSoundD powerRules := RuleSoundD.of powerRules_soundR fun e res h ρ hd => by
  cases e <;> simp only [powerRules, powerApply, reduceCtorEq] at h
  rename_i b x
  simp only [Def_pow] at hd
  obtain ⟨hb, hx, hok⟩ := hd
  simp only [powerAt] at h
  split at h
  · cases h; simp
  split at h
  · cases h; exact hb
  split at h
  · cases h; simp
  split at h
  · cases h; simp
  cases b with
  | num p =>
    cases x with
    | num q =>
      simp only [powerNum] at h
      obtain ⟨c, hc⟩ := powNumeric_num h; rw [hc]; simp
    | _ => simp [powerNum] at h
  | pow b' m =>
    cases x with
    | num n' =>
      cases m with
      | num mq =>
        simp only [Def_pow] at hb
        obtain ⟨hb', -, hok'⟩ := hb
        simp only [powerNum] at h
        split at h
        · rename_i hint
          cases h
          simp only [Bool.and_eq_true] at hint
          obtain ⟨hn', hm⟩ := hint
          refine (Def_pow ρ _ _).mpr ⟨hb', trivial, ?_⟩
          have hmn : ((mq * n' : Q).val : ℝ) = ((mq.val.num * n'.val.num : ℤ) : ℝ) := by
            rw [Q_val_mul, Rat.cast_mul, Q_cast_isInt hm, Q_cast_isInt hn']; push_cast; ring
          simp only [evalR_num] at hok hok' ⊢
          rw [hmn, powOK_int]
          rw [Q_cast_isInt hm, powOK_int] at hok'
          rw [Q_cast_isInt hn', powOK_int] at hok
          rw [evalR_pow, evalR_num, Q_cast_isInt hm, Real.rpow_intCast] at hok
          rcases hok' with hne | hm0
          · exact Or.inl hne
          · by_cases hz : evalR ρ b' = 0
            · right
              rcases lt_or_eq_of_le hm0 with hlt | heq
              · rcases hok with hne | hn0
                · exfalso; apply hne; rw [hz]; exact zero_zpow _ hlt.ne'
                · exact Int.mul_nonneg hlt.le hn0
              · rw [← heq]; simp
            · exact Or.inl hz
        · split at h
          · rename_i hnp
            cases h
            simp only [Bool.and_eq_true] at hnp
            exact (Def_pow ρ _ _).mpr ⟨hb', trivial, Or.inl (isPosNum_pos hnp.2 ρ)⟩
          · cases h
      | _ => simp [powerNum] at h
    | _ => simp [powerNum] at h
  | _ => simp [powerNum] at h

/-! ## Collecting powers -/

theorem Def_baseExp (ρ : EnvR) {e b x : Expr} (h : baseExp e = (b, x)) (hd : Def ρ e) :
    Def ρ b ∧ Def ρ x ∧ PowOK (evalR ρ b) (evalR ρ x) := by
  rcases baseExp_cases e b x h with rfl | ⟨rfl, rfl⟩
  · simpa using hd
  · refine ⟨hd, trivial, ?_⟩
    have : evalR ρ Expr.one = ((1 : ℤ) : ℝ) := by simp
    rw [this, powOK_int]; right; norm_num

/-- What merging the factors `fs` into `b^X` one at a time needs to stay defined at a point: each
pair merge defined wherever its two factors are. -/
def FoldDefOK (ρ : EnvR) (b : Expr) : Expr → List Expr → Prop
  | _, [] => True
  | X, f :: fs => (PowOK (evalR ρ b) (evalR ρ X) → PowOK (evalR ρ b) (evalR ρ (baseExp f).2) →
      PowOK (evalR ρ b) (evalR ρ X + evalR ρ (baseExp f).2)) ∧ FoldDefOK ρ b (addExp X (baseExp f).2) fs

theorem Def_addExp (ρ : EnvR) {x y : Expr} (hx : Def ρ x) (hy : Def ρ y) : Def ρ (addExp x y) := by
  unfold addExp; split
  · trivial
  · simp only [Def_add, DefList]; exact ⟨hx, hy, trivial⟩

theorem expFold_def (ρ : EnvR) {b : Expr} : ∀ (fs : List Expr) (X : Expr),
    (∀ f ∈ fs, (baseExp f).1 = b ∧ Def ρ f) → FoldDefOK ρ b X fs → Def ρ X → PowOK (evalR ρ b) (evalR ρ X) →
    Def ρ (expFold X fs) ∧ PowOK (evalR ρ b) (evalR ρ (expFold X fs))
  | [], _, _, _, hX, hok => ⟨hX, hok⟩
  | f :: fs, X, hfs, ⟨hstep, hrest⟩, hX, hok => by
    obtain ⟨hb, hdf⟩ := hfs f List.mem_cons_self
    obtain ⟨-, dy, oky⟩ := Def_baseExp ρ (baseExp_of_fst hb) hdf
    simp only [expFold]
    exact expFold_def ρ fs _ (fun g hg => hfs g (List.mem_cons_of_mem _ hg)) hrest (Def_addExp ρ hX dy)
      (by rw [evalR_addExp]; exact hstep hok oky)

/-- The merge keeps the domain wherever each of its pair merges does. -/
theorem mergePowers_def (ρ : EnvR) (es l : List Expr) (t : Expr) (h : mergePowers es = some (l, t))
    (H : ∀ b e fs others, powerGroup es = some (b, e, fs, others) → FoldDefOK ρ b (baseExp e).2 fs)
    (hd : DefList ρ es) : DefList ρ l := by
  simp only [mergePowers, Option.map_eq_some_iff] at h
  obtain ⟨⟨b, e, fs, others⟩, hg, hl⟩ := h
  simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨hperm, he, hfs, -, -⟩ := powerGroup_spec hg
  have hd' := (DefList_iff ρ _).mp ((DefList_perm ρ hperm).mp hd)
  obtain ⟨db, dx, okx⟩ := Def_baseExp ρ (baseExp_of_fst he) (hd' e List.mem_cons_self)
  have hX := expFold_def ρ fs _ (fun f hf => ⟨hfs f hf, hd' f (by simp [hf])⟩) (H _ _ _ _ hg) dx okx
  exact ⟨(Def_pow ρ _ _).mpr ⟨db, hX.1, hX.2⟩, (DefList_iff ρ others).mpr fun x hx => hd' x (by simp [hx])⟩

/-- Where `powSafe` holds, the merged power is defined wherever both factors are. -/
theorem powSafe_def {b x y : Expr} (h : powSafe b x y = true) (ρ : EnvR)
    (hx : PowOK (evalR ρ b) (evalR ρ x)) (hy : PowOK (evalR ρ b) (evalR ρ y)) :
    PowOK (evalR ρ b) (evalR ρ x + evalR ρ y) := by
  unfold powSafe at h
  simp only [Bool.or_eq_true] at h
  rcases h with hp | hi
  · exact Or.inl (isPosNum_pos hp ρ)
  · split at hi
    · rename_i m n hm hn
      rw [evalR_of_intExp hm] at hx ⊢
      rw [evalR_of_intExp hn] at hy ⊢
      rw [← Int.cast_add, powOK_int]
      rw [powOK_int] at hx hy
      rcases hx with h1 | h1
      · exact Or.inl h1
      · rcases hy with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (by omega)
    · cases hi

theorem FoldDefOK_of_safe (ρ : EnvR) {b : Expr} : ∀ (X : Expr) (fs : List Expr),
    (foldSafety b X fs).1 = true → FoldDefOK ρ b X fs
  | _, [], _ => trivial
  | _, _ :: fs, h => by
    simp only [foldSafety, Bool.and_eq_true] at h
    exact ⟨fun okx oky => powSafe_def h.1 ρ okx oky, FoldDefOK_of_safe ρ _ fs h.2⟩

theorem collectPowers_soundD : RuleSoundD collectPowers := RuleSoundD.of collectPowers_soundR fun e res h ρ hd => by
  have hs := gate_some h
  have hna : (collectAssumed e).isNone = true := by
    cases hca : (collectAssumed e).isNone with
    | true => rfl
    | false => simp only [collectPowers, Option.isNone_iff_eq_none] at h hca
               simp_all
  cases e <;> simp only [collectPowersApply, reduceCtorEq] at hs
  rename_i es
  split at hs
  · rename_i l t hm
    cases hs
    simp only [Def_mul] at hd ⊢
    refine mergePowers_def ρ es l t hm (fun b e fs others hg => ?_) hd
    simp only [collectAssumed, hg] at hna
    split at hna
    · rename_i hsafe; exact FoldDefOK_of_safe ρ _ _ hsafe
    · simp at hna
  · cases hs

/-! ## Function values -/

theorem FnOK_ln (x : ℝ) : FnOK "ln" x ↔ 0 < x := by simp [FnOK]
theorem FnOK_sqrt (x : ℝ) : FnOK "sqrt" x ↔ 0 ≤ x := by simp [FnOK]
theorem FnOK_tan (x : ℝ) : FnOK "tan" x ↔ Real.cos x ≠ 0 := by simp [FnOK]

/-- `b^p > 0` for an odd integer `p` exactly when `b > 0`: so `ln(b^p) = p ln b` keeps the domain. -/
theorem pos_of_odd_zpow {b : ℝ} {m : ℤ} (hm : Odd m) (h : 0 < b ^ m) : 0 < b := by
  by_contra hb
  exact absurd ((hm.zpow_nonpos_iff).mpr (not_lt.mp hb)) (not_le.mpr h)

theorem intOdd_odd {p : Expr} (h : intOdd p = true) : ∃ m, intExp p = some m ∧ Odd m := by
  unfold intOdd at h
  split at h
  · rename_i m hm
    refine ⟨m, hm, ?_⟩
    rw [← Int.not_even_iff_odd, Int.even_iff]
    simpa using h
  · cases h

/-- Every case of `functionApply` that assumes nothing keeps the domain. -/
theorem functionApply_def {e : Expr} {res : RuleResult} (hs : functionApply e = some res)
    (hna : (functionAssumed e).isNone = true) (ρ : EnvR) (hd : Def ρ e) : Def ρ res.result := by
  unfold functionApply at hs
  split at hs
  · -- sin u / cos u = tan u
    rename_i es
    split at hs
    · rename_i u others hft
      cases hs
      obtain ⟨c, hc, hperm⟩ := findTan_perm es hft
      rw [isCosInv_eq hc] at hperm
      simp only [Def_mul] at hd
      have hd' := (DefList_perm ρ hperm).mp hd
      simp only [DefList, Def_fn₁, Def_pow] at hd'
      obtain ⟨⟨du, -⟩, ⟨-, -, hok⟩, dothers⟩ := hd'
      apply Def_mulN
      refine ⟨(Def_fn₁ ρ _ _).mpr ⟨du, ?_⟩, dothers⟩
      rw [FnOK_tan]
      have : evalR ρ Expr.minusOne = ((-1 : ℤ) : ℝ) := by simp [Expr.minusOne, Q.minusOne]
      rw [evalR_fn₁, this, powOK_int] at hok
      rcases hok with h | h
      · simpa [applyFn] using h
      · norm_num at h
    · cases hs
  · -- √a = a^(1/2)
    cases hs
    simp only [Def_fn₁, FnOK_sqrt] at hd
    refine (Def_pow ρ _ _).mpr ⟨hd.1, trivial, ?_⟩
    rcases lt_or_eq_of_le hd.2 with h | h
    · exact Or.inl h
    · right; right
      refine ⟨h.symm, ?_⟩
      simp only [evalR_num]
      have : ((Q.ofRat (mkRat 1 2)).val : ℝ) = 1 / 2 := by
        show ((mkRat 1 2 : ℚ) : ℝ) = 1 / 2
        rw [Rat.mkRat_eq_div]; push_cast; norm_num
      rw [this]; norm_num
  · -- ln
    rename_i a
    split at hs
    · cases hs; simp
    · split at hs
      · cases hs
        simp only [Def_fn₁] at hd
        exact ((Def_fn₁ ρ _ _).mp hd.1).1
      · rename_i b p
        cases hs
        simp only [functionAssumed, Option.isNone_iff_eq_none, ite_eq_left_iff, reduceCtorEq, imp_false,
          not_not] at hna
        obtain ⟨m, hm, hodd⟩ := intOdd_odd hna
        simp only [Def_fn₁, Def_pow, FnOK_ln] at hd
        obtain ⟨⟨db, dp, -⟩, hpos⟩ := hd
        rw [evalR_pow, evalR_of_intExp hm, Real.rpow_intCast] at hpos
        refine (Def_mul ρ _).mpr ⟨dp, (Def_fn₁ ρ _ _).mpr ⟨db, ?_⟩, trivial⟩
        rw [FnOK_ln]; exact pos_of_odd_zpow hodd hpos
      · cases hs
  · -- exp
    rename_i a
    split at hs
    · cases hs; simp
    · split at hs
      · simp [functionAssumed] at hna
      · cases hs
  · rename_i a; split at hs
    · cases hs; simp
    · cases hs
  · rename_i a; split at hs
    · cases hs; simp
    · cases hs
  · cases hs; simp
  · cases hs; simp
  · cases hs

theorem functionRules_soundD : RuleSoundD functionRules := RuleSoundD.of functionRules_soundR fun e res h ρ hd => by
  simp only [functionRules] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact functionApply_def h hc.1 ρ hd
  · cases h

theorem functionReal_soundD : RuleSoundD functionReal := RuleSoundD.of functionReal_soundR fun e res h ρ hd => by
  simp only [functionReal, functionRealWith] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.true_and] at hc
    exact functionApply_def h (functionAssumed_none_of_realCase hc) ρ hd
  · cases h

/-! ## The fold -/

/-- **Every rule the simplifier runs without an assumption keeps the domain.** -/
theorem simpRulesSafe_soundD : ∀ r ∈ simpRulesSafe, RuleSoundD r := by
  intro r hr
  simp only [simpRulesSafe, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact flatten_soundD
  · exact identity_soundD
  · exact foldConstants_soundD
  · exact functionRules_soundD
  · exact functionReal_soundD
  · exact powerRules_soundD
  · exact collectPowers_soundD
  · exact collectTerms_soundD

/-- **Simplifying without an assumption keeps the domain**: wherever the input is defined, the
normal form is, with the same value. -/
theorem normalizeSafe_soundD (e : Expr) (s : Array Step) :
    DomEq e ((normalize simpRulesSafe e).run' s) :=
  normalize_sound_for domCongruence simpRulesSafe simpRulesSafe_soundD e s

/-- **…and the old `ln(b^p) = p ln b` for an even `p` did not**: `ln(x²)` is defined at `x = −2`, where
`2 ln x` is not. -/
theorem not_lnEvenPow_def :
    Def (fun _ => -2) (.fn "ln" [.pow (.var "x") (.num (Q.ofInt 2))]) ∧
    ¬ Def (fun _ => -2) (.mul [.num (Q.ofInt 2), .fn "ln" [.var "x"]]) := by
  constructor
  · simp only [Def_fn₁, Def_pow, Def_var, Def_num, true_and, FnOK_ln, evalR_pow, evalR_var, evalR_num, Q_val_ofInt]
    refine ⟨?_, ?_⟩
    · rw [show ((((2 : ℤ) : ℚ)) : ℝ) = ((2 : ℤ) : ℝ) by push_cast; rfl, powOK_int]; norm_num
    · rw [show ((((2 : ℤ) : ℚ)) : ℝ) = ((2 : ℤ) : ℝ) by push_cast; rfl, Real.rpow_intCast]; norm_num
  · simp [DefList, FnOK_ln]

/-! ## The pipeline's other value rules: parity, radicals, square roots -/

/-- A pipeline rule keeps definedness: wherever its input is defined, its output is. -/
abbrev PlainDef (r : PlainRule) : Prop := ∀ e res, r.apply e = some res → ∀ ρ, Def ρ e → Def ρ res.result

theorem Def_sqrt_pow (ρ : EnvR) {a : Expr} (h : Def ρ (.fn "sqrt" [a])) :
    Def ρ (.pow a (.num (Q.ofRat (mkRat 1 2)))) := by
  simp only [Def_fn₁, FnOK_sqrt] at h
  refine (Def_pow ρ _ _).mpr ⟨h.1, trivial, ?_⟩
  rcases lt_or_eq_of_le h.2 with h' | h'
  · exact Or.inl h'
  · right; right
    refine ⟨h'.symm, ?_⟩
    have : ((Q.ofRat (mkRat 1 2)).val : ℝ) = 1 / 2 := by
      show ((mkRat 1 2 : ℚ) : ℝ) = 1 / 2
      rw [Rat.mkRat_eq_div]; push_cast; norm_num
    rw [evalR_num, this]; norm_num

theorem sqrtPower_def : PlainDef sqrtPower := fun e res h ρ hd => by
  simp only [sqrtPower] at h
  split at h
  · split at h
    · cases h
    · cases h; exact Def_sqrt_pow ρ hd
  · cases h

theorem sqrtRadical_def : PlainDef sqrtRadical := fun e res h ρ hd => by
  simp only [sqrtRadical] at h
  split at h
  · split at h
    · cases h; exact Def_sqrt_pow ρ hd
    · cases h
  · cases h

/-- A power of numerals with a non-negative base is defined when the base is positive or the
exponent non-negative. -/
theorem Def_numPow (ρ : EnvR) {a y : Q} (h : 0 < a.val ∨ (0 ≤ a.val ∧ 0 ≤ y.val)) :
    Def ρ (.pow (.num a) (.num y)) := by
  refine (Def_pow ρ _ _).mpr ⟨trivial, trivial, ?_⟩
  simp only [evalR_num]
  rcases h with h | ⟨h0, hy⟩
  · exact Or.inl (by exact_mod_cast h)
  · rcases lt_or_eq_of_le h0 with h | h
    · exact Or.inl (by exact_mod_cast h)
    · rcases lt_or_eq_of_le hy with hy | hy
      · right; right; exact ⟨by rw [← h]; simp, by exact_mod_cast hy⟩
      · right; left; exact ⟨0, by rw [← hy]; simp, Or.inr le_rfl⟩

theorem mergeRadicals_def (ρ : EnvR) {s t m : Expr} (h : mergeRadicals s t = some m) : Def ρ m := by
  unfold mergeRadicals at h
  split at h
  · rename_i k₁ b₁ x₁ k₂ b₂ x₂ _ _
    dsimp only at h
    split at h
    · cases h
      have hrad : Def ρ (.pow (.num (Q.ofInt (qthPowerPart b₁.val.num.toNat x₁.val.den).2))
          (.num (Q.ofRat (mkRat (x₁.val.num % (x₁.val.den : ℤ)) x₁.val.den)))) := by
        apply Def_numPow; right
        refine ⟨by simp [Q.ofInt], ?_⟩
        show (0 : ℚ) ≤ mkRat _ _
        rw [Rat.mkRat_eq_div]
        apply div_nonneg
        · exact_mod_cast Int.emod_nonneg _ (by exact_mod_cast (Rat.den_nz x₁.val))
        · positivity
      split
      · trivial
      · split
        · trivial
        · split
          · exact hrad
          · exact (Def_mul ρ _).mpr ⟨trivial, hrad, trivial⟩
    · cases h
  · cases h

theorem mulRadicalPair_def (ρ : EnvR) {s t m : Expr} (h : mulRadicalPair s t = some m) : Def ρ m := by
  unfold mulRadicalPair at h
  split at h
  · rename_i a x b y
    split at h
    · rename_i hg
      cases h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq] at hg
      obtain ⟨⟨⟨⟨⟨⟨ha, ha2⟩, hb⟩, hb2⟩, _⟩, _⟩, _⟩ := hg
      have hpa : (0 : ℚ) < a.val := by exact_mod_cast Q_pos_of_ge_two ha ha2
      have hpb : (0 : ℚ) < b.val := by exact_mod_cast Q_pos_of_ge_two hb hb2
      apply Def_numPow; left
      simp only [Q_val_mul, Q_val_zpow]
      positivity
    · cases h
  · cases h

theorem collectRadicals_def : PlainDef collectRadicals := fun e res h ρ hd => by
  simp only [collectRadicals] at h
  split at h
  · rename_i es
    split at h
    · rename_i m others hfp
      split at h
      · cases h
        obtain ⟨s, t, hst, hperm⟩ := findPair_perm _ es hfp
        simp only [Def_add] at hd
        have hd' := (DefList_perm ρ hperm).mp hd
        exact Def_addN ρ _ ⟨mergeRadicals_def ρ hst, hd'.2.2⟩
      · cases h
    · cases h
  · cases h

theorem mulRadicals_def : PlainDef mulRadicals := fun e res h ρ hd => by
  simp only [mulRadicals] at h
  split at h
  · rename_i es
    split at h
    · rename_i m others hfp
      split at h
      · cases h
        obtain ⟨s, t, hst, hperm⟩ := findPair_perm _ es hfp
        simp only [Def_mul] at hd
        have hd' := (DefList_perm ρ hperm).mp hd
        exact Def_mulN ρ _ ⟨mulRadicalPair_def ρ hst, hd'.2.2⟩
      · cases h
    · cases h
  · cases h

theorem radicalBase_def : PlainDef radicalBase := fun e res h ρ hd => by
  simp only [radicalBase] at h
  split at h
  · rename_i a q
    split at h
    · rename_i hg
      split at h
      · rename_i r k hpp
        split at h
        · cases h
          simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hg
          obtain ⟨⟨ha, ha2⟩, _⟩ := hg
          have hrk := perfectPower_spec hpp
          apply Def_numPow; left
          have hr : r ≠ 0 := by
            rintro rfl
            have : (a.val.num.toNat : ℤ) = a.val.num := Int.toNat_of_nonneg (by omega)
            cases k with
            | zero => simp at hrk; omega
            | succ k => simp at hrk; omega
          simp only [Q_val_ofInt]
          exact_mod_cast Nat.pos_of_ne_zero hr
        · cases h
      · cases h
    · cases h
  · cases h

theorem prodR_ne_zero_mem (ρ : EnvR) : ∀ {fs : List Expr} {a : Expr}, a ∈ fs → prodR ρ fs ≠ 0 → evalR ρ a ≠ 0
  | b :: bs, a, ha, h => by
    rw [prodR_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact left_ne_zero_of_mul h
    · exact prodR_ne_zero_mem ρ ha (right_ne_zero_of_mul h)

theorem parityPowMul_def : PlainDef parityPowMul := fun e res h ρ hd => by
  simp only [parityPowMul] at h
  split at h
  · rename_i fs n
    split at h
    · rename_i hn
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
      have hint := hn.1.1
      simp only [Def_pow, Def_mul, evalR_mul, evalR_num, Q_cast_isInt hint, powOK_int] at hd
      obtain ⟨dfs, -, hok⟩ := hd
      simp only [Def_mul, DefList_iff, List.mem_map]
      rintro _ ⟨a, ha, rfl⟩
      refine (Def_pow ρ _ _).mpr ⟨(DefList_iff ρ fs).mp dfs a ha, trivial, ?_⟩
      rw [evalR_num, Q_cast_isInt hint, powOK_int]
      rcases hok with h0 | h0
      · exact Or.inl (prodR_ne_zero_mem ρ ha h0)
      · exact Or.inr h0
    · cases h
  · cases h

theorem parityPowPow_def : PlainDef parityPowPow := fun e res h ρ hd => by
  simp only [parityPowPow] at h
  split at h
  · rename_i b m n
    split at h
    · rename_i hn
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hn
      obtain ⟨⟨⟨hint, hz⟩, -⟩, -⟩ := hn
      simp only [Def_pow] at hd
      obtain ⟨⟨db, dm, okm⟩, -, okn⟩ := hd
      refine (Def_pow ρ _ _).mpr ⟨db, (Def_mul ρ _).mpr ⟨dm, trivial, trivial⟩, ?_⟩
      have hnz : (n.val : ℝ) ≠ 0 := by
        intro h0
        have h1 : n.val = 0 := by exact_mod_cast h0
        have h2 : n.isZero = true := by simp [Q.isZero, h1]
        revert hz; simp [h2]
      rw [evalR_pow, evalR_num, Q_cast_isInt hint, powOK_int] at okn
      rw [evalR_mul, prodR_cons, prodR_cons, prodR_nil, mul_one, evalR_num, Q_cast_isInt hint]
      rw [Q_cast_isInt hint] at hnz
      rcases okm with hb | ⟨k, hk, hk'⟩ | ⟨hb0, hm0⟩
      · exact Or.inl hb
      · rw [hk, ← Int.cast_mul, powOK_int]
        rw [hk, Real.rpow_intCast] at okn
        rcases hk' with hb | hk0
        · exact Or.inl hb
        · by_cases hb0 : evalR ρ b = 0
          · right
            rcases lt_or_eq_of_le hk0 with hlt | heq
            · rcases okn with hne | hn0
              · exfalso; apply hne; rw [hb0]; exact zero_zpow _ hlt.ne'
              · exact Int.mul_nonneg hlt.le hn0
            · rw [← heq]; simp
          · exact Or.inl hb0
      · right; right
        refine ⟨hb0, ?_⟩
        rw [hb0, Real.zero_rpow hm0.ne'] at okn
        rcases okn with hne | hn0
        · exact absurd rfl hne
        · have hn0' : (0 : ℝ) < (n.val.num : ℝ) := by
            rcases lt_or_eq_of_le (show (0 : ℝ) ≤ (n.val.num : ℝ) by exact_mod_cast hn0) with h | h
            · exact h
            · exact absurd h.symm hnz
          exact mul_pos hm0 hn0'
    · cases h
  · cases h

end MathProofs
