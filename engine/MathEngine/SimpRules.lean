import MathEngine.Rewrite
import MathEngine.Semantics
import MathEngine.Print
/-!
# `simp.*` — the simplification rules, each with its termination obligation

Ported from `simplify.ts`. Every rule is a `Rule simpW`: it comes with a proof that it strictly
decreases the weighted node count under the weights below. The weights were chosen by tabulating
the rules (see the book, "why simplification terminates"):

| node | weight | why |
|---|---|---|
| num | 2 | cheapest; rules replace whole nodes by a numeral |
| add, mul | 4 | `add [] ⟶ 0` needs add > num; `ln(b^p) ⟶ p·ln b` needs pow > mul |
| pow | 5 | `sqrt a ⟶ a^(1/2)` needs fn > pow + num |
| var, fn, matrix | 8 | `t·t ⟶ t^2` needs every non-numeral base to outweigh pow + num = 7 |

Three rules are guarded slightly more tightly than in the reference so that the obligation holds
for *all* inputs, not just normalized ones (`bigBase`), one case is dropped (`8^(2/3)`, an exact
root with a non-unit numerator: same shape before and after), and `(ab)^n ⟶ a^n b^n` moves to the
`expand` rule set because it duplicates the exponent and no additive measure can decrease.
-/
set_option linter.unusedSimpArgs false  -- the shared `rule_leaf` simp set is deliberately broad

namespace MathEngine
open Expr

-- ---------------------------------------------------------------------------
-- Weights
-- ---------------------------------------------------------------------------

def simpWeight : Expr → Nat
  | .num _ => 2
  | .var _ => 8
  | .add _ => 4
  | .mul _ => 4
  | .pow _ _ => 5
  | .fn _ _ => 8
  | .matrix _ => 8

def simpW : Weights where
  w := simpWeight
  pos e := by cases e <;> simp [simpWeight]
  head e cs := by
    cases e <;> try rfl
    match cs with
    | [_, _] => rfl
    | [] | [_] | _ :: _ :: _ :: _ => rfl

/-- Every node weighs at least 2 under `simpW`. -/
theorem measure_ge_two (e : Expr) : 2 ≤ measure simpW e := by
  rw [measure_eq]; cases e <;> simp [simpW, simpWeight] <;> omega

local notation "M" => measure simpW
local notation "ML" => measureList simpW

theorem ML_cons (e : Expr) (es : List Expr) : ML (e :: es) = M e + ML es := rfl

/-- A base that outweighs `pow + num = 7`: everything except numerals and sums/products with
fewer than two arguments. -/
def bigBase : Expr → Bool
  | .num _ => false
  | .add (_ :: _ :: _) | .mul (_ :: _ :: _) => true
  | .add _ | .mul _ => false
  | _ => true

theorem M_num (q : Q) : M (.num q) = 2 := rfl
theorem M_var (x : String) : M (.var x) = 8 := rfl
theorem M_add (es : List Expr) : M (.add es) = 4 + ML es := rfl
theorem M_mul (es : List Expr) : M (.mul es) = 4 + ML es := rfl
theorem M_pow (b x : Expr) : M (.pow b x) = 5 + M b + M x := rfl
theorem M_fn (f : String) (es : List Expr) : M (.fn f es) = 8 + ML es := rfl
theorem M_matrix (rows : List (List Expr)) : M (.matrix rows) = 8 + measureRows simpW rows := rfl
theorem ML_nil : ML [] = 0 := rfl
theorem M_zero : M Expr.zero = 2 := rfl
theorem M_one : M Expr.one = 2 := rfl

theorem bigBase_measure {e : Expr} (h : bigBase e = true) : 8 ≤ M e := by
  cases e with
  | add es => match es, h with
    | x :: y :: _, _ => rw [M_add, ML_cons, ML_cons]; have := measure_ge_two x; have := measure_ge_two y; omega
  | mul es => match es, h with
    | x :: y :: _, _ => rw [M_mul, ML_cons, ML_cons]; have := measure_ge_two x; have := measure_ge_two y; omega
  | num _ => simp [bigBase] at h
  | pow b x => rw [M_pow]; have := measure_ge_two b; have := measure_ge_two x; omega
  | var _ => rw [M_var]; omega
  | fn _ _ => rw [M_fn]; omega
  | matrix _ => rw [M_matrix]; omega

-- ---------------------------------------------------------------------------
-- Generic list lemmas about the measure
-- ---------------------------------------------------------------------------

theorem ML_filter_le (p : Expr → Bool) (es : List Expr) : ML (es.filter p) ≤ ML es := by
  induction es with
  | nil => simp [measureList]
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases hp : p e = true
    · simp only [hp, ↓reduceIte, measureList]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, measureList]; omega

theorem ML_filter_lt (p : Expr → Bool) (es : List Expr) (h : es.any (fun e => !p e) = true) :
    ML (es.filter p) < ML es := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.any_cons, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    simp only [List.filter_cons]
    have hle := ML_filter_le p es
    have h2 := measure_ge_two e
    by_cases hp : p e = true
    · have h' : es.any (fun e => !p e) = true := by
        rcases h with h | h
        · rw [hp] at h; exact absurd h (by decide)
        · exact h
      have := ih h'
      simp only [hp, ↓reduceIte, measureList]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte, measureList]; omega

/-- Splitting a list by a predicate splits its measure. -/
theorem ML_filter_split (p : Expr → Bool) (es : List Expr) :
    ML es = ML (es.filter p) + ML (es.filter (fun e => !p e)) := by
  induction es with
  | nil => simp [measureList]
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases hp : p e = true
    · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte, measureList]; omega
    · simp only [hp, Bool.not_false, Bool.false_eq_true, ↓reduceIte, measureList]; omega

theorem ML_removeFirst {p : Expr → Bool} {f : Expr} {es : List Expr} (h : es.find? p = some f) :
    ML (removeFirst p es) + M f = ML es := by
  have := measureList_perm simpW (perm_find?_removeFirst p es f h)
  simp only [measureList] at this; omega

theorem M_addN_le (l : List Expr) : M (addN l) ≤ 4 + ML l := by
  match l with
  | [e] => simp only [addN, measureList]; omega
  | [] | _ :: _ :: _ => simp [addN, measure, simpW, simpWeight]

theorem M_mulN_le (l : List Expr) : M (mulN l) ≤ 4 + ML l := by
  match l with
  | [e] => simp only [mulN, measureList]; omega
  | [] | _ :: _ :: _ => simp [mulN, measure, simpW, simpWeight]

-- ---------------------------------------------------------------------------
-- Helpers shared with the reference implementation
-- ---------------------------------------------------------------------------

def isAdd : Expr → Bool | .add _ => true | _ => false
def isMul : Expr → Bool | .mul _ => true | _ => false
def unAdd : Expr → List Expr | .add xs => xs | e => [e]
def unMul : Expr → List Expr | .mul xs => xs | e => [e]
def numOf : Expr → Q | .num q => q | _ => Q.zero
def sumQ (es : List Expr) : Q := es.foldl (fun s e => s + numOf e) Q.zero
def prodQ (es : List Expr) : Q := es.foldl (fun s e => s * numOf e) Q.one
/-- `base ^ exp`; a non-power is `base ^ 1`. -/
def baseExp : Expr → Expr × Expr | .pow b x => (b, x) | e => (e, Expr.one)
/-- Sum of two exponents, folded when both are numerals. -/
def addExp (a b : Expr) : Expr :=
  match a, b with
  | .num p, .num q => .num (p + q)
  | _, _ => .add [a, b]

/-- Integer `n`-th root of a rational, if exact. -/
def exactRoot (r : Rat) (n : Nat) : Option Rat :=
  if r < 0 || n = 0 then none else
  do let a ← natRoot n r.num.natAbs; let b ← natRoot n r.den; some (mkRat a b)

-- ---------------------------------------------------------------------------
-- simp.flatten (silent)
-- ---------------------------------------------------------------------------

def flattenApply : Expr → Option RuleResult
  | .add es => if es.any isAdd then some ⟨.add (es.flatMap unAdd), "associativity", none, none⟩ else none
  | .mul es => if es.any isMul then some ⟨.mul (es.flatMap unMul), "associativity", none, none⟩ else none
  | _ => none

theorem ML_unAdd_le (e : Expr) : ML (unAdd e) ≤ M e := by
  cases e <;> simp [unAdd, measure, simpW, simpWeight, measureList]
theorem ML_unAdd_lt (e : Expr) (h : isAdd e = true) : ML (unAdd e) < M e := by
  cases e <;> simp [isAdd] at h <;> simp [unAdd, measure, simpW, simpWeight]
theorem ML_unMul_le (e : Expr) : ML (unMul e) ≤ M e := by
  cases e <;> simp [unMul, measure, simpW, simpWeight, measureList]
theorem ML_unMul_lt (e : Expr) (h : isMul e = true) : ML (unMul e) < M e := by
  cases e <;> simp [isMul] at h <;> simp [unMul, measure, simpW, simpWeight]

theorem ML_flatMap_lt (f : Expr → List Expr) (p : Expr → Bool) (hle : ∀ e, ML (f e) ≤ M e)
    (hlt : ∀ e, p e = true → ML (f e) < M e) (es : List Expr) (h : es.any p = true) :
    ML (es.flatMap f) < ML es := by
  induction es with
  | nil => simp at h
  | cons e es ih =>
    simp only [List.flatMap_cons, List.any_cons, Bool.or_eq_true] at h ⊢
    have hb := ML_flatMap_le f hle es
    simp only [measureList_append, measureList] at *
    rcases h with h | h
    · have := hlt e h; omega
    · have := ih h; have := hle e; omega
where
  ML_flatMap_le (f : Expr → List Expr) (hle : ∀ e, ML (f e) ≤ M e) : ∀ es : List Expr, ML (es.flatMap f) ≤ ML es
    | [] => by simp [measureList]
    | e :: es => by
      simp only [List.flatMap_cons, measureList_append, measureList]
      have := hle e; have := ML_flatMap_le f hle es; omega

def flatten : Rule simpW where
  name := "simp.flatten"
  silent := true
  apply := flattenApply
  decreasing e r h := by
    cases e <;> simp only [flattenApply, reduceCtorEq] at h
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; rename_i hany
      simp only [M_add]; have := ML_flatMap_lt unAdd isAdd ML_unAdd_le ML_unAdd_lt _ hany; omega
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; rename_i hany
      simp only [M_mul]; have := ML_flatMap_lt unMul isMul ML_unMul_le ML_unMul_lt _ hany; omega

-- ---------------------------------------------------------------------------
-- simp.identity
-- ---------------------------------------------------------------------------

def identityApply : Expr → Option RuleResult
  | .add [] => some ⟨Expr.zero, "An empty sum is 0.", none, none⟩
  | .add [e] => some ⟨e, "A sum of one term is that term.", none, none⟩
  | .add es => if es.any isZero then some ⟨addN (es.filter (fun e => !isZero e)), "$a + 0 = a$: zero is the additive identity.", none, none⟩ else none
  | .mul [] => some ⟨Expr.one, "An empty product is 1.", none, none⟩
  | .mul [e] => some ⟨e, "A product of one factor is that factor.", none, none⟩
  | .mul es =>
    if es.any isZero then some ⟨Expr.zero, "$a \\cdot 0 = 0$: zero annihilates products.", none, none⟩
    else if es.any isOne then some ⟨mulN (es.filter (fun e => !isOne e)), "$a \\cdot 1 = a$: one is the multiplicative identity.", none, none⟩
    else none
  | _ => none

def identity : Rule simpW where
  name := "simp.identity"
  apply := identityApply
  decreasing e r h := by
    cases e with
    | add es =>
      match es, h with
      | [], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp [measure, measureList, simpW, simpWeight, Expr.zero]
      | [e], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp only [M_add, ML_cons, measureList]; omega
      | x :: y :: rest, h =>
        simp only [identityApply] at h
        split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
        subst h; rename_i hany
        have h1 := M_addN_le ((x :: y :: rest).filter (fun e => !isZero e))
        have h2 := ML_filter_lt (fun e => !isZero e) (x :: y :: rest) (by simpa using hany)
        simp only [M_add] at *; omega
    | mul es =>
      match es, h with
      | [], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp [measure, measureList, simpW, simpWeight, Expr.one]
      | [e], h => simp only [identityApply, Option.some.injEq] at h; subst h; simp only [M_mul, ML_cons, measureList]; omega
      | x :: y :: rest, h =>
        simp only [identityApply] at h
        split at h
        · simp only [Option.some.injEq] at h; subst h; simp only [M_zero, M_mul]; omega
        · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
          subst h; rename_i hany
          have h1 := M_mulN_le ((x :: y :: rest).filter (fun e => !isOne e))
          have h2 := ML_filter_lt (fun e => !isOne e) (x :: y :: rest) (by simpa using hany)
          simp only [M_mul] at *; omega
    | _ => simp [identityApply] at h

-- ---------------------------------------------------------------------------
-- simp.fold-constants
-- ---------------------------------------------------------------------------

/-- Fold the numerals of a sum or product into one. The result is built with `addN`/`mulN`, so when
every term was a numeral the answer is that numeral, not a one-element sum or product that
`simp.identity` would then have to collapse in a step of its own. -/
def foldApply : Expr → Option RuleResult
  | .add es =>
    let nums := es.filter isNum
    if 2 ≤ nums.length then
      some ⟨addN (.num (sumQ nums) :: es.filter (fun e => !isNum e)),
        s!"Arithmetic on constants: {" + ".intercalate (nums.map Expr.toText)} = {(sumQ nums).toText}.", none, none⟩
    else none
  | .mul es =>
    let nums := es.filter isNum
    if 2 ≤ nums.length then
      some ⟨mulN (.num (prodQ nums) :: es.filter (fun e => !isNum e)),
        s!"Arithmetic on constants: {" × ".intercalate (nums.map Expr.toText)} = {(prodQ nums).toText}.", none, none⟩
    else none
  | _ => none

theorem M_of_isNum {e : Expr} (h : isNum e = true) : M e = 2 := by
  cases e with
  | num q => rfl
  | _ => simp [isNum] at h

theorem ML_nums (es : List Expr) : ML (es.filter isNum) = 2 * (es.filter isNum).length := by
  induction es with
  | nil => simp [measureList]
  | cons e es ih =>
    simp only [List.filter_cons]
    by_cases h : isNum e = true
    · simp only [h, ↓reduceIte, measureList, List.length_cons, M_of_isNum h]; omega
    · simp only [h, Bool.false_eq_true, ↓reduceIte]; exact ih

theorem fold_decreasing (es : List Expr) (h : 2 ≤ (es.filter isNum).length) (q : Q) :
    4 + ML (.num q :: es.filter (fun e => !isNum e)) < 4 + ML es := by
  have := ML_filter_split isNum es
  have := ML_nums es
  simp only [ML_cons, M_num] at *; omega

def foldConstants : Rule simpW where
  name := "simp.fold-constants"
  apply := foldApply
  decreasing e r h := by
    cases e <;> simp only [foldApply, reduceCtorEq] at h
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp only [M_add]; exact Nat.lt_of_le_of_lt (M_addN_le _) (fold_decreasing _ ‹_› _)
    · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp only [M_mul]; exact Nat.lt_of_le_of_lt (M_mulN_le _) (fold_decreasing _ ‹_› _)

-- ---------------------------------------------------------------------------
-- simp.function
-- ---------------------------------------------------------------------------

/-- The first element satisfying `p`, and the list without it. -/
def splitFirst (p : Expr → Bool) : List Expr → Option (Expr × List Expr)
  | [] => none
  | x :: xs => if p x then some (x, xs) else (splitFirst p xs).map fun r => (r.1, x :: r.2)

theorem splitFirst_perm (p : Expr → Bool) : ∀ (l : List Expr) {c l'}, splitFirst p l = some (c, l') →
    p c = true ∧ l.Perm (c :: l')
  | [], _, _, h => by simp [splitFirst] at h
  | x :: xs, c, l', h => by
    simp only [splitFirst] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨‹_›, List.Perm.refl _⟩
    · cases hs : splitFirst p xs with
      | none => simp [hs] at h
      | some r =>
        obtain ⟨c', l''⟩ := r
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hp, hperm⟩ := splitFirst_perm p xs hs
        exact ⟨hp, (hperm.cons x).trans (List.Perm.swap c' x l'')⟩

/-- `cos u ^ (-1)`, structurally. -/
def isCosInv (u : Expr) : Expr → Bool
  | .pow (.fn "cos" [v]) x => equal u v && equal x Expr.minusOne
  | _ => false

theorem isCosInv_eq {u c : Expr} (h : isCosInv u c = true) : c = .pow (.fn "cos" [u]) Expr.minusOne := by
  unfold isCosInv at h
  split at h
  · rename_i v x
    simp only [Bool.and_eq_true] at h
    rw [Expr.beq_eq u v h.1, Expr.beq_eq x Expr.minusOne h.2]
  · simp at h

def sinArg : Expr → Option Expr | .fn "sin" [u] => some u | _ => none

theorem sinArg_eq {f u : Expr} (h : sinArg f = some u) : f = .fn "sin" [u] := by
  unfold sinArg at h; split at h <;> simp_all

/-- `sin u` and `cos u ^ (-1)` among the factors of a product, and the other factors. `acc` holds
the factors already passed over, so the cosine may sit on either side of the sine. -/
def findTanGo (acc : List Expr) : List Expr → Option (Expr × List Expr)
  | [] => none
  | f :: rest =>
    match sinArg f with
    | some u =>
      match splitFirst (isCosInv u) (acc ++ rest) with
      | some (_, others) => some (u, others)
      | none => findTanGo (acc ++ [f]) rest
    | none => findTanGo (acc ++ [f]) rest

/-- `findTanGo` looks at every pair of factors; a product without a sine has none to find. -/
def findTan (es : List Expr) : Option (Expr × List Expr) :=
  if es.any fun f => (sinArg f).isSome then findTanGo [] es else none

theorem findTanGo_perm : ∀ (l acc : List Expr) {u others}, findTanGo acc l = some (u, others) →
    ∃ c, isCosInv u c = true ∧ (acc ++ l).Perm (.fn "sin" [u] :: c :: others)
  | [], _, _, _, h => by simp [findTanGo] at h
  | f :: rest, acc, u, others, h => by
    simp only [findTanGo] at h
    split at h
    · rename_i u' hu'
      split at h
      · rename_i c os hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hc, hperm⟩ := splitFirst_perm _ _ hs
        rw [sinArg_eq hu']
        exact ⟨c, hc, List.perm_middle.trans (hperm.cons _)⟩
      · obtain ⟨c, hc, hperm⟩ := findTanGo_perm rest (acc ++ [f]) h
        exact ⟨c, hc, by simpa [List.append_assoc] using hperm⟩
    · obtain ⟨c, hc, hperm⟩ := findTanGo_perm rest (acc ++ [f]) h
      exact ⟨c, hc, by simpa [List.append_assoc] using hperm⟩

theorem findTan_perm (es : List Expr) {u others} (h : findTan es = some (u, others)) :
    ∃ c, isCosInv u c = true ∧ es.Perm (.fn "sin" [u] :: c :: others) := by
  unfold findTan at h
  split at h
  · simpa using findTanGo_perm es [] h
  · cases h

def functionApply : Expr → Option RuleResult
  | .mul es =>
    match findTan es with
    | some (u, others) => some ⟨mulN (.fn "tan" [u] :: others), "$\\sin u / \\cos u = \\tan u$.", none, none⟩
    | none => none
  | .fn "sqrt" [a] => some ⟨.pow a (.num (Q.ofRat (mkRat 1 2))), "$\\sqrt{a} = a^{1/2}$; we work with a single power form internally.", none, none⟩
  | .fn "ln" [a] =>
    if isOne a then some ⟨Expr.zero, "$\\ln 1 = 0$.", none, none⟩ else
    match a with
    | .fn "exp" [x] => some ⟨x, "$\\ln(e^x) = x$: ln and exp are inverses.", none, none⟩
    | .pow b p => some ⟨.mul [p, .fn "ln" [b]], "$\\ln(b^p) = p \\ln b$.", none, none⟩
    | _ => none
  | .fn "exp" [a] =>
    if isZero a then some ⟨Expr.one, "$e^0 = 1$.", none, none⟩ else
    match a with
    | .fn "ln" [x] => some ⟨x, "$e^{\\ln x} = x$: exp and ln are inverses.", none, none⟩
    | _ => none
  | .fn "sin" [a] => if isZero a then some ⟨Expr.zero, "$\\sin 0 = 0$.", none, none⟩ else none
  | .fn "cos" [a] => if isZero a then some ⟨Expr.one, "$\\cos 0 = 1$.", none, none⟩ else none
  | .fn "abs" [.num q] => some ⟨.num q.abs, "Absolute value of a constant.", none, none⟩
  | .fn "sign" [.num q] =>
    some ⟨.num (if q.isNeg then Q.minusOne else if q.isZero then Q.zero else Q.one), "The sign of a constant: $-1$, $0$ or $1$.", none, none⟩
  | _ => none

/-- Closes a leaf of a rule proof: either the arm returned `none`, or substitute the result and
count nodes. -/
macro "rule_leaf" h:ident : tactic =>
  `(tactic| first
    | (simp only [reduceCtorEq] at $h:ident; done)
    | (simp only [Option.some.injEq] at $h:ident; subst $h:ident
       (try subst_vars)
       simp only [M_num, M_var, M_add, M_mul, M_pow, M_fn, M_matrix, ML_cons, ML_nil, M_zero, M_one]
       omega))

theorem functionApply_decreasing : ∀ e r, functionApply e = some r → measure simpW r.result < measure simpW e := by
    intro e r h
    cases e <;> simp only [functionApply, reduceCtorEq] at h
    · -- sin u / cos u = tan u
      rename_i es
      split at h
      · rename_i u others hft
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨c, hc, hperm⟩ := findTan_perm es hft
        rw [isCosInv_eq hc] at hperm
        have hml := measureList_perm simpW hperm
        cases others with
        | nil =>
          simp only [mulN, M_mul, hml, ML_cons, ML_nil, M_fn, M_pow, M_num, Expr.minusOne]; omega
        | cons o os =>
          simp only [mulN, M_mul, hml, ML_cons, ML_nil, M_fn, M_pow, M_num, Expr.minusOne]; omega
      · simp at h
    · rename_i f args
      repeat' split at h
      all_goals (try injections)
      all_goals (try subst_vars)
      all_goals (simp only [M_num, M_var, M_add, M_mul, M_pow, M_fn, M_matrix, ML_cons, ML_nil, M_zero, M_one]; omega)

/-- A numeral that is an integer, as an integer. -/
def intExp : Expr → Option Int
  | .num q => if q.isInt then some q.val.num else none
  | _ => none

/-- An odd integer numeral. -/
def intOdd (p : Expr) : Bool :=
  match intExp p with
  | some n => n % 2 != 0
  | none => false

/-- The term a `simp.function` step needs positive, where it needs one: `x` in `exp(ln x) = x`, and
`b` in `ln(b^p) = p ln b` for an exponent `p` that is not an odd integer (for an even one, `ln(x²)`
is defined at `x = −2` and `2 ln x` is not). -/
def functionAssumed : Expr → Option Expr
  | .fn "exp" [.fn "ln" [x]] => some x
  | .fn "ln" [.pow b p] => if intOdd p then none else some b
  | _ => none

/-- The cases that hold over ℝ, where they keep the domain too, but not over ℂ's principal branch:
`ln(exp x) = x` (at `x = 4i` it is `(4 − 2π)i`) and `ln(b^p) = p ln b` for an odd integer `p`. -/
def functionRealCase : Expr → Bool
  | .fn "ln" [.fn "exp" [_]] => true
  | .fn "ln" [.pow _ p] => intOdd p
  | _ => false

/-- A rule that fires only where `p` holds, with `f`'s result. -/
theorem gate_some {p : Bool} {f : Option RuleResult} {r : RuleResult} (h : (if p then f else none) = some r) :
    f = some r := by
  split at h <;> simp_all

/-- `simp.function` where it holds for every real and every complex number, on the whole domain. -/
def functionRules : Rule simpW where
  name := "simp.function"
  apply e := if (functionAssumed e).isNone && !functionRealCase e then functionApply e else none
  decreasing e r h := functionApply_decreasing e r (gate_some h)

/-- `simp.function` where it holds over ℝ only: off (`real = false`) in a cell read over ℂ. -/
def functionRealWith (real : Bool) : Rule simpW where
  name := "simp.function.real"
  apply e := if real && functionRealCase e then functionApply e else none
  decreasing e r h := functionApply_decreasing e r (gate_some h)

def functionReal : Rule simpW := functionRealWith true

/-- `simp.function` where it needs a positive argument: the step says so. -/
def functionAssumingApply (e : Expr) : Option RuleResult :=
  match functionAssumed e with
  | some a => (functionApply e).map fun r => { r with explanation := r.explanation ++ s!" Assuming ${a.toText} > 0$." }
  | none => none

theorem functionAssumingApply_some {e : Expr} {r : RuleResult} (h : functionAssumingApply e = some r) :
    ∃ a r₀, functionAssumed e = some a ∧ functionApply e = some r₀ ∧ r.result = r₀.result ∧ r.error = r₀.error := by
  unfold functionAssumingApply at h
  split at h
  · rename_i a ha
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨a, r₀, ha, h₀, rfl, rfl⟩
  · cases h

def functionAssuming : Rule simpW where
  name := "simp.function.assuming"
  apply := functionAssumingApply
  decreasing e r h := by
    obtain ⟨_, r₀, _, h₀, hres, _⟩ := functionAssumingApply_some h
    rw [hres]; exact functionApply_decreasing e r₀ h₀

-- ---------------------------------------------------------------------------
-- simp.power
-- ---------------------------------------------------------------------------

/-- `p ^ q` for numerals: integer exponents evaluate; `p^(1/n)` evaluates when `p` is a perfect `n`-th power. -/
def powNumeric (p q : Q) : Option RuleResult :=
  -- `0^(-n)` is `1/0`, and core `Rat` (as Mathlib's `ℚ`) makes it 0; the proofs are stated over that
  -- arithmetic, and the reply says so in a warning (`derivationWarnings`, Rpc.lean)
  if q.isInt then some ⟨.num (p.zpow q.val.num), s!"Evaluate the numeric power: {p.toText}^{q.toText} = {(p.zpow q.val.num).toText}.", none, none⟩
  else if q.val.num == 1 then
    match exactRoot p.val q.val.den with
    | some r =>
      let what := match q.val.den with | 2 => "square" | 3 => "cube" | n => s!"{n}th power"
      some ⟨.num (Q.ofRat r p.approx), s!"{p.toText} is a perfect {what}: ${p.toText}^\{1/{q.val.den}} = {r}$.", none, none⟩
    | none => none
  else none

def isPosNum : Expr → Bool | .num q => !q.isNeg && !q.isZero | _ => false

/-- The structural power rules: numeric evaluation and `(b^m)^n = b^(mn)` — for integer `m` and `n`
(any base), or for an integer `n` and a positive numeral base (so `sqrt(2)^2 = 2`; a symbolic base
would need `b ≥ 0`, which `sqrt(x)^2` cannot promise over ℝ). -/
def powerNum : Expr → Expr → Option RuleResult
  | .num p, .num q => powNumeric p q
  | .pow b' (.num m), .num n =>
    if n.isInt && m.isInt then some ⟨.pow b' (.num (m * n)), "$(b^m)^n = b^{mn}$ for integer $n$.", none, none⟩
    else if n.isInt && isPosNum b' then
      some ⟨.pow b' (.num (m * n)), "$(b^m)^n = b^{mn}$ for an integer $n$ and a positive base $b$ (so $\\sqrt{b}^2 = b$).", none, none⟩
    else none
  | _, _ => none

def powerAt (b x : Expr) : Option RuleResult :=
  if isZero x then some ⟨Expr.one, "$b^0 = 1$ (for the domain we work in, $b \\neq 0$).", none, none⟩
  else if isOne x then some ⟨b, "$b^1 = b$.", none, none⟩
  else if isOne b then some ⟨Expr.one, "$1^n = 1$.", none, none⟩
  else if isZero b && isPosNum x then some ⟨Expr.zero, "$0^n = 0$ for $n > 0$.", none, none⟩
  else powerNum b x

def powerApply : Expr → Option RuleResult
  | .pow b x => powerAt b x
  | _ => none

def powerRules : Rule simpW where
  name := "simp.power"
  apply := powerApply
  decreasing e r h := by
    cases e <;> simp only [powerApply, reduceCtorEq] at h
    rename_i b x
    simp only [powerAt] at h
    repeat' split at h
    all_goals try (simp only [powerNum, powNumeric] at h; repeat' split at h)
    all_goals rule_leaf h

-- ---------------------------------------------------------------------------
-- simp.collect-powers
-- ---------------------------------------------------------------------------

/-- Is `e` a power of `b` (a factor `b` counting as `b^1`)? -/
def ofBase (b e : Expr) : Bool := equal (baseExp e).1 b

/-- A big base that two factors share. A few bases are compared pairwise, the first that recurs;
many are sorted and neighbours compared, so a product of `n` factors costs `n log n` rather than `n²`.
This is only where to look: the rule merges whatever factors have the base it returns
(`powerGroup`), and every theorem about the rule holds for any base, so the search may use the
structural order `compare`, which nothing is proved about. (A short product, the kind a proof
computes with, never reaches it.) -/
def repeatedBase (es : List Expr) : Option Expr :=
  let bs := (es.map fun e => (baseExp e).1).filter bigBase
  if bs.length ≤ 8 then firstRepeat bs else adjacent (bs.mergeSort fun a b => compare a b != .gt)
where
  firstRepeat : List Expr → Option Expr
    | [] => none
    | a :: rest => if rest.any (equal a) then some a else firstRepeat rest
  adjacent : List Expr → Option Expr
    | a :: b :: rest => if equal a b then some a else adjacent (b :: rest)
    | _ => none

/-- The factors that share a repeated big base `b`, two or more: `(b, e, fs, others)` with `e` the
first of them, `fs` the rest, and `others` the factors with another base, all in their order. -/
def powerGroup (es : List Expr) : Option (Expr × Expr × List Expr × List Expr) :=
  match repeatedBase es with
  | some b =>
    match es.filter (ofBase b) with
    | e :: f :: fs => if bigBase b then some (b, e, f :: fs, es.filter fun g => !ofBase b g) else none
    | _ => none
  | none => none

theorem powerGroup_spec {es : List Expr} {b e : Expr} {fs others : List Expr}
    (h : powerGroup es = some (b, e, fs, others)) :
    es.Perm (e :: (fs ++ others)) ∧ (baseExp e).1 = b ∧ (∀ f ∈ fs, (baseExp f).1 = b) ∧ fs ≠ [] ∧
      bigBase b = true := by
  unfold powerGroup at h
  split at h
  · rename_i b' _
    split at h
    · rename_i e' f' fs' hfil
      split at h
      · rename_i hbig
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have hmem : ∀ g ∈ e' :: f' :: fs', (baseExp g).1 = b' := fun g hg => by
          rw [← hfil] at hg; exact equal_eq (List.mem_filter.mp hg).2
        refine ⟨?_, hmem e' List.mem_cons_self, fun g hg => hmem g (List.mem_cons_of_mem _ hg), by simp, hbig⟩
        have := List.filter_append_perm (ofBase b') es
        rw [hfil] at this
        exact this.symm
      · cases h
    · cases h
  · cases h

/-- `x` plus each exponent of `fs` in turn: the exponent of the merged power. -/
def expFold (x : Expr) : List Expr → Expr
  | [] => x
  | f :: fs => expFold (addExp x (baseExp f).2) fs

/-- Merge every factor of a repeated big base `b` into one power: `b^m · b^n · … = b^(m+n+…)`.
The exponents are added one factor at a time (`expFold`), so the merge is the pair merge repeated,
and a product of `n` equal factors takes one step, not `n`. -/
def mergePowers (es : List Expr) : Option (List Expr × Expr) :=
  (powerGroup es).map fun (b, e, fs, others) => (.pow b (expFold (baseExp e).2 fs) :: others, b)

def collectPowersApply : Expr → Option RuleResult
  | .mul es =>
    match mergePowers es with
    | some (es', base) => some ⟨.mul es', s!"Same base ${base.toText}$: multiplying powers adds exponents, $b^m \\cdot b^n = b^\{m+n}$.", none, none⟩
    | none => none
  | _ => none

theorem baseExp_cases (e b x : Expr) (h : baseExp e = (b, x)) : e = .pow b x ∨ (e = b ∧ x = Expr.one) := by
  cases e <;> simp [baseExp] at h <;> simp [h]

theorem M_addExp_le (x y : Expr) : M (addExp x y) ≤ 4 + M x + M y := by
  cases x <;> cases y <;> simp [addExp, M_num, M_add, ML_cons, ML_nil] <;> omega

theorem M_addExp_num (p q : Q) : M (addExp (.num p) (.num q)) = 2 := rfl

/-- The merged power is lighter than the two factors it replaces. -/
theorem M_merged_lt (e f b x xf : Expr) (he : baseExp e = (b, x)) (hf : baseExp f = (b, xf)) (hb : bigBase b = true) :
    M (.pow b (addExp x xf)) < M e + M f := by
  have hb8 := bigBase_measure hb
  rcases baseExp_cases e b x he with he' | ⟨he', hx'⟩ <;> rcases baseExp_cases f b xf hf with hf' | ⟨hf', hxf'⟩
  · rw [he', hf']; have := M_addExp_le x xf; rw [M_pow, M_pow, M_pow]; omega
  · rw [he', hf', hxf']; have := M_addExp_le x Expr.one; rw [M_pow, M_pow]; simp only [M_one] at *; omega
  · rw [he', hx', hf']; have := M_addExp_le Expr.one xf; rw [M_pow, M_pow]; simp only [M_one] at *; omega
  · rw [he', hx', hf', hxf', M_pow, Expr.one, M_addExp_num]; omega

theorem baseExp_of_fst {f b : Expr} (h : (baseExp f).1 = b) : baseExp f = (b, (baseExp f).2) := by
  rw [← h]

/-- Each further factor merged in makes the power lighter than the factors were. -/
theorem M_expFold_le (b : Expr) (hb : bigBase b = true) : ∀ (x : Expr) (fs : List Expr),
    (∀ f ∈ fs, (baseExp f).1 = b) → M (.pow b (expFold x fs)) ≤ M (.pow b x) + ML fs
  | x, [], _ => by simp [expFold, measureList]
  | x, f :: fs, h => by
    have h1 := M_merged_lt (.pow b x) f b x (baseExp f).2 rfl (baseExp_of_fst (h f List.mem_cons_self)) hb
    have ih := M_expFold_le b hb (addExp x (baseExp f).2) fs (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [expFold, ML_cons]; omega

theorem mergePowers_lt (es l : List Expr) (t : Expr) (h : mergePowers es = some (l, t)) : ML l < ML es := by
  simp only [mergePowers, Option.map_eq_some_iff] at h
  obtain ⟨⟨b, e, fs, others⟩, hg, hl⟩ := h
  simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨hperm, he, hfs, hne, hbig⟩ := powerGroup_spec hg
  rw [measureList_perm simpW hperm]
  match fs, hne, hfs with
  | f :: fs', _, hfs =>
    have h1 := M_merged_lt e f b (baseExp e).2 (baseExp f).2 (baseExp_of_fst he)
      (baseExp_of_fst (hfs f List.mem_cons_self)) hbig
    have h2 := M_expFold_le b hbig (addExp (baseExp e).2 (baseExp f).2) fs' (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
    simp only [expFold, ML_cons, measureList_append] at *; omega

theorem collectPowersApply_decreasing : ∀ e r, collectPowersApply e = some r → measure simpW r.result < measure simpW e := by
    intro e r h
    cases e <;> simp only [collectPowersApply, reduceCtorEq] at h
    rename_i es
    split at h
    · rename_i l t hm
      simp only [Option.some.injEq] at h; subst h
      simp only [M_mul]; have := mergePowers_lt es l t hm; omega
    · simp at h

/-- `b^m · b^n = b^(m+n)` for every real `b`: a positive numeral base, or integer exponents of one
sign (at `b = 0`, `x·x⁻¹` would turn `0` into `1`). -/
def powSafe (b x y : Expr) : Bool :=
  isPosNum b || match intExp x, intExp y with
    | some m, some n => (decide (0 ≤ m) && decide (0 ≤ n)) || (decide (m ≤ 0) && decide (n ≤ 0))
    | _, _ => false

/-- For the merges `expFold` makes one factor at a time, `x` with the exponent of each factor of
`fs` in turn: whether every one holds at every real base (`powSafe`), and whether every one that
does not has integer exponents, so that it needs only `b ≠ 0`. -/
def foldSafety (b x : Expr) : List Expr → Bool × Bool
  | [] => (true, true)
  | f :: fs =>
    let y := (baseExp f).2
    let r := foldSafety b (addExp x y) fs
    (powSafe b x y && r.1, (powSafe b x y || ((intExp x).isSome && (intExp y).isSome)) && r.2)

/-- What a `simp.collect-powers` step assumes of its base, where it assumes anything: `(b, true)` for
`b ≠ 0` (each merge has integer exponents, or holds at every base), `(b, false)` for `b > 0`. -/
def collectAssumed : Expr → Option (Expr × Bool)
  | .mul es =>
    match powerGroup es with
    | some (b, e, fs, _) =>
      let s := foldSafety b (baseExp e).2 fs
      if s.1 then none else some (b, s.2)
    | none => none
  | _ => none

/-- `simp.collect-powers` where it holds for every real base. -/
def collectPowers : Rule simpW where
  name := "simp.collect-powers"
  apply e := if (collectAssumed e).isNone then collectPowersApply e else none
  decreasing e r h := collectPowersApply_decreasing e r (gate_some h)

/-- `simp.collect-powers` where it needs its base nonzero or positive: the step says which. -/
def collectAssumingApply (e : Expr) : Option RuleResult :=
  match collectAssumed e with
  | some (b, nz) => (collectPowersApply e).map fun r =>
      { r with explanation := r.explanation ++ (if nz then s!" Assuming ${b.toText} \\neq 0$." else s!" Assuming ${b.toText} > 0$.") }
  | none => none

theorem collectAssumingApply_some {e : Expr} {r : RuleResult} (h : collectAssumingApply e = some r) :
    ∃ b nz r₀, collectAssumed e = some (b, nz) ∧ collectPowersApply e = some r₀ ∧ r.result = r₀.result ∧
      r.error = r₀.error := by
  unfold collectAssumingApply at h
  split at h
  · rename_i b nz hb
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨r₀, h₀, rfl⟩ := h
    exact ⟨b, nz, r₀, hb, h₀, rfl, rfl⟩
  · cases h

def collectPowersAssuming : Rule simpW where
  name := "simp.collect-powers.assuming"
  apply := collectAssumingApply
  decreasing e r h := by
    obtain ⟨_, _, r₀, _, h₀, hres, _⟩ := collectAssumingApply_some h
    rw [hres]; exact collectPowersApply_decreasing e r₀ h₀

-- ---------------------------------------------------------------------------
-- simp.collect-like-terms
-- ---------------------------------------------------------------------------

/-- Is `e` a multiple of `t` (its rest, `coeffRest`, is `t`)? -/
def ofRest (t e : Expr) : Bool := equal (coeffRest e).2 t

/-- A big rest that two neighbouring terms share, the first such pair. Like terms are neighbours once
a sum is in canonical order (`leAdd` sorts by the rest before the coefficient), and both rewriters put
a node in that order before any rule sees it, so one pass finds them. As with `repeatedBase`, this is
only where to look: the theorems about the rule hold whatever rest it returns. -/
def likeRest : List Expr → Option Expr
  | e :: f :: rest =>
    if bigBase (coeffRest e).2 && equal (coeffRest f).2 (coeffRest e).2 then some (coeffRest e).2
    else likeRest (f :: rest)
  | _ => none

/-- The terms with a shared big rest `t`, two or more: `(t, e, fs, others)` with `e` the first of
them, `fs` the rest, and `others` the terms with another rest, all in their order. -/
def termGroup (es : List Expr) : Option (Expr × Expr × List Expr × List Expr) :=
  match likeRest es with
  | some t =>
    match es.filter (ofRest t) with
    | e :: f :: fs => if bigBase t then some (t, e, f :: fs, es.filter fun g => !ofRest t g) else none
    | _ => none
  | none => none

theorem termGroup_spec {es : List Expr} {t e : Expr} {fs others : List Expr}
    (h : termGroup es = some (t, e, fs, others)) :
    es.Perm (e :: (fs ++ others)) ∧ (coeffRest e).2 = t ∧ (∀ f ∈ fs, (coeffRest f).2 = t) ∧ fs ≠ [] ∧
      bigBase t = true := by
  unfold termGroup at h
  split at h
  · rename_i t' _
    split at h
    · rename_i e' f' fs' hfil
      split at h
      · rename_i hbig
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        have hmem : ∀ g ∈ e' :: f' :: fs', (coeffRest g).2 = t' := fun g hg => by
          rw [← hfil] at hg; exact equal_eq (List.mem_filter.mp hg).2
        refine ⟨?_, hmem e' List.mem_cons_self, fun g hg => hmem g (List.mem_cons_of_mem _ hg), by simp, hbig⟩
        have := List.filter_append_perm (ofRest t') es
        rw [hfil] at this
        exact this.symm
      · cases h
    · cases h
  · cases h

/-- `c` plus the coefficient of each term of `fs` in turn: the coefficient of the merged term. -/
def coeffFold (c : Q) : List Expr → Q
  | [] => c
  | f :: fs => coeffFold (c + (coeffRest f).1) fs

/-- Merge every term of the first shared big rest `t` into one: `a·t + b·t + … = (a+b+…)·t`. The
coefficients are added one term at a time (`coeffFold`), so the merge is the pair merge repeated,
and a sum of `n` like terms takes one step, not `n`. -/
def mergeTerms (es : List Expr) : Option (List Expr × Expr) :=
  (termGroup es).map fun (t, e, fs, others) => (.mul [.num (coeffFold (coeffRest e).1 fs), t] :: others, t)

def collectTermsApply : Expr → Option RuleResult
  | .add es =>
    match mergeTerms es with
    | some (es', t) => some ⟨.add es', s!"Like terms share the same variable part, here ${t.toLatex}$; add their coefficients (distributive law $ax + bx = (a+b)x$).", none, none⟩
    | none => none
  | _ => none

theorem coeffRest_cases (e : Expr) (c : Q) (t : Expr) (h : coeffRest e = (c, t)) :
    (e = .num c ∧ t = Expr.one) ∨ (∃ r, e = .mul (.num c :: r) ∧ t = mulN r) ∨ (e = t ∧ c = Q.one) := by
  cases e with
  | num q => simp [coeffRest] at h; simp [h]
  | mul es =>
    match es with
    | .num q :: r => simp [coeffRest] at h; exact Or.inr (Or.inl ⟨r, by simp [h]⟩)
    | [] => simp [coeffRest] at h; simp [h]
    | .var _ :: r | .add _ :: r | .mul _ :: r | .pow _ _ :: r | .fn _ _ :: r | .matrix _ :: r =>
      simp [coeffRest] at h; simp [h]
  | _ => simp [coeffRest] at h; simp [h]

/-- A term with rest `t` weighs at least `t` (a coefficient only adds). -/
theorem M_coeffRest_ge (e : Expr) (c : Q) (t : Expr) (h : coeffRest e = (c, t)) (hb : bigBase t = true) :
    M t ≤ M e ∧ (e ≠ t → 2 + M t ≤ M e) := by
  rcases coeffRest_cases e c t h with ⟨rfl, rfl⟩ | ⟨r, rfl, rfl⟩ | ⟨rfl, _⟩
  · simp [bigBase, Expr.one] at hb
  · have := M_mulN_le r
    refine ⟨?_, fun _ => ?_⟩ <;> rw [M_mul, ML_cons, M_num] <;> omega
  · exact ⟨Nat.le_refl _, fun h => absurd rfl h⟩

theorem M_mergedTerm_lt (e f : Expr) (c cf : Q) (t : Expr) (he : coeffRest e = (c, t)) (hf : coeffRest f = (cf, t))
    (hb : bigBase t = true) : M (.mul [.num (c + cf), t]) < M e + M f := by
  have hb8 := bigBase_measure hb
  have he' := M_coeffRest_ge e c t he hb
  have hf' := M_coeffRest_ge f cf t hf hb
  rw [M_mul, ML_cons, ML_cons, ML_nil, M_num]
  by_cases h1 : e = t <;> by_cases h2 : f = t
  · subst h1; subst h2; omega
  · subst h1; have := hf'.2 h2; omega
  · subst h2; have := he'.2 h1; omega
  · have := he'.2 h1; have := hf'.2 h2; omega

theorem coeffRest_of_snd {f t : Expr} (h : (coeffRest f).2 = t) : coeffRest f = ((coeffRest f).1, t) := by
  rw [← h]

/-- The merged term's own rest is `t`: merging another like term into it is the pair merge again. -/
theorem coeffRest_merged (c : Q) (t : Expr) : coeffRest (.mul [.num c, t]) = (c, t) := rfl

theorem M_coeffFold_le (t : Expr) (hb : bigBase t = true) : ∀ (c : Q) (fs : List Expr),
    (∀ f ∈ fs, (coeffRest f).2 = t) → M (.mul [.num (coeffFold c fs), t]) ≤ M (.mul [.num c, t]) + ML fs
  | c, [], _ => by simp [coeffFold, measureList]
  | c, f :: fs, h => by
    have h1 := M_mergedTerm_lt (.mul [.num c, t]) f c (coeffRest f).1 t (coeffRest_merged c t)
      (coeffRest_of_snd (h f List.mem_cons_self)) hb
    have ih := M_coeffFold_le t hb (c + (coeffRest f).1) fs (fun g hg => h g (List.mem_cons_of_mem _ hg))
    simp only [coeffFold, ML_cons]; omega

theorem mergeTerms_lt (es l : List Expr) (t : Expr) (h : mergeTerms es = some (l, t)) : ML l < ML es := by
  simp only [mergeTerms, Option.map_eq_some_iff] at h
  obtain ⟨⟨u, e, fs, others⟩, hg, hl⟩ := h
  simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
  obtain ⟨hperm, he, hfs, hne, hbig⟩ := termGroup_spec hg
  rw [measureList_perm simpW hperm]
  match fs, hne, hfs with
  | f :: fs', _, hfs =>
    have h1 := M_mergedTerm_lt e f (coeffRest e).1 (coeffRest f).1 u (coeffRest_of_snd he)
      (coeffRest_of_snd (hfs f List.mem_cons_self)) hbig
    have h2 := M_coeffFold_le u hbig ((coeffRest e).1 + (coeffRest f).1) fs' (fun g hg => hfs g (List.mem_cons_of_mem _ hg))
    simp only [coeffFold, ML_cons, measureList_append] at *; omega

def collectTerms : Rule simpW where
  name := "simp.collect-like-terms"
  apply := collectTermsApply
  decreasing e r h := by
    cases e <;> simp only [collectTermsApply, reduceCtorEq] at h
    rename_i es
    split at h
    · rename_i l t hm
      simp only [Option.some.injEq] at h; subst h
      simp only [M_add]; have := mergeTerms_lt es l t hm; omega
    · simp at h

-- ---------------------------------------------------------------------------
-- The rule set
-- ---------------------------------------------------------------------------

def simpRules : List (Rule simpW) :=
  [flatten, identity, foldConstants, functionRules, functionReal, functionAssuming, powerRules, collectPowers, collectPowersAssuming, collectTerms]

def simplify (e : Expr) : TraceM Expr := normalize simpRules e
def simplify0 (e : Expr) : Expr := (simplify e).run' #[]

/-- `simpRules` without the two rules that assume: sound at every real value (`normalizeSafe_sound`,
`proofs/Proofs/SimpAll.lean`). -/
def simpRulesSafe : List (Rule simpW) :=
  [flatten, identity, foldConstants, functionRules, functionReal, powerRules, collectPowers, collectTerms]

/-- What an `.assuming` step assumed, as TeX: the `$…$` after "Assuming". -/
def assumptionOf (explanation : String) : Option String :=
  match explanation.splitOn "Assuming $" with
  | _ :: rest :: _ => (rest.splitOn "$.").head?
  | _ => none

/-- Simplify, and say whether the result is the one the rules that assume nothing give (so it has the
input's value everywhere); otherwise list what the simplifier assumed. -/
def simplifyNoting (e : Expr) : Expr × Bool × List String :=
  let ((out : Expr), (steps : Array Step)) := (simplify e).run #[]
  let safe : Expr := (normalize simpRulesSafe e).run' #[]
  if safe == out then (safe, true, [])
  else (out, false, (steps.toList.filterMap fun (s : Step) => if s.rule.endsWith ".assuming" then assumptionOf s.explanation else none).eraseDups)

end MathEngine
