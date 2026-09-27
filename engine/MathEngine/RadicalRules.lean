import MathEngine.SimpRules
import MathEngine.Order
/-!
# `simp.radical` — radicals of integers, as far as the ordering allows

Mathematica writes `√8` as `2√2`. As a *term* that is `2 · 2^(1/2)`, and no retuning of the
ordering can make `8^(1/2) → 2 · 2^(1/2)` decrease: the result contains the input's radical and
more, so the input's numeral would have to outweigh a product node, and numeral weights must stay
bounded for `simp.fold-constants` to decrease on arbitrary sums (`1 + 7 → 8`). What the ordering
does allow, with the sixth tier (`numCount`, Order.lean), is the single-power form: a perfect-power
base is reduced, `8^(1/2) → 2^(3/2)`, at equal `M` and `size`. Two more rules then behave like
Mathematica where it matters: radicals with the same square-free part collect in a sum
(`√50 − √18 → 2√2`, which *does* decrease `M`, since a sum of two radicals outweighs one product),
and same-index radicals in a product multiply (`12^(1/2) · 3^(1/2) → 36^(1/2) → 6`). The printer
shows `2^(3/2)` as `2√2` and `12^(1/2)` as `2√3`.

Each rule guards itself with the decidable decrease its proof needs, so the ordering lemmas in
`PipelineOrder.lean` are a split on the guard. The guards never fail in practice; they are honest
boundaries, not fuel.

`√a` itself becomes `a^(1/2)` in the pipeline here rather than in `simp.function`, so that the step
can say what the reader sees. Usually that is nothing — `√x`, `√2` and `√8` print as they are — and
the step is silent (`simp.sqrt`). For `√18` the printer shows `18^(1/2)` as `3√2`, so the step is a
visible `simp.radical` that shows the square factor coming out. Either way a row shows a change and
says why: `√8 → 2√2` is `simp.radical`'s perfect-power step, with the work written out.
-/
namespace MathEngine
open Expr

/-- The largest `k ≥ 2` with `r ^ k = a`, if `a ≥ 2` is a perfect power. -/
def perfectPower (a : Nat) : Option (Nat × Nat) :=
  (List.range (Nat.log2 a + 1)).reverse.findSome? fun k =>
    if k ≥ 2 then (natRoot k a).map fun r => (r, k) else none

/-- `k · b^x` with `b` an integer ≥ 2 and `x` not an integer: `(k, b, x)`; `k = 1` when absent. -/
def radicalTerm : Expr → Option (Q × Q × Q)
  | .pow (.num b) (.num x) => if b.isInt && b.val.num ≥ 2 && !x.isInt then some (Q.one, b, x) else none
  | .mul [.num k, .pow (.num b) (.num x)] =>
    if b.isInt && b.val.num ≥ 2 && !x.isInt then some (k, b, x) else none
  | _ => none

/-- `b = m^q · s` with `m` the largest such: the `q`-th-power part of a positive integer. -/
def qthPowerPart (b q : Nat) : Nat × Nat :=
  let hi := 2 ^ (Nat.log2 b / q + 1)
  let m := ((List.range (hi + 1)).reverse.find? fun m => m ≥ 1 && b % (m ^ q) == 0).getD 1
  (m, b / (m ^ q))

/-- Two radicals with the same index and the same square-free part (`√50` and `√18` are `5√2` and
`3√2`) whose exponents agree modulo 1: one radical with a numeral coefficient.
`b^(p/q) = m^p · s^i · s^(f/q)` for `b = m^q s` and `p = i q + f`. -/
def mergeRadicals (s t : Expr) : Option Expr :=
  match radicalTerm s, radicalTerm t with
  | some (k₁, b₁, x₁), some (k₂, b₂, x₂) =>
    let q := x₁.val.den
    let ms₁ := qthPowerPart b₁.val.num.toNat q
    let ms₂ := qthPowerPart b₂.val.num.toNat q
    if x₂.val.den == q && ms₁.2 == ms₂.2 && x₁.val.num % q == x₂.val.num % q then
      let f := x₁.val.num % q
      let sq : Q := Q.ofInt ms₁.2
      let c := k₁ * (Q.ofInt ms₁.1).zpow x₁.val.num * sq.zpow (x₁.val.num / q)
             + k₂ * (Q.ofInt ms₂.1).zpow x₂.val.num * sq.zpow (x₂.val.num / q)
      let rad : Expr := .pow (.num sq) (.num (Q.ofRat (mkRat f q)))
      some (if ms₁.2 == 1 then .num c else if c.isZero then Expr.zero else if c.isOne then rad else .mul [.num c, rad])
    else none
  | _, _ => none

/-- `a^(p/q) · b^(r/q) = (a^p · b^r)^(1/q)` for integer bases ≥ 2. -/
def mulRadicalPair (s t : Expr) : Option Expr :=
  match s, t with
  | .pow (.num a) (.num x), .pow (.num b) (.num y) =>
    if a.isInt && a.val.num ≥ 2 && b.isInt && b.val.num ≥ 2 && !x.isInt && !y.isInt && x.val.den == y.val.den then
      some (.pow (.num (a.zpow x.val.num * b.zpow y.val.num)) (.num (Q.ofRat (mkRat 1 x.val.den))))
    else none
  | _, _ => none

/-! ## Finding a pair in a list, with the permutation the proofs need -/

/-- The first element `b` with `g b = some m`, and the list without it. -/
def findWith (g : Expr → Option Expr) : List Expr → Option (Expr × Expr × List Expr)
  | [] => none
  | b :: rest =>
    match g b with
    | some m => some (m, b, rest)
    | none => (findWith g rest).map fun r => (r.1, r.2.1, b :: r.2.2)

theorem findWith_perm (g : Expr → Option Expr) : ∀ (l : List Expr) {m b l'},
    findWith g l = some (m, b, l') → g b = some m ∧ l.Perm (b :: l')
  | [], _, _, _, h => by simp [findWith] at h
  | x :: xs, m, b, l', h => by
    simp only [findWith] at h
    split at h
    · rename_i m' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hm, List.Perm.refl _⟩
    · cases hr : findWith g xs with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨m', b', l''⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hg, hperm⟩ := findWith_perm g xs hr
        exact ⟨hg, (hperm.cons x).trans (List.Perm.swap b' x l'')⟩

/-- A pair `a, b` with `f a b = some m`, `b` searched among all other elements. -/
def findPairGo (f : Expr → Expr → Option Expr) (acc : List Expr) : List Expr → Option (Expr × List Expr)
  | [] => none
  | a :: rest =>
    match findWith (f a) (acc ++ rest) with
    | some (m, _, others) => some (m, others)
    | none => findPairGo f (acc ++ [a]) rest

def findPair (f : Expr → Expr → Option Expr) (es : List Expr) : Option (Expr × List Expr) := findPairGo f [] es

theorem findPairGo_perm (f : Expr → Expr → Option Expr) : ∀ (l acc : List Expr) {m others},
    findPairGo f acc l = some (m, others) → ∃ a b, f a b = some m ∧ (acc ++ l).Perm (a :: b :: others)
  | [], _, _, _, h => by simp [findPairGo] at h
  | a :: rest, acc, m, others, h => by
    simp only [findPairGo] at h
    split at h
    · rename_i m' b os hf
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hg, hperm⟩ := findWith_perm _ _ hf
      exact ⟨a, b, hg, List.perm_middle.trans (hperm.cons a)⟩
    · obtain ⟨a', b, hg, hperm⟩ := findPairGo_perm f rest (acc ++ [a]) h
      exact ⟨a', b, hg, by simpa [List.append_assoc] using hperm⟩

theorem findPair_perm (f : Expr → Expr → Option Expr) (es : List Expr) {m others}
    (h : findPair f es = some (m, others)) : ∃ a b, f a b = some m ∧ es.Perm (a :: b :: others) := by
  simpa using findPairGo_perm f es [] h

/-! ## The rules -/

/-- The equalities of a chain, each written once: `√32 = (2^5)^(1/2) = …`. -/
private def chain (xs : List String) : String :=
  " = ".intercalate (xs.foldl (fun acc x => if acc.getLast? == some x then acc else acc ++ [x]) [])

/-- The work behind `a^q = r^(k·q)` for `a = r^k`, ending in the notation the row shows:
`32 = 2^5`, so `√32 = (2^5)^(1/2) = 2^(5/2) = 2^2 · 2^(1/2) = 4√2`. -/
def radicalBaseWhy (a q : Q) (r k : Nat) : String :=
  let x := q * Q.ofInt k
  let rk := s!"{r}^\{{k}}"
  let n := x.val.num.toNat
  let d := x.val.den
  -- a whole power comes out of the root: `2^(5/2) = 2^2 · 2^(1/2)`
  let split :=
    if !x.isNeg && !x.isInt && n ≥ d then
      let whole := if n / d == 1 then toString r else s!"{r}^\{{n / d}}"
      [s!"{whole} \\cdot {r}^\{{n % d}/{d}}"]
    else []
  let steps := [(Expr.pow (.num a) (.num q)).toLatex, s!"({rk})^\{{q.toText}}", s!"{r}^\{{x.toText}}"] ++ split ++
    [(Expr.pow (.num (Q.ofInt r)) (.num x)).toLatex]
  s!"${a.toText} = {rk}$, so ${chain steps}$."

/-- `a^(p/q)` with `a = r^k` a perfect power: `r^(k·p/q)`. Guarded by the ordering it decreases. -/
def radicalBase : PlainRule :=
  { name := "simp.radical", apply := fun e =>
      match e with
      | .pow (.num a) (.num q) =>
        if a.isInt && a.val.num ≥ 2 && !q.isInt then
          match perfectPower a.val.num.toNat with
          | some (r, k) =>
            let res : Expr := .pow (.num (Q.ofInt r)) (.num (q * Q.ofInt k))
            if M res ≤ M e && numCount res < numCount e then
              some ⟨res, radicalBaseWhy a q r k, none, none⟩
            else none
          | none => none
        else none
      | _ => none }

/-- `(m, s)` with `n = m²·s` and `m ≥ 2`, for an integer numeral `n ≥ 2` that is not a perfect
power: exactly when the printer shows `n^(1/2)` as `m√s` rather than `√n` (`18^(1/2)` is `3√2`,
`8^(1/2)` stays `√8` for `simp.radical` to reduce, `2^(1/2)` is `√2`). -/
def sqrtSquarePart : Expr → Option (Nat × Nat)
  | .num a =>
    if a.isInt && a.val.num ≥ 2 && (perfectPower a.val.num.toNat).isNone then
      let ms := qthPowerPart a.val.num.toNat 2
      if ms.1 ≥ 2 then some ms else none
    else none
  | _ => none

/-- `18 = 3^2 · 2`, so `√18 = √(3^2) · √2 = 3√2`. -/
def sqrtWhy (a : Expr) (m s : Nat) : String :=
  let apart := s!"\\sqrt\{{m}^\{2}} \\cdot \\sqrt\{{s}}"
  let steps := [(Expr.fn "sqrt" [a]).toLatex, apart, (Expr.pow a (.num (Q.ofRat (mkRat 1 2)))).toLatex]
  s!"${a.toLatex} = {m}^\{2} \\cdot {s}$, so ${chain steps}$."

/-- `√a = a^(1/2)` wherever the printer shows the two alike (`√x`, `√2`, `√8`): a change of
representation only, so it leaves no step. The one exception is `sqrtRadical`'s. -/
def sqrtPower : PlainRule :=
  { name := "simp.sqrt", silent := true, apply := fun e =>
      match e with
      | .fn "sqrt" [a] =>
        if (sqrtSquarePart a).isSome then none
        else some ⟨.pow a (.num (Q.ofRat (mkRat 1 2))), "$\\sqrt{a} = a^{1/2}$; we work with a single power form internally.", none, none⟩
      | _ => none }

/-- `√n = n^(1/2)` where the printer shows `n^(1/2)` with its square factor outside (`√18` as
`3√2`): the step is visible, so it shows the factor coming out. -/
def sqrtRadical : PlainRule :=
  { name := "simp.radical", apply := fun e =>
      match e with
      | .fn "sqrt" [a] =>
        match sqrtSquarePart a with
        | some (m, s) => some ⟨.pow a (.num (Q.ofRat (mkRat 1 2))), sqrtWhy a m s, none, none⟩
        | none => none
      | _ => none }

/-- The first pair `findPair` would pick: the first element with a partner, and its first partner. -/
private def firstPair (f : Expr → Expr → Option Expr) (es : List Expr) : Option (Expr × Expr × Expr) :=
  let ix := es.zipIdx
  ix.findSome? fun (a, i) => ix.findSome? fun (b, j) => if i == j then none else (f a b).map fun m => (a, b, m)

/-- A radical term as the printer shows it: its displayed coefficient and radical (`2^(3/2)` is
`(2, √2)`, `-18^(1/2)` is `(-3, √2)`). -/
private def shownRadical (t : Expr) : Option (Q × String) :=
  (radicalTerm t).bind fun (k, b, x) => (radicalParts b x).map fun (c, rad) => (k * Q.ofInt c, rad)

/-- `2√2 + 4√2 = (2 + 4)√2 = 6√2`, for the pair `collectRadicals` merges. -/
def collectWhy (es : List Expr) : String :=
  let generic := "$k_1 b^{p_1/q} + k_2 b^{p_2/q} = (k_1 b^{i_1} + k_2 b^{i_2})\\, b^{f/q}$: radicals with the same base and index collect."
  match firstPair mergeRadicals es with
  | some (s, t, m) =>
    match shownRadical s, shownRadical t with
    | some (c₁, r₁), some (c₂, r₂) =>
      if r₁ != r₂ || r₁.isEmpty then generic else
      let term (c : Q) := if c.isOne then r₁ else if c.eq Q.minusOne then s!"-{r₁}" else s!"{c.toLatex}{r₁}"
      let op := if c₂.isNeg then "-" else "+"
      s!"${term c₁} {op} {term c₂.abs} = ({c₁.toLatex} {op} {c₂.abs.toLatex}){r₁} = {m.toLatex}$: radicals with the same base and index collect."
    | _, _ => generic
  | none => generic

/-- `√2 · √6 = √12 = 2√3`, for the pair `mulRadicals` multiplies. -/
def mulWhy (es : List Expr) : String :=
  let generic := "$a^{p/q} \\cdot b^{r/q} = (a^p b^r)^{1/q}$: radicals with the same index multiply under one root."
  match firstPair mulRadicalPair es with
  | some (s, t, m@(.pow (.num n) (.num x))) =>
    let root := if x.val.den == 2 then s!"\\sqrt\{{n.toLatex}}" else s!"\\sqrt[{x.val.den}]\{{n.toLatex}}"
    s!"${chain [s!"{s.toLatex} \\cdot {t.toLatex}", root, m.toLatex]}$: radicals with the same index multiply under one root."
  | _ => generic

/-- Same-base radicals in a sum collect into one, with a numeral coefficient. -/
def collectRadicals : PlainRule :=
  { name := "simp.collect-radicals", apply := fun e =>
      match e with
      | .add es =>
        match findPair mergeRadicals es with
        | some (m, others) =>
          let res := addN (m :: others)
          if M res < M e then
            some ⟨res, collectWhy es, none, none⟩
          else none
        | none => none
      | _ => none }

/-- Same-index radicals in a product multiply under one root. -/
def mulRadicals : PlainRule :=
  { name := "simp.radical", apply := fun e =>
      match e with
      | .mul es =>
        match findPair mulRadicalPair es with
        | some (m, others) =>
          let res := mulN (m :: others)
          if M res < M e then
            some ⟨res, mulWhy es, none, none⟩
          else none
        | none => none
      | _ => none }

def radicalRules : List PlainRule := [radicalBase, collectRadicals, mulRadicals]

/-- Ahead of `simp.function` in the pipeline, which would otherwise take `√a` first. The verified
`simplify` (`simpRules` alone) keeps `simp.function`'s own `√a = a^(1/2)`. -/
def sqrtRules : List PlainRule := [sqrtPower, sqrtRadical]

end MathEngine
