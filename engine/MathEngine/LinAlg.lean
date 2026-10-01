import MathEngine.Order
import MathEngine.Print
import MathEngine.SimpRules
import MathEngine.LinAlgQ
import MathEngine.LinAlgRref
/-!
# `la.*` — matrix arithmetic as rewriting, and Gauss–Jordan elimination as a step-recording algorithm

Ported from `linalg.ts`. Dimension errors refuse the evaluation (`RuleResult.error`), as the
reference throws. `la.context` is the catch-all that refuses a matrix literal in any position no rule
handles, which the M5 termination proof relies on.

`rref` has two paths. A matrix of numerals is reduced by the verified `LinQ.rref` (LinAlgQ.lean):
the row operations it emits are replayed here into steps; `LinQ.sol_rref` says the result has the
same solution set and `LinQ.rref_isRref` that it is in reduced row echelon form. A matrix with symbolic
entries goes through the older step-recording algorithm, whose arithmetic is the simplifier's and whose
pivot choice trusts `simplify` to decide zero-ness; its steps carry the `.symbolic` suffix so the
notebook reports them as unverified.
-/
namespace MathEngine
open Expr

def dims (rows : List (List Expr)) : Nat × Nat := (rows.length, (rows.head?.map List.length).getD 0)
def asMat : Expr → Option (List (List Expr)) | .matrix rows => some rows | _ => none
def refuse (msg : String) : RuleResult := ⟨Expr.zero, "", none, some msg⟩
def entry (rows : List (List Expr)) (i j : Nat) : Expr := ((rows.getD i []).getD j Expr.zero)

/-- Entry `(i, j)` of the product of two literal matrices. -/
def mulEntry (a b : List (List Expr)) (ac i j : Nat) : Expr :=
  .add ((List.range ac).map fun k => .mul [entry a i k, entry b k j])

def matMul (a b : List (List Expr)) : List (List Expr) :=
  let (ar, ac) := dims a
  let bc := (dims b).2
  (List.range ar).map fun i => (List.range bc).map fun j => mulEntry a b ac i j

/-- `rows ^ (k + 1)` as one literal (the product tree is left in the entries). -/
def matPow (rows : List (List Expr)) : Nat → List (List Expr)
  | 0 => rows
  | k + 1 => matMul rows (matPow rows k)

def minor (others : List (List Expr)) (j : Nat) : List (List Expr) :=
  others.map fun row => (row.zipIdx.filter (·.2 != j)).map (·.1)

/-- Determinant by Laplace expansion along the first row, fully expanded; `fuel` bounds the recursion
by the number of rows. -/
def detExpr : Nat → List (List Expr) → Expr
  | _, [[a]] => a
  | _, [[a, b], [c, d]] => Expr.sub (.mul [a, d]) (.mul [b, c])
  | fuel + 1, first :: others =>
    .add (first.zipIdx.map fun (a1j, j) =>
      let sign := if j % 2 == 0 then Expr.one else Expr.minusOne
      .mul [sign, a1j, detExpr fuel (minor others j)])
  | _, _ => Expr.zero

/-- The matrix rules. Every node with a matrix literal as a child is handled here: evaluated when it
is an operation on literals, refused otherwise (`la.context`). That is what lets the termination
proof (`PipelineOrder.lean`) know a normal form contains no literal except possibly at the root. -/
def laAdd : PlainRule :=
  { name := "la.add", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .add es =>
        if !es.any isMatrix then none else
        match es.mapM asMat with
        | some (a :: rest) =>
          let (r, c) := dims a
          if rest.any (fun m => dims m != (r, c)) then some (refuse "matrix addition: dimension mismatch")
          else some ⟨.matrix ((List.range r).map fun i => (List.range c).map fun j => .add (entry a i j :: rest.map (entry · i j))),
            "Matrices of the same shape add entrywise.", none, none⟩
        | _ => some (refuse "cannot add a matrix and a scalar")
      | _ => none }

def laScalarMul : PlainRule :=
  { name := "la.scalar-mul", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .mul es =>
        let mats := es.filter isMatrix
        let scalars := es.filter (fun a => !isMatrix a)
        match mats with
        | [.matrix rows] =>
          if scalars.isEmpty then none
          else
            let s := mulN scalars
            some ⟨.matrix (rows.map (·.map fun x => .mul [s, x])), s!"Scalar multiplication: multiply every entry by ${s.toText}$.", none, none⟩
        | _ => none
      | _ => none }

def laMul : PlainRule :=
  { name := "la.mul", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .mul es =>
        match es.zipIdx.filter (fun p => isMatrix p.1) with
        | (.matrix a, i) :: (.matrix b, j) :: _ =>
          let (ar, ac) := dims a
          let (br, bc) := dims b
          if ac != br then some (refuse s!"matrix product: {ar}×{ac} times {br}×{bc} is undefined (inner dimensions must match)")
          else
            let prod := matMul a b
            let es' := (es.zipIdx.filter (·.2 != j)).map fun (x, k) => if k == i then Expr.matrix prod else x
            some ⟨mulN es',
              s!"Matrix product: entry $(i,j)$ is the dot product of row $i$ of the left factor with column $j$ of the right factor ({ar}×{ac} · {br}×{bc} → {ar}×{bc}).", none, none⟩
        | _ => none
      | _ => none }

def laTranspose : PlainRule :=
  { name := "la.transpose", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "transpose" [.matrix rows] =>
        let (r, c) := dims rows
        some ⟨.matrix ((List.range c).map fun j => (List.range r).map fun i => entry rows i j), "Transpose swaps rows and columns.", none, none⟩
      | _ => none }

def laDet : PlainRule :=
  { name := "la.det", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "det" [.matrix rows] =>
        let (r, c) := dims rows
        if r != c || r == 0 then some (refuse "determinant of a non-square matrix is undefined")
        else match rows with
        | [[a]] => some ⟨a, "The determinant of a 1×1 matrix is its entry.", none, none⟩
        | [[a, b], [c2, d]] => some ⟨Expr.sub (.mul [a, d]) (.mul [b, c2]), "$\\det\\begin{bmatrix}a&b\\\\c&d\\end{bmatrix} = ad - bc$.", none, none⟩
        | _ => some ⟨detExpr r rows, "Laplace expansion along the first row, $\\det M = \\sum_j (-1)^{1+j} a_{1j} \\det M_{1j}$ where $M_{1j}$ deletes row 1 and column $j$, applied recursively down to 2×2 minors.", none, none⟩
      | _ => none }

def laPow : PlainRule :=
  { name := "la.pow", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .pow (.matrix rows) (.num n) =>
        let (r, c) := dims rows
        if r != c then some (refuse "only a square matrix can be raised to a power")
        else if n.isInt && n.val.num ≥ 1 then
          let k := n.val.num.toNat
          if k == 1 then some ⟨.matrix rows, "$M^1 = M$.", none, none⟩
          else some ⟨.matrix (matPow rows (k - 1)), s!"$M^\{{k}}$ is $M$ multiplied by itself {k} times; the entries are the accumulated dot products.", none, none⟩
        else some (refuse "a matrix can only be raised to a positive integer power")
      | _ => none }

/-- A row or column vector's entries. -/
def asVector : Expr → Option (List Expr)
  | .matrix [row] => some row
  | .matrix rows => if rows.all (·.length == 1) then some (rows.filterMap List.head?) else none
  | _ => none

/-- `dot(u, v) = Σ uᵢ·vᵢ`, bilinear as Mathematica's `Dot`: the Hermitian inner product of complex
vectors is `dot(u, conj(v))`. -/
def laDot : PlainRule :=
  { name := "la.dot", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "dot" [u, v] =>
        match asVector u, asVector v with
        | some us, some vs =>
          if us.length != vs.length then some (refuse s!"dot: the vectors have different lengths ({us.length} and {vs.length})")
          else if us.isEmpty then some (refuse "dot: empty vectors")
          else some ⟨.add ((us.zip vs).map fun (a, b) => .mul [a, b]), "$\\langle u, v\\rangle = \\sum_i u_i v_i$: multiply matching entries and add.", none, none⟩
        | _, _ => if (children e).any isMatrix then some (refuse "dot takes two vectors (one-row or one-column matrices)") else none
      | _ => none }

/-- `norm(v) = (Σ vᵢ²)^(1/2)`, the Euclidean length; for a complex vector use `norm` of the
entries' moduli, or `sqrt(dot(v, conj(v)))`. -/
def laNorm : PlainRule :=
  { name := "la.norm", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "norm" [v] =>
        match asVector v with
        | some vs =>
          if vs.isEmpty then some (refuse "norm: empty vector")
          else some ⟨.pow (.add (vs.map fun a => .pow a (.num (Q.ofInt 2)))) (.num (Q.ofInt 1 / Q.ofInt 2)), "$\\|v\\| = \\sqrt{\\sum_i v_i^2}$: the Pythagorean length.", none, none⟩
        | none => if (children e).any isMatrix then some (refuse "norm takes a vector (a one-row or one-column matrix)") else none
      | _ => none }

/-- `conj` of a matrix is entrywise. -/
def laConj : PlainRule :=
  { name := "la.conj", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "conj" [.matrix rows] =>
        some ⟨.matrix (rows.map fun r => r.map fun a => .fn "conj" [a]), "The conjugate of a matrix is taken entrywise.", none, none⟩
      | _ => none }

/-! ## Part: `m[[i, j]]`, Mathematica's indexing

Counting from 1, a negative index from the end (`-1` is the last), `All`, spans `a;;b;;s` (both
ends included, `s` a nonzero step) and lists `{i, j}`. A vector (one row or one column) takes one
index into its entries; a matrix takes rows, then columns. A single index drops that dimension (an
entry, or a row or column vector, which keeps its orientation); a span or list keeps it. -/

/-- The position (from 0) a single index names among `n`, or why it names none. -/
def partPos (n : Nat) (e : Expr) : Except String Nat :=
  match e with
  | .num q =>
    if !q.isInt then .error s!"a part index is a whole number, not {q.toText}"
    else
      let k := q.val.num
      if k == 0 then .error "parts count from 1 (and -1 is the last); there is no part 0"
      else if 0 < k && k ≤ n then .ok (k - 1).toNat
      else if k < 0 && -k ≤ n then .ok (n + k).toNat
      else .error s!"part {k} of {n}: the index runs from 1 to {n} (or -{n} to -1)"
  | _ => .error s!"a part index is a whole number, All, a span a;;b or a list {"{"}i, j{"}"}; ${e.toText}$ is not"

/-- The positions from `i` to `j` (both included) in steps of `st`: forwards for a positive step,
backwards for a negative one, none when `j` is on the wrong side of `i`. -/
def spanIndices (i j : Nat) (st : Int) : List Nat :=
  if 0 < st then (if i ≤ j then (List.range ((j - i) / st.toNat + 1)).map (i + · * st.toNat) else [])
  else (if j ≤ i then (List.range ((i - j) / (-st).toNat + 1)).map (i - · * (-st).toNat) else [])

/-- The positions a spec selects among `n`, and whether it was a single index (which drops the
dimension). -/
def partSpec (n : Nat) (e : Expr) : Except String (List Nat × Bool) :=
  match e with
  | .fn "All" [] => .ok (List.range n, false)
  | .fn "List" xs => do
    if xs.isEmpty then throw "an empty list of indices selects nothing"
    return (← xs.mapM (partPos n), false)
  | .fn "span" [a, b, .num s] => do
    let i ← partPos n a
    let j ← partPos n b
    if !s.isInt || s.isZero then throw s!"the step of a span is a nonzero whole number, not {s.toText}"
    let span := spanIndices i j s.val.num
    if span.isEmpty then throw s!"the span {a.toText};;{b.toText} selects nothing"
    return (span, false)
  | .fn "span" _ => .error "the step of a span is a nonzero whole number"
  | _ => do return ([← partPos n e], true)

theorem partPos_lt {n : Nat} {e : Expr} {i : Nat} (h : partPos n e = .ok i) : i < n := by
  unfold partPos at h
  split at h
  · rename_i q
    simp only at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i _ _ hk; simp only [Except.ok.injEq] at h; subst h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hk; omega
        · split at h
          · rename_i _ _ _ hk; simp only [Except.ok.injEq] at h; subst h
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hk; omega
          · simp at h
  · simp at h

theorem mapM_partPos_lt {n : Nat} : ∀ {xs : List Expr} {is : List Nat}, xs.mapM (partPos n) = .ok is → ∀ i ∈ is, i < n
  | [], is, h => by simp [List.mapM_nil, pure, Except.pure] at h; subst h; simp
  | x :: xs, is, h => by
    rw [List.mapM_cons] at h
    cases hx : partPos n x with
    | error _ => rw [hx] at h; simp [bind, Except.bind] at h
    | ok i =>
      cases hxs : xs.mapM (partPos n) with
      | error _ => rw [hx, hxs] at h; simp [bind, Except.bind] at h
      | ok js =>
        rw [hx, hxs] at h; simp [bind, Except.bind, pure, Except.pure] at h; subst h
        intro k hk; simp at hk
        rcases hk with rfl | hk
        · exact partPos_lt hx
        · exact mapM_partPos_lt hxs k hk

/-- A span between two positions in range stays in range: forwards it never passes `j`, backwards
it never passes `i`. -/
theorem spanIndices_lt {n i j : Nat} {st : Int} (hi : i < n) (hj : j < n) : ∀ x ∈ spanIndices i j st, x < n := by
  intro x hx
  unfold spanIndices at hx
  split at hx
  · split at hx
    · simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have h1 : k ≤ (j - i) / st.toNat := by omega
      have h2 := Nat.le_trans (Nat.mul_le_mul_right st.toNat h1) (Nat.div_mul_le_self (j - i) st.toNat)
      omega
    · simp at hx
  · split at hx
    · simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨k, -, rfl⟩ := hx
      omega
    · simp at hx

/-- **Part stays in range**: every position a spec selects among `n` is below `n`, so the
selection is exactly the entries Mathematica's Part names. -/
theorem partSpec_lt {n : Nat} {e : Expr} {is : List Nat} {b : Bool} (h : partSpec n e = .ok (is, b)) :
    ∀ i ∈ is, i < n := by
  unfold partSpec at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; intro i hi; simpa using hi
  · rename_i xs
    simp only [bind, Except.bind] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · cases hm : xs.mapM (partPos n) with
      | error _ => rw [hm] at h; simp at h
      | ok js => rw [hm] at h; simp [pure, Except.pure] at h; obtain ⟨rfl, -⟩ := h; exact mapM_partPos_lt hm
  · rename_i a b s
    cases ha : partPos n a with
    | error _ => simp [ha, bind, Except.bind] at h
    | ok i =>
      cases hb : partPos n b with
      | error _ => simp [ha, hb, bind, Except.bind] at h
      | ok j =>
        simp only [ha, hb, bind, Except.bind] at h
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact spanIndices_lt (partPos_lt ha) (partPos_lt hb)
  · simp at h
  · cases hp : partPos n e with
    | error _ => simp [hp, bind, Except.bind] at h
    | ok i => simp [hp, bind, Except.bind, pure, Except.pure] at h; obtain ⟨rfl, -⟩ := h; simpa using partPos_lt hp
/-- `rows[[specs]]`: the selected entries, and what was selected, for the step's explanation. -/
def partOf (rows : List (List Expr)) (specs : List Expr) : Except String (Expr × String) := do
  let (r, c) := dims rows
  if r == 0 || c == 0 then throw "part of an empty matrix"
  match specs with
  | [s] =>
    if r == 1 || c == 1 then
      -- a vector: one index into its entries, keeping its orientation
      let vs := if r == 1 then rows.head! else rows.map (·.head!)
      let (is, single) ← partSpec vs.length s
      let picked := is.map (vs.getD · Expr.zero)
      if single then return (picked.head!, s!"Entry {is.head! + 1} of the vector, counting from 1.")
      let out := if r == 1 then Expr.matrix [picked] else Expr.matrix (picked.map ([·]))
      return (out, s!"Entries {", ".intercalate (is.map (toString ∘ (· + 1)))} of the vector.")
    else
      let (is, single) ← partSpec r s
      let picked := is.map (rows.getD · [])
      if single then return (.matrix picked, s!"Row {is.head! + 1} of the {r}×{c} matrix, as a row vector.")
      return (.matrix picked, s!"Rows {", ".intercalate (is.map (toString ∘ (· + 1)))} of the {r}×{c} matrix.")
  | [s, t] =>
    let (is, si) ← partSpec r s
    let (js, sj) ← partSpec c t
    let pick := is.map fun i => js.map fun j => entry rows i j
    let what := s!"rows {", ".intercalate (is.map (toString ∘ (· + 1)))}, columns {", ".intercalate (js.map (toString ∘ (· + 1)))} of the {r}×{c} matrix"
    if si && sj then return (entry rows is.head! js.head!, s!"Entry ({is.head! + 1}, {js.head! + 1}) of the {r}×{c} matrix.")
    -- a single column keeps its orientation: a column vector
    if sj then return (.matrix (pick.map fun row => [row.head!]), s!"The selection: {what}, as a column vector.")
    if si then return (.matrix [pick.head!], s!"The selection: {what}, as a row vector.")
    return (.matrix pick, s!"The selection: {what}.")
  | [] => throw "a part needs an index: m[[i]]"
  | _ => throw s!"a matrix has two dimensions; {specs.length} indices were given"

def laPart : PlainRule :=
  { name := "la.part", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn "part" (.matrix rows :: specs) =>
        some (match partOf rows specs with
          | .ok (r, text) => ⟨r, text, none, none⟩
          | .error msg => refuse msg)
      | _ => none }

/-! ## Statistics of a vector, or of each column of a matrix

Mathematica's conventions: a statistic of a matrix is the row of its columns' statistics, and the
variance divides by `n − 1` (the sample variance, as `Variance` and Python's `statistics.variance`).
`total`, `mean`, `variance` and `stdev` are definitions, so symbolic entries work: `mean([a; b])`
is `(a + b)/2`. The variance is written in the one-pass form `(Σxᵢ² − (Σxᵢ)²/n)/(n − 1)`, linear in
`n` where the definition `Σ(xᵢ − x̄)²/(n − 1)` repeats the mean in every term; `variance_soundR`
(proofs/Proofs/Stats.lean) proves the two equal over ℝ. `min`, `max` and `median` compare, so they
take numerals only. -/

/-- The entries of a vector, or each column of a matrix (and whether it was a matrix). -/
def statColumns (rows : List (List Expr)) : List (List Expr) × Bool :=
  let (r, c) := dims rows
  if r == 1 then ([rows.head!], false)
  else if c == 1 then ([rows.map (·.head!)], false)
  else ((List.range c).map (fun j => rows.map (·.getD j Expr.zero)), true)

/-- The numerals of a list, if every entry is one. -/
def numerals (xs : List Expr) : Option (List Q) := xs.mapM fun | .num q => some q | _ => none

def totalOf (xs : List Expr) : Expr := addN xs
def meanOf (xs : List Expr) : Expr := .mul [.num (Q.ofRat (1 / (xs.length : Rat))), addN xs]
/-- The sample variance, one-pass: `(Σxᵢ² − (Σxᵢ)²/n)/(n − 1)`. -/
def varianceOf (xs : List Expr) : Expr :=
  let n : Rat := xs.length
  .mul [.num (Q.ofRat (1 / (n - 1))),
    .add [addN (xs.map fun x => .pow x (.num 2)), .mul [.num (Q.ofRat (-1 / n)), .pow (addN xs) (.num 2)]]]
def stdevOf (xs : List Expr) : Expr := .pow (varianceOf xs) (.num (Q.ofRat (1 / 2)))

/-- The least numeral (the first, among equals). -/
def minQ : List Q → Option Q
  | [] => none
  | q :: qs => some (qs.foldl (fun m x => if x.val < m.val then x else m) q)
def maxQ : List Q → Option Q
  | [] => none
  | q :: qs => some (qs.foldl (fun m x => if m.val < x.val then x else m) q)
/-- The middle of the sorted numerals, or the mean of the two middles. -/
def medianQ (qs : List Q) : Option Q :=
  let s := qs.mergeSort fun a b => a.val ≤ b.val
  let n := s.length
  if n == 0 then none
  else if n % 2 == 1 then s[n / 2]?
  else do let a ← s[n / 2 - 1]?; let b ← s[n / 2]?; return (a + b) / Q.ofInt 2

/-- One statistic: its name, how it is computed from a column, and the explanation of the step. -/
structure Stat where
  fn : String
  of : List Expr → Except String Expr
  text : String

def stats : List Stat := [
  ⟨"total", fun xs => .ok (totalOf xs), "$\\sum_i x_i$: the entries added."⟩,
  ⟨"mean", fun xs => .ok (meanOf xs), "$\\bar x = \\frac{1}{n}\\sum_i x_i$: the total over the count."⟩,
  ⟨"variance", fun xs => if xs.length < 2 then .error "variance needs at least two values (it divides by n − 1)" else .ok (varianceOf xs),
    "The sample variance $\\frac{1}{n-1}\\sum_i (x_i - \\bar x)^2$, written $\\frac{1}{n-1}\\left(\\sum_i x_i^2 - \\frac{1}{n}\\left(\\sum_i x_i\\right)^2\\right)$ (the same number: `variance_soundR`)."⟩,
  ⟨"stdev", fun xs => if xs.length < 2 then .error "stdev needs at least two values (it divides by n − 1)" else .ok (stdevOf xs),
    "The sample standard deviation, $\\sqrt{\\frac{1}{n-1}\\sum_i (x_i - \\bar x)^2}$, written in the one-pass form of the variance."⟩,
  ⟨"min", fun xs => match numerals xs >>= minQ with | some q => .ok (.num q) | none => .error "min compares numbers; an entry is not a number", "The least entry."⟩,
  ⟨"max", fun xs => match numerals xs >>= maxQ with | some q => .ok (.num q) | none => .error "max compares numbers; an entry is not a number", "The greatest entry."⟩,
  ⟨"median", fun xs => match numerals xs >>= medianQ with | some q => .ok (.num q) | none => .error "median sorts numbers; an entry is not a number",
    "The middle entry once sorted, or the mean of the two middle ones."⟩]

def statNames : List String := stats.map (·.fn)

/-- The statistics as one rule per name (`stat.mean`, …): the statistic of a vector, or the row of a
matrix's column statistics. -/
def statRule (st : Stat) : PlainRule :=
  { name := s!"stat.{st.fn}", apply := fun e => Option.map (checkedLit e) <|
      match e with
      | .fn f [.matrix rows] =>
        if f != st.fn then none
        else
          let (r, c) := dims rows
          if r == 0 || c == 0 then some (refuse s!"{st.fn} of an empty matrix")
          else
            let (cols, isMat) := statColumns rows
            match cols.mapM st.of with
            | .error msg => some (refuse msg)
            | .ok vs =>
              if isMat then some ⟨.matrix [vs], s!"Column by column: {st.text}", none, none⟩
              else some ⟨vs.head!, st.text, none, none⟩
      | .fn f args => if f == st.fn && args.any isMatrix then some (refuse s!"{st.fn} takes one vector or matrix") else none
      | _ => none }

def statRules : List PlainRule := stats.map statRule

def matrixRules : List PlainRule := [laAdd, laScalarMul, laMul, laTranspose, laDet, laPow, laDot, laNorm, laConj, laPart] ++ statRules

/-- The catch-all: a matrix literal anywhere no rule above handles it is an error, not junk. -/
def laContext : PlainRule :=
  { name := "la.context", apply := fun e =>
      match e with
      | .matrix rows => if rows.flatten.any isMatrix then some (refuse "nested matrices are not supported") else none
      | _ => if (children e).any isMatrix then some (refuse s!"a matrix cannot be used here: ${e.toText}$") else none }

def contextRules : List PlainRule := [laContext]

/-- Gauss–Jordan elimination on symbolic entries, recorded as row-operation steps whose before/after
are the whole matrix. Works as long as `simplify` can decide zero-ness of pivots — unverified. -/
def rrefSymbolic (m : List (List Expr)) : Expr × Array Step := Id.run do
  let (nr, nc) := dims m
  let mut rows := m
  let mut steps : Array Step := #[]
  let mut pivotRow := 0
  let snap (rs : List (List Expr)) : Expr := .matrix rs
  for col in [0:nc] do
    if pivotRow ≥ nr then break
    let p? := (List.range nr).find? fun i => i ≥ pivotRow && !(simplify0 (entry rows i col)).isZero
    match p? with
    | none => pure ()
    | some p =>
      if p != pivotRow then
        let before := snap rows
        let rp := rows.getD p []
        let rq := rows.getD pivotRow []
        rows := (rows.set p rq).set pivotRow rp
        steps := steps.push ⟨"la.row-swap.symbolic", s!"Swap $R_\{{p + 1}}$ and $R_\{{pivotRow + 1}}$ so the pivot for column {col + 1} is nonzero (assuming the symbolic entry is not zero).", [], before, snap rows, none⟩
      let pivot := entry rows pivotRow col
      if !pivot.isOne then
        let before := snap rows
        rows := rows.set pivotRow ((rows.getD pivotRow []).map fun x => simplify0 (Expr.div x pivot))
        steps := steps.push ⟨"la.row-scale.symbolic", s!"Scale $R_\{{pivotRow + 1}}$ by $1/({pivot.toText})$ so the pivot becomes 1 (assuming {pivot.toText} ≠ 0).", [], before, snap rows, none⟩
      for i in [0:nr] do
        if i != pivotRow then
          let factor := simplify0 (entry rows i col)
          if !factor.isZero then
            let before := snap rows
            let prow := rows.getD pivotRow []
            rows := rows.set i (((rows.getD i []).zip prow).map fun (x, y) => simplify0 (Expr.sub x (.mul [factor, y])))
            steps := steps.push ⟨"la.row-add.symbolic", s!"$R_\{{i + 1}} \\leftarrow R_\{{i + 1}} - ({factor.toText}) R_\{{pivotRow + 1}}$ to clear column {col + 1}.", [], before, snap rows, none⟩
      pivotRow := pivotRow + 1
  return (snap rows, steps)

/-- The rows as rationals, if every entry is a numeral; the flag says whether any was approximate. -/
def asRatRows (rows : List (List Expr)) : Option (List (List Rat) × Bool) := do
  let rs ← rows.mapM fun r => r.mapM fun | .num q => some q | _ => none
  return (rs.map (·.map (·.val)), rs.any (·.any (·.approx)))

/-- Gauss–Jordan elimination over ℚ: the operations of the verified `LinQ.rref`, replayed into
steps. `LinQ.sol_rref` is the theorem that the output has the input's solution set. -/
def rrefRat (rs : List (List Rat)) (approx : Bool) : Except String (Expr × Array Step) := Id.run do
  let lit (r : Rat) : Expr := .num (Q.ofRat r approx)
  let snap (m : List (List Rat)) : Expr := .matrix (m.map (·.map lit))
  let mut m := rs
  let mut steps : Array Step := #[]
  for (col, op) in LinQ.rrefOps rs do
    let before := snap m
    m := op.apply m
    let (rule, text) := match op with
      | .swap i j => ("la.row-swap", s!"Swap $R_\{{i + 1}}$ and $R_\{{j + 1}}$ so the pivot for column {col + 1} is nonzero. (Elementary row operations preserve the solution set: `LinQ.sol_swap`.)")
      | .scale i c => ("la.row-scale", s!"Scale $R_\{{i + 1}}$ by ${(lit c).toText}$ so the pivot becomes 1. (`LinQ.sol_scale`: the factor is nonzero.)")
      | .addMul i j c => ("la.row-add", s!"$R_\{{i + 1}} \\leftarrow R_\{{i + 1}} - ({(lit (-c)).toText}) R_\{{j + 1}}$ to clear column {col + 1}. (`LinQ.sol_addMul`.)")
    steps := steps.push ⟨rule, text, [], before, snap m, none⟩
  return .ok (snap m, steps)

/-- `rref`: the verified ℚ path when every entry is a numeral, the symbolic path otherwise. -/
def rref (m : List (List Expr)) : Except String (Expr × Array Step) :=
  match asRatRows m with
  | some (rs, approx) => rrefRat rs approx
  | none => .ok (rrefSymbolic m)

end MathEngine
