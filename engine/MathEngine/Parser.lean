import MathEngine.Expr
/-!
# Parser

Input language, identical to `parser.ts`:

```
stmt   := 'let' IDENT '=' expr | expr
expr   := term (('+' | '-') term)*
term   := unary (('*' | '/' | './' | '.*') unary | <implicit> unary)*
unary  := '-' unary | power
power  := part ('^' unary)?                       -- right-assoc; -x^2 parses as -(x^2)
part   := atom ('[[' spec (',' spec)* ']]')*        -- Mathematica's Part: m[[2]], m[[All, 1;;3]]
spec   := 'All' | '{' expr,* '}' | expr? ';;' expr? (';;' expr)? | expr
atom   := NUMBER | IDENT | IDENT '(' expr,* ')' | '(' expr ')' | '[' row (';' row)* ']'
row    := expr (',' expr)*
```

`m[[s, t]]` is `part(m, s, t)`; a span `a;;b;;c` is `span(a, b, c)` with an omitted end read as
Mathematica does (`;;b` from 1, `a;;` to the last, `-1`); `All` is `All()`, a list `{i, j}` is
`List(i, j)`. `[[` after a term cannot be anything else: a nested matrix literal is refused.

`a ./ b` and `a .* b` are MATLAB's entrywise division and product, `ediv(a, b)` and `emul(a, b)`
(`la.ediv`, `la.emul`); `/` and `*` stay the matrix inverse and product.

A unary builtin may carry its power before its argument, `sin^2(x)` for `sin(x)^2` and
`sin^-1(x)` for `sin(x)^-1` (the reciprocal, not `arcsin`). `sec(u)`, `csc(u)` and `cot(u)` are read
as `cos(u)^-1`, `sin(u)^-1` and `tan(u)^-1`.

Implicit multiplication (`2x`, `2(x+1)`, `x y`) is allowed when the previous token ends an atom
and the next begins one, except number-after-number (`3 4` is an error). `IDENT (` is a call
only if IDENT is a builtin or a session-known function.

Cells in the other worlds never reach this parser: a transition system or a question about one
(`Sys.isSystemSource`, grammar in `Systems.lean`), an order-theory or relation command
(`Ord.isOrderSource`, grammar in `Poset.lean`), a logic command or a formula with a connective or a
quantifier (`Logic.isLogicSource`, grammar in `Logic.lean`), and a λ-term or λ-command
(`Lam.isLambdaSource`, grammar in `Lambda.lean`) each have their own. A λ-command is routed first,
since one such as `type: f : A → B ⊢ f` holds a connective.
-/
namespace MathEngine

structure ParseError where
  message : String
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

inductive Stmt where
  /-- `let name = e`, or `let f(x, y) = e` with parameters. -/
  | «let» (name : String) (params : List String) (value : Expr)
  | expr (value : Expr)
  deriving Repr, Inhabited

def Stmt.value : Stmt → Expr | .«let» _ _ v => v | .expr v => v

inductive TokKind where | num | id | op | eof deriving Repr, DecidableEq, Inhabited

structure Tok where
  kind : TokKind
  s : String
  start : Nat
  stop : Nat
  deriving Repr, Inhabited

def builtinFunctions : List String :=
  ["sin", "cos", "tan", "sec", "csc", "cot", "arcsin", "arccos", "arctan",
   "exp", "ln", "log", "sqrt", "abs", "conj", "re", "im",
   "diff", "simplify", "expand", "factor", "N", "det", "rref", "transpose", "solve", "subst", "integrate", "plot",
   "sign", "dot", "norm", "sum", "exptotrig", "epicycles", "dft", "manipulate", "column",
   "total", "mean", "variance", "stdev", "min", "max", "median"]

/-- The unary builtins whose power is written before the argument: `sin^2(y)` is `sin(y)^2`. -/
def powerFunctions : List String :=
  ["sin", "cos", "tan", "sec", "csc", "cot", "arcsin", "arccos", "arctan", "exp", "ln", "log", "sqrt", "abs"]

/-- `sec`, `csc` and `cot` are notation, not functions: `sec u` is `(cos u)⁻¹`, and so on. The
engine knows the three it is written with, so their derivatives, integrals and values need nothing
new, and an answer written with `sec` is compared as what it means. -/
def reciprocalOf : String → Option String
  | "sec" => some "cos" | "csc" => some "sin" | "cot" => some "tan" | _ => none

/-- A call `f(args)`, with the reciprocal functions read as what they mean. -/
def mkCall (f : String) (args : List Expr) : Expr :=
  match reciprocalOf f, args with
  | some g, [u] => .pow (.fn g [u]) Expr.minusOne
  | _, _ => .fn f args

-- Greek letters (α … ω) and the script ℯ are identifier characters, so `π`, `φ`, `ℯ^x` parse
def lex.isGreek (c : Char) : Bool := (0x391 ≤ c.val && c.val ≤ 0x3C9) || c == 'ℯ'
def lex.isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || lex.isGreek c
def lex.isIdChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\'' || lex.isGreek c

theorem lex.isIdChar_of_isIdStart {c : Char} (h : lex.isIdStart c = true) : lex.isIdChar c = true := by
  simp only [lex.isIdStart, lex.isIdChar, Char.isAlphanum, Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h <;> simp [h]

/-- A numeral at the head of `cs`, `[0-9]*\.?[0-9]+ | [0-9]+`: its characters, and what follows. -/
def lexNum (cs : List Char) : List Char × List Char :=
  let ds := cs.takeWhile Char.isDigit
  let rest := cs.drop ds.length
  match rest with
  | '.' :: r => let f := r.takeWhile Char.isDigit; if f.isEmpty then (ds, rest) else (ds ++ '.' :: f, r.drop f.length)
  | _ => (ds, rest)

theorem lexNum_le (cs : List Char) (n : Nat) (h : (cs.takeWhile Char.isDigit).length ≥ n) :
    (lexNum cs).2.length ≤ cs.length - n := by
  unfold lexNum
  simp only
  split
  · next r hr =>
    have : (cs.drop (cs.takeWhile Char.isDigit).length).length = r.length + 1 := by rw [hr]; simp
    simp only [List.length_drop] at this
    split <;> simp <;> omega
  · simp; omega

/-- A numeral starts with a digit or with a point before one, so lexing one consumes a character. -/
theorem lexNum_lt {c : Char} {cs : List Char}
    (h : (c.isDigit || (c == '.' && (cs.head?.map Char.isDigit).getD false)) = true) :
    (lexNum (c :: cs)).2.length < cs.length + 1 := by
  by_cases hd : c.isDigit = true
  · have := lexNum_le (c :: cs) 1 (by simp [hd])
    simp at this; omega
  · simp [hd] at h
    obtain ⟨rfl, h⟩ := h
    match cs, h with
    | d :: ds, h =>
      simp at h
      unfold lexNum
      have hdot : Char.isDigit '.' = false := by decide
      simp [hdot, h]; omega

/-- Lexer over the character list; `i` is the byte-free character index used for spans. -/
def lex (src : String) : Except ParseError (Array Tok) := go src.toList 0 #[]
where
  go : List Char → Nat → Array Tok → Except ParseError (Array Tok)
    | [], i, acc => .ok (acc.push ⟨.eof, "", i, i⟩)
    | c :: cs, i, acc =>
      if c.isWhitespace then go cs (i + 1) acc
      else if h : c.isDigit || (c == '.' && (cs.head?.map Char.isDigit).getD false) then
        let r := lexNum (c :: cs)
        let text := String.ofList r.1
        go r.2 (i + text.length) (acc.push ⟨.num, text, i, i + text.length⟩)
      else if h : lex.isIdStart c then
        let ds := (c :: cs).takeWhile lex.isIdChar
        let text := String.ofList ds
        go ((c :: cs).drop ds.length) (i + ds.length) (acc.push ⟨.id, text, i, i + ds.length⟩)
      -- `./` and `.*`, the entrywise operators: a `.` before a digit was a numeral above
      else if c == '.' && (cs.head? == some '/' || cs.head? == some '*') then
        go cs.tail (i + 2) (acc.push ⟨.op, String.ofList (c :: cs.take 1), i, i + 2⟩)
      else if "+-*/^()[],;=%{}".contains c then go cs (i + 1) (acc.push ⟨.op, c.toString, i, i + 1⟩)
      else .error ⟨s!"unexpected character '{c}'", i, i + 1⟩
  termination_by cs _ _ => cs.length
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | exact lexNum_lt (by assumption)
      | (simp [lex.isIdChar_of_isIdStart (by assumption)]; omega)
      | (simp; omega)

/-- What the parsing functions read: the tokens, and the session's function names. The position
is an argument of its own, so that termination is on it. -/
structure PCtx where
  toks : Array Tok
  known : List String := []

/-- The token at `i`, or end of input past the last. -/
def PCtx.tok (c : PCtx) (i : Nat) : Tok := c.toks.getD i ⟨.eof, "", 0, 0⟩

/-- Only a real token is anything but end of input. -/
theorem PCtx.lt_of_kind {c : PCtx} {i : Nat} (h : (c.tok i).kind ≠ .eof) : i < c.toks.size := by
  unfold PCtx.tok at h
  rw [Array.getD_eq_getD_getElem?] at h
  apply Decidable.byContradiction
  intro hi
  rw [Array.getElem?_eq_none (by omega)] at h
  exact h rfl

theorem PCtx.lt_of_kind_eq {c : PCtx} {i : Nat} {k : TokKind} (h : (c.tok i).kind = k) (hk : k ≠ .eof) :
    i < c.toks.size :=
  PCtx.lt_of_kind (h ▸ hk)

def isOp (t : Tok) (s : String) : Bool := t.kind == .op && t.s == s

theorem PCtx.lt_of_isOp {c : PCtx} {i : Nat} {s : String} (h : isOp (c.tok i) s = true) : i < c.toks.size :=
  PCtx.lt_of_kind fun e => by simp [isOp, e] at h

/-- `;;` at `j`: a span. -/
def startsSpan (c : PCtx) (j : Nat) : Bool := isOp (c.tok j) ";" && isOp (c.tok (j + 1)) ";"

private def failT (msg : String) (t : Tok) : Except ParseError α := .error ⟨msg, t.start, t.stop⟩
private def startsAtom (t : Tok) : Bool := t.kind == .num || t.kind == .id || isOp t "(" || isOp t "[" || isOp t "%"

/-- What a parse from position `i` that consumed at least one token read, and where it stopped. -/
abbrev Adv (c : PCtx) (i : Nat) (α : Type) := α × {j : Nat // i < j ∧ j ≤ c.toks.size}
/-- The same for a parse that may consume nothing (a loop that found nothing to repeat). -/
abbrev Adv0 (c : PCtx) (i : Nat) (α : Type) := α × {j : Nat // i ≤ j ∧ j ≤ c.toks.size}

/-- The token `s` at `k`, or the error a missing one is. -/
private def expectAt (c : PCtx) (s : String) (k : Nat) : Except ParseError (PLift (k < c.toks.size)) :=
  if h : isOp (c.tok k) s then .ok ⟨PCtx.lt_of_isOp h⟩ else failT s!"expected '{s}'" (c.tok k)

/-- `%%…%` from `j`, `k` of them so far: how many, and where they stop. -/
def countPrev (c : PCtx) (j k : Nat) : Nat × Nat :=
  if h : isOp (c.tok j) "%" then countPrev c (j + 1) (k + 1) else (k, j)
termination_by c.toks.size - j
decreasing_by have := PCtx.lt_of_isOp h; omega

theorem countPrev_le (c : PCtx) (j k : Nat) (hj : j ≤ c.toks.size) :
    j ≤ (countPrev c j k).2 ∧ (countPrev c j k).2 ≤ c.toks.size := by
  unfold countPrev
  split
  · next h =>
    have := PCtx.lt_of_isOp h
    have := countPrev_le c (j + 1) (k + 1) (by omega)
    omega
  · simp; omega
termination_by c.toks.size - j

/-- The parser's termination goals: each function either consumes a token or calls one of a lower
rank at the same position. -/
local macro "parse_decreasing" : tactic => `(tactic| (
  simp_wf
  (try have := PCtx.lt_of_isOp (by assumption))
  (try omega)))

/-! Each function's measure is `8 · (tokens left) + rank`: a call at a later position always
decreases it, and a call at the same position goes to a lower rank, `atom` < `power` < `unary` <
`term` < `expr` < `spec`, `callArgs`. Every function but the loops that may find nothing to repeat
consumes a token on success, which its result type says. -/
mutual
  def expr (c : PCtx) (i : Nat) : Except ParseError (Adv c i Expr) := do
    let (lhs, ⟨j, hj⟩) ← term c i
    let (e, ⟨k, hk⟩) ← exprLoop c lhs j hj.2
    pure (e, ⟨k, by omega, hk.2⟩)
  termination_by 8 * (c.toks.size - i) + 4
  decreasing_by all_goals parse_decreasing

  def exprLoop (c : PCtx) (lhs : Expr) (j : Nat) (hj : j ≤ c.toks.size) : Except ParseError (Adv0 c j Expr) := do
    let t := c.tok j
    if h : isOp t "+" then
      let (rhs, ⟨k, hk⟩) ← term c (j + 1)
      let (e, ⟨m, hm⟩) ← exprLoop c (.add [lhs, rhs]) k hk.2
      pure (e, ⟨m, by omega, hm.2⟩)
    else if h : isOp t "-" then
      let (rhs, ⟨k, hk⟩) ← term c (j + 1)
      let (e, ⟨m, hm⟩) ← exprLoop c (Expr.sub lhs rhs) k hk.2
      pure (e, ⟨m, by omega, hm.2⟩)
    else pure (lhs, ⟨j, Nat.le_refl _, hj⟩)
  termination_by 8 * (c.toks.size - j) + 4
  decreasing_by all_goals parse_decreasing

  def term (c : PCtx) (i : Nat) : Except ParseError (Adv c i Expr) := do
    let (lhs, ⟨j, hj⟩) ← unary c i
    let (e, ⟨k, hk⟩) ← termLoop c lhs j hj.2
    pure (e, ⟨k, by omega, hk.2⟩)
  termination_by 8 * (c.toks.size - i) + 3
  decreasing_by all_goals parse_decreasing

  def termLoop (c : PCtx) (lhs : Expr) (j : Nat) (hj : j ≤ c.toks.size) : Except ParseError (Adv0 c j Expr) := do
    let t := c.tok j
    if h : isOp t "*" then
      let (rhs, ⟨k, hk⟩) ← unary c (j + 1)
      let (e, ⟨m, hm⟩) ← termLoop c (.mul [lhs, rhs]) k hk.2
      pure (e, ⟨m, by omega, hm.2⟩)
    else if h : isOp t "./" then
      let (rhs, ⟨k, hk⟩) ← unary c (j + 1)
      let (e, ⟨m, hm⟩) ← termLoop c (.fn "ediv" [lhs, rhs]) k hk.2
      pure (e, ⟨m, by omega, hm.2⟩)
    else if h : isOp t ".*" then
      let (rhs, ⟨k, hk⟩) ← unary c (j + 1)
      let (e, ⟨m, hm⟩) ← termLoop c (.fn "emul" [lhs, rhs]) k hk.2
      pure (e, ⟨m, by omega, hm.2⟩)
    else if h : isOp t "/" then
      let (rhs, ⟨k, hk⟩) ← unary c (j + 1)
      -- `3/4` is the rational 3/4, not the product 3 · 4⁻¹ (whose folding would show as steps)
      let lhs := match lhs, rhs with
        | .num p, .num q => if q.isZero then Expr.div lhs rhs else .num (p / q)
        | _, _ => Expr.div lhs rhs
      let (e, ⟨m, hm⟩) ← termLoop c lhs k hk.2
      pure (e, ⟨m, by omega, hm.2⟩)
    else if startsAtom t && !(t.kind == .num && ((if j = 0 then none else c.toks[j - 1]?).map (·.kind == .num)).getD false) then
      -- implicit multiplication
      let (rhs, ⟨k, hk⟩) ← unary c j
      let (e, ⟨m, hm⟩) ← termLoop c (.mul [lhs, rhs]) k hk.2
      pure (e, ⟨m, by omega, hm.2⟩)
    else pure (lhs, ⟨j, Nat.le_refl _, hj⟩)
  termination_by 8 * (c.toks.size - j) + 3
  decreasing_by all_goals parse_decreasing

  def unary (c : PCtx) (i : Nat) : Except ParseError (Adv c i Expr) := do
    if h : isOp (c.tok i) "-" then
      let (e, ⟨j, hj⟩) ← unary c (i + 1)
      -- a negative literal is one numeral, not (−1)·numeral: a matrix of 400 sampled points would
      -- otherwise cost a fold-constants step per negative entry (and `-2^2` is still −(2²): `power`
      -- returns a `pow`, not a numeral)
      let e := match e with
        | .num q => .num q.neg
        | e => Expr.neg e
      pure (e, ⟨j, by omega, hj.2⟩)
    else power c i
  termination_by 8 * (c.toks.size - i) + 2
  decreasing_by all_goals parse_decreasing

  def power (c : PCtx) (i : Nat) : Except ParseError (Adv c i Expr) := do
    let (a, ⟨j, hj⟩) ← atom c i
    let (b, ⟨k, hk⟩) ← part c a j hj.2
    if h : isOp (c.tok k) "^" then
      let (x, ⟨m, hm⟩) ← unary c (k + 1)
      pure (.pow b x, ⟨m, by omega, hm.2⟩)
    else pure (b, ⟨k, by omega, hk.2⟩)
  termination_by 8 * (c.toks.size - i) + 1
  decreasing_by all_goals parse_decreasing

  def atom (c : PCtx) (i : Nat) : Except ParseError (Adv c i Expr) := do
    let t := c.tok i
    match hk : t.kind with
    | .num =>
      match Q.parse t.s with
      | some q => pure (.num q, ⟨i + 1, by omega, PCtx.lt_of_kind_eq hk (by decide)⟩)
      | none => failT s!"bad number '{t.s}'" t
    | .id =>
      have hi : i < c.toks.size := PCtx.lt_of_kind_eq hk (by decide)
      let at_ (k : Nat) : Tok := c.tok (i + 1 + k)
      -- `sin^2(y)` is `sin(y)^2`: the textbook's power of a function, for the unary builtins.
      -- A negative power is one too: `sin^-1(y)` is `1/sin(y)`, never `arcsin(y)` (write that).
      let neg := isOp (at_ 1) "-"
      let k := if neg then 1 else 0
      let powFn := powerFunctions.contains t.s &&
        isOp (at_ 0) "^" && (at_ (1 + k)).kind == .num && isOp (at_ (2 + k)) "("
      if powFn then
        let n := c.tok (i + 2 + k)
        let q ← match Q.parse n.s with | some q => pure q | none => failT s!"bad number '{n.s}'" n
        let (args, ⟨j, hj⟩) ← callArgs c (i + 4 + k)
        pure (.pow (mkCall t.s args) (.num (if neg then q.neg else q)), ⟨j, by omega, hj.2⟩)
      else if isOp (c.tok (i + 1)) "(" && (builtinFunctions.contains t.s || c.known.contains t.s) then
        let (args, ⟨j, hj⟩) ← callArgs c (i + 2)
        pure (mkCall t.s args, ⟨j, by omega, hj.2⟩)
      else if t.s == "pi" || t.s == "π" then pure (.fn "π" [], ⟨i + 1, by omega, hi⟩)   -- a constant, not a variable: no binding, both semantics read it
      else if t.s == "i" then pure (.fn "i" [], ⟨i + 1, by omega, hi⟩)                   -- the imaginary unit (Mathematica's I)
      else if t.s == "ℯ" then pure (.fn "exp" [Expr.one], ⟨i + 1, by omega, hi⟩)   -- Euler's number is exp(1): every rule about exp applies
      else pure (.var t.s, ⟨i + 1, by omega, hi⟩)
    | .op =>
      have hi : i < c.toks.size := PCtx.lt_of_kind_eq hk (by decide)
      if t.s == "(" then
        let (e, ⟨j, hj⟩) ← expr c (i + 1)
        let ⟨hj'⟩ ← expectAt c ")" j
        pure (e, ⟨j + 1, by omega, hj'⟩)
      else if t.s == "%" then
        -- Mathematica's output references: `%` is the last output, `%%` the one before, `%n` is Out[n].
        -- The session resolves them (`resolveOuts`); they never reach the pipeline.
        let n := c.tok (i + 1)
        if h : n.kind == .num && n.start == t.stop && n.s.all Char.isDigit then
          have : i + 1 < c.toks.size := PCtx.lt_of_kind_eq (k := .num) (by simp at h; exact h.1.1) (by decide)
          pure (.fn "%out" [.num (Q.ofInt n.s.toNat!)], ⟨i + 2, by omega, this⟩)
        else
          have := countPrev_le c (i + 1) 1 hi
          pure (.fn "%prev" [.num (Q.ofInt (countPrev c (i + 1) 1).1)], ⟨(countPrev c (i + 1) 1).2, by omega, this.2⟩)
      else if t.s == "[" then
        let (rows, ⟨j, hj⟩) ← matRows c [] (i + 1)
        let ⟨hj'⟩ ← expectAt c "]" j
        let w := (rows.head?.map List.length).getD 0
        if rows.any (·.length != w) then failT "ragged matrix rows" t
        else pure (.matrix rows, ⟨j + 1, by omega, hj'⟩)
      else if t.s == "{" then failT "braces list the indices of a part, as in m[[{1, 3}]]" t
      else failT s!"unexpected '{t.s}'" t
    | .eof => failT "unexpected end of input" t
  termination_by 8 * (c.toks.size - i)
  decreasing_by all_goals parse_decreasing

  /-- The rows of a matrix literal from `j`, after its `[`. -/
  def matRows (c : PCtx) (rows : List (List Expr)) (j : Nat) : Except ParseError (Adv c j (List (List Expr))) := do
    let (e, ⟨k, hk⟩) ← expr c j
    let (row, ⟨m, hm⟩) ← exprList c [e] k hk.2
    let rows := rows ++ [row]
    if h : isOp (c.tok m) ";" then
      let (rows, ⟨p, hp⟩) ← matRows c rows (m + 1)
      pure (rows, ⟨p, by omega, hp.2⟩)
    else pure (rows, ⟨m, by omega, hm.2⟩)
  termination_by 8 * (c.toks.size - j) + 5
  decreasing_by all_goals parse_decreasing

  /-- `, e` while there is a comma at `k`, after `acc`. -/
  def exprList (c : PCtx) (acc : List Expr) (k : Nat) (hk : k ≤ c.toks.size) : Except ParseError (Adv0 c k (List Expr)) := do
    if h : isOp (c.tok k) "," then
      let (e, ⟨m, hm⟩) ← expr c (k + 1)
      let (es, ⟨p, hp⟩) ← exprList c (acc ++ [e]) m hm.2
      pure (es, ⟨p, by omega, hp.2⟩)
    else pure (acc, ⟨k, Nat.le_refl _, hk⟩)
  termination_by 8 * (c.toks.size - k) + 5
  decreasing_by all_goals parse_decreasing

  /-- `e[[…]]`, any number of times: Mathematica's Part, binding tighter than `^`. -/
  def part (c : PCtx) (e : Expr) (i : Nat) (hi : i ≤ c.toks.size) : Except ParseError (Adv0 c i Expr) := do
    if h : isOp (c.tok i) "[" && isOp (c.tok (i + 1)) "[" then
      have : i + 1 < c.toks.size := PCtx.lt_of_isOp (by simp at h; exact h.2)
      let (s, ⟨j, hj⟩) ← spec c (i + 2)
      let (specs, ⟨k, hk⟩) ← specList c [s] j hj.2
      let t := c.tok k
      if !isOp t "]" then failT "expected ']]' to close the part" t
      else
        let t := c.tok (k + 1)
        if h' : isOp t "]" then
          have := PCtx.lt_of_isOp h'
          let (e, ⟨m, hm⟩) ← part c (.fn "part" (e :: specs)) (k + 2) (by omega)
          pure (e, ⟨m, by omega, hm.2⟩)
        else failT "expected ']]' to close the part" t
    else pure (e, ⟨i, Nat.le_refl _, hi⟩)
  termination_by 8 * (c.toks.size - i) + 6
  decreasing_by all_goals parse_decreasing

  /-- `, spec` while there is a comma at `k`, after `acc`. -/
  def specList (c : PCtx) (acc : List Expr) (k : Nat) (hk : k ≤ c.toks.size) : Except ParseError (Adv0 c k (List Expr)) := do
    if h : isOp (c.tok k) "," then
      let (s, ⟨m, hm⟩) ← spec c (k + 1)
      let (ss, ⟨p, hp⟩) ← specList c (acc ++ [s]) m hm.2
      pure (ss, ⟨p, by omega, hp.2⟩)
    else pure (acc, ⟨k, Nat.le_refl _, hk⟩)
  termination_by 8 * (c.toks.size - k) + 6
  decreasing_by all_goals parse_decreasing

  /-- One index of a part: an expression, `All`, a span or a list of indices. -/
  def spec (c : PCtx) (i : Nat) : Except ParseError (Adv c i Expr) := do
    let t := c.tok i
    if h : t.kind == .id && t.s == "All" then
      have : i < c.toks.size := PCtx.lt_of_kind_eq (k := .id) (by simp at h; exact h.1) (by decide)
      return (.fn "All" [], ⟨i + 1, by omega, this⟩)
    if h : isOp t "{" then
      have := PCtx.lt_of_isOp h
      let (xs, ⟨j, hj⟩) ← (if isOp (c.tok (i + 1)) "}" then pure ([], ⟨i + 1, Nat.le_refl _, by omega⟩)
        else do
          let (x, ⟨j, hj⟩) ← expr c (i + 1)
          let (xs, ⟨k, hk⟩) ← exprList c [x] j hj.2
          pure (xs, ⟨k, by omega, hk.2⟩) : Except ParseError (Adv0 c (i + 1) (List Expr)))
      let ⟨hj'⟩ ← expectAt c "}" j
      return (.fn "List" xs, ⟨j + 1, by omega, hj'⟩)
    if h : startsSpan c i then
      spanFrom c (Expr.ofInt 1) i h
    else
      let (a, ⟨j, hj⟩) ← expr c i
      if h : startsSpan c j then
        let (s, ⟨k, hk⟩) ← spanFrom c a j h
        pure (s, ⟨k, by omega, hk.2⟩)
      else pure (a, ⟨j, hj⟩)
  termination_by 8 * (c.toks.size - i) + 6
  decreasing_by all_goals parse_decreasing

  /-- The rest of a span `a;;b` or `a;;b;;c`, from the `;;` at `j`: an omitted end is the last. -/
  def spanFrom (c : PCtx) (a : Expr) (j : Nat) (h : startsSpan c j = true) : Except ParseError (Adv c j Expr) := do
    have : j + 1 < c.toks.size := PCtx.lt_of_isOp (by simp [startsSpan] at h; exact h.2)
    let ends (t : Tok) : Bool := isOp t "," || isOp t "]" || isOp t ";"
    let (b, ⟨k, hk⟩) ← (if ends (c.tok (j + 2)) then pure (Expr.ofInt (-1), ⟨j + 2, Nat.le_refl _, by omega⟩)
      else do
        let (b, ⟨k, hk⟩) ← expr c (j + 2)
        pure (b, ⟨k, by omega, hk.2⟩) : Except ParseError (Adv0 c (j + 2) Expr))
    if h' : startsSpan c k then
      have : k + 1 < c.toks.size := PCtx.lt_of_isOp (by simp [startsSpan] at h'; exact h'.2)
      let (s, ⟨m, hm⟩) ← expr c (k + 2)
      pure (.fn "span" [a, b, s], ⟨m, by omega, hm.2⟩)
    else pure (.fn "span" [a, b, Expr.one], ⟨k, by omega, hk.2⟩)
  termination_by 8 * (c.toks.size - j) + 5
  decreasing_by all_goals parse_decreasing

  /-- The arguments of a call from `i`, after its `(`; consumes the `)`. -/
  def callArgs (c : PCtx) (i : Nat) : Except ParseError (Adv c i (List Expr)) := do
    let (args, ⟨j, hj⟩) ← (if h : isOp (c.tok i) ")" then pure ([], ⟨i, Nat.le_refl _, Nat.le_of_lt (PCtx.lt_of_isOp h)⟩)
      else do
        let (x, ⟨j, hj⟩) ← expr c i
        let (xs, ⟨k, hk⟩) ← exprList c [x] j hj.2
        pure (xs, ⟨k, by omega, hk.2⟩) : Except ParseError (Adv0 c i (List Expr)))
    let ⟨hj'⟩ ← expectAt c ")" j
    pure (args, ⟨j + 1, by omega, hj'⟩)
  termination_by 8 * (c.toks.size - i) + 6
  decreasing_by all_goals parse_decreasing
end

/-- `x, y, …)` of `let f(x, y) = …`, from `k`: the parameters, and where they stop. -/
def paramList (c : PCtx) (ps : List String) (k : Nat) : Except ParseError (List String × Nat) :=
  let x := c.tok k
  if h : x.kind != .id then failT "expected a parameter name" x
  else
    have : k < c.toks.size := PCtx.lt_of_kind_eq (k := .id) (by simpa using h) (by decide)
    let ps := ps ++ [x.s]
    let sep := c.tok (k + 1)
    if isOp sep ")" then .ok (ps, k + 2)
    else if !isOp sep "," then failT "expected ',' or ')' in the parameter list" sep
    else paramList c ps (k + 2)
termination_by c.toks.size - k

/-- Parse a statement. `known` lists session-defined function names that may be called. -/
def parseStmt (src : String) (known : List String := []) : Except ParseError Stmt := do
  let toks ← lex src
  let c : PCtx := { toks, known }
  let t := c.tok 0
  let (stmt, j) ← (if t.kind == .id && t.s == "let" then do
      let name := c.tok 1
      if name.kind != .id then failT "expected a name after 'let'" name
      -- an optional parameter list: let f(x, y) = ...
      let (params, k) ← if isOp (c.tok 2) "(" then paramList c [] 3 else pure ([], 2)
      let _ ← expectAt c "=" k
      -- inside the body the function may call itself or other session functions
      let (v, ⟨m, _⟩) ← expr { c with known := name.s :: c.known } (k + 1)
      pure (Stmt.«let» name.s params v, m)
    else do
      let (v, ⟨m, _⟩) ← expr c 0
      pure (Stmt.expr v, m) : Except ParseError (Stmt × Nat))
  let t := c.tok j
  if t.kind != .eof then failT s!"unexpected '{t.s}'" t
  pure stmt

def parse (src : String) (known : List String := []) : Except ParseError Expr :=
  (parseStmt src known).map Stmt.value

end MathEngine
