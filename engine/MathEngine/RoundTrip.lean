import MathEngine.Parser
import MathEngine.Print
/-!
# Reading back what the printer writes

The lexer, the algebra parser and the printer are total (`Parser.lean`, `Print.lean`). This file
proves that, on a fragment, reading back what the printer writes gives the term it printed:

```
parse_toText : Plain e → ∃ e', parse e.toText = .ok e' ∧ flat e' = flat e
```

`flat` splices a sum into a sum and a product into a product, as the normalizer's first rules do.
The parser reads `a + b + c` as `(a + b) + c`, and the printer writes `(a + b) + c` and
`a + b + c` alike, so "the same up to `flat`" is as close as the text allows. The statement is
about terms, not values: no real arithmetic is involved.

The fragment (`Plain`) is:
- natural numerals;
- variables: names the lexer reads as one identifier, other than a builtin function, `pi`, `π`,
  `i`, `ℯ` and `let`;
- calls `f(a)` of `sin cos tan arcsin arccos arctan ln log sqrt abs`;
- powers, with any exponent in the fragment;
- sums and products of two or more terms.

Outside it, the golden corpus's read-back check (`goldenTests`) still holds the printer to the
parser, but nothing is proved:
- negative numbers and subtraction;
- division and negative exponents (`x^(-2)` prints as `1/x^2`, which reads back as another term
  with the same value);
- decimals and scientific notation;
- `exp` (`exp(1)` prints as `ℯ`) and calls of several arguments;
- matrices, parts, the entrywise operators, and the other worlds' notation.

The proof follows the text through each stage:
1. **Printer** (`printRaw_plain`): the text of `e` is the characters of a token list, `ptoks e ctx`.
2. **Lexer** (`lex_render`, `lexable_plain`): lexing those characters gives back those tokens, then
   the end of input. `parse_digits` reads a printed numeral back.
3. **Parser** (`good`): at each level of the grammar, from where the tokens of `e` start, the parser
   reads a term that flattens to `e` and stops right after them. Products and sums go through their
   `units` and `summands`, which the parser folds to the left.
-/
namespace MathEngine
namespace RoundTrip

/-- A token as the parser reads it: its kind and its text, without its span. -/
abbrev T := TokKind × String

mutual
  /-- `e` with every sum in a sum and every product in a product spliced into it: `(a + b) + c`
  and `a + (b + c)` are both `a + b + c`. The normalizer's first rules do the same. -/
  def flat : Expr → Expr
    | .num q => .num q
    | .var x => .var x
    | .add es => .add (flatAdd es)
    | .mul es => .mul (flatMul es)
    | .pow b x => .pow (flat b) (flat x)
    | .fn f es => .fn f (flatList es)
    | .matrix rows => .matrix (flatRows rows)
  def flatAdd : List Expr → List Expr
    | [] => []
    | e :: es => (match flat e with | .add as => as | e' => [e']) ++ flatAdd es
  def flatMul : List Expr → List Expr
    | [] => []
    | e :: es => (match flat e with | .mul as => as | e' => [e']) ++ flatMul es
  def flatList : List Expr → List Expr
    | [] => []
    | e :: es => flat e :: flatList es
  def flatRows : List (List Expr) → List (List Expr)
    | [] => []
    | r :: rs => flatList r :: flatRows rs
end

/-- Names a variable may not have: they read as something else. -/
def reserved : List String := "pi" :: "π" :: "i" :: "ℯ" :: "let" :: builtinFunctions

/-- The calls of one argument the fragment has; `exp` is left out, since `exp(1)` prints as `ℯ`. -/
def unaryNames : List String :=
  ["sin", "cos", "tan", "arcsin", "arccos", "arctan", "ln", "log", "sqrt", "abs"]

/-- The lexer reads `x` as one identifier. -/
def isIdent (x : String) : Bool :=
  match x.toList with
  | c :: cs => lex.isIdStart c && cs.all lex.isIdChar
  | [] => false

/-- The fragment the round trip is proved for: natural numerals, variables, calls of one argument,
powers, and sums and products of two or more terms. -/
inductive Plain : Expr → Prop
  | num (n : Nat) : Plain (.num (Q.ofInt n))
  | var (x : String) : isIdent x = true → x ∉ reserved → Plain (.var x)
  | fn (f : String) (a : Expr) : f ∈ unaryNames → Plain a → Plain (.fn f [a])
  | pow (b x : Expr) : Plain b → Plain x → Plain (.pow b x)
  | add (a b : Expr) (as : List Expr) : Plain a → Plain b → (∀ c ∈ as, Plain c) → Plain (.add (a :: b :: as))
  | mul (a b : Expr) (as : List Expr) : Plain a → Plain b → (∀ c ∈ as, Plain c) → Plain (.mul (a :: b :: as))

/-- How tightly the printer says a term binds (`P_ADD` … `P_ATOM`). -/
def precOf : Expr → Nat
  | .add _ => 1 | .mul _ => 2 | .pow _ _ => 3 | _ => 4

@[scoped simp] theorem precOf_add (l : List Expr) : precOf (.add l) = 1 := rfl
@[scoped simp] theorem precOf_mul (l : List Expr) : precOf (.mul l) = 2 := rfl
@[scoped simp] theorem precOf_pow (b x : Expr) : precOf (.pow b x) = 3 := rfl
@[scoped simp] theorem precOf_num (q : Q) : precOf (.num q) = 4 := rfl
@[scoped simp] theorem precOf_var (x : String) : precOf (.var x) = 4 := rfl
@[scoped simp] theorem precOf_fn (f : String) (l : List Expr) : precOf (.fn f l) = 4 := rfl

theorem precOf_lt_one (e : Expr) : ¬ precOf e < 1 := by cases e <;> simp [precOf]

def paren (b : Bool) (ts : List T) : List T := if b then (.op, "(") :: ts ++ [(.op, ")")] else ts

mutual
  /-- The tokens of a term as the printer writes it, before any parentheses its context needs. -/
  def raw : Expr → List T
    | .num q => [(.num, toString q.val.num)]
    | .var x => [(.id, x)]
    | .fn f [a] => (.id, f) :: (.op, "(") :: paren (precOf a < 1) (raw a) ++ [(.op, ")")]
    | .pow b x => paren (precOf b < 4) (raw b) ++ (.op, "^") :: paren (precOf x < 3) (raw x)
    | .add (a :: as) => paren (precOf a < 1) (raw a) ++ rawTail "+" as
    | .mul (a :: as) => paren (precOf a < 2) (raw a) ++ rawTail "*" as
    | _ => []
  def rawTail (sep : String) : List Expr → List T
    | [] => []
    | a :: as => (.op, sep) :: paren (precOf a < 2) (raw a) ++ rawTail sep as
end

@[scoped simp] theorem paren_false (ts : List T) : paren false ts = ts := rfl

/-- The tokens of `e` printed where the context demands precedence `ctx`. -/
def ptoks (e : Expr) (ctx : Nat) : List T := paren (precOf e < ctx) (raw e)

/-- The characters of a token: a sum's `+` has a space either side. -/
def renderTok : T → List Char
  | (.op, "+") => [' ', '+', ' ']
  | t => t.2.toList

def render (ts : List T) : List Char := ts.flatMap renderTok

/-! ## The printer writes the tokens -/

theorem ofInt_num (n : Nat) : (Q.ofInt n).val.num = n := by simp [Q.ofInt]

theorem ofInt_abs (n : Nat) : (Q.ofInt n).abs = Q.ofInt n := by
  have : 0 ≤ Rat.ofInt n := Rat.num_nonneg.1 (by simp)
  simp [Q.abs, Q.ofInt, Rat.abs_of_nonneg this]

theorem ofInt_text (n : Nat) : (Q.ofInt n).toText = toString (n : Int) := by
  simp [Q.toText, Q.isSci, Q.sciExp, Q.ofInt, Q.isInt]

theorem ofInt_not_half (n : Nat) : (Expr.num (Q.ofInt n)).isNumEq (Q.ofRat (mkRat 1 2)) = false := by
  simp [Expr.isNumEq, Q.eq, Q.ofInt, Q.ofRat]
  intro h
  have := congrArg Rat.den h
  simp at this
  exact absurd this (by decide)

@[scoped simp] theorem render_nil : render [] = [] := rfl
@[scoped simp] theorem render_cons (t : T) (ts : List T) : render (t :: ts) = renderTok t ++ render ts := by
  simp [render]
@[scoped simp] theorem render_append (a b : List T) : render (a ++ b) = render a ++ render b := by simp [render]
@[scoped simp] theorem renderTok_num (s : String) : renderTok (.num, s) = s.toList := rfl
@[scoped simp] theorem renderTok_id (s : String) : renderTok (.id, s) = s.toList := rfl
@[scoped simp] theorem renderTok_plus : renderTok (.op, "+") = [' ', '+', ' '] := rfl
theorem renderTok_op {s : String} (h : s ≠ "+") : renderTok (.op, s) = s.toList := by
  simp [renderTok, h]
@[scoped simp] theorem renderTok_lp : renderTok (.op, "(") = ['('] := rfl
@[scoped simp] theorem renderTok_rp : renderTok (.op, ")") = [')'] := rfl
@[scoped simp] theorem renderTok_star : renderTok (.op, "*") = ['*'] := rfl
@[scoped simp] theorem renderTok_hat : renderTok (.op, "^") = ['^'] := rfl

theorem render_paren (b : Bool) (ts : List T) :
    render (paren b ts) = if b then '(' :: render ts ++ [')'] else render ts := by
  cases b <;> simp [paren]

theorem intercalate_star (s : String) (l : List String) :
    ("*".intercalate (s :: l)).toList = s.toList ++ l.flatMap ('*' :: ·.toList) := by
  induction l generalizing s with
  | nil => simp
  | cons t l ih => simp [String.intercalate_cons_cons, ih]

theorem printRaw_num (n : Nat) (path : Path) :
    printRaw (.num (Q.ofInt n)) path textTarget = (toString (n : Int), P_ATOM) := by
  rw [printRaw]
  have : ¬ ((n : Int) < 0) := by omega
  simp [textTarget, Q.toText, Q.isSci, Q.sciExp, Q.ofInt, Q.isNeg, Q.isInt, this]

theorem printRaw_var (x : String) (path : Path) : printRaw (.var x) path textTarget = (x, P_ATOM) := by
  rw [printRaw]; rfl

/-- What the printer does with a term of the fragment: its text is its tokens, and it says how
tightly it binds. -/
def PrintsAs (e : Expr) : Prop :=
  ∀ path, (printRaw e path textTarget).1.toList = render (raw e) ∧ (printRaw e path textTarget).2 = precOf e

theorem print_text (e : Expr) (path : Path) (ctx : Nat) :
    print e path textTarget ctx =
      if (printRaw e path textTarget).2 < ctx then "(" ++ (printRaw e path textTarget).1 ++ ")"
      else (printRaw e path textTarget).1 := by
  rw [print]; simp [textTarget]; rfl

theorem PrintsAs.print {e : Expr} (h : PrintsAs e) (path : Path) (ctx : Nat) :
    (print e path textTarget ctx).toList = render (ptoks e ctx) := by
  rw [print_text, ptoks, render_paren]
  obtain ⟨h1, h2⟩ := h path
  rw [h2]
  by_cases hc : precOf e < ctx <;> simp [hc, h1]

theorem ofInt_isNeg (n : Nat) : (Q.ofInt n).isNeg = false := by
  simp only [Q.isNeg, Q.ofInt]; exact decide_eq_false (by simp)

theorem ofInt_isInt (n : Nat) : (Q.ofInt n).isInt = true := by simp [Q.isInt, Q.ofInt]

theorem splitCoeff_plain {a : Expr} (h : Plain a) : (splitCoeff a).1.isNeg = false := by
  cases h with
  | num n => exact ofInt_isNeg n
  | mul a b as ha =>
    cases ha with
    | num n => exact ofInt_isNeg n
    | _ => rfl
  | _ => rfl

theorem addTerms_tail (path : Path) : ∀ (rest : List Expr), (∀ c ∈ rest, Plain c ∧ PrintsAs c) →
    ∀ (i : Nat) (acc : String), i ≠ 0 →
    (addTerms rest i path textTarget acc).toList = acc.toList ++ render (rawTail "+" rest)
  | [], _, i, acc, _ => by rw [addTerms]; simp [rawTail, render]
  | a :: rest, h, i, acc, hi => by
    rw [addTerms]
    have ha := h a (by simp)
    have := addTerms_tail path rest (fun c hc => h c (by simp [hc])) (i + 1)
    simp only [splitCoeff_plain ha.1]
    rw [this _ (by omega)]
    have hp := ha.2.print (path ++ [i]) 2
    simp [hi, hp, rawTail, ptoks, P_MUL]

theorem mulFactor_plain {f : Expr} (h : Plain f) (hp : PrintsAs f) (i : Nat) (p : Path)
    (sign : String) (numer denom : List String) :
    ∃ s, mulFactor f i p textTarget sign numer denom = (sign, numer ++ [s], denom) ∧
      s.toList = render (ptoks f 2) := by
  cases h with
  | num n =>
    rw [mulFactor]
    by_cases hi : i = 0
    · subst hi
      simp [ofInt_isNeg, ofInt_abs, ofInt_isInt, textTarget, ofInt_text, ptoks, paren, raw, precOf, ofInt_num]
    · have := hp.print p 3
      simp [hi, this, ptoks, paren, precOf, P_MUL]
  | pow b x hb hx =>
    cases hx with
    | num n =>
      rw [mulFactor]
      simp [ofInt_isNeg, hp.print p 2, P_MUL]
    | _ => rw [mulFactor] <;> first | simp [hp.print p 2, P_MUL] | (intros; simp_all)
  | _ => rw [mulFactor] <;> first | simp [hp.print p 2, P_MUL] | (intros; simp_all)

theorem mulFactors_plain (path : Path) (off : Nat) : ∀ (args : List Expr), (∀ c ∈ args, Plain c ∧ PrintsAs c) →
    ∀ (i : Nat) (sign : String) (numer denom : List String),
    ∃ strs : List String, mulFactors args i path off textTarget sign numer denom = (sign, numer ++ strs, denom) ∧
      strs.map String.toList = args.map (fun c => render (ptoks c 2))
  | [], _, i, sign, numer, denom => ⟨[], by rw [mulFactors]; simp, rfl⟩
  | a :: rest, h, i, sign, numer, denom => by
    have ha := h a (by simp)
    obtain ⟨s, hs, hs'⟩ := mulFactor_plain ha.1 ha.2 i (path ++ [i + off]) sign numer denom
    obtain ⟨strs, h1, h2⟩ := mulFactors_plain path off rest (fun c hc => h c (by simp [hc])) (i + 1) sign (numer ++ [s]) denom
    refine ⟨s :: strs, ?_, ?_⟩
    · rw [mulFactors]; simp [hs, h1]
    · simp [hs', h2]

theorem render_rawTail (sep : String) (hsep : sep ≠ "+") (as : List Expr) :
    render (rawTail sep as) = as.flatMap (fun c => sep.toList ++ render (ptoks c 2)) := by
  induction as with
  | nil => simp [rawTail, render]
  | cons a as ih =>
    simp only [rawTail, List.flatMap_cons]
    rw [← ih]
    have : renderTok (.op, sep) = sep.toList := by simp [renderTok, hsep]
    simp [render, this, ptoks]

theorem flatMap_star (l : List String) : l.flatMap ('*' :: ·.toList) = (l.map String.toList).flatMap ('*' :: ·) := by
  induction l <;> simp_all

theorem printRaw_fn (f : String) (a : Expr) (hf : f ∈ unaryNames) (path : Path) :
    printRaw (.fn f [a]) path textTarget = fnRaw textTarget f [a] (printArgs [a] 0 path textTarget) := by
  rw [printRaw]
  all_goals first | rfl | (intros; subst_vars; simp [unaryNames] at hf)

theorem fnRaw_generic (f : String) (a : Expr) (s : String) (hf : f ∈ unaryNames) (h1 : f ≠ "sqrt")
    (h2 : f ≠ "abs") : fnRaw textTarget f [a] [s] = (f ++ "(" ++ s ++ ")", P_ATOM) := by
  rw [fnRaw]
  all_goals first | (simp [textTarget]; rfl) | (intros; subst_vars; simp_all [unaryNames])

theorem fnRaw_sqrt (a : Expr) (s : String) : fnRaw textTarget "sqrt" [a] [s] = ("sqrt" ++ "(" ++ s ++ ")", P_ATOM) := by
  rw [fnRaw]; simp [textTarget]; rfl

theorem fnRaw_abs (a : Expr) (s : String) : fnRaw textTarget "abs" [a] [s] = ("abs" ++ "(" ++ s ++ ")", P_ATOM) := by
  rw [fnRaw]; simp [textTarget]; rfl

theorem printRaw_pow {x : Expr} (hx : Plain x) (b : Expr) (path : Path) :
    printRaw (.pow b x) path textTarget =
      (print b (path ++ [0]) textTarget 4 ++ "^" ++ print x (path ++ [1]) textTarget 3, P_POW) := by
  cases hx with
  | num n =>
    rw [printRaw, powRaw]
    simp [textTarget, ofInt_not_half, ofInt_isNeg, ofInt_isInt, P_POW]; rfl
  | _ =>
    rw [printRaw, powRaw]
    all_goals first | (simp [textTarget, Expr.isNumEq, P_POW]; rfl) | (intros; simp_all)

theorem printRaw_plain {e : Expr} (h : Plain e) : PrintsAs e := by
  induction h with
  | num n => intro path; simp [printRaw_num, raw, render, renderTok, ofInt_num, precOf, P_ATOM]
  | var x _ _ => intro path; simp [printRaw_var, raw, render, renderTok, precOf, P_ATOM]
  | fn f a hf _ iha =>
    intro path
    have hp := iha.print (path ++ [0]) 1
    have hargs : printArgs [a] 0 path textTarget = [print a (path ++ [0]) textTarget P_ADD] := by
      rw [printArgs, printArgs]
    rw [printRaw_fn f a hf, hargs]
    have hfn : fnRaw textTarget f [a] [print a (path ++ [0]) textTarget P_ADD] =
        (f ++ "(" ++ print a (path ++ [0]) textTarget P_ADD ++ ")", P_ATOM) := by
      by_cases h1 : f = "sqrt"
      · subst h1; exact fnRaw_sqrt _ _
      by_cases h2 : f = "abs"
      · subst h2; exact fnRaw_abs _ _
      exact fnRaw_generic f a _ hf h1 h2
    rw [hfn]
    refine ⟨?_, rfl⟩
    simp only [P_ADD]
    simp [hp, raw, ptoks]
  | pow b x hb hx ihb ihx =>
    intro path
    rw [printRaw_pow hx]
    simp [ihb.print, ihx.print, raw, ptoks, precOf, P_POW]
  | add a b as ha hb has iha ihb ihas =>
    intro path
    have hall : ∀ c ∈ b :: as, Plain c ∧ PrintsAs c := by
      intro c hc; simp at hc; rcases hc with rfl | hc
      · exact ⟨hb, ihb⟩
      · exact ⟨has c hc, ihas c hc⟩
    have ht := addTerms_tail path (b :: as) hall 1 (print a (path ++ [0]) textTarget P_ADD) (by omega)
    rw [printRaw]
    refine ⟨?_, rfl⟩
    rw [addTerms]
    simp only [splitCoeff_plain ha, P_ADD] at ht ⊢
    simp [ht, iha.print, raw, ptoks]
  | mul a b as ha hb has iha ihb ihas =>
    intro path
    have hall : ∀ c ∈ a :: b :: as, Plain c ∧ PrintsAs c := by
      intro c hc; simp at hc; rcases hc with rfl | rfl | hc
      · exact ⟨ha, iha⟩
      · exact ⟨hb, ihb⟩
      · exact ⟨has c hc, ihas c hc⟩
    obtain ⟨strs, h1, h2⟩ := mulFactors_plain path 0 (a :: b :: as) hall 0 "" [] []
    rw [printRaw, mulRaw, h1]
    match strs, h2 with
    | s :: rest, h2 =>
      simp only [List.map_cons, List.cons.injEq] at h2
      have hs : ("*".intercalate (s :: rest)).toList = render (raw (.mul (a :: b :: as))) := by
        rw [intercalate_star, flatMap_star, h2.1, h2.2, raw, render_append, render_rawTail "*" (by decide)]
        simp [ptoks, List.flatMap_map]
      simp [textTarget, hs, precOf, P_MUL]

/-! ## The lexer reads the tokens back -/

/-- The one-character operators the fragment prints. -/
def opChars : List Char := ['+', '*', '^', '(', ')']

/-- A token the lexer reads back as itself. -/
def TokOk : T → Prop
  | (.num, s) => s.toList ≠ [] ∧ ∀ c ∈ s.toList, c.isDigit = true
  | (.id, s) => isIdent s = true
  | (.op, s) => ∃ c ∈ opChars, s = String.singleton c
  | (.eof, _) => False

/-- A number or a name: two of them in a row would run together. -/
def isWord : T → Bool
  | (.num, _) | (.id, _) => true
  | _ => false

/-- A token list whose rendering lexes back to it. -/
def Lexable : List T → Prop
  | [] => True
  | [t] => TokOk t
  | t :: u :: ts => TokOk t ∧ ¬(isWord t = true ∧ isWord u = true) ∧ Lexable (u :: ts)

/-- What may follow a word without running into it: an operator, or the space before `+`. -/
def HeadOk (r : List Char) : Prop := ∀ c, r.head? = some c → c ∈ opChars ∨ c = ' '

theorem headOk_nil : HeadOk [] := by intro c h; simp at h

theorem not_digit_of_headOk {c : Char} (h : c ∈ opChars ∨ c = ' ') : c.isDigit = false ∧ c ≠ '.' ∧
    lex.isIdChar c = false := by
  simp only [opChars, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with (rfl | rfl | rfl | rfl | rfl) | rfl <;> decide

theorem takeWhile_append_of_all {p : Char → Bool} {ds r : List Char} (hd : ∀ c ∈ ds, p c = true)
    (hr : ∀ c, r.head? = some c → p c = false) : (ds ++ r).takeWhile p = ds := by
  induction ds with
  | nil => cases r with
    | nil => rfl
    | cons c r => simp [hr c rfl]
  | cons d ds ih =>
    simp only [List.cons_append, List.takeWhile_cons, hd d (by simp), ite_true]
    rw [ih (fun c hc => hd c (by simp [hc]))]

/-- A numeral, then something that is not a digit or a point. -/
theorem lex_num {ds r : List Char} (hne : ds ≠ []) (hd : ∀ c ∈ ds, c.isDigit = true) (hr : HeadOk r)
    (i : Nat) (acc : Array Tok) :
    lex.go (ds ++ r) i acc =
      lex.go r (i + ds.length) (acc.push ⟨.num, String.ofList ds, i, i + ds.length⟩) := by
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, ds = c :: cs := List.exists_cons_of_ne_nil hne
  have hc : c.isDigit = true := hd c (by simp)
  have hw : c.isWhitespace = false := by
    revert hc; generalize c = c
    intro hc; simp only [Char.isDigit, Char.isWhitespace, Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro h <;> rw [h] at hc <;> simp at hc
  have hn : lexNum (c :: cs ++ r) = (c :: cs, r) := by
    have ht : (c :: cs ++ r).takeWhile Char.isDigit = c :: cs :=
      takeWhile_append_of_all hd (fun x hx => (not_digit_of_headOk (hr x hx)).1)
    unfold lexNum
    simp only [ht]
    have hdrop : (c :: cs ++ r).drop (c :: cs).length = r := by simp
    rw [hdrop]
    cases r with
    | nil => rfl
    | cons x r' =>
      have hx := (not_digit_of_headOk (hr x rfl)).2.1
      simp [hx]
  rw [lex.go.eq_def]
  simp only [List.cons_append, hw, hc, Bool.true_or, dite_true, Bool.false_eq_true, ite_false]
  rw [← List.cons_append, hn]
  simp only [String.length_ofList, List.length_cons]

/-- A name starts with neither a digit, a space nor a point. -/
theorem idStart_facts {c : Char} (h : lex.isIdStart c = true) :
    c.isDigit = false ∧ c.isWhitespace = false ∧ c ≠ '.' := by
  simp only [lex.isIdStart, lex.isGreek, Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  simp only [Char.isDigit, Char.isWhitespace, Bool.and_eq_false_iff, decide_eq_false_iff_not,
    Bool.or_eq_false_iff, ne_eq, Char.ext_iff, UInt32.le_iff_toNat_le, ge_iff_le, ← UInt32.toNat_inj] at h ⊢
  simp at h ⊢
  omega

/-- A name, then something that is not a name's character. -/
theorem lex_id {x : String} (hx : isIdent x = true) {r : List Char} (hr : HeadOk r) (i : Nat) (acc : Array Tok) :
    lex.go (x.toList ++ r) i acc =
      lex.go r (i + x.toList.length) (acc.push ⟨.id, x, i, i + x.toList.length⟩) := by
  unfold isIdent at hx
  split at hx
  · next c cs hcs =>
    simp only [Bool.and_eq_true, List.all_eq_true] at hx
    obtain ⟨hs, hall⟩ := hx
    obtain ⟨hd, hw, hdot⟩ := idStart_facts hs
    have ht : (x.toList ++ r).takeWhile lex.isIdChar = x.toList := by
      apply takeWhile_append_of_all
      · rw [hcs]; intro d hd'; simp at hd'; rcases hd' with rfl | hd'
        · exact lex.isIdChar_of_isIdStart hs
        · exact hall d hd'
      · exact fun y hy => (not_digit_of_headOk (hr y hy)).2.2
    rw [hcs] at ht ⊢
    rw [lex.go.eq_def]
    have hdot' : (c == '.') = false := by simp [hdot]
    simp only [List.cons_append, hw, hd, hdot', hs, Bool.false_or, Bool.false_and, dite_true,
      Bool.false_eq_true, ite_false, dite_false]
    rw [← List.cons_append, ht]
    have : String.ofList (c :: cs) = x := by rw [← hcs, String.ofList_toList]
    simp [this]
  · simp at hx

theorem lex_op {c : Char} (hc : c ∈ opChars) (hp : c ≠ '+') (r : List Char) (i : Nat) (acc : Array Tok) :
    lex.go (c :: r) i acc = lex.go r (i + 1) (acc.push ⟨.op, String.singleton c, i, i + 1⟩) := by
  simp only [opChars, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl hp
  all_goals
    rw [lex.go.eq_def]
    simp [lex.isIdStart, lex.isGreek]

theorem lex_plus (r : List Char) (i : Nat) (acc : Array Tok) :
    lex.go (' ' :: '+' :: ' ' :: r) i acc = lex.go r (i + 3) (acc.push ⟨.op, "+", i + 1, i + 2⟩) := by
  rw [lex.go.eq_def]; simp
  rw [lex.go.eq_def]; simp [lex.isIdStart, lex.isGreek]
  rw [lex.go.eq_def]; simp

/-- A token without its span. -/
def strip (t : Tok) : T := (t.kind, t.s)

/-- One token, read off the front of the characters. -/
theorem lex_tok {t : T} (ht : TokOk t) {r : List Char} (hr : isWord t = true → HeadOk r) (i : Nat)
    (acc : Array Tok) : ∃ i' tok, strip tok = t ∧
      lex.go (renderTok t ++ r) i acc = lex.go r i' (acc.push tok) := by
  match t, ht with
  | (.num, s), ⟨hne, hd⟩ =>
    refine ⟨_, _, ?_, lex_num (ds := s.toList) (by simpa using hne) hd (hr rfl) i acc⟩
    simp [strip]
  | (.id, s), hs => exact ⟨_, _, rfl, lex_id hs (hr rfl) i acc⟩
  | (.op, s), ⟨c, hc, hsc⟩ =>
    subst hsc
    by_cases hp : c = '+'
    · subst hp
      exact ⟨_, _, rfl, lex_plus r i acc⟩
    · have : renderTok (.op, String.singleton c) = [c] := by
        rw [renderTok_op (by intro h; exact hp (by simpa using congrArg String.toList h))]; simp
      rw [this]
      exact ⟨_, _, rfl, lex_op hc hp r i acc⟩

theorem headOk_render {u : T} (hu : TokOk u) (hw : isWord u = false) (ts : List T) :
    HeadOk (render (u :: ts)) := by
  match u, hu, hw with
  | (.op, s), ⟨c, hc, hsc⟩, _ =>
    subst hsc
    intro x hx
    by_cases hp : c = '+'
    · subst hp; simp at hx; exact .inr hx.symm
    · have : renderTok (.op, String.singleton c) = [c] := by
        rw [renderTok_op (by intro h; exact hp (by simpa using congrArg String.toList h))]; simp
      simp [this] at hx; subst hx; exact .inl hc

/-- The lexer reads back a rendered token list, and then the end of input. -/
theorem lex_render : ∀ (ts : List T), Lexable ts → ∀ (i : Nat) (acc : Array Tok),
    ∃ arr, lex.go (render ts) i acc = .ok arr ∧
      arr.toList.map strip = acc.toList.map strip ++ ts ++ [(.eof, "")]
  | [], _, i, acc => ⟨_, by rw [render_nil, lex.go.eq_def], by simp [strip]⟩
  | [t], ht, i, acc => by
    obtain ⟨i', tok, hs, he⟩ := lex_tok (r := []) ht (fun _ => headOk_nil) i acc
    simp only [render_cons, render_nil]
    rw [he, lex.go.eq_def]
    exact ⟨_, rfl, by simp [strip] at hs ⊢; exact hs⟩
  | t :: u :: ts, ⟨ht, hw, hrest⟩, i, acc => by
    have hr : isWord t = true → HeadOk (render (u :: ts)) := by
      intro htw
      have hu : TokOk u := by
        match ts, hrest with
        | [], h => exact h
        | _ :: _, h => exact h.1
      exact headOk_render hu (by cases h : isWord u <;> simp_all) ts
    obtain ⟨i', tok, hs, he⟩ := lex_tok ht hr i acc
    obtain ⟨arr, h1, h2⟩ := lex_render (u :: ts) hrest i' (acc.push tok)
    refine ⟨arr, ?_, ?_⟩
    · rw [render_cons, he, h1]
    · rw [h2]; simp [hs]

/-! ## The fragment's tokens are well formed -/

theorem digits_int (n : Nat) : (toString (n : Int)).toList = Nat.toDigits 10 n := by
  rw [show toString (n : Int) = toString n from rfl, Nat.toString_eq_ofList_toDigits, String.toList_ofList]

theorem lexable_cons_op {o : T} (ho : TokOk o) (hw : isWord o = false) :
    ∀ {ys : List T}, Lexable ys → Lexable (o :: ys)
  | [], _ => ho
  | _ :: _, h => ⟨ho, by simp [hw], h⟩

theorem lexable_append_op {o : T} {ys : List T} (hw : isWord o = false) (hy : Lexable (o :: ys)) :
    ∀ {xs : List T}, Lexable xs → Lexable (xs ++ o :: ys)
  | [], _ => hy
  | [t], ht => ⟨ht, by simp [hw], hy⟩
  | t :: u :: ts, ⟨ht, hn, hrest⟩ => ⟨ht, hn, lexable_append_op hw hy hrest⟩

theorem tokOk_op {c : Char} (hc : c ∈ opChars) : TokOk (.op, String.singleton c) := ⟨c, hc, rfl⟩

theorem tokOk_lp : TokOk (.op, "(") := tokOk_op (c := '(') (by decide)
theorem tokOk_rp : TokOk (.op, ")") := tokOk_op (c := ')') (by decide)
theorem tokOk_plus : TokOk (.op, "+") := tokOk_op (c := '+') (by decide)
theorem tokOk_star : TokOk (.op, "*") := tokOk_op (c := '*') (by decide)
theorem tokOk_hat : TokOk (.op, "^") := tokOk_op (c := '^') (by decide)

theorem lexable_rp : Lexable [((.op, ")") : T)] := tokOk_rp

theorem lexable_paren (b : Bool) {ts : List T} (h : Lexable ts) : Lexable (paren b ts) := by
  cases b
  · exact h
  · exact lexable_cons_op tokOk_lp rfl (lexable_append_op rfl lexable_rp h)

theorem lexable_rawTail {sep : String} (hs : TokOk (.op, sep)) {as : List Expr}
    (h : ∀ c ∈ as, ∀ ctx, Lexable (ptoks c ctx)) : Lexable (rawTail sep as) := by
  induction as with
  | nil => trivial
  | cons a as ih =>
    have ha := h a (by simp) 2
    have ih := ih (fun c hc => h c (by simp [hc]))
    simp only [rawTail]
    apply lexable_cons_op hs rfl
    cases as with
    | nil => simpa [rawTail, ptoks] using ha
    | cons b bs => simp only [rawTail]; exact lexable_append_op rfl (by simpa [rawTail] using ih) (by simpa [ptoks] using ha)

theorem isIdent_unary {f : String} (hf : f ∈ unaryNames) : isIdent f = true := by
  simp only [unaryNames, List.mem_cons, List.mem_nil_iff, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [isIdent, lex.isIdStart, lex.isIdChar, lex.isGreek]

theorem lexable_plain {e : Expr} (h : Plain e) : ∀ ctx, Lexable (ptoks e ctx) := by
  induction h with
  | num n =>
    intro ctx
    apply lexable_paren
    refine ⟨?_, ?_⟩ <;> simp only [ofInt_num, digits_int]
    · exact Nat.toDigits_ne_nil
    · exact fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  | var x hx _ => intro ctx; exact lexable_paren _ hx
  | fn f a hf _ iha =>
    intro ctx
    apply lexable_paren
    exact ⟨isIdent_unary hf, by simp [isWord],
      lexable_cons_op tokOk_lp rfl (lexable_append_op rfl lexable_rp (iha 1))⟩
  | pow b x _ _ ihb ihx =>
    intro ctx
    exact lexable_paren _ (lexable_append_op rfl (lexable_cons_op tokOk_hat rfl (ihx 3)) (ihb 4))
  | add a b as _ _ _ iha ihb ihas =>
    intro ctx
    apply lexable_paren
    simp only [raw]
    have := lexable_rawTail tokOk_plus (as := b :: as) (by
      intro c hc; simp at hc; rcases hc with rfl | hc
      · exact ihb
      · exact ihas c hc)
    simp only [rawTail] at this ⊢
    exact lexable_append_op rfl this (iha 1)
  | mul a b as _ _ _ iha ihb ihas =>
    intro ctx
    apply lexable_paren
    simp only [raw]
    have := lexable_rawTail tokOk_star (as := b :: as) (by
      intro c hc; simp at hc; rcases hc with rfl | hc
      · exact ihb
      · exact ihas c hc)
    simp only [rawTail] at this ⊢
    exact lexable_append_op rfl this (iha 2)

/-! ## What the parser does on the fragment's tokens

Each lemma below is one path through one parsing function, stated by its outcome: what it returns
and where it stops. -/

@[scoped simp] theorem except_pure {ε α} (x : α) : (pure x : Except ε α) = .ok x := rfl
@[scoped simp] theorem except_bind_ok {ε α β} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl
@[scoped simp] theorem except_map_ok {ε α β} (a : α) (f : α → β) : (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

theorem isOp_strip {t : Tok} {k : TokKind} {x : String} (h : strip t = (k, x)) (s : String) :
    isOp t s = (k == .op && x == s) := by
  simp only [strip, Prod.mk.injEq] at h
  simp [isOp, h.1, h.2]

/-- What may follow an expression: the end, or the `)` that closes it. -/
def FollowE (c : PCtx) (j : Nat) : Prop := (c.tok j).kind = .eof ∨ strip (c.tok j) = (.op, ")")
/-- What may follow a term: that, or a `+`. -/
def FollowT (c : PCtx) (j : Nat) : Prop := FollowE c j ∨ strip (c.tok j) = (.op, "+")
/-- What may follow a factor: that, or a `*`. -/
def FollowU (c : PCtx) (j : Nat) : Prop := FollowT c j ∨ strip (c.tok j) = (.op, "*")

theorem FollowE.T {c : PCtx} {j : Nat} (h : FollowE c j) : FollowT c j := .inl h
theorem FollowT.U {c : PCtx} {j : Nat} (h : FollowT c j) : FollowU c j := .inl h

/-- None of what may follow a factor is an operator that would continue it. -/
theorem followU_isOp {c : PCtx} {j : Nat} (h : FollowU c j) {s : String}
    (hs : s ≠ "+" ∧ s ≠ "*" ∧ s ≠ ")") : isOp (c.tok j) s = false := by
  rcases h with ((h | h) | h) | h
  · simp [isOp, h]
  all_goals rw [isOp_strip h]; simp; intro e; subst e; simp at hs

theorem followT_isOp {c : PCtx} {j : Nat} (h : FollowT c j) {s : String}
    (hs : s ≠ "+" ∧ s ≠ ")") : isOp (c.tok j) s = false := by
  rcases h with (h | h) | h
  · simp [isOp, h]
  all_goals rw [isOp_strip h]; simp; intro e; subst e; simp at hs

theorem followE_isOp {c : PCtx} {j : Nat} (h : FollowE c j) {s : String}
    (hs : s ≠ ")") : isOp (c.tok j) s = false := by
  rcases h with h | h
  · simp [isOp, h]
  · rw [isOp_strip h]; simp; intro e; subst e; simp at hs

theorem followU_not_atom {c : PCtx} {j : Nat} (h : FollowU c j) : startsAtom (c.tok j) = false := by
  rcases h with ((h | h) | h) | h
  · simp [startsAtom, isOp, h]
  all_goals
    simp only [strip, Prod.mk.injEq] at h
    simp [startsAtom, isOp, h.1, h.2]

theorem part_stop (c : PCtx) (e : Expr) (i : Nat) (hi : i ≤ c.toks.size) (h : isOp (c.tok i) "[" = false) :
    part c e i hi = .ok (e, ⟨i, Nat.le_refl _, hi⟩) := by
  rw [part]; simp [h]

theorem exprLoop_stop (c : PCtx) (lhs : Expr) (j : Nat) (hj : j ≤ c.toks.size) (h : FollowE c j) :
    exprLoop c lhs j hj = .ok (lhs, ⟨j, Nat.le_refl _, hj⟩) := by
  rw [exprLoop]
  simp [followE_isOp h (s := "+") (by decide), followE_isOp h (s := "-") (by decide)]

theorem exprLoop_plus (c : PCtx) (lhs : Expr) (j : Nat) (hj : j ≤ c.toks.size)
    (h1 : strip (c.tok j) = (.op, "+")) {rhs : Expr} {k : Nat} {hk}
    (ht : term c (j + 1) = .ok (rhs, ⟨k, hk⟩)) {e : Expr} {m : Nat} {hm}
    (hl : exprLoop c (.add [lhs, rhs]) k hk.2 = .ok (e, ⟨m, hm⟩)) :
    ∃ h, exprLoop c lhs j hj = .ok (e, ⟨m, h⟩) := by
  rw [exprLoop]; simp [isOp_strip h1, ht, hl]; omega

theorem termLoop_stop (c : PCtx) (lhs : Expr) (j : Nat) (hj : j ≤ c.toks.size) (h : FollowT c j) :
    termLoop c lhs j hj = .ok (lhs, ⟨j, Nat.le_refl _, hj⟩) := by
  rw [termLoop]
  simp [followT_isOp h (s := "*") (by decide), followT_isOp h (s := "./") (by decide),
    followT_isOp h (s := ".*") (by decide), followT_isOp h (s := "/") (by decide), followU_not_atom h.U]

theorem termLoop_star (c : PCtx) (lhs : Expr) (j : Nat) (hj : j ≤ c.toks.size)
    (h1 : strip (c.tok j) = (.op, "*")) {rhs : Expr} {k : Nat} {hk}
    (ht : unary c (j + 1) = .ok (rhs, ⟨k, hk⟩)) {e : Expr} {m : Nat} {hm}
    (hl : termLoop c (.mul [lhs, rhs]) k hk.2 = .ok (e, ⟨m, hm⟩)) :
    ∃ h, termLoop c lhs j hj = .ok (e, ⟨m, h⟩) := by
  rw [termLoop]; simp [isOp_strip h1, ht, hl]; omega

theorem expr_spec (c : PCtx) (i : Nat) {a : Expr} {j : Nat} {hj} (ht : term c i = .ok (a, ⟨j, hj⟩))
    {e : Expr} {k : Nat} {hk} (hl : exprLoop c a j hj.2 = .ok (e, ⟨k, hk⟩)) :
    ∃ h, expr c i = .ok (e, ⟨k, h⟩) := by
  rw [expr]; simp [ht, hl]; omega

theorem term_spec (c : PCtx) (i : Nat) {a : Expr} {j : Nat} {hj} (hu : unary c i = .ok (a, ⟨j, hj⟩))
    {e : Expr} {k : Nat} {hk} (hl : termLoop c a j hj.2 = .ok (e, ⟨k, hk⟩)) :
    ∃ h, term c i = .ok (e, ⟨k, h⟩) := by
  rw [term]; simp [hu, hl]; omega

theorem unary_power (c : PCtx) (i : Nat) (h : isOp (c.tok i) "-" = false) : unary c i = power c i := by
  rw [unary]; simp [h]

theorem power_atom (c : PCtx) (i : Nat) {a : Expr} {j : Nat} {hj} (ha : atom c i = .ok (a, ⟨j, hj⟩))
    (h1 : isOp (c.tok j) "[" = false) (h2 : isOp (c.tok j) "^" = false) :
    power c i = .ok (a, ⟨j, hj⟩) := by
  rw [power]; simp [ha, part_stop c a j hj.2 h1, h2]

theorem power_pow (c : PCtx) (i : Nat) {a : Expr} {j : Nat} {hj} (ha : atom c i = .ok (a, ⟨j, hj⟩))
    (h1 : strip (c.tok j) = (.op, "^")) {x : Expr} {k : Nat} {hk} (hx : unary c (j + 1) = .ok (x, ⟨k, hk⟩)) :
    ∃ h, power c i = .ok (.pow a x, ⟨k, h⟩) := by
  rw [power]
  simp [ha, part_stop c a j hj.2 (by rw [isOp_strip h1]; decide), isOp_strip h1, hx]
  omega

theorem atom_num (c : PCtx) (i : Nat) (hk : (c.tok i).kind = .num) {q : Q} (hq : Q.parse (c.tok i).s = some q) :
    ∃ h, atom c i = .ok (.num q, ⟨i + 1, h⟩) := by
  have := PCtx.lt_of_kind (c := c) (i := i) (by simp [hk])
  rw [atom]
  split <;> simp_all
  omega

theorem atom_var (c : PCtx) (i : Nat) (hk : (c.tok i).kind = .id) (hc : c.known = [])
    (hx : (c.tok i).s ∉ reserved) : ∃ h, atom c i = .ok (.var (c.tok i).s, ⟨i + 1, h⟩) := by
  have hp : powerFunctions.contains (c.tok i).s = false := by
    simp only [reserved, builtinFunctions, List.mem_cons, not_or] at hx
    simp [powerFunctions, hx]
  have hb : builtinFunctions.contains (c.tok i).s = false := by
    simp only [reserved, List.mem_cons, not_or] at hx
    simpa using hx.2.2.2.2.2
  simp only [reserved, List.mem_cons, not_or] at hx
  have := PCtx.lt_of_kind (c := c) (i := i) (by simp [hk])
  rw [atom]
  split <;> simp_all
  omega

theorem exprList_stop (c : PCtx) (acc : List Expr) (k : Nat) (hk : k ≤ c.toks.size)
    (h : strip (c.tok k) = (.op, ")")) : exprList c acc k hk = .ok (acc, ⟨k, Nat.le_refl _, hk⟩) := by
  rw [exprList]; simp [isOp_strip h]

theorem expectAt_ok (c : PCtx) (s : String) (k : Nat) (h : strip (c.tok k) = (.op, s)) :
    ∃ p, expectAt c s k = .ok p :=
  ⟨⟨PCtx.lt_of_isOp (s := s) (by rw [isOp_strip h]; simp)⟩, by unfold expectAt; simp [isOp_strip h]⟩

theorem callArgs_one (c : PCtx) (i : Nat) (h0 : isOp (c.tok i) ")" = false) {e : Expr} {j : Nat} {hj}
    (he : expr c i = .ok (e, ⟨j, hj⟩)) (hr : strip (c.tok j) = (.op, ")")) :
    ∃ h, callArgs c i = .ok ([e], ⟨j + 1, h⟩) := by
  obtain ⟨p, hp⟩ := expectAt_ok c ")" j hr
  rw [callArgs]; simp [h0, he, exprList_stop c [e] j hj.2 hr, hp]
  have := p.down; omega

theorem atom_call (c : PCtx) (i : Nat) (hk : (c.tok i).kind = .id) {f : String} (hf : f ∈ unaryNames)
    (hs : (c.tok i).s = f) (hlp : strip (c.tok (i + 1)) = (.op, "(")) {args : List Expr} {j : Nat} {hj}
    (ha : callArgs c (i + 2) = .ok (args, ⟨j, hj⟩)) : ∃ h, atom c i = .ok (mkCall f args, ⟨j, h⟩) := by
  have hb : builtinFunctions.contains f = true := by
    simp only [unaryNames, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hpow : isOp (c.tok (i + 1 + 0)) "^" = false := by simp [isOp_strip hlp]
  have hlp' := isOp_strip hlp "("
  simp at hlp'
  rw [atom]
  split <;> simp_all
  omega

theorem atom_paren (c : PCtx) (i : Nat) (h0 : strip (c.tok i) = (.op, "(")) {e : Expr} {j : Nat} {hj}
    (he : expr c (i + 1) = .ok (e, ⟨j, hj⟩)) (hr : strip (c.tok j) = (.op, ")")) :
    ∃ h, atom c i = .ok (e, ⟨j + 1, h⟩) := by
  obtain ⟨p, hp⟩ := expectAt_ok c ")" j hr
  simp only [strip, Prod.mk.injEq] at h0
  have := p.down
  rw [atom]
  split <;> simp_all
  omega

/-! ## Numerals read back -/

theorem splitOn_digits {l : List Char} (hd : ∀ c ∈ l, c.isDigit = true) {sep : Char}
    (hs : sep.isDigit = false) : l.splitOn sep = [l] := by
  unfold List.splitOn
  apply List.splitOnP_eq_singleton
  intro x hx
  have := hd x hx
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro e; subst e; simp_all

theorem parse_digits (n : Nat) : Q.parse (toString (n : Int)) = some (Q.ofInt n) := by
  have hd : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true :=
    fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have hne : Nat.toDigits 10 n ≠ [] := Nat.toDigits_ne_nil
  unfold Q.parse
  rw [digits_int, splitOn_digits hd (by decide), splitOn_digits hd (by decide)]
  have : (Nat.toDigits 10 n).isEmpty = false := by cases h : Nat.toDigits 10 n <;> simp_all
  simp [this, List.all_eq_true.2 hd, Nat.ofDigitChars_ten_toDigits]

/-! ## The token array spells the tokens -/

/-- From position `i`, the parser's tokens are `ts`, kind and text. -/
def Matches (c : PCtx) (i : Nat) (ts : List T) : Prop :=
  ∀ k (hk : k < ts.length), strip (c.tok (i + k)) = ts[k]

theorem matches_nil (c : PCtx) (i : Nat) : Matches c i [] := fun _ hk => absurd hk (by simp)

theorem matches_cons {c : PCtx} {i : Nat} {t : T} {ts : List T} :
    Matches c i (t :: ts) ↔ strip (c.tok i) = t ∧ Matches c (i + 1) ts := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun k hk => ?_⟩
    have := h (k + 1) (by simp; omega)
    simpa [Nat.add_assoc, Nat.add_comm 1 k] using this
  · rintro ⟨h0, h⟩ k hk
    cases k with
    | zero => simpa using h0
    | succ k =>
      have := h k (by simp at hk; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem matches_append {c : PCtx} {i : Nat} {xs ys : List T} :
    Matches c i (xs ++ ys) ↔ Matches c i xs ∧ Matches c (i + xs.length) ys := by
  induction xs generalizing i with
  | nil => simp [matches_nil]
  | cons t xs ih =>
    simp only [List.cons_append, matches_cons, ih, List.length_cons]
    rw [show i + 1 + xs.length = i + (xs.length + 1) by omega]
    exact ⟨fun ⟨a, b, d⟩ => ⟨⟨a, b⟩, d⟩, fun ⟨⟨a, b⟩, d⟩ => ⟨a, b, d⟩⟩

/-! ## Products and sums, as the parser builds them

The parser reads `a*b*c` as `(a*b)*c` and `a + b + c` as `(a + b) + c`; the printer writes a product
in a product, wherever it is, and a sum first in a sum, without parentheses. So a product's tokens are
its `units` joined by `*`, and a sum's its `summands` joined by `+`, and the parser builds the left
fold of each. `flat` takes both to the same term. -/

mutual
  /-- The factors of a product, with products in it spliced in. -/
  def units : Expr → List Expr
    | .mul es => unitsList es
    | e => [e]
  def unitsList : List Expr → List Expr
    | [] => []
    | e :: es => units e ++ unitsList es
end

/-- The terms of a sum, with a sum first in it spliced in. -/
def summands : Expr → List Expr
  | .add (a :: as) => summands a ++ as
  | e => [e]

/-- What a term contributes to a flattened product, or to a flattened sum. -/
def mp (x : Expr) : List Expr := match flat x with | .mul as => as | y => [y]
def ap (x : Expr) : List Expr := match flat x with | .add as => as | y => [y]

def foldMul (l : Expr) (us : List Expr) : Expr := us.foldl (fun acc u => .mul [acc, u]) l
def foldAdd (l : Expr) (ss : List Expr) : Expr := ss.foldl (fun acc s => .add [acc, s]) l

theorem flatMul_eq (l : List Expr) : flatMul l = l.flatMap mp := by
  induction l with
  | nil => simp [flatMul]
  | cons e es ih => simp [flatMul, ih, mp]

theorem flatAdd_eq (l : List Expr) : flatAdd l = l.flatMap ap := by
  induction l with
  | nil => simp [flatAdd]
  | cons e es ih => simp [flatAdd, ih, ap]

theorem flat_mul2 (a b : Expr) : flat (.mul [a, b]) = .mul (mp a ++ mp b) := by
  simp [flat, flatMul_eq]

theorem flat_add2 (a b : Expr) : flat (.add [a, b]) = .add (ap a ++ ap b) := by
  simp [flat, flatAdd_eq]

theorem mp_congr {a b : Expr} (h : flat a = flat b) : mp a = mp b := by simp [mp, h]
theorem ap_congr {a b : Expr} (h : flat a = flat b) : ap a = ap b := by simp [ap, h]

theorem flat_foldMul_congr {x y : Expr} (h : flat x = flat y) :
    ∀ us : List Expr, flat (foldMul x us) = flat (foldMul y us)
  | [] => h
  | u :: us => by
    simp only [foldMul, List.foldl_cons]
    exact flat_foldMul_congr (by rw [flat_mul2, flat_mul2, mp_congr h]) us

theorem flat_foldAdd_congr {x y : Expr} (h : flat x = flat y) :
    ∀ ss : List Expr, flat (foldAdd x ss) = flat (foldAdd y ss)
  | [] => h
  | s :: ss => by
    simp only [foldAdd, List.foldl_cons]
    exact flat_foldAdd_congr (by rw [flat_add2, flat_add2, ap_congr h]) ss

theorem flat_foldMul (l : Expr) : ∀ (us : List Expr), us ≠ [] → flat (foldMul l us) = .mul (mp l ++ us.flatMap mp)
  | [u], _ => by simp [foldMul, flat_mul2]
  | u :: v :: us, _ => by
    have := flat_foldMul (.mul [l, u]) (v :: us) (by simp)
    simp only [foldMul, List.foldl_cons] at this ⊢
    rw [this]
    have hm : mp (.mul [l, u]) = mp l ++ mp u := by simp [mp, flat_mul2]
    simp [hm]

theorem flat_foldAdd (l : Expr) : ∀ (ss : List Expr), ss ≠ [] → flat (foldAdd l ss) = .add (ap l ++ ss.flatMap ap)
  | [s], _ => by simp [foldAdd, flat_add2]
  | s :: t :: ss, _ => by
    have := flat_foldAdd (.add [l, s]) (t :: ss) (by simp)
    simp only [foldAdd, List.foldl_cons] at this ⊢
    rw [this]
    have ha : ap (.add [l, s]) = ap l ++ ap s := by simp [ap, flat_add2]
    simp [ha]

theorem units_ne_nil {e : Expr} (h : Plain e) : units e ≠ [] := by
  cases h with
  | mul a b as ha =>
    have := units_ne_nil ha
    simp [units, unitsList]; intro h'; exact absurd h' this
  | _ => simp [units]

theorem summands_ne_nil {e : Expr} (h : Plain e) : summands e ≠ [] := by
  cases h with
  | add a b as ha => simp [summands]
  | _ => simp [summands]

theorem mp_units {e : Expr} (h : Plain e) : mp e = (units e).flatMap mp := by
  induction h with
  | mul a b as ha hb has iha ihb ihas =>
    have hl : ∀ l : List Expr, (∀ c ∈ l, mp c = (units c).flatMap mp) → l.flatMap mp = (unitsList l).flatMap mp := by
      intro l hl
      induction l with
      | nil => simp [unitsList]
      | cons x xs ih =>
        simp only [List.flatMap_cons, unitsList, List.flatMap_append]
        rw [hl x (by simp), ih (fun c hc => hl c (by simp [hc]))]
    have := hl (a :: b :: as) (by
      intro c hc; simp at hc; rcases hc with rfl | rfl | hc
      · exact iha
      · exact ihb
      · exact ihas c hc)
    simp only [units]
    rw [← this]
    simp [mp, flat, flatMul_eq]
  | _ => simp [units]

theorem ap_summands {e : Expr} (h : Plain e) : ap e = (summands e).flatMap ap := by
  induction h with
  | add a b as ha hb has iha ihb ihas =>
    simp only [summands, List.flatMap_append, ← iha]
    simp [ap, flat, flatAdd_eq]
  | _ => simp [summands]

/-- A product's left fold over its units flattens to it. -/
theorem flat_foldMul_units {e : Expr} (h : Plain e) {u : Expr} {us : List Expr} (hu : units e = u :: us) :
    flat (foldMul u us) = flat e := by
  cases h with
  | mul a b as ha hb has =>
    have hus : us ≠ [] := by
      intro e'; subst e'
      have h1 := units_ne_nil ha
      have h2 := units_ne_nil hb
      simp only [units, unitsList] at hu
      cases h3 : units a with
      | nil => exact h1 h3
      | cons x xs =>
        rw [h3] at hu; simp at hu
        cases h4 : units b with
        | nil => exact h2 h4
        | cons y ys => rw [h4] at hu; simp at hu
    rw [flat_foldMul u us hus]
    have := mp_units (Plain.mul a b as ha hb has)
    rw [hu] at this
    simp only [List.flatMap_cons] at this
    rw [← this]
    simp [mp, flat]
  | _ => simp [units] at hu; obtain ⟨rfl, rfl⟩ := hu; rfl

/-- A sum's left fold over its summands flattens to it. -/
theorem flat_foldAdd_summands {e : Expr} (h : Plain e) {s : Expr} {ss : List Expr} (hs : summands e = s :: ss) :
    flat (foldAdd s ss) = flat e := by
  cases h with
  | add a b as ha hb has =>
    have hss : ss ≠ [] := by
      intro e'; subst e'
      simp only [summands] at hs
      cases h3 : summands a with
      | nil => exact summands_ne_nil ha h3
      | cons x xs => rw [h3] at hs; simp at hs
    rw [flat_foldAdd s ss hss]
    have := ap_summands (Plain.add a b as ha hb has)
    rw [hs] at this
    simp only [List.flatMap_cons] at this
    rw [← this]
    simp [ap, flat]
  | _ => simp [summands] at hs; obtain ⟨rfl, rfl⟩ := hs; rfl

def starTail (us : List Expr) : List T := us.flatMap (fun u => (.op, "*") :: ptoks u 3)
def plusTail (ss : List Expr) : List T := ss.flatMap (fun s => (.op, "+") :: ptoks s 2)

theorem ptoks_units {e : Expr} (h : Plain e) : ∀ {u : Expr} {us : List Expr}, units e = u :: us →
    ptoks e 2 = ptoks u 3 ++ starTail us := by
  induction h with
  | mul a b as ha hb has iha ihb ihas =>
    intro u us hu
    have hl : ∀ l : List Expr, (∀ c ∈ l, Plain c ∧ ∀ {u us}, units c = u :: us → ptoks c 2 = ptoks u 3 ++ starTail us) →
        rawTail "*" l = starTail (unitsList l) := by
      intro l hl
      induction l with
      | nil => simp [rawTail, unitsList, starTail]
      | cons x xs ih =>
        obtain ⟨hx, hxt⟩ := hl x (by simp)
        obtain ⟨v, vs, hv⟩ : ∃ v vs, units x = v :: vs := List.exists_cons_of_ne_nil (units_ne_nil hx)
        simp only [rawTail, unitsList, hv, List.cons_append]
        rw [ih (fun c hc => hl c (by simp [hc]))]
        have := hxt hv
        simp only [ptoks] at this
        simp [this, starTail, ptoks]
    obtain ⟨v, vs, hv⟩ : ∃ v vs, units a = v :: vs := List.exists_cons_of_ne_nil (units_ne_nil ha)
    have ht := hl (b :: as) (by
      intro c hc; simp at hc; rcases hc with rfl | hc
      · exact ⟨hb, ihb⟩
      · exact ⟨has c hc, ihas c hc⟩)
    simp only [units, unitsList, hv, List.cons_append, List.cons.injEq] at hu
    obtain ⟨rfl, rfl⟩ := hu
    have ha2 := iha hv
    simp only [ptoks] at ha2
    simp only [ptoks, precOf_mul, raw]
    rw [ht]
    simp [ha2, starTail, unitsList]
  | _ => intro u us hu; simp [units] at hu; obtain ⟨rfl, rfl⟩ := hu; simp [ptoks, precOf, starTail]

theorem ptoks_summands {e : Expr} (h : Plain e) : ∀ {s : Expr} {ss : List Expr}, summands e = s :: ss →
    ptoks e 1 = ptoks s 2 ++ plusTail ss := by
  induction h with
  | add a b as ha hb has iha _ _ =>
    intro s ss hs
    obtain ⟨v, vs, hv⟩ : ∃ v vs, summands a = v :: vs := List.exists_cons_of_ne_nil (summands_ne_nil ha)
    simp only [summands, hv, List.cons_append, List.cons.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have ha1 := iha hv
    have hr : ∀ l : List Expr, rawTail "+" l = plusTail l := by
      intro l; induction l with
      | nil => simp [rawTail, plusTail]
      | cons x xs ih => simp [rawTail, plusTail, ih, ptoks]
    simp only [ptoks] at ha1
    simp only [ptoks, precOf_add, raw]
    rw [ha1]
    simp [hr, plusTail]
  | _ => intro s ss hs; simp [summands] at hs; obtain ⟨rfl, rfl⟩ := hs; simp [ptoks, precOf, plusTail]

/-- A term's first token is neither an operator that a parser would take for something else, nor
the `let` of a definition. -/
def GoodHead (t : T) : Prop := t ≠ (.op, "-") ∧ t ≠ (.op, ")") ∧ t ≠ (.id, "let")

theorem head_paren (b : Bool) {t : T} {ts : List T} (ht : GoodHead t) :
    ∃ t' ts', paren b (t :: ts) = t' :: ts' ∧ GoodHead t' := by
  cases b
  · exact ⟨t, ts, rfl, ht⟩
  · exact ⟨_, _, rfl, by simp [GoodHead]⟩

theorem ptoks_head {e : Expr} (h : Plain e) : ∀ ctx, ∃ t ts, ptoks e ctx = t :: ts ∧ GoodHead t := by
  induction h with
  | num n => intro ctx; exact head_paren _ (by simp [GoodHead])
  | var x _ hx =>
    intro ctx
    exact head_paren _ (by simp [GoodHead]; intro e; subst e; simp [reserved] at hx)
  | fn f a hf _ _ =>
    intro ctx
    exact head_paren _ (by
      simp [GoodHead]; intro e; subst e; simp [unaryNames] at hf)
  | pow b x _ _ ihb _ =>
    intro ctx
    obtain ⟨t, ts, h1, h2⟩ := ihb 4
    simp only [ptoks, raw] at h1 ⊢
    rw [h1]
    exact head_paren _ h2
  | add a b as _ _ _ iha _ _ =>
    intro ctx
    obtain ⟨t, ts, h1, h2⟩ := iha 1
    simp only [ptoks, raw] at h1 ⊢
    rw [h1]
    exact head_paren _ h2
  | mul a b as _ _ _ iha _ _ =>
    intro ctx
    obtain ⟨t, ts, h1, h2⟩ := iha 2
    simp only [ptoks, raw] at h1 ⊢
    rw [h1]
    exact head_paren _ h2

/-! ## The parser reads the fragment's tokens back

Four statements, one per level of the grammar: from a position where the tokens of `e` start, in
the context of that level, and followed by a token the level stops at, the level's function reads a
term that flattens to `e` and stops right after those tokens. -/

def ALem (e : Expr) : Prop := ∀ (c : PCtx) (i : Nat), c.known = [] → Matches c i (ptoks e 4) →
  ∃ e' m h, atom c i = .ok (e', ⟨m, h⟩) ∧ m = i + (ptoks e 4).length ∧ flat e' = flat e
def ULem (e : Expr) : Prop := ∀ (c : PCtx) (i : Nat), c.known = [] → Matches c i (ptoks e 3) →
  FollowU c (i + (ptoks e 3).length) →
  ∃ e' m h, unary c i = .ok (e', ⟨m, h⟩) ∧ m = i + (ptoks e 3).length ∧ flat e' = flat e
def TLem (e : Expr) : Prop := ∀ (c : PCtx) (i : Nat), c.known = [] → Matches c i (ptoks e 2) →
  FollowT c (i + (ptoks e 2).length) →
  ∃ e' m h, term c i = .ok (e', ⟨m, h⟩) ∧ m = i + (ptoks e 2).length ∧ flat e' = flat e
def ELem (e : Expr) : Prop := ∀ (c : PCtx) (i : Nat), c.known = [] → Matches c i (ptoks e 1) →
  FollowE c (i + (ptoks e 1).length) →
  ∃ e' m h, expr c i = .ok (e', ⟨m, h⟩) ∧ m = i + (ptoks e 1).length ∧ flat e' = flat e

theorem isOp_false_of_ne {t : Tok} {s : String} (h : strip t ≠ (.op, s)) : isOp t s = false := by
  simp only [strip, ne_eq, Prod.mk.injEq] at h
  simp only [isOp, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  by_cases hk : t.kind = .op
  · exact .inr (fun hs => h ⟨hk, hs⟩)
  · exact .inl hk

theorem head_isOp {e : Expr} (h : Plain e) {c : PCtx} {i : Nat} {ctx : Nat} (hm : Matches c i (ptoks e ctx)) :
    isOp (c.tok i) "-" = false ∧ isOp (c.tok i) ")" = false ∧ ¬((c.tok i).kind = .id ∧ (c.tok i).s = "let") := by
  obtain ⟨t, ts, ht, hg⟩ := ptoks_head h ctx
  rw [ht, matches_cons] at hm
  have h0 := hm.1
  obtain ⟨g1, g2, g3⟩ := hg
  subst h0
  refine ⟨isOp_false_of_ne g1, isOp_false_of_ne g2, ?_⟩
  intro hc; apply g3; simp [strip, hc]

theorem ptoks_three_four {e : Expr} (h3 : precOf e ≠ 3) : ptoks e 3 = ptoks e 4 := by
  simp only [ptoks]
  have : precOf e ≤ 4 := by unfold precOf; split <;> omega
  congr 1
  simp; omega

theorem ptoks_two_three {e : Expr} (h2 : precOf e ≠ 2) : ptoks e 2 = ptoks e 3 := by
  simp only [ptoks]
  have : precOf e ≤ 4 := by unfold precOf; split <;> omega
  have : 1 ≤ precOf e := by unfold precOf; split <;> omega
  congr 1
  simp; omega

theorem ptoks_one_two {e : Expr} (h1 : precOf e ≠ 1) : ptoks e 1 = ptoks e 2 := by
  simp only [ptoks]
  have : 1 ≤ precOf e := by unfold precOf; split <;> omega
  congr 1
  simp; omega

/-- G1: a factor that is not a power is read by `atom`, and nothing after it continues it. -/
theorem ulem_of_alem {e : Expr} (h : Plain e) (hA : ALem e) (h3 : precOf e ≠ 3) : ULem e := by
  intro c i hc hm hf
  rw [ptoks_three_four h3] at hm hf ⊢
  obtain ⟨e', m, hm', ha, rfl, hfl⟩ := hA c i hc hm
  refine ⟨e', _, hm', ?_, rfl, hfl⟩
  rw [unary_power c i (head_isOp h hm).1]
  exact power_atom c i ha (followU_isOp hf (by decide)) (followU_isOp hf (by decide))

/-- `* u * v …`: `termLoop` reads the factors, building the left fold. -/
theorem termLoop_units : ∀ (us : List Expr), (∀ u ∈ us, ULem u) →
    ∀ (c : PCtx) (j : Nat) (hj : j ≤ c.toks.size) (lhs : Expr), c.known = [] → Matches c j (starTail us) →
    FollowT c (j + (starTail us).length) →
    ∃ r m h, termLoop c lhs j hj = .ok (r, ⟨m, h⟩) ∧ m = j + (starTail us).length ∧ flat r = flat (foldMul lhs us)
  | [], _, c, j, hj, lhs, _, _, hf => by
    simp only [starTail, List.flatMap_nil, List.length_nil, Nat.add_zero] at hf ⊢
    exact ⟨lhs, j, ⟨Nat.le_refl _, hj⟩, termLoop_stop c lhs j hj hf, rfl, rfl⟩
  | u :: us, hU, c, j, hj, lhs, hc, hm, hf => by
    have hst : starTail (u :: us) = (.op, "*") :: (ptoks u 3 ++ starTail us) := by simp [starTail]
    rw [hst, matches_cons, matches_append] at hm
    obtain ⟨h0, hmu, hmus⟩ := hm
    rw [hst] at hf
    simp only [List.length_cons, List.length_append] at hf
    have hfu : FollowU c (j + 1 + (ptoks u 3).length) := by
      cases us with
      | nil => simp [starTail] at hf ⊢; exact .inl (by rw [show j + 1 + (ptoks u 3).length = j + ((ptoks u 3).length + 1) by omega]; exact hf)
      | cons v vs =>
        have : starTail (v :: vs) = (.op, "*") :: (ptoks v 3 ++ starTail vs) := by simp [starTail]
        rw [this, matches_cons] at hmus
        exact .inr hmus.1
    obtain ⟨u', k, hk, hu, rfl, hfl⟩ := hU u (by simp) c (j + 1) hc hmu hfu
    obtain ⟨r, m, hm', hl, rfl, hfr⟩ := termLoop_units us (fun v hv => hU v (by simp [hv])) c _ hk.2
      (.mul [lhs, u']) hc hmus (by rw [show j + 1 + (ptoks u 3).length + (starTail us).length =
        j + ((ptoks u 3).length + (starTail us).length + 1) by omega]; exact hf)
    obtain ⟨h', hres⟩ := termLoop_star c lhs j hj h0 hu hl
    refine ⟨r, _, h', hres, by rw [hst]; simp; omega, ?_⟩
    rw [hfr]
    simp only [foldMul, List.foldl_cons]
    exact flat_foldMul_congr (by rw [flat_mul2, flat_mul2, mp_congr hfl]) us

/-- `+ s + t …`: `exprLoop` reads the terms, building the left fold. -/
theorem exprLoop_summands : ∀ (ss : List Expr), (∀ s ∈ ss, TLem s) →
    ∀ (c : PCtx) (j : Nat) (hj : j ≤ c.toks.size) (lhs : Expr), c.known = [] → Matches c j (plusTail ss) →
    FollowE c (j + (plusTail ss).length) →
    ∃ r m h, exprLoop c lhs j hj = .ok (r, ⟨m, h⟩) ∧ m = j + (plusTail ss).length ∧ flat r = flat (foldAdd lhs ss)
  | [], _, c, j, hj, lhs, _, _, hf => by
    simp only [plusTail, List.flatMap_nil, List.length_nil, Nat.add_zero] at hf ⊢
    exact ⟨lhs, j, ⟨Nat.le_refl _, hj⟩, exprLoop_stop c lhs j hj hf, rfl, rfl⟩
  | s :: ss, hT, c, j, hj, lhs, hc, hm, hf => by
    have hst : plusTail (s :: ss) = (.op, "+") :: (ptoks s 2 ++ plusTail ss) := by simp [plusTail]
    rw [hst, matches_cons, matches_append] at hm
    obtain ⟨h0, hms, hmss⟩ := hm
    rw [hst] at hf
    simp only [List.length_cons, List.length_append] at hf
    have hft : FollowT c (j + 1 + (ptoks s 2).length) := by
      cases ss with
      | nil => simp [plusTail] at hf ⊢; exact .inl (by rw [show j + 1 + (ptoks s 2).length = j + ((ptoks s 2).length + 1) by omega]; exact hf)
      | cons v vs =>
        have : plusTail (v :: vs) = (.op, "+") :: (ptoks v 2 ++ plusTail vs) := by simp [plusTail]
        rw [this, matches_cons] at hmss
        exact .inr hmss.1
    obtain ⟨s', k, hk, hs, rfl, hfl⟩ := hT s (by simp) c (j + 1) hc hms hft
    obtain ⟨r, m, hm', hl, rfl, hfr⟩ := exprLoop_summands ss (fun v hv => hT v (by simp [hv])) c _ hk.2
      (.add [lhs, s']) hc hmss (by rw [show j + 1 + (ptoks s 2).length + (plusTail ss).length =
        j + ((ptoks s 2).length + (plusTail ss).length + 1) by omega]; exact hf)
    obtain ⟨h', hres⟩ := exprLoop_plus c lhs j hj h0 hs hl
    refine ⟨r, _, h', hres, by rw [hst]; simp; omega, ?_⟩
    rw [hfr]
    simp only [foldAdd, List.foldl_cons]
    exact flat_foldAdd_congr (by rw [flat_add2, flat_add2, ap_congr hfl]) ss

/-- G2: a term is read as its units joined by `*`. -/
theorem tlem_of_units {e : Expr} (h : Plain e) (hU : ∀ u ∈ units e, ULem u) : TLem e := by
  intro c i hc hm hf
  obtain ⟨u, us, hu⟩ := List.exists_cons_of_ne_nil (units_ne_nil h)
  rw [ptoks_units h hu] at hm hf ⊢
  rw [matches_append] at hm
  obtain ⟨hmu, hmus⟩ := hm
  simp only [List.length_append] at hf ⊢
  have hfu : FollowU c (i + (ptoks u 3).length) := by
    cases us with
    | nil => simp [starTail] at hf ⊢; exact .inl hf
    | cons v vs =>
      have : starTail (v :: vs) = (.op, "*") :: (ptoks v 3 ++ starTail vs) := by simp [starTail]
      rw [this, matches_cons] at hmus
      exact .inr hmus.1
  obtain ⟨u', k, hk, hu', rfl, hfl⟩ := hU u (by simp [hu]) c i hc hmu hfu
  obtain ⟨r, m, hm', hl, rfl, hfr⟩ := termLoop_units us (fun v hv => hU v (by simp [hu, hv])) c _ hk.2 u' hc hmus
    (by rw [← Nat.add_assoc] at hf; exact hf)
  obtain ⟨h', hres⟩ := term_spec c i hu' hl
  refine ⟨r, _, h', hres, by omega, ?_⟩
  rw [hfr, flat_foldMul_congr hfl us, flat_foldMul_units h hu]

/-- G3: an expression is read as its summands joined by `+`. -/
theorem elem_of_summands {e : Expr} (h : Plain e) (hT : ∀ s ∈ summands e, TLem s) : ELem e := by
  intro c i hc hm hf
  obtain ⟨s, ss, hs⟩ := List.exists_cons_of_ne_nil (summands_ne_nil h)
  rw [ptoks_summands h hs] at hm hf ⊢
  rw [matches_append] at hm
  obtain ⟨hms, hmss⟩ := hm
  simp only [List.length_append] at hf ⊢
  have hft : FollowT c (i + (ptoks s 2).length) := by
    cases ss with
    | nil => simp [plusTail] at hf ⊢; exact .inl hf
    | cons v vs =>
      have : plusTail (v :: vs) = (.op, "+") :: (ptoks v 2 ++ plusTail vs) := by simp [plusTail]
      rw [this, matches_cons] at hmss
      exact .inr hmss.1
  obtain ⟨s', k, hk, hs', rfl, hfl⟩ := hT s (by simp [hs]) c i hc hms hft
  obtain ⟨r, m, hm', hl, rfl, hfr⟩ := exprLoop_summands ss (fun v hv => hT v (by simp [hs, hv])) c _ hk.2 s' hc hmss
    (by rw [← Nat.add_assoc] at hf; exact hf)
  obtain ⟨h', hres⟩ := expr_spec c i hs' hl
  refine ⟨r, _, h', hres, by omega, ?_⟩
  rw [hfr, flat_foldAdd_congr hfl ss, flat_foldAdd_summands h hs]

/-- G4: a term that binds looser than an atom is read in its parentheses. -/
theorem alem_of_elem {e : Expr} (hE : ELem e) (h4 : precOf e < 4) : ALem e := by
  intro c i hc hm
  have h1 : 1 ≤ precOf e := by unfold precOf; split <;> omega
  have hp4 : ptoks e 4 = (.op, "(") :: (ptoks e 1 ++ [(.op, ")")]) := by
    simp only [ptoks, paren]; simp [h4]; omega
  rw [hp4, matches_cons, matches_append, matches_cons] at hm
  obtain ⟨h0, hme, hr, _⟩ := hm
  obtain ⟨e', j, hj, he, rfl, hfl⟩ := hE c (i + 1) hc hme (.inr hr)
  obtain ⟨h', ha⟩ := atom_paren c i h0 he hr
  refine ⟨e', _, h', ha, ?_, hfl⟩
  rw [hp4]; simp; omega

theorem alem_num (n : Nat) : ALem (.num (Q.ofInt n)) := by
  intro c i hc hm
  have hp : ptoks (.num (Q.ofInt n)) 4 = [(.num, toString (n : Int))] := by simp [ptoks, raw, ofInt_num]
  rw [hp, matches_cons] at hm
  simp only [strip, Prod.mk.injEq] at hm
  obtain ⟨⟨hk, hs⟩, _⟩ := hm
  have hq : Q.parse (c.tok i).s = some (Q.ofInt n) := by rw [hs]; exact parse_digits n
  obtain ⟨h', ha⟩ := atom_num c i hk hq
  exact ⟨_, _, h', ha, by rw [hp]; rfl, rfl⟩

theorem alem_var (x : String) (hx : x ∉ reserved) : ALem (.var x) := by
  intro c i hc hm
  have hp : ptoks (.var x) 4 = [(.id, x)] := by simp [ptoks, raw]
  rw [hp, matches_cons] at hm
  simp only [strip, Prod.mk.injEq] at hm
  obtain ⟨⟨hk, hs⟩, _⟩ := hm
  obtain ⟨h', ha⟩ := atom_var c i hk hc (by rw [hs]; exact hx)
  rw [hs] at ha
  exact ⟨_, _, h', ha, by rw [hp]; rfl, rfl⟩

theorem mkCall_unary {f : String} (hf : f ∈ unaryNames) (args : List Expr) : mkCall f args = .fn f args := by
  have : reciprocalOf f = none := by
    simp only [unaryNames, List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  unfold mkCall; rw [this]

theorem alem_fn {f : String} (hf : f ∈ unaryNames) {a : Expr} (ha : Plain a) (hE : ELem a) :
    ALem (.fn f [a]) := by
  intro c i hc hm
  have hp : ptoks (.fn f [a]) 4 = (.id, f) :: (.op, "(") :: (ptoks a 1 ++ [(.op, ")")]) := by
    simp [ptoks, raw]
  rw [hp, matches_cons, matches_cons, matches_append, matches_cons] at hm
  obtain ⟨h0, hlp, hma, hr, _⟩ := hm
  simp only [strip, Prod.mk.injEq] at h0
  obtain ⟨a', j, hj, he, rfl, hfl⟩ := hE c (i + 1 + 1) hc hma (.inr hr)
  obtain ⟨h1, hca⟩ := callArgs_one c (i + 1 + 1) (head_isOp ha hma).2.1 he hr
  obtain ⟨h2, hat⟩ := atom_call c i h0.1 hf h0.2 hlp hca
  rw [mkCall_unary hf] at hat
  refine ⟨_, _, h2, hat, by rw [hp]; simp; omega, ?_⟩
  simp [flat, flatList, hfl]

theorem ulem_pow {b x : Expr} (hb : Plain b) (hA : ALem b) (hU : ULem x) : ULem (.pow b x) := by
  intro c i hc hm hf
  have hp : ptoks (.pow b x) 3 = ptoks b 4 ++ (.op, "^") :: ptoks x 3 := by simp [ptoks, raw]
  rw [hp, matches_append, matches_cons] at hm
  obtain ⟨hmb, h0, hmx⟩ := hm
  rw [hp] at hf
  simp only [List.length_append, List.length_cons] at hf
  obtain ⟨b', j, hj, hab, rfl, hfb⟩ := hA c i hc hmb
  obtain ⟨x', k, hk, hux, rfl, hfx⟩ := hU c (i + (ptoks b 4).length + 1) hc hmx
    (by rw [show i + (ptoks b 4).length + 1 + (ptoks x 3).length = i + ((ptoks b 4).length + ((ptoks x 3).length + 1)) by omega]; exact hf)
  obtain ⟨h', hpw⟩ := power_pow c i hab h0 hux
  refine ⟨.pow b' x', _, h', ?_, by rw [hp]; simp; omega, ?_⟩
  · rw [unary_power c i (head_isOp hb hmb).1]; exact hpw
  · simp [flat, hfb, hfx]

/-- All four levels read `e`, and the levels below a product and a sum read its units and terms. -/
def Good (e : Expr) : Prop :=
  ALem e ∧ ULem e ∧ TLem e ∧ ELem e ∧ (∀ u ∈ units e, ULem u) ∧ (∀ s ∈ summands e, TLem s)

/-- An atom of the fragment, read at every level. -/
theorem good_of_alem {e : Expr} (h : Plain e) (hA : ALem e) (h4 : precOf e = 4) (hu : units e = [e])
    (hs : summands e = [e]) : Good e := by
  have hU := ulem_of_alem h hA (by omega)
  have hT := tlem_of_units h (by rw [hu]; simpa using hU)
  have hE := elem_of_summands h (by rw [hs]; simpa using hT)
  exact ⟨hA, hU, hT, hE, by rw [hu]; simpa using hU, by rw [hs]; simpa using hT⟩

theorem good {e : Expr} (h : Plain e) : Good e := by
  induction h with
  | num n => exact good_of_alem (.num n) (alem_num n) rfl rfl rfl
  | var x hx hr => exact good_of_alem (.var x hx hr) (alem_var x hr) rfl rfl rfl
  | fn f a hf ha iha => exact good_of_alem (.fn f a hf ha) (alem_fn hf ha iha.2.2.2.1) rfl rfl rfl
  | pow b x hb hx ihb ihx =>
    have hp := Plain.pow b x hb hx
    have hU := ulem_pow hb ihb.1 ihx.2.1
    have hT := tlem_of_units hp (by simpa [units] using hU)
    have hE := elem_of_summands hp (by simpa [summands] using hT)
    exact ⟨alem_of_elem hE (by simp), hU, hT, hE, by simpa [units] using hU, by simpa [summands] using hT⟩
  | mul a b as ha hb has iha ihb ihas =>
    have hp := Plain.mul a b as ha hb has
    have hUs : ∀ u ∈ units (.mul (a :: b :: as)), ULem u := by
      intro u hu
      simp only [units, unitsList] at hu
      have hl : ∀ l : List Expr, (∀ c ∈ l, Good c) → ∀ u ∈ unitsList l, ULem u := by
        intro l hl; induction l with
        | nil => simp [unitsList]
        | cons x xs ih =>
          intro u hu; simp only [unitsList, List.mem_append] at hu
          rcases hu with hu | hu
          · exact (hl x (by simp)).2.2.2.2.1 u hu
          · exact ih (fun c hc => hl c (by simp [hc])) u hu
      simp only [List.mem_append] at hu
      rcases hu with hu | hu | hu
      · exact iha.2.2.2.2.1 u hu
      · exact ihb.2.2.2.2.1 u hu
      · exact hl as ihas u hu
    have hT := tlem_of_units hp hUs
    have hE := elem_of_summands hp (by simpa [summands] using hT)
    have hA := alem_of_elem hE (by simp)
    exact ⟨hA, ulem_of_alem hp hA (by simp), hT, hE, hUs, by simpa [summands] using hT⟩
  | add a b as ha hb has iha ihb ihas =>
    have hp := Plain.add a b as ha hb has
    have hTs : ∀ s ∈ summands (.add (a :: b :: as)), TLem s := by
      intro s hs
      simp only [summands, List.mem_append, List.mem_cons] at hs
      rcases hs with hs | rfl | hs
      · exact iha.2.2.2.2.2 s hs
      · exact ihb.2.2.1
      · exact (ihas s hs).2.2.1
    have hE := elem_of_summands hp hTs
    have hA := alem_of_elem hE (by simp)
    have hU := ulem_of_alem hp hA (by simp)
    have hT := tlem_of_units hp (by simpa [units] using hU)
    exact ⟨hA, hU, hT, hE, by simpa [units] using hU, hTs⟩

/-! ## The round trip -/

theorem matches_of_lex {arr : Array Tok} {L : List T} (h : arr.toList.map strip = L) (known : List String) :
    Matches ⟨arr, known⟩ 0 L := by
  subst h
  intro k hk
  simp only [List.length_map, Array.length_toList] at hk
  simp [PCtx.tok, Array.getD_eq_getD_getElem?, hk]

/-- **Round trip.** On the fragment, the printed text of a term parses back to a term that is the
same up to how sums in sums and products in products are bracketed. -/
theorem parse_toText {e : Expr} (h : Plain e) : ∃ e', parse e.toText = .ok e' ∧ flat e' = flat e := by
  have hp : e.toText.toList = render (ptoks e 1) := (printRaw_plain h).print [] 1
  obtain ⟨arr, hlex, hstrip⟩ := lex_render (ptoks e 1) (lexable_plain h 1) 0 #[]
  have hl : lex e.toText = .ok arr := by unfold lex; rw [hp]; exact hlex
  simp only [List.map_nil, List.nil_append] at hstrip
  have hm := matches_of_lex hstrip []
  rw [matches_append] at hm
  obtain ⟨hme, heof⟩ := hm
  have hf : FollowE ⟨arr, []⟩ (0 + (ptoks e 1).length) := by
    rw [matches_cons] at heof
    left; simp only [strip, Prod.mk.injEq] at heof; exact heof.1.1
  obtain ⟨e', m, hmh, he, rfl, hfl⟩ := (good h).2.2.2.1 ⟨arr, []⟩ 0 rfl hme hf
  have hlet := (head_isOp h hme).2.2
  refine ⟨e', ?_, hfl⟩
  unfold parse parseStmt
  simp only [hl, except_bind_ok]
  have hk : ((PCtx.tok ⟨arr, []⟩ 0).kind == .id && (PCtx.tok ⟨arr, []⟩ 0).s == "let") = false := by
    simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    by_cases h1 : (PCtx.tok ⟨arr, []⟩ 0).kind = .id
    · exact .inr (fun h2 => hlet ⟨h1, h2⟩)
    · exact .inl h1
  have heof' : (PCtx.tok ⟨arr, []⟩ (0 + (ptoks e 1).length)).kind = .eof := hf.elim id (fun h => by
    rw [matches_cons] at heof; simp only [strip, Prod.mk.injEq] at heof h; rw [heof.1.1] at h; exact absurd h.1 (by decide))
  simp only [Nat.zero_add] at heof'
  simp [hk, he, heof']
  rfl

/-- `x^2 + 3*sin(x)` is in the fragment, so `parse_toText` applies to it. -/
example : Plain (.add [.pow (.var "x") (.num (Q.ofInt (2 : Nat))),
    .mul [.num (Q.ofInt (3 : Nat)), .fn "sin" [.var "x"]]]) :=
  have hx : Plain (.var "x") := .var "x" (by simp [isIdent, lex.isIdStart, lex.isGreek])
    (by simp [reserved, builtinFunctions])
  .add _ _ [] (.pow _ _ hx (.num 2)) (.mul _ _ [] (.num 3) (.fn "sin" _ (by simp [unaryNames]) hx) nofun) nofun

end RoundTrip
end MathEngine
