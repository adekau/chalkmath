import MathEngine.Parser
import MathEngine.Print
/-!
# Reading back what the printer writes

WIP
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

@[simp] theorem render_nil : render [] = [] := rfl
@[simp] theorem render_cons (t : T) (ts : List T) : render (t :: ts) = renderTok t ++ render ts := by
  simp [render]
@[simp] theorem render_append (a b : List T) : render (a ++ b) = render a ++ render b := by simp [render]
@[simp] theorem renderTok_num (s : String) : renderTok (.num, s) = s.toList := rfl
@[simp] theorem renderTok_id (s : String) : renderTok (.id, s) = s.toList := rfl
@[simp] theorem renderTok_plus : renderTok (.op, "+") = [' ', '+', ' '] := rfl
theorem renderTok_op {s : String} (h : s ≠ "+") : renderTok (.op, s) = s.toList := by
  simp [renderTok, h]
@[simp] theorem renderTok_lp : renderTok (.op, "(") = ['('] := rfl
@[simp] theorem renderTok_rp : renderTok (.op, ")") = [')'] := rfl
@[simp] theorem renderTok_star : renderTok (.op, "*") = ['*'] := rfl
@[simp] theorem renderTok_hat : renderTok (.op, "^") = ['^'] := rfl

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

end RoundTrip
end MathEngine
