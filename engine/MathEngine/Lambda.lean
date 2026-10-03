import MathEngine.Print
/-!
# The λ-calculus world

A second little language inside the same engine: untyped λ-terms with named variables, reduced in
normal order one β-step at a time, each step recorded like the rewriter's. Terms are *encoded* into
`Expr` for the wire (`fn "λ" [var x, body]`, `fn "@" [f, a]`), so the notebook's selection,
explanation and origin tracking work unchanged; the printer knows the two heads. The de Bruijn view
is computed alongside every step (`toDB`), so the notebook's toggle is a rendering, not a
recomputation. Definitions (`name := term`, with the Church library preloaded) are unfolded first,
as one δ-step.

Reduction is on fuel — the one budget in the engine, and the honest one: whether a term has a
normal form is undecidable, so a term that has not reached one after `maxSteps` β-steps, or that grows
past `maxSize` symbols, is refused with what it has become so far (a definition is then bound
unreduced, as `fact := Y F` must be). The parts that are proved are in `LambdaProofs.lean`.

The grammar of a λ-cell:

    cell    ::= NAME ':=' term | 'let' NAME '=' term | command | term
    command ::= STRATEGY [NUM] ':' term          -- STRATEGY: normal | cbn | cbv | applicative
              | 'eta' [NUM] ':' term             -- β and η, leftmost-outermost
              | 'fv' ':' term | 'db' ':' term
              | 'alpha' ':' term ',' term
              | 'subst' ':' term ',' NAME ':=' term
              | ('type' | 'infer') ':' [ctx ('⊢' | '|-')] term
    ctx     ::= NAME ':' type (',' NAME ':' type)*
    term    ::= ('λ' | '\') binder+ '.' term | app
    binder  ::= NAME [':' type] | '(' NAME ':' type ')'
    app     ::= atom atom*                       -- application groups to the left
    atom    ::= NAME | NUM | '(' term ')' | 'λ' …
    type    ::= tatom [('→' | '->') type]        -- the arrow groups to the right
    tatom   ::= NAME | '(' type ')'

A NUM is a Church numeral; NAME may use Greek letters (type variables, `α → α`). A typed binder's type
is erased when the term is reduced; `type:` and `infer:` are in `Stlc.lean`.
-/
namespace MathEngine
namespace Lam

/-- Named terms. -/
inductive Term where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq, Inhabited

/-- De Bruijn terms; a free variable keeps its name. -/
inductive DB where
  | bvar : Nat → DB
  | free : String → DB
  | lam : DB → DB
  | app : DB → DB → DB
  deriving Repr, DecidableEq, Inhabited

open Term

def freeVars : Term → List String
  | .var x => [x]
  | .lam x e => (freeVars e).filter (· != x)
  | .app a b => (freeVars a ++ freeVars b).eraseDups

def size : Term → Nat
  | .var _ => 1
  | .lam _ e => 1 + size e
  | .app a b => 1 + size a + size b

/-- The length of the longest name in a list. -/
def longest (l : List String) : Nat := l.foldl (fun m s => max m s.length) 0

/-- A name not in `avoid`, derived from `base`: `x`, `x'`, `x''`, … and, should those run out, one
longer than every name in `avoid` (`freshVar_not_mem`). -/
def freshVar (avoid : List String) (base : String) : String :=
  go base avoid.length
where
  go (cand : String) : Nat → String
    | 0 => if cand ∈ avoid then base ++ String.ofList (List.replicate (longest avoid + 1) '\'') else cand
    | n + 1 => if cand ∈ avoid then go (cand ++ "'") n else cand

/-- Does `x` occur free in the term? -/
def occursFree (x : String) : Term → Bool
  | .var y => y == x
  | .lam y e => y != x && occursFree x e
  | .app a b => occursFree x a || occursFree x b

/-- Every name in the term, bound or free (with repeats). -/
def names : Term → List String
  | .var x => [x]
  | .lam x e => x :: names e
  | .app a b => names a ++ names b

/-- Rename, before substituting for `x`, each binder that would capture: one whose name is in `clash`
(the free variables of what is put in) over a body where `x` is free. Below a binder named `x` nothing
is substituted, so nothing is renamed. A new name avoids `avoid` (every name in sight) and the names
already given. One structural pass with the renaming carried down (`ren`), hence total. -/
def freshen (x : String) (clash avoid : List String) (ren : List (String × String)) : Term → Term
  | .var w => .var ((ren.lookup w).getD w)
  | .app a b => .app (freshen x clash avoid ren a) (freshen x clash avoid ren b)
  | .lam y e =>
    if y == x then .lam y (freshen x [] avoid ((y, y) :: ren) e)
    else
      let y' := if clash.contains y && occursFree x e then freshVar avoid y else y
      .lam y' (freshen x clash (y' :: avoid) ((y, y') :: ren) e)

/-- Capture-free substitution `e[x := s]`, assuming no binder of `e` is free in `s`. -/
def substRaw (x : String) (s : Term) : Term → Term
  | .var y => if y == x then s else .var y
  | .app a b => .app (substRaw x s a) (substRaw x s b)
  | .lam y e => if y == x then .lam y e else .lam y (substRaw x s e)

/-- The term with the binders that would capture a free variable of `s` renamed, ready for `substRaw`. -/
def renameFor (x : String) (s : Term) (e : Term) : Term :=
  let clash := (freeVars s).filter (· != x)
  if clash.isEmpty then e else freshen x clash (x :: clash ++ names e) [] e

/-- Capture-avoiding substitution: first rename the binders that would capture, then substitute.
Whether any renaming happened is reported, so the derivation can show the α-step. -/
def subst (x : String) (s : Term) (e : Term) : Term × Bool :=
  let e' := renameFor x s e
  (substRaw x s e', e' != e)

/-- One normal-order β-step: the leftmost-outermost redex. Returns the contractum and whether an
α-renaming preceded it. -/
def betaStep : Term → Option (Term × Bool)
  | .app (.lam x body) arg => some (subst x arg body)
  | .app a b =>
    match betaStep a with
    | some (a', r) => some (.app a' b, r)
    | none => (betaStep b).map fun (b', r) => (.app a b', r)
  | .lam x e => (betaStep e).map fun (e', r) => (.lam x e', r)
  | .var _ => none

/-! ## The de Bruijn view -/

def toDB (ctx : List String := []) : Term → DB
  | .var x => match ctx.idxOf? x with | some i => .bvar i | none => .free x
  | .lam x e => .lam (toDB (x :: ctx) e)
  | .app a b => .app (toDB ctx a) (toDB ctx b)

/-! ## Church encodings -/

def church (n : Nat) : Term :=
  .lam "f" (.lam "x" (go n))
where
  go : Nat → Term
    | 0 => .var "x"
    | k + 1 => .app (.var "f") (go k)

/-- The Church numeral a normal form is, if it is one. -/
def readChurch : Term → Option Nat
  | .lam f (.lam x body) => go f x body
  | _ => none
where
  go (f x : String) : Term → Option Nat
    | .var y => if y == x then some 0 else none
    | .app (.var g) e => if g == f then (go f x e).map (· + 1) else none
    | _ => none

def readBool : Term → Option Bool
  | .lam t (.lam f (.var y)) => if y == t && t != f then some true else if y == f then some false else none
  | _ => none

/-- Unfold definitions: free occurrences of defined names, outermost first; a name that is a
numeral unfolds to its Church numeral. -/
def expandDefs (defs : List (String × Term)) : Term → Term
  | .var x =>
    match defs.lookup x with
    | some t => t
    | none => if x.all Char.isDigit && !x.isEmpty then church x.toNat! else .var x
  | .lam x e => .lam x (expandDefs (defs.filter (·.1 != x)) e)
  | .app a b => .app (expandDefs defs a) (expandDefs defs b)

/-- The library every λ-cell can use: booleans, numerals, pairs, combinators. -/
def churchDefs : List (String × Term) :=
  let t := Term.var
  let l := Term.lam
  let a := Term.app
  [ ("true",  l "t" (l "f" (t "t"))),
    ("false", l "t" (l "f" (t "f"))),
    ("and",   l "p" (l "q" (a (a (t "p") (t "q")) (t "p")))),
    ("or",    l "p" (l "q" (a (a (t "p") (t "p")) (t "q")))),
    ("not",   l "p" (a (a (t "p") (l "t" (l "f" (t "f")))) (l "t" (l "f" (t "t"))))),
    ("if",    l "c" (l "a" (l "b" (a (a (t "c") (t "a")) (t "b"))))),
    ("zero",  church 0),
    ("succ",  l "n" (l "f" (l "x" (a (t "f") (a (a (t "n") (t "f")) (t "x")))))),
    ("add",   l "m" (l "n" (l "f" (l "x" (a (a (t "m") (t "f")) (a (a (t "n") (t "f")) (t "x"))))))),
    ("mul",   l "m" (l "n" (l "f" (a (t "m") (a (t "n") (t "f")))))),
    ("pow",   l "m" (l "n" (a (t "n") (t "m")))),
    ("iszero", l "n" (a (a (t "n") (l "y" (l "t" (l "f" (t "f"))))) (l "t" (l "f" (t "t"))))),
    ("pair",  l "a" (l "b" (l "s" (a (a (t "s") (t "a")) (t "b"))))),
    ("fst",   l "p" (a (t "p") (l "a" (l "b" (t "a"))))),
    ("snd",   l "p" (a (t "p") (l "a" (l "b" (t "b"))))),
    ("id",    l "x" (t "x")),
    ("const", l "x" (l "y" (t "x"))),
    ("K",     l "x" (l "y" (t "x"))),
    ("S",     l "x" (l "y" (l "z" (a (a (t "x") (t "z")) (a (t "y") (t "z")))))),
    ("I",     l "x" (t "x")),
    ("omega", l "x" (a (t "x") (t "x"))),
    ("Y",     l "f" (a (l "x" (a (t "f") (a (t "x") (t "x")))) (l "x" (a (t "f") (a (t "x") (t "x")))))) ]

/-! ## Encoding into `Expr` for the wire -/

def toExpr : Term → Expr
  | .var x => .var x
  | .lam x e => .fn "λ" [.var x, toExpr e]
  | .app a b => .fn "@" [toExpr a, toExpr b]

/-- Decoding, the inverse of `toExpr` on its image. -/
partial def ofExpr : Expr → Option Term
  | .var x => some (.var x)
  | .fn "λ" [.var x, e] => (ofExpr e).map (.lam x)
  | .fn "λ:" [.var x, _, e] => (ofExpr e).map (.lam x)
  | .fn "@" [f, a] => do pure (.app (← ofExpr f) (← ofExpr a))
  | _ => none

def dbToExpr : DB → Expr
  | .bvar n => .num (Q.ofInt n)
  | .free x => .var x
  | .lam e => .fn "λ." [dbToExpr e]
  | .app a b => .fn "@" [dbToExpr a, dbToExpr b]

/-! ## Simple types and annotated terms

The simply typed λ-calculus writes a binder's type, `λx:A. e`. A term as parsed keeps its
annotations (`ATerm`); reduction erases them (the types say which terms are allowed, not how they
compute). Types are base names (`A`, `Nat`), arrows, and the type variables inference introduces. -/

inductive Ty where
  | base : String → Ty
  | tvar : Nat → Ty
  | arrow : Ty → Ty → Ty
  deriving Repr, DecidableEq, Inhabited

/-- Terms whose binders may carry a type. -/
inductive ATerm where
  | var : String → ATerm
  | lam : String → Option Ty → ATerm → ATerm
  | app : ATerm → ATerm → ATerm
  deriving Repr, DecidableEq, Inhabited

/-- A typing context, innermost binding first. -/
abbrev Ctx := List (String × Ty)

def ATerm.erase : ATerm → Term
  | .var x => .var x
  | .lam x _ e => .lam x e.erase
  | .app a b => .app a.erase b.erase

def ATerm.ofTerm : Term → ATerm
  | .var x => .var x
  | .lam x e => .lam x none (ofTerm e)
  | .app a b => .app (ofTerm a) (ofTerm b)

/-- Unfold definitions in an annotated term, as `expandDefs` does. -/
def ATerm.expandDefs (defs : List (String × Term)) : ATerm → ATerm
  | .var x =>
    match defs.lookup x with
    | some t => ofTerm t
    | none => if x.all Char.isDigit && !x.isEmpty then ofTerm (church x.toNat!) else .var x
  | .lam x T e => .lam x T (expandDefs (defs.filter (·.1 != x)) e)
  | .app a b => .app (expandDefs defs a) (expandDefs defs b)

/-- A type variable prints as τ₁, τ₂, … while inference works on it. -/
def Ty.toExpr : Ty → Expr
  | .base s => .var s
  | .tvar n => .var ("τ" ++ toString (n + 1))
  | .arrow a b => .fn "→" [a.toExpr, b.toExpr]

def ATerm.toExpr : ATerm → Expr
  | .var x => .var x
  | .lam x none e => .fn "λ" [.var x, e.toExpr]
  | .lam x (some T) e => .fn "λ:" [.var x, T.toExpr, e.toExpr]
  | .app a b => .fn "@" [a.toExpr, b.toExpr]

/-! ## Parsing: `λx y. e`, `λx:A. e`, `\\x. e`, application by juxtaposition, numerals as Church numerals -/

inductive Tok where | lam | dot | lp | rp | colon | arrow | ident (s : String) | num (n : Nat) | eof
  deriving Repr, BEq, Inhabited

/-- A Greek letter other than λ: type variables are written α, β, …. -/
def isGreek (c : Char) : Bool := (c.val ≥ 0x3B1 && c.val ≤ 0x3C9 && c != 'λ') || (c.val ≥ 0x391 && c.val ≤ 0x3A9)

partial def lex (src : String) : Except String (List Tok) := go src.toList []
where
  go : List Char → List Tok → Except String (List Tok)
    | [], acc => .ok (acc.reverse ++ [.eof])
    | c :: cs, acc =>
      if c.isWhitespace then go cs acc
      else if c == 'λ' || c == '\\' then go cs (.lam :: acc)
      else if c == '.' then go cs (.dot :: acc)
      else if c == '(' then go cs (.lp :: acc)
      else if c == ')' then go cs (.rp :: acc)
      else if c == ':' then go cs (.colon :: acc)
      else if c == '→' then go cs (.arrow :: acc)
      else if c == '-' && cs.head? == some '>' then go cs.tail (.arrow :: acc)
      else if c.isDigit then
        let ds := (c :: cs).takeWhile Char.isDigit
        go ((c :: cs).drop ds.length) (.num ((String.ofList ds).toNat!) :: acc)
      else if c.isAlpha || c == '_' || isGreek c then
        let ds := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_' || d == '\'' || isGreek d
        go ((c :: cs).drop ds.length) (.ident (String.ofList ds) :: acc)
      else .error s!"unexpected character '{c}' in a λ-term"

/-- A type: `A`, `A → B` (to the right: `A → B → C` is `A → (B → C)`), `(A → B) → C`. -/
partial def parseTy (ts : List Tok) : Except String (Ty × List Tok) := do
  let (a, ts) ← atom ts
  match ts with
  | .arrow :: ts => let (b, ts) ← parseTy ts; pure (.arrow a b, ts)
  | ts => pure (a, ts)
where
  atom : List Tok → Except String (Ty × List Tok)
    | .ident x :: ts => pure (.base x, ts)
    | .lp :: ts => do
      let (t, ts) ← parseTy ts
      match ts with
      | .rp :: ts => pure (t, ts)
      | _ => throw "expected ')' in a type"
    | _ => throw "expected a type: a name such as A, or an arrow A → B"

/-- Recursive descent; the parser is mutual, hence `partial`. -/
partial def parseExpr : List Tok → Except String (ATerm × List Tok)
  | .lam :: ts => do
    let (names, ts) ← binders ts
    if names.isEmpty then throw "expected a variable after λ"
    match ts with
    | .dot :: ts =>
      let (body, ts) ← parseExpr ts
      pure (names.foldr (fun (x, T) e => .lam x T e) body, ts)
    | _ => throw "expected '.' after the λ-binders"
  | ts => parseApp ts
where
  binders : List Tok → Except String (List (String × Option Ty) × List Tok)
    | .ident x :: .colon :: ts => do
      let (T, ts) ← parseTy ts
      let (xs, ts) ← binders ts
      pure ((x, some T) :: xs, ts)
    | .ident x :: ts => do let (xs, ts) ← binders ts; pure ((x, none) :: xs, ts)
    | .lp :: .ident x :: .colon :: ts => do
      let (T, ts) ← parseTy ts
      match ts with
      | .rp :: ts => let (xs, ts) ← binders ts; pure ((x, some T) :: xs, ts)
      | _ => throw "expected ')' after the binder's type"
    | ts => if ts.head? == some .dot then pure ([], ts) else throw "expected a variable after λ"
  parseApp (ts : List Tok) : Except String (ATerm × List Tok) := do
    let (f, ts) ← atom ts
    loop f ts
  loop (f : ATerm) : List Tok → Except String (ATerm × List Tok)
    | ts@(.ident _ :: _) | ts@(.num _ :: _) | ts@(.lp :: _) | ts@(.lam :: _) => do
      let (a, ts') ← if ts.head? == some .lam then parseExpr ts else atom ts
      loop (.app f a) ts'
    | ts => pure (f, ts)
  atom : List Tok → Except String (ATerm × List Tok)
    | .ident x :: ts => pure (.var x, ts)
    | .num n :: ts => pure (.var (toString n), ts)   -- a numeral is a name, unfolded by the δ-step
    | .lp :: ts => do
      let (e, ts) ← parseExpr ts
      match ts with
      | .rp :: ts => pure (e, ts)
      | _ => throw "expected ')'"
    | .lam :: ts => parseExpr (.lam :: ts)
    | .eof :: _ => throw "unexpected end of the λ-term"
    | .colon :: _ => throw "unexpected ':' (a type belongs after a binder: λx:A. e)"
    | _ => throw "unexpected token in the λ-term"

def parseATerm (src : String) : Except String ATerm := do
  let toks ← lex src
  let (t, rest) ← parseExpr toks
  match rest with
  | [.eof] | [] => pure t
  | _ => throw "unexpected input after the λ-term"

/-- A term, its binders' types (if any) erased. -/
def parseTerm (src : String) : Except String Term := (parseATerm src).map ATerm.erase

/-- A type on its own, as an exercise's answer gives one. -/
def parseType (src : String) : Except String Ty := do
  let (T, rest) ← parseTy (← lex src)
  if rest == [.eof] then pure T else throw "unexpected input after the type"

/-- A λ-cell: `name := term`, `let name = term`, or a term. -/
def parseStmt (src : String) : Except String (Option String × Term) := do
  let s := src.trimAscii.copy
  let (name, body) :=
    if s.startsWith "let " then
      let rest := (s.drop 4).trimAscii.copy
      match rest.splitOn "=" with
      | n :: r => (some n.trimAscii.copy, "=".intercalate r)
      | [] => (none, rest)
    else match s.splitOn ":=" with
      | [n, r] => (some n.trimAscii.copy, r)
      | _ => (none, s)
  let t ← parseTerm body
  match name with
  | some n => if n.isEmpty || !(n.all fun c => c.isAlphanum || c == '_' || c == '\'') then throw s!"'{n}' is not a name" else pure (some n, t)
  | none => pure (none, t)

/-! ## Commands

A λ-cell may start with a command and a colon: a reduction strategy (`cbv: t`, with an optional
step count, `normal 5: t`), `eta:`, `fv:`, `db:`, `alpha: s, t`, `subst: e, x := s`, and the typed
calculus's `type: Γ ⊢ t` and `infer: Γ ⊢ t`. -/

/-- Which redex a reduction contracts next. -/
inductive Strategy where
  | normal | cbn | cbv | applicative
  deriving BEq, Repr, Inhabited

inductive Cmd where
  | reduce (s : Strategy) (limit : Option Nat) (t : ATerm)
  | eta (limit : Option Nat) (t : ATerm)
  | fv (t : ATerm)
  | db (t : ATerm)
  | alpha (a b : ATerm)
  | subst (e : ATerm) (x : String) (s : ATerm)
  | type (Γ : Ctx) (t : ATerm)
  | infer (Γ : Ctx) (t : ATerm)

def commandWords : List String := ["normal", "cbn", "cbv", "applicative", "eta", "fv", "db", "alpha", "subst", "type", "infer"]

/-- A command's word, its step count, and the text after the colon (not a `:=` definition). -/
def commandHead (src : String) : Option (String × Option Nat × String) :=
  let cs := src.trimAscii.copy.toList
  let w := cs.takeWhile Char.isAlpha
  let rest := (cs.drop w.length).dropWhile Char.isWhitespace
  let ds := rest.takeWhile Char.isDigit
  let rest := (rest.drop ds.length).dropWhile Char.isWhitespace
  let word := String.ofList w
  match rest with
  | ':' :: r =>
    if commandWords.contains word && r.head? != some '=' then
      some (word, if ds.isEmpty then none else some (String.ofList ds).toNat!, String.ofList r)
    else none
  | _ => none

/-- `Γ ⊢ t` (or `|-`): the context and the term; no turnstile, an empty context. -/
def splitTurnstile (s : String) : String × String :=
  match s.splitOn "⊢" with
  | [g, t] => (g, t)
  | _ => match s.splitOn "|-" with
    | [g, t] => (g, t)
    | _ => ("", s)

/-- A context, `x : A, f : A → B`, as written: the later entries shadow the earlier. -/
def parseCtx (s : String) : Except String Ctx := do
  if s.trimAscii.isEmpty then return []
  let entries ← (s.splitOn ",").mapM fun (entry : String) => do
    let bad : String := s!"expected 'name : type' in the context, not '{entry.trimAscii}'"
    match ← lex entry with
    | .ident x :: .colon :: ts =>
      let (T, rest) ← parseTy ts
      if rest == [.eof] then pure (x, T) else throw bad
    | _ => throw bad
  pure entries.reverse

def isName (x : String) : Bool := !x.isEmpty && x.all fun c => c.isAlphanum || c == '_' || c == '\''

/-- The command a source starts with, if it does, parsed. -/
def parseCmd (src : String) : Option (Except String Cmd) :=
  (commandHead src).map fun (w, n, rest) => do
    if n.isSome && !["normal", "cbn", "cbv", "applicative", "eta"].contains w then
      throw s!"{w}: takes no step count"
    match w with
    | "normal" => pure (.reduce .normal n (← parseATerm rest))
    | "cbn" => pure (.reduce .cbn n (← parseATerm rest))
    | "cbv" => pure (.reduce .cbv n (← parseATerm rest))
    | "applicative" => pure (.reduce .applicative n (← parseATerm rest))
    | "eta" => pure (.eta n (← parseATerm rest))
    | "fv" => pure (.fv (← parseATerm rest))
    | "db" => pure (.db (← parseATerm rest))
    | "alpha" =>
      match rest.splitOn "," with
      | [a, b] => pure (.alpha (← parseATerm a) (← parseATerm b))
      | _ => throw "alpha: give two terms, separated by a comma"
    | "subst" =>
      let usage := "subst: write `subst: term, x := term`"
      match rest.splitOn "," with
      | [e, b] =>
        match b.splitOn ":=" with
        | [x, s] =>
          let x := x.trimAscii.copy
          if !isName x then throw s!"subst: '{x}' is not a variable"
          pure (.subst (← parseATerm e) x (← parseATerm s))
        | _ => throw usage
      | _ => throw usage
    | "type" | "infer" =>
      let (g, t) := splitTurnstile rest
      let Γ ← parseCtx g
      let t ← parseATerm t
      pure (if w == "type" then .type Γ t else .infer Γ t)
    | _ => throw s!"unknown λ-command {w}"

/-- Is this cell a λ-cell? A command, a λ or backslash anywhere, a `:=` definition, or a first word
that is a λ-definition of the session or the Church library. -/
def isLambdaSource (src : String) (defs : List String) : Bool :=
  (commandHead src).isSome ||
  src.any (fun c => c == 'λ' || c == '\\') || (src.splitOn ":=").length == 2 ||
  (let w := (src.trimAscii.copy.splitOn " ").headD ""
   let w := if w == "let" then "" else w
   defs.contains w && !src.contains '(' || (defs.contains w && src.contains ' '))

/-! ## Reduction strategies and η -/

/-- One call-by-name step: the leftmost-outermost redex, but never under a λ, and arguments are passed
unevaluated. It stops at a weak head normal form. -/
def cbnStep : Term → Option (Term × Bool)
  | .app (.lam x body) arg => some (subst x arg body)
  | .app a b => (cbnStep a).map fun (a', r) => (.app a' b, r)
  | _ => none

/-- A value of call by value: a variable or an abstraction (Plotkin's λ_V; for closed terms, just the
abstractions). -/
def isValue : Term → Bool
  | .app _ _ => false
  | _ => true

/-- One call-by-value step: the function, then the argument, are reduced to values before the call;
never under a λ. -/
def cbvStep : Term → Option (Term × Bool)
  | .app (.lam x body) arg =>
    if isValue arg then some (subst x arg body)
    else (cbvStep arg).map fun (a', r) => (.app (.lam x body) a', r)
  | .app a b =>
    match cbvStep a with
    | some (a', r) => some (.app a' b, r)
    | none => (cbvStep b).map fun (b', r) => (.app a b', r)
  | _ => none

/-- One applicative-order step: the leftmost-innermost redex — the function and the argument are
reduced to normal form first, under λ too. -/
def appStep : Term → Option (Term × Bool)
  | .var _ => none
  | .lam x e => (appStep e).map fun (e', r) => (.lam x e', r)
  | .app a b =>
    match appStep a with
    | some (a', r) => some (.app a' b, r)
    | none =>
      match appStep b with
      | some (b', r) => some (.app a b', r)
      | none =>
        match a with
        | .lam x body => some (subst x b body)
        | _ => none

def Strategy.step : Strategy → Term → Option (Term × Bool)
  | .normal => betaStep
  | .cbn => cbnStep
  | .cbv => cbvStep
  | .applicative => appStep

def Strategy.name : Strategy → String
  | .normal => "normal order"
  | .cbn => "call by name"
  | .cbv => "call by value"
  | .applicative => "applicative order"

/-- An η-redex `λx. f x`, with `x` not free in `f`, contracts to `f`. -/
def etaRedex : Term → Option Term
  | .lam x (.app f (.var y)) => if y == x && !(freeVars f).contains x then some f else none
  | _ => none

inductive StepKind where
  | beta | alphaBeta | eta
  deriving BEq, Repr, Inhabited

/-- One βη-step, leftmost-outermost: at each node an η- or β-redex is contracted before looking inside. -/
def betaEtaStep : Term → Option (Term × StepKind)
  | .var _ => none
  | t@(.lam x e) =>
    match etaRedex t with
    | some f => some (f, .eta)
    | none => (betaEtaStep e).map fun (e', k) => (.lam x e', k)
  | .app (.lam x body) arg =>
    let (r, ren) := subst x arg body
    some (r, if ren then .alphaBeta else .beta)
  | .app a b =>
    match betaEtaStep a with
    | some (a', k) => some (.app a' b, k)
    | none => (betaEtaStep b).map fun (b', k) => (.app a b', k)

def maxSteps : Nat := 10000

/-- The largest term reduction goes on with: a term that grows past it (a fixed-point combinator
unfolding under call by value, say) is stopped, so a cell answers in time whatever it is given. -/
def maxSize : Nat := 6000

/-- How much of a long run is kept, from its start and from its end, as the work shown: at most so
many steps, and at most so many symbols over their terms together (a big term costs its size on the
page, every step it appears in). -/
def keepFirst : Nat := 100
def keepLast : Nat := 20
def keepFirstSize : Nat := 20000
def keepLastSize : Nat := 10000

/-- Why a run of steps ended. -/
inductive Halt where
  /-- No step applies: the strategy's normal form. -/
  | done
  /-- The step count ran out. -/
  | fuel
  /-- The term grew past `maxSize`. -/
  | size
  deriving BEq, Repr, Inhabited

/-- A run of steps: where it ended and why, and the steps kept — the first `keepFirst`, and the last
`keepLast` after the term `lastFrom`, with `dropped` steps between them not kept. -/
structure Run (α : Type) where
  out : Term
  first : List (Term × α)
  lastFrom : Term
  last : List (Term × α)
  dropped : Nat
  halt : Halt

def Run.count (r : Run α) : Nat := r.first.length + r.dropped + r.last.length

/-- Drop the oldest of the latest steps while there are too many, or they are too big together; the
next kept step then starts from where the dropped one ended. -/
def trimLast (last : List (Term × α)) (sz : Nat) (base : Term) (dropped : Nat) : List (Term × α) × Nat × Term × Nat :=
  match last with
  | oldest :: rest@(_ :: _) =>
    if last.length > keepLast || sz > keepLastSize then trimLast rest (sz - size oldest.1) oldest.1 (dropped + 1)
    else (last, sz, base, dropped)
  | _ => (last, sz, base, dropped)

/-- Take steps until none applies, the fuel runs out, or the term grows past `maxSize`, keeping the
first and the last steps. -/
def runSteps (step : Term → Option (Term × α)) (t : Term) (fuel : Nat) : Run α :=
  go t fuel [] 0 true t [] 0 0
where
  /-- `first` is reversed, `last` oldest first, each with its terms' total size; `filling` until the
  first part is full; `base` is the term before `last`'s oldest. -/
  go (t : Term) : Nat → List (Term × α) → Nat → Bool → Term → List (Term × α) → Nat → Nat → Run α
    | 0, first, _, _, base, last, _, dropped => ⟨t, first.reverse, base, last, dropped, if (step t).isNone then .done else .fuel⟩
    | n + 1, first, fsz, filling, base, last, lsz, dropped =>
      match step t with
      | none => ⟨t, first.reverse, base, last, dropped, .done⟩
      | some (t', k) =>
        let z := size t'
        if filling && first.length < keepFirst && fsz + z ≤ keepFirstSize then
          if z > maxSize then ⟨t', ((t', k) :: first).reverse, t', [], dropped, .size⟩
          else go t' n ((t', k) :: first) (fsz + z) true t' last lsz dropped
        else
          let (last, lsz, base, dropped) := trimLast (last ++ [(t', k)]) (lsz + z) base dropped
          if z > maxSize then ⟨t', first.reverse, base, last, dropped, .size⟩
          else go t' n first fsz false base last lsz dropped

/-- Reduce to normal form in normal order: where the reduction stopped and why, and its steps. -/
def reduce (t : Term) : Run Bool := runSteps betaStep t maxSteps

/-- The binders' names, in order, each once. -/
def boundVars : Term → List String
  | .var _ => []
  | .lam x e => (x :: boundVars e).eraseDups
  | .app a b => (boundVars a ++ boundVars b).eraseDups

end Lam
end MathEngine
