import MathEngine.Systems
/-!
# Rewriting systems

A first-order rewriting system is a list of rules `l -> r` between terms built from function symbols
and variables. `rules(…)` declares one (a rule per line, or separated by `;`, optionally named
`name: l -> r`); a variable is `u`, `v`, `w`, `x`, `y` or `z`, perhaps with digits or primes (`x1`,
`y'`); any other bare name (`0`, `e`, `nil`) is a constant, and `f(t, u)` applies a symbol.

- `rewrite(R, t)` rewrites `t` to a normal form, leftmost-outermost, a step per rule application, at
  its position in the term;
- `terminates(R)` checks that every rule decreases a measure, so no term rewrites for ever: the size
  by default, or a linear interpretation of the symbols given after a `;`, as
  `terminates(R; add(x, y) = 2x + y, s(x) = x + 1)`. `RewritingProofs` proves the check sound;
- `critical(R)` finds the critical pairs, where two rules overlap, and rewrites both sides of each to
  normal form: all joinable means the system is locally confluent, and with termination confluent
  (Newman's lemma). `CriticalProofs` proves it: unification is complete and most general, no overlap
  is missed, and the critical pair lemma.
-/
namespace MathEngine
namespace TRS

/-- Terms: a variable, or a symbol applied to arguments (a constant has none). -/
inductive T where
  | v (x : String)
  | f (name : String) (args : List T)
  deriving Repr, Inhabited

mutual
/-- Equality of terms is decidable (written out: the deriving handler does not take nested types). -/
def T.decEq : (a b : T) → Decidable (a = b)
  | .v x, .v y => if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .f n as, .f m bs =>
    if h : n = m then
      match T.decEqArgs as bs with
      | isTrue h2 => isTrue (h ▸ h2 ▸ rfl)
      | isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
    else isFalse (fun e => by cases e; exact h rfl)
  | .v _, .f _ _ => isFalse (fun e => by cases e)
  | .f _ _, .v _ => isFalse (fun e => by cases e)
def T.decEqArgs : (as bs : List T) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | a :: as, b :: bs =>
    match T.decEq a b, T.decEqArgs as bs with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
end

instance : DecidableEq T := T.decEq

partial def T.toString : T → String
  | .v x => x
  | .f n [] => n
  | .f n as => s!"{n}({", ".intercalate (as.map T.toString)})"

instance : ToString T := ⟨T.toString⟩

partial def T.toExpr : T → Expr
  | .v x => .var x
  | .f n [] => .var n
  | .f n as => .fn n (as.map T.toExpr)

/-- A variable's name, as the textbooks write them: `u`, `v`, `w`, `x`, `y` or `z`, perhaps with digits
or primes (`x1`, `y'`). Any other name is a constant or a symbol (`a`, `e`, `nil`, `0`). -/
def isVarName (s : String) : Bool :=
  match s.toList with
  | c :: cs => "uvwxyz".contains c && cs.all fun d => d.isDigit || d == '\''
  | [] => false

/-! ## Parsing -/

inductive Tok where | ident (s : String) | lp | rp | comma | eof
  deriving BEq, Repr, Inhabited

partial def lex (s : String) : Except String (List Tok) := go s.toList []
where
  go : List Char → List Tok → Except String (List Tok)
    | [], acc => .ok (acc.reverse ++ [.eof])
    | c :: cs, acc =>
      if c.isWhitespace then go cs acc
      else if c == '(' then go cs (.lp :: acc)
      else if c == ')' then go cs (.rp :: acc)
      else if c == ',' then go cs (.comma :: acc)
      else if c.isAlphanum || c == '_' then
        let ds := (c :: cs).takeWhile fun d => d.isAlphanum || d == '_' || d == '\''
        go ((c :: cs).drop ds.length) (.ident (String.ofList ds) :: acc)
      else .error s!"unexpected character '{c}' in a term"

partial def parseT : List Tok → Except String (T × List Tok)
  | .ident n :: .lp :: ts => do
    let (as, ts) ← args ts []
    pure (.f n as, ts)
  | .ident n :: ts => pure (if isVarName n then .v n else .f n [], ts)
  | _ => throw "expected a term: a name, or name(…)"
where
  args (ts : List Tok) (acc : List T) : Except String (List T × List Tok) := do
    let (a, ts) ← parseT ts
    match ts with
    | .comma :: ts => args ts (a :: acc)
    | .rp :: ts => pure ((a :: acc).reverse, ts)
    | _ => throw "expected ',' or ')' in a term's arguments"

def parseTerm (s : String) : Except String T := do
  let (t, rest) ← parseT (← lex s)
  if rest == [.eof] then pure t else throw s!"unexpected input after the term in '{s.trimAscii}'"

/-! ## Terms -/

mutual
/-- The variables of a term, in order of appearance (with repeats). -/
def T.vars : T → List String
  | .v x => [x]
  | .f _ as => T.varsArgs as
def T.varsArgs : List T → List String
  | [] => []
  | a :: as => a.vars ++ T.varsArgs as
end

mutual
def T.size : T → Nat
  | .v _ => 1
  | .f _ as => 1 + T.sizeArgs as
def T.sizeArgs : List T → Nat
  | [] => 0
  | a :: as => a.size + T.sizeArgs as
end

abbrev Subst := List (String × T)

mutual
def T.subst (σ : Subst) : T → T
  | .v x => (σ.lookup x).getD (.v x)
  | .f n as => .f n (T.substArgs σ as)
def T.substArgs (σ : Subst) : List T → List T
  | [] => []
  | a :: as => a.subst σ :: T.substArgs σ as
end

mutual
/-- Match a pattern against a term, extending `σ`: the substitution that makes them equal. -/
def matchT (σ : Subst) : T → T → Option Subst
  | .v x, t => match σ.lookup x with
    | some u => if u == t then some σ else none
    | none => some ((x, t) :: σ)
  | .f n as, .f m bs => if n == m then matchArgs σ as bs else none
  | .f _ _, .v _ => none
def matchArgs (σ : Subst) : List T → List T → Option Subst
  | [], [] => some σ
  | a :: as, b :: bs => (matchT σ a b).bind (matchArgs · as bs)
  | _, _ => none
end

/-- Positions: the path of argument indices to a subterm (as `Expr` paths: argument `i` is child `i`). -/
abbrev Pos := List Nat

mutual
def T.replace : T → Pos → T → T
  | _, [], u => u
  | .f n as, i :: p, u => .f n (T.replaceArgs as i p u)
  | t, _ :: _, _ => t
/-- Replace, in argument `i`, the subterm at `p`. -/
def T.replaceArgs : List T → Nat → Pos → T → List T
  | [], _, _, _ => []
  | a :: as, 0, p, u => a.replace p u :: as
  | a :: as, i + 1, p, u => a :: T.replaceArgs as i p u
end

mutual
/-- The subterm at a position. -/
def T.at? : T → Pos → Option T
  | t, [] => some t
  | .f _ as, i :: p => T.atArgs as i p
  | .v _, _ :: _ => none
/-- The subterm at `p` in argument `i`. -/
def T.atArgs : List T → Nat → Pos → Option T
  | [], _, _ => none
  | a :: _, 0, p => a.at? p
  | _ :: as, i + 1, p => T.atArgs as i p
end

mutual
/-- The non-variable positions of a term, outermost first, left to right. -/
def T.positions : T → List Pos
  | .v _ => []
  | .f _ as => [] :: T.positionsArgs as 0
/-- The positions in the arguments, from argument `i` on. -/
def T.positionsArgs : List T → Nat → List Pos
  | [], _ => []
  | a :: as, i => a.positions.map (i :: ·) ++ T.positionsArgs as (i + 1)
end

/-! ## Systems -/

structure Rule where
  name : String
  lhs : T
  rhs : T

structure System where
  rules : List Rule

def Rule.toExpr (ρ : Rule) : Expr := .fn "→" [ρ.lhs.toExpr, ρ.rhs.toExpr]

/-- A rule as written: `l -> r`, or `name: l -> r`. -/
def parseRule (k : Nat) (c : String) : Except String Rule := do
  let (name, body) := match c.splitOn ":" with
    | [n, b] =>
      let n := n.trimAscii.copy
      if !n.isEmpty && n.all (fun (ch : Char) => ch.isAlphanum || ch == '_') then (n, b) else (s!"r{k}", c)
    | _ => (s!"r{k}", c)
  match body.splitOn "->" with
  | [l, r] =>
    let lhs ← parseTerm l
    let rhs ← parseTerm r
    if let .v _ := lhs then throw s!"rule {name}: the left side is a variable, so it would rewrite every term"
    let extra := rhs.vars.filter (!lhs.vars.contains ·)
    if !extra.isEmpty then throw s!"rule {name}: {", ".intercalate extra.eraseDups} on the right does not occur on the left"
    pure ⟨name, lhs, rhs⟩
  | _ => throw s!"write a rule as l -> r, not '{c.trimAscii}'"

def parseSystem (body : String) : Except String System := do
  let cs := Sys.clauses body
  if cs.isEmpty then throw "a rewriting system needs rules: rules(l -> r, …)"
  let rules ← (cs.zipIdx.map fun (c, i) => (c, i + 1)).mapM fun (c, k) => parseRule k c
  if (rules.map (·.name)).eraseDups.length != rules.length then throw "two rules share a name"
  pure ⟨rules⟩

/-- The first rule that matches a term at its root, with the substitution. -/
def rootRedex (S : System) (t : T) : Option (Rule × Subst) :=
  S.rules.findSome? fun ρ => (matchT [] ρ.lhs t).map (ρ, ·)

mutual
/-- One rewrite step at the leftmost-outermost redex: the rule, the position, and the result. The
search stops at the first redex, so a step costs a walk of the term at most. -/
def step (S : System) : T → Option (Rule × Pos × T)
  | t@(.v _) => (rootRedex S t).map fun (ρ, σ) => (ρ, [], ρ.rhs.subst σ)
  | t@(.f n as) =>
    match rootRedex S t with
    | some (ρ, σ) => some (ρ, [], ρ.rhs.subst σ)
    | none => (stepArgs S as 0).map fun (ρ, p, as') => (ρ, p, .f n as')
/-- A step in the first argument that has one: the rule, the position from the arguments, and the
new arguments. -/
def stepArgs (S : System) : List T → Nat → Option (Rule × Pos × List T)
  | [], _ => none
  | a :: as, i =>
    match step S a with
    | some (ρ, p, a') => some (ρ, i :: p, a' :: as)
    | none => (stepArgs S as (i + 1)).map fun (ρ, p, as') => (ρ, p, a :: as')
end

def maxSteps : Nat := 10000
def maxSize : Nat := 6000

/-- Rewrite to a normal form, recording each step; `none` when the budget runs out first. -/
def normalize (S : System) (t : T) (fuel : Nat := maxSteps) : List (Rule × Pos × T) × T × Bool :=
  go t fuel []
where
  go (t : T) : Nat → List (Rule × Pos × T) → List (Rule × Pos × T) × T × Bool
    | 0, acc => (acc.reverse, t, (step S t).isNone)
    | n + 1, acc =>
      match step S t with
      | none => (acc.reverse, t, true)
      | some (ρ, p, t') => if t'.size > maxSize then ((ρ, p, t') :: acc).reverse |> (·, t', false) else go t' n ((ρ, p, t') :: acc)

/-! ## Termination by a linear interpretation -/

/-- A linear interpretation of a symbol: a constant and a coefficient per argument. -/
structure Interp where
  const : Nat
  coeffs : List Nat
  deriving Repr, Inhabited

/-- The size interpretation: one for the symbol, plus each argument. -/
def sizeInterp (arity : Nat) : Interp := ⟨1, List.replicate arity 1⟩

/-- The interpretation of `f` with `n` arguments: the one given, when it has a coefficient of at
least one per argument, else the size. `RewritingProofs` needs both: an argument without a
coefficient, or with a zero one, could grow without the term growing. -/
def interpOf (given : List (String × Interp)) (f : String) (n : Nat) : Interp :=
  match given.lookup f with
  | some i => if i.coeffs.length == n && i.coeffs.all (· ≥ 1) then i else sizeInterp n
  | none => sizeInterp n

/-- A linear form: a constant and a coefficient per variable. -/
structure Lin where
  const : Nat
  coef : List (String × Nat)
  deriving Repr, Inhabited

/-- A variable's coefficient: the sum of its entries (a form may list a variable more than once). -/
def Lin.get (L : Lin) (x : String) : Nat := ((L.coef.filter (·.1 == x)).map (·.2)).sum

/-- The variables a form mentions, each once. -/
def Lin.keys (L : Lin) : List String := (L.coef.map (·.1)).eraseDups

def Lin.add (a b : Lin) : Lin := ⟨a.const + b.const, a.coef ++ b.coef⟩

def Lin.scale (k : Nat) (a : Lin) : Lin := ⟨k * a.const, a.coef.map fun (x, c) => (x, k * c)⟩

mutual
/-- A term's interpretation as a linear form in its variables. -/
def lin (I : String → Nat → Interp) : T → Lin
  | .v x => ⟨0, [(x, 1)]⟩
  | .f n as => (linArgs I (I n as.length).coeffs as).add ⟨(I n as.length).const, []⟩
/-- The arguments' forms, each scaled by its coefficient, added up. -/
def linArgs (I : String → Nat → Interp) : List Nat → List T → Lin
  | c :: cs, a :: as => ((lin I a).scale c).add (linArgs I cs as)
  | _, _ => ⟨0, []⟩
end

def Lin.text (L : Lin) : String :=
  let parts := (L.keys.map fun x => (x, L.get x)).filter (·.2 != 0) |>.map (fun (x, c) => if c == 1 then x else s!"{c}{x}")
  let parts := parts ++ (if L.const != 0 || parts.isEmpty then [toString L.const] else [])
  " + ".intercalate parts

/-- Every assignment makes `l` larger than `r`: a larger constant and no smaller coefficient. -/
def decreases (l r : Lin) : Bool :=
  l.const > r.const && r.keys.all fun x => decide (l.get x ≥ r.get x)

/-- An interpretation as written: `add(x, y) = 2x + y`. -/
def parseInterp (c : String) : Except String (String × Interp) := do
  match c.splitOn "=" with
  | [lhs, rhs] =>
    let head ← parseTerm lhs
    match head with
    | .f n args =>
      let params ← args.mapM fun a => match a with
        | .v x => pure x
        | _ => throw s!"in {lhs.trimAscii}, the arguments are variables"
      let terms := (rhs.splitOn "+").map (·.trimAscii.copy)
      let mut const := 0
      let mut coeffs := params.map fun _ => 0
      for term in terms do
        let ds := term.toList.takeWhile Char.isDigit
        let rest := String.ofList ((term.toList.drop ds.length).filter (fun c => c != '*' && !c.isWhitespace))
        let k := if ds.isEmpty then 1 else (String.ofList ds).toNat!
        if rest.isEmpty then const := const + k
        else match params.idxOf? rest with
          | some i => coeffs := coeffs.modify i (· + k)
          | none => throw s!"{rest} is not an argument of {n}"
      if coeffs.any (· == 0) then throw s!"every argument of {n} needs a coefficient of at least 1, so that a smaller argument makes a smaller term"
      pure (n, ⟨const, coeffs⟩)
    | .v _ => throw s!"write an interpretation as f(x, y) = 2x + y + 1, not '{c.trimAscii}'"
  | _ => throw s!"write an interpretation as f(x, y) = 2x + y + 1, not '{c.trimAscii}'"

/-- Split at the top-level commas. -/
def topCommas (s : String) : List String :=
  let rec go : List Char → Nat → List Char → List String → List String
    | [], _, cur, acc => (String.ofList cur.reverse :: acc).reverse
    | c :: cs, d, cur, acc =>
      if c == ',' && d == 0 then go cs d [] (String.ofList cur.reverse :: acc)
      else if c == '(' then go cs (d + 1) (c :: cur) acc
      else if c == ')' then go cs (d - 1) (c :: cur) acc
      else go cs d (c :: cur) acc
  (go s.toList 0 [] []).map (·.trimAscii.copy) |>.filter (· != "")

/-! ## Unification and critical pairs -/

mutual
def T.occurs (x : String) : T → Bool
  | .v y => x == y
  | .f _ as => T.occursArgs x as
def T.occursArgs (x : String) : List T → Bool
  | [] => false
  | a :: as => a.occurs x || T.occursArgs x as
end

/-- The distinct names of a list, each once. -/
def dedup : List String → List String
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup {y : String} : ∀ {l : List String}, y ∈ dedup l ↔ y ∈ l
  | [] => by simp [dedup]
  | x :: xs => by
    have ih := @mem_dedup y xs
    unfold dedup
    split
    · rename_i h
      by_cases e : y = x
      · subst e; simp [h]
      · simp [ih, e]
    · simp [ih]

theorem nodup_dedup : ∀ l : List String, (dedup l).Nodup
  | [] => by simp [dedup]
  | x :: xs => by
    unfold dedup
    split
    · exact nodup_dedup xs
    · rename_i h; exact List.nodup_cons.2 ⟨h, nodup_dedup xs⟩

theorem dedup_length_le {l₁ l₂ : List String} (h : ∀ y ∈ l₁, y ∈ l₂) :
    (dedup l₁).length ≤ (dedup l₂).length :=
  (nodup_dedup l₁).length_le_of_subset fun _ hy => mem_dedup.2 (h _ (mem_dedup.1 hy))

theorem dedup_length_lt {l₁ l₂ : List String} {x : String} (h : ∀ y ∈ l₁, y ∈ l₂) (hx : x ∈ l₂)
    (hx' : x ∉ l₁) : (dedup l₁).length < (dedup l₂).length := by
  have hn : (x :: dedup l₁).Nodup := List.nodup_cons.2 ⟨fun e => hx' (mem_dedup.1 e), nodup_dedup l₁⟩
  have := hn.length_le_of_subset (l₂ := dedup l₂) fun y hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact mem_dedup.2 hx
    · exact mem_dedup.2 (h _ (mem_dedup.1 hy))
  simp at this; omega

mutual
theorem occurs_iff {x : String} : ∀ t : T, t.occurs x = true ↔ x ∈ t.vars
  | .v y => by simp [T.occurs, T.vars]
  | .f _ as => by simp [T.occurs, T.vars, occursArgs_iff as]
theorem occursArgs_iff {x : String} : ∀ as : List T, T.occursArgs x as = true ↔ x ∈ T.varsArgs as
  | [] => by simp [T.occursArgs, T.varsArgs]
  | a :: as => by simp [T.occursArgs, T.varsArgs, occurs_iff a, occursArgs_iff as]
end

mutual
/-- Binding `x` to `u` leaves no `x` and adds only `u`'s variables. -/
theorem mem_vars_subst1 {x y : String} {u : T} : ∀ t : T, y ∈ (t.subst [(x, u)]).vars →
    (y ∈ t.vars ∧ y ≠ x) ∨ y ∈ u.vars
  | .v z, h => by
    by_cases e : z = x
    · subst e; simp [T.subst] at h; exact .inr h
    · have : (z == x) = false := by simp [e]
      simp [T.subst, List.lookup, this, T.vars] at h
      subst h; exact .inl ⟨by simp [T.vars], e⟩
  | .f _ as, h => by
    simp only [T.subst, T.vars] at h ⊢
    exact mem_varsArgs_subst1 as h
theorem mem_varsArgs_subst1 {x y : String} {u : T} : ∀ as : List T,
    y ∈ T.varsArgs (T.substArgs [(x, u)] as) → (y ∈ T.varsArgs as ∧ y ≠ x) ∨ y ∈ u.vars
  | [], h => by simp [T.substArgs, T.varsArgs] at h
  | a :: as, h => by
    simp only [T.substArgs, T.varsArgs, List.mem_append] at h ⊢
    rcases h with h | h
    · rcases mem_vars_subst1 a h with ⟨h1, h2⟩ | h
      · exact .inl ⟨.inl h1, h2⟩
      · exact .inr h
    · rcases mem_varsArgs_subst1 as h with ⟨h1, h2⟩ | h
      · exact .inl ⟨.inr h1, h2⟩
      · exact .inr h
end

/-- The variables of a list of equations, and its size: each step of `unify` removes a variable from
the equations or makes them smaller, so it stops. -/
def eqsVars : List (T × T) → List String
  | [] => []
  | (s, t) :: rest => s.vars ++ t.vars ++ eqsVars rest

def eqsSize : List (T × T) → Nat
  | [] => 0
  | (s, t) :: rest => s.size + t.size + eqsSize rest

/-- Bind `x` to `u` in some equations. -/
def elim (x : String) (u : T) (eqs : List (T × T)) : List (T × T) :=
  eqs.map fun (a, b) => (a.subst [(x, u)], b.subst [(x, u)])

/-- Bind `x` to `u` in a substitution: in what it binds already, and then `x` itself. -/
def extend (x : String) (u : T) (σ : Subst) : Subst :=
  (x, u) :: σ.map fun (y, w) => (y, w.subst [(x, u)])

theorem mem_eqsVars_elim {x y : String} {u : T} : ∀ eqs : List (T × T), y ∈ eqsVars (elim x u eqs) →
    (y ∈ eqsVars eqs ∧ y ≠ x) ∨ y ∈ u.vars
  | [], h => by simp [elim, eqsVars] at h
  | (a, b) :: rest, h => by
    simp only [elim, List.map_cons, eqsVars, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · rcases mem_vars_subst1 a h with ⟨h1, h2⟩ | h
      · exact .inl ⟨.inl (.inl h1), h2⟩
      · exact .inr h
    · rcases mem_vars_subst1 b h with ⟨h1, h2⟩ | h
      · exact .inl ⟨.inl (.inr h1), h2⟩
      · exact .inr h
    · rcases mem_eqsVars_elim rest h with ⟨h1, h2⟩ | h
      · exact .inl ⟨.inr h1, h2⟩
      · exact .inr h

theorem mem_eqsVars_zip {y : String} : ∀ (as bs : List T), y ∈ eqsVars (as.zip bs) →
    y ∈ T.varsArgs as ∨ y ∈ T.varsArgs bs
  | [], _, h => by simp [eqsVars] at h
  | _ :: _, [], h => by simp [eqsVars] at h
  | a :: as, b :: bs, h => by
    simp only [List.zip_cons_cons, eqsVars, T.varsArgs, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact .inl (.inl h)
    · exact .inr (.inl h)
    · rcases mem_eqsVars_zip as bs h with h | h
      · exact .inl (.inr h)
      · exact .inr (.inr h)

theorem eqsSize_zip : ∀ (as bs : List T), eqsSize (as.zip bs) ≤ T.sizeArgs as + T.sizeArgs bs
  | [], _ => by simp [eqsSize]
  | _ :: _, [] => by simp [eqsSize, T.sizeArgs]
  | a :: as, b :: bs => by
    simp only [List.zip_cons_cons, eqsSize, T.sizeArgs]
    have := eqsSize_zip as bs
    omega

theorem eqsVars_append (a b : List (T × T)) : eqsVars (a ++ b) = eqsVars a ++ eqsVars b := by
  induction a with
  | nil => rfl
  | cons p a ih => obtain ⟨s, t⟩ := p; simp [eqsVars, ih]

theorem eqsSize_append (a b : List (T × T)) : eqsSize (a ++ b) = eqsSize a + eqsSize b := by
  induction a with
  | nil => simp [eqsSize]
  | cons p a ih => obtain ⟨s, t⟩ := p; simp [eqsSize, ih]; omega

theorem lex_le_lt {a₁ a₂ b₁ b₂ : Nat} (ha : a₁ ≤ a₂) (hb : b₁ < b₂) :
    Prod.Lex (· < ·) (· < ·) (a₁, b₁) (a₂, b₂) := by
  rcases Nat.lt_or_eq_of_le ha with h | rfl
  · exact .left _ _ h
  · exact .right _ hb

theorem T.size_pos : ∀ t : T, 0 < t.size
  | .v _ => by simp [T.size]
  | .f _ _ => by simp only [T.size]; omega

/-- Binding a variable of the equations, which does not occur in what it is bound to, removes it. -/
theorem elim_lt {x : String} {u : T} {rest : List (T × T)} {all : List String} (hx : x ∈ all)
    (hu : x ∉ u.vars) (h : ∀ y, (y ∈ eqsVars rest ∧ y ≠ x) ∨ y ∈ u.vars → y ∈ all) :
    (dedup (eqsVars (elim x u rest))).length < (dedup all).length :=
  dedup_length_lt (fun y hy => h y (mem_eqsVars_elim rest hy)) hx fun hm => by
    rcases mem_eqsVars_elim rest hm with ⟨_, h⟩ | h
    · exact h rfl
    · exact hu h

/-- Most general unifier, by Robinson's algorithm. Each variable bound is replaced in the equations
left and in the substitution so far, so the substitution never mentions a variable it binds. -/
def unify (eqs : List (T × T)) (σ : Subst) : Option Subst :=
  match eqs with
  | [] => some σ
  | (.v x, u) :: rest =>
    if .v x = u then unify rest σ
    else if u.occurs x then none
    else unify (elim x u rest) (extend x u σ)
  | (.f n as, .v x) :: rest =>
    if (T.f n as).occurs x then none
    else unify (elim x (.f n as) rest) (extend x (.f n as) σ)
  | (.f n as, .f m bs) :: rest =>
    if T.f n as = .f m bs then unify rest σ
    else if n != m || as.length != bs.length then none
    else unify (as.zip bs ++ rest) σ
termination_by ((dedup (eqsVars eqs)).length, eqsSize eqs)
decreasing_by
  · exact lex_le_lt (dedup_length_le fun y h => by simp [eqsVars, h])
      (by have := T.size_pos u; simp [eqsSize, T.size]; omega)
  · exact Prod.Lex.left _ _ (elim_lt (by simp [eqsVars, T.vars]) (by rwa [occurs_iff] at *)
      fun y h => by rcases h with ⟨h, _⟩ | h <;> simp [eqsVars, h])
  · exact Prod.Lex.left _ _ (elim_lt (by simp [eqsVars, T.vars]) (by rwa [occurs_iff] at *)
      fun y h => by rcases h with ⟨h, _⟩ | h <;> simp [eqsVars, h])
  · exact lex_le_lt (dedup_length_le fun y h => by simp [eqsVars, h])
      (by simp only [eqsSize, T.size]; omega)
  · refine lex_le_lt (dedup_length_le fun y h => ?_) ?_
    · rw [eqsVars_append, List.mem_append] at h
      simp only [eqsVars, T.vars, List.mem_append]
      rcases h with h | h
      · rcases mem_eqsVars_zip as bs h with h | h <;> simp [h]
      · simp [h]
    · have := eqsSize_zip as bs
      simp only [eqsSize_append, eqsSize, T.size]
      omega

mutual
/-- Rename a rule's variables apart, with a suffix. -/
def T.rename (k : String) : T → T
  | .v x => .v (x ++ k)
  | .f n as => .f n (T.renameArgs k as)
def T.renameArgs (k : String) : List T → List T
  | [] => []
  | a :: as => a.rename k :: T.renameArgs k as
end

/-- The suffix for the second rule's variables `V₂`, when the first rule's `V₁` take one prime: two
primes, unless that gives two variables one name (`x'` and `x`, primed once and twice), and then more
primes than any name of the first rule is long, so that every name of the second is longer. -/
def apart (V₁ V₂ : List String) : String :=
  if V₁.all fun x => V₂.all fun y => x ++ "'" != y ++ "''" then "''"
  else String.ofList (List.replicate ((V₁.map String.length).foldr max 0 + 2) '\'')

/-- Rename the variables of some terms, in order of appearance, back to their names without the
primes that kept two rules apart, where no other variable has that name already. The renaming is
checked to be undone by its inverse (it always is), so the terms are only renamed. -/
def tidy (ts : List T) : List T :=
  let vs := (ts.map T.vars).flatten.eraseDups
  let base (v : String) := String.ofList (v.toList.reverse.dropWhile (· == '\'')).reverse
  let (σ, κ, _) := vs.foldl (fun ((σ : Subst), (κ : Subst), (used : List String)) v =>
      let cands := (List.range (vs.length + 1)).map fun k => base v ++ String.ofList (List.replicate k '\'')
      let n := (cands.find? (!used.contains ·)).getD v
      ((v, T.v n) :: σ, (n, T.v v) :: κ, n :: used)) ([], [], [])
  let ts' := ts.map (·.subst σ)
  if ts'.map (·.subst κ) = ts then ts' else ts

/-- A critical pair: rules `ρ₁` (at the root of the overlap) and `ρ₂` (at position `p` in it), the
overlapping term, and its two results. -/
structure Critical where
  outer : Rule
  inner : Rule
  pos : Pos
  peak : T
  left : T
  right : T

/-- The overlaps of `ρ₂` on `ρ₁`: at each non-variable position of `ρ₁`'s left side (but the root, when
the two are one rule), the subterm there unified with `ρ₂`'s left side, the two rules' variables
renamed apart (`apart`). -/
def criticalOf (ρ₁ ρ₂ : Rule) (same : Bool) : List Critical :=
  let k := apart (ρ₁.lhs.vars ++ ρ₁.rhs.vars) (ρ₂.lhs.vars ++ ρ₂.rhs.vars)
  let l₁ := ρ₁.lhs.rename "'"
  let r₁ := ρ₁.rhs.rename "'"
  let l₂ := ρ₂.lhs.rename k
  let r₂ := ρ₂.rhs.rename k
  l₁.positions.filterMap fun p =>
    if p.isEmpty && same then none else
    match l₁.at? p with
    | none => none
    | some sub =>
      match unify [(sub, l₂)] [] with
      | none => none
      | some σ =>
        match tidy [l₁.subst σ, r₁.subst σ, (l₁.replace p r₂).subst σ] with
        | [peak, left, right] => some ⟨ρ₁, ρ₂, p, peak, left, right⟩
        | _ => none

/-- Every critical pair of a system: each rule on each, in order. -/
def critical (S : System) : List Critical :=
  S.rules.zipIdx.flatMap fun (ρ₁, i) => S.rules.zipIdx.flatMap fun (ρ₂, j) => criticalOf ρ₁ ρ₂ (i == j)

/-- The pair is a real overlap: the peak rewrites to `left` by the outer rule at the root, and to
`right` by the inner rule at the position (`isPeak_sound`, `RewritingProofs.lean`). -/
def Critical.isPeak (c : Critical) : Bool :=
  (match matchT [] c.outer.lhs c.peak with
   | some σ => c.outer.rhs.subst σ == c.left
   | none => false) &&
  (match c.peak.at? c.pos with
   | some s =>
     match matchT [] c.inner.lhs s with
     | some σ => c.peak.replace c.pos (c.inner.rhs.subst σ) == c.right
     | none => false
   | none => false)

end TRS
end MathEngine
