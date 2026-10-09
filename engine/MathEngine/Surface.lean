import MathEngine.Parser
import MathEngine.Logic
/-!
# A world cell's input as written

A math cell's input reading is the parse the pipeline starts from: the cell as typed. The other
worlds' readings are not: a `system` is read as its variables and actions, `le(C, a, c)` as the
element it asks about, `poset(…)` as its carrier. Those are the values the worlds compute with, and
the derivation keeps them; what the notebook shows as the input, and what a reader hovers to see how
an operator binds, is this: the input as written.

It is read without the worlds' semantics. A world's notation is math between separators: calls
whose arguments are separated by `,`, `;` and line breaks, keywords (`var … in`, `init`,
`action … when … do`), arrows and assignments (`->`, `<-`, `:=`, `↦`), ranges (`0..2`) and sets.
The text is cut at those, and each piece between them is read by the grammar it is written in: a
formula (`p = done ∧ q = done → x = 2`) by `Logic.parseFormula`, an expression by `MathEngine.parse`.
Binding happens inside the pieces, where those grammars decide it; between them the separators are
written as they are.

Separators are literal pieces of a node (`tpl`), not subterms: the printer writes them without a
path, so every labelled subterm is something the reader wrote, in the order they wrote it, and the
notebook can find each one in the source.
-/
namespace MathEngine.Surface

/-- A node whose children sit between literal pieces: `pieces` has one more entry than `kids`, each
the LaTeX and the text written there. The pieces travel as the node's first argument, which the
printer (`printPieces`) does not print: it writes the pieces unlabelled and labels the children,
the first at index 1. -/
def tpl (pieces : List (String × String)) (kids : List Expr) : Expr :=
  .fn "§" (.var ("␟".intercalate (pieces.map fun (l, t) => l ++ "␞" ++ t)) :: kids)

private def isOpen (c : Char) : Bool := c == '(' || c == '[' || c == '{'
private def isClose (c : Char) : Bool := c == ')' || c == ']' || c == '}'

/-- The index of the bracket that closes the one `cs` starts with. -/
private def closing (cs : List Char) : Option Nat := go cs 0 0
where
  go : List Char → Nat → Nat → Option Nat
    | [], _, _ => none
    | c :: rest, i, d =>
      if isOpen c then go rest (i + 1) (d + 1)
      else if isClose c then (if d == 1 then some i else go rest (i + 1) (d - 1))
      else go rest (i + 1) d

private def trimL (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

private def ident (c : Char) : Bool := Logic.identChar c

/-- The separator `cs` starts with, if any (the first of `seps` that fits): a word only as a word
of its own, not the start or the end of a longer name. `prev` is the character before. -/
private def sepAt (seps : List String) (prev : Option Char) (cs : List Char) : Option String :=
  seps.find? fun s =>
    let sc := s.toList
    cs.take sc.length == sc &&
      -- `x<-1` compares with -1, as the editor reads it; `b <- m` is a message's arrow
      !(s == "<-" && ((cs.drop 2).head?.map fun c => c.isDigit || c == '.').getD false) &&
      (!(sc.head?.map ident).getD false ||
        (!(prev.map ident).getD false && !((cs.drop sc.length).head?.map ident).getD false))

/-- `cs` cut at `seps` outside brackets: the pieces (one more than the separators) and the
separators found. -/
private partial def splitTop (seps : List String) (cs : List Char) : List (List Char) × List String :=
  go cs none 0 [] #[] #[]
where
  go : List Char → Option Char → Nat → List Char → Array (List Char) → Array String → List (List Char) × List String
    | [], _, _, cur, items, ss => ((items.push cur.reverse).toList, ss.toList)
    | c :: rest, prev, d, cur, items, ss =>
      match (if d == 0 then sepAt seps prev (c :: rest) else none) with
      | some s =>
        let n := s.toList.length
        go ((c :: rest).drop n) (s.toList.getLast?) 0 [] (items.push cur.reverse) (ss.push s)
      | none =>
        let d := if isOpen c then d + 1 else if isClose c && d > 0 then d - 1 else d
        go rest (some c) d (c :: cur) items ss

/-- How a separator is written: its LaTeX and its text. -/
private def written : String → String × String
  | ";" => (";\\ ", "; ")
  | "," => (",\\ ", ", ")
  | "\n" => ("\\\\ ", "\n")
  | ":=" => (" \\coloneqq ", " := ")
  | "->" => (" \\to ", " -> ")
  | "→" => (" \\to ", " → ")
  | "<-" => (" \\leftarrow ", " <- ")
  | "↦" => (" \\mapsto ", " ↦ ")
  | ".." => ("..", "..")
  | ":" => (":\\ ", ": ")
  | "≠" | "!=" => (" \\ne ", " ≠ ")
  | "≤" | "<=" => (" \\le ", " ≤ ")
  | "≥" | ">=" => (" \\ge ", " ≥ ")
  | "=" => (" = ", " = ")
  | "<" => (" < ", " < ")
  | ">" => (" > ", " > ")
  | " " => ("\\ ", " ")
  | w => ("\\mathsf{" ++ w ++ "}\\ ", w ++ " ")

private def join (a b : String × String) : String × String := (a.1 ++ b.1, a.2 ++ b.2)

/-- A `tpl` from pieces and the separators between them, opened and closed by `opn` and `cls`: an
empty piece is no child, its separators run on into the next literal. -/
private def weave (opn cls : String × String) (items : List (List Char)) (seps : List String)
    (kid : List Char → Expr) : Expr :=
  let rec go : List (List Char) → List String → String × String → Array (String × String) → Array Expr →
      Array (String × String) × Array Expr
    | [], _, pend, pieces, kids => (pieces.push (join pend cls), kids)
    | it :: rest, seps, pend, pieces, kids =>
      let (pend, pieces, kids) :=
        if (trimL it).isEmpty then (pend, pieces, kids) else (("", ""), pieces.push pend, kids.push (kid it))
      -- a keyword is spaced from what stands before it, not from the start of a line
      let spaced (s : String) : String × String :=
        if (s.toList.head?.map ident).getD false && !kids.isEmpty && pend == ("", "") then join ("\\ ", " ") (written s) else written s
      match seps with
      | s :: ss => go rest ss (join pend (spaced s)) pieces kids
      | [] => go rest [] pend pieces kids
  let (pieces, kids) := go items seps opn #[] #[]
  tpl pieces.toList kids.toList

/-- `name(…)` to the end of `cs`: the name and what the brackets hold. -/
private def callParts (cs : List Char) : Option (String × List Char) :=
  let name := cs.takeWhile ident
  let rest := cs.drop name.length
  if name.isEmpty || (name.head?.map Char.isDigit).getD true then none else
  match rest with
  | '(' :: _ => if closing rest == some (rest.length - 1) then some (String.ofList name, (rest.drop 1).dropLast) else none
  | _ => none

/-- Whether a piece is a formula: it has a connective, a comparison or a quantifier, in glyphs or
in words (`and`, `->`, `<=`). -/
private def formulaish (s : String) : Bool :=
  (Logic.glyphs s).toList.any fun c => "∧∨¬→↔≤≥≠<>=∀∃∣".toList.contains c

/-- The separators of the worlds' notation inside an argument, longest first; the words are
keywords. A piece is cut at these before any grammar reads it (`init x = 0` is `init` and a
formula, not the product `init·x`). -/
private def worldSeps : List String :=
  [":=", "<-", "↦", "..", ":", "strong", "weak", "fair", "action", "when", "do", "init", "var", "in"]

/-- `worldSeps` and the arrows, which a formula reads as implication (`p -> q`), so a piece is cut
at them only when it is no formula (`1 -> 2` in a map). -/
private def innerSeps : List String := ":=" :: "->" :: "→" :: worldSeps.tail

mutual
  /-- One piece of a world's input, as written. -/
  partial def item (cs0 : List Char) : Expr :=
    let cs := trimL cs0
    let s := String.ofList cs
    match callParts cs with
    | some (name, inner) =>
      if MathEngine.builtinFunctions.contains name then
        match MathEngine.parse s with
        | .ok e => e
        | .error _ => call name inner
      else call name inner
    | none =>
    if cs.head? == some '{' && closing cs == some (cs.length - 1) then
      let (items, _) := splitTop [","] ((cs.drop 1).dropLast)
      .fn "set" ((items.filter fun it => !(trimL it).isEmpty).map item)
    else if cs.head? == some '[' && closing cs == some (cs.length - 1) && cs.contains '{' then
      -- a table of sets (`op` on subsets): each entry read as a set, not as a name spelled with braces
      let (items, seps) := splitTop [";", ","] ((cs.drop 1).dropLast)
      tpl ((("\\begin{bmatrix}", "[") :: seps.map (fun s => if s == ";" then (" \\\\ ", "; ") else (" & ", ", "))) ++ [("\\end{bmatrix}", "]")])
        (items.map item)
    else if cs.head? == some '(' && closing cs == some (cs.length - 1) then
      let (items, seps) := splitTop [","] ((cs.drop 1).dropLast)
      weave ("\\left(", "(") ("\\right)", ")") items seps item
    else if !(splitTop worldSeps cs).2.isEmpty then apart cs
    else if formulaish s then
      match Logic.parseFormula s with
      | .ok f => f.toExpr
      | .error _ => apart cs
    else match MathEngine.parse s with
      | .ok e => e
      | .error _ => apart cs

  /-- A call of a world's command: its arguments, separated as written, a line each when it has
  several lines (a `system`'s declarations). -/
  partial def call (name : String) (inner : List Char) : Expr :=
    -- a system's clauses are lines (or `;`): a comma is inside a clause, between its updates
    let (items, seps) := splitTop (if name == "system" then [";", "\n"] else [";", ",", "\n"]) (trimL inner)
    let head := if ["sin", "cos", "tan", "arcsin", "arccos", "arctan", "exp", "ln", "log", "arg"].contains name
      then "\\" ++ name else "\\operatorname{" ++ name ++ "}"
    if seps.contains "\n" then
      weave (head ++ "\\left(\\begin{array}{l}", name ++ "(") ("\\end{array}\\right)", ")") items seps item
    else
      weave (head ++ "\\left(", name ++ "(") ("\\right)", ")") items seps item

  /-- A piece no grammar reads whole: cut at the worlds' separators and keywords, else at its
  comparisons (`add(x, y) = 2x + y`, each side an expression), else into words. -/
  partial def apart (cs : List Char) : Expr :=
    let (items, seps) := splitTop innerSeps cs
    -- what stands between two separators may be a list (`do x := a, p := done` has `a, p`)
    let listed (it : List Char) : Expr :=
      let (is, ss) := splitTop [","] it
      if ss.isEmpty then item it else weave ("", "") ("", "") is ss item
    if !seps.isEmpty then weave ("", "") ("", "") items seps listed else
    let (items, seps) := splitTop ["≠", "≤", "≥", "<=", ">=", "!=", "=", "<", ">"] cs
    if !seps.isEmpty && items.all (fun it => !(trimL it).isEmpty) then weave ("", "") ("", "") items seps item
    else words cs

  /-- Words: each a name or a number where it is one, else written as it is. -/
  partial def words (cs : List Char) : Expr :=
    let (items, seps) := splitTop [" "] cs
    match items.filter fun it => !(trimL it).isEmpty with
    | [w] =>
      let s := String.ofList (trimL w)
      if s.toList.all ident then (match MathEngine.parse s with | .ok e => e | .error _ => .var s)
      else if (callParts (trimL w)).isSome || w.head? == some '{' then item w
      else tpl [(s, s)] []
    | _ => weave ("", "") ("", "") items seps words
end

/-- A world cell's input as written, after its `let name =` head. -/
def asWritten (src : String) : Expr :=
  let cs := trimL src.toList
  let body := match cs with
    | 'l' :: 'e' :: 't' :: ' ' :: rest =>
      let rest := rest.dropWhile Char.isWhitespace
      let name := rest.takeWhile ident
      match (rest.drop name.length).dropWhile Char.isWhitespace with
      | '=' :: more => if name.isEmpty then cs else more
      | _ => cs
    | _ => cs
  item body

/-- Whether the cell is a call of a command, `head(…)` (after a `let` head): a logic cell's input
is read as written only then; a statement (`∀ n ∈ 1..10, …`) keeps its own reading. -/
def isCall (src : String) : Bool :=
  let cs := trimL src.toList
  let cs := match cs with
    | 'l' :: 'e' :: 't' :: ' ' :: rest => ((rest.dropWhile (· != '=')).drop 1).dropWhile Char.isWhitespace
    | _ => cs
  (callParts (trimL cs)).isSome

end MathEngine.Surface
