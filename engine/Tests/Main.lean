import MathEngine
/-!
# Engine tests (`lake test`)

The cases were ported from the TypeScript reference engine's `engine.test.mjs` (deleted in M2, commit
c18b367); `Tests/golden.tsv` holds its answers on a larger corpus. Each `check` compares a string;
failures are listed and the exit code is 1.
-/
open MathEngine

structure Failure where
  name : String
  expected : String
  actual : String

abbrev TestM := StateT (Array Failure) IO

def check (name : String) (actual expected : String) : TestM Unit :=
  if actual == expected then pure () else modify (·.push ⟨name, expected, actual⟩)

def checkTrue (name : String) (b : Bool) (detail := "") : TestM Unit :=
  if b then pure () else modify (·.push ⟨name, "true", if detail.isEmpty then "false" else detail⟩)

/-- Parse and print without simplification. -/
def roundtrip (src : String) : String :=
  match parse src with
  | .ok e => e.toText
  | .error err => s!"<syntax error: {err.message} @{err.start}-{err.stop}>"

def latexOf (src : String) (paths := false) : String :=
  match parse src with
  | .ok e => e.toLatex paths
  | .error err => s!"<syntax error: {err.message}>"

def rpc (method : String) (params : String) : String :=
  handle s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"{method}\",\"params\":{params}}"

/-- Evaluate through the RPC surface and return the rendered text. -/
def evalText (src : String) : String :=
  let raw := rpc "engine.evaluate" s!"\{\"sessionId\":\"t\",\"cellId\":\"c\",\"source\":\"{src}\"}"
  match Json.parse raw with
  | .ok j =>
    match j.get? "result" >>= (·.get? "rendered") >>= (·.getStr? "text") with
    | some t => t
    | none => match j.get? "result" >>= (·.get? "error") >>= (·.getStr? "message") with
      | some m => s!"<error: {m}>"
      | none => s!"<unexpected: {raw}>"
  | .error m => s!"<bad json: {m}>"

/-- Substring test, for assertions that should not depend on JSON field order. -/
def contains (hay needle : String) : Bool := (hay.splitOn needle).length > 1

def qParse (s : String) : Q := (Q.parse s).getD default

-- --- step 4: a stateful session for the engine tests -------------------------------------------
/-- Evaluate in a persistent session through the RPC surface; returns the rendered text or the error. -/
def sessionEval (st : Store) (src : String) (extra := "") : Store × String :=
  let esc := src.replace "\\" "\\\\" |>.replace "\"" "\\\""
  let (st, raw) := handleS st s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":\{\"sessionId\":\"t\",\"cellId\":\"{esc}\",\"source\":\"{esc}\"{extra}}}"
  match Json.parse raw with
  | .ok j =>
    match j.get? "result" >>= (·.get? "rendered") >>= (·.getStr? "text") with
    | some t => (st, t)
    | none => match j.get? "result" >>= (·.get? "error") >>= (·.getStr? "message") with
      | some m => (st, s!"<error: {m}>")
      | none => match j.get? "error" >>= (·.getStr? "message") with
        | some m => (st, s!"<rpc error: {m}>")
        | none => (st, s!"<unexpected: {raw}>")
  | .error m => (st, s!"<bad json: {m}>")

/-- The paths a LaTeX rendering with `paths := true` wraps its subterms in, as printed. -/
def latexPaths (latex : String) : List String :=
  (latex.splitOn "\\htmlData{path=").drop 1 |>.map fun s => (s.splitOn "}").head!

/-- Paths a printed term names that are not in it: each one must reach a subterm (`Expr.at?`). -/
def badPaths (e : Expr) : List String :=
  (latexPaths (e.toLatex true)).filter fun p =>
    p != "root" && (e.at? ((p.splitOn ".").map String.toNat!)).isNone

/-- Rule names of a cell's derivation (needs `showWork`). -/
def derivationRules (st : Store) (src : String) : List String :=
  match (st.get "t").cells.lookup src with
  | some cell => cell.derivation.steps.toList.map (·.rule)
  | none => []

/-- Explanations of a cell's derivation (needs `showWork`). -/
def derivationExplanations (st : Store) (src : String) : List String :=
  match (st.get "t").cells.lookup src with
  | some cell => cell.derivation.steps.toList.map (·.explanation)
  | none => []

-- --- step 2: the traced rewriter ---------------------------------------------------------
/-- A toy verified rule: a one-element sum or product is that element. Under unit weights the
node it removes weighs 1, so the obligation is immediate. -/
def unwrap : Rule unitWeights where
  name := "test.unwrap"
  apply e := match e with
    | .add [x] => some ⟨x, "A sum of one term is that term.", none, none⟩
    | .mul [x] => some ⟨x, "A product of one factor is that factor.", none, none⟩
    | _ => none
  decreasing e r h := by
    cases e with
    | add es => match es, h with
      | [x], h => simp at h; subst h; simp only [MathEngine.measure, MathEngine.measureList, unitWeights]; omega
    | mul es => match es, h with
      | [x], h => simp at h; subst h; simp only [MathEngine.measure, MathEngine.measureList, unitWeights]; omega
    | _ => simp at h

def unwrapP : PlainRule := { name := "test.unwrap", apply := unwrap.apply }

def showSteps (d : Derivation) : String :=
  ", ".intercalate (d.steps.toList.map fun s => s!"{s.rule}@{s.path} {s.before.toText} -> {s.after.toText}")

set_option maxRecDepth 8192 in
def tests : TestM Unit := do
  -- rational arithmetic is exact and normalized
  check "Q 6/-4" (Q.ofRat (Rat.divInt 6 (-4))).toText "-3/2"
  check "Q 0.125 approx" (qParse "0.125").toText "0.125"
  check "Q 1/8 exact" (Q.ofRat (mkRat 1 8)).toText "1/8"
  check "Q 2.5" (qParse "2.5").toText "2.5"
  check "Q 0.125+0.875" (qParse "0.125" + qParse "0.875").toText "1"
  check "Q 1.5*2" (qParse "1.5" * Q.ofInt 2).toText "3"
  check "Q 1/3+1/6" (Q.ofRat (mkRat 1 3) + Q.ofRat (mkRat 1 6)).toText "1/2"
  check "Q decimal 15 digits" (Q.ofRat (mkRat 314159265358979323 100000000000000000) true).toText "3.14159265358979"
  check "Q decimal small" (Q.ofRat (mkRat 1 1000) true).toText "0.001"
  check "Q decimal big" (Q.ofRat (mkRat 123456789 1) true).toText "123456789"
  check "Q latex frac" (Q.ofRat (mkRat (-1) 2)).toLatex "-\\frac{1}{2}"
  -- scientific notation as a product, not JavaScript's 2.5e+43 (which reads back as 2.5·e + 43)
  check "Q text sci" (Q.ofRat 25000000000000000000 true).toText "2.5*10^19"
  check "Q text sci small" (Q.ofRat (mkRat 3 100000000) true).toText "3*10^(-8)"
  check "Q latex sci" (Q.ofRat 25000000000000000000 true).toLatex "2.5 \\times 10^{19}"
  check "sci binds as a product" (Expr.pow (.num (Q.ofRat 25000000000000000000 true)) (.num (Q.ofInt 2))).toText "(2.5*10^19)^2"
  -- parser: precedence and associativity (raw round trips; simplification is step 3)
  check "parse 2 + 3*4" (roundtrip "2 + 3*4") "2 + 3*4"
  check "parse -2^2" (roundtrip "-2^2") "-2^2"
  check "parse (-2)^2" (roundtrip "(-2)^2") "(-2)^2"
  check "parse 2^3^2" (roundtrip "2^3^2") "2^3^2"
  check "parse x/y/z" (roundtrip "x/y/z") "x/y/z"
  -- a fraction numeral prints as a division, so as a power's base it keeps its parentheses; the
  -- output, pasted back in, is the same term (`4/9^(3/2)` would read back as 4/27)
  check "print fraction base" (evalText "(4/9)^(3/2)") "(4/9)^(3/2)"
  check "print fraction base, pasted back" (evalText (evalText "(4/9)^(3/2)")) "(4/9)^(3/2)"
  check "print fraction base, symbolic exponent" (evalText "(4/9)^x") "(4/9)^x"
  check "print fraction base, negative" (evalText "(-4/9)^x") "(-4/9)^x"
  check "print fraction base, in a denominator" (evalText "(4/9)^(-3/2)") "1/(4/9)^(3/2)"
  check "print decimal exponent keeps its parentheses" (evalText "x^0.3") "x^(0.3)"
  -- Fourier milestone: definite integrals, finite sums, Euler as a command, dot/norm, sign
  check "definite integral of a power" (evalText "integrate(x^2, x, 0, 1)") "1/3"
  check "definite integral with symbolic bound" (evalText "integrate(2x, x, 0, b)") "b^2"
  check "definite integral of sin over a period" (evalText "integrate(sin(x), x, 0, 2pi)") "0"
  check "definite integral of cos over a period" (evalText "integrate(cos(x), x, 0, 2pi)") "0"
  check "definite integral with an exact root at a bound" (evalText "integrate(sqrt(x), x, 0, 4)") "16/3"
  check "definite integral bound must not mention the variable" (evalText "integrate(x, x, 0, x)") "<error: integrate: the bounds may not mention the variable x>"
  check "cos·sin are orthogonal" (evalText "integrate(cos(t)*sin(t), t, 0, 2pi)") "0"
  check "sum expands and collects" (evalText "sum(k^2, k, 1, 4)") "30"
  check "sum with a symbolic term" (evalText "sum(a*k, k, 1, 3)") "6*a"
  check "sum over negative indices" (evalText "sum(k, k, -2, 2)") "0"
  check "sum with bad bounds" (evalText "sum(k, k, 3, 1)") "<error: sum: the upper bound is below the lower bound (an empty sum is 0; write 0)>"
  check "exptotrig on a pure imaginary exponential" (evalText "exptotrig(exp(i*t))") "cos(t) + i*sin(t)"
  check "exptotrig on a negated angle" (evalText "exptotrig(exp(-i*t))") "cos(t) - i*sin(t)"
  check "exptotrig on e^(-it) - e^(it), expanded" (evalText "expand(exptotrig(exp(-i*t) - exp(i*t)))") "-2*i*sin(t)"
  check "exptotrig gives the square wave's partial sum" (evalText "expand(exptotrig(2i/pi*(exp(-i*t) - exp(i*t)) + 2i/(3pi)*(exp(-3i*t) - exp(3i*t))))") "4*sin(t)/π + 4*sin(3*t)/(3*π)"
  check "exptotrig leaves a real exponential" (evalText "exptotrig(exp(2t))") "exp(2*t)"
  check "dot of real vectors" (evalText "dot([1,2,3],[4,5,6])") "32"
  check "dot of column vectors" (evalText "dot([1;2],[3;4])") "11"
  check "dot is bilinear, not sesquilinear" (evalText "dot([i, 1],[i, 1])") "0"
  check "Hermitian product via conj" (evalText "dot([i, 1], conj([i, 1]))") "2"
  check "dot length mismatch" (evalText "dot([1,2],[1,2,3])") "<error: dot: the vectors have different lengths (2 and 3)>"
  check "norm of a 3-4-5 vector" (evalText "norm([3,4])") "5"
  check "norm symbolic" (evalText "norm([a,b])") "sqrt(a^2 + b^2)"
  check "exponentials of a product merge" (evalText "exp(2i*t)*exp(-3i*t)") "exp(-i*t)"
  check "three exponentials merge" (evalText "exp(a)*exp(b)*exp(c)*x") "x*exp(a + b + c)"
  check "orthogonality of e^{ikt}, k ≠ m" (evalText "integrate(exp(2i*t)*exp(-3i*t), t, -pi, pi)") "0"
  check "orthogonality of e^{ikt}, k = m" (evalText "integrate(exp(2i*t)*exp(-2i*t), t, -pi, pi)") "2*π"
  check "sign of numerals" (evalText "sign(-3) + sign(0) + sign(5/2)") "0"
  check "sign stays symbolic" (evalText "sign(sin(t))") "sign(sin(t))"
  check "N of sign" (evalText "N(sign(-2.5))") "-1"
  check "N over the complex numbers" (evalText "N(exp(i*pi/4))") "0.707106781186548 + 0.707106781186548*i"
  check "N of a complex power" (evalText "N((1+2i)^2)") "-3 + 4*i"
  check "N falls back to ℂ when the real value is not finite" (evalText "N(sqrt(-1))") "i"
  check "N of ln(-1)" (evalText "N(ln(-1))") "3.14159265358979*i"
  check "parse 8/2/2 is a rational" (roundtrip "8/2/2") "2"
  check "parse a - b - c" (roundtrip "a - b - c") "a - b - c"
  -- parser: implicit multiplication and calls
  check "parse 2x^2" (roundtrip "2x^2") "2*x^2"
  check "parse 2(x+1)" (roundtrip "2(x+1)") "2*(x + 1)"
  check "parse x y" (roundtrip "x y") "x*y"
  check "parse sin(0)" (roundtrip "sin(0)") "sin(0)"
  check "parse diff" (roundtrip "diff(x^2, x)") "diff(x^2, x)"
  check "parse unknown call is implicit mul" (roundtrip "f(x)") "f*x"
  check "parse known call" (match parse "f(x)" ["f"] with | .ok e => e.toText | .error _ => "err") "f(x)"
  check "parse 3 4 error" (roundtrip "3 4") "<syntax error: unexpected '4' @2-3>"
  check "parse x + error" (roundtrip "x +") "<syntax error: unexpected end of input @3-3>"
  check "parse pi" (roundtrip "pi") "π"
  check "parse let" (match parseStmt "let f = x^2 + 3x" with | .ok (.«let» n _ v) => s!"{n} = {v.toText}" | _ => "err") "f = x^2 + 3*x"
  check "parse matrix" (roundtrip "[1,2;3,4]") "[1, 2; 3, 4]"
  check "parse ragged" (roundtrip "[1,2;3]") "<syntax error: ragged matrix rows @0-1>"
  check "parse decimal" (roundtrip "2.5x + .5") "2.5*x + 0.5"
  -- the entrywise operators: `./` and `.*` are tokens, and a `.` before a digit is still a numeral
  check "parse ./" (roundtrip "a ./ b") "a ./ b"
  check "parse .*" (roundtrip "a.*b") "a .* b"
  check "parse 2./3" (roundtrip "2./3") "2 ./ 3"
  check "parse ./ is left-associative" (roundtrip "a ./ b ./ c") "(a ./ b) ./ c"
  check "parse ./ binds as a product" (roundtrip "a + b ./ c*d") "a + (b ./ c)*d"
  check "print a factor ./ keeps its parentheses" (roundtrip "x*(a ./ b)") "x*(a ./ b)"
  check "latex ./" (latexOf "[1,2] ./ [3,4]") "\\begin{bmatrix}1 & 2\\end{bmatrix} \\oslash \\begin{bmatrix}3 & 4\\end{bmatrix}"
  check "latex .*" (latexOf "[1,2] .* [3,4]") "\\begin{bmatrix}1 & 2\\end{bmatrix} \\odot \\begin{bmatrix}3 & 4\\end{bmatrix}"
  -- printer: recovers -, /, sqrt and parenthesizes correctly
  check "print x/(y*z)" (roundtrip "x/(y*z)") "x/(y*z)"
  check "print (x+1)/(x-1)" (roundtrip "(x+1)/(x-1)") "(x + 1)/(x - 1)"
  check "print 1/x" (roundtrip "1/x") "1/x"
  check "print -(-x) raw" (roundtrip "-(-x)") "--x"  -- same as printer.ts on the raw tree; simplify gives x
  check "print sqrt(2)" (roundtrip "sqrt(2)") "sqrt(2)"
  check "print x - 2y" (roundtrip "x - 2y") "x - 2*y"
  check "print -x - 1" (roundtrip "-x - 1") "-x - 1"
  check "print 2/3 x" (Expr.toText (.mul [.num (Q.ofRat (mkRat 2 3)), .var "x"])) "2*x/3"
  check "print 1/x^2" (Expr.toText (.pow (.var "x") (.ofInt (-2)))) "1/x^2"
  check "print x^(1/2)" (Expr.toText (.pow (.var "x") (.num (Q.ofRat (mkRat 1 2))))) "sqrt(x)"
  check "latex x/2 + sqrt(y)" (latexOf "x/2 + sqrt(y)") "\\frac{x}{2} + \\sqrt{y}"
  check "latex diff" (latexOf "diff(x^2, x)") "\\frac{d}{dx}\\left({x}^{2}\\right)"
  check "latex exp is a power of e" (latexOf "exp(x + 1)") "e^{x + 1}"
  check "latex exp(1) is e" (latexOf "exp(1)") "e"
  check "latex exp(2) is e squared" (latexOf "exp(2)") "e^{2}"
  check "latex a power of exp is grouped" (latexOf "exp(x)^2") "{\\left(e^{x}\\right)}^{2}"
  check "latex exp in a product" (latexOf "2*exp(-x)") "2 \\cdot e^{-x}"
  check "latex exp's paths" (latexOf "exp(x)" true) "\\htmlData{path=root}{e^{\\htmlData{path=0}{x}}}"
  check "text exp is unchanged" (match parseStmt "exp(x)" with | .ok st => st.value.toText | .error _ => "parse") "exp(x)"
  check "latex greek and mathit" (latexOf "pi * abc") "\\pi \\cdot \\mathit{abc}"
  -- a subsets-poset element is named by its set literal; braces are LaTeX grouping, so they are escaped
  check "latex set-literal elements" ((Expr.fn "set" [.var "{}", .var "{x,y}"]).toLatex false) "\\{\\varnothing, \\{x,y\\}\\}"
  check "latex matrix" (latexOf "[1,2;3,4]") "\\begin{bmatrix}1 & 2 \\\\ 3 & 4\\end{bmatrix}"
  check "latex paths" (latexOf "x^3" true) "\\htmlData{path=root}{{\\htmlData{path=0}{x}}^{\\htmlData{path=1}{3}}}"
  -- `-(a·b)` prints without its `-1`: the product is the signed term's, and each factor keeps its own
  -- index (`0.2.1`, not `0.1.1.1`, which names nothing)
  let negProd := Expr.add [.mul [.num Q.minusOne, .pow (.num (Q.ofInt 2)) (.num (Q.ofRat (mkRat (-1) 2))),
    .pow (.fn "sin" [.var "t"]) (.num (Q.ofInt 2))], .fn "cos" [.var "t"]]
  check "latex paths: a negated product" (negProd.toLatex true)
    "\\htmlData{path=root}{-\\htmlData{path=0}{\\frac{\\htmlData{path=0.2}{{\\htmlData{path=0.2.0}{\\sin\\left(\\htmlData{path=0.2.0.0}{t}\\right)}}^{\\htmlData{path=0.2.1}{2}}}}{\\htmlData{path=0.1}{\\sqrt{2}}}} + \\htmlData{path=1}{\\cos\\left(\\htmlData{path=1.0}{t}\\right)}}"
  check "latex paths: a negated product, every path reaches a subterm" (toString (badPaths negProd)) "[]"
  -- step 2: normalize records whole-term before/after and the path; innermost order
  let x := Expr.var "x"; let y := Expr.var "y"
  let d := derive [unwrap] (.add [x, .add [y]])
  check "rewrite: one step" (showSteps d) "test.unwrap@[1] x + (y) -> x + y"
  check "rewrite: output" d.output.toText "x + y"
  let d2 := derive [unwrap] (.mul [.add [.add [x]]])
  check "rewrite: innermost, three steps" (showSteps d2)
    "test.unwrap@[0, 0] (x) -> (x), test.unwrap@[0] (x) -> x, test.unwrap@[] x -> x"
  check "rewrite: canonical order is silent" (derive [unwrap] (.add [y, x])).output.toText "x + y"
  check "rewrite: sums ordered by degree" (derive [unwrap] (.add [.ofInt 1, .pow x (.ofInt 2), .mul [.ofInt 3, x]])).output.toText "x^2 + 3*x + 1"
  -- step 3: simplify (rendered text after normalization, as the reference tests do)
  let simp (src : String) : String := match parse src with
    | .ok e => (simplify0 e).toText
    | .error err => s!"<syntax error: {err.message}>"
  check "simp 2 + 3*4" (simp "2 + 3*4") "14"
  check "simp -2^2" (simp "-2^2") "-4"
  check "simp (-2)^2" (simp "(-2)^2") "4"
  check "simp 2^3^2" (simp "2^3^2") "512"
  check "simp 8/2/2" (simp "8/2/2") "2"
  check "simp a - b - c" (simp "a - b - c") "a - b - c"
  check "simp 2x + 3x" (simp "2x + 3x") "5*x"
  check "simp 2(x+1)" (simp "2(x+1)") "2*(x + 1)"
  check "simp sin(0)" (simp "sin(0)") "0"
  check "simp x/(y*z)" (simp "x/(y*z)") "x/(y*z)"
  check "simp (x+1)/(x-1)" (simp "(x+1)/(x-1)") "(x + 1)/(x - 1)"
  check "simp 1/x" (simp "1/x") "1/x"
  check "simp -(-x)" (simp "-(-x)") "x"
  check "simp sqrt(2)" (simp "sqrt(2)") "sqrt(2)"
  check "simp 0*x + 1*y" (simp "0*x + 1*y") "y"
  check "simp x - x" (simp "x - x") "0"
  check "simp x*x*x" (simp "x*x*x") "x^3"
  check "simp x^2 * x^3 / x" (simp "x^2 * x^3 / x") "x^4"
  check "simp (x^2)^3" (simp "(x^2)^3") "x^6"
  check "simp sqrt(16)" (simp "sqrt(16)") "4"
  check "radical power: sqrt(2)^2" (simp "sqrt(2)^2") "2"
  check "radical power: sqrt(74)^2" (simp "sqrt(74)^2") "74"
  check "radical power: 1/sqrt(2)^2" (simp "1/sqrt(2)^2") "1/2"
  check "radical power: 2^(3/2) squared" (simp "(2^(3/2))^2") "8"
  check "radical power: symbolic base stays" (simp "sqrt(x)^2") "sqrt(x)^2"
  check "print 2^(-1/2) as 1/sqrt(2)" (simp "1/sqrt(2)") "1/sqrt(2)"
  check "print 2^(-3/2) with parentheses" (simp "2^(-3/2)") "1/2^(3/2)"
  check "print a product over sqrt(2)" (simp "1/(4*sqrt(2))") "1/(4*sqrt(2))"
  check "print a product over 2^(3/2)" (simp "3/(2*2^(3/2))") "3/(2*2^(3/2))"
  check "simp ln(exp(x))" (simp "ln(exp(x))") "x"
  check "simp 1/2 + 1/3" (simp "1/2 + 1/3") "5/6"
  check "simp x^2 + 3x + 1 order" (simp "1 + 3x + x^2") "x^2 + 3*x + 1"
  check "simp x + 2x + y" (simp "x + 2x + y") "3*x + y"
  check "simp x*0.5*2" (simp "x*0.5*2") "x"  -- 0.5*2 folds to an approximate 1, which isOne drops (same as the reference)
  checkTrue "simp canonical order" (match parse "x*2 + y", parse "y + 2*x" with
    | .ok a, .ok b => Expr.equal (simplify0 a) (simplify0 b) | _, _ => false)
  let d := match parse "0*x + 1*y" with | .ok e => derive simpRules e | .error _ => default
  check "simp derivation rules" (", ".intercalate (d.steps.toList.map (·.rule))) "simp.identity, simp.identity, simp.identity"
  check "simp derivation before/after" (showSteps d) "simp.identity@[0] 0*x + 1*y -> 0 + 1*y, simp.identity@[1] 0 + 1*y -> 0 + y, simp.identity@[] y + 0 -> y"  -- canonical order (constants last) is silent

set_option maxRecDepth 2048 in
/-- Step 4 onwards, through the stateful RPC surface. A definition of its own: one `do` block holding
every test outgrows the compiler's heartbeat budget. -/
def sessionTests : TestM Unit := do
  -- step 4: diff, linalg, session, show work, explain (through the stateful RPC surface)
  let mut st : Store := []
  let ev (st : Store) (src : String) : Store × String := sessionEval st src
  let mut r := ""
  (st, r) := ev st "diff(x^3, x)"; check "diff x^3" r "3*x^2"
  (st, r) := ev st "diff(5, x)"; check "diff 5" r "0"
  (st, r) := ev st "diff(sin(x^2), x)"; check "diff sin(x^2)" r "2*x*cos(x^2)"
  (st, r) := ev st "norm([sqrt(2)/2, sqrt(2)/2])"; check "radical power: unit vector norm" r "1"
  (st, r) := ev st "let sq(k) = 1/(2pi)*(integrate(exp(-i*k*t), t, 0, pi) - integrate(exp(-i*k*t), t, -pi, 0))"
  (st, r) := ev st "factor(sq(k))"; check "factor: the square wave's coefficient in the hand form" r "i*(-2 + exp(-i*π*k) + exp(i*π*k))/(2*π*k)"
  (st, r) := ev st "factor(x^2 + 2*x)"; check "factor: common factor" r "x*(x + 2)"
  (st, r) := ev st "factor(a/x + b/y)"; check "factor: together" r "(a*y + b*x)/(x*y)"
  (st, r) := ev st "factor(-2*x - 4)"; check "factor: negative common factor" r "-2*(x + 2)"
  (st, r) := ev st "factor(x/2 + x/3)"; check "factor: collects first" r "5*x/6"
  (st, r) := ev st "factor(a/(x+1) + b/x)"; check "factor: denominators that are sums" r "(a*x + b*(x + 1))/(x*(x + 1))"
  (st, r) := sessionEval st "factor(1/(x+1) + 1/(x-1))" ",\"showWork\":true"
  check "factor: checked by cross-multiplying" r "2*x/((x - 1)*(x + 1))"
  checkTrue "factor: the step says what was checked" ((derivationExplanations st "factor(1/(x+1) + 1/(x-1))").any (contains · "Checked: times its denominator"))
  checkTrue "factor: the step names the denominator it assumes nonzero" ((derivationExplanations st "factor(1/(x+1) + 1/(x-1))").any (contains · "Assuming $\\left(x - 1\\right) \\cdot \\left(x + 1\\right) \\neq 0$"))
    s!"{derivationExplanations st "factor(1/(x+1) + 1/(x-1))"}"
  (st, r) := ev st "diff(x*sin(x), x)"; check "diff x sin x" r "x*cos(x) + sin(x)"
  (st, r) := ev st "diff(2^x, x)"; check "diff 2^x" r "2^x*ln(2)"
  (st, r) := ev st "diff(x^x, x)"; check "diff x^x" r "x^x*(ln(x) + 1)"
  (st, r) := ev st "diff(x^3, x, 2)"; check "diff x^3 twice" r "6*x"
  (st, r) := ev st "diff(ln(x), x)"; check "diff ln x" r "1/x"
  (st, r) := ev st "expand((x+1)^3)"; check "expand (x+1)^3" r "x^3 + 3*x^2 + 3*x + 1"
  (st, r) := ev st "[1,2;3,4] * [5,6;7,8]"; check "la mul" r "[19, 22; 43, 50]"
  (st, r) := ev st "det([1,2;3,4])"; check "la det 2" r "-2"
  (st, r) := ev st "det([2,0,1;1,3,2;1,1,1])"; check "la det 3 zero" r "0"
  (st, r) := ev st "det([1,2,3;4,5,6;7,8,10])"; check "la det 3" r "-3"
  (st, r) := ev st "transpose([1,2,3;4,5,6])"; check "la transpose" r "[1, 4; 2, 5; 3, 6]"
  (st, r) := ev st "rref([1,2,3;4,5,6;7,8,10])"; check "la rref" r "[1, 0, 0; 0, 1, 0; 0, 0, 1]"
  (st, r) := ev st "rref([1,2;2,4])"; check "la rref rank 1" r "[1, 2; 0, 0]"
  (st, r) := ev st "det([a,b;c,d])"; check "la det symbolic" r "a*d - b*c"
  (st, r) := ev st "[1,2] * [1,2]"; check "la dimension error" r "<error: matrix product: 1×2 times 1×2 is undefined (inner dimensions must match)>"
  (st, r) := ev st "let f = x^2 + 3x"; check "session let" r "x^2 + 3*x"
  (st, r) := ev st "diff(f, x)"; check "session diff f" r "2*x + 3"
  (st, r) := ev st "subst(f, x, 2)"; check "session subst" r "10"
  (st, r) := ev st "N(pi)"; check "session N(pi)" r "3.14159265358979"
  (st, r) := ev st "N(sqrt(2))"; check "N sqrt 2" r "1.4142135623731"
  (st, r) := sessionEval st "diff(x^2 * sin(x), x)" ",\"showWork\":true"
  let rules := derivationRules st "diff(x^2 * sin(x), x)"
  checkTrue "show work: diff rules present" (rules.contains "diff.product" && rules.contains "diff.power" && rules.contains "diff.chain") (", ".intercalate rules)
  (st, r) := sessionEval st "rref([1,2;3,4])" ",\"showWork\":true"
  let rr := (st.get "t").cells.lookup "rref([1,2;3,4])"
  check "show work: rref is a command step" ((rr.map fun c => (c.derivation.steps.toList.map (·.rule))).getD []).toString "[cmd.rref]"
  checkTrue "show work: rref sub steps" ((rr.bind fun c => c.derivation.steps[0]? >>= (·.sub)).map (fun d => d.steps.toList.any (·.rule == "la.row-add")) |>.getD false)
  -- M7: numerals take the verified ℚ path, symbolic entries the unverified one
  (st, r) := ev st "rref([1/2,1,3;1,3,5])"; check "la rref rational" r "[1, 0, 8; 0, 1, -1]"
  (st, r) := ev st "rref([0,1,2;0,0,0;3,4,5])"; check "la rref swap" r "[1, 0, -1; 0, 1, 2; 0, 0, 0]"
  (st, r) := sessionEval st "rref([0,1;2,4])" ",\"showWork\":true"
  let subRules (src : String) : List String :=
    ((st.get "t").cells.lookup src >>= fun c => c.derivation.steps[0]? >>= (·.sub)).map (fun d => d.steps.toList.map (·.rule)) |>.getD []
  check "rref ℚ path: verified rule names" (subRules "rref([0,1;2,4])").toString "[la.row-swap, la.row-scale, la.row-add]"
  (st, r) := sessionEval st "rref([a,1;1,a])" ",\"showWork\":true"
  check "rref symbolic path" r "[1, 0; 0, 1]"
  checkTrue "rref symbolic path: .symbolic rule names" ((subRules "rref([a,1;1,a])").all (·.endsWith ".symbolic")) (subRules "rref([a,1;1,a])").toString
  (st, r) := sessionEval st "rref([x,y;x^2,1])" ",\"showWork\":true"
  check "rref symbolic: a cancellation that assumes" r "[1, 0; 0, 1]"
  (st, _) := sessionEval st "N(pi)" ",\"showWork\":true"
  (st, _) := sessionEval st "N(tan(pi/2))" ",\"showWork\":true"
  let lastRule (src : String) : String :=
    ((st.get "t").cells.lookup src >>= fun c => c.derivation.steps.toList.getLast? |>.map (·.rule)).getD ""
  check "N: certified by intervals" (lastRule "N(pi)") "cmd.N"
  check "N: a pole is not certified" (lastRule "N(tan(pi/2))") "cmd.N.float"
  checkTrue "N: the certified step states its bound"
    ((((st.get "t").cells.lookup "N(pi)").bind fun c => c.derivation.steps.toList.getLast?).map (fun s => contains s.explanation "to within $10^{-14}$") |>.getD false) "N(pi)"
  let symSteps := ((st.get "t").cells.lookup "rref([x,y;x^2,1])" >>= fun c => c.derivation.steps[0]? >>= (·.sub)).map (·.steps.toList) |>.getD []
  check "rref symbolic: the row addition that cancelled says so" (symSteps.map (·.rule)).toString
    "[la.row-scale.symbolic, la.row-add.symbolic.assuming, la.row-scale.symbolic, la.row-add.symbolic]"
  let symTexts := symSteps.map (·.explanation)
  checkTrue "rref symbolic: the scale states its pivot, the addition its cancellation"
    ((symTexts[0]?.getD "").endsWith "assuming $x \\neq 0$." && (symTexts[1]?.getD "").endsWith "Simplifying the entries assumes $x \\neq 0$.") symTexts.toString
  -- the order-theory world
  (st, r) := ev st "let D = divisors(12)"; checkTrue "order: divisors is a poset" (r.startsWith "poset {1, 2, 3, 4, 6, 12}") r
  (st, r) := ev st "join(D, 4, 6)"; check "order: join in divisors(12)" r "12"
  (st, r) := ev st "meet(D, 4, 6)"; check "order: meet in divisors(12)" r "2"
  (st, r) := ev st "lattice(D)"; check "order: divisors(12) is a lattice" r "true"
  (st, r) := ev st "le(D, 2, 12)"; check "order: le by a chain of covers" r "true"
  (st, r) := ev st "let P = poset({a,b,c,d}; a<b, a<c, b<d, c<d)"; checkTrue "order: a diamond" (r.startsWith "poset") r
  (st, r) := ev st "let N = poset({a,b,c}; a<b, a<c)"; checkTrue "order: a vee" (r.startsWith "poset") r
  (st, r) := ev st "lattice(N)"; check "order: the vee is not a lattice" r "false"
  (st, r) := ev st "poset({a,b}; a<b, b<a)"; checkTrue "order: antisymmetry is checked" (r.startsWith "<error: not a partial order") r
  (st, r) := ev st "let f = map(D; 1->2, 2->2, 3->6, 4->4, 6->6, 12->12)"; checkTrue "order: a map" (r.startsWith "{") r
  (st, r) := ev st "monotone(D, f)"; check "order: monotone" r "true"
  (st, r) := ev st "lfp(D, f)"; check "order: least fixed point by the Kleene chain" r "2"
  (st, r) := ev st "gfp(D, f)"; check "order: greatest fixed point" r "12"
  (st, r) := ev st "let S = subsets({x,y})"; checkTrue "order: subsets" (r.startsWith "poset") r
  (st, r) := ev st "join(S, {x}, {y})"; check "order: join of subsets" r "{x,y}"
  -- the λ-calculus world
  (st, r) := ev st "(λx. x) y"; check "λ: identity" r "y"
  (st, r) := ev st "\\x y. x"; check "λ: backslash and multi-binder" r "λx. λy. x"
  (st, r) := ev st "(λx. λy. x) a b"; check "λ: K a b" r "a"
  (st, r) := ev st "(λx. λy. x y) y"; check "λ: capture avoided" r "λy'. y y'"
  (st, r) := ev st "TWO := succ (succ zero)"; check "λ: define via the Church library" r "λf. λx. f (f x)"
  (st, r) := ev st "add TWO 3"; check "λ: Church arithmetic" r "λf. λx. f (f (f (f (f x))))"
  (st, r) := ev st "if true a b"; check "λ: Church booleans" r "a"
  (st, r) := ev st "omega omega"; checkTrue "λ: Ω is refused, not looped" (r.startsWith "<error: λ: no normal form") r
  -- λ-commands: a strategy, the typed calculus; a typed binder prints back as written
  (st, r) := ev st "cbv: (λx. x) ((λy. y) z)"; check "λ: call by value reduces the argument first" r "z"
  (st, r) := ev st "type := λx. x"; check "λ: `type :=` is a definition, not a command" r "λx. x"
  (st, r) := ev st "type: λx:A→B. x"; check "λ: a typed binder" r "(A → B) → A → B"
  (st, r) := ev st "type: λ(x:A) (y:B). x"; check "λ: binders in parentheses" r "A → B → A"
  (st, r) := ev st "type: x : A, x : B ⊢ x"; check "λ: a later context entry shadows" r "B"
  (st, r) := ev st "infer: λf. λx. f (f x)"; check "λ: infer a numeral's type" r "(α → α) → α → α"
  (st, r) := ev st "alpha: λx. y, λy. y"; check "λ: a free variable is not a bound one" r "⊥"
  (st, r) := ev st "fv: 3"; checkTrue "λ: fv does not unfold names" (r == "{3}") r
  (st, r) := ev st "fv 2: x"; checkTrue "λ: a step count only on a reduction" (r.startsWith "<error: fv: takes no step count") r
  (st, r) := ev st "p ∧ q"; checkTrue "λ: a formula is still logic" (r == "p ∧ q") r
  -- nested calls in the order world: the inner call's work comes first, and its name is forgotten
  check "nested: a source unnested" (unnest Ord.commands "let P = product(chain(2), chain(3))").2.1 "let P = product(chain_1, chain_2)"
  check "nested: innermost first" (toString ((unnest Ord.commands "lattice(product(chain(2), chain(3)))").1.map (·.1))) "[chain_1, chain_2, product_3]"
  check "nested: a pair is not a call" (unnest Ord.commands "join(PQ, (a, b), (c, d))").2.1 "join(PQ, (a, b), (c, d))"
  (st, r) := ev st "product(chain(2), chain(2))"; checkTrue "nested: product of chains" (r.startsWith "poset") r
  (st, r) := ev st "chain_1"; check "nested: the inner names are forgotten" r "chain_1"
  let nested := rpc "engine.evaluate" "{\"sessionId\":\"n\",\"cellId\":\"a\",\"source\":\"lattice(chain(3))\",\"showWork\":true}"
  checkTrue "nested: the inner call is a step with its own derivation" (contains nested "\"rule\":\"order.inner\"" && contains nested "\"sub\":") nested
  let reqN (id method params : String) := s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"{method}\",\"params\":{params}}"
  let (stN, _) := handleS [] (reqN "20" "engine.evaluate" "{\"sessionId\":\"n\",\"cellId\":\"a\",\"source\":\"lattice(chain(3))\"}")
  checkTrue "nested: engine.steps has the inner call too" (contains (handleS stN (reqN "21" "engine.steps" "{\"sessionId\":\"n\",\"cellId\":\"a\"}")).2 "\"rule\":\"order.inner\"")
  let tr := rpc "engine.evaluate" "{\"sessionId\":\"tr\",\"cellId\":\"a\",\"source\":\"let L = system(var c in {red, green}; init c = red; action go when c = red do c := green)\"}"
  checkTrue "trace: a system" (contains tr "\"ok\":true") tr
  let (stT, _) := handleS [] (reqN "22" "engine.evaluate" "{\"sessionId\":\"tr\",\"cellId\":\"a\",\"source\":\"let L = system(var c in {red, green}; init c = red; action go when c = red do c := green)\"}")
  let (_, trc) := handleS stT (reqN "23" "engine.evaluate" "{\"sessionId\":\"tr\",\"cellId\":\"b\",\"source\":\"trace(L; go)\"}")
  checkTrue "trace: the graph places each step, the first at its state and the next on its transition" (contains trc "\"steps\":[{\"node\":\"red\"},{\"edge\":[\"red\",\"green\"]}]") trc
  let rep := rpc "engine.evaluate" "{\"sessionId\":\"rp\",\"cellId\":\"a\",\"source\":\"replicas(gcounter; a, b; a: inc; m := a; a: inc; b <- m)\",\"showWork\":true}"
  checkTrue "replicas: a space-time diagram, a message from the send to the delivery" (contains rep "\"kind\":\"replicas.spacetime\"" && contains rep "\"messages\":[[1,3]]") rep
  checkTrue "replicas: the work says it has not converged, and there is no note beside the answer" (contains rep "\"rule\":\"crdt.diverged\"" && !contains rep "\"summary\"") rep
  checkTrue "replicas: a merge step" (contains rep "\"rule\":\"crdt.merge\"") rep
  let trs (st : Store) (src : String) := handleS st s!"\{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":\{\"sessionId\":\"trs\",\"cellId\":\"{src.length}\",\"source\":\"{src}\",\"showWork\":true}}"
  let (stT, rulesA) := trs [] "let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))"
  checkTrue "rules: the note names the rules, which the answer does not show" (contains rulesA "\"summary\":\"named r1, r2\"") rulesA
  let (stT, _) := trs stT "let C = rules(f(f(x)) -> g(x))"
  let rw := (trs stT "rewrite(A, add(s(0), add(0, 0)))").2
  checkTrue "rewrite: the first step is r2 at the root" (contains rw "\"rule\":\"trs.step\",\"explanation\":\"r2: " && contains rw "\"path\":[]") rw
  checkTrue "rewrite: an inner step names its position" (contains rw "\"path\":[0]") rw
  let te := (trs stT "terminates(A; add(x, y) = 2x + y, s(x) = x + 1)").2
  checkTrue "terminates: a step per rule, with its forms" (contains te "\"rule\":\"trs.decrease\"" && contains te "the left side's interpretation is 2x + y + 2, the right side's 2x + y + 1: larger") te
  let cr := (trs stT "critical(C)").2
  checkTrue "critical: an overlap of a rule with itself, two normal forms" (contains cr "\"rule\":\"trs.critical\"" && contains cr "the system is not confluent" && contains cr "position [0]") cr
  let (stT, _) := trs stT "let L = rules(r1: f(x) -> f(x); r2: f(x) -> f(x))"
  let cl := (trs stT "critical(L)").2
  checkTrue "critical: a pair that rewrites for ever but meets joins" (contains cl "all joinable" && !contains cl "not confluent") cl
  let (stT, _) := trs stT "let U = rules(r1: f(x) -> g(x); r2: f(x) -> h(x); g(x) -> g(x); h(x) -> h(x))"
  let cu := (trs stT "critical(U)").2
  checkTrue "critical: sides that rewrite for ever apart are undecided, not refuted" (contains cu "undecided" && !contains cu "not confluent") cu
  let (stT, _) := trs stT "let P = rules(f(g(x')) -> a; g(h(x)) -> b)"
  let cp := (trs stT "critical(P)").2
  checkTrue "critical: x' in one rule and x in the other are renamed apart, so the overlap is found" (contains cp "1 critical pair, 1 with two different normal forms: not confluent") cp
  check "rewriting: the second rule's suffix is lengthened when two primes would collide" (TRS.apart ["x'"] ["x"]) "''''"
  check "rewriting: two primes otherwise" (TRS.apart ["x", "y"] ["x", "z"]) "''"
  check "rewriting: a variable keeps its name, a constant is a symbol" (toString ((TRS.parseTerm "f(x1, e, y')").toOption.getD default)) "f(x1, e, y')"
  check "rewriting: renamed-apart variables get their names back" (toString (TRS.tidy [.f "f" [.v "x''", .v "z'", .v "x'"]])) "[f(x, z, x')]"
  check "replicas: the map prints in LaTeX" ((Expr.fn "set" [.fn "↦" [.var "a", .num (Q.ofInt 2)]]).toLatex false) "\\{a \\mapsto 2\\}"
  -- a Church name at the head makes a λ-cell only when the source lexes as a λ-term
  (st, r) := ev st "S + 1"; check "λ: `S + 1` is arithmetic, not a λ-term" r "S + 1"
  (st, r) := ev st "I + x"; checkTrue "λ: `I + x` is arithmetic" (!r.startsWith "<error") r
  (st, r) := ev st "fst (pair a b)"; check "λ: a Church name at the head, with no λ, is still a λ-term" r "a"
  checkTrue "λ: `K * 2` is not a λ-cell" (!Lam.isLambdaSource "K * 2" (Lam.churchDefs.map (·.1)))
  checkTrue "λ: `id x` is a λ-cell" (Lam.isLambdaSource "id x" (Lam.churchDefs.map (·.1)))
  -- a definition with no normal form is bound unreduced, and the reduction is cut off by size, not hung
  (st, r) := ev st "pred := λn. fst (n (λp. pair (snd p) (succ (snd p))) (pair 0 0))"; checkTrue "λ: pred" (r.startsWith "λn.") r
  (st, r) := ev st "fact := Y (λself. λn. if (iszero n) 1 (mul n (self (pred n))))"; checkTrue "λ: a Y definition is bound unreduced" (r.startsWith "(λf. (λx. f (x x))") r
  (st, r) := ev st "fact 2"; check "λ: recursion through Y" r "λf. λx. f (f x)"
  (st, r) := ev st "fact 3"; check "λ: fact 3 within the budget (1525 β-steps)" r "λf. λx. f (f (f (f (f (f x)))))"
  let long := rpc "engine.evaluate" "{\"sessionId\":\"f\",\"cellId\":\"a\",\"source\":\"omega omega\",\"showWork\":true}"
  checkTrue "λ: Ω is refused after the budget" (contains long "no normal form after 10000 β-steps") long
  let elided := rpc "engine.evaluate" "{\"sessionId\":\"f\",\"cellId\":\"b\",\"source\":\"normal 500: omega omega\",\"showWork\":true}"
  checkTrue "λ: a long run shows its ends and one step for the middle" (contains elided "\"rule\":\"lambda.elided\"" && contains elided "380 more steps") elided
  (st, r) := ev st "cbv: fact 1"; checkTrue "λ: call by value unfolds Y until the term is too big" (r.startsWith "<error: λ: no value yet after" && contains r "grown past") r
  -- printing is linear in a term's depth: forty nested λs and a forty-deep arrow type
  let deep := (List.range 40).foldr (fun i e => Expr.fn "λ" [.var s!"x{i}", e]) (.var "x0")
  checkTrue "λ: a deep term prints" ((deep.toLatex false).length > 100)
  let arrows := (List.range 40).foldr (fun i e => Expr.fn "→" [.var s!"A{i}", e]) (.var "B")
  checkTrue "λ: a deep type prints" ((arrows.toLatex false).length > 100)
  check "λ: a typed binder in LaTeX" ((Lam.ATerm.lam "x" (some (.arrow (.base "A") (.base "B"))) (.var "x")).toExpr.toLatex false) "\\lambda x{:}\\left(A \\to B\\right).\\, x"
  check "λ: a type variable's index is a subscript" ((Lam.Ty.tvar 0).toExpr.toLatex false) "\\tau_{1}"
  check "λ: a typed term reads back" (match Lam.parseATerm "λf:(A → B). λx:A. f x" with | .ok t => t.text | .error e => e) "λf:(A → B). λx:A. f x"
  (st, r) := ev st "x^2 + y"; check "an ordinary cell is still ordinary" r "x^2 + y"
  -- % output references, numbered like Mathematica's In/Out
  (st, r) := ev st "x^2 + 1"; check "%: seed" r "x^2 + 1"
  (st, r) := ev st "diff(%, x)"; check "% is the last output" r "2*x"
  (st, r) := ev st "%% - %"; check "%% is the one before" r "x^2 - 2*x + 1"
  (st, r) := ev st "2%"; check "% under implicit multiplication" r "2*(x^2 - 2*x + 1)"
  (st, r) := ev st "%9999"; checkTrue "%n undefined is an error" (r.startsWith "<error: Out[9999] is not defined") r
  let (_, r0) := sessionEval {} "%"; checkTrue "% in a fresh session is an error" (r0.startsWith "<error: % refers") r0
  let (st3, _) := sessionEval {} "x + 0"
  let (_, raw) := handleS st3 "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"c\",\"source\":\"%1 + %\"}}"
  checkTrue "the reply carries the evaluation number" ((raw.splitOn "\"label\":2").length == 2) raw
  -- a power of a function, and expansion through a nested sum (the integral check needs both)
  (st, r) := ev st "sin^2(y)"; check "sin^2(y) is sin(y)^2" r "sin(y)^2"
  (st, r) := ev st "expand(a*(-(-y^2*sin(y) + 2*y*cos(y)) + 2*y*cos(y)))"; check "expand flattens nested sums" r "a*y^2*sin(y)"
  (st, r) := ev st "integrate(5 y^2 sin(y), y)"; check "integrate with a constant factor and two by-parts rounds" r "5*(-y^2*cos(y) + 2*(y*sin(y) + cos(y)))"
  -- powers of sine and cosine (reduction formulas) and of exp, all verified by the check
  for src in ["integrate(sin^3(y), y)", "integrate(sin(y)^2, y)", "integrate(5y sin^3(y), y)", "integrate(sin(y)^2*cos(y)^2, y)",
              "integrate(cos^4(2y), y)", "integrate(cos^5(y), y)", "integrate(exp(x)^2, x)", "integrate(exp(2x+1)^3, x)"] do
    let (st', res) := ev st src
    st := st'
    checkTrue s!"accepted: {src}" (!res.startsWith "<error") res
  (st, r) := ev st "integrate(sin^2(y) + exp(x)^2, y)"; checkTrue "mixed sum with a trig power" (!r.startsWith "<error") r
  -- Greek letters and Euler's number
  (st, r) := ev st "φ + φ"; check "Greek identifiers" r "2*φ"
  (st, r) := ev st "ℯ^x"; check "ℯ^x is exp(x)" r "exp(x)"
  (st, r) := ev st "ln(ℯ)"; check "ln ℯ = 1 through exp(1)" r "1"
  (st, r) := ev st "diff(ℯ^x, x)"; check "d/dx ℯ^x" r "exp(x)"
  (st, r) := ev st "N(ℯ)"; check "N(ℯ)" r "2.71828182845905"
  (st, r) := ev st "N(π)"; check "N(π)" r "3.14159265358979"
  -- complex numbers: i and π are constants; Gaussian arithmetic; exact trig; Euler
  (st, r) := ev st "i^2"; check "i^2" r "-1"
  (st, r) := ev st "i^3"; check "i^3" r "-i"
  (st, r) := ev st "i^(-1)"; check "1/i" r "-i"
  (st, r) := ev st "(1+i)*(2-i)"; check "Gaussian product" r "3 + i"
  (st, r) := ev st "(1+i)^2"; check "Gaussian square" r "2*i"
  (st, r) := ev st "1/(1+i)"; check "Gaussian inverse" r "1/2 - i/2"
  (st, r) := ev st "(2+i)/(1+i)"; check "Gaussian quotient" r "3/2 - i/2"
  (st, r) := ev st "conj(2+3i)"; check "conjugate" r "2 - 3*i"
  (st, r) := ev st "re(2+3i) + im(2+3i)"; check "re and im" r "5"
  (st, r) := ev st "abs(3+4i)"; check "modulus" r "5"
  (st, r) := ev st "sin(pi)"; check "sin π" r "0"
  (st, r) := ev st "cos(pi/3)"; check "cos π/3" r "1/2"
  (st, r) := ev st "sin(3pi/4)"; check "sin 3π/4" r "sqrt(2)/2"
  (st, r) := ev st "tan(pi/4) + tan(pi/3)"; check "tan values" r "sqrt(3) + 1"
  (st, r) := ev st "cos(7pi/6)"; check "cos 7π/6" r "-sqrt(3)/2"
  (st, r) := ev st "ℯ^(pi*i)"; check "Euler's identity" r "-1"
  (st, r) := ev st "exp(i*pi/2)"; check "exp(iπ/2)" r "i"
  (st, r) := ev st "ℯ^(2*pi*i)"; check "exp(2πi)" r "1"
  (st, r) := ev st "N(sin(pi/6))"; check "N of an exact value" r "0.5"
  (st, r) := ev st "diff(sin(pi*x), x)"; check "π is a constant under diff" r "π*cos(π*x)"
  -- user functions with parameters
  (st, r) := ev st "let sq(x) = x^2 + 1"; check "let with parameters" r "x^2 + 1"
  (st, r) := ev st "sq(3)"; check "call a session function" r "10"
  (st, r) := ev st "sq(y)"; check "call with a symbolic argument" r "y^2 + 1"
  (st, r) := ev st "diff(sq(x), x)"; check "differentiate a session function" r "2*x"
  (st, r) := ev st "sq(sq(2))"; check "nested calls" r "26"
  (st, r) := ev st "let g(a, b) = a*b - sq(a)"; check "definition using another function" r "-(a^2 + 1) + a*b"
  (st, r) := ev st "diff(g, b)"; check "a bare function name stands for its body over its parameters" r "a"
  (st, r) := ev st "g(2, 5)"; check "two parameters" r "5"
  (st, r) := ev st "let sqz(zz) = zz^2 + 1"; check "let with a parameter named like a later binding" r "zz^2 + 1"
  (st, r) := ev st "let zz = 7"; check "bind zz" r "7"
  (st, r) := ev st "sqz(2)"; check "a parameter is not captured by a session variable" r "5"
  -- radicals: the single-power normal form, collected and multiplied; displayed the textbook way
  (st, r) := ev st "sqrt(8)+sqrt(2)"; check "radicals collect (same base)" r "3*sqrt(2)"
  (st, r) := ev st "sqrt(50)-sqrt(18)"; check "radicals collect (square-free part)" r "2*sqrt(2)"
  (st, r) := ev st "sqrt(8)*sqrt(2)"; check "radicals multiply" r "4"
  (st, r) := ev st "sqrt(12)*sqrt(3)"; check "radicals multiply under one root" r "6"
  (st, r) := ev st "32^(1/2)"; check "perfect-power base reduced" r "2^(5/2)"
  check "radical display" (match parseStmt "sqrt(8)/2" with | .ok st => (match (normalizeT pipelineRules pipelineOrdered st.value).run' #[] with | .ok e => e.toLatex | .error m => m) | .error _ => "parse") "\\sqrt{2}"
  check "radical display, square-free part" (match parseStmt "5*sqrt(12)" with | .ok st => (match (normalizeT pipelineRules pipelineOrdered st.value).run' #[] with | .ok e => e.toLatex | .error m => m) | .error _ => "parse") "10\\sqrt{3}"
  -- radicals, shown: one row per radical with its work written out; √a = a^(1/2) alone leaves no row
  (st, r) := sessionEval st "sqrt(8)+sqrt(32)" ",\"showWork\":true"
  check "radical steps: perfect-power bases" (derivationRules st "sqrt(8)+sqrt(32)").toString "[simp.radical, simp.radical, simp.collect-radicals]"
  (st, r) := sessionEval st "sqrt(8)+sqrt(18)" ",\"showWork\":true"
  check "radical steps: a square factor" (derivationRules st "sqrt(8)+sqrt(18)").toString "[simp.radical, simp.radical, simp.collect-radicals]"
  (st, r) := sessionEval st "sqrt(x)*sqrt(x)" ",\"showWork\":true"
  check "radical steps: sqrt as a power is silent" ((derivationRules st "sqrt(x)*sqrt(x)").head?.getD "") "simp.collect-powers.assuming"
  -- the laws split at their assumptions: the verified half, and the half whose step states what it assumes
  (st, r) := sessionEval st "x*x" ",\"showWork\":true"
  check "collect powers, integers of one sign: verified" ((derivationRules st "x*x").head?.getD "") "simp.collect-powers"
  (st, r) := sessionEval st "y^(-1)*y^(-2)" ",\"showWork\":true"
  check "collect powers, negative integers: verified" ((derivationRules st "y^(-1)*y^(-2)").head?.getD "") "simp.collect-powers"
  (st, r) := sessionEval st "z*z^(-1)" ",\"showWork\":true"
  check "collect powers, mixed signs: assumes" ((derivationRules st "z*z^(-1)").head?.getD "") "simp.collect-powers.assuming"
  checkTrue "collect powers, mixed signs: the step says b ≠ 0" ((derivationExplanations st "z*z^(-1)").any (contains · "Assuming $z \\neq 0$."))
  check "collect powers, mixed signs: value" r "1"
  checkTrue "collect powers, real exponents: the step says b > 0" ((derivationExplanations st "sqrt(x)*sqrt(x)").any (contains · "Assuming $x > 0$."))
  (st, r) := sessionEval st "exp(ln(w))" ",\"showWork\":true"
  check "exp(ln w): assumes" (derivationRules st "exp(ln(w))").toString "[simp.function.assuming]"
  checkTrue "exp(ln w): the step says w > 0" ((derivationExplanations st "exp(ln(w))").any (contains · "Assuming $w > 0$."))
  (st, r) := sessionEval st "ln(exp(w))" ",\"showWork\":true"
  check "ln(exp w): verified over ℝ" (derivationRules st "ln(exp(w))").toString "[simp.function.real]"
  (st, r) := sessionEval st "ln(w^(1/2))" ",\"showWork\":true"
  check "ln(w^(1/2)): assumes" ((derivationRules st "ln(w^(1/2))").head?.getD "") "simp.function.assuming"
  (st, r) := sessionEval st "ln(w^3)" ",\"showWork\":true"
  check "ln(w^3): verified over ℝ, an odd power" ((derivationRules st "ln(w^3)").head?.getD "") "simp.function.real"
  (st, r) := sessionEval st "diff(ln(w), w)" ",\"showWork\":true"
  check "diff(ln w): the chain rule assumes w > 0" ((derivationRules st "diff(ln(w), w)").head?.getD "") "diff.chain.assuming"
  checkTrue "diff(ln w): the step says so" (((derivationExplanations st "diff(ln(w), w)").head?.getD "").endsWith "Assuming $w > 0$.") r
  (st, r) := sessionEval st "diff(w^3 + sin(w), w)" ",\"showWork\":true"
  check "diff of a smooth sum: verified" ((derivationRules st "diff(w^3 + sin(w), w)").head?.getD "") "diff.sum"
  (st, r) := sessionEval st "diff(w^(1/2), w)" ",\"showWork\":true"
  check "diff(w^(1/2)): a real exponent assumes w > 0" ((derivationRules st "diff(w^(1/2), w)").head?.getD "") "diff.power.assuming"
  (st, r) := sessionEval st "ln(w^2)" ",\"showWork\":true"
  check "ln(w^2): an even power assumes w > 0" ((derivationRules st "ln(w^2)").head?.getD "") "simp.function.assuming"
  (st, r) := sessionEval st "ln(exp(4*i))" ",\"showWork\":true"
  check "ln(exp(4i)) is not 4i over ℂ" r "ln(exp(4*i))"
  -- an exact root: the perfect-power base comes out whole (M drops though 2 + 3 outweighs 4), then evaluates
  (st, r) := sessionEval st "4^(3/2)" ",\"showWork\":true"
  check "radical steps: exact root of a perfect-power base" (derivationRules st "4^(3/2)").toString "[simp.radical, simp.power]"
  check "radical steps: exact root, value" r "8"
  (st, r) := sessionEval st "integrate(sqrt(x), x, 0, 4)" ",\"showWork\":true"
  check "radical steps: exact root at an integral's bound" ((derivationRules st "integrate(sqrt(x), x, 0, 4)").take 4).toString
    "[cmd.integrate, simp.radical, simp.power, simp.fold-constants]"
  check "radical steps: exact root at an integral's bound, value" r "16/3"
  (st, r) := sessionEval st "sqrt(2)*sqrt(6)" ",\"showWork\":true"
  let whys (src : String) : List String :=
    ((st.get "t").cells.lookup src).map (fun c => c.derivation.steps.toList.map (·.explanation)) |>.getD []
  check "radical work: perfect-power base" ((whys "sqrt(8)+sqrt(32)")[1]?.getD "")
    "$32 = 2^{5}$, so $\\sqrt{32} = (2^{5})^{1/2} = 2^{5/2} = 2^{2} \\cdot 2^{1/2} = 4\\sqrt{2}$."
  check "radical work: square factor" ((whys "sqrt(8)+sqrt(18)")[1]?.getD "")
    "$18 = 3^{2} \\cdot 2$, so $\\sqrt{18} = \\sqrt{3^{2}} \\cdot \\sqrt{2} = 3\\sqrt{2}$."
  check "radical work: collect" ((whys "sqrt(8)+sqrt(18)")[2]?.getD "")
    "$2\\sqrt{2} + 3\\sqrt{2} = (2 + 3)\\sqrt{2} = 5\\sqrt{2}$: radicals with the same base and index collect."
  check "radical work: exact root" ((whys "4^(3/2)")[0]?.getD "")
    "$4 = 2^{2}$, so ${4}^{\\frac{3}{2}} = (2^{2})^{3/2} = 2^{3}$."
  check "radical work: multiply" ((whys "sqrt(2)*sqrt(6)")[0]?.getD "")
    "$\\sqrt{2} \\cdot \\sqrt{6} = \\sqrt{12} = 2\\sqrt{3}$: radicals with the same index multiply under one root."
  -- M8: integrate is a checked guess
  (st, r) := ev st "integrate(x^2 + sin(x), x)"; check "integrate sum" r "x^3/3 - cos(x)"
  (st, r) := ev st "integrate(exp(2*x), x)"; check "integrate linear substitution" r "exp(2*x)/2"
  (st, r) := ev st "integrate(x^a, x)"; check "integrate symbolic exponent" r "x^(a + 1)/(a + 1)"
  (st, r) := ev st "integrate(2^x, x)"; check "integrate exponential" r "2^x/ln(2)"
  (st, r) := ev st "diff(integrate(x^3, x), x)"; check "diff of integrate" r "x^3"
  (st, r) := ev st "integrate(integrate(x, x), x)"; check "nested integrate" r "x^3/6"
  (st, r) := ev st "integrate(exp(x)*sin(x), x)"; checkTrue "integrate refuses what it cannot find" (r.startsWith "<error: integrate: no antiderivative") r
  (st, r) := ev st "integrate(tan(x), x)"; check "integrate tan (needs the tan normal form)" r "-ln(cos(x))"
  (st, r) := ev st "sin(x)/cos(x)"; check "simp.function: sin/cos = tan" r "tan(x)"
  (st, r) := ev st "cos(x)^(-1)*y*sin(x)"; check "simp.function: tan with the cosine first" r "y*tan(x)"
  (st, r) := ev st "integrate(x*sin(x), x)"; check "integrate by parts" r "-x*cos(x) + sin(x)"
  (st, r) := ev st "integrate(x*ln(x), x)"; check "integrate by parts, log first" r "x^2*ln(x)/2 - x^2/4"
  (st, r) := ev st "integrate(x^2*exp(x), x)"; check "integrate by parts twice" r "x^2*exp(x) - 2*(x*exp(x) - exp(x))"
  (st, r) := ev st "integrate(ln(x)/x, x)"; check "integrate u as u^1" r "ln(x)^2/2"
  (st, r) := ev st "integrate(sin(x)*cos(x), x)"; check "integrate sin cos" r "-cos(x)^2/2"
  (st, r) := ev st "integrate(x*exp(x^2), x)"; check "integrate by substitution" r "exp(x^2)/2"
  (st, r) := ev st "integrate(x/(x^2+1), x)"; check "integrate by substitution, log" r "ln(x^2 + 1)/2"
  (st, r) := sessionEval st "integrate(5*x^3 - 2*x + 7, x)" ",\"showWork\":true"
  let intSub := (st.get "t").cells.lookup "integrate(5*x^3 - 2*x + 7, x)" >>= fun c => c.derivation.steps.toList.find? (·.rule == "cmd.integrate") >>= (·.sub)
  check "integrate: finder steps end with the check" (intSub.map (fun d => d.steps.toList.map (·.rule)) |>.getD []).toString "[int.sum, int.constant-multiple, int.power, int.constant-multiple, int.variable, int.constant, int.check, int.compare]"
  let checkStep := intSub.bind fun d => d.steps.toList.find? (·.rule == "int.check")
  checkTrue "integrate: the check step carries the differentiation" ((checkStep >>= (·.sub)).map (fun d => d.steps.toList.any (·.rule == "diff.power")) |>.getD false)
  let (st2, raw) := handleS st "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"dx3\",\"source\":\"diff(x^3, x)\",\"showWork\":true,\"paths\":true}}"
  checkTrue "show work: latex paths" ((raw.splitOn "\\htmlData{path=1.0}{x}").length > 1) raw
  let (_, exraw) := handleS st2 "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"engine.explain\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"dx3\",\"path\":[1]}}"
  checkTrue "explain: subterm x^2 with diff.power" ((exraw.splitOn "\"text\":\"x^2\"").length > 1 && (exraw.splitOn "diff.power").length > 1) exraw
  -- M6: the power rule *created* x^2 (through a silent reordering of its exponent); the arithmetic step fired inside it
  -- (one step: fold-constants yields the numeral 2 directly, not a one-term sum for simp.identity to collapse)
  checkTrue "explain trace: x^2 created by step 0, contained by step 1"
    (contains exraw "{\"index\":0,\"relation\":\"created\"}" && contains exraw "{\"index\":1,\"relation\":\"contains\"}" && !contains exraw "{\"index\":2,") exraw
  check "diff(x^3, x) takes two steps" (derivationRules st2 "dx3").toString "[diff.power, simp.fold-constants]"
  let (_, exq) := handleS st2 "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"engine.explain\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"dx3\",\"path\":[0]}}"
  checkTrue "explain trace: the coefficient 3 was copied out of the exponent by step 0 and untouched since"
    (contains exq "\"text\":\"3\"" && contains exq "{\"index\":0,\"relation\":\"copied\"}" && !(contains exq "\"index\":1")) exq
  let (_, exstep) := handleS st2 "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"engine.explain\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"dx3\",\"path\":[],\"term\":{\"kind\":\"step\",\"index\":0}}}"
  checkTrue "explain: root of the term after step 0 relates only step 0" ((exstep.splitOn "\"rule\":").length == 2) exstep
  let (_, exin) := handleS st2 "{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"engine.explain\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"dx3\",\"path\":[],\"term\":{\"kind\":\"input\"}}}"
  checkTrue "explain: the input relates no steps" ((exin.splitOn "\"rule\":").length == 1 && (exin.splitOn "\"steps\":[]").length == 2) exin
  -- wire: RPC round trip
  checkTrue "capabilities" ((rpc "engine.capabilities" "{}").startsWith "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"engine\":\"engine-lean\"")
  check "rpc x + 0" (evalText "x + 0") "x"
  checkTrue "rpc derivation" (contains (rpc "engine.evaluate" "{\"source\":\"x + 0\",\"showWork\":true}") "\"derivation\":{\"input\":{\"k\":\"add\",\"args\":[{\"k\":\"var\",\"name\":\"x\"},{\"k\":\"num\",\"v\":{\"num\":\"0\",\"den\":\"1\"}}]},\"steps\":[{\"rule\":\"simp.identity\",\"explanation\":\"$a + 0 = a$: zero is the additive identity.\",\"path\":[],\"before\":{\"k\":\"add\",\"args\":[{\"k\":\"var\",\"name\":\"x\"},{\"k\":\"num\",\"v\":{\"num\":\"0\",\"den\":\"1\"}}]},\"after\":{\"k\":\"var\",\"name\":\"x\"},\"beforeRendered\":{\"text\":\"x + 0\",\"latex\":\"x + 0\"},\"afterRendered\":{\"text\":\"x\",\"latex\":\"x\"}}],\"output\":{\"k\":\"var\",\"name\":\"x\"},\"inputRendered\":{\"text\":\"x + 0\",\"latex\":\"x + 0\"}}")
  check "rpc syntax error" (evalText "x +") "<error: unexpected end of input>"
  checkTrue "rpc inputRendered" (contains (rpc "engine.evaluate" "{\"source\":\"x + 0\",\"showWork\":true}") "\"inputRendered\":{\"text\":\"x + 0\"")
  checkTrue "rpc ruleStatus" (contains (rpc "engine.capabilities" "{}") "\"rule\":\"simp.collect-powers.assuming\",\"status\":\"conditional\"")
  checkTrue "rpc ruleStatus, the verified half" (contains (rpc "engine.capabilities" "{}") "\"rule\":\"simp.collect-powers\",\"status\":\"verified\"")
  -- every rule of the notebook pipeline has a status in the ledger (a rule absent from it would read as unverified silently)
  let ledger := ruleStatus.render
  for rule in pipelineRules do
    checkTrue s!"ledger lists {rule.name}" (contains ledger s!"\"rule\":\"{rule.name}\"") rule.name
  checkTrue "rpc error span" (contains (rpc "engine.evaluate" "{\"source\":\"3 4\"}") "\"span\":{\"start\":2,\"end\":3}},\"label\":")
  checkTrue "rpc epicycles of points is dft" (contains (rpc "engine.plot" "{\"source\":\"epicycles([1, i, -1, -i])\"}") "\"terms\":[") 
  checkTrue "rpc plot list, first series" (contains (rpc "engine.plot" "{\"source\":\"plot([sin(x), x^2], x, -1, 1, 3)\"}") "\"series\":[{\"rendered\":{\"text\":\"sin(x)\"")
  checkTrue "rpc plot list, second series" (contains (rpc "engine.plot" "{\"source\":\"plot([sin(x), x^2], x, -1, 1, 3)\"}") "{\"rendered\":{\"text\":\"x^2\"")
  checkTrue "rpc plot list normalizes entries" (contains (rpc "engine.plot" "{\"source\":\"plot([diff(x^2, x), x + 0], x, -1, 1, 3)\"}") "\"series\":[{\"rendered\":{\"text\":\"2*x\"")
  checkTrue "rpc plot single is one series" (contains (rpc "engine.plot" "{\"source\":\"plot(x, x, 0, 1, 2)\"}") "\"series\":[{\"rendered\":{\"text\":\"x\",\"latex\":\"x\"},\"points\":[[")
  checkTrue "rpc plot rejects a matrix" (contains (rpc "engine.plot" "{\"source\":\"plot([1, 2; 3, 4], x, 0, 1)\"}") "not a matrix")
  -- manipulate: any body, once per value of the parameter; a plot body is sampled per frame
  let man := rpc "engine.manipulate" "{\"source\":\"manipulate(diff(x^n, x), n, 1, 3, 3)\"}"
  checkTrue "rpc manipulate: kind and parameter" (contains man "\"kind\":\"manipulate\"" && contains man "\"param\":\"n\"") man
  checkTrue "rpc manipulate: each frame's normal form" (contains man "\"rendered\":{\"text\":\"1\"" && contains man "\"rendered\":{\"text\":\"2*x\"" && contains man "\"rendered\":{\"text\":\"3*x^2\"") man
  checkTrue "rpc manipulate: three frames" ((man.splitOn "\"valueRendered\"").length == 4) man
  checkTrue "rpc manipulate: exact values, either way round" (contains (rpc "engine.manipulate" "{\"source\":\"manipulate(h, h, 1, 0, 3)\"}") "\"valueRendered\":{\"text\":\"1/2\"")
  let manp := rpc "engine.manipulate" "{\"source\":\"manipulate(plot(h, x, 0, 1, 2), h, 0, 1, 2)\"}"
  checkTrue "rpc manipulate plot: a frame's samples follow the parameter"
    (contains manp s!"\"points\":[[{toString (0 : Float)},{toString (1 : Float)}],[{toString (1 : Float)},{toString (1 : Float)}]]") manp
  checkTrue "rpc manipulate plot: the plot's own variable is refused" (contains (rpc "engine.manipulate" "{\"source\":\"manipulate(plot(x, x, 0, 1), x, 0, 1)\"}") "the plot's own variable")
  checkTrue "rpc manipulate: the range must be numbers" (contains (rpc "engine.manipulate" "{\"source\":\"manipulate(h, h, 0, y)\"}") "the range must evaluate to numbers")
  checkTrue "rpc manipulate: the cell's value is the first frame's" (contains (rpc "engine.manipulate" "{\"source\":\"manipulate(h + 1, h, 0, 1, 2)\"}") "\"value\":{\"k\":\"num\",\"v\":{\"num\":\"1\",\"den\":\"1\"}}")
  let (stm, _) := handleS [] "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.manipulate\",\"params\":{\"sessionId\":\"m\",\"cellId\":\"a\",\"source\":\"manipulate(h + 1, h, 0, 1, 2)\"}}"
  let (_, hAfter) := handleS stm "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"m\",\"cellId\":\"b\",\"source\":\"h\"}}"
  checkTrue "rpc manipulate: the parameter is bound only inside the frames" (contains hAfter "\"rendered\":{\"text\":\"h\"") hAfter
  -- column: each part evaluated as its own cell; a term keeps its calculation, ending in its value
  let col := rpc "engine.manipulate" "{\"source\":\"manipulate(column(h + 1, plot(h, x, 0, 1, 2)), h, 0, 1, 2)\"}"
  checkTrue "rpc manipulate column: each frame's parts" (contains col "\"parts\":[{\"rendered\":{\"text\":\"1\"" && contains col "\"parts\":[{\"rendered\":{\"text\":\"2\"") col
  checkTrue "rpc manipulate column: a plot part is sampled" (contains col "\"plot\":{\"var\":\"x\"") col
  checkTrue "rpc manipulate column: the cell's value is the column" (contains col "\"rendered\":{\"text\":\"column(") col
  let wk := rpc "engine.manipulate" "{\"source\":\"manipulate(h*h + 1, h, 3, 4, 2)\"}"
  checkTrue "rpc manipulate: a term's calculation, ending in its value" (contains wk "\"work\":[" && contains wk "{\"text\":\"10\",\"latex\":\"10\"}]") wk
  checkTrue "rpc manipulate: one body has no parts" (!(contains manp "\"parts\"")) manp
  let (stl, _) := handleS [] "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"l\",\"cellId\":\"a\",\"source\":\"let m = h + 1\"}}"
  let (_, lab) := handleS stl "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"engine.manipulate\",\"params\":{\"sessionId\":\"l\",\"cellId\":\"b\",\"source\":\"manipulate(column(m, h), h, 0, 1, 2)\"}}"
  checkTrue "rpc manipulate column: a part that is a bound name is labelled with it" ((lab.splitOn "\"label\":\"m\"").length == 3 && !(contains lab "\"label\":\"h\"")) lab
  checkTrue "rpc value json" ((rpc "engine.evaluate" "{\"source\":\"2x\"}").startsWith "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"ok\":true,\"value\":{\"k\":\"mul\",\"args\":[{\"k\":\"num\",\"v\":{\"num\":\"2\",\"den\":\"1\"}},{\"k\":\"var\",\"name\":\"x\"}]}")

/-- The certified `N`'s Taylor sums are taken in interval arithmetic (`expSumI`, `trigSumI`): each
interval holds the exact sum it stands for, and stays narrow; `remainder` rounds `|y|` up, never down. -/
def intervalTests : TestM Unit := do
  let narrow (a : Ival.I) : Bool := a.hi - a.lo < 1 / ((2 ^ 180 : Nat) : Rat)
  for y in [(7 : Rat) / 8, -1, 1, 0, 1 / 3, -5 / 7, 123456789 / 987654321] do
    let e := (Ival.expSumI y Ival.terms).1
    let x := Ival.expSum y Ival.terms
    checkTrue s!"interval: expSumI holds expSum at {y}" (e.lo ≤ x && x ≤ e.hi && narrow e)
    let (c, sn, _) := Ival.trigSumI y Ival.terms
    let cx := Ival.cosSum y Ival.terms
    let sx := Ival.sinSum y Ival.terms
    checkTrue s!"interval: trigSumI holds cosSum and sinSum at {y}" (c.lo ≤ cx && cx ≤ c.hi && sn.lo ≤ sx && sx ≤ sn.hi && narrow c && narrow sn)
    checkTrue s!"interval: the remainder is at least Taylor's at {y}"
      (Ival.rabs y ^ Ival.terms * ((Ival.terms + 1 : Nat) : Rat) / ((Ival.fact Ival.terms * Ival.terms : Nat) : Rat) ≤ Ival.remainder y Ival.terms)
  -- the paths that went through the slow exact sums: still certified
  let mut st : Store := []
  for src in ["N(sqrt(2))", "N(e^3.5)", "N(ln(2))", "N(arctan(1/3))", "N(2^(1/3))", "N(sqrt(0))"] do
    (st, _) := sessionEval st src ",\"showWork\":true"
  let lastRule (src : String) : String :=
    ((st.get "t").cells.lookup src >>= fun c => c.derivation.steps.toList.getLast? |>.map (·.rule)).getD ""
  for src in ["N(sqrt(2))", "N(e^3.5)", "N(ln(2))", "N(arctan(1/3))", "N(2^(1/3))"] do
    check s!"interval: {src} is certified" (lastRule src) "cmd.N"
  -- a variable named e is not Euler's number: the answer says so
  let warns (src : String) : Bool := contains (rpc "engine.evaluate" s!"\{\"sessionId\":\"w\",\"cellId\":\"c\",\"source\":\"{src}\"}") "\"warnings\""
  checkTrue "warnings: e^x warns that e is a variable" (warns "e^x")
  checkTrue "warnings: N(e^3.5) warns too" (warns "N(e^3.5)")
  checkTrue "warnings: ℯ^x does not warn" (!warns "ℯ^x")
  checkTrue "warnings: exp(x) does not warn" (!warns "exp(x)")
  checkTrue "warnings: a parameter named e does not warn" (!warns "let g(e) = e^2")

/-- `N` over ℂ: certified where the rectangle reaches, double precision where it does not. -/
def complexNTests : TestM Unit := do
  let mut st : Store := []
  for src in ["N(exp(i*pi/4))", "N((-8)^(1/3))", "N(ln(i))", "N(i^i)", "N((1+i)^(1/2))", "N(ln(-1 + (sin(1)^2 + cos(1)^2 - 1)*i))"] do
    (st, _) := sessionEval st src ",\"showWork\":true"
  let lastRule (src : String) : String :=
    ((st.get "t").cells.lookup src >>= fun c => c.derivation.steps.toList.getLast? |>.map (·.rule)).getD ""
  check "N: a complex value is certified" (lastRule "N(exp(i*pi/4))") "cmd.N"
  check "N: a negative base under a real power is certified" (lastRule "N((-8)^(1/3))") "cmd.N"
  check "N: the log of a non-real number is certified, through a certified arctan" (lastRule "N(ln(i))") "cmd.N"
  check "N: a non-real base under a non-real power is certified" (lastRule "N(i^i)") "cmd.N"
  check "N: a non-real base under a fractional power is certified" (lastRule "N((1+i)^(1/2))") "cmd.N"
  check "N: on the branch cut, where the argument jumps, it is not" (lastRule "N(ln(-1 + (sin(1)^2 + cos(1)^2 - 1)*i))") "cmd.N.float"

/-- A term with every numeral exact: a decimal answer prints as the numeral it is. -/
partial def exact : Expr → Expr
  | .num q => .num { q with approx := false }
  | .add es => .add (es.map exact)
  | .mul es => .mul (es.map exact)
  | .pow b e => .pow (exact b) (exact e)
  | .fn f as => .fn f (as.map exact)
  | .matrix rows => .matrix (rows.map (·.map exact))
  | e => e

/-- M2 golden test: `Tests/golden.tsv` holds the reference engine's rendered text for a corpus of
sources, evaluated in one session in file order (so `let` bindings carry over). It was produced by the
wire-level differential test that ran both engines (`scripts/difftest.mjs`, last present in commit
680e360) with zero mismatches, and it is what stands in for the deleted reference. -/
def goldenTests : TestM Unit := do
  let lines ← (IO.FS.lines "Tests/golden.tsv").toBaseIO >>= fun r => match r with
    | .ok ls => pure ls.toList
    | .error e => do modify (·.push ⟨"golden file", "readable", toString e⟩); pure []
  let mut st : Store := []
  for line in lines do
    match line.splitOn "\t" with
    | [source, expected] =>
      let (st', actual) := sessionEval st source
      st := st'
      check s!"golden: {source}" actual expected
      -- every subterm the notebook can click names a real path (`engine.explain` takes it)
      match (st.get "t").cells.lookup source with
      | some cell =>
        check s!"golden paths: {source}" (toString (badPaths cell.output)) "[]"
        -- the text shown means the term the proofs are about: it parses back to the same term
        let txt := cell.output.toText
        -- (a text that is not algebra at all, a set or a formula, is another world's and is skipped)
        let otherWorld := cell.derivation.steps.any (·.rule.startsWith "trs.")
        if let (.ok b, false) := (parse txt ((st.get "t").fns.map (·.1)), otherWorld) then
          -- the same term, or (where the pipeline has two normal forms for one value, as for
          -- (x^(1/2))^(-1) and x^(-1/2), which it rightly does not merge over ℝ) one printed the same
          let ok := match (normCell b).1 with
            | .ok out => Expr.equal (exact out) (exact cell.output) || out.toText == txt
            | .error _ => false
          let why := match (normCell b).1 with
            | .ok out => s!"reads back as {out.toText}: {repr out}, not {repr cell.output}"
            | .error msg => msg
          checkTrue s!"golden round trip: {source} ↦ {txt}" ok why
      | none => pure ()
    | _ => pure ()

/-- Part (`m[[…]]`) and the statistics. -/
def partStatTests : TestM Unit := do
  -- Part, Mathematica's indexing: from 1, negative from the end, All, spans, lists
  check "part parses and prints" (roundtrip "m[[2, 1;;3]]") "m[[2, 1;;3]]"
  check "part: omitted span ends" (roundtrip "m[[;;2, 2;;, All, {1, 3}, 1;;-1;;2]]") "m[[1;;2, 2;;-1, All, {1, 3}, 1;;-1;;2]]"
  check "part binds tighter than ^" (roundtrip "v[[1]]^2") "v[[1]]^2"
  check "part latex" (latexOf "m[[2, All]]") "m\\llbracket 2, \\mathrm{All}\\rrbracket"
  check "part: a row" (evalText "[1,2,3;4,5,6;7,8,9][[2]]") "[4, 5, 6]"
  check "part: an entry" (evalText "[1,2,3;4,5,6;7,8,9][[2, 3]]") "6"
  check "part: a column stays a column" (evalText "[1,2,3;4,5,6;7,8,9][[All, 2]]") "[2; 5; 8]"
  check "part: span and list" (evalText "[1,2,3;4,5,6;7,8,9][[1;;2, {1, 3}]]") "[1, 3; 4, 6]"
  check "part: from the end" (evalText "[1,2,3;4,5,6;7,8,9][[-1, -1]]") "9"
  check "part: a negative step" (evalText "[1,2,3;4,5,6;7,8,9][[3;;1;;-1, 1]]") "[7; 4; 1]"
  check "part: a vector takes one index" (evalText "[10, 20, 30][[2]]") "20"
  check "part: a column vector's span" (evalText "[10; 20; 30][[2;;]]") "[20; 30]"
  check "part: out of range" (evalText "[1, 2, 3][[4]]") "<error: part 4 of 3: the index runs from 1 to 3 (or -3 to -1)>"
  check "part: no part 0" (evalText "[1, 2, 3][[0]]") "<error: parts count from 1 (and -1 is the last); there is no part 0>"
  check "part: too many indices" (evalText "[1, 2; 3, 4][[1, 2, 1]]") "<error: a matrix has two dimensions; 3 indices were given>"
  check "part: an empty span" (evalText "[1, 2, 3][[3;;1]]") "<error: the span 3;;1 selects nothing>"
  check "part of a symbol stays" (evalText "x[[1]]") "x[[1]]"
  check "braces outside a part" (evalText "{1, 2}") "<error: braces list the indices of a part, as in m[[{1, 3}]]>"
  -- statistics: definitions, so symbolic entries work; a matrix gives its columns' statistics
  check "total" (evalText "total([1; 2; 3])") "6"
  check "mean" (evalText "mean([1, 2, 3, 4])") "5/2"
  check "mean symbolic" (evalText "mean([a; b])") "(a + b)/2"
  check "mean of a matrix is by column" (evalText "mean([1, 2, 3; 4, 5, 6; 7, 8, 9])") "[4, 5, 6]"
  check "sample variance" (evalText "variance([2, 4, 4, 4, 5, 5, 7, 9])") "32/7"
  check "variance symbolic" (evalText "variance([a, b])") "a^2 + b^2 - (a + b)^2/2"
  check "stdev" (evalText "stdev([1, 3])") "sqrt(2)"
  check "variance of one value" (evalText "variance([1])") "<error: variance needs at least two values (it divides by n − 1)>"
  check "median odd" (evalText "median([5, 1, 3])") "3"
  check "median even" (evalText "median([4, 1, 3, 2])") "5/2"
  check "min" (evalText "min([3, -1, 2.5])") "-1"
  check "max" (evalText "max([3, -1, 2.5])") "3"
  check "min needs numbers" (evalText "min([a, 1])") "<error: min compares numbers; an entry is not a number>"
  check "a statistic of a part" (evalText "mean([1,2,3;4,5,6;7,8,9][[All, 2]])") "5"

/-- Show work for big terms: entrywise steps (`buildSteps`), outline replies and `engine.steps`. -/
def workTests : TestM Unit := do
  -- entrywise: a run of rewrites inside one matrix's entries is one step, each entry's steps nested
  -- with the entry alone as their term, so the derivation grows with the matrix, not its square
  let (st3, _) := sessionEval [] "[1,2;3,4]*2" ",\"showWork\":true"
  check "entrywise: scalar multiple, then entry by entry" (derivationRules st3 "[1,2;3,4]*2").toString "[la.scalar-mul, la.entrywise]"
  let ew := (st3.get "t").cells.lookup "[1,2;3,4]*2" >>= fun c => c.derivation.steps[1]?
  check "entrywise: the step spans the matrix" ((ew.map fun s => s!"{s.before.toText} -> {s.after.toText}").getD "") "[2*1, 2*2; 2*3, 2*4] -> [2, 4; 6, 8]"
  check "entrywise: nested steps on the entries alone"
    ((ew >>= (·.sub)).map (fun d => d.steps.toList.map fun s => s!"{s.before.toText} -> {s.after.toText}") |>.getD []).toString
    "[1*2 -> 2, 2*2 -> 4, 2*3 -> 6, 2*4 -> 8]"
  checkTrue "entrywise: a nested step says which entry" ((ew >>= (·.sub) >>= (·.steps[2]?)).map (fun s => contains s.explanation "(row 2, column 1).") |>.getD false)
  let (st3, _) := sessionEval st3 "[x+x, 1]" ",\"showWork\":true"
  check "entrywise: one entry rewritten stays as it was" (derivationRules st3 "[x+x, 1]").toString "[simp.collect-like-terms, simp.identity]"
  let (_, exew) := handleS st3 "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"engine.explain\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"[1,2;3,4]*2\",\"path\":[2]}}"
  checkTrue "entrywise: explain an entry: created by the entrywise step" (contains exew "\"text\":\"6\"" && contains exew "{\"index\":1,\"relation\":\"created\"}") exew
  -- outline: the steps without their terms; engine.steps sends the derivation an eager reply would have
  let req (id method params : String) := s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"{method}\",\"params\":{params}}"
  let (st4, oraw) := handleS [] (req "7" "engine.evaluate" "{\"sessionId\":\"o\",\"cellId\":\"a\",\"source\":\"[1,2;3,4]*2\",\"showWork\":true,\"outline\":true,\"paths\":true}")
  checkTrue "outline: rules and paths, no terms" (contains oraw "\"outline\":{\"steps\":[{\"rule\":\"la.scalar-mul\"" && !contains oraw "\"derivation\"" && !contains oraw "\"before\"" && contains oraw "\"inputRendered\"") oraw
  let (st4, sraw) := handleS st4 (req "8" "engine.steps" "{\"sessionId\":\"o\",\"cellId\":\"a\",\"paths\":true}")
  let (_, eraw) := handleS st4 (req "9" "engine.evaluate" "{\"sessionId\":\"o\",\"cellId\":\"b\",\"source\":\"[1,2;3,4]*2\",\"showWork\":true,\"paths\":true}")
  let deriv (raw : String) := ((Json.parse raw).toOption >>= (·.get? "result") >>= (·.get? "derivation")).map (·.render)
  checkTrue "engine.steps: the derivation an eager reply carries" (deriv sraw == deriv eraw && (deriv sraw).isSome) sraw
  checkTrue "outline: a step that prints the same is quiet" (contains (rpc "engine.evaluate" "{\"source\":\"1/x\",\"showWork\":true,\"outline\":true}") "\"quiet\":true")
  checkTrue "engine.steps: an unknown cell is an error" (contains (rpc "engine.steps" "{\"sessionId\":\"o\",\"cellId\":\"zz\"}") "\"error\":{\"code\":-32000")
  let (st5, _) := handleS [] (req "10" "engine.evaluate" "{\"sessionId\":\"l\",\"cellId\":\"a\",\"source\":\"(λx. x) y\",\"showWork\":true,\"outline\":true}")
  checkTrue "engine.steps: a λ-cell's steps keep their de Bruijn view" (contains (handleS st5 (req "11" "engine.steps" "{\"sessionId\":\"l\",\"cellId\":\"a\"}")).2 "\"afterDeBruijn\"")

/-- Exercises (`engine.check`): an answer is right when it reduces to the question's normal form. -/
def checkTests : TestM Unit := do
  let ask (q a : String) := rpc "engine.check" s!"\{\"sessionId\":\"x\",\"cellId\":\"e\",\"source\":\"{q}\",\"answer\":\"{a}\"}"
  let eqv (q a : String) := contains (ask q a) "\"equivalent\":true"
  checkTrue "check: the answer as the engine writes it" (eqv "diff(x^2*sin(x), x)" "2x sin(x) + x^2 cos(x)")
  checkTrue "check: a factored answer" (eqv "diff(x^2*sin(x), x)" "x(2sin(x) + x cos(x))")
  checkTrue "check: a wrong answer" (!eqv "diff(x^2*sin(x), x)" "2x sin(x)")
  checkTrue "check: the identity the integration check knows" (eqv "integrate(cos(x)^2*sin(x), x)" "-cos(x)^3/3")
  checkTrue "check: the work is not an answer" (contains (ask "diff(x^2, x)" "diff(x^2 + 0, x)") "the answer may not use diff")
  checkTrue "check: the question is not its own answer" (contains (ask "[1, 2; 3, 4]*[0, 1; 1, 0]" "[1,2;3,4] * [0,1;1,0]") "that is the question itself")
  checkTrue "check: a matrix answer" (eqv "[1, 2; 3, 4]*[0, 1; 1, 0]" "[2, 1; 4, 3]")
  checkTrue "check: elementary functions are allowed" (eqv "diff(sin(x^2), x)" "2x cos(x^2)")
  checkTrue "check: i is a value, not work" (eqv "i*(1 + 2i)" "-2 + i")
  checkTrue "check: so is π" (eqv "exptotrig(exp(i*pi/2))" "i")
  checkTrue "check: a syntax error in the answer" (contains (ask "diff(x^2, x)" "2x +") "\"answer\":{\"ok\":false,\"error\":{\"code\":\"syntax\"")
  checkTrue "check: λ normal forms up to α" (eqv "add 2 1" "λg. λy. g (g (g y))")
  checkTrue "check: a different λ normal form" (!eqv "add 2 1" "λf. λx. f (f x)")
  checkTrue "check: a λ answer with a redex" (contains (ask "add 2 1" "succ 2") "reduce it to normal form")
  checkTrue "check: a cbv value, compared as written" (eqv "cbv: (λx. x) (λy. (λz. z) y)" "λa. (λb. b) a")
  checkTrue "check: not a cbv value" (!eqv "cbv: (λx. x) (λy. (λz. z) y)" "λa. a")
  checkTrue "check: free variables as a set" (eqv "fv: λx. x y (λy. y z)" "{z, y}")
  checkTrue "check: free variables, one missing" (!eqv "fv: λx. x y (λy. y z)" "{y}")
  checkTrue "check: α-equivalence" (eqv "alpha: λx. x, λy. y" "true")
  checkTrue "check: a type" (eqv "type: λf:A→B. λx:A. f x" "(A -> B) -> A -> B")
  checkTrue "check: a type is not up to renaming" (!eqv "type: λx:A. x" "B -> B")
  checkTrue "check: an inferred type up to renaming" (eqv "infer: K" "a -> b -> a")
  checkTrue "check: an inferred type, too special" (!eqv "infer: K" "a -> a -> a")
  checkTrue "check: a substitution up to α" (eqv "subst: λy. x y, x := y" "λz. y z")
  let tree := rpc "engine.evaluate" "{\"sessionId\":\"x\",\"cellId\":\"t\",\"source\":\"type: λx:A. x\"}"
  checkTrue "λ: type: draws its derivation" (contains tree "\"kind\":\"typing.tree\"" && contains tree "\"rule\":\"→I\"" && contains tree "x : A \\\\vdash x : A") tree
  let noAnswer := rpc "engine.check" "{\"sessionId\":\"x\",\"cellId\":\"e\",\"source\":\"expand((x+1)^2)\",\"showWork\":true}"
  checkTrue "check: without an answer, the solution and its work" (contains noAnswer "\"rendered\":{\"text\":\"x^2 + 2*x + 1\"" && contains noAnswer "\"derivation\"" && !contains noAnswer "\"equivalent\"") noAnswer
  -- a check is not an evaluation: no label, no binding, and % is untouched
  let req (id method params : String) := s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"{method}\",\"params\":{params}}"
  let (st, _) := handleS [] (req "1" "engine.evaluate" "{\"sessionId\":\"p\",\"cellId\":\"a\",\"source\":\"let f = x^3\"}")
  let (st, craw) := handleS st (req "2" "engine.check" "{\"sessionId\":\"p\",\"cellId\":\"q\",\"source\":\"diff(f, x)\",\"answer\":\"3x^2\"}")
  checkTrue "check: the session's names" (contains craw "\"equivalent\":true" && !contains craw "\"label\"") craw
  let (_, praw) := handleS st (req "3" "engine.evaluate" "{\"sessionId\":\"p\",\"cellId\":\"b\",\"source\":\"%\"}")
  checkTrue "check: % is the last evaluation's" (contains praw "\"text\":\"x^3\"" && contains praw "\"label\":2") praw

/-- The logic world and relations: the steps the normal forms take, the witnesses, the visuals. -/
def logicRelTests : TestM Unit := do
  let ev (src : String) := rpc "engine.evaluate" s!"\{\"sessionId\":\"lg\",\"cellId\":\"c\",\"source\":\"{src}\",\"showWork\":true}"
  checkTrue "logic: cnf distributes, one law a step" (contains (ev "cnf(p ∨ (q ∧ r))") "\"rule\":\"logic.distribute\"")
  checkTrue "logic: nnf names De Morgan" (contains (ev "nnf(¬(p ∧ q))") "\"rule\":\"logic.de-morgan\"")
  checkTrue "logic: taut's counterexample row, in the work" (contains (ev "taut(p → q)") "False when p = true, q = false: not a tautology.")
  checkTrue "logic: equiv's distinguishing row, in the work" (contains (ev "equiv(p → q, q → p)") "They differ when p = true, q = false")
  checkTrue "logic: no note beside the answer" (!contains (ev "taut(p → q)") "\"summary\"" && !contains (ev "truthtable(p ∧ q)") "\"summary\"")
  checkTrue "logic: sat's answer is the assignment, as a map" (contains (ev "sat((p ∨ q) ∧ ¬p)") "\"text\":\"{p↦false, q↦true}\"")
  let lg (st : Store) (id src : String) := handleS st s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"engine.evaluate\",\"params\":\{\"sessionId\":\"lgw\",\"cellId\":\"{id}\",\"source\":\"{src}\"}}"
  let (stW, _) := lg [] "1" "let w = falsify(p → q)"
  checkTrue "logic: a let binds the assignment as its literals' conjunction" (contains (lg stW "2" "equiv(w, p ∧ ¬q)").2 "\"text\":\"⊤\"") (lg stW "2" "equiv(w, p ∧ ¬q)").2
  checkTrue "logic: a truth table is a visual" (contains (ev "truthtable(p ∧ q)") "\"kind\":\"logic.truthtable\"")
  checkTrue "logic: a truth table's rows" (contains (ev "truthtable(p ∧ q)") "\"rows\":[[true,true,true],[true,false,false],[false,true,false],[false,false,false]]")
  checkTrue "logic: a ∀ names its counterexample" (contains (ev "∀ n ∈ 1..10, n^2 ≥ 2n") "at $n = 1$")
  checkTrue "logic: an ∃ names its witness" (contains (ev "∃ n ∈ {4, 6, 9, 11}, prime(n)") "at $n = 11$")
  checkTrue "logic: a λ-cell stays a λ-cell" (contains (ev "(λx. x) y") "\"kind\":\"lambda\"")
  checkTrue "logic: a math cell stays a math cell" (contains (ev "diff(x^2, x)") "\"text\":\"2*x\"")
  let (st, _) := sessionEval [] "let R = rel({a, b, c}; a->b, b->c)"
  let (_, traw) := handleS st "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"x\",\"source\":\"transitive(R)\",\"showWork\":true}}"
  checkTrue "relations: the pairs that break transitivity are marked" (contains traw "\"bad\":[[\"a\",\"b\"],[\"b\",\"c\"]]") traw
  let (_, craw) := handleS st "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"engine.evaluate\",\"params\":{\"sessionId\":\"t\",\"cellId\":\"y\",\"source\":\"closure(R, transitive)\",\"showWork\":true}}"
  checkTrue "relations: a closure marks what it added, a round a step" (contains craw "\"added\":[[\"a\",\"c\"]]" && contains craw "\"rule\":\"rel.transitive-closure\"") craw
  -- exercises in these worlds
  let ask (q a : String) := rpc "engine.check" s!"\{\"sessionId\":\"x\",\"cellId\":\"e\",\"source\":\"{q}\",\"answer\":\"{a}\"}"
  let eqv (q a : String) := contains (ask q a) "\"equivalent\":true"
  checkTrue "check logic: a CNF" (eqv "cnf(p → (q ∧ r))" "(¬p ∨ q) ∧ (¬p ∨ r)")
  checkTrue "check logic: equivalent but not CNF" (contains (ask "cnf(p → (q ∧ r))" "¬p ∨ (q ∧ r)") "the answer must be in CNF")
  checkTrue "check logic: a CNF of something else" (!eqv "cnf(p → (q ∧ r))" "(¬p ∨ q) ∧ (p ∨ r)")
  checkTrue "check logic: a tautology is true" (eqv "taut(p ∨ ¬p)" "true" && !eqv "taut(p ∨ ¬p)" "⊥")
  checkTrue "check logic: any satisfying assignment" (eqv "sat(p ∧ ¬q)" "p ∧ ¬q" && !eqv "sat(p ∧ ¬q)" "p")
  checkTrue "check logic: unsatisfiable is ⊥" (eqv "sat(p ∧ ¬p)" "false")
  checkTrue "check logic: an assignment as the map the engine answers with" (eqv "sat(p ∧ ¬q)" "{p ↦ true, q ↦ false}" && eqv "falsify(p → q)" "{p -> true, q = false}" && !eqv "sat(p ∧ ¬q)" "{p ↦ true, q ↦ true}")
  checkTrue "check logic: an equivalent formula" (eqv "p → q" "¬p ∨ q" && !eqv "p → q" "q → p")
  checkTrue "check logic: a bounded ∀" (eqv "∀ x ∈ 1..5, x < 6" "true")
  let req (id src : String) := s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"engine.evaluate\",\"params\":\{\"sessionId\":\"r\",\"cellId\":\"d{id}\",\"source\":\"{src}\"}}"
  let (st, _) := handleS [] (req "1" "let R = rel({a, b, c}; a->b, b->c)")
  let (st, _) := handleS st (req "2" "let K = kernel({r1, r2, r3, r4}; r1->k1, r2->k1, r3->k2, r4->k2)")
  let askR (q a : String) := (handleS st s!"\{\"jsonrpc\":\"2.0\",\"id\":9,\"method\":\"engine.check\",\"params\":\{\"sessionId\":\"r\",\"cellId\":\"q\",\"source\":\"{q}\",\"answer\":\"{a}\"}}").2
  let eqvR (q a : String) := contains (askR q a) "\"equivalent\":true"
  checkTrue "check relations: a closure's pairs, in any order or notation" (eqvR "closure(R, transitive)" "a->b, b->c, a->c" && eqvR "closure(R, transitive)" "(a, c), (a, b), (b, c)")
  checkTrue "check relations: a closure missing a pair" (!eqvR "closure(R, transitive)" "a->b, b->c")
  checkTrue "check relations: a property" (eqvR "transitive(R)" "false" && !eqvR "transitive(R)" "true")
  checkTrue "check relations: classes, in any order" (eqvR "classes(K)" "{r2, r1}, {r3, r4}" && !eqvR "classes(K)" "{r1}, {r2, r3, r4}")

/-- Finite algebra (`Algebra.lean`): the tables and contexts the notebook draws, the cells a failing law
marks, and elements written as pairs or sets. -/
def algebraTests : TestM Unit := do
  let req (id src : String) := s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"engine.evaluate\",\"params\":\{\"sessionId\":\"a\",\"cellId\":\"c{id}\",\"source\":\"{src}\",\"showWork\":true}}"
  let (st, opRaw) := handleS [] (req "1" "let F = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, deny, deny])")
  checkTrue "algebra: an operation is drawn as its table" (contains opRaw "\"kind\":\"algebra.optable\"" && contains opRaw "\"rows\":[[\"na\",\"permit\",\"deny\"],[\"permit\",\"permit\",\"permit\"],[\"deny\",\"deny\",\"deny\"]]") opRaw
  let (st, cRaw) := handleS st (req "2" "commutative(F)")
  checkTrue "algebra: a failing law marks the two cells that differ" (contains cRaw "\"marks\":[[\"permit\",\"deny\"],[\"deny\",\"permit\"]]" && contains cRaw "\"rule\":\"alg.commutative\"") cRaw
  let (st, fRaw) := handleS st (req "3" "fold(F; na, deny, permit)")
  checkTrue "algebra: a fold is a step per element" (contains fRaw "\"text\":\"deny\"" && contains fRaw "\"rule\":\"alg.fold\"") fRaw
  let (st, _) := handleS st (req "4" "let Lv = poset({low, high}; low < high)")
  let (st, _) := handleS st (req "5" "let Cat = subsets({fin, hr})")
  let (st, _) := handleS st (req "6" "let SC = product(Lv, Cat)")
  let (st, jRaw) := handleS st (req "7" "join(SC, (low, {hr, fin}), ( high , {} ))")
  checkTrue "algebra: pair elements, written with any spacing and set order" (contains jRaw "\"text\":\"(high, {fin,hr})\"") jRaw
  let (_, xRaw) := handleS st (req "8" "let X = context({duck, dog}, {flies, mammal}; duck->flies, dog->mammal)")
  checkTrue "algebra: a context is drawn as its cross table" (contains xRaw "\"kind\":\"context.table\"" && contains xRaw "\"has\":[[true,false],[false,true]]") xRaw

/-- The systems world: a system written over several lines, its state graph, a counterexample's
trace marked on it, and the Kleene iterations of a CTL formula as steps. -/
def systemsTests : TestM Unit := do
  let req (id src : String) := s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"engine.evaluate\",\"params\":\{\"sessionId\":\"s\",\"cellId\":\"c{id}\",\"source\":\"{src}\",\"showWork\":true}}"
  let (st, defRaw) := handleS [] (req "1" "let C = system(\\n  var x in 0..2\\n  init x = 0\\n  action inc when x < 2 do x := x + 1\\n)")
  checkTrue "systems: a system over several lines, its graph drawn" (contains defRaw "\"kind\":\"system\"" && contains defRaw "\"edges\":[[\"0\",\"1\"],[\"1\",\"2\"]]") defRaw
  let (st, invRaw) := handleS st (req "2" "invariant(C, x ≤ 1)")
  checkTrue "systems: a counterexample's trace is marked on the graph" (contains invRaw "\"bad\":[[\"0\",\"1\"],[\"1\",\"2\"]]") invRaw
  checkTrue "systems: each step of the trace names its action" (contains invRaw "\"explanation\":\"inc (x < 2 holds): x := x + 1.\"") invRaw
  let (_, ctlRaw) := handleS st (req "3" "ctl(C, EF x = 2)")
  checkTrue "systems: a CTL formula's fixed point, a round a step" (contains ctlRaw "\"rule\":\"sys.iterate\"" && contains ctlRaw "\"rule\":\"sys.fixed\"") ctlRaw

/-- Inverse trigonometric functions, and `sec`, `csc`, `cot` and `f^-1(x)` as reciprocals. -/
def trigTests : TestM Unit := do
  let (_, r) := sessionEval {} "sin^-1(y)"; check "sin^-1(y) is the reciprocal, not arcsin" r "1/sin(y)"
  let (_, r) := sessionEval {} "tan^-2(y)"; check "a negative power before the argument" r "1/tan(y)^2"
  let (_, r) := sessionEval {} "sec(y) + csc(y) + cot(y)"; check "sec, csc and cot are read as reciprocals" r "1/cos(y) + 1/sin(y) + 1/tan(y)"
  let (_, r) := sessionEval {} "sec^2(y)"; check "sec^2(y) is cos(y)^-2" r "1/cos(y)^2"
  let (_, r) := sessionEval {} "sec(y, 2)"; check "sec with two arguments is left alone" r "sec(y, 2)"
  let (_, r) := sessionEval {} "cosh(y)"; check "cosh is read as its definition" r "(exp(y) + exp(-y))/2"
  let (_, r) := sessionEval {} "sinh(y)"; check "sinh is read as its definition" r "(exp(y) - exp(-y))/2"
  let (_, r) := sessionEval {} "tanh(y)"; check "tanh is read as sinh over cosh" r "(exp(y) - exp(-y))/(exp(y) + exp(-y))"
  let (_, r) := sessionEval {} "cosh^2(y)"; check "cosh^2(y) is cosh(y)^2" r "(exp(y) + exp(-y))^2/4"
  let (_, r) := sessionEval {} "cosh(y, 2)"; check "cosh with two arguments is left alone" r "cosh(y, 2)"
  check "arctan prints" (roundtrip "arctan(x)") "arctan(x)"
  check "arcsin latex" (latexOf "arcsin(x)") "\\arcsin\\left(x\\right)"
  check "arccos^2 latex" (latexOf "arccos^2(x)") "{\\arccos\\left(x\\right)}^{2}"
  check "arg latex" (latexOf "arg(z)") "\\arg\\left(z\\right)"

/-- A scene's samples (`quiet`) are not evaluations: no `In[n]`, the session as it was. -/
def quietTests : TestM Unit := do
  let req (id method src : String) (quiet : Bool) :=
    s!"\{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":\"{method}\",\"params\":\{\"sessionId\":\"q\",\"cellId\":\"c{id}\",\"source\":\"{src}\"{if quiet then ",\"quiet\":true" else ""}}}"
  let (st, _) := handleS [] (req "1" "engine.evaluate" "x + 0" false)
  let (st, p) := handleS st (req "2" "engine.plot" "plot(exp(i*t), t, 0, 1)" true)
  checkTrue "quiet plot: samples, and no evaluation number" (contains p "\"points\"" && !contains p "\"label\"") p
  let (st, m) := handleS st (req "3" "engine.manipulate" "manipulate(plot(s*exp(i*t), s, 0, 1), t, 0, 1, 3)" true)
  checkTrue "quiet manipulate: frames, and no evaluation number" (contains m "\"frames\"" && !contains m "\"label\"") m
  let (_, e) := handleS st (req "4" "engine.evaluate" "%" false)
  checkTrue "after quiet samples the next evaluation is In[2], and % is still In[1]" (contains e "\"label\":2" && contains e "\"text\":\"x\"") e

/-- The antiderivative finder's rules, split at their conditions (`Antiderivative.lean`): the
verified half assumes nothing, the `.assuming` half says what, and what rests on the check is marked. -/
def integrateTests : TestM Unit := do
  let mut st : Store := []
  -- the finder's rules split at their conditions: the verified half assumes nothing, the `.assuming` half says what
  let intSteps (st : Store) (src : String) : List Step :=
    ((st.get "t").cells.lookup src >>= fun c => c.derivation.steps.toList.find? (·.rule == "cmd.integrate") >>= (·.sub)).map (·.steps.toList) |>.getD []
  for (src, rule, assumes) in [("integrate(1/x, x)", "int.power.assuming", "Assuming $x > 0$."),
      ("integrate(x^(-2), x)", "int.power.assuming", "Assuming $x \\neq 0$."),
      ("integrate(x^a, x)", "int.power.assuming", "Assuming $x > 0$, $a \\neq -1$."),
      ("integrate(ln(x), x)", "int.table.assuming", "Assuming $x > 0$."),
      ("integrate(tan(x), x)", "int.table.assuming", "Assuming $\\cos(x) > 0$."),
      ("integrate(sec(x)^2, x)", "int.table.assuming", "Assuming $\\cos(x) \\neq 0$."),
      ("integrate(arcsin(x), x)", "int.table.assuming", "Assuming $-1 < x < 1$."),
      ("integrate(b^x, x)", "int.exponential.assuming", "Assuming $b > 0$ and $b \\neq 1$."),
      ("integrate(sin(k*x), x)", "int.linear-substitution.assuming", "Assuming $k \\neq 0$."),
      ("integrate(sin(k*x)^2, x)", "int.trig-power.assuming", "Assuming $k \\neq 0$.")] do
    let (st', _) := sessionEval st src ",\"showWork\":true"
    st := st'
    let step := (intSteps st src).find? (·.rule == rule)
    checkTrue s!"integrate: {src} has a {rule} step" step.isSome ((intSteps st src).map (·.rule)).toString
    checkTrue s!"integrate: {src} says what it assumes" ((step.map (·.explanation.endsWith assumes)).getD false) ((step.map (·.explanation)).getD "")
  for (src, rules) in [("integrate(cos(3x+1), x)", "[int.table, int.linear-substitution, int.check, int.compare]"),
      ("integrate(2^x, x)", "[int.exponential, int.check, int.compare]"),
      ("integrate(pi^x, x)", "[int.exponential, int.check, int.compare]"),
      ("integrate(arctan(x), x)", "[int.table, int.check, int.compare]"),
      ("integrate(exp(x)^2, x)", "[int.exp-power, int.table, int.linear-substitution, int.check, int.compare]"),
      ("integrate(sin(x)^3, x)", "[int.trig-power, int.table, int.check, int.compare]"),
      ("integrate(x*exp(x^2), x)", "[int.substitution, int.check, int.compare]")] do
    let (st', _) := sessionEval st src ",\"showWork\":true"
    st := st'
    check s!"integrate: {src} steps" ((intSteps st src).map (·.rule)).toString rules
  -- the finder is total and marks what rests on the check (`anti_sound` claims nothing for it)
  let normOpt : Expr → Option Expr := fun e => (checkNorm e).toOption.map (·.1)
  let findOf (src : String) : Option Anti.Found := match parse src with
    | .ok (.fn "integrate" [f, .var x]) => Anti.anti normOpt x Anti.maxDepth 3 f
    | _ => none
  checkTrue "anti: a table entry is not checked, and says what it assumes"
    ((findOf "integrate(ln(x), x)").map (fun r => !r.checked && r.conds.length == 1) |>.getD false)
  checkTrue "anti: by-parts is marked checked" ((findOf "integrate(x*sin(x), x)").map (·.checked) |>.getD false)
  checkTrue "anti: u-substitution is marked checked" ((findOf "integrate(x*exp(x^2), x)").map (·.checked) |>.getD false)
  checkTrue "anti: verified steps assume nothing"
    ((findOf "integrate(x^2 + sin(x), x)").map (fun r => !r.checked && r.conds.isEmpty) |>.getD false)
  checkTrue "anti: depth 0 finds nothing" (Anti.anti normOpt "x" 0 3 (.var "x")).isNone

def main : IO UInt32 := do
  let ((), failures) ← (do tests; sessionTests; integrateTests; trigTests; quietTests; partStatTests; workTests; checkTests; logicRelTests; algebraTests; systemsTests; complexNTests; intervalTests; goldenTests).run #[]
  for f in failures do
    IO.println s!"FAIL {f.name}\n  expected: {f.expected}\n  actual:   {f.actual}"
  IO.println s!"{failures.size} failures"
  pure (if failures.isEmpty then 0 else 1)
