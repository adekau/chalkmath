/**
 * The function reference: a page for every command the engine (or the notebook, for files) knows,
 * laid out as Mathematica's documentation lays out a symbol — usage lines, details, examples in
 * sections, and related functions. The completion list, signature help, the sidebar's command list,
 * hover help and the Explanation panel all read their entries from here too.
 *
 * Examples are inputs, never outputs: the documentation evaluates each section in a session of its
 * own when the page is shown, so what a page shows is what this engine says, and cannot go stale.
 * Usage, details and notes are Markdown (`code`, *emphasis*, $math$).
 */

export type Area =
  | "Algebra" | "Elementary functions" | "Calculus" | "Complex numbers" | "Linear algebra"
  | "Lists, tables and files" | "Statistics" | "Fourier series" | "Order theory" | "λ-calculus" | "The notebook language";

/** The areas in the order the index lists them, each with a line saying what is there. */
export const AREAS: [Area, string][] = [
  ["Algebra", "Normal forms, expansion and factoring, substitution, numbers."],
  ["Elementary functions", "Roots, powers, exponentials, logarithms and the trigonometric functions."],
  ["Calculus", "Derivatives, integrals checked by differentiation, sums, plots."],
  ["Complex numbers", "The imaginary unit, conjugates, real and imaginary parts, Euler's formula."],
  ["Linear algebra", "Matrices and vectors: determinants, elimination, products, lengths."],
  ["Lists, tables and files", "Parts of matrices, tables and JSON; files as values."],
  ["Statistics", "Totals, means, medians, spread, of vectors and of a matrix's columns."],
  ["Fourier series", "Finite Fourier sums drawn as circles, and the discrete Fourier transform."],
  ["Order theory", "Finite partial orders, lattices, monotone maps and their fixed points."],
  ["λ-calculus", "The untyped λ-calculus, reduced one β-step at a time, and the Church encodings."],
  ["The notebook language", "Names and functions, earlier answers, questions."],
];

/** A section of examples: inputs, evaluated in order in one session, with notes between them. */
export interface ExampleSection { title: string; items: (string | { note: string })[] }

export interface FnDoc {
  /** What is typed: the page's name, and the key completion and signature help look it up by. */
  name: string;
  /** The page's heading when it is not the name (a notation: `%`, `λ`). */
  title?: string;
  area: Area;
  /** Mathematica's usage lines: a form, and what it gives. */
  usage: [form: string, what: string][];
  /** Details: one Markdown bullet each. */
  details?: string[];
  examples: ExampleSection[];
  /** Related pages, by name. */
  see?: string[];
  /** An outside reference (MathWorld). */
  ref?: string;
  /** A notation or a library rather than a function to call: not offered as a completion. */
  notation?: boolean;
}

const basic = (...items: ExampleSection["items"]): ExampleSection => ({ title: "Basic examples", items });
const section = (title: string, ...items: ExampleSection["items"]): ExampleSection => ({ title, items });
const note = (text: string) => ({ note: text });

export const FUNCTIONS: FnDoc[] = [
  // --- Algebra ---------------------------------------------------------------------------------
  {
    name: "simplify", area: "Algebra",
    usage: [["simplify(e)", "gives the normal form of `e`."]],
    details: [
      "Every math cell is simplified anyway; `simplify` names the intent.",
      "The normal form collects like terms, combines powers of the same base, cancels what cancels and keeps arithmetic exact: fractions stay fractions and roots stay roots.",
      "Each rewrite is a step, with its rule and the rule's proof status.",
    ],
    examples: [
      basic("simplify(x + x)", "simplify(x^2 * x^3 / x)"),
      section("Scope", note("Exact arithmetic:"), "1/2 + 1/3", "sqrt(8) + sqrt(18)", note("Powers of a power, and of a product:"), "(x^2)^3", "(2x)^2"),
    ],
    see: ["expand", "factor", "N"],
  },
  {
    name: "expand", area: "Algebra",
    usage: [["expand(e)", "multiplies out the products and powers of sums in `e`, and collects the result."]],
    details: ["Expansion is repeated distribution; each distribution is a step."],
    examples: [
      basic("expand((x+1)^3)", "expand((a+b)^4)"),
      section("Scope", "expand((x+1)*(x-1))", "expand(2*(x+y))", note("With Euler's formula, to distribute and collect:"), "expand(exptotrig(exp(-i*t) - exp(i*t)))"),
    ],
    see: ["factor", "simplify", "exptotrig"],
    ref: "https://mathworld.wolfram.com/Expand.html",
  },
  {
    name: "factor", area: "Algebra",
    usage: [["factor(e)", "puts `e` over a common denominator and pulls the numerator's common factor out."]],
    details: [
      "The shape a hand derivation ends in: expand and collect, put the sum over a common denominator (Mathematica's `Together`), then take out the common factor.",
      "It is one presentation of the normal form, not a factorization into irreducibles: $x^2 - 1$ stays as it is.",
    ],
    examples: [
      basic("factor(x^2 + 2*x)", "factor(a/x + b/y)"),
      section("Scope", "factor(-2*x - 4)", "factor(x/2 + x/3)"),
    ],
    see: ["expand", "simplify"],
  },
  {
    name: "subst", area: "Algebra",
    usage: [["subst(e, x, v)", "replaces every free occurrence of `x` in `e` with `v`."]],
    examples: [
      basic("subst(x^2 + 1, x, 3)"),
      section("Scope", note("A value bound with `let`:"), "let f = x^2 + 3x", "subst(f, x, 2)", note("Another expression:"), "subst(f, x, y + 1)"),
    ],
    see: ["let"],
  },
  {
    name: "N", area: "Algebra",
    usage: [["N(e)", "gives a numerical approximation of `e`, to fifteen significant digits."]],
    details: [
      "IEEE-754 double precision.",
      "Over ℂ when the term mentions `i`, or when its real value is not finite: `N(sqrt(-1))` is `i`.",
      "A term with a free variable has no numerical value.",
    ],
    examples: [
      basic("N(pi)", "N(sqrt(2))"),
      section("Scope", "N(1/3)", "N(exp(1))", "N(sin(pi/6))"),
    ],
    see: ["simplify"],
  },

  // --- Elementary functions --------------------------------------------------------------------
  {
    name: "sqrt", area: "Elementary functions",
    usage: [["sqrt(x)", "gives the square root of `x`."]],
    details: ["`sqrt(x)` is $x^{1/2}$, so the power rules handle it: it differentiates and simplifies like any power.", "Roots of numbers stay exact and simplest: $\\sqrt{8} = 2\\sqrt{2}$."],
    examples: [
      basic("sqrt(16)", "sqrt(8) + sqrt(18)"),
      section("Scope", "diff(sqrt(x), x)", "sqrt(12)*sqrt(3)", "integrate(sqrt(x), x, 0, 4)"),
    ],
    see: ["exp", "abs"],
    ref: "https://mathworld.wolfram.com/SquareRoot.html",
  },
  {
    name: "abs", area: "Elementary functions",
    usage: [["abs(x)", "gives the absolute value of `x`; of a complex number, its modulus."]],
    examples: [basic("abs(-3)", "abs(3+4i)")],
    see: ["sign", "norm", "conj"],
    ref: "https://mathworld.wolfram.com/AbsoluteValue.html",
  },
  {
    name: "sign", area: "Elementary functions",
    usage: [["sign(x)", "gives −1, 0 or 1 according to the sign of `x`."]],
    details: ["It folds on numbers and stays symbolic otherwise, so `sign(sin(t))` is the square wave."],
    examples: [
      basic("sign(-3)", "sign(-3) + sign(0) + sign(5/2)"),
      section("Applications", note("A square wave:"), "plot(sign(sin(t)), t, -pi, pi)"),
    ],
    see: ["abs"],
  },
  {
    name: "exp", area: "Elementary functions",
    usage: [["exp(x)", "gives the exponential of `x`: e to the power `x`."]],
    details: ["`exp(x)`, `ℯ^x` and `e^x` written with `\\e` are the same function.", "Its own derivative and its own antiderivative."],
    examples: [
      basic("diff(exp(2x), x)", "ln(exp(x))"),
      section("Scope", "integrate(exp(2*x), x)", "ℯ^(pi*i)"),
    ],
    see: ["ln", "exptotrig"],
    ref: "https://mathworld.wolfram.com/ExponentialFunction.html",
  },
  {
    name: "ln", area: "Elementary functions",
    usage: [["ln(x)", "gives the natural logarithm of `x`."]],
    details: ["The derivative is $1/x$; the logarithm of a power brings the exponent down."],
    examples: [
      basic("ln(exp(x))", "diff(ln(x), x)"),
      section("Scope", "ln(x^2)", "integrate(ln(x), x)", "integrate(1/x, x)"),
    ],
    see: ["exp"],
    ref: "https://mathworld.wolfram.com/NaturalLogarithm.html",
  },
  {
    name: "sin", area: "Elementary functions",
    usage: [["sin(x)", "gives the sine of `x`, in radians."]],
    details: ["Exact at rational multiples of π where the value is a root.", "The derivative is $\\cos x$."],
    examples: [
      basic("sin(pi)", "sin(3pi/4)"),
      section("Scope", "diff(sin(x^2), x)", "integrate(x*sin(x), x)", "plot(sin(x)/x, x, -10, 10)"),
    ],
    see: ["cos", "tan", "exptotrig"],
    ref: "https://mathworld.wolfram.com/Sine.html",
  },
  {
    name: "cos", area: "Elementary functions",
    usage: [["cos(x)", "gives the cosine of `x`, in radians."]],
    details: ["Exact at rational multiples of π where the value is a root.", "The derivative is $-\\sin x$."],
    examples: [
      basic("cos(pi/3)", "cos(7pi/6)"),
      section("Scope", "diff(cos(x), x)", "integrate(cos(3*x + 1), x)"),
    ],
    see: ["sin", "tan"],
    ref: "https://mathworld.wolfram.com/Cosine.html",
  },
  {
    name: "tan", area: "Elementary functions",
    usage: [["tan(x)", "gives the tangent of `x`, sin x / cos x."]],
    details: ["The derivative is $\\sec^2 x$."],
    examples: [
      basic("tan(pi/4) + tan(pi/3)", "diff(tan(x), x)"),
      section("Scope", "integrate(tan(x), x)"),
    ],
    see: ["sin", "cos"],
    ref: "https://mathworld.wolfram.com/Tangent.html",
  },

  // --- Calculus --------------------------------------------------------------------------------
  {
    name: "diff", area: "Calculus",
    usage: [["diff(f, x)", "gives the derivative of `f` with respect to `x`."], ["diff(f, x, n)", "gives the `n`-th derivative."]],
    details: [
      "Implemented as rewrite rules that push $d/dx$ inward (sum, product, quotient, chain and power rules), so the derivation reads like a textbook's.",
      "Other variables are constants: `diff(x*y, x)` is `y`.",
      "A vector or matrix is differentiated entry by entry.",
    ],
    examples: [
      basic("diff(x^2 * sin(x), x)", "diff(x^3, x, 2)"),
      section("Scope", "diff(sin(x^2), x)", "diff(1/(x+1), x)", "diff(x^x, x)", "diff(2^x, x)", "diff(x*y, x)", "diff([x, x^2], x)"),
      section("Properties and relations", note("Differentiation undoes integration:"), "diff(integrate(x^3, x), x)"),
    ],
    see: ["integrate", "sum", "plot"],
    ref: "https://mathworld.wolfram.com/Derivative.html",
  },
  {
    name: "integrate", area: "Calculus",
    usage: [["integrate(f, x)", "gives an antiderivative of `f` in `x`, without the constant."], ["integrate(f, x, a, b)", "gives the definite integral of `f` from `a` to `b`."]],
    details: [
      "A small rule set (substitution, parts, a table of forms) guesses an antiderivative, and the guess is accepted only if differentiating it gives `f` back: the check is the proof. Its steps are marked *checked*.",
      "With bounds, the checked antiderivative at `b` minus at `a`: the fundamental theorem of calculus (`integrate_definite`).",
      "When no guess checks out, the integral is left as it is.",
    ],
    examples: [
      basic("integrate(x^2 + sin(x), x)", "integrate(cos(t)*sin(t), t, 0, 2pi)"),
      section("Scope", "integrate(exp(2*x), x)", "integrate(x/(x^2+1), x)", "integrate(x*exp(x^2), x)", "integrate(ln(x), x)", "integrate(x^2*exp(x), x)", "integrate(exp(-3i*t), t, 0, pi)"),
      section("Properties and relations", "diff(integrate(x^3, x), x)"),
    ],
    see: ["diff", "sum"],
    ref: "https://mathworld.wolfram.com/IndefiniteIntegral.html",
  },
  {
    name: "sum", area: "Calculus",
    usage: [["sum(f, k, a, b)", "gives the finite sum of `f` for `k` from `a` to `b`."]],
    details: ["The bounds are integers; the terms are expanded and collected.", "A definition, read over ℝ by `sum_soundR`."],
    examples: [
      basic("sum(k^2, k, 1, 10)", "sum(1/2^k, k, 0, 5)"),
      section("Scope", note("Symbolic terms, such as a Fourier sum:"), "sum(c*exp(i*k*t), k, -3, 3)"),
    ],
    see: ["integrate", "epicycles"],
  },
  {
    name: "plot", area: "Calculus",
    usage: [["plot(f, x, from, to)", "draws `f` as `x` runs from `from` to `to`."], ["plot([f, g, …], x, from, to)", "draws several functions, with a legend."], ["plot(f, x, from, to, n)", "samples `n` points."]],
    details: [
      "The engine simplifies each function under the session first (a derivative plots as the derivative) and samples it where it has a finite value; the notebook draws the curves.",
      "A complex-valued function of a real variable is drawn as a curve in the plane.",
    ],
    examples: [
      basic("plot(sin(x)/x, x, -10, 10)", "plot([sin(x), cos(x)], x, 0, 2pi)"),
      section("Scope", note("A function and its derivative:"), "plot([x^2, diff(x^2, x)], x, -3, 3)", note("A complex-valued curve:"), "plot(exp(i*t), t, 0, 2pi)"),
    ],
    see: ["manipulate", "epicycles", "diff"],
  },
  {
    name: "manipulate", area: "Calculus",
    usage: [
      ["manipulate(e, p, from, to)", "shows `e` with a slider for `p`, from `from` to `to`, and ▶ Play to animate it."],
      ["manipulate(e, p, from, to, n)", "uses `n` values of `p` (40 unless given, at most 200)."],
    ],
    details: [
      "Mathematica's `Manipulate`. `e` is any expression: a plot animates, and a derivative, a sum or a matrix shows its value at each `p`.",
      "The engine evaluates `e` once for each value of `p`, evenly spaced from `from` to `to`, in one go; moving the slider and playing never wait for it.",
      "`from` may be larger than `to`: the slider starts at `from`, so `manipulate(…, h, 1, 0.01)` plays `h` down toward 0.",
      "A plot keeps one window for every frame, so the axes hold still while the curves move. While it plays, the page draws between neighbouring frames; where the slider stops, it shows the engine's own frame.",
      "`p` is bound only inside the frames, and must not be the plot's own variable. The cell's value and work are its first frame's.",
    ],
    examples: [
      basic("manipulate(plot(sin(a*x), x, 0, 2pi), a, 1, 4)", "manipulate(diff(x^n, x), n, 1, 5, 5)"),
      section("Scope",
        note("A secant turning into the tangent of x² at 1 as h shrinks toward 0:"),
        "manipulate(plot([x^2, 1 + ((1 + h)^2 - 1)/h*(x - 1)], x, -0.5, 3), h, 2, 0.05)"),
    ],
    see: ["plot", "subst"],
  },

  // --- Complex numbers -------------------------------------------------------------------------
  {
    name: "i", area: "Complex numbers", notation: true,
    usage: [["i", "is the imaginary unit, with i² = −1."]],
    details: [
      "Gaussian numbers $a + b\\,i$ add, multiply, divide and take powers exactly.",
      "`sin`, `cos` and `tan` are exact at rational multiples of π, and `exp(iθ)` becomes $\\cos θ + i \\sin θ$ where both are exact, so $e^{\\pi i}$ is $-1$.",
      "A cell that mentions `i` is read over ℂ, and shows each rule's proof status there.",
    ],
    examples: [
      basic("i^2", "(1+i)*(2-i)", "ℯ^(pi*i)"),
      section("Scope", "(2+i)/(1+i)", "(1+i)^2", "exp(i*pi/2)", "abs(3+4i)"),
    ],
    see: ["conj", "re", "im", "abs", "exptotrig"],
    ref: "https://mathworld.wolfram.com/i.html",
  },
  {
    name: "conj", area: "Complex numbers",
    usage: [["conj(z)", "gives the complex conjugate of `z`."]],
    examples: [
      basic("conj(2+3i)"),
      section("Applications", note("The Hermitian inner product of complex vectors:"), "dot([i, 1], conj([i, 1]))"),
    ],
    see: ["re", "im", "abs", "dot"],
  },
  {
    name: "re", area: "Complex numbers",
    usage: [["re(z)", "gives the real part of `z`."]],
    examples: [basic("re(2+3i) + im(2+3i)")],
    see: ["im", "conj"],
  },
  {
    name: "im", area: "Complex numbers",
    usage: [["im(z)", "gives the imaginary part of `z`."]],
    examples: [basic("re(2+3i) + im(2+3i)")],
    see: ["re", "conj"],
  },
  {
    name: "exptotrig", area: "Complex numbers",
    usage: [["exptotrig(e)", "applies Euler's formula, exp(iθ) = cos θ + i sin θ, to every exponential in `e` with a pure-imaginary argument."]],
    details: [
      "Mathematica's `ExpToTrig`. It is a command rather than a simplification rule because the general formula makes the term bigger.",
      "Wrap it in `expand` to distribute and collect. Proved sound over ℂ.",
    ],
    examples: [
      basic("exptotrig(exp(i*t))", "exptotrig(exp(-i*t))"),
      section("Scope", "expand(exptotrig(exp(-i*t) - exp(i*t)))"),
    ],
    see: ["exp", "i", "expand"],
  },

  // --- Linear algebra --------------------------------------------------------------------------
  {
    name: "det", area: "Linear algebra",
    usage: [["det(M)", "gives the determinant of the square matrix `M`."]],
    details: ["Laplace expansion along the first row. Symbolic entries work."],
    examples: [
      basic("det([1,2;3,4])", "det([a,b;c,d])"),
      section("Scope", "det([1,2,3;4,5,6;7,8,10])", "det([2,0,1;1,3,2;1,1,1])"),
    ],
    see: ["rref", "transpose"],
    ref: "https://mathworld.wolfram.com/Determinant.html",
  },
  {
    name: "rref", area: "Linear algebra",
    usage: [["rref(M)", "gives the reduced row echelon form of `M`."]],
    details: ["Gauss–Jordan elimination. Each row operation is a step of its own, nested under the command."],
    examples: [
      basic("rref([1,2,3;4,5,6;7,8,10])"),
      section("Scope", note("A singular matrix:"), "rref([1,2;2,4])", note("Fractions stay exact:"), "rref([1/2,1,3;1,3,5])", "rref([1,2,3,4;2,4,6,8;1,1,1,1])"),
    ],
    see: ["det", "transpose"],
    ref: "https://mathworld.wolfram.com/ReducedRowEchelonForm.html",
  },
  {
    name: "transpose", area: "Linear algebra",
    usage: [["transpose(M)", "swaps the rows and columns of `M`."]],
    examples: [basic("transpose([1,2,3;4,5,6])")],
    see: ["det", "rref"],
  },
  {
    name: "dot", area: "Linear algebra",
    usage: [["dot(u, v)", "gives the dot product Σ uᵢvᵢ of two vectors."]],
    details: [
      "A vector is a one-row or one-column matrix.",
      "Bilinear, like Mathematica's `Dot`: the Hermitian inner product of complex vectors is `dot(u, conj(v))`.",
      "`*` is the matrix product: `[1,2,3] * [1;2;3]` is a 1×1 matrix.",
    ],
    examples: [
      basic("dot([1,2,3],[4,5,6])"),
      section("Scope", "dot([i,1], conj([i,1]))", "[1,2;3,4] * [5,6;7,8]", "[1,2,3] * [1;2;3]"),
    ],
    see: ["norm", "conj"],
    ref: "https://mathworld.wolfram.com/DotProduct.html",
  },
  {
    name: "norm", area: "Linear algebra",
    usage: [["norm(v)", "gives the Euclidean length √(Σ vᵢ²) of the vector `v`."]],
    examples: [basic("norm([3,4])", "norm([a,b])")],
    see: ["dot", "abs"],
    ref: "https://mathworld.wolfram.com/VectorNorm.html",
  },

  {
    name: "entrywise", title: "./ and .* (entrywise)", area: "Linear algebra", notation: true,
    usage: [
      ["A ./ B", "divides entry by entry: entry (i, j) is aᵢⱼ/bᵢⱼ."],
      ["A .* B", "multiplies entry by entry (the Hadamard product): entry (i, j) is aᵢⱼ·bᵢⱼ."],
    ],
    details: [
      "MATLAB's entrywise operators. The two matrices must have the same shape; a number on either side meets every entry.",
      "Plain `/` and `*` keep their matrix meaning: `A / B` is `A·B⁻¹` and `A * B` is the matrix product, so `[1, 2] / [3, 10]` is an error while `[1, 2] ./ [3, 10]` is `[1/3, 1/5]`.",
      "They bind like a product and group to the left: `a ./ b ./ c` is `(a ./ b) ./ c`.",
      "Each entry's arithmetic shows as its own steps under one `la.entrywise` step.",
    ],
    examples: [
      basic("[1, 2] ./ [3, 10]", "[1, 2; 3, 4] .* [5, 6; 7, 8]"),
      section("Scope", "[2, 4] ./ 2", "1 ./ [2, 4]", "[x, y] .* [2, 3]"),
    ],
    see: ["dot", "transpose"],
  },

  // --- Lists, tables and files -----------------------------------------------------------------
  {
    name: "part", title: "[[ ]] (part)", area: "Lists, tables and files", notation: true,
    usage: [
      ["m[[i]]", "gives the `i`-th row of a matrix, or the `i`-th entry of a vector."],
      ["m[[i, j]]", "gives the entry in row `i`, column `j`."],
      ["m[[All, j]]", "gives column `j`."],
      ["m[[a;;b]]", "gives rows `a` through `b`; `a;;b;;s` steps by `s`."],
      ["m[[{i, j}]]", "gives rows `i` and `j`, in that order."],
      ["t[[All, \"name\"]]", "gives a table's column by name."],
    ],
    details: [
      "Mathematica's `Part`. Positions count from 1, and a negative one from the end: −1 is the last.",
      "`All` takes every position. `a;;b` includes both ends; `;;b` starts at the beginning and `a;;` runs to the end. A negative step goes backwards.",
      "A single index drops that dimension (an entry, or a row or column vector); a span or a list keeps it.",
      "A table also takes column names in quotes; JSON takes keys and positions one level at a time, with `All` applying the rest to every element: `j[[\"planets\", All, \"mass\"]]`.",
      "A selection of numbers goes to the engine (`la.part`, every position checked in range by `partSpec_lt`); one with text in it stays a table, JSON or text.",
    ],
    examples: [
      basic("[1, 2, 3; 4, 5, 6; 7, 8, 9][[2]]", "[1, 2, 3; 4, 5, 6; 7, 8, 9][[All, -1]]"),
      section("Scope", "[1, 2, 3; 4, 5, 6; 7, 8, 9][[1;;3;;2, {3, 1}]]", "let m = [1, 2, 3; 4, 5, 6; 7, 8, 9]", "m[[2, 3]]", "m[[-1;;1;;-1]]"),
      section("Tables", "let planets = import(\"examples/data/planets.csv\")", "planets[[All, \"period\"]]", "planets[[2;;4]]"),
    ],
    see: ["import", "matrix", "dimensions"],
  },
  {
    name: "import", area: "Lists, tables and files",
    usage: [["import(\"url\")", "gives the file at `url` as a value."], ["⟦name⟧", "is the file `name` attached to the notebook."], ["let x = import(…)", "binds `x` to the file."]],
    details: [
      "A file is kept as it came — its name, media type and contents — and shown by what it is: an image as the image, a CSV or TSV as a table, JSON and other text as text, anything else as a card with its type and size.",
      "Attach a file with File › Attach file…, or paste one into a cell. `import(\"url\")` fetches one from the web; the server must allow other sites to read it.",
      "Nothing is converted on the way in: parts and functions turn a file into numbers — `t[[All, \"mass\"]]` for a table, `j[[\"key\"]]` for JSON, `samplePoints` for an SVG, `matrix` and `dimensions` for a table. A file anywhere else in a cell is an error that says which.",
      "Files are the notebook's; the engine only ever sees numbers.",
    ],
    examples: [
      basic("let planets = import(\"examples/data/planets.csv\")", "dimensions(planets)"),
      section("Scope", note("An SVG from the web:"), "import(\"https://raw.githubusercontent.com/adekau/fourier/master/src/assets/llama.svg\")"),
    ],
    see: ["part", "matrix", "dimensions", "samplePoints"],
  },
  {
    name: "matrix", area: "Lists, tables and files",
    usage: [["matrix(t)", "gives the numbers of a table (a CSV or TSV file, or JSON that is a list of records) as a matrix."]],
    details: [
      "Every data row, every column: an error names the field if one is not a number.",
      "The first line of a CSV is a header when it has no numbers in it.",
      "To take some columns, take parts first: `matrix(t[[All, 2;;]])`.",
    ],
    examples: [basic("let planets = import(\"examples/data/planets.csv\")", "matrix(planets[[All, 2;;]])")],
    see: ["dimensions", "part", "import"],
  },
  {
    name: "dimensions", area: "Lists, tables and files",
    usage: [["dimensions(t)", "gives `[rows, columns]` of a table, or of a part of one that is numbers."]],
    details: ["Mathematica's `Dimensions`, for a CSV or TSV file or JSON that is a list of records."],
    examples: [basic("let planets = import(\"examples/data/planets.csv\")", "dimensions(planets)", "dimensions(planets[[All, 2;;]])")],
    see: ["matrix", "part"],
  },
  {
    name: "samplePoints", area: "Lists, tables and files",
    usage: [["samplePoints(svg)", "gives 400 points sampled along the paths of an SVG image, as an n×2 matrix."], ["samplePoints(svg, n)", "gives `n` points."]],
    details: [
      "Points are spaced at equal arc lengths, centred, and scaled so the larger extent is [−1, 1]: ready for `epicycles` and `dft`.",
      "Only SVG paths are traced; another kind of image is an error.",
    ],
    examples: [
      basic("let llama = import(\"https://raw.githubusercontent.com/adekau/fourier/master/src/assets/llama.svg\")", "let pts = samplePoints(llama)", "epicycles(pts, 60)"),
    ],
    see: ["epicycles", "dft", "import"],
  },

  // --- Statistics ------------------------------------------------------------------------------
  {
    name: "total", area: "Statistics",
    usage: [["total(v)", "gives the sum of the entries of the vector `v`."], ["total(m)", "gives the sum of each column of the matrix `m`."]],
    details: ["Mathematica's `Total`: the sum of a list. `sum(f, k, a, b)` is the sum of a term over an index.", "A definition, so symbolic entries work; over ℝ the value is the list's sum (`total_soundR`)."],
    examples: [basic("total([1; 2; 3])", "total([1, 2; 3, 4])"), section("Scope", "total([a, b, c])")],
    see: ["mean", "sum"],
  },
  {
    name: "mean", area: "Statistics",
    usage: [["mean(v)", "gives the mean of the entries of `v`."], ["mean(m)", "gives the mean of each column of the matrix `m`, as a row."]],
    details: ["A definition, so symbolic entries work: `mean([a; b])` is $(a + b)/2$.", "Over ℝ the value is the sum over the count (`mean_soundR`)."],
    examples: [
      basic("mean([2, 4, 4, 4, 5, 5, 7, 9])"),
      section("Scope", "mean([a; b])", "mean([1, 2; 3, 4])"),
      section("Applications", "let planets = import(\"examples/data/planets.csv\")", "mean(planets[[All, \"mass\"]])"),
    ],
    see: ["median", "variance", "stdev", "total"],
    ref: "https://mathworld.wolfram.com/ArithmeticMean.html",
  },
  {
    name: "median", area: "Statistics",
    usage: [["median(v)", "gives the middle entry of `v`, or the mean of the two middle ones."], ["median(m)", "gives the median of each column."]],
    details: ["It compares exact rationals, so the entries must be numbers.", "The result is the middle of a sorted permutation of the entries (`medianQ_spec`)."],
    examples: [basic("median([5, 1, 3])", "median([4, 1, 3, 2])")],
    see: ["mean", "min", "max"],
  },
  {
    name: "variance", area: "Statistics",
    usage: [["variance(v)", "gives the sample variance of `v`, dividing by n − 1."], ["variance(m)", "gives the variance of each column."]],
    details: [
      "The sample variance, as Mathematica's `Variance` and Python's `statistics.variance` compute it.",
      "The engine writes it in its one-pass form, $(\\sum x_i^2 - (\\sum x_i)^2/n)/(n-1)$, proved equal to $\\sum (x_i - \\bar x)^2/(n-1)$ (`variance_soundR`). Symbolic entries work.",
      "It needs two values or more.",
    ],
    examples: [basic("variance([2, 4, 4, 4, 5, 5, 7, 9])"), section("Scope", "variance([a, b])")],
    see: ["stdev", "mean"],
    ref: "https://mathworld.wolfram.com/SampleVariance.html",
  },
  {
    name: "stdev", area: "Statistics",
    usage: [["stdev(v)", "gives the sample standard deviation of `v`, the square root of its variance."], ["stdev(m)", "gives the standard deviation of each column."]],
    details: ["Proved to be the square root of `variance` (`stdev_soundR`)."],
    examples: [basic("stdev([1, 3])", "stdev([2, 4, 4, 4, 5, 5, 7, 9])")],
    see: ["variance", "mean"],
    ref: "https://mathworld.wolfram.com/StandardDeviation.html",
  },
  {
    name: "min", area: "Statistics",
    usage: [["min(v)", "gives the least entry of `v`."], ["min(m)", "gives the least entry of each column."]],
    details: ["It compares exact rationals, so the entries must be numbers.", "The result is an entry, and no entry is smaller (`minQ_spec`)."],
    examples: [basic("min([3, -1, 2.5])")],
    see: ["max", "median"],
  },
  {
    name: "max", area: "Statistics",
    usage: [["max(v)", "gives the greatest entry of `v`."], ["max(m)", "gives the greatest entry of each column."]],
    details: ["It compares exact rationals, so the entries must be numbers.", "The result is an entry, and no entry is larger (`maxQ_spec`)."],
    examples: [basic("max([3, -1, 2.5])")],
    see: ["min", "median"],
  },

  // --- Fourier series --------------------------------------------------------------------------
  {
    name: "epicycles", area: "Fourier series",
    usage: [
      ["epicycles(f, t)", "draws the finite Fourier sum `f` = Σ cₖ·exp(i k t) with one circle per term."],
      ["epicycles(f, t, n)", "samples `n` points of the curve."],
      ["epicycles(points)", "computes the coefficients of a list of points numerically and draws them."],
      ["epicycles(points, modes)", "keeps the `modes` largest coefficients."],
    ],
    details: [
      "Each term is a circle of radius $|c_k|$ and phase $\\arg c_k$, turning $k$ times a period, drawn tip to tail; the tip traces the curve.",
      "Points are `[x, y; …]` rows or complex numbers; their coefficients are the discrete Fourier transform (`dft`).",
      "The drawing is numeric presentation; the sum's algebra is the engine's.",
    ],
    examples: [
      basic("epicycles(exp(i*t) + 1/2*exp(-3i*t), t)"),
      section("Applications", note("A square wave from its first Fourier terms:"), "epicycles(sum(2i/(k*pi)*(exp(-i*k*t) - exp(i*k*t)), k, 1, 3), t)"),
    ],
    see: ["dft", "sum", "samplePoints", "plot"],
  },
  {
    name: "dft", area: "Fourier series",
    usage: [["dft(points)", "gives the discrete Fourier transform of a list of points: the coefficients `epicycles` draws."], ["dft(points, modes)", "keeps the `modes` largest."]],
    examples: [basic("dft([1, i, -1, -i])")],
    see: ["epicycles", "samplePoints"],
    ref: "https://mathworld.wolfram.com/DiscreteFourierTransform.html",
  },

  // --- Order theory ----------------------------------------------------------------------------
  {
    name: "poset", area: "Order theory",
    usage: [["poset({a, b, c}; a<b, a<c)", "gives the partial order on `{a, b, c}` generated by the relations."], ["poset({a, b, c})", "gives the antichain: no two elements compare."]],
    details: [
      "The order is the reflexive-transitive closure of the relations given, checked to be antisymmetric: `a<b, b<a` is an error.",
      "Bind it with `let` and ask about it: `hasse`, `le`, `join`, `meet`, `upper`, `lower`, `top`, `bottom`, `maximal`, `minimal`, `lattice`.",
      "The output is the Hasse diagram.",
    ],
    examples: [
      basic("let P = poset({a,b,c,d}; a<b, a<c, b<d, c<d)", "join(P, b, c)", "lattice(P)"),
      section("Possible issues", note("A vee is not a lattice: two elements with no join."), "let N = poset({a,b,c}; a<b, a<c)", "lattice(N)"),
    ],
    see: ["divisors", "subsets", "chain", "hasse", "lattice"],
    ref: "https://mathworld.wolfram.com/PartiallyOrderedSet.html",
  },
  {
    name: "divisors", area: "Order theory",
    usage: [["divisors(n)", "gives the divisors of `n` ordered by divisibility: a ≤ b when a divides b."]],
    examples: [basic("let D = divisors(12)", "join(D, 4, 6)", "meet(D, 4, 6)")],
    see: ["poset", "subsets", "chain"],
  },
  {
    name: "subsets", area: "Order theory",
    usage: [["subsets({a, b, …})", "gives all subsets of a finite set ordered by inclusion."]],
    details: ["Its elements are written as sets, in any order: `{x,y}` and `{y,x}` are the same element."],
    examples: [basic("let S = subsets({x,y})", "join(S, {x}, {y})")],
    see: ["poset", "divisors"],
  },
  {
    name: "chain", area: "Order theory",
    usage: [["chain(n)", "gives the chain 0 < 1 < … < n − 1."]],
    examples: [basic("let C = chain(4)", "le(C, 1, 3)", "lattice(C)")],
    see: ["poset", "divisors"],
  },
  {
    name: "hasse", area: "Order theory",
    usage: [["hasse(P)", "gives the Hasse diagram of `P`: its covers, the pairs x < y with nothing strictly between."]],
    examples: [basic("let D = divisors(12)", "hasse(D)")],
    see: ["poset", "le"],
    ref: "https://mathworld.wolfram.com/HasseDiagram.html",
  },
  {
    name: "le", area: "Order theory",
    usage: [["le(P, a, b)", "gives `true` when a ≤ b in `P`, and `false` otherwise."]],
    details: ["When it holds, the steps are a chain of covers from `a` up to `b`."],
    examples: [basic("let D = divisors(12)", "le(D, 2, 12)", "le(D, 4, 6)")],
    see: ["hasse", "join", "meet"],
  },
  {
    name: "join", area: "Order theory",
    usage: [["join(P, a, b)", "gives the least upper bound a ∨ b of `a` and `b` in `P`."], ["sup(P, a, b)", "is the same."]],
    details: ["The steps find the upper bounds, then the least of them (`order.sup_spec`).", "Two elements with no least upper bound are an error that names the upper bounds."],
    examples: [basic("let D = divisors(12)", "join(D, 4, 6)", "sup(D, 2, 3)")],
    see: ["meet", "upper", "lattice"],
    ref: "https://mathworld.wolfram.com/Join.html",
  },
  {
    name: "meet", area: "Order theory",
    usage: [["meet(P, a, b)", "gives the greatest lower bound a ∧ b of `a` and `b` in `P`."], ["inf(P, a, b)", "is the same."]],
    examples: [basic("let D = divisors(12)", "meet(D, 4, 6)", "inf(D, 4, 12)")],
    see: ["join", "lower", "lattice"],
    ref: "https://mathworld.wolfram.com/Meet.html",
  },
  {
    name: "upper", area: "Order theory",
    usage: [["upper(P, {a, b, …})", "gives the elements of `P` above every one of `a`, `b`, …"]],
    examples: [basic("let D = divisors(12)", "upper(D, {2, 3})")],
    see: ["lower", "join"],
  },
  {
    name: "lower", area: "Order theory",
    usage: [["lower(P, {a, b, …})", "gives the elements of `P` below every one of `a`, `b`, …"]],
    examples: [basic("let D = divisors(12)", "lower(D, {4, 6})")],
    see: ["upper", "meet"],
  },
  {
    name: "top", area: "Order theory",
    usage: [["top(P)", "gives the greatest element ⊤ of `P`, if it has one."]],
    examples: [basic("let D = divisors(12)", "top(D)")],
    see: ["bottom", "maximal"],
  },
  {
    name: "bottom", area: "Order theory",
    usage: [["bottom(P)", "gives the least element ⊥ of `P`, if it has one."]],
    examples: [basic("let D = divisors(12)", "bottom(D)")],
    see: ["top", "minimal"],
  },
  {
    name: "maximal", area: "Order theory",
    usage: [["maximal(P)", "gives the elements of `P` with nothing above them."]],
    examples: [basic("let N = poset({a,b,c}; a<b, a<c)", "maximal(N)")],
    see: ["minimal", "top"],
  },
  {
    name: "minimal", area: "Order theory",
    usage: [["minimal(P)", "gives the elements of `P` with nothing below them."]],
    examples: [basic("let N = poset({a,b,c}; a<b, a<c)", "minimal(N)")],
    see: ["maximal", "bottom"],
  },
  {
    name: "lattice", area: "Order theory",
    usage: [["lattice(P)", "gives `true` when every pair of elements of `P` has a join and a meet."]],
    details: ["When it does not, the step names a pair without one."],
    examples: [basic("let D = divisors(12)", "lattice(D)", "let N = poset({a,b,c}; a<b, a<c)", "lattice(N)")],
    see: ["join", "meet", "poset"],
    ref: "https://mathworld.wolfram.com/Lattice.html",
  },
  {
    name: "map", area: "Order theory",
    usage: [["map(P; a->b, c->d, …)", "gives the map on `P` sending `a` to `b`, `c` to `d`, …, and every other element to itself."]],
    details: ["Bind it with `let` to use it with `monotone`, `lfp`, `gfp` and `fixpoints`."],
    examples: [basic("let D = divisors(12)", "let f = map(D; 1->2, 3->6)", "monotone(D, f)", "lfp(D, f)")],
    see: ["monotone", "lfp", "fixpoints"],
  },
  {
    name: "monotone", area: "Order theory",
    usage: [["monotone(P, f)", "gives `true` when x ≤ y implies f(x) ≤ f(y) for every pair in `P`."]],
    details: ["When it does not hold, the step names a pair where it fails."],
    examples: [basic("let D = divisors(12)", "let f = map(D; 1->2, 3->6)", "monotone(D, f)")],
    see: ["map", "lfp"],
  },
  {
    name: "lfp", area: "Order theory",
    usage: [["lfp(P, f)", "gives the least fixed point of the monotone map `f`, by iterating from ⊥."]],
    details: ["The steps are the Kleene chain $⊥, f(⊥), f(f(⊥)), …$, which is proved to end at the least fixed point (`order.iter_le_fixed`).", "`f` must be monotone and `P` must have a bottom."],
    examples: [basic("let D = divisors(12)", "let f = map(D; 1->2, 2->2, 3->6, 4->4, 6->6, 12->12)", "lfp(D, f)")],
    see: ["gfp", "fixpoints", "monotone"],
    ref: "https://mathworld.wolfram.com/FixedPoint.html",
  },
  {
    name: "gfp", area: "Order theory",
    usage: [["gfp(P, f)", "gives the greatest fixed point of the monotone map `f`, by iterating down from ⊤."]],
    examples: [basic("let D = divisors(12)", "let f = map(D; 1->2, 2->2, 3->6, 4->4, 6->6, 12->12)", "gfp(D, f)")],
    see: ["lfp", "fixpoints"],
  },
  {
    name: "fixpoints", area: "Order theory",
    usage: [["fixpoints(P, f)", "gives every `x` in `P` with f(x) = x."]],
    examples: [basic("let D = divisors(12)", "let f = map(D; 1->2, 3->6)", "fixpoints(D, f)", "lfp(D, f)")],
    see: ["lfp", "gfp"],
  },

  // --- λ-calculus ------------------------------------------------------------------------------
  {
    name: "lambda", title: "λ", area: "λ-calculus", notation: true,
    usage: [["λx. e", "is the function taking `x` to `e`; type `\\lam` for λ."], ["f a", "applies `f` to `a`."], ["name := term", "defines `name` for the cells after."]],
    details: [
      "Any cell with a λ, or a backslash (`\\x. x`), is a λ-cell.",
      "Application is juxtaposition and groups to the left; `λx y. e` binds two.",
      "The engine reduces in normal order, one β-step at a time, renaming bound variables to avoid capture.",
      "Digits are Church numerals, and the Church library is always there.",
      "A normal form that is a Church numeral or boolean is read out beside the result; View › de Bruijn indices shows the result with indices.",
      "A term with no normal form, such as `omega omega`, is refused rather than reduced forever.",
    ],
    examples: [
      basic("(λx. x) y", "(λx. λy. x) a b"),
      section("Scope", note("Capture is avoided:"), "(λx. λy. x y) y", note("Definitions:"), "TWO := succ (succ zero)", "add TWO 3"),
    ],
    see: ["church"],
    ref: "https://mathworld.wolfram.com/Lambda-Calculus.html",
  },
  {
    name: "church", title: "Church library", area: "λ-calculus", notation: true,
    usage: [
      ["true false and or not if", "are the Church booleans."],
      ["zero succ add mul pow iszero", "are the Church numerals' arithmetic; a digit is a numeral."],
      ["pair fst snd", "are pairs."],
      ["id const K S I omega Y", "are the classic combinators."],
    ],
    examples: [basic("if (iszero 0) a b", "fst (pair 1 2)", "mul 2 3")],
    see: ["lambda"],
  },

  // --- The notebook language -------------------------------------------------------------------
  {
    name: "let", area: "The notebook language", notation: true,
    usage: [["let name = e", "binds `name` to `e` for the cells after."], ["let f(x, y) = e", "defines a function of `x` and `y`."]],
    details: [
      "Later cells substitute the value, or expand the call.",
      "A bare function name stands for its body over its own parameters: after `let g(a, b) = a*b`, `integrate(g, a)` integrates `a*b`.",
      "`let x = import(…)` binds a file, and `let x = ?question` the answer to a question.",
    ],
    examples: [
      basic("let f = x^3 - 3x", "diff(f, x, 2)"),
      section("Functions", "let sq(x) = x^2 + 1", "sq(3)", "diff(sq(x), x)", "let g(a, b) = a*b", "integrate(g, a)"),
    ],
    see: ["%", "subst"],
  },
  {
    name: "%", title: "% (earlier output)", area: "The notebook language", notation: true,
    usage: [["%", "is the last output."], ["%%", "is the one before it."], ["%n", "is `Out[n]`."]],
    details: [
      "Mathematica's output references. The engine numbers every evaluation and substitutes the value before anything else happens, so the input interpretation shows what `%` stood for.",
      "Outputs are numbered in the order cells run, not their order on the page.",
    ],
    examples: [basic("x^3", "diff(%, x)", "diff(%, x)", "%1 + %2")],
    see: ["let"],
  },
  {
    name: "?", title: "? (lookup)", area: "The notebook language", notation: true,
    usage: [["?question", "looks the answer up and evaluates it: a number, a list, a table or a formula."], ["let x = ?question", "binds the answer; a formula becomes a function of its letters."]],
    details: [
      "A language model answers, from its own knowledge for standard mathematics and science, else by searching; every number it gives is checked against what it read.",
      "The answer is saved with the cell. See [Lookups](#doc:ask) and [Setting up lookups](#doc:ask-setup).",
    ],
    examples: [section("Examples", "?volume of a cone", "?the first ten primes", "let V = ?volume of a cone", "V(3, 4)")],
    see: ["let"],
  },
];

export const FN_BY_NAME = new Map(FUNCTIONS.map((f) => [f.name, f]));
/** The page id of a function's page. */
export const fnPage = (name: string) => `fn:${name}`;
/** Whether a section can be evaluated in the documentation: files and questions belong to a
 *  notebook (attachments, fetches, a model), so those sections are shown as inputs only. */
export const evaluable = (s: ExampleSection) => s.items.every((it) => typeof it !== "string" || !/\bimport\(|⟦|^\s*(let\s+\w+\s*=\s*)?\?|samplePoints|\bplanets\b|\bllama\b|\bpts\b/.test(it));
