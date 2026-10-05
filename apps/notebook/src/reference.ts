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
  | "Lists, tables and files" | "Statistics" | "Fourier series" | "Logic" | "Order theory" | "Transition systems" | "λ-calculus" | "The notebook language";

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
  ["Logic", "Propositional formulas, truth tables, normal forms, and quantifiers over finite sets."],
  ["Order theory", "Finite partial orders, lattices, monotone maps and their fixed points; relations and their properties."],
  ["Transition systems", "Finite state machines: reachable states, invariants with counterexample traces, induction, temporal logic, fairness, refinement; replicated data; term rewriting."],
  ["λ-calculus", "The untyped λ-calculus, reduced one β-step at a time by the strategy you choose, the Church encodings, and the simply typed calculus: type checking and inference."],
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
      "A power of numbers is computed exactly up to 19,728 digits (65,536 bits); a bigger one, like `2^(10^9)`, is an error that says how many digits it would have. `N` cannot help there, since it computes the exact value first.",
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
      "The combined form is checked before it is shown: it and the input, each times the common denominator, must normalize to the same term. So the two agree wherever the denominator is not zero, and the step says which denominator it assumes nonzero: `factor(1/x + 1)` is `(x + 1)/x`, assuming $x \\neq 0$ (at $x = 0$ the input is undefined).",
      "`expand` undoes it only up to value: `expand(factor(e))` equals `e` wherever the denominator is not zero, but it keeps every term over that denominator, so it is usually written differently from `e`.",
    ],
    examples: [
      basic("factor(x^2 + 2*x)", "factor(a/x + b/y)"),
      section("Scope", "factor(-2*x - 4)", "factor(x/2 + x/3)", "factor(1/x + 1)"),
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
    see: ["let", "lambda-subst"],
  },
  {
    name: "N", area: "Algebra",
    usage: [["N(e)", "gives a numerical value of `e`, to fifteen significant digits, each one certified."]],
    details: [
      "The digits are certified: the term is evaluated again over the rationals, to an interval proved to hold its exact value, and only the digits the interval pins down are shown, each within a unit of its last place. Usually that is all fifteen; when it is fewer, fewer are shown, and a value pinned down only near zero shows as 0.",
      "Over ℂ when the term mentions `i`, or when its real value is not finite: `N(sqrt(-1))` is `i`. A complex value is certified too, its real and imaginary parts each to their own digits: sums, products, quotients and integer powers, `exp`, `sin`, `cos` and `tan`, `abs`, `conj`, `re` and `im`, `ln` and `sqrt` of a real number, and a real number to a real power, on the principal branch (`N((-8)^(1/3))` is `1 + 1.73205080756888i`), and `ln` and powers of any complex number off the negative real axis, through a certified `arctan` for the angle (`N(ln(i))` is `1.5707963267949i`, `N(i^i)` is `0.207879576350762`).",
      "What the intervals do not reach is a floating-point approximation in IEEE-754 double precision, and its step says it is not certified: a function across a pole or a jump (`N(tan(pi/2))`), the logarithm or a power of a number on the negative real axis whose imaginary part is not exactly zero, where the angle jumps, and `arcsin`, `arccos`.",
      "A value too large or too small for fifteen places is written as a product with a power of ten, `N(exp(100))` as `2.68811714181614*10^43`, which reads back as the same number (not `2.68811714181614e+43`, which would be read as that times `e`, plus 43).",
      "A term with a free variable has no numerical value. The one exception is a variable named `e`, which `N` reads as Euler's number, though nothing else does; the answer warns that it is a variable (type `\\e` for the constant `ℯ`).",
    ],
    examples: [
      basic("N(pi)", "N(sqrt(2))"),
      section("Scope", "N(1/3)", "N(exp(1))", "N(exp(100))", "N(sin(pi/6))", "N(sin(10^30))", note("Not certified:"), "N(tan(pi/2))"),
      section("Over ℂ", "N(exp(i*pi/4))", "N(1/(1+i))", "N(sqrt(-4))", "N((-8)^(1/3))", "N(ln(i))", "N(i^i)"),
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
    details: ["`exp(x)`, `ℯ^x` and `e^x` written with `\\e` are the same function. A plain letter `e` is a variable, so `e^x` typed without `\\e` is not `exp(x)`; the answer says so under it.", "Its own derivative and its own antiderivative.", "An answer shows it as a power of e, $e^{x}$; as text it stays `exp(x)`, which reads back as the same thing."],
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
    see: ["cos", "tan", "csc", "arcsin", "exptotrig"],
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
    see: ["sin", "tan", "sec", "arccos"],
    ref: "https://mathworld.wolfram.com/Cosine.html",
  },
  {
    name: "tan", area: "Elementary functions",
    usage: [["tan(x)", "gives the tangent of `x`, sin x / cos x."]],
    details: ["The derivative is $\\sec^2 x$."],
    examples: [
      basic("tan(pi/4) + tan(pi/3)", "diff(tan(x), x)"),
      section("Scope", "integrate(tan(x), x)", "integrate(sec(x)^2, x)"),
    ],
    see: ["sin", "cos", "cot", "arctan"],
    ref: "https://mathworld.wolfram.com/Tangent.html",
  },
  {
    name: "sec", area: "Elementary functions",
    usage: [["sec(x)", "gives the secant of `x`, 1 / cos x."]],
    details: [
      "Notation, not a function of its own: `sec(x)` is read as `cos(x)^-1`, and the answer is written that way.",
      "So its derivative, its integrals and its values are those of the cosine, and an exercise answer written with `sec` is checked by what it means.",
    ],
    examples: [
      basic("sec(x)", "sec^2(x)", "diff(sec(x), x)"),
      section("Scope", "integrate(sec(x)^2, x)", "diff(tan(x), x) - sec(x)^2"),
    ],
    see: ["cos", "csc", "cot"],
    ref: "https://mathworld.wolfram.com/Secant.html",
  },
  {
    name: "csc", area: "Elementary functions",
    usage: [["csc(x)", "gives the cosecant of `x`, 1 / sin x."]],
    details: ["Notation, not a function of its own: `csc(x)` is read as `sin(x)^-1`, and the answer is written that way."],
    examples: [
      basic("csc(x)", "csc(x) * sin(x)", "diff(csc(x), x)"),
    ],
    see: ["sin", "sec", "cot"],
    ref: "https://mathworld.wolfram.com/Cosecant.html",
  },
  {
    name: "cot", area: "Elementary functions",
    usage: [["cot(x)", "gives the cotangent of `x`, 1 / tan x."]],
    details: ["Notation, not a function of its own: `cot(x)` is read as `tan(x)^-1`, and the answer is written that way."],
    examples: [
      basic("cot(x)", "cot(x) * tan(x)", "diff(cot(x), x)"),
    ],
    see: ["tan", "sec", "csc"],
    ref: "https://mathworld.wolfram.com/Cotangent.html",
  },
  {
    name: "cosh", area: "Elementary functions",
    usage: [["cosh(x)", "gives the hyperbolic cosine of `x`, (e^x + e^-x) / 2."]],
    details: [
      "Notation, not a function of its own: `cosh(x)` is read as `(exp(x) + exp(-x))/2`, the even part of `exp`, and the answer is written that way.",
      "So its derivative, its integrals and its values are those of `exp`, with their proofs, and an exercise answer written with `cosh` is checked by what it means.",
      "`(cosh t, sinh t)` runs along the hyperbola x² − y² = 1 as `(cos t, sin t)` runs round the circle, and `cosh(i*t)` is `cos(t)`.",
    ],
    examples: [
      basic("cosh(x)", "cosh(0)", "N(cosh(1))"),
      section("Scope", "diff(cosh(x), x) - sinh(x)", "expand(cosh(x)^2 - sinh(x)^2)", "exptotrig(cosh(i*t))"),
    ],
    see: ["sinh", "tanh", "exp", "cos"],
    ref: "https://mathworld.wolfram.com/HyperbolicCosine.html",
  },
  {
    name: "sinh", area: "Elementary functions",
    usage: [["sinh(x)", "gives the hyperbolic sine of `x`, (e^x − e^-x) / 2."]],
    details: ["Notation, not a function of its own: `sinh(x)` is read as `(exp(x) - exp(-x))/2`, the odd part of `exp`, and the answer is written that way."],
    examples: [
      basic("sinh(x)", "diff(sinh(x), x) - cosh(x)", "expand(cosh(x) + sinh(x))"),
    ],
    see: ["cosh", "tanh", "exp", "sin"],
    ref: "https://mathworld.wolfram.com/HyperbolicSine.html",
  },
  {
    name: "tanh", area: "Elementary functions",
    usage: [["tanh(x)", "gives the hyperbolic tangent of `x`, sinh x / cosh x."]],
    details: ["Notation, not a function of its own: `tanh(x)` is read as `(exp(x) - exp(-x))/(exp(x) + exp(-x))`, and the answer is written that way."],
    examples: [
      basic("tanh(x)", "N(tanh(2))", "expand(diff(tanh(x), x) - (1 - tanh(x)^2))"),
    ],
    see: ["sinh", "cosh", "tan"],
    ref: "https://mathworld.wolfram.com/HyperbolicTangent.html",
  },
  {
    name: "arcsin", area: "Elementary functions",
    usage: [["arcsin(x)", "gives the inverse sine of `x`, the angle from -π/2 to π/2 whose sine is `x`."]],
    details: [
      "`sin^-1(x)` is the reciprocal $1/\\sin x$, as `sin^2(x)` is the square; write `arcsin(x)` for the inverse.",
      "The derivative is $1/\\sqrt{1 - x^2}$; the step assumes $-1 < x < 1$, where it is proved.",
      "`N` gives its value as a double, not certified.",
    ],
    examples: [
      basic("arcsin(x)", "N(arcsin(1/2))", "diff(arcsin(x), x)"),
      section("Scope", "diff(arcsin(2x), x)", "integrate(1/sqrt(1 - x^2), x)", "integrate(1/sqrt(4 - x^2), x)", "integrate(arcsin(x), x)"),
    ],
    see: ["arccos", "arctan", "sin"],
    ref: "https://mathworld.wolfram.com/InverseSine.html",
  },
  {
    name: "arccos", area: "Elementary functions",
    usage: [["arccos(x)", "gives the inverse cosine of `x`, the angle from 0 to π whose cosine is `x`."]],
    details: [
      "The derivative is $-1/\\sqrt{1 - x^2}$; the step assumes $-1 < x < 1$, where it is proved.",
      "`N` gives its value as a double, not certified.",
    ],
    examples: [
      basic("N(arccos(0))", "diff(arccos(x), x)"),
      section("Scope", "diff(arccos(x^2), x)", "integrate(arccos(2x), x)"),
    ],
    see: ["arcsin", "arctan", "cos"],
    ref: "https://mathworld.wolfram.com/InverseCosine.html",
  },
  {
    name: "arctan", area: "Elementary functions",
    usage: [["arctan(x)", "gives the inverse tangent of `x`, the angle strictly between -π/2 and π/2 whose tangent is `x`."]],
    details: [
      "The derivative is $1/(1 + x^2)$, proved for every real `x`.",
      "`integrate` finds $\\int dx/(k + c x^2)$ as an arctangent, and checks it by differentiating.",
      "`N` gives its value as a double, not certified.",
    ],
    examples: [
      basic("arctan(x)", "N(4*arctan(1))", "diff(arctan(x), x)"),
      section("Scope", "integrate(1/(1 + x^2), x)", "integrate(1/(4 + x^2), x)", "integrate(arctan(x), x)"),
    ],
    see: ["arcsin", "arccos", "tan"],
    ref: "https://mathworld.wolfram.com/InverseTangent.html",
  },

  // --- Calculus --------------------------------------------------------------------------------
  {
    name: "diff", area: "Calculus",
    usage: [["diff(f, x)", "gives the derivative of `f` with respect to `x`."], ["diff(f, x, n)", "gives the `n`-th derivative."]],
    details: [
      "Implemented as rewrite rules that push $d/dx$ inward (sum, product, quotient, chain and power rules), so the derivation reads like a textbook's.",
      "Other variables are constants: `diff(x*y, x)` is `y`.",
      "A vector or matrix is differentiated entry by entry.",
      "A step that needs something says so: the derivative of `ln u` assumes `u > 0`, of `tan u` that `cos u ≠ 0`, a real exponent a positive base, and a rule applied to a part that is not differentiable everywhere (`abs(x)`) assumes it differentiable. The other steps hold at every point.",
    ],
    examples: [
      basic("diff(x^2 * sin(x), x)", "diff(x^3, x, 2)"),
      section("Steps that assume", "diff(ln(x), x)", "diff(x^(1/2), x)", "diff(tan(x), x)"),
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
      "A small rule set (substitution, parts, a table of forms) finds an antiderivative, and it is accepted only if differentiating it gives `f` back.",
      "Most of the rules are proved as well (`anti_sound`): given antiderivatives of the parts, each rule's result is one of the whole. A rule that needs a condition says so in its step: `ln u` for `u > 0`, `tan u` for `cos u > 0`, `bᵘ` for `b > 0, b ≠ 1`, dividing by a symbolic coefficient `k` for `k ≠ 0`. Substitution and integration by parts build on the simplifier's outputs; their steps are marked *checked*, and the check above is their proof.",
      "With bounds, the checked antiderivative at `b` minus at `a`: the fundamental theorem of calculus (`integrate_definite`).",
      "When no guess checks out, the integral is left as it is.",
    ],
    examples: [
      basic("integrate(x^2 + sin(x), x)", "integrate(cos(t)*sin(t), t, 0, 2pi)"),
      section("Scope", "integrate(exp(2*x), x)", "integrate(x/(x^2+1), x)", "integrate(x*exp(x^2), x)", "integrate(ln(x), x)", "integrate(x^2*exp(x), x)", "integrate(exp(-3i*t), t, 0, pi)"),
      section("Steps that assume", "integrate(1/x, x)", "integrate(tan(x), x)", "integrate(sin(k*x), x)", "integrate(b^x, x)"),
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
      "Beside a plot, any other value shows its calculation at each `p`: the expression with `p` put in, the engine's steps, and the value, as `m = ((2 + 1)^2 - 1)/2 = (9 - 1)/2 = 4`.",
      "`column(e₁, e₂, …)` puts several things under the one slider, like Mathematica's `Column`: each is evaluated as its own cell. A part that is a name (`m`) is labelled with it.",
      "`p` is bound only inside the frames, and must not be the plot's own variable. The cell's value and work are its first frame's.",
    ],
    examples: [
      basic("manipulate(plot(sin(a*x), x, 0, 2pi), a, 1, 4)", "manipulate(diff(x^n, x), n, 1, 5, 5)"),
      section("Scope",
        note("A secant turning into the tangent of x² at 1 as h shrinks toward 0:"),
        "manipulate(plot([x^2, 1 + ((1 + h)^2 - 1)/h*(x - 1)], x, -0.5, 3), h, 2, 0.05)",
        note("With the slope worked out beside it:"),
        "let m = ((1 + h)^2 - 1)/h",
        "manipulate(column(plot([x^2, 1 + m*(x - 1)], x, -0.5, 3), m), h, 2, 0.05)"),
    ],
    see: ["column", "plot", "subst"],
  },
  {
    name: "column", area: "Calculus",
    usage: [["column(e₁, e₂, …)", "inside `manipulate`, shows each `eᵢ` under the one slider, one below the other."]],
    details: [
      "Mathematica's `Column`. Each part is evaluated as its own cell would be, at every value of the slider: a plot animates, and any other part shows its calculation there.",
      "A part that is a name the notebook has bound (`let m = …`) is labelled with the name.",
      "Outside `manipulate` it is only its parts, evaluated.",
    ],
    examples: [basic("manipulate(column(plot(x^n, x, 0, 2), diff(x^n, x)), n, 1, 4, 4)")],
    see: ["manipulate", "plot"],
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
    see: ["re", "conj", "arg"],
  },
  {
    name: "arg", area: "Complex numbers",
    usage: [["arg(z)", "gives the argument of `z`: the angle from the positive real axis to `z`, in radians, between -π and π."]],
    details: [
      "With `abs`, it is `z` in polar form: $z = |z|\\,e^{i \\arg z}$.",
      "Left as it is in the answer; `N` gives its value as a double, not certified.",
    ],
    examples: [
      basic("N(arg(1 + i))", "N(arg(-1))", "N(arg(exp(2i)))"),
      section("Polar form", "let z = 1 + i", "abs(z)", "N(arg(z))"),
    ],
    see: ["abs", "re", "im", "exptotrig"],
    ref: "https://mathworld.wolfram.com/ComplexArgument.html",
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
    details: ["Gauss–Jordan elimination. Each row operation is a step of its own, nested under the command.",
      "With symbols among the entries, a pivot is an entry the simplifier cannot show is zero, and the step that divides by it says it assumes it is not zero; where simplifying a row cancels a factor, the step says that too. The answer holds wherever those assumptions do."],
    examples: [
      basic("rref([1,2,3;4,5,6;7,8,10])"),
      section("Symbolic entries", "rref([x, y; x^2, 1])"),
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
    usage: [
      ["map(P; a->b, c->d, …)", "gives the map on `P` sending `a` to `b`, `c` to `d`, …, and every other element to itself."],
      ["map(P, Q; a->x, …)", "gives a map from `P` to `Q`, which must list every element of `P`."],
    ],
    details: ["Bind it with `let` to use it with `monotone`, `lfp`, `gfp`, `fixpoints`, `galois` and `closureop`."],
    examples: [
      basic("let D = divisors(12)", "let f = map(D; 1->2, 3->6)", "monotone(D, f)", "lfp(D, f)"),
      section("Between two posets", "let D = divisors(12)", "let C = chain(3)", "let h = map(D, C; 1->0, 2->1, 3->1, 4->2, 6->2, 12->2)", "monotone(D, C, h)"),
    ],
    see: ["monotone", "lfp", "fixpoints", "galois"],
  },
  {
    name: "monotone", area: "Order theory",
    usage: [["monotone(P, f)", "gives `true` when x ≤ y implies f(x) ≤ f(y) for every pair in `P`."], ["monotone(P, Q, f)", "does the same for a map from `P` to `Q`."]],
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
  // relations: a poset is a relation with three properties built in; here the properties are the question
  {
    name: "rel", area: "Order theory",
    usage: [["rel({a, b, c}; a->b, b->c)", "is the relation on the set whose pairs are the arrows listed."]],
    details: [
      "`x->y` is the pair $(x, y)$: read it as $x \\mathrel{R} y$, or as \"x steps to y\".",
      "A relation's commands take a name: bind a relation with `let` to ask about it, or about its closure.",
      "The answer is the set of pairs, and the cell draws the relation as a graph.",
      "Unlike `poset`, nothing is assumed: whether it is reflexive, symmetric or transitive is for `reflexive`, `symmetric` and `transitive` to say.",
    ],
    examples: [basic("let R = rel({a, b, c}; a->b, b->c)", "transitive(R)", "closure(R, transitive)")],
    see: ["kernel", "transitive", "closure", "poset"],
    ref: "https://mathworld.wolfram.com/Relation.html",
  },
  {
    name: "kernel", area: "Order theory",
    usage: [["kernel({x, y, …}; x->k, y->k, …)", "is the relation \"has the same label as\": x and y are related when they are sent to the same label."]],
    details: [
      "The kernel of a map is always an equivalence relation; its classes are the map's fibres.",
      "An element given no label is its own label.",
    ],
    examples: [basic("let K = kernel({r1, r2, r3, r4}; r1->k1, r2->k1, r3->k2, r4->k2)", "equivalence(K)", "classes(K)")],
    see: ["classes", "equivalence", "finer"],
  },
  {
    name: "reflexive", area: "Order theory",
    usage: [["reflexive(R)", "gives `true` when every element is related to itself."]],
    details: ["When it does not hold, the step names an element $x$ without $x \\mathrel{R} x$."],
    examples: [basic("let R = rel({a, b, c}; a->b, b->c)", "reflexive(R)", "let S = closure(R, reflexive)", "reflexive(S)")],
    see: ["symmetric", "transitive", "closure"],
  },
  {
    name: "symmetric", area: "Order theory",
    usage: [["symmetric(R)", "gives `true` when every pair's reverse is a pair too."]],
    details: ["When it does not hold, the graph marks a pair whose reverse is missing."],
    examples: [basic("let R = rel({a, b, c}; a->b, b->c)", "symmetric(R)", "closure(R, symmetric)")],
    see: ["antisymmetric", "closure"],
  },
  {
    name: "antisymmetric", area: "Order theory",
    usage: [["antisymmetric(R)", "gives `true` when no two different elements are related both ways."]],
    examples: [basic("let R = rel({a, b, c}; a->b, b->a)", "antisymmetric(R)", "let D = divisors(12)", "antisymmetric(D)")],
    see: ["symmetric", "preorder"],
  },
  {
    name: "transitive", area: "Order theory",
    usage: [["transitive(R)", "gives `true` when x R y and y R z always give x R z."]],
    details: ["When it does not hold, the graph marks two pairs that chain without their composite."],
    examples: [basic("let R = rel({a, b, c}; a->b, b->c)", "transitive(R)", "let T = closure(R, transitive)", "transitive(T)")],
    see: ["closure", "preorder"],
    ref: "https://mathworld.wolfram.com/Transitive.html",
  },
  {
    name: "equivalence", area: "Order theory",
    usage: [["equivalence(R)", "gives `true` when `R` is reflexive, symmetric and transitive."]],
    details: ["When it does not hold, the step says which property fails, with its witness."],
    examples: [basic("let K = kernel({r1, r2, r3}; r1->k, r2->k)", "equivalence(K)", "let R = rel({a, b}; a->b)", "equivalence(R)")],
    see: ["classes", "kernel", "closure"],
    ref: "https://mathworld.wolfram.com/EquivalenceRelation.html",
  },
  {
    name: "preorder", area: "Order theory",
    usage: [["preorder(R)", "gives `true` when `R` is reflexive and transitive."]],
    details: ["A preorder that is also antisymmetric is a partial order."],
    examples: [basic("let D = divisors(12)", "preorder(D)", "let R = rel({a, b}; a->a, b->b, a->b, b->a)", "preorder(R)", "antisymmetric(R)")],
    see: ["antisymmetric", "poset"],
  },
  {
    name: "closure", area: "Order theory",
    usage: [["closure(R, p)", "gives the least relation containing `R` with property `p`: reflexive, symmetric, transitive or equivalence."]],
    details: [
      "Each round of the transitive closure is a step: the pairs forced by two that chain. It stops when a round adds nothing.",
      "The transitive closure is proved transitive and inside every transitive relation containing `R`, so it is the least (`transClosure_transitive`, `transClosure_sub`).",
      "The graph shows the added pairs dashed.",
    ],
    examples: [
      basic("let R = rel({a, b, c, d}; a->b, b->c, c->d)", "closure(R, transitive)"),
      section("Scope", "let R = rel({a, b, c}; a->b, b->c)", "closure(R, reflexive)", "closure(R, symmetric)", "let E = closure(R, equivalence)", "classes(E)"),
      section("Calls inside calls", "transitive(closure(R, transitive))", "classes(closure(R, equivalence))"),
    ],
    see: ["transitive", "equivalence", "classes"],
    ref: "https://mathworld.wolfram.com/TransitiveClosure.html",
  },
  {
    name: "classes", area: "Order theory",
    usage: [["classes(R)", "gives the equivalence classes of the equivalence relation `R`: a partition of its set."]],
    examples: [basic("let K = kernel({r1, r2, r3, r4}; r1->k1, r2->k1, r3->k2, r4->k2)", "classes(K)")],
    see: ["kernel", "equivalence", "finer"],
    ref: "https://mathworld.wolfram.com/EquivalenceClass.html",
  },
  {
    name: "finer", area: "Order theory",
    usage: [["finer(R, S)", "gives `true` when every pair of `R` is a pair of `S`."]],
    details: ["For equivalence relations: every class of `R` lies inside a class of `S`. When it does not hold, the step names a pair of `R` that `S` lacks."],
    examples: [basic("let K = kernel({r1, r2, r3, r4}; r1->k1, r2->k1, r3->k2, r4->k2)", "let A = kernel({r1, r2, r3, r4}; r1->a, r2->b, r3->c, r4->c)", "finer(A, K)", "finer(K, A)")],
    see: ["classes", "kernel"],
  },
  {
    name: "wellfounded", area: "Order theory",
    usage: [["wellfounded(R)", "gives `true` when there is no infinite chain of steps x R y R z …."]],
    details: ["On a finite set that is the same as having no cycle; when there is one, the step shows it."],
    examples: [basic("let R = rel({a, b, c}; a->b, b->c)", "wellfounded(R)", "let C = rel({x, y, z}; x->y, y->z, z->x)", "wellfounded(C)")],
    see: ["measure"],
  },
  {
    name: "measure", area: "Order theory",
    usage: [["measure(R; x->n, …)", "gives `true` when every step x R y goes down: m(y) < m(x)."]],
    details: [
      "A measure into the natural numbers proves a relation well-founded: a chain of steps is a decreasing chain of numbers, which cannot go on forever.",
      "When it does not hold, the step names a step the measure does not decrease along.",
    ],
    examples: [basic("let R = rel({a, b, c}; a->b, b->c)", "measure(R; a->2, b->1, c->0)", "measure(R; a->0, b->1, c->2)")],
    see: ["wellfounded"],
  },

  // happens-before
  {
    name: "events", area: "Order theory",
    usage: [["events({a1, a2}, {b1, b2}; a1->b2)", "gives the happens-before order of events on processes: each set is one process's events in order, each arrow a message from its sending to its receipt."]],
    details: ["Messages that would make an event happen before itself are refused."],
    examples: [basic("let E = events({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)", "le(E, a1, b2)", "concurrent(E, a2, b2)")],
    see: ["clocks", "concurrent"],
  },
  {
    name: "clocks", area: "Order theory",
    usage: [["clocks({a1, a2}, {b1, b2}; a1->b2)", "gives each event's vector clock: for each process, how many of its events happen before the event or are it."]],
    details: ["One event happens before another exactly when its clock is below the other's in every entry."],
    examples: [basic("clocks({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)")],
    see: ["events"],
  },
  {
    name: "concurrent", area: "Order theory",
    usage: [["concurrent(E, a, b)", "gives `true` when neither event happens before the other."]],
    examples: [basic("let E = events({a1, a2}, {b1, b2}; a1->b2)", "concurrent(E, a2, b2)", "concurrent(E, a1, b2)")],
    see: ["events"],
  },
  // finite algebra: a lattice read as operations with laws, and the bridges between the two readings
  {
    name: "op", area: "Order theory",
    usage: [["op({a, b, …}; [row; row; …])", "is the operation on the set whose table has those rows: row i, column j is the i-th element times the j-th."]],
    details: [
      "Bind it with `let`; the cell draws the table. Every entry must be an element of the set.",
      "Its laws are questions: `associative`, `commutative`, `idempotent`, `semilattice`, `identity`.",
    ],
    examples: [
      basic("let M = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])", "semilattice(M)", "identity(M)"),
      section("Combining access decisions", note("Deny overrides: a deny anywhere wins, then a permit; not applicable is neutral."), "let DO = op({na, permit, deny}; [na, permit, deny; permit, permit, deny; deny, deny, deny])", "fold(DO; permit, na, deny, permit)"),
    ],
    see: ["joinop", "semilattice", "fold", "order"],
    ref: "https://mathworld.wolfram.com/BinaryOperation.html",
  },
  {
    name: "joinop", area: "Order theory",
    usage: [["joinop(L)", "gives the join of the lattice `L` as an operation table."]],
    details: ["Every pair must have a join. The table is a semilattice, and `order` of it gives back `L`'s order."],
    examples: [basic("let D = divisors(12)", "let J = joinop(D)", "semilattice(J)")],
    see: ["meetop", "op", "order"],
  },
  {
    name: "meetop", area: "Order theory",
    usage: [["meetop(L)", "gives the meet of the lattice `L` as an operation table."]],
    examples: [basic("let D = divisors(12)", "meetop(D)")],
    see: ["joinop"],
  },
  {
    name: "table", area: "Order theory",
    usage: [["table(J)", "draws the table of the operation `J`."]],
    examples: [basic("let M = op({0, 1}; [0, 1; 1, 1])", "table(M)")],
    see: ["op"],
  },
  {
    name: "associative", area: "Order theory",
    usage: [["associative(J)", "gives `true` when (x · y) · z = x · (y · z) for every triple."]],
    details: ["When it fails, the step names the triple and the table marks the four entries the two sides read."],
    examples: [basic("let RPS = op({r, p, s}; [r, p, r; p, p, s; r, s, s])", "commutative(RPS)", "idempotent(RPS)", "associative(RPS)")],
    see: ["commutative", "idempotent", "semilattice"],
    ref: "https://mathworld.wolfram.com/Associative.html",
  },
  {
    name: "commutative", area: "Order theory",
    usage: [["commutative(J)", "gives `true` when x · y = y · x for every pair."]],
    details: ["When it fails, the table marks the two entries that differ."],
    examples: [basic("let FA = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, deny, deny])", "commutative(FA)", "associative(FA)")],
    see: ["associative", "semilattice"],
    ref: "https://mathworld.wolfram.com/Commutative.html",
  },
  {
    name: "idempotent", area: "Order theory",
    usage: [["idempotent(J)", "gives `true` when x · x = x for every x."]],
    examples: [basic("let A = op({0, 1}; [0, 1; 1, 0])", "idempotent(A)")],
    see: ["semilattice"],
  },
  {
    name: "semilattice", area: "Order theory",
    usage: [["semilattice(J)", "gives `true` when `J` is associative, commutative and idempotent."]],
    details: ["A semilattice orders its set: x ≤ y when x · y = y, and then x · y is the join. `order` draws it."],
    examples: [basic("let DO = op({na, permit, deny}; [na, permit, deny; permit, permit, deny; deny, deny, deny])", "semilattice(DO)", "order(DO)")],
    see: ["order", "associative", "joinop"],
    ref: "https://mathworld.wolfram.com/Semilattice.html",
  },
  {
    name: "identity", area: "Order theory",
    usage: [["identity(J)", "gives the element e with e · x = x = x · e for every x, if there is one."]],
    details: ["In a join-semilattice the identity is the bottom element."],
    examples: [basic("let DO = op({na, permit, deny}; [na, permit, deny; permit, permit, deny; deny, deny, deny])", "identity(DO)")],
    see: ["fold"],
  },
  {
    name: "fold", area: "Order theory",
    usage: [["fold(J; x, y, z, …)", "combines the elements left to right: ((x · y) · z) · …."]],
    details: ["Each combination is a step. With no elements the answer is the identity.", "For an associative and commutative operation the order of the list does not matter; for others it can."],
    examples: [
      basic("let DO = op({na, permit, deny}; [na, permit, deny; permit, permit, deny; deny, deny, deny])", "fold(DO; permit, na, deny, permit)"),
      section("Order matters", note("First applicable: the first decision that is not na wins."), "let FA = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, deny, deny])", "fold(FA; na, permit, deny)", "fold(FA; na, deny, permit)"),
    ],
    see: ["op", "identity"],
  },
  {
    name: "order", area: "Order theory",
    usage: [["order(J)", "gives the partial order of the semilattice `J`: x ≤ y when x · y = y."]],
    details: ["Proved a partial order in which x · y is the join of x and y (`semilattice_order`). Refused, with the law that fails, when `J` is not a semilattice."],
    examples: [basic("let M = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])", "order(M)")],
    see: ["semilattice", "joinop"],
  },
  {
    name: "distributive", area: "Order theory",
    usage: [["distributive(L)", "gives `true` when x ∧ (y ∨ z) = (x ∧ y) ∨ (x ∧ z) for every triple of the lattice `L`."]],
    details: ["When it fails, the step computes both sides for the triple. Every non-distributive lattice contains M₃ or N₅."],
    examples: [basic("let M3 = poset({bot, a, b, c, top}; bot < a, bot < b, bot < c, a < top, b < top, c < top)", "distributive(M3)", "let D = divisors(12)", "distributive(D)")],
    see: ["boolean", "complement", "lattice"],
    ref: "https://mathworld.wolfram.com/DistributiveLattice.html",
  },
  {
    name: "complement", area: "Order theory",
    usage: [["complement(L, x)", "gives every y with x ∨ y = ⊤ and x ∧ y = ⊥."]],
    details: ["In a distributive lattice there is at most one; in M₃ there can be two."],
    examples: [basic("let M3 = poset({bot, a, b, c, top}; bot < a, bot < b, bot < c, a < top, b < top, c < top)", "complement(M3, a)", "let D = divisors(12)", "complement(D, 4)", "complement(D, 2)")],
    see: ["complemented", "boolean"],
  },
  {
    name: "complemented", area: "Order theory",
    usage: [["complemented(L)", "gives `true` when every element of the lattice `L` has a complement."]],
    examples: [basic("let D = divisors(12)", "complemented(D)")],
    see: ["complement", "boolean"],
  },
  {
    name: "boolean", area: "Order theory",
    usage: [["boolean(L)", "gives `true` when the lattice `L` is distributive and complemented: a Boolean lattice."]],
    examples: [basic("let P = subsets({x, y, z})", "boolean(P)", "let D = divisors(12)", "boolean(D)", "let E = divisors(30)", "boolean(E)")],
    see: ["distributive", "complement", "subsets"],
    ref: "https://mathworld.wolfram.com/BooleanAlgebra.html",
  },
  {
    name: "product", area: "Order theory",
    usage: [["product(P, Q)", "gives the pairs (x, y) ordered componentwise: (a, c) ≤ (b, d) when a ≤ b and c ≤ d."]],
    details: [
      "Write a pair element as `(x, y)`, and a set element as `{a, b}`: `join(PQ, (low, {a}), (high, {}))`.",
      "Like every order and systems command, it takes a call where it takes a name: `product(chain(2), chain(3))` builds the chains first.",
    ],
    examples: [
      basic("let Lv = poset({low, high}; low < high)", "let Cat = subsets({a, b})", "let SC = product(Lv, Cat)", "join(SC, (low, {a}), (high, {}))"),
      section("Calls inside calls", "lattice(product(chain(2), chain(3)))"),
    ],
    see: ["secure", "subsets"],
    ref: "https://mathworld.wolfram.com/ProductOrder.html",
  },
  {
    name: "galois", area: "Order theory",
    usage: [["galois(P, Q, f, g)", "gives `true` when f(x) ≤ y exactly when x ≤ g(y), for every x in `P` and y in `Q`."]],
    details: ["`f` is a map from `P` to `Q` and `g` one back; `f` is the lower adjoint, `g` the upper. When it fails, the step names the pair."],
    examples: [basic("let C7 = chain(7)", "let C4 = chain(4)", "let half = map(C7, C4; 0->0, 1->1, 2->1, 3->2, 4->2, 5->3, 6->3)", "let dbl = map(C4, C7; 0->0, 1->2, 2->4, 3->6)", "galois(C7, C4, half, dbl)")],
    see: ["map", "closureop"],
    ref: "https://mathworld.wolfram.com/GaloisConnection.html",
  },
  {
    name: "closureop", area: "Order theory",
    usage: [["closureop(P, f)", "gives `true` when `f` is extensive (x ≤ f(x)), monotone and idempotent (f(f(x)) = f(x))."]],
    details: ["Its fixed points (`fixpoints`) are the closed elements, and they form a lattice of their own."],
    examples: [basic("let D = divisors(12)", "let c = map(D; 3->6)", "closureop(D, c)", "fixpoints(D, c)")],
    see: ["galois", "fixpoints"],
    ref: "https://mathworld.wolfram.com/ClosureOperator.html",
  },
  {
    name: "context", area: "Order theory",
    usage: [["context({objects}, {attributes}; o->a, …)", "is the formal context in which each object `o` has the attributes listed for it."]],
    details: ["Bind it with `let`; the cell draws the cross table. `concepts` gives its concept lattice."],
    examples: [basic("let A = context({duck, eagle, dog, bat}, {flies, mammal, bird}; duck->flies, duck->bird, eagle->flies, eagle->bird, dog->mammal, bat->flies, bat->mammal)", "concepts(A)")],
    see: ["concepts"],
  },
  {
    name: "concepts", area: "Order theory",
    usage: [["concepts(C)", "gives the concept lattice of the context `C`: the pairs (objects, attributes) that determine each other, ordered by objects."]],
    details: ["A concept's objects are all those having all its attributes, and its attributes are all those its objects share. The concepts always form a complete lattice."],
    examples: [basic("let A = context({duck, eagle, dog, bat}, {flies, mammal, bird}; duck->flies, duck->bird, eagle->flies, eagle->bird, dog->mammal, bat->flies, bat->mammal)", "concepts(A)")],
    see: ["context", "galois"],
    ref: "https://mathworld.wolfram.com/FormalConceptAnalysis.html",
  },
  {
    name: "secure", area: "Order theory",
    usage: [["secure(P, R; x->c, …)", "gives `true` when every flow x → y of the relation `R` goes from the class of x to one at least as high in the lattice `P`."]],
    details: ["Denning's model: information may flow up the lattice of security classes, never down. When a flow goes down, the graph marks it."],
    examples: [basic("let Lv = poset({low, high}; low < high)", "let Cat = subsets({a, b})", "let SC = product(Lv, Cat)", "let F = rel({x, y, z}; x->y, y->z)", "secure(SC, F; x->(low, {a}), y->(high, {a}), z->(low, {a, b}))")],
    see: ["product", "rel"],
  },

  // --- Transition systems ----------------------------------------------------------------------
  {
    name: "system", area: "Transition systems",
    usage: [["system(var x in 0..3; init x = 0; action inc when x < 3 do x := x + 1)", "is the transition system with those variables, initial condition and actions."]],
    details: [
      "Clauses are separated by `;` or by line breaks (Shift+Enter starts a new line in a cell): `var x in lo..hi`, `var p in {idle, crit}`, `var b in bool`; one `init` condition; and `action NAME when GUARD do x := e, y := e'`.",
      "Updates in one action happen together, reading the old values. The guard may be left out. `fair action` and `strong fair action` mark actions for `eventually`.",
      "Bind it with `let`; the cell draws the reachable states (up to 40) as a graph.",
    ],
    examples: [basic("let C = system(var x in 0..3; var y in 0..3; init x = 0 ∧ y = 0; action inc when x < 3 do x := x + 1; action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1)", "states(C)")],
    see: ["states", "invariant", "trace"],
  },
  {
    name: "states", area: "Transition systems",
    usage: [["states(S)", "gives the number of reachable states of `S` and draws its state graph."]],
    examples: [basic("let C = system(var x in 0..3; var y in 0..3; init x = 0 ∧ y = 0; action inc when x < 3 do x := x + 1; action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1)", "states(C)")],
    see: ["system", "reach"],
  },
  {
    name: "invariant", area: "Transition systems",
    usage: [["invariant(S, φ)", "gives `true` when φ holds in every reachable state, and otherwise `false` with a shortest trace to a state that breaks it."]],
    details: ["The trace is the work: a step per action, which can be stepped through, and its transitions are marked on the graph."],
    examples: [basic("let C = system(var x in 0..3; var y in 0..3; init x = 0 ∧ y = 0; action inc when x < 3 do x := x + 1; action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1)", "invariant(C, x + y ≤ 3)", "invariant(C, y ≤ 3)"), section("Mutual exclusion", "let L = system(var p in {idle, crit}; var q in {idle, crit}; var lock in bool; init p = idle ∧ q = idle ∧ lock = false; action penter when p = idle ∧ lock = false do lock := true, p := crit; action pexit when p = crit do p := idle, lock := false; action qenter when q = idle ∧ lock = false do lock := true, q := crit; action qexit when q = crit do q := idle, lock := false)", "invariant(L, ¬(p = crit ∧ q = crit))")],
    see: ["inductive", "reach", "trace"],
  },
  {
    name: "inductive", area: "Transition systems",
    usage: [["inductive(S, φ)", "gives `true` when φ holds initially and every action from any state where it holds (reachable or not) leads to one where it holds."]],
    details: ["An inductive formula is an invariant with a one-step proof. When it fails, the step shows a counterexample to induction and says whether that state is reachable: if not, the formula may be an invariant that needs strengthening."],
    examples: [basic("let L = system(var p in {idle, crit}; var q in {idle, crit}; var lock in bool; init p = idle ∧ q = idle ∧ lock = false; action penter when p = idle ∧ lock = false do lock := true, p := crit; action pexit when p = crit do p := idle, lock := false; action qenter when q = idle ∧ lock = false do lock := true, q := crit; action qexit when q = crit do q := idle, lock := false)", "inductive(L, ¬(p = crit ∧ q = crit))", "inductive(L, (p = crit → lock = true) ∧ (q = crit → lock = true) ∧ ¬(p = crit ∧ q = crit))")],
    see: ["invariant"],
  },
  {
    name: "reach", area: "Transition systems",
    usage: [["reach(S, φ)", "gives `true` with a shortest trace when some reachable state satisfies φ."]],
    examples: [basic("let C = system(var x in 0..3; var y in 0..3; init x = 0 ∧ y = 0; action inc when x < 3 do x := x + 1; action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1)", "reach(C, y = 3)")],
    see: ["invariant", "states"],
  },
  {
    name: "deadlock", area: "Transition systems",
    usage: [["deadlock(S)", "gives `true` with a trace when a reachable state has no enabled action."]],
    examples: [basic("let C = system(var x in 0..3; var y in 0..3; init x = 0 ∧ y = 0; action inc when x < 3 do x := x + 1; action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1)", "deadlock(C)")],
    see: ["eventually"],
  },
  {
    name: "replicas", area: "Transition systems",
    usage: [
      ["replicas(type; a, b, …; events…)", "runs a state-based CRDT on the replicas `a`, `b`, … through the events, and gives each replica's reading; its work says whether they converged."],
    ],
    details: [
      "The types: `gcounter` (`inc`), `pncounter` (`inc`, `dec`), `gset` (`add x`), `twopset` and `orset` (`add x`, `remove x`), and `lww` (`write v`, or `write v @ t` with a timestamp; by default the event's number).",
      "Events, one per line or separated by `;`: `a: inc` updates `a`; `a -> b` has `b` merge `a`'s state now; `m := a` sends a message holding `a`'s state now, and `b <- m` delivers it, later, again, or after newer ones.",
      "Every type is a vector of numbers merged by the entrywise maximum, which is proved a join (commutative, associative, idempotent), and every update only raises entries. So replicas that have received the same updates are in the same state, whatever the order, delays and duplicates.",
      "The drawing is a space-time diagram: a lane per replica, an arrow per message. Stepping through the work builds it event by event.",
    ],
    examples: [
      basic("replicas(gcounter; a, b, c; a: inc; b: inc; b: inc; a -> b; b -> c; c -> a)"),
      section("Delayed and duplicated messages", "replicas(gcounter; a, b; a: inc; m := a; a: inc; b <- m; b <- m)", "replicas(gcounter; a, b; a: inc; m := a; a: inc; b <- m; a -> b)"),
      section("Add and remove", "replicas(twopset; a, b; a: add x; a -> b; b: remove x; a: add x; b -> a)", "replicas(orset; a, b; a: add x; a -> b; b: remove x; a: add x; b -> a; a -> b)"),
      section("Last writer wins", "replicas(lww; a, b; a: write red @ 5; b: write blue @ 3; a -> b; b -> a)"),
    ],
    see: ["clocks", "system"],
  },
  {
    name: "rules", area: "Transition systems",
    usage: [["let R = rules(l -> r; …)", "declares a rewriting system: rules between terms, applied left to right."]],
    details: [
      "A term is a variable, a constant, or a symbol applied to terms: `add(s(x), y)`. Variables are `u`, `v`, `w`, `x`, `y` and `z`, perhaps with digits or primes (`x1`, `y'`); any other name (`0`, `e`, `nil`) is a constant.",
      "Rules go one per line or separated by `;`, and are named `r1`, `r2`, … in order, or by a name before a colon: `assoc: f(f(x, y), z) -> f(x, f(y, z))`.",
      "A rule's left side cannot be a variable, and its right side can only use the left side's variables, so a step never invents a term.",
    ],
    examples: [basic("let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))", "rewrite(A, add(s(s(0)), s(0)))")],
    see: ["rewrite", "terminates", "critical"],
  },
  {
    name: "rewrite", area: "Transition systems",
    usage: [["rewrite(R, t)", "rewrites the term `t` with the system's rules until none applies, and gives the normal form."]],
    details: [
      "Each step rewrites the leftmost-outermost redex: the first subterm, from the root and left to right, that is an instance of a rule's left side, with the first rule that matches. The work names the rule and marks the subterm.",
      "A term that has not reached a normal form after 10,000 steps, or has grown past 6000 symbols, is an error: the system may not terminate on it. `terminates` can show that it always does.",
    ],
    examples: [
      basic("let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))", "rewrite(A, add(s(s(0)), s(s(0))))"),
      section("A term with variables", "let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))", "rewrite(A, add(s(x), y))"),
    ],
    see: ["rules", "terminates"],
  },
  {
    name: "terminates", area: "Transition systems",
    usage: [
      ["terminates(R)", "checks that every rule makes the term smaller, so no term rewrites for ever."],
      ["terminates(R; f(x, y) = 2x + y + 1, …)", "checks the same with a linear interpretation of the symbols in place of the size."],
    ],
    details: [
      "An interpretation gives each symbol a value: a constant plus a coefficient, at least one, times each argument. A term is then worth a linear form in its variables, and a rule passes when its left side's form has a larger constant and no smaller coefficient than its right side's, so it is worth more whatever the variables are.",
      "When every rule passes, every step lowers a natural number, so no term rewrites for ever. This is proved; so is the converse for each rule: one that fails is worth no more on the right for some values of the variables. Failing does not show that the system loops: another interpretation may work.",
      "Symbols not given take the size: one, plus each argument.",
    ],
    examples: [
      basic("let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))", "terminates(A)", "terminates(A; add(x, y) = 2x + y, s(x) = x + 1)"),
      section("A rule that cannot pass", "let L = rules(f(x) -> f(f(x)))", "terminates(L)"),
    ],
    see: ["rewrite", "critical"],
  },
  {
    name: "critical", area: "Transition systems",
    usage: [["critical(R)", "finds where two rules overlap, and whether the two results of each overlap rewrite to the same normal form."]],
    details: [
      "A critical pair comes from a term where one rule applies at the root and another (or the same one, deeper) inside it; the two rewrites give the pair. Each side is rewritten to normal form: when every pair joins, the system is locally confluent, and if it also terminates, confluent (Newman's lemma), so every term has one normal form.",
      "A pair whose sides reach two different normal forms is a choice the rules leave open, and the system is not confluent; adding a rule between the two is the start of Knuth–Bendix completion. Sides that keep rewriting past the step limit without meeting leave the question undecided.",
      "The two rules' variables are renamed apart before they are unified, so `x'` in one rule and `x` in the other are different variables. The verdicts are proved in Lean (`CriticalProofs.lean`): unification finds an overlap whenever there is one, no overlap is missed, and every pair joining makes the system locally confluent (the critical pair lemma).",
    ],
    examples: [
      basic("let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))", "critical(A)"),
      section("A group's axioms", "let G = rules(f(e, x) -> x; f(i(x), x) -> e; f(f(x, y), z) -> f(x, f(y, z)))", "critical(G)"),
      section("Variables renamed apart", "let P = rules(f(g(x')) -> a; g(h(x)) -> b)", "critical(P)"),
    ],
    see: ["rules", "terminates"],
  },
  {
    name: "trace", area: "Transition systems",
    usage: [["trace(S; a, b, …)", "runs the actions in order from the initial state and gives the state reached, a step per action."]],
    details: [
      "The system must have one initial state; an action that is not enabled is an error naming the guard that fails.",
      "The graph of reachable states is drawn with the trace's transitions marked. Stepping through the work, or clicking a step, marks where that step is on the graph; the same holds for the traces `invariant`, `reach`, `deadlock` and `eventually` give.",
    ],
    examples: [basic("let C = system(var x in 0..3; var y in 0..3; init x = 0 ∧ y = 0; action inc when x < 3 do x := x + 1; action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1)", "trace(C; inc, inc, move)")],
    see: ["system", "invariant"],
  },
  {
    name: "ctl", area: "Transition systems",
    usage: [["ctl(S, EF φ)", "decides a CTL formula at the initial states: EF, AF, EG, AG, EX or AX applied to a state formula φ."]],
    details: [
      "EF and AF are least fixed points, EG and AG greatest ones, on the lattice of sets of reachable states; each round of the Kleene iteration is a step.",
      "A state with no successor has no path onward: it satisfies AF φ only where φ holds, and EG φ nowhere.",
    ],
    examples: [basic("let C = system(var x in 0..3; var y in 0..3; init x = 0 ∧ y = 0; action inc when x < 3 do x := x + 1; action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1)", "ctl(C, EF y = 3)", "ctl(C, AG x ≤ 2)", "ctl(C, AF y = 3)")],
    see: ["eventually", "lfp"],
  },
  {
    name: "eventually", area: "Transition systems",
    usage: [["eventually(S, φ)", "gives `true` when every fair run reaches φ, and otherwise a deadlock or a fair loop that avoids it forever."]],
    details: ["`fair action` is weak fairness: if it stays enabled it is taken. `strong fair action` is strong fairness: if it is enabled again and again it is taken.",
      "A run that keeps away from where a strongly fair action is enabled owes it nothing: below, `stay` forever never enables `fin`, so it is fair and never reaches `c`.",
      "Both answers are checked before they are given: a deadlock or a fair loop is re-run as a run of the system, and `true` comes with a ranking of the states that every fair run has to leave."],
    examples: [section("Weak and strong fairness", "let W = system(var p in {idle, crit}; var q in {wait, crit}; var lock in bool; init p = idle ∧ q = wait ∧ lock = false; action penter when p = idle ∧ lock = false do lock := true, p := crit; action pexit when p = crit do p := idle, lock := false; fair action qenter when q = wait ∧ lock = false do lock := true, q := crit)", "eventually(W, q = crit)", "let S = system(var p in {idle, crit}; var q in {wait, crit}; var lock in bool; init p = idle ∧ q = wait ∧ lock = false; action penter when p = idle ∧ lock = false do lock := true, p := crit; action pexit when p = crit do p := idle, lock := false; strong fair action qenter when q = wait ∧ lock = false do lock := true, q := crit)", "eventually(S, q = crit)"), section("Strong fairness asks nothing of a run that avoids the action", "let F = system(var p in {a, b, c}; init p = a; action stay when p = a do p := a; action go when p = a do p := b; action back when p = b do p := a; strong fair action fin when p = b do p := c)", "eventually(F, p = c)")],
    see: ["ctl", "deadlock"],
  },
  {
    name: "refines", area: "Transition systems",
    usage: [["refines(C, A; X := e, …)", "gives `true` when every step of `C`, mapped to `A`'s variables by the expressions, is a step of `A` or leaves the mapped state unchanged."]],
    examples: [basic("let Two = system(var a in 0..2; var b in 0..2; init a = 0 ∧ b = 0; action ta when a < 2 do a := a + 1; action tb when b < 2 do b := b + 1)", "let Sum = system(var s in 0..4; init s = 0; action t when s < 4 do s := s + 1)", "refines(Two, Sum; s := a + b)")],
    see: ["system"],
  },

  // --- Logic -----------------------------------------------------------------------------------
  {
    name: "connectives", title: "∧ ∨ ¬ → ↔", area: "Logic", notation: true,
    usage: [
      ["p ∧ q", "is p and q; type `&&`, `and` or `\\and`."], ["p ∨ q", "is p or q; type `||`, `or` or `\\or`."], ["¬p", "is not p; type `!`, `not` or `\\not`."],
      ["p → q", "is if p then q; type `->` or `\\to`."], ["p ↔ q", "is p if and only if q; type `<->` or `\\iff`."], ["⊤, ⊥", "are true and false; type `true` and `false`, or `\\top` and `\\bot`."],
    ],
    details: [
      "A formula with a connective is a logic cell: its value is the formula, and the commands on this page's see-also act on it.",
      "¬ binds tightest, then ∧, ∨, →, ↔; → and ↔ group to the right, ∧ and ∨ to the left.",
      "`let φ = p → q` names a formula for the cells after.",
    ],
    examples: [basic("p && q -> p", "let phi = p → q", "taut(phi ∨ (q → p))")],
    see: ["truthtable", "taut", "cnf", "forall"],
  },
  {
    name: "forall", title: "∀ ∃", area: "Logic", notation: true,
    usage: [["∀ x ∈ S, φ", "is true when φ holds for every x in the finite set S; type `forall x in S, …` or `\\forall x \\in S, …`."], ["∃ x ∈ S, φ", "is true when φ holds for some x in S; type `exists x in S, …` or `\\exists`."]],
    details: [
      "`S` is a range `1..10` or a set `{4, 6, 9}`; the body can compare numbers (`<`, `≤`, `=`, `≠`, `∣` for divides) and use `prime`, `even` and `odd`. `\\le`, `\\ge`, `\\ne` and `\\mid` type ≤, ≥, ≠ and ∣.",
      "The engine checks every element in order; the step names the counterexample of a false ∀ or the witness of a true ∃.",
    ],
    examples: [basic("∀ n ∈ 1..10, n^2 ≥ n", "∀ n ∈ 1..10, n^2 ≥ 2n", "∃ n ∈ {4, 6, 9, 11}, prime(n)"),
      section("Nested", "∀ n ∈ 2..30, ∃ p ∈ 2..n, prime(p) ∧ p ∣ n")],
    see: ["connectives"],
  },
  {
    name: "truthtable", area: "Logic",
    usage: [["truthtable(φ)", "draws the truth table of φ: a row for each assignment to its variables."]],
    details: ["Up to 8 variables (256 rows). The rows where φ is false are shaded."],
    examples: [basic("truthtable(p → q)", "truthtable((p → q) ∧ (q → r) → (p → r))")],
    see: ["taut", "sat", "equiv"],
    ref: "https://mathworld.wolfram.com/TruthTable.html",
  },
  {
    name: "taut", area: "Logic",
    usage: [["taut(φ)", "gives ⊤ when φ is true under every assignment, and otherwise ⊥; its work names a row that falsifies it."]],
    details: ["Decided by truth table, which is proved to decide (`taut_sound`)."],
    examples: [basic("taut(p ∧ q → p)", "taut(p → q)", "taut((p → q) ∨ (q → p))")],
    see: ["sat", "falsify", "truthtable"],
    ref: "https://mathworld.wolfram.com/Tautology.html",
  },
  {
    name: "sat", area: "Logic",
    usage: [["sat(φ)", "gives an assignment that makes φ true, as a map from each variable to its value (`{p ↦ true, q ↦ false}`), or ⊥ when there is none."]],
    details: [
      "`let w = sat(φ)` names the assignment as a formula, the conjunction of its literals (`p ∧ ¬q`), so `w` can be used in other formulas.",
      "As an exercise, any satisfiable formula that implies φ is an answer: an assignment written as a map, as the engine answers, or as a conjunction of literals.",
    ],
    examples: [basic("sat(p ∧ ¬q)", "sat((p ∨ q) ∧ ¬p)", "sat(p ∧ ¬p)")],
    see: ["falsify", "taut"],
  },
  {
    name: "falsify", area: "Logic",
    usage: [["falsify(φ)", "gives an assignment that makes φ false, as a map from each variable to its value, or ⊥ when φ is a tautology."]],
    details: ["`let w = falsify(φ)` names the assignment as the conjunction of its literals, as `sat` does."],
    examples: [basic("falsify(p → q)", "falsify(p ∨ ¬p)")],
    see: ["sat", "taut"],
  },
  {
    name: "equiv", area: "Logic",
    usage: [["equiv(φ, ψ)", "gives ⊤ when φ and ψ have the same value under every assignment, and otherwise ⊥; its work names a row where they differ."]],
    examples: [basic("equiv(p → q, ¬q → ¬p)", "equiv(p → q, q → p)", "equiv(¬(p ∧ q), ¬p ∨ ¬q)")],
    see: ["taut", "nnf"],
  },
  {
    name: "nnf", area: "Logic",
    usage: [["nnf(φ)", "gives φ in negation normal form: no → or ↔, and ¬ only on variables."]],
    details: ["Each law applied is a step: eliminating → and ↔, De Morgan's laws, double negation. Every step is proved to keep the value (`toNormal_sound`)."],
    examples: [basic("nnf(¬(p ∧ (q ∨ ¬r)))", "nnf(¬(p → q))")],
    see: ["cnf", "dnf", "equiv"],
  },
  {
    name: "cnf", area: "Logic",
    usage: [["cnf(φ)", "gives φ in conjunctive normal form: an ∧ of clauses, each an ∨ of literals."]],
    details: ["The negation normal form first, then ∨ distributed over ∧, one distribution a step."],
    examples: [basic("cnf(p ∨ (q ∧ r))", "cnf(p ↔ q)"), section("Exercises", note("As an exercise, an answer must be in CNF and equivalent; the truth table decides."), "cnf(¬(p → q))")],
    see: ["dnf", "nnf"],
    ref: "https://mathworld.wolfram.com/ConjunctiveNormalForm.html",
  },
  {
    name: "dnf", area: "Logic",
    usage: [["dnf(φ)", "gives φ in disjunctive normal form: an ∨ of terms, each an ∧ of literals."]],
    examples: [basic("dnf((p ∨ q) ∧ r)", "dnf(p ↔ q)")],
    see: ["cnf", "nnf"],
    ref: "https://mathworld.wolfram.com/DisjunctiveNormalForm.html",
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
      "A term with no normal form, such as `omega omega`, is refused rather than reduced forever: after 10,000 steps, or once it grows past 6000 symbols.",
      "A long reduction shows its first steps and its last, and one step between saying how many it leaves out.",
      "A definition with no normal form, such as `fact := Y F`, is bound as written, so recursion through `Y` works.",
      "A binder may carry a type, `λx:A. e`; reduction ignores it, and `type:` checks it.",
      "A cell can start with a command: a strategy (`cbv:`, `cbn:`, `applicative:`, `normal 5:`), `eta:`, `fv:`, `db:`, `alpha:`, `subst:`, `type:` or `infer:`.",
    ],
    examples: [
      basic("(λx. x) y", "(λx. λy. x) a b"),
      section("Scope", note("Capture is avoided:"), "(λx. λy. x y) y", note("Definitions:"), "TWO := succ (succ zero)", "add TWO 3"),
    ],
    see: ["church", "cbv", "fv", "type"],
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
    details: [
      "A cell that starts with one of these names (or a λ-definition of your own) is a λ-term when it reads as one: names, numerals and parentheses only. `S + 1` is arithmetic on a variable `S`.",
    ],
    examples: [basic("if (iszero 0) a b", "fst (pair 1 2)", "mul 2 3")],
    see: ["lambda"],
  },
  {
    name: "normal", title: "normal: (normal order)", area: "λ-calculus", notation: true,
    usage: [["normal: t", "reduces `t` in normal order, the leftmost-outermost redex first, to its normal form."], ["normal n: t", "takes at most `n` steps and shows where they lead."]],
    details: [
      "A plain λ-cell reduces in normal order too; the command names the strategy, and the step count lets a term with no normal form be watched for a few steps.",
      "Normal order finds a normal form whenever the term has one (the standardization theorem), even when an argument it never uses has none.",
    ],
    examples: [basic("normal: K I (omega omega)", "normal 3: omega omega", "normal 4: Y f")],
    see: ["cbn", "cbv", "applicative", "eta"],
  },
  {
    name: "cbn", title: "cbn: (call by name)", area: "λ-calculus", notation: true,
    usage: [["cbn: t", "reduces `t` by name: the leftmost-outermost redex, never under a λ, the argument passed unevaluated."], ["cbn n: t", "takes at most `n` steps."]],
    details: [
      "It stops at a weak head normal form: a λ, or a variable applied to arguments. Redexes under a λ or in those arguments are left alone, and the reading says so.",
      "An argument that is never used is never evaluated, so `K I (omega omega)` gives `I`.",
    ],
    examples: [basic("cbn: K I (omega omega)", "cbn: λx. (λy. y) x", "cbn: x ((λy. y) z)")],
    see: ["cbv", "normal", "applicative"],
  },
  {
    name: "cbv", title: "cbv: (call by value)", area: "λ-calculus", notation: true,
    usage: [["cbv: t", "reduces `t` by value: the function and then the argument become values before the call, never under a λ."], ["cbv n: t", "takes at most `n` steps."]],
    details: [
      "A value is a λ or a variable (Plotkin's call by value). The result is a value, which may still have redexes under its λs.",
      "Every argument is evaluated, used or not, so `K I (omega omega)` runs forever: the cell is refused after 10,000 steps. `cbv 5:` shows the first five.",
      "Most programming languages call by value.",
    ],
    examples: [basic("cbv: (λx. x) ((λy. y) z)", "cbv 4: K I (omega omega)", "cbv: (λx. x) (λy. (λz. z) y)")],
    see: ["cbn", "normal", "applicative"],
  },
  {
    name: "applicative", title: "applicative: (applicative order)", area: "λ-calculus", notation: true,
    usage: [["applicative: t", "reduces `t` in applicative order, the leftmost-innermost redex first, under λ too, to its normal form."], ["applicative n: t", "takes at most `n` steps."]],
    details: ["It is call by value that also reduces under λ. Like call by value it evaluates arguments it then throws away, so it can miss a normal form that normal order finds."],
    examples: [basic("applicative: (λx. a) ((λy. y) b)", "applicative 3: K I (omega omega)")],
    see: ["normal", "cbv"],
  },
  {
    name: "eta", title: "eta: (β and η)", area: "λ-calculus", notation: true,
    usage: [["eta: t", "reduces `t` with β and η, leftmost-outermost, to its βη-normal form."], ["eta n: t", "takes at most `n` steps."]],
    details: [
      "η contracts `λx. f x` to `f` when `x` is not free in `f`: both give `f a` for every `a`, so a function is determined by what it does (extensionality).",
      "The side condition matters: `λx. x x` is not `x`.",
    ],
    examples: [basic("eta: λx. f x", "eta: λf. λx. f x", "eta: λx. x x", "eta: λx. (λy. g y) x")],
    see: ["normal", "alpha"],
  },
  {
    name: "fv", title: "fv: (free variables)", area: "λ-calculus", notation: true,
    usage: [["fv: t", "gives the set of variables free in `t`, and names the bound ones."]],
    details: [
      "An occurrence is bound when a λ above it has its name, and free otherwise; the same name can be both in one term.",
      "Names are not unfolded: in `fv: K`, `K` is just a variable. A term with no free variables is closed, a combinator.",
    ],
    examples: [basic("fv: λx. x y", "fv: λx. x y (λy. y z)", "fv: (λx. x) x", "fv: λf. λx. f x")],
    see: ["db", "alpha", "lambda-subst"],
  },
  {
    name: "db", title: "db: (de Bruijn indices)", area: "λ-calculus", notation: true,
    usage: [["db: t", "writes `t` with de Bruijn indices: each bound variable becomes the number of λs between it and its binder."]],
    details: [
      "The nearest binder is 0. A free variable keeps its name.",
      "Bound names are gone, so two terms are α-equivalent exactly when their de Bruijn forms are equal. View › de Bruijn indices shows every λ-cell this way.",
    ],
    examples: [basic("db: λx. x", "db: λx. λy. x", "db: λx. λy. x (λz. z y)", "db: λx. x y")],
    see: ["alpha", "fv"],
  },
  {
    name: "alpha", title: "alpha: (α-equivalence)", area: "λ-calculus", notation: true,
    usage: [["alpha: s, t", "gives ⊤ when `s` and `t` differ only in the names of bound variables, and ⊥ otherwise."]],
    details: ["The terms are compared by their de Bruijn forms, which the steps show. Free variables count: `λx. y` and `λx. z` are different functions."],
    examples: [basic("alpha: λx. λy. x y, λa. λb. a b", "alpha: λx. λy. x y, λa. λb. b a", "alpha: λx. y, λy. y")],
    see: ["db", "fv"],
  },
  {
    name: "lambda-subst", title: "subst: (λ-terms)", area: "λ-calculus", notation: true,
    usage: [["subst: e, x := s", "gives `e[x := s]`: every free `x` in `e` replaced by `s`, renaming binders so no free variable of `s` is captured."]],
    details: [
      "An `x` under a binder named `x` is bound, and stays.",
      "If `s` has a free `y` and the replacement lands under a `λy`, that binder is renamed first (an α-step), so the `y` stays free.",
      "This is the substitution a β-step does: `(λx. e) s` becomes `e[x := s]`.",
    ],
    examples: [basic("subst: x y, x := λz. z", "subst: λx. x, x := y", "subst: λy. x y, x := y")],
    see: ["fv", "lambda"],
  },
  {
    name: "type", title: "type: (simply typed)", area: "λ-calculus", notation: true,
    usage: [
      ["type: t", "gives the simple type of `t`, whose every binder has one (`λx:A. e`), with its derivation tree."],
      ["type: x : A, f : A → B ⊢ t", "types `t` in a context that gives its free variables types."],
    ],
    details: [
      "Types are base names (`A`, `Nat`) and arrows; `A → B → C` is `A → (B → C)`. Type `->` for → and `|-` for ⊢.",
      "Three rules: Var looks a variable up in the context; →I types `λx:A. e` as `A → B` when `e` has type `B` with `x : A` added; →E types `f a` as `B` when `f : A → B` and `a : A`.",
      "The steps are the rules, premises first, and the tree draws them. A term without a type is refused with the reason. The checker is proved sound: every tree it draws is a derivation.",
    ],
    examples: [
      basic("type: λx:A. x", "type: λf:A→B. λx:A. f x", "type: f : A → B, x : A ⊢ f x"),
      section("Errors", "type: λx:A. x x", "type: λx. x", "type: λx:A. λy:B → B. y x"),
    ],
    see: ["infer"],
  },
  {
    name: "infer", title: "infer: (type inference)", area: "λ-calculus", notation: true,
    usage: [
      ["infer: t", "finds the most general simple type of `t`, whose binders need no types."],
      ["infer: Γ ⊢ t", "infers in a context; a free variable not in it gets a type too."],
    ],
    details: [
      "Each binder without a type and each application gets a type variable (τ₁, τ₂, …), and each application `f a` gives an equation: `f`'s type is an arrow from `a`'s type to the result's.",
      "The equations are solved one at a time by unification. The occurs check refuses `τ = τ → σ`, which is why `λx. x x` and `Y` have no simple type.",
      "The variables left are named α, β, …; any types put for them give a type of the term. The answer is checked by the type checker on the annotated term, and the tree shows that derivation.",
      "Church library names are unfolded first, so `infer: S` works.",
    ],
    examples: [
      basic("infer: λx. x", "infer: K", "infer: S", "infer: λf. λx. f (f x)"),
      section("No simple type", "infer: λx. x x", "infer: Y"),
      section("With some types given", "infer: λf:A→B. λx. f x", "infer: f x"),
    ],
    see: ["type"],
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
