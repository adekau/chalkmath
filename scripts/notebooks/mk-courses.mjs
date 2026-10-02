// node scripts/notebooks/mk-courses.mjs
// Generates the courses: notebooks/courses/<course>/<nn-lesson>.chalk and notebooks/courses.json, the
// list of projects the Courses tab shows (the courses, then the example notebooks as a collection).
// A lesson is short: a goal, worked examples to step through, a slider where a picture moves, and
// exercises the engine checks by normal form. Every cell is checked against the engine by
// `drive.mjs --check` (notebooks/golden/), so a lesson cannot quietly stop working.
// Inline code is written ‹like this› (template literals cannot hold backticks).
import { writeFileSync, mkdirSync } from "node:fs";

const r = String.raw;
const code = (text) => text.replace(/‹([^‹›\n]*)›/g, "`$1`").trim();

/** A lesson being written: its cells, added in order. */
function lesson() {
  const cells = [];
  return {
    cells,
    sec: (title) => cells.push({ src: title, type: "section", showWork: false, label: null }),
    md: (text) => cells.push({ src: code(text), type: "markdown", showWork: false, label: null }),
    /** A math cell. `work`: show the steps; `step`: step through them from that many; `slider`: [min, max, step]. */
    m: (src, o = {}) => cells.push({
      src, showWork: !!(o.work || o.step !== undefined), label: null,
      ...(o.step !== undefined ? { stepwise: o.step } : {}),
      ...(o.slider ? { slider: { min: o.slider[0], max: o.slider[1], step: o.slider[2] }, mode: "raw" } : {}),
    }),
    /** An exercise: the question (its value is the answer), the prompt, the hints. */
    ex: (question, prompt, hints = [], o = {}) => cells.push({
      src: question, type: "exercise", prompt: code(prompt), ...(hints.length ? { hints: hints.map(code) } : {}),
      ...(o.hide ? { hideQuestion: true } : {}), showWork: false, label: null,
    }),
    /** A Lean cell. */
    lean: (src) => cells.push({ src, type: "lean", showWork: false, label: null }),
    /** A Lean exercise: the statement (ending `:= by`), the prompt, the author's proof (required: CI checks
     *  it), the hints, and `o.start`, the proof the reader starts from (`sorry` if absent). */
    lx: (statement, prompt, proof, hints = [], o = {}) => cells.push({
      src: statement, type: "exercise", lean: true, prompt: code(prompt), leanSolution: proof,
      ...(o.start ? { leanStart: o.start } : {}), ...(hints.length ? { hints: hints.map(code) } : {}), showWork: false, label: null,
    }),
  };
}

const courses = [];
/** A course: its lessons are written by `build`, one call of `add(file, title, blurb, write)` each.
 *  `o.leanPrelude`: each lesson's Lean sees the Lean of the lessons before it. */
function course(id, title, blurb, level, build, o = {}) {
  const lessons = [];
  build((file, ltitle, lblurb, write) => {
    const L = lesson();
    write(L);
    lessons.push({ file, title: ltitle, blurb: lblurb, cells: L.cells });
  });
  courses.push({ id, title, blurb, level, lessons, ...(o.leanPrelude ? { leanPrelude: true } : {}) });
}

// ---------------------------------------------------------------------------------------------------
course("calculus", "Calculus: derivatives and integrals",
  "The rules of differentiation, the chain rule and tangent lines; then antiderivatives the engine checks by differentiating, definite integrals and Riemann sums.",
  "Calculus I–II", (add) => {

  add("01-rules.chalk", "The rules of differentiation", "Powers, sums, constant multiples and products: four rules, every step named.", ({ sec, md, m, ex }) => {
    sec("The rules of differentiation");
    md(r`
> [!goal]
> Differentiate polynomials and products with four rules, and read every step the engine takes.

‹diff(f, x)› is the derivative of $f$ with respect to $x$. The engine does not look the answer up: it applies one rule at a time, and each rule is a step you can read, with a dot that says whether the rule is proved in Lean.
`);
    md(r`
> [!definition] Derivative
> The derivative of $f$ at $x$ is $f'(x) = \lim_{h \to 0} \dfrac{f(x + h) - f(x)}{h}$, the slope of the graph there. The rules below are consequences of this definition, so they can be applied without taking a limit each time.
`);
    sec("Powers, sums and constants");
    md(r`
> [!theorem] Power, sum and constant-multiple rules
> $\dfrac{d}{dx} x^n = n x^{n-1}$, $\quad (f + g)' = f' + g'$, $\quad (c f)' = c f'$, and a constant has derivative $0$.
`);
    m("diff(x^5, x)", { work: true });
    md(r`A polynomial takes all four. Step through it: before each ‹▸ Next step›, say which rule comes next.`);
    m("diff(3x^4 - 2x + 7, x)", { step: 0 });
    ex("diff(x^4 - 5x^2 + 2, x)", r`Differentiate $x^4 - 5x^2 + 2$.`, [
      r`Differentiate term by term: the sum rule.`,
      r`Each term: $\frac{d}{dx}\, a x^n = a n x^{n-1}$, and the constant $2$ has derivative $0$.`,
    ]);
    sec("Products");
    md(r`
> [!theorem] Product rule
> $(fg)' = f'g + fg'$: differentiate one factor at a time and add.
`);
    m("diff(x^2 * sin(x), x)", { step: 0 });
    md(r`
> [!mistake]
> The derivative of a product is **not** the product of the derivatives. Here is $f' \cdot g'$ for the same $f = x^2$ and $g = \sin x$, which is not the answer above:
`);
    m("diff(x^2, x) * diff(sin(x), x)");
    ex("diff(x^3 * cos(x), x)", r`Differentiate $x^3 \cos x$.`, [
      r`It is a product: $f = x^3$ and $g = \cos x$.`,
      r`$f' = 3x^2$ and $g' = -\sin x$; now $f'g + fg'$.`,
    ]);
    ex("diff(exp(x) * cos(x), x)", r`Differentiate $e^x \cos x$. (Type $e^x$ as ‹exp(x)›.)`, [
      r`$(e^x)' = e^x$: the exponential is its own derivative.`,
      r`Any correct form is accepted: $e^x \cos x - e^x \sin x$ and $e^x(\cos x - \sin x)$ reduce to the same normal form.`,
    ]);
    md(r`
> [!summary]
> Four rules differentiate every polynomial and every product of functions you know: power, sum, constant multiple, product. The next lesson adds the fifth, for functions inside functions.
`);
  });

  add("02-chain-rule.chalk", "The chain rule", "Functions of functions: the outer derivative times the inner one, with a slider to watch the inner factor.", ({ sec, md, m, ex }) => {
    sec("The chain rule");
    md(r`
> [!goal]
> Differentiate a function of a function, such as $\sin(x^2)$ or $e^{3x}$, and see where the inner derivative goes.
`);
    md(r`
> [!theorem] Chain rule
> $\dfrac{d}{dx} f(g(x)) = f'(g(x))\, g'(x)$: the outer derivative, evaluated at the inner function, times the inner derivative.
`);
    m("diff(sin(x^2), x)", { step: 0 });
    m("diff(exp(3x), x)", { work: true });
    sec("The inner derivative comes out in front");
    md(r`
> [!try]
> Drag ‹a›. The derivative of $\sin(ax)$ is $a\cos(ax)$: the inner derivative $a$ is a factor in front, so the derivative's curve is $a$ times taller and the slopes are $a$ times steeper.
`);
    m("let a = 2", { slider: [1, 6, 1] });
    m("diff(sin(a*x), x)");
    m("plot([sin(a*x), diff(sin(a*x), x)], x, 0, 6.28)");
    sec("Chains inside chains");
    md(r`A power of a sum is a chain too: the outer function is $u^5$, the inner $2x + 1$.`);
    m("diff((2x + 1)^5, x)", { step: 0 });
    m("diff(ln(x^2 + 1), x)", { work: true });
    ex("diff(cos(x^3), x)", r`Differentiate $\cos(x^3)$.`, [
      r`The outer function is $\cos u$, the inner $u = x^3$.`,
      r`$(\cos u)' = -\sin u$ and $(x^3)' = 3x^2$.`,
    ]);
    ex("diff(exp(x^2), x)", r`Differentiate $e^{x^2}$. (Type it as ‹exp(x^2)›.)`, [
      r`The outer function is $e^u$, whose derivative is itself.`,
    ]);
    ex("diff((x^2 + 1)^3, x)", r`Differentiate $(x^2 + 1)^3$.`, [
      r`The outer function is $u^3$, the inner $u = x^2 + 1$.`,
      r`Factored or multiplied out, either form is right: the check compares normal forms.`,
    ]);
    md(r`
> [!summary]
> Peel the function from the outside in: differentiate the outer layer, keep the inside as it is, and multiply by the derivative of the inside.
`);
  });

  add("03-tangent-lines.chalk", "Higher derivatives and tangent lines", "Derivatives of derivatives, slopes at a point, and the tangent line that follows a slider.", ({ sec, md, m, ex }) => {
    sec("Higher derivatives and tangent lines");
    md(r`
> [!goal]
> Take second derivatives, find the slope of a curve at a point, and draw the tangent line there.
`);
    m("let f = x^3 - 3x");
    m("diff(f, x)");
    md(r`‹diff(f, x, 2)› differentiates twice: the second derivative, which measures how the slope itself changes.`);
    m("diff(f, x, 2)", { work: true });
    sec("Slope at a point");
    md(r`The slope at one point is the derivative with a number put in for $x$: ‹subst(e, x, v)› substitutes.`);
    m("subst(diff(f, x), x, 2)", { work: true });
    sec("The tangent line");
    md(r`
> [!definition] Tangent line
> The tangent line to $y = f(x)$ at $x = a$ is $y = f(a) + f'(a)\,(x - a)$: the line through the point with the curve's slope there.
`);
    m("let a = 2", { slider: [-2, 2, 1] });
    m("let s = subst(diff(f, x), x, a)");
    m("let t = subst(f, x, a) + s*(x - a)");
    m("plot([f, t], x, -2.5, 2.5)");
    md(r`
> [!try]
> Drag ‹a›. At which points is the tangent flat? There $f'(a) = 3a^2 - 3 = 0$, so $a = \pm 1$: the top of the hump and the bottom of the dip.
`);
    ex("subst(diff(x^2, x), x, 3)", r`What is the slope of $y = x^2$ at $x = 3$?`, [
      r`The slope is the derivative, $2x$, at $x = 3$.`,
    ], { hide: true });
    ex("diff(x^4, x, 2)", r`Find the second derivative of $x^4$.`, [
      r`Differentiate twice: $x^4 \to 4x^3 \to \dots$`,
    ]);
    ex("subst(diff(f, x, 2), x, 1)", r`For the $f$ above, what is $f''(1)$?`, [
      r`$f''(x) = 6x$ (the cell above shows it).`,
    ], { hide: true });
    md(r`
> [!summary]
> The derivative at a point is a number, the slope there; the tangent line is the straight line with that slope through the point. Where the slope is zero the curve turns.
`);
  });

  add("04-antiderivatives.chalk", "Antiderivatives, checked", "Integration as the search for a function whose derivative you know, accepted only after the engine differentiates it back.", ({ sec, md, m, ex }) => {
    sec("Antiderivatives, checked");
    md(r`
> [!goal]
> Find antiderivatives, including by substitution and by parts, and see why every answer the engine gives is checked.
`);
    md(r`
> [!definition] Antiderivative
> $F$ is an antiderivative of $f$ when $F' = f$. Any two differ by a constant, so the engine gives one and leaves out the $+\,C$.
`);
    md(r`‹integrate(f, x)› searches for an antiderivative with a few textbook rules. The search proves nothing, so its steps are marked **checked** (a hollow dot): the answer is accepted only when the engine differentiates it and gets $f$ back. Open the work to see the guess and the check.`);
    m("integrate(x^3, x)", { work: true });
    m("integrate(3x^2 + 2x + 1, x)");
    sec("Substitution");
    md(r`
> [!theorem] Substitution
> $\int f(g(x))\, g'(x)\, dx = F(g(x))$ where $F' = f$: the chain rule, read backwards.
`);
    m("integrate(2x*cos(x^2), x)", { work: true });
    sec("By parts");
    md(r`
> [!theorem] Integration by parts
> $\int u\, dv = uv - \int v\, du$: the product rule, read backwards.
`);
    m("integrate(x*exp(x), x)", { work: true });
    md(r`Check it yourself: differentiate the answer, and the integrand comes back.`);
    m("diff(x*exp(x) - exp(x), x)");
    md(r`
> [!mistake]
> An antiderivative is not unique: $x^4$ and $x^4 + 1$ both have derivative $4x^3$. The exercises compare answers exactly, so give them **without** the $+\,C$.
`);
    ex("integrate(4x^3, x)", r`Find an antiderivative of $4x^3$.`, [r`Which power has derivative $4x^3$?`]);
    ex("integrate(cos(3x), x)", r`Find an antiderivative of $\cos 3x$.`, [
      r`$\sin 3x$ is close: its derivative is $3\cos 3x$.`,
      r`Divide by the inner derivative $3$.`,
    ]);
    ex("integrate(2x*exp(x^2), x)", r`Find an antiderivative of $2x\,e^{x^2}$.`, [r`Substitute $u = x^2$: then $du = 2x\,dx$.`]);
    ex("integrate(x*cos(x), x)", r`Find an antiderivative of $x \cos x$.`, [
      r`By parts, with $u = x$ and $dv = \cos x\,dx$.`,
      r`$uv - \int v\,du = x \sin x - \int \sin x\,dx$.`,
    ]);
    md(r`
> [!summary]
> Integration is guessing; differentiation is checking. Substitution undoes the chain rule and parts undoes the product rule.
`);
  });

  add("05-definite-integrals.chalk", "Definite integrals and sums", "The fundamental theorem of calculus, finite sums, and Riemann sums that close in on the area as a slider adds rectangles.", ({ sec, md, m, ex }) => {
    sec("Definite integrals and sums");
    md(r`
> [!goal]
> Evaluate definite integrals with the fundamental theorem, compute finite sums, and watch Riemann sums approach an integral.
`);
    md(r`
> [!theorem] Fundamental theorem of calculus
> If $F' = f$ on $[a, b]$, then $\displaystyle\int_a^b f(x)\,dx = F(b) - F(a)$.
`);
    md(r`‹integrate(f, x, a, b)› finds a checked antiderivative, then evaluates it at the bounds. Step through it.`);
    m("integrate(x^2, x, 0, 1)", { step: 0 });
    m("integrate(sin(x), x, 0, pi)");
    sec("Sums");
    md(r`‹sum(f, k, a, b)› adds $f$ for $k = a, a + 1, \dots, b$.`);
    m("sum(k, k, 1, 10)");
    m("sum(k^2, k, 1, 5)", { work: true });
    sec("Riemann sums");
    md(r`
> [!definition] Right Riemann sum
> Cut $[0, 1]$ into $n$ strips of width $\frac1n$ and stand a rectangle of height $f(\frac kn)$ on the $k$-th: the area of the rectangles is $\displaystyle\sum_{k=1}^{n} f\!\left(\tfrac kn\right) \tfrac1n$.
`);
    m("let n = 10", { slider: [1, 60, 1] });
    m("let R = sum((k/n)^2 / n, k, 1, n)");
    m("N(R)");
    md(r`
> [!try]
> Drag ‹n›. The sum is an exact fraction for every $n$, and its decimal closes in on $\int_0^1 x^2\,dx = \frac13 \approx 0.333$ from above: the rectangles stand above the curve.
`);
    ex("integrate(x, x, 0, 2)", r`Evaluate $\displaystyle\int_0^2 x\,dx$.`, [r`An antiderivative is $\frac{x^2}{2}$; evaluate at $2$ and at $0$.`]);
    ex("integrate(x^2, x, 1, 3)", r`Evaluate $\displaystyle\int_1^3 x^2\,dx$.`, [r`$F(x) = \frac{x^3}{3}$; the answer is $F(3) - F(1)$.`]);
    ex("sum(2k - 1, k, 1, 6)", r`Add the first six odd numbers, $1 + 3 + 5 + \dots + 11$.`, [
      r`Try $1$, then $1 + 3$, then $1 + 3 + 5$: what do the totals have in common?`,
    ], { hide: true });
    md(r`
> [!summary]
> A definite integral is a difference of antiderivative values, and the limit of Riemann sums: the same number reached two ways.
`);
  });
});

// ---------------------------------------------------------------------------------------------------
course("linear-algebra", "Linear algebra: vectors, matrices and systems",
  "Vectors and the dot product, matrix arithmetic, solving systems by row reduction with verified row operations, and determinants.",
  "Linear algebra", (add) => {

  add("01-vectors.chalk", "Vectors and the dot product", "Adding and scaling vectors, lengths, and the dot product that measures angles.", ({ sec, md, m, ex }) => {
    sec("Vectors and the dot product");
    md(r`
> [!goal]
> Add and scale vectors, find lengths, and use the dot product to tell when two vectors are perpendicular.
`);
    md(r`A vector is a list of numbers in brackets, ‹[1, 2, 3]›. Vectors add and scale entry by entry.`);
    m("let u = [1, 2, 3]");
    m("let v = [4, -1, 2]");
    m("u + v", { work: true });
    m("2u");
    sec("The dot product");
    md(r`
> [!definition] Dot product and length
> $u \cdot v = \sum_i u_i v_i$, and the length of $v$ is $\lVert v \rVert = \sqrt{v \cdot v}$.
`);
    m("dot(u, v)", { step: 0 });
    m("norm([3, 4])", { work: true });
    m("norm(u)");
    md(r`
> [!theorem] Angle
> $u \cdot v = \lVert u \rVert\, \lVert v \rVert \cos\theta$, where $\theta$ is the angle between them. So $u \cdot v = 0$ exactly when $u$ and $v$ are perpendicular.
`);
    m("dot([1, 2], [2, -1])");
    ex("dot([1, 2, 3], [4, 5, 6])", r`Compute $(1, 2, 3) \cdot (4, 5, 6)$.`, [r`Multiply entry by entry and add: $1 \cdot 4 + 2 \cdot 5 + 3 \cdot 6$.`]);
    ex("norm([6, 8])", r`How long is the vector $(6, 8)$?`, [r`$\sqrt{6^2 + 8^2}$.`], { hide: true });
    ex("dot([2, 3], [3, -2])", r`Compute $(2, 3) \cdot (3, -2)$. What does the answer say about the two vectors?`, [r`Zero means perpendicular.`]);
    md(r`
> [!summary]
> Vectors add and scale entrywise; the dot product turns two vectors into a number that is zero exactly when they are perpendicular.
`);
  });

  add("02-matrices.chalk", "Matrices", "Matrix arithmetic, the product that is not commutative, the transpose, and a matrix acting on a vector.", ({ sec, md, m, ex }) => {
    sec("Matrices");
    md(r`
> [!goal]
> Multiply matrices, see that the order matters, transpose, and apply a matrix to a vector.
`);
    md(r`Rows are separated by ‹;›: ‹[1, 2; 3, 4]› is the $2 \times 2$ matrix with first row $1, 2$.`);
    m("let A = [1, 2; 3, 4]");
    m("let B = [0, 1; 1, 0]");
    md(r`
> [!definition] Matrix product
> The entry in row $i$, column $j$ of $AB$ is the dot product of row $i$ of $A$ with column $j$ of $B$.
`);
    m("A*B", { work: true });
    md(r`
> [!mistake]
> Matrix multiplication is not commutative: $AB$ and $BA$ are different matrices. Here $B$ swaps: on the right of $A$ it swaps $A$'s columns, on the left its rows.
`);
    m("B*A");
    m("transpose(A)", { work: true });
    sec("A matrix acting on a vector");
    md(r`A column vector is a matrix with one column, ‹[1; 1]›. $A$ sends it to the sum of $A$'s columns.`);
    m("A*[1; 1]");
    ex("[1, 2; 3, 4]*[0, 1; 1, 0]", r`Multiply.`, [r`Row $i$ of the first times column $j$ of the second.`, r`The answer is a matrix: type it as ‹[a, b; c, d]›.`]);
    ex("[2, 0; 1, 3]*[1; 2]", r`Apply the matrix to the vector.`, [r`The first entry is $2 \cdot 1 + 0 \cdot 2$.`, r`The answer is a column: ‹[a; b]›.`]);
    ex("transpose([1, 2, 3; 4, 5, 6])", r`Transpose the $2 \times 3$ matrix.`, [r`Rows become columns: the answer is $3 \times 2$.`]);
    md(r`
> [!summary]
> A matrix product is a table of dot products, and its order matters; a matrix times a vector is a combination of the matrix's columns.
`);
  });

  add("03-systems.chalk", "Solving systems by row reduction", "An augmented matrix, the three row operations (each proved to keep the solutions), and reading the answer off the reduced form.", ({ sec, md, m, ex }) => {
    sec("Solving systems by row reduction");
    md(r`
> [!goal]
> Solve a system of linear equations by reducing its augmented matrix, and read each row operation.
`);
    md(r`The system $x + 2y = 5,\ 3x + 4y = 6$ is the augmented matrix ‹[1, 2, 5; 3, 4, 6]›: one row per equation, the right-hand sides in the last column.`);
    md(r`
> [!theorem] Row operations keep the solutions
> Swapping two rows, scaling a row by a nonzero number, and adding a multiple of one row to another do not change the solution set. Each of the three is proved in Lean (the green dots), and so is the claim that the result is in reduced row echelon form.
`);
    m("rref([1, 2, 5; 3, 4, 6])", { work: true });
    md(r`Read it off: the first row says $x = -4$, the second $y = \frac92$.`);
    sec("Three equations");
    m("rref([2, 1, -1, 8; -3, -1, 2, -11; -2, 1, 2, -3])", { work: true });
    md(r`
> [!try]
> Check the solution $x = 2,\ y = 3,\ z = -1$: put it into the first equation, $2x + y - z$.
`);
    m("subst(subst(subst(2x + y - z, x, 2), y, 3), z, -1)");
    ex("rref([1, 1, 3; 1, -1, 1])", r`Solve $x + y = 3,\ x - y = 1$ by reducing the augmented matrix. Give the reduced matrix.`, [
      r`The augmented matrix is ‹[1, 1, 3; 1, -1, 1]›.`,
      r`Subtract the first row from the second, then scale.`,
    ], { hide: true });
    ex("rref([2, 4, 6; 1, 3, 4])", r`Reduce the augmented matrix of $2x + 4y = 6,\ x + 3y = 4$.`, [
      r`Scale the first row by $\frac12$ first.`,
    ], { hide: true });
    md(r`
> [!summary]
> Row reduction is elimination written on the matrix: three operations, none of which changes the solutions, until each variable stands alone in its row.
`);
  });

  add("04-determinants.chalk", "Determinants", "The determinant of 2×2 and 3×3 matrices, the product rule, and what a zero determinant means.", ({ sec, md, m, ex }) => {
    sec("Determinants");
    md(r`
> [!goal]
> Compute determinants, see that the determinant of a product is the product of determinants, and recognise a matrix with no inverse.
`);
    md(r`
> [!definition] Determinant of a $2 \times 2$ matrix
> $\det \begin{pmatrix} a & b \\ c & d \end{pmatrix} = ad - bc$: the signed area of the parallelogram the columns span.
`);
    m("let A = [1, 2; 3, 4]");
    m("det(A)", { step: 0 });
    m("det([2, 1, 0; 1, 3, 1; 0, 1, 2])");
    sec("Products");
    md(r`
> [!theorem] Determinant of a product
> $\det(AB) = \det A \cdot \det B$.
`);
    m("let B = [0, 1; 1, 0]");
    m("det(A*B)");
    m("det(A)*det(B)");
    sec("When the determinant is zero");
    md(r`
> [!theorem] Invertibility
> A square matrix has an inverse exactly when its determinant is not zero. A zero determinant means the columns lie on one line (or plane): the area they span is flat.
`);
    m("det([1, 2; 2, 4])");
    m("rref([1, 2; 2, 4])", { work: true });
    md(r`The reduced form has a row of zeros: the second column is twice the first.`);
    ex("det([2, 1; 5, 3])", r`Compute the determinant.`, [r`$ad - bc$ with $a = 2,\ b = 1,\ c = 5,\ d = 3$.`]);
    ex("det([3, 6; 1, 2])", r`Compute the determinant. Is the matrix invertible?`, [r`Is one column a multiple of the other?`]);
    ex("det([1, 0, 0; 0, 2, 0; 0, 0, 3])", r`Compute the determinant of this diagonal matrix.`, [r`For a diagonal matrix it is the product of the diagonal.`]);
    md(r`
> [!summary]
> The determinant is a single number that measures how a matrix scales area; it multiplies across products, and it is zero exactly when the matrix cannot be undone.
`);
  });
});

// ---------------------------------------------------------------------------------------------------
course("lambda", "λ-calculus: computing by reduction",
  "Terms, β-reduction in normal order and why substitution must avoid capture; then numbers, arithmetic and booleans built from functions alone.",
  "Logic and computation", (add) => {

  add("01-beta-reduction.chalk", "β-reduction", "Applying a function by substituting its argument, one redex at a time, and the renaming that keeps substitution honest.", ({ sec, md, m, ex }) => {
    sec("β-reduction");
    md(r`
> [!goal]
> Reduce λ-terms to normal form by β-reduction, and see why substitution must rename bound variables.
`);
    md(r`
> [!definition] Terms and β-reduction
> A term is a variable $x$, a function $\lambda x.\, M$, or an application $M\ N$. A **redex** is a function applied to an argument, $(\lambda x.\, M)\ N$, and β-reduction replaces it by $M[x := N]$: the body with the argument put in for the parameter.
`);
    md(r`Type λ as ‹\lam› then space (or a backslash). The engine reduces in **normal order**: always the leftmost, outermost redex first.`);
    m("(λx. x) y", { work: true });
    m("(λx. x x) (λy. y)", { step: 0 });
    m("(λx. λy. x) a b", { work: true });
    sec("Normal forms");
    md(r`
> [!definition] Normal form
> A term with no redex left is in **normal form**. Two terms are equal as programs when they reduce to the same normal form, up to the names of bound variables ($\lambda x.\, x$ and $\lambda y.\, y$ are the same function).
`);
    md(r`The exercises use exactly this: your answer and the question are both reduced, and compared by their normal forms. So any name for a bound variable is right.`);
    ex("(λx. λy. y x) a (λz. z)", r`Reduce to normal form.`, [r`The first redex puts $a$ for $x$: $(\lambda y.\, y\ a)\ (\lambda z.\, z)$.`]);
    ex("(λx. x x) (λy. y)", r`Reduce to normal form. Any name for the bound variable will do.`, [r`$x$ is replaced by $\lambda y.\, y$ twice: $(\lambda y.\, y)(\lambda y.\, y)$.`]);
    sec("Capture");
    md(r`
> [!mistake]
> Substituting blindly can **capture** a variable. In $(\lambda x.\, \lambda y.\, x)\ y$, putting $y$ for $x$ naively gives $\lambda y.\, y$, the identity, but the $y$ that was passed in is free, not the parameter. The engine renames the binder first (an α-step) and gets $\lambda y'.\, y$, the function that ignores its argument and returns $y$.
`);
    m("(λx. λy. x) y", { work: true });
    ex("(λx. λy. x) y", r`Reduce $(\lambda x.\, \lambda y.\, x)\ y$ to normal form. (The trap: $\lambda y.\, y$ is wrong.)`, [
      r`Rename the inner binder first, say to $z$: $\lambda x.\, \lambda z.\, x$.`,
    ], { hide: true });
    md(r`
> [!summary]
> Computation in the λ-calculus is substitution: find the leftmost outermost redex, put the argument in for the parameter, renaming binders that would capture, and repeat until nothing is left to reduce.
`);
  });

  add("02-church-numerals.chalk", "Church numerals and booleans", "Numbers as repeated application, arithmetic as composition, and booleans as choice.", ({ sec, md, m, ex }) => {
    sec("Church numerals and booleans");
    md(r`
> [!goal]
> Represent numbers and truth values as functions, and compute with them by reduction alone.
`);
    md(r`
> [!definition] Church numerals
> The number $n$ is the function that applies $f$ to $x$ $n$ times: $0 = \lambda f.\, \lambda x.\, x$, $1 = \lambda f.\, \lambda x.\, f\ x$, $2 = \lambda f.\, \lambda x.\, f\,(f\ x)$, and so on.
`);
    md(r`The engine knows the numerals and a small library (‹succ›, ‹add›, ‹mul›, ‹pow›, ‹true›, ‹false›, ‹not›, ‹and›, ‹or›, ‹if›, ‹iszero›, ‹pair›, ‹fst›, ‹snd›). It unfolds the names first, in one δ-step, then reduces, and reads a numeral back when the result is one.`);
    m("succ 2", { step: 0 });
    m("add 2 3", { work: true });
    m("mul 2 3");
    sec("Your own definitions");
    md(r`‹name := term› defines a term for the rest of the notebook.`);
    m("twice := λf. λx. f (f x)");
    m("twice twice g z", { work: true });
    sec("Booleans");
    md(r`
> [!definition] Church booleans
> $\mathsf{true} = \lambda t.\, \lambda f.\, t$ and $\mathsf{false} = \lambda t.\, \lambda f.\, f$: a boolean chooses one of two things. Then $\mathsf{if}\ b\ x\ y$ is just $b\ x\ y$.
`);
    m("and true false");
    m("if true a b");
    ex("succ 1", r`Reduce $\mathsf{succ}\ 1$. Write the numeral out as a λ-term (or by its name).`, [r`$\mathsf{succ}$ adds one more application of $f$.`]);
    ex("mul 2 2", r`Reduce $\mathsf{mul}\ 2\ 2$ to a numeral.`, [r`$2 \cdot 2 = 4$: four applications of $f$.`]);
    ex("not true", r`Reduce $\mathsf{not}\ \mathsf{true}$.`, [r`The answer is a boolean: which one chooses its second argument?`]);
    md(r`
> [!summary]
> With nothing but functions and substitution you get numbers, arithmetic and logic: the λ-calculus computes everything a computer can.
`);
  });
});

// ---------------------------------------------------------------------------------------------------
const manifest = {
  projects: [
    ...courses.map((c) => ({ id: c.id, title: c.title, blurb: c.blurb, kind: "course", level: c.level, path: `courses/${c.id}`,
      ...(c.leanPrelude ? { leanPrelude: true } : {}),
      lessons: c.lessons.map((l) => ({ file: l.file, title: l.title, blurb: l.blurb })) })),
    { id: "explorations", title: "Explorations", kind: "collection", path: "",
      blurb: "Notebooks that show what ChalkMath does: a tour, Fourier series drawing a llama, and order theory with its proofs in Lean.",
      lessons: [
        { file: "welcome.chalk", title: "Welcome to ChalkMath", blurb: "A short tour: running cells, reading the steps, and one example from each area." },
        { file: "llamas.chalk", title: "Drawing llamas with circles", blurb: "Fourier series from inner products to epicycles, ending with a llama drawn by spinning circles." },
        { file: "order-lattices.chalk", title: "Order and lattices", blurb: "Part I of From Zero to Propagators: partial orders, joins and meets, monotone maps and fixed points, with the proofs in Lean cells." },
      ] },
  ],
};
for (const c of courses) {
  const dir = new URL(`../../notebooks/courses/${c.id}/`, import.meta.url);
  mkdirSync(dir, { recursive: true });
  for (const l of c.lessons) {
    writeFileSync(new URL(l.file, dir), JSON.stringify({ chalk: 1, name: l.file, cells: l.cells, scenes: [] }, null, 2) + "\n");
  }
  console.log(`notebooks/courses/${c.id}: ${c.lessons.length} lessons, ${c.lessons.reduce((n, l) => n + l.cells.filter((x) => x.type === "exercise").length, 0)} exercises`);
}
writeFileSync(new URL("../../notebooks/courses.json", import.meta.url), JSON.stringify(manifest, null, 2) + "\n");
console.log(`notebooks/courses.json: ${manifest.projects.length} projects`);
