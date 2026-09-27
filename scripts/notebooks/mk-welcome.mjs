// node scripts/notebooks/mk-welcome.mjs
// Generates notebooks/welcome.chalk: the notebook a first-time visitor sees. A short tour — how to
// run a cell, see its work and ask where a piece of an answer came from — then one section per
// area, each with a few cells to run and change. The inputs are the Reference tab's examples.
// Inline code is written ‹like this› (template literals cannot hold backticks).
import { writeFileSync } from "node:fs";

const cells = [];
const sec = (title) => cells.push({ src: title, type: "section", showWork: false, label: null });
const md = (text) => cells.push({ src: text.replace(/‹|›/g, "`").trim(), type: "markdown", showWork: false, label: null });
const m = (src, showWork = false) => cells.push({ src, showWork, label: null });
const r = String.raw;

sec("Welcome to ChalkMath");
md(r`
ChalkMath is a notebook for mathematics that **shows its work**. Type an expression into a cell and press **Enter**: the answer comes back with every step that produced it, each named and explained the way a textbook would.

Everything runs in your browser. Nothing you type is sent to a server, and your notebooks are kept in this browser until you export them.
`);
m("diff(x^2 * sin(x), x)", true);
md(r`
That is the product rule, then the power rule, each a step you can read. A few things to try:

- **Show or hide the steps** with the ‹Work› button beside a cell (it appears when you hover), or View › Show all work.
- **Click any part of an answer**, a single term or a whole fraction, and the panel below says which rule produced it and traces it back through the steps.
- **Change a cell** and press Enter again. The cells below keep their answers until you run them.
- Press **Enter in the empty cell at the bottom** to start your own work.
`);

sec("Algebra");
m("expand((x+1)^3)", true);
m("factor(x^2 + 2*x)");
m("subst(x^2 + 1, x, 3)");
md(r`
Arithmetic is exact: fractions stay fractions and roots stay roots. ‹N(…)› gives a decimal when you want one.
`);
m("sqrt(8) + sqrt(18)");
m("N(sqrt(2))");

sec("Names and functions");
md(r`
‹let› names a value or defines a function for the rest of the notebook. ‹%› is the previous answer.
`);
m("let f = x^3 - 3x");
m("diff(f, x, 2)");
m("let sq(x) = x^2 + 1");
m("diff(sq(x), x)");
m("diff(%, x)");

sec("Calculus");
m("diff(sin(x^2), x)", true);
md(r`
‹integrate› finds an antiderivative and then **checks** it: it differentiates its own answer and only replies if that gives your function back. With bounds it is the definite integral.
`);
m("integrate(x^2 + sin(x), x)", true);
m("integrate(cos(t)*sin(t), t, 0, 2pi)");
m("sum(k^2, k, 1, 10)");

sec("Linear algebra");
md(r`
Matrices are written row by row: commas between entries, semicolons between rows. ‹rref› records each row operation as its own step.
`);
m("rref([1,2,3;4,5,6;7,8,10])", true);
m("det([a,b;c,d])");
m("dot([1,2,3],[4,5,6])");

sec("Plots");
m("plot([sin(x), cos(x)], x, 0, 2pi)");
m("plot([x^2, diff(x^2, x)], x, -3, 3)");

sec("Complex numbers");
m("ℯ^(pi*i)");
m("(1+i)*(2-i)");
m("abs(3+4i)");

sec("A little further");
md(r`
The same engine draws Fourier series as spinning circles, reasons about finite orders, and reduces λ-terms one step at a time.
`);
m("epicycles(exp(i*t) + 1/2*exp(-3i*t), t)");
m("let D = divisors(12)");
m("join(D, 4, 6)");
m("add 2 3");

sec("Where to next");
md(r`
- **Reference** (the tab at the top) lists every command, with examples you can click to run.
- **File › Examples** opens longer notebooks: drawing a llama with Fourier series, and a course on orders and lattices.
- **Help › Keyboard shortcuts** lists the keys. Type ‹\pi›, ‹\lam› or another ‹\›-name for a symbol, and **Tab** completes a command.
- **File › Save** keeps a notebook in this browser. **Export to file** and **Copy link to notebook** are for sharing.
`);

writeFileSync(new URL("../../notebooks/welcome.chalk", import.meta.url), JSON.stringify({ chalk: 1, name: "welcome.chalk", cells, scenes: [] }, null, 2) + "\n");
console.log(`notebooks/welcome.chalk: ${cells.length} cells`);
