import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import katex from "katex";
import { read, write, toLatex, show, sameStmt, atomsInSpan, letHead, hasNotation } from "../dist/index.js";

const root = new URL("../../../", import.meta.url);
const golden = readFileSync(new URL("engine/Tests/golden.tsv", root), "utf8").split("\n").filter(Boolean).map((l) => l.split("\t"));
/** The bundled notebooks: notebooks/*.chalk and the courses' lessons, notebooks/courses/<course>/*.chalk. */
const chalkFiles = () => [
  ...readdirSync(new URL("notebooks/", root)).filter((f) => f.endsWith(".chalk")),
  ...readdirSync(new URL("notebooks/courses/", root)).flatMap((c) => readdirSync(new URL(`notebooks/courses/${c}/`, root)).filter((f) => f.endsWith(".chalk")).map((f) => `courses/${c}/${f}`)),
];
/** A cell the engine reads as notation: a math cell, or an exercise's question (a Lean exercise's is Lean). */
const mathCell = (c) => !c.type || c.type === "math" || (c.type === "exercise" && !c.lean);
/** Every math cell of the bundled notebooks, in order, with the functions defined above it. */
const notebookCells = chalkFiles().flatMap((f) => {
  const known = [];
  return JSON.parse(readFileSync(new URL(`notebooks/${f}`, root), "utf8")).cells.filter(mathCell).map((c) => {
    const cell = { file: f, src: c.src, known: [...known] };
    const r = read(c.src, known);
    if (r.ok && letHead(r.stmt)?.params) known.push(letHead(r.stmt).name);
    return cell;
  });
});
const corpus = [...golden.map(([src]) => ({ file: "golden.tsv", src, known: [] })), ...notebookCells];

const tree = (src, known) => { const r = read(src, known); assert.ok(r.ok, `${src}: ${r.ok ? "" : r.error.message}`); return r.stmt; };
const shape = (src, known = []) => show(tree(src, known).body);

test("the tree is the engine's parse: precedence, implicit products, what the numerator takes", () => {
  const cases = {
    "2x/3": "[(frac [2 x] [3])]",
    "x/2y": "[(frac [x] [2]) y]",
    "8/2/2": "[(frac [(frac [8] [2])] [2])]",
    "a/(b/c)": "[(frac [a] [(frac [b] [c])])]",
    "-2^2": "[- 2 (^ [2])]",
    "(-2)^2": "[(paren [- 2]) (^ [2])]",
    "2^3^2": "[2 (^ [3 (^ [2])])]",
    "x^-1": "[x (^ [- 1])]",
    "x^(1/2)": "[x (^ [(frac [1] [2])])]",
    "(x+1)/(x-1)": "[(frac [x + 1] [x - 1])]",
    "2(a/b)": "[2 (frac [a] [b])]",
    "(a/b)^2": "[(paren [(frac [a] [b])]) (^ [2])]",
    "-a/b": "[(frac [- a] [b])]",
    "a - b - c": "[a - b - c]",
    "x y": "[x ␣ y]",
    "xy": "[x y]",
    "2 x": "[2 x]",
    "x 2": "[x ␣ 2]",
    "sin^2(y)": "[(sin [y]) (^ [2])]",
    "sin^2(y)^3": "[(paren [(sin [y]) (^ [2])]) (^ [3])]",
    "%": "[%]", "%%": "[% %]", "%2": "[% 2]", "% 2": "[% ␣ 2]",
    "diff(x^2, x, 2)": "[(diff [x (^ [2])] [x] [2])]",
    "integrate(x, x, 0, 1)": "[(integrate [x] [x] [0] [1])]",
    "[1,2;3,4]": "[(matrix [1] [2] ; [3] [4])]",
    "2.5x + .5": "[2 . 5 x + . 5]",
    "x_1 + π": "[x _ 1 + π]",
    // the entrywise operators are one atom each, and a product's precedence: `/` after one takes it all
    "[1,2] ./ [3,10]": "[(matrix [1] [2]) ./ (matrix [3] [1 0])]",
    "a.*b": "[a .* b]",
    "2./3": "[2 ./ 3]",
    "a ./ b/c": "[(frac [a ./ b] [c])]",
  };
  for (const [src, want] of Object.entries(cases)) assert.equal(shape(src), want, src);
  // a name followed by `(` is a call only when it is a function
  assert.equal(shape("f(x)"), "[f (paren [x])]");
  assert.equal(shape("f(x)", ["f"]), "[(f [x])]");
  const s = tree("let g(a, b) = a*b + g(a, 1)");
  assert.deepEqual(letHead(s), { name: "g", params: ["a", "b"] });
  assert.equal(show(s.body), "[(let [g] [a] [b]) a * b + (g [a] [1])]");
});

/** A golden source the engine reads in another world (logic, relations and posets), not as notation. */
const otherWorld = (src) => /[∧∨¬→↔⊤⊥∀∃]|->|&&|\|\|/.test(src) || /^\s*(forall|exists)\b/.test(src)
  || /^\s*(let\s+\w+\s*=\s*)?(truthtable|taut|sat|falsify|equiv|nnf|cnf|dnf|poset|divisors|subsets|chain|map|hasse|join|meet|sup|inf|upper|lower|lattice|top|bottom|le|maximal|minimal|monotone|lfp|gfp|fixpoints|rel|kernel|reflexive|symmetric|antisymmetric|transitive|equivalence|preorder|closure|classes|finer|wellfounded|measure|op|joinop|meetop|table|associative|commutative|idempotent|semilattice|identity|fold|order|distributive|complement|complemented|boolean|product|galois|closureop|context|concepts|secure|events|clocks|concurrent|system|states|invariant|inductive|reach|deadlock|trace|ctl|eventually|refines)\s*\(/.test(src);

test("parse errors are the engine's, with its spans", () => {
  for (const [src, answer] of golden) {
    const m = /^<error: (.*)>$/.exec(answer);
    const r = read(src);
    const parseError = m && /^(unexpected|expected|ragged|bad number)/.test(m[1]);
    if (otherWorld(src)) continue;
    if (parseError) assert.equal(r.ok ? "(read)" : r.error.message, m[1], src);
    else assert.ok(r.ok, `${src}: ${r.ok ? "" : r.error.message}`);
  }
  const bad = read("x + )");
  assert.deepEqual(bad.ok ? null : bad.error, { message: "unexpected ')'", span: { start: 4, end: 5 } });
  // λ-terms and the other worlds are not this grammar: those cells stay raw
  for (const src of ["(λx. x) y", "TWO := succ (succ zero)", "poset({a,b}; a<b)", "p ∧ q → p", "∀ n ∈ 1..10, n^2 ≥ n", "rel({a, b}; a->b)"]) assert.equal(read(src).ok, false, src);
  // a quoted name outside a part is the engine's lexer error
  const q = read('x "a"');
  assert.deepEqual(q.ok ? null : q.error, { message: "unexpected character '\"'", span: { start: 2, end: 3 } });
  const brace = read("{1, 2}");
  assert.equal(brace.ok ? "(read)" : brace.error.message, "braces list the indices of a part, as in m[[{1, 3}]]");
  // the statistics are calls, as in the engine, not products
  const mean = read("mean(x)");
  assert.ok(mean.ok && JSON.stringify(mean.stmt).includes('"k":"call"'), JSON.stringify(mean));
});

test("writing puts back exactly the parentheses the engine needs", () => {
  const cases = {
    "2(a/b)": "2(a/b)", "(a+b)/(c+d)": "(a + b)/(c + d)", "x^(2n)": "x^(2n)", "x^(1/2)": "x^(1/2)",
    "a/(b/c)": "a/(b/c)", "-(a/b)": "-(a/b)", "a - (b/c)": "a - b/c", "((a+b))/c": "(a + b)/c",
    "x sin(y)": "x sin(y)", "sin^2(y)": "sin(y)^2", "x^n y": "x^n y", "% 2": "% 2", "(a/b)(c/d)": "a/b(c/d)",
    "a*b/c": "a*b/c", "a*(b/c)": "a*(b/c)", "x/(2y)": "x/(2y)", "x/(y)": "x/y", "1/x^2": "1/x^2",
    "let f(x, y) = x/y": "let f(x, y) = x/y", "[1, 2; 3, 4]": "[1, 2; 3, 4]", "diff(x^2,x)": "diff(x^2, x)",
  };
  for (const [src, want] of Object.entries(cases)) assert.equal(write(tree(src)).text, want, src);
  // spans: each atom's text, for showing an engine error where it happened
  const t = tree("1 + x/y");
  const w = write(t);
  const frac = t.body[2];
  assert.equal(w.text, "1 + x/y");
  assert.deepEqual(w.spans.get(frac), { start: 4, end: 7 });
  assert.equal(w.holes, 0);
  assert.equal(write({ body: [{ k: "frac", num: [], den: [{ k: "ch", c: "2" }] }] }).holes, 1);
});

test("read ∘ write is the identity on every golden source and notebook cell", () => {
  let n = 0;
  for (const { file, src, known } of corpus) {
    const r = read(src, known);
    if (!r.ok) continue;
    n++;
    const text = write(r.stmt).text;
    const again = read(text, known);
    assert.ok(again.ok, `${file}: ${src} → ${text}: ${again.ok ? "" : again.error.message}`);
    assert.ok(sameStmt(r.stmt, again.stmt), `${file}: ${src} → ${text}\n  ${show(r.stmt.body)}\n  ${show(again.stmt.body)}`);
    assert.equal(write(again.stmt).text, text, `${file}: ${src}`);
  }
  // all but the order-theory and λ cells, and `import("…")`, which stay raw
  assert.ok(n >= 250, `only ${n} cells read`);
});

test("every notation is LaTeX KaTeX renders, with every atom tagged", () => {
  let id = 0;
  const wrap = (_atoms, s) => `\\htmlData{a=${id++}}{${s}}`;
  for (const { src, known } of corpus) {
    const r = read(src, known);
    if (!r.ok) continue;
    for (const opts of [{}, { wrap }]) {
      const latex = toLatex(r.stmt, opts);
      assert.doesNotThrow(() => katex.renderToString(latex, { throwOnError: true, strict: false, trust: (c) => c.command === "\\htmlData" }), `${src}: ${latex}`);
    }
  }
  const tex = (src) => toLatex(tree(src));
  assert.equal(tex("diff(x^2, x)"), "\\frac{d}{d{x}}\\htmlData{pg=1}{\\htmlData{pd=o}{(}{x}^{2}\\htmlData{pd=c}{)}}");
  assert.equal(tex("integrate(f, x, 0, 1)"), "\\int_{0}^{1} {f} \\, d{x}");
  assert.equal(tex("sum(k^2, k, 1, 10)"), "\\sum_{{k}=1}^{10} {k}^{2}");
  assert.equal(tex("det([a,b;c,d])"), "\\begin{vmatrix}{a} & {b} \\\\ {c} & {d}\\end{vmatrix}");
  assert.equal(tex("transpose(M) + conj(z)"), "{{M}}^{\\mathsf{T}}+\\overline{{z}}");
  assert.equal(tex("dot(u, v + w)"), "{u} \\cdot \\htmlData{pg=1}{\\htmlData{pd=o}{(}{v}+{w}\\htmlData{pd=c}{)}}");
  assert.equal(tex("2 llama + x_1"), "2{\\mathit{llama}}+{x_{1}}");
  // a fixed output reference is a %ₙ chip; a relative one stays % or %% (it follows the outputs),
  // in a chip of its own, with the output it means now (when the host says) faint beside it
  assert.equal(tex("%3 + %"), "\\htmlData{out=n3}{\\%_{3}}+\\htmlData{out=p1, rel=1}{\\%}");
  assert.equal(toLatex(tree("%%"), { outRef: (r) => (r === "%%" ? { label: 5 } : null) }), "\\htmlData{out=p2, rel=1}{\\%\\%_{\\htmlData{now=1}{5}}}");
  // while the cell is edited, or before it has run: an arrow to the output a run now would use
  assert.equal(toLatex(tree("%"), { outRef: () => ({ label: 22, pending: true }) }), "\\htmlData{out=p1, rel=1}{\\%_{\\htmlData{next=1}{\\to 22}}}");
  assert.equal(tex("norm(v) + abs(x) + sqrt(2)"), "\\htmlData{pg=1, pk=norm}{\\htmlData{pd=o}{\\lVert }{v}\\htmlData{pd=c}{\\rVert }}+\\htmlData{pg=1, pk=abs}{\\htmlData{pd=o}{\\lvert }{x}\\htmlData{pd=c}{\\rvert }}+\\sqrt{2}");
});

test("an engine span maps to the innermost atoms it covers", () => {
  const t = tree("1 + x/y + sqrt(z)");
  const at = (start, end) => atomsInSpan(t, { start, end }).map((a) => show([a])).join(" ");
  assert.equal(at(4, 5), "[x]");                       // inside the fraction: just the x
  assert.equal(at(4, 7), "[(frac [x] [y])]");          // the whole fraction: the fraction
  assert.equal(at(10, 17), "[(sqrt [z])]");
  assert.equal(at(10, 14), "[(sqrt [z])]");            // the name of a call is the call
  assert.equal(at(17, 17), "[(sqrt [z])]");            // the end of the input: the last atom
});

test("tokens carry the host's highlight classes, with binders' variables and parameters bound", () => {
  const seen = [];
  const classify = (text, as) => { seen.push(`${as}:${text}`); return as === "name" ? null : as; };
  const latex = toLatex(tree("let f(x) = diff(x^2 + y, x) + rref(M) + 2"), { classify });
  assert.deepEqual(seen.sort(), ["bound:x", "bound:x", "bound:x", "call:rref", "keyword:let", "name:M", "name:f", "name:y", "num:2", "num:2"]);
  // a call's name is a word in the text face, against its parentheses
  assert.match(latex, /\\htmlData\{hl=call\}\{\\htmlData\{word=1\}\{\\mathrm\{rref\}\}\}\{\\htmlData\{pg=c\}\{\\htmlData\{pd=o\}\{\(\}/);
  assert.doesNotThrow(() => katex.renderToString(latex, { throwOnError: true, strict: false, trust: (c) => c.command === "\\htmlData" }));
});

test("notation is what the text cannot show: fractions, powers, matrices, d/dx, ∫, Σ, √, bars", () => {
  const has = (src) => hasNotation(tree(src).body);
  for (const src of ["1/2", "x^2", "[1,2]", "diff(f, x)", "sqrt(2)", "abs(x)", "rref([1,2;3,4])", "N(1/3)"]) assert.equal(has(src), true, src);
  for (const src of ["epicycles(llama, 60)", "x + 1", "N(pi)", "rref(M)", "subst(f, x, 3)", "let f = g", "diff"]) assert.equal(has(src), false, src);
});

test("fractions keep full size when nested, script size in exponents and bounds; Re, Im, sgn are words", () => {
  const tex = (src) => toLatex(tree(src));
  // N(80000/3 / (250/(300/7))): the first two levels full size, each padded so the bars nest
  assert.equal(tex("(a/b)/(c/d)"), "\\dfrac{\\,\\dfrac{\\,{a}\\,}{\\,{b}\\,}\\,}{\\,\\dfrac{\\,{c}\\,}{\\,{d}\\,}\\,}");
  // deeper levels shrink gently, to 70% at the deepest
  const deep = tex("a/(b/(c/(d/(e/f))))");
  assert.match(deep, /\\small \{c\}/);
  assert.match(deep, /\\footnotesize \{d\}/);
  assert.match(deep, /\\scriptsize \{f\}/);
  // an open group's paren is drawn faint where it would go
  assert.match(toLatex({ body: [{ k: "paren", body: [], open: true }] }), /\\htmlData\{pd=c, open=1\}\{\)\}/);
  assert.equal(tex("x^(1/2)"), "{x}^{\\frac{1}{2}}");
  assert.match(tex("integrate(x, x, 0, 1/2)"), /\^\{\\frac\{1\}\{2\}\}/);
  // a word in an exponent, or in a fraction that has shrunk, shrinks with it
  assert.match(tex("x^sin(t)"), /word=s/);
  assert.match(tex("a/(b/(c/sin(t)))"), /word=s/);
  assert.match(tex("a/(b/sin(t))"), /word=1/);
  assert.match(tex("sign(sin(t))"), /^\\htmlData\{call=1\}\{\\htmlData\{word=1\}\{\\mathrm\{sgn\}\}\{\\htmlData\{pg=c\}\{\\htmlData\{pd=o\}\{\(\}\\htmlData\{call=1\}\{\\htmlData\{word=1\}\{\\mathrm\{sin\}\}/);
});

test("a part reads as a part atom, its indices kept as typed, and writes back the same", () => {
  for (const src of ['planets[[All, "mass"]]', 'mean(t[[All, {"mass", "period"}]])', "m[[2, 1;;-1;;2]]^2", "f(x)[[1]][[2]]", "[1, 2; 3, 4][[-1]]", 'x[["a,b", 2]]']) {
    const r = read(src);
    assert.ok(r.ok, src);
    assert.equal(write(r.stmt).text, src, src);
  }
  const r = read("m[[2, 1;;3]]^2");
  assert.deepEqual(r.stmt.body.map((a) => a.k), ["ch", "part", "sup"]);
  const open = read("m[[1");
  assert.equal(open.ok ? "(read)" : open.error.message, "expected ']]' to close the part");
});

test("text in quotes and attached files read as atoms of their own and write back the same", () => {
  const known = ["import", "samplePoints", "dimensions"];
  for (const src of ['import("https://example.org/a/b.csv")', "samplePoints(⟦llama.svg⟧, 100)", 'dimensions(import("x.csv")[[All, 2;;]])', 'let t = import("data/planets.csv")']) {
    const r = read(src, known);
    assert.ok(r.ok, src);
    assert.equal(write(r.stmt).text, src, src);
  }
  const call = read('import("a/b.csv")', known).stmt.body[0];
  assert.equal(call.k, "call");
  assert.deepEqual(call.args[0].map((a) => a.k), ["str"]);   // the URL's slashes are text, not fractions
  assert.deepEqual(read("⟦a.svg⟧").stmt.body, [{ k: "asset", name: "a.svg" }]);
});

test("the entrywise operators write back spaced, and draw as ⊘ and ⊙", () => {
  for (const [src, want] of [["2./3", "2 ./ 3"], ["a.*b", "a .* b"], ["a ./ -b", "a ./ -b"], ["a ./ (b/c)", "a ./ (b/c)"], ["[1,2] ./ [3,10]", "[1, 2] ./ [3, 10]"]]) {
    assert.equal(write(tree(src)).text, want, src);
    assert.ok(sameStmt(tree(write(tree(src)).text), tree(src)), src);
  }
  assert.match(toLatex(tree("a ./ b")), /\\oslash/);
  assert.match(toLatex(tree("a .* b")), /\\odot/);
});
