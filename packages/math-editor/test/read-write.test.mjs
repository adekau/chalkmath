import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import katex from "katex";
import { read, write, toLatex, show, sameStmt, atomsInSpan, letHead } from "../dist/index.js";

const root = new URL("../../../", import.meta.url);
const golden = readFileSync(new URL("engine/Tests/golden.tsv", root), "utf8").split("\n").filter(Boolean).map((l) => l.split("\t"));
/** Every math cell of the bundled notebooks, in order, with the functions defined above it. */
const notebookCells = readdirSync(new URL("notebooks/", root)).filter((f) => f.endsWith(".chalk")).flatMap((f) => {
  const known = [];
  return JSON.parse(readFileSync(new URL(`notebooks/${f}`, root), "utf8")).cells.filter((c) => !c.type || c.type === "math").map((c) => {
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
  };
  for (const [src, want] of Object.entries(cases)) assert.equal(shape(src), want, src);
  // a name followed by `(` is a call only when it is a function
  assert.equal(shape("f(x)"), "[f (paren [x])]");
  assert.equal(shape("f(x)", ["f"]), "[(f [x])]");
  const s = tree("let g(a, b) = a*b + g(a, 1)");
  assert.deepEqual(letHead(s), { name: "g", params: ["a", "b"] });
  assert.equal(show(s.body), "[(let [g] [a] [b]) a * b + (g [a] [1])]");
});

test("parse errors are the engine's, with its spans", () => {
  for (const [src, answer] of golden) {
    const m = /^<error: (.*)>$/.exec(answer);
    const r = read(src);
    const parseError = m && /^(unexpected|expected|ragged|bad number)/.test(m[1]);
    if (parseError) assert.equal(r.ok ? "(read)" : r.error.message, m[1], src);
    else assert.ok(r.ok, `${src}: ${r.ok ? "" : r.error.message}`);
  }
  const bad = read("x + )");
  assert.deepEqual(bad.ok ? null : bad.error, { message: "unexpected ')'", span: { start: 4, end: 5 } });
  // λ-terms and the other worlds are not this grammar: those cells stay raw
  for (const src of ["(λx. x) y", "TWO := succ (succ zero)", "poset({a,b}; a<b)", "import(\"a.svg\")", "⟦llama.svg⟧"]) assert.equal(read(src).ok, false, src);
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
  assert.equal(tex("diff(x^2, x)"), "\\frac{d}{d{x}}\\left({x}^{2}\\right)");
  assert.equal(tex("integrate(f, x, 0, 1)"), "\\int_{0}^{1} {f} \\, d{x}");
  assert.equal(tex("sum(k^2, k, 1, 10)"), "\\sum_{{k}=1}^{10} {k}^{2}");
  assert.equal(tex("det([a,b;c,d])"), "\\begin{vmatrix}{a} & {b} \\\\ {c} & {d}\\end{vmatrix}");
  assert.equal(tex("transpose(M) + conj(z)"), "{{M}}^{\\mathsf{T}}+\\overline{{z}}");
  assert.equal(tex("dot(u, v + w)"), "{u} \\cdot \\left({v}+{w}\\right)");
  assert.equal(tex("2 llama + x_1"), "2{\\mathit{llama}}+{x_{1}}");
  // output references are Out[n] chips; a relative one needs the host to say which output it is
  assert.equal(tex("%3 + %"), "\\htmlData{out=n3}{\\mathrm{Out}[3]}+\\htmlData{out=p1}{\\mathrm{Out}[\\%]}");
  assert.equal(toLatex(tree("%%"), { outRef: (r) => (r === "%%" ? 5 : null) }), "\\htmlData{out=p2}{\\mathrm{Out}[5]}");
  assert.equal(tex("norm(v) + abs(x) + sqrt(2)"), "\\left\\lVert {v}\\right\\rVert+\\left|{x}\\right|+\\sqrt{2}");
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
