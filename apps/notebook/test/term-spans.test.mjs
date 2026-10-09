// Where a reading's subterms were written (src/term-spans.ts), and whether a reading is the input
// itself. The readings here are the engine's, as the page has them: each tagged subterm's path and
// the text KaTeX shows for it. The module is TypeScript for the page, so it is bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-term-spans-"));
const out = await build({ entryPoints: [new URL("../src/term-spans.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "node" });
writeFileSync(join(dir, "term-spans.mjs"), out.outputFiles[0].text);
const T = await import(pathToFileURL(join(dir, "term-spans.mjs")).href);

/** A reading from its leaves (path → text) and its other tagged paths. */
const reading = (leaves, inner = []) => [...inner.map((path) => ({ path, text: "" })), ...Object.entries(leaves).map(([path, text]) => ({ path, text }))];
const text = (src, span) => (span ? Array.from(src).slice(span.start, span.end).join("") : null);

test("a subterm spans what was written for it: an operator's operands, a call, a group", () => {
  // taut(p and q implies r): ∧ binds tighter than →
  const src = "taut(p and q implies r)";
  const { spans, faithful } = T.termSpans(src, [{ path: "root", text: "taut(p∧q→r)" }, ...reading({ "0.0.0": "p", "0.0.1": "q", "0.1": "r" }, ["0", "0.0"])]);
  assert.equal(faithful, true);
  assert.equal(text(src, spans.get("0.0").inner), "p and q");
  assert.equal(text(src, spans.get("0").inner), "p and q implies r");
  assert.equal(text(src, spans.get("root").inner), src);

  const paren = "taut((p and q) implies r)";
  const g = T.termSpans(paren, reading({ "0.0.0": "p", "0.0.1": "q", "0.1": "r" }, ["root", "0", "0.0"])).spans.get("0.0");
  assert.equal(text(paren, g.inner), "p and q");
  assert.equal(text(paren, g.outer), "(p and q)");

  // a call is its name and arguments; `not p` is the `not` and its operand
  const d = "diff(x^2*sin(x), x)";
  const ds = T.termSpans(d, reading({ "0.0.0": "x", "0.0.1": "2", "0.1.0": "x", "1": "x" }, ["root", "0", "0.0", "0.1"])).spans;
  assert.equal(text(d, ds.get("0.1").inner), "sin(x)");
  assert.equal(text(d, ds.get("0").inner), "x^2*sin(x)");
  const n = "taut(not p or q)";
  assert.equal(text(n, T.termSpans(n, reading({ "0.0.0": "p", "0.1": "q" }, ["root", "0", "0.0"])).spans.get("0.0").inner), "not p");
});

test("deleting a subterm takes the operator or comma joining it to its neighbour", () => {
  const src = "taut(p and q implies r)";
  const { spans } = T.termSpans(src, reading({ "0.0.0": "p", "0.0.1": "q", "0.1": "r" }, ["root", "0", "0.0"]));
  assert.equal(T.deleteTerm(src, spans, "0.0.1"), "taut(p implies r)");
  assert.equal(T.deleteTerm(src, spans, "0.0"), "taut(r)");
  const d = "diff(x^2*sin(x), x)";
  const ds = T.termSpans(d, reading({ "0.0.0": "x", "0.0.1": "2", "0.1.0": "x", "1": "x" }, ["root", "0", "0.0", "0.1"])).spans;
  assert.equal(T.deleteTerm(d, ds, "0.1"), "diff(x^2, x)");
  // the only part of its parent takes the parent with it
  assert.equal(T.deleteTerm(d, ds, "0.1.0"), "diff(x^2, x)");
});

test("a reading after a let head, and of a single number", () => {
  // the parameter in the head is not the x after the =
  const f = "let sq(x) = x^2 + 1";
  const r = T.termSpans(f, reading({ "0.0": "x", "0.1": "2", "1": "1" }, ["root", "0"]));
  assert.equal(r.faithful, true);
  assert.equal(r.spans.get("0.0").inner.start, f.indexOf("= x") + 2);
  assert.equal(text(f, r.spans.get("root").inner), "x^2 + 1");
  assert.equal(T.termSpans("let a = 2", reading({ root: "2" })).faithful, true);
});

test("literals the reading shows whole: a fraction (its denominator first in the text), Euler's number", () => {
  assert.equal(T.termSpans("let w = [7/10, 6/5]", reading({ "0": "107", "1": "56" }, ["root"])).faithful, true);
  assert.equal(T.termSpans("ℯ^(pi*i)", reading({ "0": "e", "1.0": "π", "1.1": "i" }, ["root", "1"]), { pi: "π" }).faithful, true);
});

test("a reading that is not the input does not stand in for it", () => {
  // a system read as its variables and actions: its declarations are gone
  const sys = "let Inc = system(\n  var x in 0..2\n  var p in {read, done}\n  init x = 0 ∧ p = read\n  action go when p = read do x := 1, p := done\n)";
  assert.equal(T.termSpans(sys, reading({ "0.0": "x", "0.1": "p", "1.0": "go" }, ["root", "0", "1"])).faithful, false);
  // a call read without its name
  assert.equal(T.termSpans("let D = divisors(12)", reading({ root: "12" })).faithful, false);
  // a name read as its value
  assert.equal(T.termSpans("dot(u, w)", reading({ "0.0": "1", "0.1": "2", "1.0": "3", "1.1": "4" }, ["root", "0", "1"])).faithful, false);
  // functions drawn as notation are not missing
  assert.equal(T.termSpans("sqrt(x)", reading({ "0": "x" }, ["root"])).faithful, true);
});

test("a λ's binder, a λ cell's directive and a definition's name", () => {
  // `λx` is one name to the editor's lexer; the reading has the binder on its own
  const lam = "(λx. x) y";
  const r = T.termSpans(lam, reading({ "0.0": "x", "0.1": "x", "1": "y" }, ["root", "0"]));
  assert.equal(r.faithful, true);
  assert.equal(text(lam, r.spans.get("0.0").inner), "x");
  // the reading leaves out `fv:` and `normal 2:`, as it leaves out `let name =`
  assert.equal(T.termSpans("fv: λx. x y", reading({ "0": "x", "1.0": "x", "1.1": "y" }, ["root", "1"])).faithful, true);
  assert.equal(T.termSpans("normal 2: omega omega", reading({ "0": "omega", "1": "omega" }, ["root"])).faithful, true);
  assert.equal(T.termSpans("twice := λf. λx. f (f x)", reading({ "0": "f", "1.0": "x", "1.1.0": "f", "1.1.1.0": "f", "1.1.1.1": "x" }, ["root", "1", "1.1", "1.1.1"])).faithful, true);
});

test("notation the reading writes as it is is not a name the source lacks", () => {
  // a world's input as written: `{}` and `@` are pieces of notation, not names or numbers
  const src = "join(S, {}, {x})";
  assert.equal(T.termSpans(src, [{ path: "root", text: "join(S, {}, {x})" }, ...reading({ "1": "S", "2": "{}", "3.0": "x" }, ["3"])]).faithful, true);
});
