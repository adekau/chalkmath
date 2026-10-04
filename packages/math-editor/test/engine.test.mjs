import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync, readFileSync, readdirSync } from "node:fs";
import { read, write, letHead } from "../dist/index.js";

// The reader and writer against the engine itself: every golden source and every notebook cell, as
// written and as the visual editor would write it back, evaluated side by side in two sessions of
// the native engine. The parsed input (`inputRendered`) and the answer must be the same. Needs the
// native build (`cd engine && lake build`), which CI makes before `npm test`.
const root = new URL("../../../", import.meta.url);
const exe = new URL("engine/.lake/build/bin/mathengine", root).pathname;

/** The bundled notebooks: notebooks/*.chalk and the courses' lessons, notebooks/courses/<course>/*.chalk. */
const chalkFiles = () => [
  ...readdirSync(new URL("notebooks/", root)).filter((f) => f.endsWith(".chalk")),
  ...readdirSync(new URL("notebooks/courses/", root)).flatMap((c) => readdirSync(new URL(`notebooks/courses/${c}/`, root)).filter((f) => f.endsWith(".chalk")).map((f) => `courses/${c}/${f}`)),
];
/** A cell the engine reads as notation: a math cell, or an exercise's question (a Lean exercise's is Lean). */
const mathCell = (c) => !c.type || c.type === "math" || (c.type === "exercise" && !c.lean);

test("what the editor writes means what the source meant, to the engine", { skip: !existsSync(exe) && "no native engine build" }, async () => {
  const { leanNativeClient } = await import("@chalkmath/engine-host/lean-native");
  const c = leanNativeClient(exe);
  const suites = [
    { name: "golden.tsv", cells: readFileSync(new URL("engine/Tests/golden.tsv", root), "utf8").split("\n").filter(Boolean).map((l) => l.split("\t")[0]) },
    ...chalkFiles().map((f) => ({
      name: f, cells: JSON.parse(readFileSync(new URL(`notebooks/${f}`, root), "utf8")).cells.filter(mathCell).map((x) => x.src),
    })),
  ];
  const answer = (r) => JSON.stringify(r.ok === false ? { error: r.error.message } : {
    value: r.rendered?.text, input: r.inputRendered?.text, series: r.series?.map((s) => s.rendered.text),
    frames: r.frames?.map((f) => f.rendered.text),
  });
  let compared = 0;
  // the engine's `Lam.isLambdaSource`: a λ, a definition or a λ-command, or a first word that is a
  // λ-definition (the cells' own or the Church library's) in a source that lexes as a λ-term (`Lam.lex`)
  // — `fst (pair a b)` has no λ but is a λ-term, `S + 1` is arithmetic
  const church = ["true", "false", "and", "or", "not", "if", "zero", "succ", "add", "mul", "pow", "iszero", "pair", "fst", "snd", "id", "const", "K", "S", "I", "omega", "Y"];
  const lambdaLexes = /^(?:[ \t\r\n.():λ\\→]|->|[0-9]+(?![0-9])|[A-Za-z_\u0391-\u03A9\u03B1-\u03C9][A-Za-z0-9_'\u0391-\u03A9\u03B1-\u03C9]*(?![A-Za-z0-9_'\u0391-\u03A9\u03B1-\u03C9]))*$/;
  const lambdaCell = (src, defs) => {
    if (/[λ\\]|:=/.test(src) || /^\s*(normal|cbn|cbv|applicative|eta|fv|db|alpha|subst|type|infer)\s*(\d+\s*)?:(?!=)/.test(src)) return true;
    const w = src.trim().split(" ")[0] ?? "";
    return w !== "let" && (church.includes(w) || defs.includes(w)) && (!src.includes("(") || src.includes(" ")) && lambdaLexes.test(src);
  };
  for (const { name, cells } of suites) {
    const known = [];
    const defs = [];
    for (const [i, src] of cells.entries()) {
      const def = /^\s*([A-Za-z_][\w']*)\s*:=/.exec(src);
      const lambda = lambdaCell(src, defs);
      if (def) defs.push(def[1]);
      const r = lambda ? { ok: false } : read(src, known);
      // cells this grammar does not read (λ, order theory, import) go to both sessions unchanged
      const rewritten = r.ok ? write(r.stmt).text : src;
      if (r.ok && letHead(r.stmt)?.params) known.push(letHead(r.stmt).name);
      const method = /^\s*(plot|epicycles|dft)\s*\(/.test(src) ? "engine.plot" : /^\s*manipulate\s*\(/.test(src) ? "engine.manipulate" : "engine.evaluate";
      const call = (sessionId, source) => c.call(method, { sessionId, cellId: `c${i}`, source, showWork: true })
        .catch((e) => ({ ok: false, error: { message: `rpc: ${e.message}` } }));
      const [a, b] = await Promise.all([call(`${name}:source`, src), call(`${name}:written`, rewritten)]);
      assert.equal(answer(b), answer(a), `${name} cell ${i}: ${JSON.stringify(src)} written as ${JSON.stringify(rewritten)}`);
      if (r.ok) compared++;
    }
  }
  c.close();
  assert.ok(compared >= 250, `only ${compared} cells compared`);
});
