// The function reference (src/reference.ts): every engine function has a page, the pages' links
// resolve, and every example input is one the engine's grammar reads (by the visual input's reader,
// which is held to agree with Parser.lean). The examples' outputs are not here: the documentation
// asks the engine for them when a page is shown.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-ref-"));
async function load(entry, name) {
  const out = await build({ entryPoints: [entry], bundle: true, format: "esm", write: false, platform: "neutral" });
  const file = join(dir, name);
  writeFileSync(file, out.outputFiles[0].text);
  return import(pathToFileURL(file).href);
}
const R = await load(new URL("../src/reference.ts", import.meta.url).pathname, "reference.mjs");
const M = await load(new URL("../../../packages/math-editor/src/index.ts", import.meta.url).pathname, "math-editor.mjs");

// the engine's own lists (Parser.lean's builtins, mirrored by the math editor; Poset.lean's heads)
const ORDER = ["poset", "divisors", "subsets", "chain", "map", "hasse", "join", "meet", "upper", "lower",
  "lattice", "top", "bottom", "le", "maximal", "minimal", "monotone", "lfp", "gfp", "fixpoints",
  "rel", "kernel", "reflexive", "symmetric", "antisymmetric", "transitive", "equivalence", "preorder", "closure", "classes", "finer", "wellfounded", "measure",
  "op", "joinop", "meetop", "table", "associative", "commutative", "idempotent", "semilattice", "identity", "fold", "order",
  "distributive", "complement", "complemented", "boolean", "product", "galois", "closureop", "context", "concepts", "secure",
  "events", "clocks", "concurrent"];
// Systems.lean's commands
const SYSTEMS = ["system", "states", "invariant", "inductive", "reach", "deadlock", "trace", "ctl", "eventually", "refines"];
// Logic.lean's commands
const LOGIC = ["truthtable", "taut", "sat", "falsify", "equiv", "nnf", "cnf", "dnf"];
// not documented: `log` is only numeric (N), and `solve` is a reserved name with nothing behind it yet
const UNDOCUMENTED = ["log", "solve"];

test("every engine function has a page", () => {
  for (const name of [...M.BUILTIN_FUNCTIONS, ...ORDER, ...LOGIC, ...SYSTEMS]) {
    if (UNDOCUMENTED.includes(name)) continue;
    assert.ok(R.FN_BY_NAME.has(name), `${name} has no page`);
  }
});

test("pages are unique, complete, and link to pages that exist", () => {
  assert.equal(R.FN_BY_NAME.size, R.FUNCTIONS.length, "two pages share a name");
  const areas = new Set(R.AREAS.map(([a]) => a));
  for (const f of R.FUNCTIONS) {
    assert.ok(areas.has(f.area), `${f.name}: unknown area ${f.area}`);
    assert.ok(f.usage.length, `${f.name}: no usage`);
    for (const [form, what] of f.usage) {
      assert.ok(/[.…]$/.test(what), `${f.name}: usage of ${form} is not a sentence`);
      assert.ok(!what.includes("$"), `${f.name}: usage lines are plain text (they are hover and signature help too)`);
    }
    assert.ok(f.examples.some((s) => s.items.some((it) => typeof it === "string")), `${f.name}: no examples`);
    for (const n of f.see ?? []) assert.ok(R.FN_BY_NAME.has(n), `${f.name}: see also ${n} has no page`);
  }
});

test("every example input reads in the engine's grammar", () => {
  const bad = [];
  for (const f of R.FUNCTIONS) {
    if (f.area === "Order theory" || f.area === "λ-calculus" || f.area === "Logic" || f.area === "Transition systems") continue;   // their own grammars
    for (const sec of f.examples) {
      const known = [];
      for (const src of sec.items.filter((it) => typeof it === "string")) {
        // a bound question's answer can be a formula, which defines a function of its letters
        const asked = /^\s*let\s+([A-Za-z_]\w*)\s*=\s*\?/.exec(src);
        if (asked) known.push(asked[1]);
        // questions, files, output references, and parts (which the reader leaves to the text input)
        if (/^\s*(let\s+\w+\s*=\s*)?\?|import\(|%|\[\[/.test(src)) continue;
        const r = M.read(src, known);
        if (!r.ok) bad.push(`${f.name} › ${sec.title}: ${src} — ${r.error.message}`);
        const fn = /^\s*let\s+([A-Za-z_]\w*)\s*\(/.exec(src);
        if (fn) known.push(fn[1]);
      }
    }
  }
  assert.deepEqual(bad, []);
});
