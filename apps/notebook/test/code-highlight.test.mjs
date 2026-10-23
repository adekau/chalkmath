// The colours of a Markdown cell's fenced code (src/code-highlight.ts): each language's tokens, that
// the tokens are the source again, and that a language the notebook does not know gives nothing. The
// module is TypeScript for the page, so it is bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, readFileSync, readdirSync, statSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-code-highlight-"));
const out = await build({ entryPoints: [new URL("../src/code-highlight.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" });
writeFileSync(join(dir, "code-highlight.mjs"), out.outputFiles[0].text);
const C = await import(pathToFileURL(join(dir, "code-highlight.mjs")).href);

/** The text of each token of class `cls`. */
const of = (toks, cls) => toks.filter((t) => t.cls === cls).map((t) => t.text.trim());

test("TypeScript: keywords, types, calls, strings, numbers and comments", () => {
  const src = "// area\nfunction area(r: number): number {\n  const s = `r=${r}`; /* note */\n  return Math.PI * r ** 2.5 + Math.max(0, 1e3) + 'x'.length;\n}";
  const t = C.highlightCode("ts", src);
  assert.deepEqual(of(t, "hcom"), ["// area", "/* note */"]);
  assert.deepEqual(of(t, "hkw"), ["function", "const", "return"]);
  assert.deepEqual(of(t, "htype"), ["number", "number", "Math", "PI", "Math"]);
  assert.deepEqual(of(t, "hfn"), ["area", "max"]);
  assert.deepEqual(of(t, "hnum"), ["2.5", "0", "1e3"]);
  assert.deepEqual(of(t, "hstr"), ["`r=${r}`", "'x'"]);
  // a word is a keyword only whole, and the aliases name the same language
  assert.deepEqual(of(C.highlightCode("ts", "returned"), "hkw"), []);
  assert.deepEqual(C.highlightCode("JavaScript", "let x"), C.highlightCode("ts", "let x"));
});

test("Lean: commands, tactics, types, comments and notation", () => {
  const src = "theorem t (p q : Prop) : p ∧ q → p := by\n  intro h -- one step\n  exact h.1\n/- a block\ncomment -/";
  const t = C.highlightCode("lean", src);
  assert.deepEqual(of(t, "hkw"), ["theorem", "Prop", "by"]);
  assert.deepEqual(of(t, "hcmd"), ["intro", "exact"]);
  assert.deepEqual(of(t, "hcom"), ["-- one step", "/- a block\ncomment -/"]);
  assert.ok(of(t, "hop").includes("∧") && of(t, "hop").includes("→"));
  assert.deepEqual(of(C.highlightCode("lean", "def f (n : Nat) : Nat := n"), "htype"), ["Nat", "Nat"]);
});

test("Python and JSON", () => {
  const py = C.highlightCode("python", "@cache\ndef f(n):  # fib\n    return None if n < 0 else f\"{n}\"");
  assert.deepEqual(of(py, "hkw"), ["def", "return", "if", "else"]);
  assert.deepEqual(of(py, "hcmd"), ["@cache"]);
  assert.deepEqual(of(py, "hcom"), ["# fib"]);
  assert.deepEqual(of(py, "hconst"), ["None"]);
  assert.deepEqual(of(py, "hstr"), ["f\"{n}\""]);
  const js = C.highlightCode("json", '{"a": [1, -2.5, true, null], "b": "x"}');
  assert.deepEqual(of(js, "hdef"), ['"a"', '"b"']);
  assert.deepEqual(of(js, "hnum"), ["1", "-2.5"]);
  assert.deepEqual(of(js, "hconst"), ["true", "null"]);
  assert.deepEqual(of(js, "hstr"), ['"x"']);
});

test("an unknown language gives nothing; a registered one is used", () => {
  assert.equal(C.highlightCode("cobol", "MOVE A TO B."), null);
  C.registerLanguage(["shout"], (s) => [{ cls: "hkw", text: s.toUpperCase() }]);
  assert.deepEqual(C.highlightCode("Shout", "hi"), [{ cls: "hkw", text: "HI" }]);
  assert.ok(C.languages().includes("ts") && C.languages().includes("lean"));
});

test("the tokens are the source, for every fenced block in the bundled notebooks, and unclosed ones", () => {
  const files = [];
  const walk = (d) => { for (const f of readdirSync(d)) { const p = join(d, f); if (statSync(p).isDirectory()) walk(p); else if (p.endsWith(".chalk")) files.push(p); } };
  walk(new URL("../../../notebooks", import.meta.url).pathname);
  let blocks = 0;
  for (const f of files) {
    for (const cell of JSON.parse(readFileSync(f, "utf8")).cells ?? []) {
      for (const m of String(cell.src ?? "").matchAll(/^\s*```\s*([\w+-]+)\s*\n([\s\S]*?)\n\s*```/gm)) {
        const toks = C.highlightCode(m[1], m[2]);
        if (!toks) continue;
        blocks++;
        assert.equal(toks.map((t) => t.text).join(""), m[2], `${f}: a ${m[1]} block`);
      }
    }
  }
  assert.ok(blocks >= 8, `only ${blocks} highlighted blocks in the bundled notebooks`);
  for (const [lang, src] of [["ts", "/* open"], ["ts", "\"open"], ["ts", "`open\n"], ["lean", "/- open"], ["python", "'''open"], ["json", '{"a'], ["ts", "0x1F_n é ∑"]])
    assert.equal(C.highlightCode(lang, src).map((t) => t.text).join(""), src, `${lang}: ${src}`);
});
