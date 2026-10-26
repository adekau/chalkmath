// The page's own CSS (index.html) against Monaco's: a Lean cell is Monaco, inside the page, and its
// suggestion list and widgets are built from generic class names (.main, .body, .docs, .code, ...). A
// page rule that names one of them bare also styles Monaco's: `.main { flex-direction:column }` once
// hid every label in the suggestion list. Such a rule has to name where the page puts the element.
import { test } from "node:test";
import assert from "node:assert/strict";
import { readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";

const html = readFileSync(new URL("../index.html", import.meta.url), "utf8");
const css = [...html.matchAll(/<style[^>]*>([\s\S]*?)<\/style>/g)].map((m) => m[1]).join("\n").replace(/\/\*[\s\S]*?\*\//g, "");

/** Every class name in the stylesheets of Monaco's editor and its widgets (lean4monaco's `vscode`). */
function monacoClasses() {
  const root = new URL("../../../node_modules/vscode/vscode/src/vs/", import.meta.url).pathname;
  const names = new Set();
  for (const part of ["editor", "base"])
    for (const f of readdirSync(join(root, part), { recursive: true }))
      if (f.endsWith(".css.js")) for (const m of readFileSync(join(root, part, f), "utf8").matchAll(/\.([a-zA-Z][\w-]*)/g)) names.add(m[1]);
  return names;
}

test("no page rule starts from a bare class name Monaco's editor also uses", () => {
  const monaco = monacoClasses();
  assert.ok(monaco.has("suggest-widget") && monaco.has("main"), "Monaco's stylesheets were not found");
  const bare = [];
  for (const [, selectors] of css.matchAll(/([^{}]+)\{[^{}]*\}/g))
    for (const sel of selectors.split(",").map((s) => s.trim())) {
      const [first, combinator] = sel.split(/\s*([>+~\s])\s*/);
      const classes = [...(first ?? "").matchAll(/\.([\w-]+)/g)].map((m) => m[1]);
      // a selector that starts from the root, an element or an id, or ties the class to its parent with `>`, is the page's
      if (!classes.length || /^[#\w[:]/.test(first) || combinator === ">") continue;
      if (classes.every((c) => monaco.has(c))) bare.push(sel);
    }
  assert.deepEqual(bare, []);
});
