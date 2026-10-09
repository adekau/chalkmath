// The worlds as the notebook knows them (src/worlds.ts): the fallback list is the engine's own, and a
// cell's world is read from its source as the engine reads it. The module is TypeScript for the page,
// so it is bundled first. The equality with the engine needs the native build (`cd engine && lake build`).
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { existsSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-worlds-"));
const out = await build({ entryPoints: [new URL("../src/worlds.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" });
writeFileSync(join(dir, "worlds.mjs"), out.outputFiles[0].text);
const W = await import(pathToFileURL(join(dir, "worlds.mjs")).href);

const root = new URL("../../../", import.meta.url);
const exe = new URL("engine/.lake/build/bin/mathengine", root).pathname;

test("the fallback list is what the native engine publishes", { skip: !existsSync(exe) && "no native engine build" }, async () => {
  const { leanNativeClient } = await import("@chalkmath/engine-host/lean-native");
  const c = leanNativeClient(exe);
  const caps = await c.call("engine.capabilities", {});
  c.close();
  assert.deepEqual(W.FALLBACK_WORLDS, caps.worlds);
});

test("a cell's world is read from its source as the engine routes it", () => {
  const defs = (w) => w === "pred";
  assert.equal(W.worldOf("diff(x^2, x)"), null);
  assert.equal(W.worldOf("let f = x^2 + 1"), null);
  assert.equal(W.worldOf("taut(p → q)"), "logic");
  assert.equal(W.worldOf("p && q"), "logic");
  assert.equal(W.worldOf("forall n in 1..5, n^2 > 0"), "logic");
  assert.equal(W.worldOf("let P = poset({a, b}; a < b)"), "poset");
  assert.equal(W.worldOf("closure(R, transitive)"), "poset");
  assert.equal(W.worldOf("let S = system(var x in 0..1; init x = 0; action t when x < 1 do x := x + 1)"), "system");
  assert.equal(W.worldOf("invariant(S, x ≤ 1)"), "system");
  assert.equal(W.worldOf("rules(f(x) -> x)"), "system");
  // a λ-command is the λ-world's whatever else it holds; `type := …` is a definition
  assert.equal(W.worldOf("type: f : A → B ⊢ f"), "lambda");
  assert.equal(W.worldOf("cbv 3: (λx. x) y"), "lambda");
  assert.equal(W.worldOf("λx. x"), "lambda");
  assert.equal(W.worldOf("pred := λn. n"), "lambda");
  assert.equal(W.worldOf("succ zero"), "lambda");
  assert.equal(W.worldOf("pred zero", defs), "lambda");
  assert.equal(W.worldOf("pred zero"), null);
  assert.equal(W.worldOf("S + 1"), null);
  assert.equal(W.lambdaCommand("type: x"), true);
  assert.equal(W.lambdaCommand("type := x"), false);
});

test("the lexicon the page reads: calls, keywords", () => {
  const fns = W.worldFns();
  for (const n of ["taut", "poset", "system", "prime", "closure"]) assert.ok(fns.includes(n), n);
  assert.ok(!fns.includes("type"), "a λ-command is not a call");
  assert.ok(W.worldKeywords().has("when") && W.worldKeywords().has("forall"));
  assert.equal(W.hasKeywords("let S = system(var x in 0..1)"), true);
  assert.equal(W.hasKeywords("x^2"), false);
  assert.equal(W.hasKeywords("λx. x"), false);
});
