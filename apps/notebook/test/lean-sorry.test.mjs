// Whether a Lean exercise's proof leaves a `sorry` (src/lean-sorry.ts): a commented-out or quoted one
// does not count. The module is TypeScript for the page, so it is bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-lean-sorry-"));
const out = await build({ entryPoints: [new URL("../src/lean-sorry.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "node" });
writeFileSync(join(dir, "lean-sorry.mjs"), out.outputFiles[0].text);
const { leavesSorry, leanCode } = await import(pathToFileURL(join(dir, "lean-sorry.mjs")).href);

test("a sorry or admit in the code counts", () => {
  assert.equal(leavesSorry("  sorry"), true);
  assert.equal(leavesSorry("intro h\nexact h -- done\nadmit"), true);
  assert.equal(leavesSorry("constructor <;> sorry"), true);
});

test("a commented-out sorry does not count", () => {
  const proof = [
    "intro s h", "induction h", "case init t a =>", "  exact hinit t a",
    "case step t x rs rt ih =>", "  exact hstep t x ih rt",
    "-- apply hinit", "-- case step t rt st =>", "--   sorry",
  ].join("\n");
  assert.equal(leavesSorry(proof), false);
  assert.equal(leavesSorry("exact h /- sorry -/"), false);
  assert.equal(leavesSorry("/- outer /- sorry -/ still a comment sorry -/ exact h"), false);
  assert.equal(leavesSorry("exact h /- unclosed sorry"), false);
});

test("a quoted sorry does not count, and a name containing it is not one", () => {
  assert.equal(leavesSorry('trace "sorry \\" sorry"\nexact h'), false);
  assert.equal(leavesSorry("exact sorryAx_free h"), false);
});

test("code after a block comment is kept, lines and all", () => {
  assert.equal(leavesSorry("/- a\nb -/ sorry"), true);
  assert.equal(leanCode("a /- x\ny -/ b").split("\n").length, 2);
});
