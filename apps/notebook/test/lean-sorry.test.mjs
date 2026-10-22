// Whether a Lean exercise's proof leaves a `sorry` (src/lean-sorry.ts): a commented-out or quoted one
// does not count. The module is TypeScript for the page, so it is bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-lean-sorry-"));
const out = await build({ entryPoints: [new URL("../src/lean-sorry.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "node" });
writeFileSync(join(dir, "lean-sorry.mjs"), out.outputFiles[0].text);
const { leavesSorry, leanCode, escapesIn, forbiddenIn } = await import(pathToFileURL(join(dir, "lean-sorry.mjs")).href);

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

test("a definition exercise's form: what the definition may not use, in its code", () => {
  const rec = "def double : Nat → Nat\n  | 0 => 0\n  | n + 1 => double n + 2";
  assert.deepEqual(forbiddenIn(rec, ["*", "Nat.mul", "mul"]), []);
  assert.deepEqual(forbiddenIn("def double (n : Nat) : Nat := 2 * n", ["*", "Nat.mul", "mul"]), ["*"]);
  assert.deepEqual(forbiddenIn("def double (n : Nat) : Nat := Nat.mul 2 n", ["*", "Nat.mul", "mul"]), ["Nat.mul", "mul"]);
  // a helper of the reader's own is in the same definition part, so it is seen too
  assert.deepEqual(forbiddenIn("def twice (a : Nat) := a * 2\ndef double (n : Nat) := twice n", ["*"]), ["*"]);
  // comments and strings are not code; a longer name that only contains a forbidden one is not it
  assert.deepEqual(forbiddenIn("def double (n : Nat) : Nat := n + n -- not 2 * n\n/- * -/", ["*"]), []);
  assert.deepEqual(forbiddenIn("def multiply := 0\ndef mul' := 1", ["mul"]), []);
});

test("a way out of proving is refused wherever it is written", () => {
  assert.deepEqual(escapesIn("theorem t : 1 = 2 := by native_decide"), ["native_decide"]);
  assert.deepEqual(escapesIn("axiom cheat : ∀ n, double n = 2 * n"), ["axiom"]);
  assert.deepEqual(escapesIn("@[implemented_by fast] def double (n : Nat) := n"), ["implemented_by"]);
  assert.deepEqual(escapesIn("unsafe def f := 0"), ["unsafe"]);
  assert.deepEqual(escapesIn("-- no axiom here\nexact Nat.two_mul n"), []);
  assert.deepEqual(escapesIn("exact axiomatic"), []);
});

test("every definition exercise in the courses: the author's definition keeps the exercise's own rules", () => {
  const root = new URL("../../../notebooks/courses/", import.meta.url);
  let n = 0;
  for (const c of readdirSync(root)) for (const f of readdirSync(new URL(`${c}/`, root)).filter((x) => x.endsWith(".chalk"))) {
    for (const cell of JSON.parse(readFileSync(new URL(`${c}/${f}`, root), "utf8")).cells) {
      if (cell.type !== "exercise" || cell.leanDef === undefined) continue;
      n++;
      const at = `${c}/${f}: ${cell.src.split("\n")[0]}`;
      assert.ok(cell.leanDefSolution?.trim(), `${at}: no definition of the author's`);
      assert.deepEqual(forbiddenIn(cell.leanDefSolution, cell.leanForbid ?? []), [], `${at}: the author's definition breaks its own rules`);
      assert.deepEqual(escapesIn(`${cell.leanDefSolution}\n${cell.leanSolution}`), [], `${at}: the author's work has a way out`);
      assert.equal(leavesSorry(cell.leanDefSolution), false, `${at}: the author's definition has a sorry`);
      assert.equal(leavesSorry(cell.leanDef), true, `${at}: the starting definition leaves nothing to write`);
    }
  }
  assert.ok(n > 0, "no definition exercise in the courses");
});
