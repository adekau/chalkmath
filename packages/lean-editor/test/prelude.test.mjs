import { test } from "node:test";
import assert from "node:assert/strict";
import { leanForPrelude } from "../src/prelude.js";

test("a prelude keeps declarations and drops what only shows something", () => {
  const src = [
    "def a := 1", "",
    "/-- shown, then dropped with its example -/", "example : a = 1 := rfl", "",
    "#eval a", "#print axioms a", "#check (a : Nat)", "#reduce a + 1",
    "theorem t : a = 1 :=", "  rfl",
    "set_option pp.all true in", "#check a",
    "#guard_msgs in", "#eval a",
    "/-- kept with its definition -/", "def b := a + 1",
  ].join("\n");
  assert.equal(leanForPrelude(src), ["def a := 1", "", "theorem t : a = 1 :=", "  rfl", "/-- kept with its definition -/", "def b := a + 1"].join("\n"));
});

test("commands inside a block comment, a string or an indented proof are not commands", () => {
  const src = ["/- notes", "#eval x", "example : True := trivial", "-/", "def s := \"/- not a comment\"", "#eval s", "def c := 3",
    "theorem u : c = 3 := by", "  -- #eval in a proof stays", "  rfl"].join("\n");
  assert.equal(leanForPrelude(src), ["/- notes", "#eval x", "example : True := trivial", "-/", "def s := \"/- not a comment\"", "def c := 3",
    "theorem u : c = 3 := by", "  -- #eval in a proof stays", "  rfl"].join("\n"));
});

test("Lean without show-only commands is unchanged", () => {
  const src = "namespace N\n\ndef f (n : Nat) : Nat :=\n  n + 1\n\nend N";
  assert.equal(leanForPrelude(src), src);
});

import { authorLean, preludePart, preludeOf, scopeOf, textHash, moduleName, moduleSource, moduleEntry, importedPrelude } from "../src/prelude.js";

test("a lesson's part of its course's prelude: its Lean, the author's proofs, under its title", () => {
  const cells = [
    { type: "markdown", src: "# notes" },
    { type: "lean", src: "def a := 1\n#eval a" },
    { type: "exercise", lean: true, src: "theorem t : a = 1 := by", leanSolution: "  rfl" },
    { type: "exercise", lean: true, src: "theorem u : a = a := by" },
  ];
  assert.deepEqual(authorLean(cells), ["def a := 1\n#eval a", "theorem t : a = 1 := by\n  rfl", "theorem u : a = a := by\n  sorry"]);
  assert.equal(preludePart("One", cells), "-- One\ndef a := 1\ntheorem t : a = 1 := by\n  rfl\n\ntheorem u : a = a := by\n  sorry");
  assert.equal(preludePart("None", [{ type: "markdown", src: "x" }]), null);
  assert.equal(preludeOf(["-- A\ndef a := 1", null, "-- C\ndef c := 3"]), "-- A\ndef a := 1\n\n-- C\ndef c := 3");
});

test("the scope a prelude leaves: its namespaces, sections, opens and variables, not their `in` forms", () => {
  const src = ["namespace Crdt", "open Nat", "def x := 1", "section", "variable {α : Type}", "theorem t : x = 1 := rfl", "end",
    "open List in", "def y := 2", "set_option pp.all true in", "#check y", "/- namespace Not", "-/", "universe u"].join("\n");
  assert.equal(scopeOf(src), ["namespace Crdt", "open Nat", "section", "variable {α : Type}", "end", "universe u"].join("\n"));
});

test("modules: each lesson's part after an import of the one before and its scope; a prelude imported only when it is the module's", () => {
  const parts = ["-- One\nnamespace A\ndef a := 1", null, "-- Three\ndef c := a"];
  assert.equal(moduleName("order-lattices", 3), "ChalkCourse.OrderLattices.L03");
  assert.equal(moduleName("2d", 1), "ChalkCourse.C2d.L01");
  assert.equal(moduleSource("c", parts, 1), "-- One\nnamespace A\ndef a := 1\n");
  assert.equal(moduleSource("c", parts, 3), "import ChalkCourse.C.L02\nnamespace A\n-- Three\ndef c := a\n");
  const full = preludeOf(parts);
  const e2 = moduleEntry("c", parts, 2), e3 = moduleEntry("c", parts, 3);
  assert.equal(importedPrelude(e3, full), "import ChalkCourse.C.L03\nnamespace A");
  // the first two lessons imported, the third inline after them
  assert.equal(importedPrelude(e2, full), "import ChalkCourse.C.L02\nnamespace A\n\n-- Three\ndef c := a");
  // a prelude saved from an older course is not the module's
  assert.equal(importedPrelude(e3, full.replace("def a := 1", "def a := 2")), null);
  assert.equal(importedPrelude(e2, `${full.slice(0, e2.length)}X`), null);
  assert.notEqual(textHash("a"), textHash("b"));
  assert.equal(textHash(""), textHash(""));
});
