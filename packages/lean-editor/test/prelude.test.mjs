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
