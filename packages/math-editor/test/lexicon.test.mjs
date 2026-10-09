import { test } from "node:test";
import assert from "node:assert/strict";
import { existsSync } from "node:fs";
import { KEYWORDS, MULTI_OPS, configureLexicon } from "../dist/index.js";

// The editor's lexicon of the other worlds (model.ts: the keywords that end a product, the operators
// of several characters read as one atom) against the engine's own, as `engine.capabilities`
// publishes it (`World.lean`). The lists here are the fallback for an engine that predates the
// capability; this test is what keeps them from drifting. Needs the native build.
const root = new URL("../../../", import.meta.url);
const exe = new URL("engine/.lake/build/bin/mathengine", root).pathname;

test("the editor's keywords and multi-character operators are the engine's", { skip: !existsSync(exe) && "no native engine build" }, async () => {
  const { leanNativeClient } = await import("@chalkmath/engine-host/lean-native");
  const c = leanNativeClient(exe);
  const caps = await c.call("engine.capabilities", {});
  c.close();
  assert.ok(Array.isArray(caps.worlds) && caps.worlds.length >= 5, "the engine publishes its worlds");
  const keywords = new Set(caps.worlds.flatMap((w) => w.keywords));
  const multi = new Set(caps.worlds.flatMap((w) => w.glyphs).filter((g) => Array.from(g).length > 1 && !/\s/.test(g)));
  assert.deepEqual([...KEYWORDS].sort(), [...keywords].sort(), "keywords");
  assert.deepEqual([...MULTI_OPS].sort(), [...multi].sort(), "operators of several characters");
  // adding the engine's lexicon changes nothing, since it is already the editor's
  const before = [...MULTI_OPS];
  configureLexicon(caps.worlds);
  assert.deepEqual(MULTI_OPS, before);
});
