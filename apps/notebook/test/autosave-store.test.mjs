// Where the open notebooks are kept between visits (src/autosave-store.ts): each tab under its own key,
// a closed tab's notebooks adopted by the next tab to start, and an unreadable autosave set aside rather
// than saved over. The module is TypeScript for the page, so it is bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-autosave-"));
const out = await build({ entryPoints: [new URL("../src/autosave-store.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" });
writeFileSync(join(dir, "autosave-store.mjs"), out.outputFiles[0].text);
const A = await import(pathToFileURL(join(dir, "autosave-store.mjs")).href);

/** localStorage, in memory; `full` makes every write fail as a full storage does. */
function storage(entries = {}) {
  const m = new Map(Object.entries(entries));
  return {
    full: false, m,
    getItem: (k) => m.get(k) ?? null,
    setItem(k, v) { if (this.full) throw new Error("QuotaExceededError"); m.set(k, String(v)); },
    removeItem: (k) => m.delete(k),
    get length() { return m.size; },
    key: (i) => [...m.keys()][i] ?? null,
  };
}
const nb = (name) => ({ chalk: 1, name, cells: [{ src: "1+1" }], scenes: [] });
const tab = (active, ...names) => JSON.stringify({ chalkmath: 1, active, docs: names.map((n) => ({ file: nb(n), dirty: true })) });
const names = (a) => a?.docs.map((d) => d.file.name);

test("a reload finds its own tab's notebooks, and leaves a live tab's alone", () => {
  const s = storage({ [A.keyOf("me")]: tab(1, "a", "b"), [A.keyOf("other")]: tab(0, "c") });
  const { merged } = A.gather(s, "me", new Set(["me", "other"]));
  assert.deepEqual(names(merged), ["a", "b"]);
  assert.equal(merged.active, 1);
  assert.ok(s.getItem(A.keyOf("other")), "a live tab's autosave was taken");
});

test("a tab that has closed is adopted: its notebooks open, and its key goes", () => {
  const s = storage({ [A.keyOf("me")]: tab(0, "a"), [A.keyOf("gone")]: tab(0, "c"), [A.keyOf("live")]: tab(0, "d") });
  const { merged } = A.gather(s, "me", new Set(["me", "live"]));
  assert.deepEqual(names(merged), ["a", "c"]);
  assert.equal(s.getItem(A.keyOf("gone")), null);
  assert.deepEqual(names(A.parseAutosave(s.getItem(A.keyOf("me")))), ["a", "c"], "what was adopted is saved under this tab's key at once");
});

test("the single key of older versions, either format, is adopted too", () => {
  const s = storage({ "chalkmath.autosave": tab(0, "old"), "lemma.autosave": JSON.stringify(nb("older")) });
  const { merged } = A.gather(s, "new", new Set(["new"]));
  assert.deepEqual(names(merged).sort(), ["old", "older"]);
  assert.equal(s.getItem("chalkmath.autosave"), null);
  assert.equal(s.getItem("lemma.autosave"), null);
});

test("an unreadable autosave is set aside, not lost to the next save", () => {
  const s = storage({ [A.keyOf("me")]: "{\"chalkmath\":1,\"docs\":[{\"fi", [A.keyOf("gone")]: tab(0, "c") });
  const { merged, setAside } = A.gather(s, "me", new Set(["me"]), 42);
  assert.deepEqual(names(merged), ["c"]);
  assert.equal(setAside.length, 1);
  assert.equal(s.getItem(setAside[0]), "{\"chalkmath\":1,\"docs\":[{\"fi");
  // set aside, it is not adopted (or set aside again) by the next tab
  assert.deepEqual(A.orphans(s, "next", new Set(["me", "next"])), []);
});

test("with the storage full, nothing is removed: the orphans wait to be adopted next time", () => {
  const s = storage({ [A.keyOf("gone")]: tab(0, "c") });
  s.full = true;
  const { merged } = A.gather(s, "me", new Set(["me"]));
  assert.deepEqual(names(merged), ["c"], "the notebooks still open");
  assert.ok(s.getItem(A.keyOf("gone")), "removed though the merge was never written");
});

test("only autosaves are read as autosaves", () => {
  assert.equal(A.parseAutosave("not json"), null);
  assert.equal(A.parseAutosave("null"), null);
  assert.equal(A.parseAutosave(JSON.stringify({ chalkmath: 1, docs: [{ dirty: true }] })), null);
  assert.deepEqual(names(A.parseAutosave(tab(0, "a"))), ["a"]);
});
