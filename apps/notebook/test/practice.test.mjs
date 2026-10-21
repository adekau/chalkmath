// Practice generators (src/practice.ts): seeded, varied, and every question they write is one the
// engine answers. Each topic's questions for many seeds go to the native engine; each must evaluate,
// and its value, typed back as the answer, must be checked right, so a reader can always answer it.
// Needs the native build (`cd engine && lake build`), which CI makes before `npm test`.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { existsSync, mkdtempSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-practice-"));
const out = await build({ entryPoints: [new URL("../src/practice.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "node" });
writeFileSync(join(dir, "practice.mjs"), out.outputFiles[0].text);
const P = await import(pathToFileURL(join(dir, "practice.mjs")).href);

const SEEDS = 40;
const exe = new URL("../../../engine/.lake/build/bin/mathengine", import.meta.url).pathname;

test("a seed gives the same question; another seed, another question", () => {
  for (const t of P.TOPICS) {
    assert.deepEqual(P.generate(t.id, 7), P.generate(t.id, 7), `${t.id} is not determined by its seed`);
    const srcs = new Set(Array.from({ length: SEEDS }, (_, s) => P.generate(t.id, s).src));
    assert.ok(srcs.size >= 5, `${t.id} wrote only ${srcs.size} questions in ${SEEDS} seeds`);
  }
  assert.equal(P.generate("no.such.topic", 1), null);
  assert.equal(new Set(P.TOPICS.map((t) => t.id)).size, P.TOPICS.length, "two topics share an id");
});

test("every lesson exercise with a practice topic names one there is", () => {
  const root = new URL("../../../notebooks/courses/", import.meta.url);
  let n = 0;
  for (const c of readdirSync(root)) for (const f of readdirSync(new URL(`${c}/`, root)).filter((x) => x.endsWith(".chalk"))) {
    for (const cell of JSON.parse(readFileSync(new URL(`${c}/${f}`, root), "utf8")).cells) {
      if (cell.practice === undefined) continue;
      n++;
      assert.equal(cell.type, "exercise", `${c}/${f}: a practice topic on a ${cell.type ?? "math"} cell`);
      assert.ok(P.topicOf(cell.practice), `${c}/${f}: no practice topic ${cell.practice}`);
    }
  }
  assert.ok(n > 0, "no lesson offers practice");
});

test("every question has an answer, and the engine's value typed back is right", { skip: !existsSync(exe) && "no native engine build" }, async () => {
  const { leanNativeClient } = await import("@chalkmath/engine-host/lean-native");
  const c = leanNativeClient(exe);
  let n = 0;
  for (const t of P.TOPICS) {
    for (let seed = 0; seed < SEEDS; seed++) {
      const q = P.generate(t.id, seed);
      const at = `${t.id} seed ${seed}: ${q.src}`;
      assert.ok(q.prompt.trim(), `${at}: no prompt`);
      const sessionId = `practice-${n++}`;
      const r = await c.call("engine.check", { sessionId, cellId: "q", source: q.src });
      assert.ok(r.ok, `${at}: ${r.ok ? "" : r.error.message}`);
      // a puzzle has a solution to find
      if (t.id === "logic.knights") assert.notEqual(r.rendered.text, "⊥", `${at}: the puzzle has no solution`);
      const a = await c.call("engine.check", { sessionId, cellId: "q", source: q.src, answer: r.rendered.text });
      assert.ok(a.ok && a.equivalent, `${at}: its own value ${r.rendered.text} is not accepted (${a.ok ? a.answer?.error?.message ?? "not equivalent" : a.error.message})`);
    }
  }
  console.log(`${n} practice questions, each answered by the engine`);
  await c.close?.();
});
