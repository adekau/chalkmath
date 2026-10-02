// Animated graphs (src/animate.ts): the positions ▶ Play moves a slider through, how long each is
// held, and the window a plot keeps while a slider drives it. The module is TypeScript for the page,
// so it is bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-animate-"));
const out = await build({ entryPoints: [new URL("../src/animate.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" });
writeFileSync(join(dir, "animate.mjs"), out.outputFiles[0].text);
const A = await import(pathToFileURL(join(dir, "animate.mjs")).href);

test("a slider plays up from where it is to its max, a step at a time", () => {
  assert.deepEqual(A.playFrames({ min: 1, max: 6, step: 1 }, 3), [4, 5, 6]);
});

test("a slider at the end it plays toward starts over from the other end", () => {
  assert.deepEqual(A.playFrames({ min: 1, max: 4, step: 1 }, 4), [1, 2, 3, 4]);
  assert.deepEqual(A.playFrames({ min: 1, max: 4, step: 1, play: "down" }, 1), [4, 3, 2, 1]);
});

test("h → 0: playing down toward a small min, with no float noise", () => {
  const f = A.playFrames({ min: 0.05, max: 2, step: 0.05, play: "down" }, 2);
  assert.equal(f.length, 39);
  assert.equal(f[0], 1.95);
  assert.equal(f.at(-1), 0.05);
  assert.ok(f.every((v) => String(v).length <= 4), `noisy: ${f.find((v) => String(v).length > 4)}`);
  for (let k = 1; k < f.length; k++) assert.ok(f[k] < f[k - 1]);
});

test("a min with more decimals than the step keeps them", () => {
  assert.deepEqual(A.playFrames({ min: 0.05, max: 0.35, step: 0.1 }, 0.05), [0.15, 0.25, 0.35]);
});

test("a fine range is played in strides, and still ends at the end", () => {
  const f = A.playFrames({ min: 0, max: 1000, step: 1 }, 0);
  assert.ok(f.length <= A.MAX_FRAMES, `${f.length} frames`);
  assert.equal(f.at(-1), 1000);
});

test("a play lasts about PLAY_MS, each frame held within FRAME_MS", () => {
  assert.equal(A.frameMs(40), A.PLAY_MS / 40);
  assert.equal(A.frameMs(2), A.FRAME_MS[1]);
  assert.equal(A.frameMs(10000), A.FRAME_MS[0]);
});

const graph = (...ys) => ({ series: [{ points: ys.map((y, i) => [i, y]) }] });

test("a plot's window takes in the axis and a margin", () => {
  const [y0, y1] = A.plotYRange(graph(1, 2, 3, null));
  assert.ok(y0 < 0 && y1 > 3);
  assert.deepEqual(A.plotYRange(graph(null)), [-1, 1]);
});

test("a held window widens to take in the curves, and never narrows", () => {
  const w1 = A.holdWindow(null, graph(0, 10));
  const w2 = A.holdWindow(w1, graph(0, 2));
  assert.deepEqual(w2, w1, "a smaller curve narrowed the window");
  const w3 = A.holdWindow(w2, graph(-5, 2));
  assert.ok(w3[0] < -5 && w3[1] === w1[1], "a curve below the window did not widen it");
});

test("a curve in the plane or epicycles keeps no window: both axes are fitted at once", () => {
  assert.equal(A.holdWindow(null, { series: [{ points: [[0, 1]], parametric: true }] }), null);
  assert.equal(A.holdWindow([0, 1], { series: [{ points: [[0, 1]] }], terms: [{}] }), null);
});
