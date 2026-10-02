// Manipulate's frames on the page (src/animate.ts): one window for every frame of a plot, blending
// two neighbouring frames while it plays, and where a play is after a while. The module is
// TypeScript for the page, so it is bundled first.
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

const graph = (...ys) => ({ series: [{ latex: "f", points: ys.map((y, i) => [i, y]) }] });

test("a plot's window takes in the axis and a margin", () => {
  const [y0, y1] = A.plotYRange(graph(1, 2, 3, null));
  assert.ok(y0 < 0 && y1 > 3);
  assert.deepEqual(A.plotYRange(graph(null)), [-1, 1]);
});

test("every frame of a manipulated plot shares one window, wide enough for all of them", () => {
  const [y0, y1] = A.framesWindow([graph(0, 1), graph(-5, 0), graph(0, 9)]);
  assert.ok(y0 < -5 && y1 > 9, `${y0}, ${y1}`);
});

test("a curve in the plane or epicycles keeps no shared window: both axes are fitted at once", () => {
  assert.equal(A.framesWindow([{ series: [{ points: [[0, 1]], parametric: true }] }]), null);
  assert.equal(A.framesWindow([{ series: [{ points: [[0, 1]] }], terms: [{}] }]), null);
  assert.equal(A.framesWindow([]), null);
});

test("between two frames, each sample is blended; a gap in either is a gap; the curve keeps its fields", () => {
  const b = A.blend(graph(0, 2, null), graph(4, 6, 1), 0.25);
  assert.deepEqual(b[0].points, [[0, 1], [1, 3], [2, null]]);
  assert.equal(b[0].latex, "f");
});

test("only frames with the same curves at the same points blend", () => {
  assert.ok(A.blendable(graph(0, 1), graph(2, 3)));
  assert.ok(!A.blendable(graph(0, 1), graph(2, 3, 4)));
  assert.ok(!A.blendable({ series: [{ points: [[0, 1]], parametric: true }] }, { series: [{ points: [[0, 1]], parametric: true }] }));
});

test("a play moves at a steady pace from where it starts and stops on the last frame", () => {
  const n = 40, ms = A.playMs(n);
  assert.ok(ms >= 2500 && ms <= 6000);
  assert.equal(A.playPosition(0, 0, n), 0);
  assert.equal(A.playPosition(0, ms / 2, n), (n - 1) / 2);
  assert.equal(A.playPosition(10, ms * 10, n), n - 1);
  assert.equal(A.playPosition(0, 100, 1), 0);
});

test("a calculation reads as one line: the name, the steps, the value; a long one keeps its ends", () => {
  assert.equal(A.workLine(["((2 + 1)^2 - 1)/2", "8/2", "4"], "4", "m"), "m = ((2 + 1)^2 - 1)/2 = 8/2 = 4");
  assert.equal(A.workLine(undefined, "4", "slope"), "\\mathrm{slope} = 4");
  assert.equal(A.workLine(["4"], "4"), "4");
  assert.equal(A.workLine(["a", "b", "c", "d", "e", "f", "g", "h"], "h", undefined, 6), "a = \\cdots = e = f = g = h");
});
