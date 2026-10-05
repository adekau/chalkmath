// Scenes (src/scene.ts): the script read, its mistakes named at their line, the beats laid out in
// time, and a scene sampled by the native engine and played: a point on the unit circle is where
// e^(it) says it is at each moment. The module is TypeScript for the page, so it is bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { existsSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-scene-"));
const out = await build({ entryPoints: [new URL("../src/scene.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" });
writeFileSync(join(dir, "scene.mjs"), out.outputFiles[0].text);
const S = await import(pathToFileURL(join(dir, "scene.mjs")).href);

const circle = `
clock t from 0 to 2pi
# the unit circle, a point on it, and its shadow
C = curve(exp(i*s), s, 0, 2pi) faint
P = point(exp(i*t))
R = arrow(0, P)
X = point(cos(t))
D = segment(P, X) dashed
W = trace(P)
L = label(P, "e^{it}")
E = eq(exptotrig(exp(i*pi)))
> show C, P, R | The unit circle, and a point on it.
> show X, D, W; play t to pi in 2s | Half way round, the shadow is at $-1$.
> work E | Euler's formula at $\\pi$.
`;

test("a scene's script: the clock, the objects with their styles, the beats with their captions", () => {
  const spec = S.parseScene(circle);
  assert.deepEqual(spec.clock, { name: "t", from: "0", to: "2pi" });
  assert.deepEqual(spec.objects.map((o) => `${o.name}:${o.kind}`), ["C:curve", "P:point", "R:arrow", "X:point", "D:segment", "W:trace", "L:label", "E:eq"]);
  assert.deepEqual(spec.objects[0].args, ["exp(i*s)", "s", "0", "2pi"]);
  assert.equal(spec.objects[0].style.faint, true);
  assert.equal(spec.objects[4].style.dashed, true);
  assert.equal(spec.beats.length, 3);
  assert.deepEqual(spec.beats[1].actions, [{ kind: "show", names: ["X", "D", "W"] }, { kind: "play", from: null, to: "pi", dur: 2 }]);
  assert.equal(spec.beats[2].caption, "Euler's formula at $\\pi$.");
});

test("a caption may hold a bar of its own, and an argument a comma inside parentheses", () => {
  const spec = S.parseScene('P = point(f(1, 2))\n> show P | the modulus $|z|$');
  assert.deepEqual(spec.objects[0].args, ["f(1, 2)"]);
  assert.equal(spec.beats[0].caption, "the modulus $|z|$");
});

test("mistakes are named at their line", () => {
  const err = (src) => { try { S.parseScene(src); return null; } catch (e) { return [e.line, e.message]; } };
  assert.deepEqual(err("P = point(1)\nQ = blob(2)"), [2, "unknown object \"blob\": point, curve, graph, arrow, segment, line, poly, grid, trace, label, eq, value"]);
  assert.deepEqual(err("P = point(1, 2)"), [1, "point takes 1 argument"]);
  assert.deepEqual(err("P = point(1)\n> show Q"), [2, "there is no object Q"]);
  assert.deepEqual(err("P = point(1) wobbly"), [1, 'unknown style "wobbly": faint, dashed, thick, or color 1 to 6']);
  assert.deepEqual(err("clock t from 0 to 1\n> play u to 1"), [2, "the scene's clock is t, not u"]);
  assert.deepEqual(err("P = point(1)\nW = trace(Q)"), [2, "trace follows a point, and Q is not one"]);
  assert.deepEqual(err("P = point(1)\n> work P"), [2, "work steps an equation (eq), and P is not one"]);
  assert.deepEqual(err("> wait soon"), [1, 'a duration is seconds, like 2s, not "soon"']);
});

test("the engine is asked once per expression, the moving curves for frames, all of it quiet to the session", () => {
  const spec = S.parseScene(circle);
  const nums = S.numberRequests(spec);
  assert.deepEqual(nums.filter((r) => r.key.startsWith("num:")).map((r) => r.source), ["N(0)", "N(2pi)", "N(pi)"]);
  assert.deepEqual(nums.filter((r) => r.key.startsWith("is:")).map((r) => r.source), ["exp(i*t)", "cos(t)"],
    "each point's expression is asked what it is, once: an arrow to P asks about P's");
  const reqs = [...nums, ...S.sampleRequests(spec, (e) => /\bt\b/.test(e), { "0": 0, "2pi": 6.283185307179586, pi: 3.141592653589793 })];
  const by = Object.fromEntries(reqs.map((r) => [r.key, r]));
  assert.equal(by["pt:exp(i*t)"].source, "plot(exp(i*t), t, 0, 2pi)");
  assert.equal(by["pt:0"].source, "plot(0, t, 0, 2pi)");
  assert.equal(by["cv:C"].method, "engine.plot");
  assert.equal(by["num:pi"].source, "N(pi)");
  assert.equal(by["eq:E"].method, "engine.check");
  const moving = S.sampleRequests(S.parseScene("clock t from 0 to 2pi\nA = curve(s*exp(i*t), s, 0, 1)"), (e) => /\bt\b/.test(e), { "0": 0, "2pi": 6.283185307179586 });
  assert.equal(moving.find((r) => r.key === "cv:A").method, "engine.manipulate");
  assert.equal(moving.find((r) => r.key === "cv:A").source, "manipulate(plot(s*exp(i*t), s, 0, 1), t, 0, 6.283185307179586, 61)", "a manipulate's range is the numbers the engine gave");
});

test("beats in time: each long enough to read, a play as long as it says; the clock eased between", () => {
  const spec = S.parseScene("clock t from 0 to 10\nP = point(t)\n> show P\n> play t to 10 in 4s");
  const tl = S.compile(spec, { "0": 0, "10": 10 }, {});
  assert.equal(tl.beats.length, 2);
  assert.ok(Math.abs(tl.beats[1].end - tl.beats[1].start - 4) < 1e-9);
  assert.equal(S.clockAt(tl, 0, tl.beats[1].start), 0);
  assert.ok(Math.abs(S.clockAt(tl, 0, tl.beats[1].start + 2) - 5) < 1e-9, "half way through an eased play is half way");
  assert.equal(S.clockAt(tl, 0, tl.total), 10);
  assert.equal(S.opacityAt(tl, "P", 0), 0);
  assert.equal(S.opacityAt(tl, "P", S.FADE), 1);
  assert.equal(S.opacityAt(tl, "Q", 0), 1, "an object no beat mentions is there from the start");
});

test("a path's sample between the engine's, and a gap where it has none", () => {
  const pts = [[0, 0], [1, 0], null, [3, 0]];
  assert.deepEqual(S.sampleAt(pts, 0, 3, 0.5), [0.5, 0]);
  assert.deepEqual(S.sampleAt(pts, 0, 3, 1.5), [1, 0]);
  assert.deepEqual(S.sampleAt(pts, 0, 3, 3), [3, 0]);
});

test("vectors are points: a literal, an expression the engine says is one, a grid's columns", () => {
  const spec = S.parseScene("clock t from 0 to 1\nV = point(A*[1; 1])\nG = grid((1-t)*[1,0;0,1] + t*A)\nS = poly(0, [1, 0], V, [0, 1]) color 2\nK = line(0, V) dashed\nR = arrow([1, 2][[1]], V)\nD = value(det(A), \"\\det A = \")");
  assert.equal(S.anchorOf(spec, "V"), "A*[1; 1]", "until the engine says it is a vector");
  const vectors = S.vectorsOf({ "is:A*[1; 1]": { ok: true, rendered: { text: "[3; f(1, 2)]" } }, "is:exp(i*t)": { ok: true, rendered: { text: "exp(i*t)" } }, "is:B": { ok: true, rendered: { text: "[1, 2; 3, 4]" } } });
  assert.deepEqual(vectors, ["A*[1; 1]"]);
  assert.equal(S.anchorOf(spec, "V", vectors), "(A*[1; 1])[[1]] + i*(A*[1; 1])[[2]]");
  assert.equal(S.anchorOf(spec, "[1, 0]"), "([1, 0])[[1]] + i*([1, 0])[[2]]");
  assert.equal(S.anchorOf(spec, "[1, 2][[1]]"), "[1, 2][[1]]", "an indexed vector is a number, not a vector");
  assert.ok(S.numberRequests(spec).some((r) => r.key === "is:A*[1; 1]"));
  assert.ok(!S.numberRequests(spec).some((r) => r.key === "is:[1, 0]"), "a literal is not asked about");
  const reqs = S.sampleRequests(spec, (e) => /\bt\b/.test(e), { "0": 0, "1": 1 }, vectors);
  assert.ok(reqs.some((r) => r.key === "pt:(A*[1; 1])[[1]] + i*(A*[1; 1])[[2]]"));
  const keys = reqs.map((r) => r.key);
  assert.ok(keys.includes("pt:((1-t)*[1,0;0,1] + t*A)[[1, 1]] + i*((1-t)*[1,0;0,1] + t*A)[[2, 1]]"), "the grid's first column");
  assert.ok(keys.includes("pt:((1-t)*[1,0;0,1] + t*A)[[1, 2]] + i*((1-t)*[1,0;0,1] + t*A)[[2, 2]]"), "and its second");
  assert.ok(keys.includes("val:det(A)"));
  assert.equal(spec.objects.find((o) => o.name === "S").args.length, 4);
  const err = (src) => { try { S.parseScene(src); return null; } catch (e) { return [e.line, e.message]; } };
  assert.deepEqual(err("S = poly(0, 1)"), [1, "poly takes three corners or more"]);
  assert.deepEqual(err('D = value(1, x)'), [1, 'a value\'s text is TeX in quotes: value(1, "z")']);
  assert.deepEqual(err("V = point([1, 2])\nW = trace(V)"), null, "a vector point can be traced");
});

test("a script's names are written in where they are used, each with the names before it", () => {
  const spec = S.parseScene("clock t from 0 to 1\nlet A = [2, 1; 1, 2]\nlet M = (1 - t)*[1, 0; 0, 1] + t*A\nG = grid(M)\nV = point(M*[1; 0])\nL = label(V, \"M e_1\")\nAt = point(At2)");
  assert.deepEqual(spec.lets, { A: "[2, 1; 1, 2]", M: "(1 - t)*[1, 0; 0, 1] + t*([2, 1; 1, 2])" });
  assert.equal(spec.objects[0].args[0], "((1 - t)*[1, 0; 0, 1] + t*([2, 1; 1, 2]))");
  assert.equal(spec.objects[1].args[0], "((1 - t)*[1, 0; 0, 1] + t*([2, 1; 1, 2]))*[1; 0]");
  assert.equal(spec.objects[2].args[1], '"M e_1"', "a label's TeX is left as it is");
  assert.equal(spec.objects[3].args[0], "At2", "a name is replaced as a whole word only");
  const err = (src) => { try { S.parseScene(src); return null; } catch (e) { return [e.line, e.message]; } };
  assert.deepEqual(err("let M = 1\nlet M = 2"), [2, "M is already a name"]);
  assert.deepEqual(err("let M = 1\nM = point(2)"), [2, "M is already a name (line 1)"]);
  assert.deepEqual(err("let = 1"), [1, "write a name as: let M = [1, 2; 3, 4]"]);
});

test("a value reads two decimals at most, and never -0", () => {
  assert.equal(S.formatValue(2), "2");
  assert.equal(S.formatValue(-0.001), "0");
  assert.equal(S.formatValue(1.504), "1.5");
  assert.equal(S.formatValue(-2.25), "-2.25");
  assert.equal(S.formatValue(10), "10");
});

const exe = new URL("../../../engine/.lake/build/bin/mathengine", import.meta.url).pathname;
test("a scene sampled by the engine: the point is e^(it), its shadow cos t, the equation stepped to -1", { skip: !existsSync(exe) && "no native engine build" }, async () => {
  const { leanNativeClient } = await import("@chalkmath/engine-host/lean-native");
  const c = leanNativeClient(exe);
  try {
    const spec = S.parseScene(circle);
    const replies = {};
    let k = 0;
    const ask = async (reqs) => { for (const r of reqs) replies[r.key] = await c.call(r.method, { sessionId: "scene", cellId: `s${k++}`, source: r.source, quiet: true, ...(r.showWork ? { showWork: true } : {}) }); };
    await ask(S.numberRequests(spec));
    await ask(S.sampleRequests(spec, (e) => /\bt\b/.test(e), S.numbersOf(spec, replies), S.vectorsOf(replies)));
    const data = S.build(spec, replies);
    assert.ok(Math.abs(data.clock.to - 2 * Math.PI) < 1e-9);
    // the second beat plays t from 0 to π: at its end the point is at -1 and the shadow under it
    const end = data.timeline.beats[1].end;
    const f = S.frameAt(data, end);
    assert.ok(Math.abs(f.clock - Math.PI) < 1e-9);
    const P = f.items.find((i) => i.name === "P"), X = f.items.find((i) => i.name === "X");
    assert.ok(Math.abs(P.at[0] + 1) < 1e-3 && Math.abs(P.at[1]) < 1e-3, `P at ${P.at}`);
    assert.ok(Math.abs(X.at[0] + 1) < 1e-3 && X.at[1] === 0, `X at ${X.at}`);
    // a quarter of the way: e^(iπ/2) = i
    const quarter = S.frameAt(data, data.timeline.beats[1].start + 1);
    const Q = quarter.items.find((i) => i.name === "P");
    assert.ok(Math.abs(Q.at[0]) < 2e-2 && Math.abs(Q.at[1] - 1) < 2e-2, `P at ${Q.at}`);
    // the trace runs from 1 (where the clock was when it was shown) to the point
    const W = f.items.find((i) => i.name === "W");
    assert.ok(Math.abs(W.pts[0][0] - 1) < 1e-3 && Math.abs(W.pts.at(-1)[0] + 1) < 1e-3);
    // the equation starts as typed and ends as the engine's answer
    assert.ok(data.eqs.E.length >= 2);
    const last = S.frameAt(data, data.timeline.total).eqs.find((e) => e.name === "E");
    assert.equal(last.to, data.eqs.E.at(-1));
    assert.equal(last.to.replace(/\s/g, ""), "-1");
    // the window takes in the circle
    const [x0, x1, y0, y1] = data.window;
    assert.ok(x0 < -1 && x1 > 1 && y0 < -1 && y1 > 1);
    // a curve that moves with the clock: the wave unrolled to where the clock is
    const wave = S.parseScene("clock t from 0.01 to 2pi\nW = graph(sin(x), x, 0, t)\n> play t to pi in 2s");
    const wr = {};
    for (const r of S.numberRequests(wave)) wr[r.key] = await c.call(r.method, { sessionId: "scene", cellId: `w${k++}`, source: r.source, quiet: true });
    for (const r of S.sampleRequests(wave, (e) => /\bt\b/.test(e), S.numbersOf(wave, wr))) wr[r.key] = await c.call(r.method, { sessionId: "scene", cellId: `w${k++}`, source: r.source, quiet: true });
    const wd = S.build(wave, wr);
    const wf = S.frameAt(wd, wd.timeline.total);
    const tip = wf.items[0].pts.filter(Boolean).at(-1);
    assert.ok(Math.abs(tip[0] - Math.PI) < 0.06 && Math.abs(tip[1]) < 0.06, `the wave ends at (${tip}) when the clock is at π`);
    // a grid sheared by a moving matrix: the columns where the matrix sends the basis, its determinant read off
    const shear = S.parseScene("clock t from 0 to 1\nG = grid([1, t; 0, 1])\nV = point([1, t; 0, 1]*[1; 1])\nS = poly(0, [1, 0], V, [0, 1])\nD = value(det([2, t; 0, 1]), \"\\det = \")\n> play t to 1 in 2s");
    const sr = {};
    for (const r of S.numberRequests(shear)) sr[r.key] = await c.call(r.method, { sessionId: "scene", cellId: `g${k++}`, source: r.source, quiet: true });
    for (const r of S.sampleRequests(shear, (e) => /\bt\b/.test(e), S.numbersOf(shear, sr), S.vectorsOf(sr))) sr[r.key] = await c.call(r.method, { sessionId: "scene", cellId: `g${k++}`, source: r.source, quiet: true });
    const sd = S.build(shear, sr);
    const gf = S.frameAt(sd, sd.timeline.total), grid = gf.items.find((i) => i.kind === "grid");
    assert.deepEqual(grid.e1.map((x) => +x.toFixed(6)), [1, 0], "e1 stays put");
    assert.deepEqual(grid.e2.map((x) => +x.toFixed(6)), [1, 1], "e2 is sheared to (1, 1)");
    assert.deepEqual(gf.items.find((i) => i.name === "V").at.map((x) => +x.toFixed(6)), [2, 1]);
    assert.equal(gf.items.find((i) => i.kind === "poly").pts.length, 4);
    assert.equal(gf.eqs.find((e) => e.name === "D").to, "\\det = 2");
    // a quiet sample is no evaluation: the session's next one is In[1]
    const r = await c.call("engine.evaluate", { sessionId: "scene", cellId: "after", source: "1 + 1" });
    assert.equal(r.label, 1);
  } finally { c.close?.(); }
});
