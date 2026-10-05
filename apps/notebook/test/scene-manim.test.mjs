// A scene as a Manim script (src/scene-manim.ts): the captions made LaTeX, and a scene with every
// kind of object sampled by the native engine and written out as Python that compiles and carries the
// engine's samples. With MANIM set to a `manim` executable the script is also run, as a dry run.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { execFileSync } from "node:child_process";
import { existsSync, mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-manim-"));
const bundle = async (entry, file) => {
  const out = await build({ entryPoints: [new URL(entry, import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" });
  writeFileSync(join(dir, file), out.outputFiles[0].text);
  return import(pathToFileURL(join(dir, file)).href);
};
const S = await bundle("../src/scene.ts", "scene.mjs");
const M = await bundle("../src/scene-manim.ts", "scene-manim.mjs");

test("a caption's Markdown as LaTeX text: math kept, emphasis LaTeX's, reserved characters escaped", () => {
  assert.equal(M.captionTex("The **cosine** is *your* shadow: $\\cos t$, 50% & more"), "The \\textbf{cosine} is \\emph{your} shadow: $\\cos t$, 50\\% \\& more");
  assert.equal(M.captionTex("$$x_1$$ and ‹u_1›"), "$x_1$ and \\texttt{u\\_1}");
});

test("a scene's class name is a Python identifier", () => {
  assert.equal(M.className("04-determinants-6"), "Scene04Determinants6");
  assert.equal(M.className("circles and rotation"), "CirclesAndRotation");
});

const exe = new URL("../../../engine/.lake/build/bin/mathengine", import.meta.url).pathname;
const python = (() => { try { execFileSync("python3", ["--version"]); return "python3"; } catch { return null; } })();
test("every kind of object, sampled by the engine, as a Manim script that compiles", { skip: !existsSync(exe) && "no native engine build" }, async () => {
  const { leanNativeClient } = await import("@chalkmath/engine-host/lean-native");
  const c = leanNativeClient(exe);
  try {
    const script = [
      "clock t from 0 to 1",
      "let M = (1 - t)*[1, 0; 0, 1] + t*[2, 1; 1, 2]",
      "G = grid(M) color 2",
      "Sq = poly(0, M*[1; 0], M*[1; 1], M*[0; 1]) color 1",
      "C = curve(exp(i*s), s, 0, 2pi) faint color 6",
      "Wv = graph(sin(x), x, 0, 3*t + 0.1) color 3",
      "P = point(exp(i*pi*t)) thick",
      "R = arrow(0, M*[1; 0]) color 3",
      "D = segment(P, [1, 0]) dashed",
      "K = line(0, [1, 1]) dashed color 4",
      "Tr = trace(P)",
      'L = label(P, "e^{i\\pi t}")',
      'V = value(det(M), "\\det = ")',
      "E = eq(diff(exp(i*t), t))",
      "> show G, Sq, P, L | The **plane**, and $e^{i\\pi t}$.",
      "> show Tr, E; play t to 1 in 2s; work E | Both at once.",
      "> hide Sq; wait 1s",
    ].join("\n");
    const spec = S.parseScene(script);
    const replies = {};
    let k = 0;
    const ask = async (reqs) => { for (const r of reqs) replies[r.key] = await c.call(r.method, { sessionId: "manim", cellId: `m${k++}`, source: r.source, quiet: true, ...(r.showWork ? { showWork: true } : {}) }); };
    await ask(S.numberRequests(spec));
    await ask(S.sampleRequests(spec, (e) => /\bt\b/.test(e), S.numbersOf(spec, replies), S.vectorsOf(replies)));
    const data = S.build(spec, replies);
    const py = M.manimOfScene(data, "every object");
    assert.match(py, /^class EveryObject\(Scene\):$/m);
    // the samples are the engine's: P's last sample is e^(iπ) = -1, the grid's columns end at A's
    const row = (expr) => py.split("\n").find((l) => l.endsWith(`# ${expr}`));
    assert.match(row("exp(i*pi*t)"), /\(-1, 0\)\],/, "the point ends at -1");
    assert.match(row(S.columnPoint("((1 - t)*[1, 0; 0, 1] + t*[2, 1; 1, 2])", 1)), /\(2, 1\)\],/, "e1 lands on A's first column");
    assert.match(py, /"V": \[1, .*, 3\],/, "the determinant's samples run from 1 to 3");
    for (const kind of ["grid", "poly", "curve", "graph", "point", "arrow", "segment", "line", "trace", "label", "value"]) assert.match(py, new RegExp(`# ${kind} `), `a ${kind} is drawn`);
    // one AnimationGroup per beat, the clock played as the notebook plays it, the equation's work as morphs
    assert.equal(py.match(/self\.play\(AnimationGroup/g).length, 3);
    assert.match(py, /clock\.animate\(run_time=2, rate_func=rate_functions\.ease_in_out_quad\)\.set_value\(1\)/);
    assert.match(py, /TransformMatchingShapes/);
    assert.match(py, /\\\\textbf\{plane\}/, "the caption's bold is LaTeX's");
    const file = join(dir, "every_object.py");
    writeFileSync(file, py);
    if (python) execFileSync(python, ["-m", "py_compile", file]);
    if (process.env.MANIM) execFileSync(process.env.MANIM, ["--dry_run", "--disable_caching", "-ql", file, "EveryObject"], { cwd: dir, stdio: "pipe" });
  } finally { c.close?.(); }
});
