// Run every math cell of a .chalk file through the native engine, in order, in one session,
// and print each cell's source, output text, summary, error and (optionally) step count.
//   node scripts/notebooks/drive.mjs notebooks/x.chalk [--steps] [--json out.json]
//
// With --check, every file given is compared with its golden outcomes in notebooks/golden/<name>.tsv:
// each cell's answer, or its error (a notebook may show one on purpose: the poset that is not
// antisymmetric), must be the one the notebook was written with. --update writes the golden files.
//   node scripts/notebooks/drive.mjs --check notebooks/*.chalk notebooks/courses/*/*.chalk
//   node scripts/notebooks/drive.mjs --update notebooks/*.chalk notebooks/courses/*/*.chalk
//
// Exercise cells are checked through `engine.check`: the question must evaluate, to its golden answer.
// A scene cell is read and sampled as the page does it (apps/notebook/src/scene.ts, quiet requests):
// its outcome is how many objects and beats it has and how long it plays, or the mistake at its line.
// With --manim <dir>, each scene is also written as a Manim script, <dir>/<notebook>-<cell>.py, for
// Manim to render on this computer (apps/notebook/src/scene-manim.ts):
//   node scripts/notebooks/drive.mjs --manim out notebooks/courses/linear-algebra/04-determinants.chalk
//   manim -pqh out/04-determinants-6.py
// A cell that reads a file (import("…"), ⟦name⟧) is the page's to evaluate (files.ts), not the
// engine's; it is skipped, and so is every cell that uses a name such a cell binds.
import { spawn } from "node:child_process";
import { readFileSync, writeFileSync, existsSync, mkdirSync } from "node:fs";
import { createInterface } from "node:readline";
import path from "node:path";
import { tmpdir } from "node:os";
import { pathToFileURL } from "node:url";
import { build as esbuild } from "esbuild";

// the page's scene module, bundled for Node
const sceneJs = path.join(tmpdir(), `chalk-drive-scene-${process.pid}.mjs`);
writeFileSync(sceneJs, (await esbuild({ entryPoints: [new URL("../../apps/notebook/src/scene.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" })).outputFiles[0].text);
const Scene = await import(pathToFileURL(sceneJs).href);
const manimJs = path.join(tmpdir(), `chalk-drive-manim-${process.pid}.mjs`);
writeFileSync(manimJs, (await esbuild({ entryPoints: [new URL("../../apps/notebook/src/scene-manim.ts", import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" })).outputFiles[0].text);
const Manim = await import(pathToFileURL(manimJs).href);

const args = process.argv.slice(2);
const flags = new Set(args.filter((a) => a.startsWith("--")));
const jsonOut = flags.has("--json") ? args[args.indexOf("--json") + 1] : null;
const manimDir = flags.has("--manim") ? args[args.indexOf("--manim") + 1] : null;
const files = args.filter((a, k) => !a.startsWith("--") && args[k - 1] !== "--json" && args[k - 1] !== "--manim");
const showSteps = flags.has("--steps");
const golden = flags.has("--check") || flags.has("--update");
const goldenDir = new URL("../../notebooks/golden/", import.meta.url).pathname;

const proc = spawn(new URL("../../engine/.lake/build/bin/mathengine", import.meta.url).pathname, [], { stdio: ["pipe", "pipe", "inherit"] });
const rl = createInterface({ input: proc.stdout });
const pending = [];
// a line that is not JSON (Lean aborting on a stack overflow) answers the oldest call with an error
rl.on("line", (l) => {
  const r = pending.shift(); if (!r) return;
  let reply;
  try { reply = JSON.parse(l); } catch { reply = { error: { message: `the engine answered with a line that is not JSON: ${l.slice(0, 80)}` } }; }
  r(reply);
});
// an engine that stops (or never started) fails every call it owed, so the run ends with a reason, not a hang
proc.on("exit", (code, signal) => { for (const r of pending.splice(0)) r({ error: { message: `the engine stopped (${signal ?? `exit code ${code}`})` } }); });
proc.on("error", (e) => { for (const r of pending.splice(0)) r({ error: { message: `the engine could not run: ${e.message}` } }); });
proc.stdin.on("error", () => {});
let id = 0;
const call = (method, params) => new Promise((res) => {
  if (proc.exitCode !== null) { res({ error: { message: `the engine stopped (exit code ${proc.exitCode})` } }); return; }
  pending.push(res); proc.stdin.write(JSON.stringify({ jsonrpc: "2.0", id: ++id, method, params }) + "\n");
});

/** The identifiers of a source, roughly as the page's tokenizer reads them. */
const names = (src) => src.match(/[A-Za-z_Ͱ-Ͽℯ][A-Za-z0-9_Ͱ-Ͽℯ']*/gu) ?? [];
const esc = (s) => String(s ?? "").replace(/\\/g, "\\\\").replace(/\t/g, "\\t").replace(/\n/g, "\\n");

/** Every cell's outcome, one line each: `= answer`, `✗ error`, or `page` (a file the page evaluates). */
async function drive(file, session) {
  const nb = JSON.parse(readFileSync(file, "utf8"));
  const results = [];
  const pageNames = new Set();   // bound to files: the page's
  for (let i = 0; i < nb.cells.length; i++) {
    const c = nb.cells[i];
    const exercise = c.type === "exercise" && !c.lean;   // a Lean exercise is Lean's to check (check-lean.mjs)
    if (c.type === "scene" && c.src.trim()) { results.push(await driveScene(c.src, session, i, `${path.basename(file, ".chalk")}-${i}`)); continue; }
    if (c.type && c.type !== "math" && !exercise) continue;
    const src = c.src;
    if (!src.trim()) continue;
    const bind = /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)/.exec(src)?.[1];
    if (/import\s*\(|⟦/.test(src) || names(src).some((n) => n !== bind && pageNames.has(n))) {
      if (bind) pageNames.add(bind);
      results.push({ i, src, ok: true, outcome: "page", text: "", steps: 0 });
      continue;
    }
    if (bind) pageNames.delete(bind);
    const isPlot = /^\s*(plot|epicycles|dft)\s*\(/.test(src), isManip = /^\s*manipulate\s*\(/.test(src);
    const method = exercise ? "engine.check" : isPlot ? "engine.plot" : isManip ? "engine.manipulate" : "engine.evaluate";
    const r = await call(method, { sessionId: session, cellId: `c${i}`, source: src, showWork: true, paths: false });
    const res = r.result ?? r.error;
    const failed = res?.ok === false || !!r.error;
    const text = res?.rendered?.text ?? (res?.series ? `plot: ${res.series.length} series` : "");
    const message = res?.error?.message ?? res?.message ?? (failed ? JSON.stringify(res).slice(0, 200) : "");
    // a manipulate cell: its first frame's answer, and how many frames to the last one's
    const frames = res?.frames?.length ? `   [${res.frames.length} frames of ${res.param}; at ${res.param} = ${res.frames.at(-1).valueRendered.text}: ${res.frames.at(-1).rendered.text}]` : "";
    const outcome = failed ? `✗ ${message}` : `= ${text}${frames}${res?.summary ? `   [${res.summary}]` : ""}${res?.reading ? `   (${res.reading})` : ""}`;
    const steps = res?.derivation?.steps ?? [];
    results.push({ i, src, ok: !failed, outcome, text, summary: res?.summary, error: failed ? message : undefined, steps: steps.length, hasse: res?.hasse, stepList: steps });
  }
  return results;
}

/** A scene cell, as the page plays it: every request quiet, so the session is as the cells left it. */
async function driveScene(src, session, i, name) {
  try {
    const spec = Scene.parseScene(src);
    const clock = spec.clock.name;
    const moves = (e) => names(e).includes(clock);
    const replies = {};
    let k = 0;
    const ask = async (reqs) => {
      for (const q of reqs) {
        const r = await call(q.method, { sessionId: session, cellId: `c${i}~${k++}`, source: q.source, quiet: true, ...(q.showWork ? { showWork: true } : {}) });
        replies[q.key] = r.result ?? { ok: false, error: r.error };
      }
    };
    await ask(Scene.numberRequests(spec));
    await ask(Scene.sampleRequests(spec, moves, Scene.numbersOf(spec, replies), Scene.vectorsOf(replies)));
    const data = Scene.build(spec, replies);
    if (manimDir) {
      mkdirSync(manimDir, { recursive: true });
      writeFileSync(path.join(manimDir, `${name}.py`), Manim.manimOfScene(data, name));
    }
    const outcome = `scene: ${spec.objects.length} objects, ${data.timeline.beats.length} beats, ${data.timeline.total.toFixed(1)} s`;
    return { i, src, ok: true, outcome, text: outcome, steps: 0 };
  } catch (e) {
    const message = e.line ? `line ${e.line}: ${e.message}` : String(e.message ?? e);
    return { i, src, ok: false, outcome: `✗ ${message}`, text: "", error: message, steps: 0 };
  }
}

let bad = 0;
const all = [];
for (const [k, file] of files.entries()) {
  const results = await drive(file, `s${k}`);
  all.push(...results.map((r) => ({ file, ...r, stepList: undefined })));
  if (!golden) {
    for (const r of results) {
      console.log(`[${r.i}] ${r.src}`);
      console.log(`  ${r.outcome}`);
      if (showSteps && r.stepList?.length) for (const st of r.stepList) console.log(`      · ${st.rule}: ${st.explanation ?? st.text ?? ""}`.slice(0, 160));
      else if (r.steps) console.log(`      (${r.steps} steps)`);
      if (!r.ok) bad++;
    }
    console.log(`\n${results.length} cells, ${results.filter((r) => !r.ok).length} errors`);
    continue;
  }
  const tsv = results.map((r) => `${r.i}\t${esc(r.src)}\t${esc(r.outcome)}`).join("\n") + "\n";
  // notebooks/x.chalk → golden/x.tsv; notebooks/courses/c/l.chalk → golden/courses-c-l.tsv
  const rel = path.relative(path.join(goldenDir, ".."), path.resolve(file)).replace(/\.chalk$/, "");
  const gfile = path.join(goldenDir, `${rel.startsWith("..") ? path.basename(rel) : rel.split(path.sep).join("-")}.tsv`);
  if (flags.has("--update")) {
    mkdirSync(goldenDir, { recursive: true });
    writeFileSync(gfile, tsv);
    console.log(`${file}: ${results.length} cells written to ${path.relative(process.cwd(), gfile)}`);
    continue;
  }
  if (!existsSync(gfile)) { console.log(`${file}: no golden outcomes (run with --update)`); bad++; continue; }
  const want = readFileSync(gfile, "utf8").split("\n").filter(Boolean);
  const got = tsv.split("\n").filter(Boolean);
  const diffs = [];
  for (let k = 0; k < Math.max(want.length, got.length); k++) if (want[k] !== got[k]) diffs.push([want[k], got[k]]);
  if (diffs.length) {
    bad++;
    console.log(`${file}: ${diffs.length} cell${diffs.length === 1 ? "" : "s"} differ from ${path.relative(process.cwd(), gfile)}`);
    for (const [w, g] of diffs.slice(0, 20)) console.log(`  expected: ${w ?? "(nothing)"}\n  actual:   ${g ?? "(nothing)"}`);
    if (diffs.length > 20) console.log(`  … and ${diffs.length - 20} more`);
  } else console.log(`${file}: ${results.length} cells as written`);
}
proc.stdin.end();
if (jsonOut) writeFileSync(jsonOut, JSON.stringify(all, null, 1));
process.exit(bad ? 1 : 0);
