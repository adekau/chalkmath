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
// A cell that reads a file (import("…"), ⟦name⟧) is the page's to evaluate (files.ts), not the
// engine's; it is skipped, and so is every cell that uses a name such a cell binds.
import { spawn } from "node:child_process";
import { readFileSync, writeFileSync, existsSync, mkdirSync } from "node:fs";
import { createInterface } from "node:readline";
import path from "node:path";

const args = process.argv.slice(2);
const flags = new Set(args.filter((a) => a.startsWith("--")));
const jsonOut = flags.has("--json") ? args[args.indexOf("--json") + 1] : null;
const files = args.filter((a, k) => !a.startsWith("--") && args[k - 1] !== "--json");
const showSteps = flags.has("--steps");
const golden = flags.has("--check") || flags.has("--update");
const goldenDir = new URL("../../notebooks/golden/", import.meta.url).pathname;

const proc = spawn(new URL("../../engine/.lake/build/bin/mathengine", import.meta.url).pathname, [], { stdio: ["pipe", "pipe", "inherit"] });
const rl = createInterface({ input: proc.stdout });
const pending = [];
rl.on("line", (l) => { const r = pending.shift(); if (r) r(JSON.parse(l)); });
let id = 0;
const call = (method, params) => new Promise((res) => { pending.push(res); proc.stdin.write(JSON.stringify({ jsonrpc: "2.0", id: ++id, method, params }) + "\n"); });

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
    const exercise = c.type === "exercise";
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
    const isPlot = /^\s*(plot|epicycles|dft)\s*\(/.test(src);
    const method = exercise ? "engine.check" : isPlot ? "engine.plot" : "engine.evaluate";
    const r = await call(method, { sessionId: session, cellId: `c${i}`, source: src, showWork: true, paths: false });
    const res = r.result ?? r.error;
    const failed = res?.ok === false || !!r.error;
    const text = res?.rendered?.text ?? (res?.series ? `plot: ${res.series.length} series` : "");
    const message = res?.error?.message ?? res?.message ?? (failed ? JSON.stringify(res).slice(0, 200) : "");
    const outcome = failed ? `✗ ${message}` : `= ${text}${res?.summary ? `   [${res.summary}]` : ""}${res?.reading ? `   (${res.reading})` : ""}`;
    const steps = res?.derivation?.steps ?? [];
    results.push({ i, src, ok: !failed, outcome, text, summary: res?.summary, error: failed ? message : undefined, steps: steps.length, hasse: res?.hasse, stepList: steps });
  }
  return results;
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
