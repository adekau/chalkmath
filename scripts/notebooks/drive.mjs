// Run every math cell of a .chalk file through the native engine, in order, in one session,
// and print each cell's source, output text, summary, error and (optionally) step count.
//   node scripts/notebooks/drive.mjs notebooks/x.chalk [--steps] [--json out.json]
import { spawn } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { createInterface } from "node:readline";

const [file, ...flags] = process.argv.slice(2);
const showSteps = flags.includes("--steps");
const jsonOut = flags.includes("--json") ? flags[flags.indexOf("--json") + 1] : null;
const nb = JSON.parse(readFileSync(file, "utf8"));

const proc = spawn(new URL("../../engine/.lake/build/bin/mathengine", import.meta.url).pathname, [], { stdio: ["pipe", "pipe", "inherit"] });
const rl = createInterface({ input: proc.stdout });
const pending = [];
rl.on("line", (l) => { const r = pending.shift(); if (r) r(JSON.parse(l)); });
let id = 0;
const call = (method, params) => new Promise((res) => { pending.push(res); proc.stdin.write(JSON.stringify({ jsonrpc: "2.0", id: ++id, method, params }) + "\n"); });

const results = [];
let bad = 0;
for (let i = 0; i < nb.cells.length; i++) {
  const c = nb.cells[i];
  if (c.type && c.type !== "math") continue;
  const src = c.src;
  const isPlot = /^\s*(plot|epicycles|dft)\s*\(/.test(src);
  const r = await call(isPlot ? "engine.plot" : "engine.evaluate", { sessionId: "s", cellId: `c${i}`, source: src, showWork: true, paths: false });
  const res = r.result ?? r.error;
  const out = res?.rendered?.text ?? (res?.series ? `plot: ${res.series.length} series` : "");
  const line = res?.ok === false || r.error ? `  ✗ ${res?.message ?? JSON.stringify(res).slice(0, 200)}` : `  = ${out}${res?.summary ? `   [${res.summary}]` : ""}${res?.reading ? `   (${res.reading})` : ""}`;
  if (res?.ok === false || r.error) bad++;
  console.log(`[${i}] ${src}`);
  console.log(line);
  const steps = res?.derivation?.steps ?? [];
  if (showSteps && steps.length) for (const st of steps) console.log(`      · ${st.rule}: ${st.explanation ?? st.text ?? ""}`.slice(0, 160));
  else if (steps.length) console.log(`      (${steps.length} steps)`);
  results.push({ i, src, ok: !(res?.ok === false || r.error), text: out, summary: res?.summary, error: res?.message, steps: steps.length, hasse: res?.hasse });
}
proc.stdin.end();
console.log(`\n${results.length} cells, ${bad} errors`);
if (jsonOut) writeFileSync(jsonOut, JSON.stringify(results, null, 1));
process.exit(bad ? 1 : 0);
