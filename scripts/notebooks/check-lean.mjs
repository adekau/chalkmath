// Check the Lean cells of .chalk files with the Lean pinned in engine/lean-toolchain: a notebook's Lean cells,
// in order, are one Lean file (joined as packages/lean-editor does), and a cell with an error or a warning
// shows it to the reader. `#eval` output is printed.
//   node scripts/notebooks/check-lean.mjs notebooks/x.chalk [...]
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";

const SEPARATOR = "--⁅cell⁆";   // packages/lean-editor/src/index.ts
const engine = new URL("../../engine/", import.meta.url).pathname;   // elan picks the toolchain from here
const dir = mkdtempSync(path.join(tmpdir(), "chalk-lean-"));
let bad = 0;
for (const file of process.argv.slice(2)) {
  const cells = JSON.parse(readFileSync(file, "utf8")).cells.filter((c) => c.type === "lean").map((c) => c.src);
  if (!cells.length) { console.log(`${file}: no Lean cells`); continue; }
  const lean = path.join(dir, `${path.basename(file, ".chalk")}.lean`);
  writeFileSync(lean, cells.join(`\n${SEPARATOR}\n`));
  const r = spawnSync("lean", [lean], { cwd: engine, encoding: "utf8" });
  const out = `${r.stdout ?? ""}${r.stderr ?? ""}${r.error ? String(r.error) : ""}`;
  const failed = r.status !== 0 || /: (error|warning)/.test(out);
  if (failed) bad++;
  console.log(`${file}: ${cells.length} Lean cells, ${failed ? "FAILED" : "ok"}`);
  if (out.trim()) console.log(out.trim().replace(/^/gm, "  "));
}
process.exit(bad ? 1 : 0);
