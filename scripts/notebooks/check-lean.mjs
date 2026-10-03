// Check the Lean of .chalk files with the Lean pinned in engine/lean-toolchain: a notebook's Lean cells and
// Lean exercises (each its statement and the author's proof), in order, are one Lean file (joined as
// packages/lean-editor does), and a cell with an error or a warning shows it to the reader. A lesson of a
// course with a Lean prelude is checked after the lessons before it. `#eval` output is printed.
//   node scripts/notebooks/check-lean.mjs notebooks/x.chalk [...]
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { leanForPrelude } from "../../packages/lean-editor/src/prelude.js";

const SEPARATOR = "--⁅cell⁆";   // packages/lean-editor/src/index.ts
const engine = new URL("../../engine/", import.meta.url).pathname;   // elan picks the toolchain from here
const dir = mkdtempSync(path.join(tmpdir(), "chalk-lean-"));
let bad = 0;
/** A notebook's Lean, as the page assembles it: Lean cells, and Lean exercises with the author's proofs. */
const leanOf = (cells) => cells.flatMap((c) => c.type === "lean" ? [c.src] : c.type === "exercise" && c.lean && c.src.trim() ? [`${c.src}\n${c.leanSolution ?? "  sorry"}`] : []);
// A lesson of a course with a Lean prelude sees the Lean of the lessons before it (notebooks/courses.json),
// as the page gives it (without the commands that only show something, leanForPrelude): it is checked
// with them in front.
const notebooks = new URL("../../notebooks/", import.meta.url).pathname;
const preludes = new Map();
try {
  for (const p of JSON.parse(readFileSync(path.join(notebooks, "courses.json"), "utf8")).projects) {
    if (!p.leanPrelude) continue;
    const parts = [];
    p.lessons.forEach((l) => {
      const file = path.join(notebooks, p.path, l.file);
      preludes.set(path.resolve(file), parts.join("\n\n"));
      const lean = leanOf(JSON.parse(readFileSync(file, "utf8")).cells);
      if (lean.length) parts.push(`-- ${l.title}\n${leanForPrelude(lean.join("\n\n"))}`);
    });
  }
} catch { /* no courses */ }
for (const file of process.argv.slice(2)) {
  // a Lean exercise is its statement and the author's proof, which must be there: it is what the reader's is
  // measured against, and what a course's later lessons see of it (their Lean prelude)
  const all = JSON.parse(readFileSync(file, "utf8")).cells;
  const unproved = all.filter((c) => c.type === "exercise" && c.lean && c.src.trim() && !c.leanSolution?.trim());
  if (unproved.length) { bad++; console.log(`${file}: FAILED, ${unproved.length} Lean exercise${unproved.length === 1 ? " has" : "s have"} no proof of the author's: ${unproved.map((c) => c.src.split("\n")[0]).join("; ")}`); continue; }
  const prelude = preludes.get(path.resolve(file));
  const cells = [...(prelude ? [prelude] : []), ...leanOf(all)];
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
