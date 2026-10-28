// Check the Lean of .chalk files with the Lean pinned in engine/lean-toolchain: a notebook's Lean cells and
// Lean exercises (each its statement and the author's proof), in order, are one Lean file (joined as
// packages/lean-editor does), and a cell with an error or a warning shows it to the reader. A lesson of a
// course with a Lean prelude is checked after the lessons before it. `#eval` output is printed.
//   node scripts/notebooks/check-lean.mjs notebooks/x.chalk [...]
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { authorLean, preludePart, preludeOf, moduleName, moduleSource, moduleEntry, importedPrelude } from "../../packages/lean-editor/src/prelude.js";

const SEPARATOR = "--⁅cell⁆";   // packages/lean-editor/src/index.ts
const engine = new URL("../../engine/", import.meta.url).pathname;   // elan picks the toolchain from here
const dir = mkdtempSync(path.join(tmpdir(), "chalk-lean-"));
let bad = 0;
// A lesson of a course with a Lean prelude sees the Lean of the lessons before it (notebooks/courses.json),
// as the page gives it (without the commands that only show something, preludePart): it is checked with
// them in front, inline, and as the page gives it when the bundle has the course's modules
// (scripts/lean-courses.mjs): an import of the module that holds them, and the scope they leave. Here the
// modules are compiled by native Lean, from the same sources.
const notebooks = new URL("../../notebooks/", import.meta.url).pathname;
const preludes = new Map();
const modulesDir = path.join(dir, "modules");
const compiled = new Map();   // course → how many of its modules compiled
/** Compiles a course's first `upTo` modules (once), and says whether they did. */
function modulesOf(course, parts, upTo) {
  for (let m = (compiled.get(course) ?? 0) + 1; m <= upTo; m++) {
    const name = moduleName(course, m), file = path.join(modulesDir, `${name.replaceAll(".", "/")}.lean`);
    mkdirSync(path.dirname(file), { recursive: true });
    writeFileSync(file, moduleSource(course, parts, m));
    const r = spawnSync("lean", ["-R", modulesDir, "-o", file.replace(/\.lean$/, ".olean"), file], { cwd: engine, encoding: "utf8", env: { ...process.env, LEAN_PATH: modulesDir } });
    const out = `${r.stdout ?? ""}${r.stderr ?? ""}`;
    if (r.status !== 0 || /: error/.test(out)) { bad++; console.log(`${course}: FAILED to compile its prelude's module ${name}\n${out.trim().replace(/^/gm, "  ")}`); return false; }
    compiled.set(course, m);
  }
  return true;
}
try {
  for (const p of JSON.parse(readFileSync(path.join(notebooks, "courses.json"), "utf8")).projects) {
    if (!p.leanPrelude) continue;
    const parts = [];
    const here = () => ({ course: p.id, parts: [...parts] });
    p.lessons.forEach((l) => {
      const file = path.join(notebooks, p.path, l.file);
      preludes.set(path.resolve(file), here());
      parts.push(preludePart(l.title, JSON.parse(readFileSync(file, "utf8")).cells));
      // a lesson's applications see its Lean too; later lessons do not see theirs
      for (const ap of l.apps ?? []) preludes.set(path.resolve(path.join(notebooks, p.path, ap.file)), here());
    });
  }
} catch { /* no courses */ }
/** Lean `cells` as one file: ok, or what Lean says. */
function checkLean(name, cells, env) {
  const lean = path.join(dir, `${name}.lean`);
  writeFileSync(lean, cells.join(`\n${SEPARATOR}\n`));
  const r = spawnSync("lean", [lean], { cwd: engine, encoding: "utf8", ...(env ? { env } : {}) });
  const out = `${r.stdout ?? ""}${r.stderr ?? ""}${r.error ? String(r.error) : ""}`;
  return { failed: r.status !== 0 || /: (error|warning)/.test(out), out };
}
for (const file of process.argv.slice(2)) {
  // a Lean exercise is its statement and the author's proof, which must be there: it is what the reader's is
  // measured against, and what a course's later lessons see of it (their Lean prelude)
  const all = JSON.parse(readFileSync(file, "utf8")).cells;
  const unproved = all.filter((c) => c.type === "exercise" && c.lean && c.src.trim() && (!c.leanSolution?.trim() || (c.leanDef !== undefined && !c.leanDefSolution?.trim())));
  if (unproved.length) { bad++; console.log(`${file}: FAILED, ${unproved.length} Lean exercise${unproved.length === 1 ? " has" : "s have"} no proof (or, asking for a definition, no definition) of the author's: ${unproved.map((c) => c.src.split("\n")[0]).join("; ")}`); continue; }
  const pre = preludes.get(path.resolve(file));
  const prelude = pre ? preludeOf(pre.parts) : "";
  const own = authorLean(all);
  const cells = [...(prelude ? [prelude] : []), ...own];
  if (!cells.length) { console.log(`${file}: no Lean cells`); continue; }
  const base = path.basename(file, ".chalk");
  const inline = checkLean(base, cells);
  // and with the prelude imported, as the page gives it with the course's modules
  let imported = null;
  if (prelude && own.length && modulesOf(pre.course, pre.parts, pre.parts.length)) {
    const src = importedPrelude(moduleEntry(pre.course, pre.parts, pre.parts.length), prelude);
    imported = src === null ? { failed: true, out: "the prelude is not the one its module holds" }
      : checkLean(`${base}-imported`, [src, ...own], { ...process.env, LEAN_PATH: modulesDir });
  }
  const failed = inline.failed || !!imported?.failed;
  if (failed) bad++;
  console.log(`${file}: ${cells.length} Lean cells, ${failed ? "FAILED" : "ok"}${imported ? ` (inline and imported: ${inline.failed ? "inline failed" : "inline ok"}, ${imported.failed ? "imported failed" : "imported ok"})` : ""}`);
  if (inline.out.trim()) console.log(inline.out.trim().replace(/^/gm, "  "));
  if (imported?.failed && imported.out.trim()) console.log(`  with its prelude imported:\n${imported.out.trim().replace(/^/gm, "    ")}`);
}
process.exit(bad ? 1 : 0);
