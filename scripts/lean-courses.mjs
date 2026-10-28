// Compiles each course's Lean prelude (a project with `leanPrelude` in notebooks/courses.json) into a chain of
// modules the browser's Lean imports instead of elaborating it each time a lesson opens: module
// `ChalkCourse.<Course>.L<m>` holds lesson m's Lean (what the prelude takes of it, preludePart) and imports
// module m - 1 (packages/lean-editor/src/prelude.js). They are compiled by the wasm Lean's command-line
// driver (bin/lean.js, the release's lean-wasm-cli.tar.gz): its oleans are 32-bit, as the browser's Lean
// reads them, where a native olean is a 64-bit memory image.
//
// Writes, into the bundle's lean/ directory, `courses/<course>-<hash>.pack.gz` (the course's oleans, packed
// as the library is, named by their contents so a browser keeps one as long as it is the same) and
// `lean-courses.json`, which the notebook reads: for each course, its pack and, for each module, the prelude
// it stands for (its length and hash) and the scope that prelude leaves. A lesson whose prelude is not one of
// them (a notebook saved from an older course) keeps it inline.
//
// A module is compiled again only when its source or the modules before it change: the oleans are kept in
// `.cache/lean-courses/`, under a hash of the compiler, the source and the hashes before it.
//   node scripts/lean-courses.mjs <compiler dir (bin/lean.js, lib/lean)> <out dir>
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { copyFileSync, existsSync, mkdirSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { cpus } from "node:os";
import path from "node:path";
import { gzipSync } from "node:zlib";
import { pathToFileURL } from "node:url";
import { preludePart, moduleName, moduleSource, moduleEntry } from "../packages/lean-editor/src/prelude.js";

const root = path.resolve(import.meta.dirname, "..");

/** The courses with a Lean prelude, each with its lessons' parts (null: a lesson with no Lean), and how many
 *  modules it needs: a lesson sees the lessons before it, and its applications see it too. */
export function coursePreludes(notebooks = path.join(root, "notebooks")) {
  const out = [];
  for (const p of JSON.parse(readFileSync(path.join(notebooks, "courses.json"), "utf8")).projects) {
    if (!p.leanPrelude) continue;
    const parts = p.lessons.map((l) => preludePart(l.title, JSON.parse(readFileSync(path.join(notebooks, p.path, l.file), "utf8")).cells));
    const last = p.lessons.length - 1;
    out.push({ id: p.id, parts, modules: p.lessons[last]?.apps?.length ? last + 1 : last });
  }
  return out;
}

/** The pack format of the library (scripts/lean-bundle.mjs, worker-lean-server.ts `unpack`): a u32 (little
 *  endian) index length, the index (JSON [[path, size], ...]), then the files in its order. */
function pack(files) {
  const index = Buffer.from(JSON.stringify(files.map(([p, d]) => [p, d.length])));
  const head = Buffer.alloc(4); head.writeUInt32LE(index.length);
  return gzipSync(Buffer.concat([head, index, ...files.map(([, d]) => d)]), { level: 9 });
}

const run = (cmd, args, env) => new Promise((resolve) => {
  const p = spawn(cmd, args, { env, stdio: ["ignore", "pipe", "pipe"] });
  let out = "";
  p.stdout.on("data", (d) => { out += d; }); p.stderr.on("data", (d) => { out += d; });
  p.on("close", (code) => resolve({ code, out }));
});

export async function buildCourseModules(compiler, outDir, { log = console.log, cache = path.join(root, ".cache/lean-courses") } = {}) {
  const lib = path.join(compiler, "lib/lean");
  if (!existsSync(path.join(compiler, "bin/lean.js")) || !existsSync(path.join(lib, "Init.olean"))) return null;
  const wasm = path.join(compiler, "bin/lean.wasm");
  const tool = createHash("sha256").update(readFileSync(wasm)).digest("hex").slice(0, 16);
  const courses = coursePreludes();
  const manifest = {};
  rmSync(path.join(outDir, "courses"), { recursive: true, force: true });
  mkdirSync(path.join(outDir, "courses"), { recursive: true });
  const t0 = Date.now();
  // the courses compile side by side, each one's modules in order
  const slots = Math.max(1, Math.min(courses.length, cpus().length));
  const queue = [...courses];
  /** A copy of the compiler's layout whose library also holds the course's modules: it looks for modules
   *  only in the library beside its script (Emscripten passes it none of Node's environment, so not
   *  LEAN_PATH), and Node, told to, keeps a linked script's own path. */
  const stage = (dir) => {
    rmSync(dir, { recursive: true, force: true });
    mkdirSync(path.join(dir, "bin"), { recursive: true });
    mkdirSync(path.join(dir, "lib/lean/ChalkCourse"), { recursive: true });
    for (const f of readdirSync(path.join(compiler, "bin"))) symlinkSync(path.join(compiler, "bin", f), path.join(dir, "bin", f));
    for (const f of readdirSync(lib)) symlinkSync(path.join(lib, f), path.join(dir, "lib/lean", f));
    return path.join(dir, "lib/lean");
  };
  const failures = [];
  const one = async (c) => {
    const dir = path.join(cache, "work", c.id), work = stage(dir);
    let before = tool;
    const files = [], entries = [];
    for (let m = 1; m <= c.modules; m++) {
      const name = moduleName(c.id, m), rel = `${name.replaceAll(".", "/")}`;
      const src = moduleSource(c.id, c.parts, m);
      const key = createHash("sha256").update(before).update(src).digest("hex").slice(0, 24);
      const kept = path.join(cache, "oleans", `${key}.olean`);
      if (!existsSync(kept)) {
        // the modules before it, where the compiler looks for them
        for (const [p, d] of files) { mkdirSync(path.dirname(path.join(work, p)), { recursive: true }); writeFileSync(path.join(work, p), d); }
        const file = path.join(work, `${rel}.lean`);
        mkdirSync(path.dirname(file), { recursive: true });
        writeFileSync(file, src);
        const t = Date.now();
        const r = await run("node", ["--preserve-symlinks-main", "--stack-size=65500", path.join(dir, "bin/lean.js"), "-R", work, "-o", path.join(work, `${rel}.olean`), file], process.env);
        if (r.code !== 0 || /: error/.test(r.out)) { failures.push(`${name}:\n${r.out.trim().slice(0, 2000)}`); return; }
        mkdirSync(path.dirname(kept), { recursive: true });
        copyFileSync(path.join(work, `${rel}.olean`), kept);
        log(`lean: ${name} compiled (${((Date.now() - t) / 1000).toFixed(0)} s)`);
      }
      files.push([`${rel}.olean`, readFileSync(kept)]);
      entries.push(moduleEntry(c.id, c.parts, m));
      before = key;
    }
    rmSync(dir, { recursive: true, force: true });
    const data = pack(files);
    const file = `courses/${c.id}-${createHash("sha256").update(data).digest("hex").slice(0, 12)}.pack.gz`;
    writeFileSync(path.join(outDir, file), data);
    manifest[c.id] = { pack: file, size: data.length, modules: entries };
  };
  await Promise.all(Array.from({ length: slots }, async () => { for (let c; (c = queue.shift());) await one(c); }));
  if (failures.length) throw new Error(`lean-courses: a course's Lean did not compile as modules:\n${failures.join("\n\n")}`);
  writeFileSync(path.join(outDir, "lean-courses.json"), JSON.stringify(manifest));
  const total = Object.values(manifest).reduce((n, c) => n + c.size, 0);
  log(`lean: ${Object.keys(manifest).length} courses' preludes as modules, ${(total / 1e6).toFixed(1)} MB packed (${((Date.now() - t0) / 1000).toFixed(0)} s)`);
  return manifest;
}

if (import.meta.url === pathToFileURL(process.argv[1]).href) {
  const [compiler, out] = process.argv.slice(2);
  const m = await buildCourseModules(path.resolve(compiler), path.resolve(out));
  if (!m) { console.error(`no compiler in ${compiler} (bin/lean.js and lib/lean/Init.olean)`); process.exit(1); }
}
