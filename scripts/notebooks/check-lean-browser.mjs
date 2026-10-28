// Check that Lean in the browser gets through each notebook's Lean: every notebook and lesson with Lean
// cells, assembled as the page assembles it (a course's Lean prelude, then its Lean cells and its Lean
// exercises, each exercise with the reader's starting proof), is opened in the bundled Lean server
// (dist/lean/lean-server.worker.js, Lean compiled to wasm) in Chromium, and must be checked to the end, and
// again after an edit at its end (a reader typing in the last cell).
//   node scripts/notebooks/check-lean-browser.mjs [--jobs N] notebooks/x.chalk [...]
// Needs `npm run bundle` with Lean (npm run lean-wasm, or its release in LEAN_WASM_DIR). Chromium:
// playwright-core's own, or the executable named by CHROMIUM.
//
// check-lean.mjs checks the same Lean with native Lean; this catches what only the browser hits. A
// browser gives each worker thread a small stack (Chromium: 500 KB, against the 8 MB Lean's threads
// have natively), and Lean compiled to wasm needs much more of it per level of recursion than native
// Lean, so Lean that elaborates deep enough (a long `do` block, say) overflows it: the thread throws
// "Maximum call stack size exceeded" and the whole server stops (ARCHITECTURE.md §4b).
import { chromium } from "playwright-core";
import { createServer } from "node:http";
import { existsSync, readFileSync, statSync } from "node:fs";
import path from "node:path";
import { preludePart, preludeOf, importedPrelude } from "../../packages/lean-editor/src/prelude.js";

const SEPARATOR = "--⁅cell⁆";   // packages/lean-editor/src/index.ts
const LEAN_START = "  sorry";    // apps/notebook/src/app.ts: an exercise's proof before the reader writes one
const TIMEOUT = 600_000;
const root = path.resolve(import.meta.dirname, "../..");
const dist = path.join(root, "apps/notebook/dist");
const args = process.argv.slice(2);
const jobsAt = args.indexOf("--jobs");
const jobs = jobsAt >= 0 ? Number(args.splice(jobsAt, 2)[1]) : 2;
if (!existsSync(path.join(dist, "lean/lean-server.wasm.gz"))) {
  console.log("no Lean in apps/notebook/dist: npm run lean-wasm (or set LEAN_WASM_DIR to its release), then npm run bundle");
  process.exit(1);
}

// a course's lessons' preludes, as the page gives them (app.ts `leanPreludeOf`, `leanPreludeSrc`): an
// import of the course's module that holds the prelude (lean/lean-courses.json, scripts/lean-courses.mjs)
// when the bundle has them, with the module's pack loaded, else the prelude inline
const modulesFile = path.join(dist, "lean/lean-courses.json");
const modules = existsSync(modulesFile) ? JSON.parse(readFileSync(modulesFile, "utf8")) : {};
const preludes = new Map();
for (const p of JSON.parse(readFileSync(path.join(root, "notebooks/courses.json"), "utf8")).projects) {
  if (!p.leanPrelude) continue;
  const parts = [];
  const prelude = () => {
    const text = preludeOf(parts), c = modules[p.id];
    const entry = c && text ? c.modules[parts.length - 1] : undefined;
    const src = entry ? importedPrelude(entry, text) : null;
    return src === null ? { src: text } : { src, pack: c.pack };
  };
  for (const l of p.lessons) {
    const file = path.join(root, "notebooks", p.path, l.file);
    preludes.set(file, prelude());
    parts.push(preludePart(l.title, JSON.parse(readFileSync(file, "utf8")).cells));
    // a lesson's applications see its Lean too; later lessons do not see theirs
    for (const ap of l.apps ?? []) preludes.set(path.join(root, "notebooks", p.path, ap.file), prelude());
  }
}
/** The document the page gives Lean for a notebook (app.ts `leanDocCells`), the pack its import needs, and
 *  how many lines its prelude has; null when it has no Lean. */
function documentOf(file) {
  const out = [];
  for (const c of JSON.parse(readFileSync(file, "utf8")).cells) {
    if (c.type === "lean") out.push(c.src);
    // a definition exercise: the reader's definition as it starts, before the statement
    else if (c.type === "exercise" && c.lean && c.src.trim()) out.push(...(c.leanDef !== undefined ? [c.leanDef] : []), c.src, c.leanStart ?? LEAN_START);
  }
  const prelude = preludes.get(file);
  if (prelude?.src && out.length) out.unshift(prelude.src);
  return out.length ? { text: out.join(`\n${SEPARATOR}\n`), pack: prelude?.src ? prelude.pack : undefined, preludeLines: prelude?.src ? prelude.src.split("\n").length : 0 } : null;
}

// the headers a host serving Lean cells sends (or the page's service worker adds): SharedArrayBuffer
const site = createServer((req, res) => {
  const url = decodeURIComponent(new URL(req.url, "http://x").pathname);
  const headers = { "cross-origin-opener-policy": "same-origin", "cross-origin-embedder-policy": "require-corp" };
  if (url === "/check.html") { res.writeHead(200, { ...headers, "content-type": "text/html" }); res.end("<!doctype html><title>check</title>"); return; }
  const file = path.join(dist, url);
  try { if (!statSync(file).isFile()) throw 0; } catch { res.writeHead(404); res.end(); return; }
  res.writeHead(200, { ...headers, "content-type": file.endsWith(".js") ? "text/javascript" : file.endsWith(".json") ? "application/json" : "application/octet-stream" });
  res.end(readFileSync(file));
}).listen(0);
await new Promise((r) => site.once("listening", r));
const browser = await chromium.launch({ ...(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {}), args: ["--no-sandbox"] });
const context = await browser.newContext();
const base = `http://localhost:${site.address().port}/check.html`;

/** Lean's server on one document, then on it edited at its end: done (with its errors), or stopped (with
 *  where it was), or out of time. */
async function check(text, pack, preludeLines) {
  const page = await context.newPage();
  try {
    await page.goto(base);
    return await page.evaluate(([text, timeout, pack, preludeLines]) => new Promise((resolve) => {
      const worker = new Worker(`lean/lean-server.worker.js${pack ? `?packs=${encodeURIComponent(pack)}` : ""}`);
      let diagnostics = [], at = null;
      const t0 = Date.now();
      const end = (r) => { worker.terminate(); resolve({ ...r, secs: Math.round((Date.now() - t0) / 1000), at, edited: version === 2 }); };
      worker.onerror = (e) => end({ result: "stopped", message: e.message });
      const uri = "file:///notebook/Cell.lean";
      let version = 1;
      worker.onmessage = (e) => {
        const m = e.data;
        if (m.method === "textDocument/publishDiagnostics") diagnostics = m.params.diagnostics;
        if (m.method !== "$/lean/fileProgress" || m.params.textDocument.version !== version) return;
        const left = m.params.processing;
        if (left.length) { at = Math.min(...left.map((p) => p.range.start.line)); return; }
        if (version === 2) {
          const errors = diagnostics.filter((d) => d.severity === 1);
          // the prelude is the course's, not the reader's: an error there (its module did not import) fails it
          const inPrelude = errors.filter((d) => d.range.start.line < preludeLines);
          end({ result: "done", errors: errors.length, prelude: inPrelude.map((d) => `${d.range.start.line + 1}: ${d.message.split("\n")[0]}`) });
          return;
        }
        // Lean fast-forwards over the commands an edit leaves unchanged, one after another
        version = 2; at = null;
        worker.postMessage({ jsonrpc: "2.0", method: "textDocument/didChange", params: { textDocument: { uri, version }, contentChanges: [{ text: `${text}\n` }] } });
      };
      worker.postMessage({ jsonrpc: "2.0", id: 1, method: "initialize", params: { processId: null, rootUri: null, capabilities: {} } });
      worker.postMessage({ jsonrpc: "2.0", method: "textDocument/didOpen", params: { textDocument: { uri, languageId: "lean4", version, text } } });
      setTimeout(() => end({ result: "timeout" }), timeout);
    }), [text, TIMEOUT, pack, preludeLines]);
  } finally { await page.close(); }
}

/** The declaration a 0-based line of `text` is in: its first line. */
function declarationAt(text, line) {
  const lines = text.split("\n");
  for (let k = Math.min(line, lines.length - 1); k >= 0; k--)
    if (/^[^\s/-]/.test(lines[k]) && !/^(namespace|end|open|section|variable)\b/.test(lines[k])) return `line ${k + 1}: ${lines[k].slice(0, 100)}`;
  return `line ${line + 1}`;
}

const queue = args.map((f) => path.resolve(f)).map((file) => ({ file, doc: documentOf(file) })).filter((d) => d.doc);
let bad = 0;
await Promise.all(Array.from({ length: Math.max(1, jobs) }, async () => {
  for (let d; (d = queue.shift());) {
    const r = await check(d.doc.text, d.doc.pack, d.doc.preludeLines);
    const name = path.relative(root, d.file);
    const how = d.doc.pack ? ", its prelude imported" : "";
    if (r.result === "done" && r.prelude.length) { bad++; console.log(`${name}: FAILED, errors in its prelude${how}: ${r.prelude.slice(0, 3).join("; ")}`); continue; }
    if (r.result === "done") { console.log(`${name}: ok (${r.secs} s${how}${r.errors ? `, ${r.errors} errors the reader sees` : ""})`); continue; }
    bad++;
    const where = r.at === null ? (r.edited ? ", after an edit at its end" : "") : `, while checking ${declarationAt(d.doc.text, r.at)}`;
    console.log(`${name}: FAILED, ${r.result === "timeout" ? `not checked in ${TIMEOUT / 1000} s` : `Lean's server stopped (${r.message})`}${where}`);
  }
}));
await browser.close();
site.close();
process.exit(bad ? 1 : 0);
