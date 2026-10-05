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
import { leanForPrelude } from "../../packages/lean-editor/src/prelude.js";

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

/** A lesson's Lean as a later lesson sees it (app.ts `leanPreludeOf`): exercises with the author's proofs. */
const leanOf = (cells) => cells.flatMap((c) => c.type === "lean" ? [c.src] : c.type === "exercise" && c.lean && c.src.trim() ? [`${c.src}\n${c.leanSolution ?? LEAN_START}`] : []);
const preludes = new Map();
for (const p of JSON.parse(readFileSync(path.join(root, "notebooks/courses.json"), "utf8")).projects) {
  if (!p.leanPrelude) continue;
  const parts = [];
  for (const l of p.lessons) {
    const file = path.join(root, "notebooks", p.path, l.file);
    preludes.set(file, parts.join("\n\n"));
    const lean = leanOf(JSON.parse(readFileSync(file, "utf8")).cells);
    if (lean.length) parts.push(`-- ${l.title}\n${leanForPrelude(lean.join("\n\n"))}`);
  }
}
/** The document the page gives Lean for a notebook (app.ts `leanDocCells`), or null when it has no Lean. */
function documentOf(file) {
  const out = [];
  for (const c of JSON.parse(readFileSync(file, "utf8")).cells) {
    if (c.type === "lean") out.push(c.src);
    else if (c.type === "exercise" && c.lean && c.src.trim()) out.push(c.src, c.leanStart ?? LEAN_START);
  }
  const prelude = preludes.get(file);
  if (prelude && out.length) out.unshift(prelude);
  return out.length ? out.join(`\n${SEPARATOR}\n`) : null;
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
async function check(text) {
  const page = await context.newPage();
  try {
    await page.goto(base);
    return await page.evaluate(([text, timeout]) => new Promise((resolve) => {
      const worker = new Worker("lean/lean-server.worker.js");
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
        if (version === 2) { end({ result: "done", errors: diagnostics.filter((d) => d.severity === 1).length }); return; }
        // Lean fast-forwards over the commands an edit leaves unchanged, one after another
        version = 2; at = null;
        worker.postMessage({ jsonrpc: "2.0", method: "textDocument/didChange", params: { textDocument: { uri, version }, contentChanges: [{ text: `${text}\n` }] } });
      };
      worker.postMessage({ jsonrpc: "2.0", id: 1, method: "initialize", params: { processId: null, rootUri: null, capabilities: {} } });
      worker.postMessage({ jsonrpc: "2.0", method: "textDocument/didOpen", params: { textDocument: { uri, languageId: "lean4", version, text } } });
      setTimeout(() => end({ result: "timeout" }), timeout);
    }), [text, TIMEOUT]);
  } finally { await page.close(); }
}

/** The declaration a 0-based line of `text` is in: its first line. */
function declarationAt(text, line) {
  const lines = text.split("\n");
  for (let k = Math.min(line, lines.length - 1); k >= 0; k--)
    if (/^[^\s/-]/.test(lines[k]) && !/^(namespace|end|open|section|variable)\b/.test(lines[k])) return `line ${k + 1}: ${lines[k].slice(0, 100)}`;
  return `line ${line + 1}`;
}

const queue = args.map((f) => path.resolve(f)).map((file) => ({ file, text: documentOf(file) })).filter((d) => d.text);
let bad = 0;
await Promise.all(Array.from({ length: Math.max(1, jobs) }, async () => {
  for (let d; (d = queue.shift());) {
    const r = await check(d.text);
    const name = path.relative(root, d.file);
    if (r.result === "done") { console.log(`${name}: ok (${r.secs} s${r.errors ? `, ${r.errors} errors the reader sees` : ""})`); continue; }
    bad++;
    const where = r.at === null ? (r.edited ? ", after an edit at its end" : "") : `, while checking ${declarationAt(d.text, r.at)}`;
    console.log(`${name}: FAILED, ${r.result === "timeout" ? `not checked in ${TIMEOUT / 1000} s` : `Lean's server stopped (${r.message})`}${where}`);
  }
}));
await browser.close();
site.close();
process.exit(bad ? 1 : 0);
