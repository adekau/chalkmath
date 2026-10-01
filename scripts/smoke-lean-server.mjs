// Smoke test + timing for Lean's language server compiled to wasm (scripts/build-lean-wasm-compiler.sh),
// driven through the same in-browser watchdog the page uses (packages/engine-host/src/lean-server.ts):
//   node scripts/smoke-lean-server.mjs [engine/toolchains/lean-<ver>-wasm32/compiler]
// Opens a small file, waits for Lean to finish it, and checks the diagnostics and a goal.
import { createRequire } from "node:module";
import { readFileSync, readdirSync } from "node:fs";
import { gunzipSync } from "node:zlib";
import path from "node:path";
import { startLeanServer } from "../packages/engine-host/dist/lean-server.js";

const root = path.resolve(import.meta.dirname, "..");
const dir = path.resolve(process.argv[2] ?? path.join(root, "engine/toolchains", readdirSync(path.join(root, "engine/toolchains")).find((d) => d.endsWith("-wasm32")), "compiler"));
const t0 = performance.now();
const ms = () => Math.round(performance.now() - t0);

function unpack(buf) {
  const n = buf.readUInt32LE(0);
  const index = JSON.parse(buf.subarray(4, 4 + n).toString());
  let off = 4 + n;
  return index.map(([p, size]) => { const d = buf.subarray(off, off + size); off += size; return [p, d]; });
}
const library = unpack(gunzipSync(readFileSync(path.join(dir, "lean-lib.pack.gz"))));
console.log(`[${ms()} ms] library: ${library.length} files`);

const createLeanServer = createRequire(import.meta.url)(path.join(dir, "lean-server.js"));
const module = await createLeanServer({ locateFile: (p) => path.join(dir, p) });
console.log(`[${ms()} ms] module instantiated`);

const text = [
  "def fib : Nat → Nat | 0 => 0 | 1 => 1 | n+2 => fib n + fib (n+1)",
  "#eval fib 20",
  "theorem t (a b : Nat) : a + b = b + a := by",
  "  omega",
  "example : 2 + 2 = 5 := by decide",
  "example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by",
  "  constructor",
  "  · exact hp",
  "  · exact hq",
  "",
].join("\n");
const uri = "file:///notebook/Cell.lean";

let done, pending = new Map(), nextId = 1, diagnostics = [];
const finished = new Promise((r) => (done = r));
const server = startLeanServer({
  module, library,
  initializeResult: JSON.parse(readFileSync(path.join(dir, "lean-initialize.json"), "utf8")),
  log: (l) => console.log(`  [lean] ${l}`),
  send(msg) {
    if (msg.id != null && pending.has(msg.id)) { pending.get(msg.id)(msg); pending.delete(msg.id); return; }
    if (msg.method === "textDocument/publishDiagnostics") diagnostics = msg.params.diagnostics;
    if (msg.method === "$/lean/fileProgress" && msg.params.processing.length === 0) done();
  },
});
const request = (method, params) => new Promise((r) => { const id = nextId++; pending.set(id, r); server.receive({ jsonrpc: "2.0", id, method, params }); });

const init = await request("initialize", { processId: null, rootUri: null, capabilities: {} });
console.log(`[${ms()} ms] initialize: ${init.result.serverInfo.name}`);
server.receive({ jsonrpc: "2.0", method: "initialized", params: {} });
server.receive({ jsonrpc: "2.0", method: "textDocument/didOpen", params: { textDocument: { uri, languageId: "lean4", version: 1, text } } });
// notifications the Lean 4 extension sends that Lean's watchdog keeps from the file worker, which stops
// on them ("Got unsupported notification method: $/setTrace"); and one without params
for (const [method, params] of [["$/setTrace", { value: "off" }], ["workspace/didChangeConfiguration", { settings: {} }],
  ["textDocument/didSave", { textDocument: { uri } }], ["$/lean/noParams", undefined]])
  server.receive({ jsonrpc: "2.0", method, ...(params ? { params } : {}) });
const timeout = (p, what) => Promise.race([p, new Promise((_, no) => setTimeout(() => no(new Error(`${what}: no answer in 120 s (did the worker stop?)`)), 120000))]);
await timeout(finished, "processing the file").catch((e) => { console.log(`FAILED: ${e.message}`); process.exit(1); });
console.log(`[${ms()} ms] file processed`);
for (const d of diagnostics) console.log(`  ${d.range.start.line + 1}:${d.range.start.character} ${["", "error", "warning", "info", "hint"][d.severity]}: ${d.message.split("\n")[0]}`);
const goal = await timeout(request("$/lean/plainGoal", { textDocument: { uri }, position: { line: 6, character: 13 } }), "the goal request")
  .catch((e) => { console.log(`FAILED: ${e.message}`); process.exit(1); });
console.log(`[${ms()} ms] goal after constructor:\n${goal.result?.rendered ?? JSON.stringify(goal)}`);

const has = (sev, s) => diagnostics.some((d) => d.severity === sev && d.message.includes(s));
const ok = has(3, "6765") && has(1, "decide") && diagnostics.filter((d) => d.severity === 1).length === 1 && /hp : p/.test(goal.result?.rendered ?? "");
console.log(ok ? "OK" : "FAILED");
process.exit(ok ? 0 : 1);
