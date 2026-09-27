/// <reference lib="webworker" />
/**
 * Web-worker host for Lean's language server compiled to wasm (scripts/build-lean-wasm-compiler.sh).
 * The page's Lean 4 extension (vscode-lean4 in the VS Code web editor, via lean4monaco) talks LSP to
 * this worker, one JSON-RPC object per postMessage; `startLeanServer` plays Lean's watchdog.
 *
 * The module is threaded (Lean's server needs tasks), so the page must be cross-origin isolated
 * (COOP/COEP) for SharedArrayBuffer. Its pthreads are further workers that load `lean-server.js` itself,
 * hence `mainScriptUrlOrBlob`: this file is not the module's script.
 */
import { startLeanServer, type LspMessage, type LeanServerModule } from "./lean-server.js";

declare const createLeanServer: (opts: object) => Promise<LeanServerModule>;
declare const __BUILD_ID__: string;
const stamp = typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev";
const at = (file: string) => new URL(`${file}?v=${stamp}`, self.location.href).href;

importScripts(at("lean-server.js"));

/** `lean-lib.pack.gz`: [u32 LE index length] [JSON [[path, size], ...]] [the files, in index order]. */
async function library(): Promise<[string, Uint8Array][]> {
  const res = await fetch(at("lean-lib.pack.gz"));
  if (!res.ok || !res.body) throw new Error(`Lean's library did not load (${res.status})`);
  const buf = new Uint8Array(await new Response(res.body.pipeThrough(new DecompressionStream("gzip"))).arrayBuffer());
  const n = new DataView(buf.buffer).getUint32(0, true);
  const index = JSON.parse(new TextDecoder().decode(buf.subarray(4, 4 + n))) as [string, number][];
  let off = 4 + n;
  return index.map(([p, size]) => { const d = buf.subarray(off, off + size); off += size; return [p, d]; });
}

const early: LspMessage[] = [];
let receive = (m: LspMessage) => { early.push(m); };
self.onmessage = (ev: MessageEvent<LspMessage>) => receive(ev.data);

Promise.all([
  createLeanServer({ locateFile: (p: string) => at(p), mainScriptUrlOrBlob: at("lean-server.js") }),
  library(),
  fetch(at("lean-initialize.json")).then((r) => r.json()),
]).then(([module, lib, initializeResult]) => {
  const server = startLeanServer({
    module, library: lib, initializeResult,
    send: (m) => self.postMessage(m),
    log: (l) => console.debug(`[lean] ${l}`),
  });
  receive = (m) => server.receive(m);
  for (const m of early.splice(0)) server.receive(m);
}, (e: unknown) => {
  // an uncaught error ends the worker; the page's transport reports it (Transport.onError)
  setTimeout(() => { throw e; });
});
