/// <reference lib="webworker" />
/**
 * Web-worker host for Lean's language server compiled to wasm (scripts/build-lean-wasm-compiler.sh).
 * The page's Lean 4 extension (vscode-lean4 in the VS Code web editor, via lean4monaco) talks LSP to
 * this worker, one JSON-RPC object per postMessage; `startLeanServer` plays Lean's watchdog.
 *
 * The module is threaded (Lean's server needs tasks), so the page must be cross-origin isolated
 * (COOP/COEP) for SharedArrayBuffer. Emscripten starts each pthread as a further worker running the
 * script that loaded the module, which is this file: in such a worker (named `em-pthread`) it only loads
 * the module's script, whose pthread runtime takes over.
 */
import { startLeanServer, type LspMessage, type LeanServerModule } from "./lean-server.js";

declare const createLeanServer: (opts: object) => Promise<LeanServerModule>;
declare const __BUILD_ID__: string;
/** How many parts scripts/lean-bundle.mjs split the library into. */
declare const __LEAN_LIB_PARTS__: number;
const stamp = typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev";
const at = (file: string) => new URL(`${file}?v=${stamp}`, self.location.href).href;

importScripts(at("lean-server.js"));
if (self.name !== "em-pthread") host();

function host() {
  /** A gzipped file, decompressed as it arrives; `parts` > 0: shipped as `<file>.0`, `<file>.1`, … */
  function gunzip(file: string, parts = 0): ReadableStream<Uint8Array> {
    const names = parts > 0 ? Array.from({ length: parts }, (_, i) => `${file}.${i}`) : [file];
    let i = 0, reader: ReadableStreamDefaultReader<Uint8Array<ArrayBuffer>> | null = null;
    const joined = new ReadableStream<BufferSource>({
      async pull(c) {
        for (;;) {
          if (!reader) {
            if (i === names.length) { c.close(); return; }
            const res = await fetch(at(names[i++]!));
            if (!res.ok || !res.body) throw new Error(`Lean's ${names[i - 1]} did not load (${res.status})`);
            reader = res.body.getReader();
          }
          const { done, value } = await reader.read();
          if (!done) { c.enqueue(value); return; }
          reader = null;
        }
      },
    });
    return joined.pipeThrough(new DecompressionStream("gzip"));
  }

  /** `lean-lib.pack.gz`: [u32 LE index length] [JSON [[path, size], ...]] [the files, in index order]. */
  async function library(): Promise<[string, Uint8Array][]> {
    const buf = new Uint8Array(await new Response(gunzip("lean-lib.pack.gz", __LEAN_LIB_PARTS__)).arrayBuffer());
    const n = new DataView(buf.buffer).getUint32(0, true);
    const index = JSON.parse(new TextDecoder().decode(buf.subarray(4, 4 + n))) as [string, number][];
    let off = 4 + n;
    return index.map(([p, size]) => { const d = buf.subarray(off, off + size); off += size; return [p, d]; });
  }

  const early: LspMessage[] = [];
  let receive = (m: LspMessage) => { early.push(m); };
  self.onmessage = (ev: MessageEvent<LspMessage>) => receive(ev.data);

  Promise.all([
    createLeanServer({
      locateFile: (p: string) => at(p),
      // the wasm is shipped gzipped (scripts/lean-bundle.mjs), and compiled as it downloads
      instantiateWasm(imports: WebAssembly.Imports, done: (i: WebAssembly.Instance, m: WebAssembly.Module) => void) {
        const wasm = new Response(gunzip("lean-server.wasm.gz"), { headers: { "content-type": "application/wasm" } });
        WebAssembly.instantiateStreaming(wasm, imports).then((r) => done(r.instance, r.module), (e: unknown) => setTimeout(() => { throw e; }));
        return {};
      },
    }),
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
}
