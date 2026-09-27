/**
 * Lean's language server in a web worker (or Node): the part of Lean's watchdog a single document needs,
 * in front of the file worker compiled to wasm (engine/wasm/server/LeanWorker.lean, built by
 * scripts/build-lean-wasm-compiler.sh).
 *
 * Natively the Lean 4 extension talks to `lean --server` (the watchdog, `Lean.Server.Watchdog`), which
 * answers `initialize` and starts one `lean --worker` process per open file. A page cannot start
 * processes, so this module takes the watchdog's place for one document:
 *   - `initialize` is answered here, with the reply the real watchdog gives (`capabilities`, printed
 *     at build time by engine/wasm/server/capabilities.lean);
 *   - the first `textDocument/didOpen` starts the wasm worker and hands it `initialize` + `didOpen`, the
 *     handshake the watchdog performs (`startFileWorker`);
 *   - everything else is relayed. From the worker, the notifications that feed the watchdog's
 *     cross-file index (`$/lean/ilean*`, `$/lean/importClosure`) are dropped, and its
 *     `$/lean/queryModule` request is answered with no results, as for a module nothing else imports.
 * Messages are JSON-RPC objects, one per call, as monaco-languageclient's browser transport posts them.
 */

export type LspMessage = { jsonrpc: "2.0"; id?: number | string | null; method?: string; params?: unknown; result?: unknown; error?: unknown };

/** What the Emscripten module (`createLeanServer`, `-sMODULARIZE`) exposes. */
export interface LeanServerModule {
  HEAP32: Int32Array;
  HEAPU8: Uint8Array;
  FS: { mkdirTree(path: string): void; writeFile(path: string, data: Uint8Array): void };
  callMain(args: string[]): void;
  _leanweb_in_buf(): number;
  _leanweb_in_cap(): number;
  _leanweb_in_w(): number;
  _leanweb_in_r(): number;
  leanwebOut?: (fd: number, bytes: Uint8Array) => void;
}

export interface LeanServerOptions {
  /** The started Emscripten module (before `callMain`). */
  module: LeanServerModule;
  /** The files of Lean's library, written to `/lib/lean` before the worker starts. */
  library: Iterable<[path: string, data: Uint8Array]>;
  /** `InitializeResult` as the native watchdog sends it. */
  initializeResult: unknown;
  /** Deliver a message to the client. */
  send(msg: LspMessage): void;
  /** Where the worker's stderr goes. */
  log?(line: string): void;
}

const WATCHDOG_ONLY = new Set(["$/lean/ileanHeaderSetupInfo", "$/lean/ileanInfoUpdate", "$/lean/ileanInfoFinal", "$/lean/importClosure"]);

/** Splits a byte stream into LSP messages (`Content-Length` framing). */
export function lspFramer(onMessage: (msg: LspMessage) => void): (bytes: Uint8Array) => void {
  let buf = new Uint8Array(0);
  const dec = new TextDecoder();
  return (bytes) => {
    const next = new Uint8Array(buf.length + bytes.length);
    next.set(buf); next.set(bytes, buf.length); buf = next;
    for (;;) {
      let end = -1;
      for (let i = 0; i + 3 < buf.length; i++) if (buf[i] === 13 && buf[i + 1] === 10 && buf[i + 2] === 13 && buf[i + 3] === 10) { end = i; break; }
      if (end < 0) return;
      const m = /Content-Length:\s*(\d+)/i.exec(dec.decode(buf.subarray(0, end)));
      if (!m) throw new Error("LSP header without Content-Length");
      const n = Number(m[1]), start = end + 4;
      if (buf.length < start + n) return;
      onMessage(JSON.parse(dec.decode(buf.subarray(start, start + n))) as LspMessage);
      buf = buf.slice(start + n);
    }
  };
}

export function startLeanServer(o: LeanServerOptions): { receive(msg: LspMessage): void } {
  const M = o.module;
  const enc = new TextEncoder();
  let initParams: unknown = null;
  let openUri: string | null = null;
  const backlog: Uint8Array[] = [];

  // --- input: the ring buffer leanweb.c reads (static data, so the views need no refresh on growth)
  const ring = M._leanweb_in_buf(), cap = M._leanweb_in_cap(), wIdx = M._leanweb_in_w() >> 2, rIdx = M._leanweb_in_r() >> 2;
  const pump = () => {
    while (backlog.length) {
      const chunk = backlog[0]!;
      const w = Atomics.load(M.HEAP32, wIdx) >>> 0, r = Atomics.load(M.HEAP32, rIdx) >>> 0;
      const free = cap - ((w - r) >>> 0);
      if (free === 0) { setTimeout(pump, 1); return; }
      const k = Math.min(free, chunk.length);
      for (let i = 0; i < k; i++) M.HEAPU8[ring + ((w + i) % cap)] = chunk[i]!;
      Atomics.store(M.HEAP32, wIdx, (w + k) | 0);
      Atomics.notify(M.HEAP32, wIdx);
      if (k === chunk.length) backlog.shift(); else backlog[0] = chunk.subarray(k);
    }
  };
  const toWorker = (msg: LspMessage) => {
    const body = enc.encode(JSON.stringify(msg));
    backlog.push(enc.encode(`Content-Length: ${body.length}\r\n\r\n`), body);
    pump();
  };

  // --- output
  const fromWorker = lspFramer((msg) => {
    if (msg.method && WATCHDOG_ONLY.has(msg.method)) return;
    if (msg.method === "$/lean/queryModule" && msg.id != null) {
      const queries = (msg.params as { queries?: unknown[] } | undefined)?.queries ?? [];
      toWorker({ jsonrpc: "2.0", id: msg.id, result: { queryResults: queries.map(() => []) } });
      return;
    }
    o.send(msg);
  });
  let errLine = "";
  const dec = new TextDecoder();
  M.leanwebOut = (fd, bytes) => {
    if (fd === 1) { fromWorker(bytes); return; }
    errLine += dec.decode(bytes, { stream: true });
    let i;
    while ((i = errLine.indexOf("\n")) >= 0) { o.log?.(errLine.slice(0, i)); errLine = errLine.slice(i + 1); }
  };

  const start = () => {
    for (const [path, data] of o.library) {
      const full = `/lib/lean/${path}`;
      M.FS.mkdirTree(full.slice(0, full.lastIndexOf("/")));
      M.FS.writeFile(full, data);
    }
    M.callMain([]);
  };

  return {
    receive(msg) {
      switch (msg.method) {
        case "initialize":
          initParams = msg.params;
          o.send({ jsonrpc: "2.0", id: msg.id ?? null, result: o.initializeResult });
          return;
        case "initialized": case "exit":
          return;
        case "shutdown":
          o.send({ jsonrpc: "2.0", id: msg.id ?? null, result: null });
          return;
        case "textDocument/didOpen": {
          const uri = (msg.params as { textDocument: { uri: string } }).textDocument.uri;
          if (openUri === null) {
            openUri = uri;
            start();
            toWorker({ jsonrpc: "2.0", id: 0, method: "initialize", params: initParams ?? {} });
            toWorker(msg);
          } else if (uri !== openUri) {
            o.send({ jsonrpc: "2.0", method: "window/showMessage", params: { type: 1, message: `This Lean server holds one document (${openUri}); ${uri} was not opened.` } });
          }
          return;
        }
        default:
          if (openUri !== null) toWorker(msg);
          // before the document opens the worker would read it ahead of its handshake; the watchdog
          // answers requests to files it has no worker for with `contentModified` (Watchdog.lean)
          else if (msg.id != null && msg.method) o.send({ jsonrpc: "2.0", id: msg.id, error: { code: -32801, message: "the document is not open" } });
      }
    },
  };
}
