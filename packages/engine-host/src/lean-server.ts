/**
 * Lean's language server in a web worker (or Node): the part of Lean's watchdog a single document needs,
 * in front of the file worker compiled to wasm (engine/wasm/server/LeanWorker.lean, built by
 * scripts/build-lean-wasm-compiler.sh).
 *
 * Natively the Lean 4 extension talks to `lean --server` (the watchdog, `Lean.Server.Watchdog`), which
 * answers `initialize` and starts one `lean --worker` process per open file. A page cannot start
 * processes, so this module takes the watchdog's place for one document:
 *   - `initialize` is answered here, with the reply the real watchdog gives (`capabilities`, printed
 *     at build time by engine/wasm/server/capabilities.lean), less semantic tokens for the whole
 *     document (`rangeTokensOnly`);
 *   - the first `textDocument/didOpen` starts the wasm worker and hands it `initialize` + `didOpen`, the
 *     handshake the watchdog performs (`startFileWorker`);
 *   - of the client's notifications, only those the watchdog forwards and the file worker handles are
 *     relayed (FORWARDED); the worker ends its main loop on any other ("Got unsupported notification
 *     method", FileWorker.lean), as on a message without params, so those never reach it;
 *   - requests and responses are relayed. From the worker, the notifications that feed the watchdog's
 *     cross-file index (`$/lean/ilean*`, `$/lean/importClosure`) are dropped, and its
 *     `$/lean/queryModule` request is answered with no results, as for a module nothing else imports.
 * Messages are JSON-RPC objects, one per call, as monaco-languageclient's browser transport posts them.
 */

export type LspMessage = { jsonrpc: "2.0"; id?: number | string | null; method?: string; params?: unknown; result?: unknown; error?: unknown };

/** What the Emscripten module (`createLeanServer`, `-sMODULARIZE`) exposes. */
export interface LeanServerModule {
  HEAP32: Int32Array;
  HEAPU8: Uint8Array;
  FS: { mkdirTree(path: string): void; writeFile(path: string, data: Uint8Array, opts?: { canOwn?: boolean }): void };
  ENV: Record<string, string>;
  callMain(args: string[]): void;
  _leanweb_in_buf(): number;
  _leanweb_in_cap(): number;
  _leanweb_in_w(): number;
  _leanweb_in_r(): number;
  leanwebOut?: (fd: number, bytes: Uint8Array) => void;
  /** What `IO.appPath` returns (engine/wasm/lean-compiler-emscripten.patch): a web worker has no executable. */
  leanAppPath?: string;
}

export interface LeanServerOptions {
  /** The started Emscripten module (before `callMain`). */
  module: LeanServerModule;
  /** The files of Lean's library, written to `/lib/lean` before the worker starts. The filesystem keeps
   *  each array as it is rather than a copy, so the caller must not reuse them. */
  library: Iterable<[path: string, data: Uint8Array]>;
  /** `InitializeResult` as the native watchdog sends it. */
  initializeResult: unknown;
  /** Deliver a message to the client. */
  send(msg: LspMessage): void;
  /** Where the worker's stderr goes. */
  log?(line: string): void;
}

/** The client notifications the watchdog relays to a file worker (Watchdog.lean `handleNotification`,
 *  FileWorker.lean `handleNotification`); `$/setTrace`, `didSave`, `didClose`, configuration and the
 *  rest stop at the watchdog. */
const FORWARDED = new Set(["textDocument/didChange", "$/cancelRequest", "$/lean/rpc/release", "$/lean/rpc/keepAlive"]);
const WATCHDOG_ONLY = new Set(["$/lean/ileanHeaderSetupInfo", "$/lean/ileanInfoUpdate", "$/lean/ileanInfoFinal", "$/lean/importClosure"]);

/** The `initialize` reply with semantic tokens offered for ranges only, so the editor asks for the lines it
 *  shows. Lean computes a request's tokens with recursion as deep as the commands it spans, and a whole
 *  long document (a late lesson of a course, with its prelude) runs a browser thread out of stack, which
 *  stops the server (ARCHITECTURE.md §4b). */
export function rangeTokensOnly(initializeResult: unknown): unknown {
  const r = initializeResult as { capabilities?: { semanticTokensProvider?: Record<string, unknown> } } | null;
  const tokens = r?.capabilities?.semanticTokensProvider;
  if (!tokens) return initializeResult;
  return { ...r, capabilities: { ...r!.capabilities, semanticTokensProvider: { ...tokens, full: false, range: true } } };
}

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
    // Lean's server resolves its source search path from the application's directory (`IO.appDir`)
    M.FS.mkdirTree("/bin");
    M.leanAppPath = "/bin/lean";
    // Lean's task manager runs this many threads, and adds one whenever a pooled task waits on another;
    // in a browser each is a worker from the pool the module pre-creates (32), and one started beyond
    // it is not ready in time
    M.ENV["LEAN_NUM_THREADS"] = "4";
    for (const [path, data] of o.library) {
      const full = `/lib/lean/${path}`;
      M.FS.mkdirTree(full.slice(0, full.lastIndexOf("/")));
      M.FS.writeFile(full, data, { canOwn: true });   // a copy would hold the library (~280 MB) twice
    }
    M.callMain([]);
  };

  return {
    receive(msg) {
      switch (msg.method) {
        case "initialize":
          initParams = msg.params;
          o.send({ jsonrpc: "2.0", id: msg.id ?? null, result: rangeTokensOnly(o.initializeResult) });
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
        default: {
          const request = msg.id != null && !!msg.method;
          if (!request && msg.method) {
            if (openUri !== null && FORWARDED.has(msg.method) && msg.params !== undefined) toWorker(msg);
            return;
          }
          // before the document opens the worker would read it ahead of its handshake; the watchdog
          // answers requests to files it has no worker for with `contentModified` (Watchdog.lean)
          if (openUri === null) {
            if (request) o.send({ jsonrpc: "2.0", id: msg.id!, error: { code: -32801, message: "the document is not open" } });
            return;
          }
          if (request && msg.params === undefined) {
            o.send({ jsonrpc: "2.0", id: msg.id!, error: { code: -32601, message: `${msg.method} is not supported by this Lean server` } });
            return;
          }
          toWorker(msg);
        }
      }
    },
  };
}
