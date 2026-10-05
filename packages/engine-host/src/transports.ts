import type { Transport } from "@chalkmath/protocol";

/** Browser side: talk to an engine running in a Web Worker. */
export function workerTransport(worker: Worker): Transport {
  return {
    send: (m) => worker.postMessage(m),
    onMessage: (h) => { worker.onmessage = (ev: MessageEvent<string>) => h(ev.data); },
    // an uncaught error in the worker (its script or the wasm failed to load) ends the engine
    onError: (h) => { worker.onerror = (ev) => { ev.preventDefault(); h(new Error(ev.message || "the engine worker failed")); }; },
    close: () => worker.terminate(),
  };
}

/** Worker side: expose the engine to the page that created the worker. */
export function workerSelfTransport(self: DedicatedWorkerGlobalScope): Transport {
  return {
    send: (m) => self.postMessage(m),
    onMessage: (h) => { self.onmessage = (ev: MessageEvent<string>) => h(ev.data); },
  };
}

/** Browser or Node side: one HTTP POST per request to a remote/self-hosted engine. Every request is
 *  answered: an unreachable server, an HTTP error page (a proxy's 502) or a body that is not JSON-RPC
 *  becomes an error reply for that request rather than a call that never settles. */
export function httpTransport(url: string, fetchImpl: typeof fetch = fetch): Transport {
  let handler: (m: string) => void = () => {};
  return {
    send: (m) => {
      const id = (JSON.parse(m) as { id?: number | string }).id ?? null;
      const fail = (message: string) => handler(JSON.stringify({ jsonrpc: "2.0", id, error: { code: -32000, message } }));
      void fetchImpl(url, { method: "POST", headers: { "content-type": "application/json" }, body: m }).then(async (r) => {
        const text = await r.text();
        let reply: unknown = null;
        try { reply = JSON.parse(text); } catch { /* not JSON: answered below */ }
        if (reply && typeof reply === "object" && "jsonrpc" in reply) handler(text);
        else fail(`the engine at ${url} answered HTTP ${r.status}${r.ok ? " with a reply that is not JSON-RPC" : ` ${r.statusText}`.trimEnd()}`);
      }).catch((e: unknown) => fail(`the engine at ${url} is unreachable: ${e instanceof Error ? e.message : String(e)}`));
    },
    onMessage: (h) => { handler = h; },
  };
}

/** Browser or Node side: WebSocket for a long-lived session. */
export function webSocketTransport(ws: WebSocket): Transport {
  return {
    send: (m) => ws.send(m),
    onMessage: (h) => { ws.onmessage = (ev) => h(String(ev.data)); },
    close: () => ws.close(),
  };
}

/** Node side: newline-delimited JSON over a child process's stdio (how the Lean engine is hosted).
 *  Given the process's events, its exit or failure to start is reported (`onError`), so pending calls
 *  fail instead of waiting forever; a close the host asked for is not reported. */
export function stdioTransport(proc: {
  stdin: NodeJS.WritableStream; stdout: NodeJS.ReadableStream; kill?(): void;
  on?(event: string, listener: (...args: any[]) => void): unknown;
}): Transport {
  let handler: (m: string) => void = () => {};
  let onError: (e: Error) => void = () => {};
  let closing = false;
  let buf = "";
  // decoded as a stream, so a character split between two chunks of the pipe arrives whole
  proc.stdout.setEncoding("utf8");
  proc.stdout.on("data", (chunk: string) => {
    buf += chunk;
    let i;
    while ((i = buf.indexOf("\n")) >= 0) { const line = buf.slice(0, i); buf = buf.slice(i + 1); if (line.trim()) handler(line); }
  });
  // writing to a process that has exited is EPIPE on stdin; the exit itself is what is reported
  proc.stdin.on("error", () => {});
  proc.on?.("error", (e: Error) => { if (!closing) onError(new Error(`the engine could not run: ${e.message}`)); });
  proc.on?.("exit", (code: number | null, signal: string | null) => {
    if (!closing) onError(new Error(`the engine process stopped (${signal ?? `exit code ${code}`})`));
  });
  return {
    send: (m) => { proc.stdin.write(m + "\n"); },
    onMessage: (h) => { handler = h; },
    onError: (h) => { onError = h; },
    close: () => { closing = true; proc.kill?.(); },
  };
}
