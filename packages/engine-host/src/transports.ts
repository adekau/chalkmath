import type { Transport } from "@mathbook/protocol";

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

/** Browser or Node side: one HTTP POST per request to a remote/self-hosted engine. */
export function httpTransport(url: string, fetchImpl: typeof fetch = fetch): Transport {
  let handler: (m: string) => void = () => {};
  return {
    send: (m) => {
      void fetchImpl(url, { method: "POST", headers: { "content-type": "application/json" }, body: m }).then((r) => r.text()).then(handler, (e: unknown) => {
        // an unreachable server answers the request with an error instead of leaving it pending
        const id = (JSON.parse(m) as { id?: number | string }).id ?? null;
        handler(JSON.stringify({ jsonrpc: "2.0", id, error: { code: -32000, message: `the engine at ${url} is unreachable: ${e instanceof Error ? e.message : String(e)}` } }));
      });
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

/** Node side: newline-delimited JSON over a child process's stdio (how the Lean engine is hosted). */
export function stdioTransport(proc: { stdin: NodeJS.WritableStream; stdout: NodeJS.ReadableStream; kill?(): void }): Transport {
  let handler: (m: string) => void = () => {};
  let buf = "";
  proc.stdout.on("data", (chunk: Buffer | string) => {
    buf += chunk.toString();
    let i;
    while ((i = buf.indexOf("\n")) >= 0) { const line = buf.slice(0, i); buf = buf.slice(i + 1); if (line.trim()) handler(line); }
  });
  return {
    send: (m) => proc.stdin.write(m + "\n"),
    onMessage: (h) => { handler = h; },
    close: () => proc.kill?.(),
  };
}
