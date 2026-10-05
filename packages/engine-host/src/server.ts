import { createServer } from "node:http";
import { rpcErrorOf, type RpcRequest, type RpcResponse } from "@chalkmath/protocol";
import { leanNativeClient } from "./lean-native.js";

export interface ServerOptions {
  /** The interface to listen on: this machine only unless asked (`0.0.0.0` for every interface). */
  host?: string | undefined;
  /** A request that takes longer stops the engine, which restarts without its sessions (see
   *  `leanNativeClient`): the engine serves one request at a time, so a stuck one blocks everyone. */
  timeoutMs?: number | undefined;
  /** Largest request body accepted, in bytes; a larger one is answered 413. */
  maxBody?: number | undefined;
  /** The page origins allowed to call (CORS). Unset, any page may: the notebook is served from
   *  another origin than this host (a static site, or a dev server), so that is the default; a
   *  host on a shared machine can name the origins it serves. */
  origins?: string[] | undefined;
}

const rpcError = (id: RpcRequest["id"] | null, code: number, message: string) => JSON.stringify({ jsonrpc: "2.0", id, error: { code, message } });
/** The request's id from the start of its body, so that even a body refused unread is answered by id. */
const idOf = (head: string): RpcRequest["id"] | null => {
  const m = /^\s*\{\s*"jsonrpc"\s*:\s*"2\.0"\s*,\s*"id"\s*:\s*(\d+|"(?:[^"\\]|\\.)*")/.exec(head);
  if (!m) return null;
  try { return JSON.parse(m[1]!) as RpcRequest["id"]; } catch { return null; }
};

/**
 * Self-hostable HTTP server: POST a JSON-RPC request, get a JSON-RPC response.
 *   node packages/engine-host/dist/server.js [port] [path/to/mathengine]
 *   (environment: CHALKMATH_HOST, CHALKMATH_TIMEOUT in seconds, CHALKMATH_ORIGIN as a comma-separated
 *   list of the page origins allowed to call; unset, any page may)
 * The engine is the native Lean executable, spoken to over stdio; its session store lives in that
 * process, keyed by sessionId in the protocol. Requests are served one at a time, in the order they
 * arrived (`leanNativeClient` queues them), and the deadline counts a request's own time only.
 */
export function startServer(port = 8787, exe = "engine/.lake/build/bin/mathengine", opts: ServerOptions = {}) {
  const { host = "localhost", timeoutMs = 60_000, maxBody = 1 << 20, origins } = opts;
  const client = leanNativeClient(exe, { timeoutMs });
  client.onError?.((e) => console.error(`chalkmath engine-lean: ${e.message}`));
  const server = createServer((req, res) => {
    const origin = req.headers.origin;
    if (!origins) res.setHeader("access-control-allow-origin", "*");
    else if (origin && origins.includes(origin)) { res.setHeader("access-control-allow-origin", origin); res.setHeader("vary", "origin"); }
    res.setHeader("access-control-allow-headers", "content-type");
    if (req.method === "OPTIONS") { res.writeHead(204); res.end(); return; }
    if (req.method !== "POST") { res.writeHead(405); res.end(); return; }
    const chunks: Buffer[] = [];
    let size = 0;
    req.on("data", (c: Buffer) => {
      size += c.length;
      if (size <= maxBody) { chunks.push(c); return; }
      // answered by the request's id where its first chunk shows it, and the socket is closed only
      // once the reply has been written, so the client reads the answer rather than a reset
      const id = idOf(Buffer.concat([...chunks, c]).toString("utf8", 0, 256));
      res.writeHead(413, { "content-type": "application/json", connection: "close" });
      res.end(rpcError(id, -32600, `request body larger than ${maxBody} bytes`), () => req.destroy());
    });
    req.on("error", () => { /* the client went away: nothing to answer */ });
    req.on("end", async () => {
      if (size > maxBody) return;
      res.setHeader("content-type", "application/json");
      let rpc: RpcRequest;
      try { rpc = JSON.parse(Buffer.concat(chunks).toString("utf8")) as RpcRequest; }
      catch { res.end(rpcError(null, -32700, "Parse error")); return; }
      if (!rpc || typeof rpc !== "object" || typeof rpc.method !== "string") { res.end(rpcError(null, -32600, "Invalid Request")); return; }
      let out: RpcResponse;
      try { out = { jsonrpc: "2.0", id: rpc.id, result: await client.call(rpc.method, rpc.params as never) }; }
      catch (e) { out = { jsonrpc: "2.0", id: rpc.id, error: rpcErrorOf(e) }; }
      res.end(JSON.stringify(out));
    });
  });
  server.on("close", () => client.close());
  server.listen(port, host, () => console.log(`chalkmath engine-lean listening on http://${host}:${(server.address() as { port: number }).port}`));
  return server;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const timeout = Number(process.env.CHALKMATH_TIMEOUT);
  const origins = process.env.CHALKMATH_ORIGIN?.split(",").map((o) => o.trim()).filter(Boolean);
  startServer(Number(process.argv[2] ?? 8787), process.argv[3], {
    host: process.env.CHALKMATH_HOST || undefined, timeoutMs: timeout > 0 ? timeout * 1000 : undefined,
    origins: origins?.length ? origins : undefined,
  });
}
