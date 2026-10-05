/// <reference lib="webworker" />
/**
 * Web-worker host for the Lean engine compiled to wasm (scripts/build-wasm.sh).
 *
 * The engine's `handle` takes a JSON-RPC request and returns the JSON-RPC reply to it, with the
 * request's own id, so the page's messages go to it as they are and its replies back as they are:
 * nothing is parsed or serialized here, where a derivation can run to megabytes. What is added is
 * the one thing the engine cannot say for itself: that it crashed part way through a call.
 */
import { wasmCall, type WasmModule } from "./wasm-call.js";

declare const createMathEngine: (opts?: object) => Promise<WasmModule>;
declare const __BUILD_ID__: string;
declare const __ASSET_VERSIONS__: Record<string, string>;
/** A file of the engine with its version, a hash of its contents (scripts/bundle.mjs), so the
 *  browser keeps the wasm across deploys that did not change it; the build where it has none. */
const versioned = (file: string) => `${file}?v=${(typeof __ASSET_VERSIONS__ === "object" && __ASSET_VERSIONS__[file]) || (typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev")}`;

importScripts(versioned("engine-lean.js"));

const ready = createMathEngine({ locateFile: (p: string) => versioned(p) }).then((M) => {
  if (M.ccall("mathengine_init", "number", [], []) !== 0) throw new Error("Lean runtime failed to initialize");
  return wasmCall(M);
});

/** The engine trapped (wasm ran out of stack or memory, or Lean aborted) part way through a call. */
let crashed: Error | null = null;

/** The request's id, to answer with when the engine itself cannot (it failed to load, or crashed). */
const idOf = (raw: string): string => /^\{"jsonrpc":"2\.0","id":(\d+|"(?:[^"\\]|\\.)*")/.exec(raw)?.[1] ?? "null";
const errorReply = (raw: string, message: string) => `{"jsonrpc":"2.0","id":${idOf(raw)},"error":{"code":-32000,"message":${JSON.stringify(message)}}}`;

const scope = self as unknown as DedicatedWorkerGlobalScope;
scope.onmessage = async (ev: MessageEvent<string>) => {
  const raw = ev.data;
  let call: (req: string) => string;
  try { call = await ready; }
  catch (e) { scope.postMessage(errorReply(raw, e instanceof Error ? e.message : String(e))); return; }
  if (crashed) { scope.postMessage(errorReply(raw, crashed.message)); return; }
  let out: string;
  try { out = call(raw); }
  catch (e) {
    // The call stopped in the middle of the Lean code, which had already taken the session store
    // (engine/c/shim.c): nothing the runtime holds can be trusted now, so this is not an error reply
    // but the worker failing. Uncaught, it reaches the page as the worker's error, which fails every
    // pending call and offers the restart that rebuilds the sessions (apps/notebook: kernelFailed).
    crashed = new Error(`the engine crashed: ${e instanceof Error ? e.message : String(e)}`);
    const err = crashed;
    setTimeout(() => { throw err; });
    return;
  }
  scope.postMessage(out);
};
