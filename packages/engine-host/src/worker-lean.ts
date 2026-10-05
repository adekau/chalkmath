/// <reference lib="webworker" />
/**
 * Web-worker host for the Lean engine compiled to wasm (scripts/build-wasm.sh).
 * Mirrors worker.ts: same Transport, same protocol, different engine behind it.
 */
import { serve } from "@chalkmath/protocol";
import { workerSelfTransport } from "./transports.js";

type Module = {
  ccall(name: string, ret: string, argTypes: string[], args: unknown[]): unknown;
  cwrap(name: string, ret: string | null, argTypes: string[]): (...a: unknown[]) => unknown;
  UTF8ToString(ptr: number): string;
};
declare const createMathEngine: (opts?: object) => Promise<Module>;
declare const __BUILD_ID__: string;
const stamp = typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev";

importScripts(`engine-lean.js?v=${stamp}`);

const ready = createMathEngine({ locateFile: (p: string) => `${p}?v=${stamp}` }).then((M) => {
  if (M.ccall("mathengine_init", "number", [], []) !== 0) throw new Error("Lean runtime failed to initialize");
  const call = M.cwrap("mathengine_call", "number", ["string"]) as (s: string) => number;
  const free = M.cwrap("mathengine_free", null, ["number"]) as (p: number) => void;
  return (req: string): string => { const p = call(req); const out = M.UTF8ToString(p); free(p); return out; };
});

/** The engine trapped (wasm ran out of stack or memory, or Lean aborted) part way through a call. */
let crashed: Error | null = null;

serve(workerSelfTransport(self as unknown as DedicatedWorkerGlobalScope), {
  async handle(method, params) {
    const call = await ready;
    if (crashed) throw crashed;
    let raw: string;
    try { raw = call(JSON.stringify({ jsonrpc: "2.0", id: 1, method, params })); }
    catch (e) {
      // The call stopped in the middle of the Lean code, which had already taken the session store
      // (engine/c/shim.c): nothing the runtime holds can be trusted now, so this is not an error reply
      // but the worker failing. Uncaught, it reaches the page as the worker's error, which fails every
      // pending call and offers the restart that rebuilds the sessions (apps/notebook: kernelFailed).
      crashed = new Error(`the engine crashed: ${e instanceof Error ? e.message : String(e)}`);
      const err = crashed;
      setTimeout(() => { throw err; });
      return new Promise<never>(() => {});
    }
    const res = JSON.parse(raw);
    if (res.error) throw new Error(res.error.message);
    return res.result;
  },
});
