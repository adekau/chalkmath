import { spawn } from "node:child_process";
import { createClient, type EngineClient } from "@chalkmath/protocol";
import { stdioTransport } from "./transports.js";

export interface LeanNativeOptions {
  /** A call that takes longer than this kills the process (it serves one request at a time, so a
   *  stuck one blocks every other) and fails what was in flight. Unset: no deadline. */
  timeoutMs?: number | undefined;
}

const LOST = "; it restarts on the next request, without the sessions it held";

/** Self-hosted / test path: the native Lean exe over stdio. A process that stops (Lean aborts on a
 *  stack overflow, or the deadline killed it) fails the calls in flight, and the next call starts a
 *  new one: the sessions the old one held are gone, which the error says. */
export function leanNativeClient(exe = "engine/.lake/build/bin/mathengine", opts: LeanNativeOptions = {}): EngineClient {
  type Running = { client: EngineClient; kill(): void };
  let current: Running | null = null;
  let closed = false;
  const listeners: ((e: Error) => void)[] = [];
  const start = (): Running => {
    const proc = spawn(exe, [], { stdio: ["pipe", "pipe", "inherit"] });
    const client = createClient(stdioTransport(proc));
    const me: Running = { client, kill: () => proc.kill("SIGKILL") };
    client.onError?.((e) => {
      if (current === me) current = null;
      for (const l of listeners) l(new Error(e.message + LOST));
    });
    return me;
  };
  return {
    call(method, params) {
      if (closed) return Promise.reject(new Error("the engine connection was closed"));
      const me = (current ??= start());
      // the transport's own failures (the process stopped, or never ran) are the ones that lose sessions
      const reply = me.client.call(method, params).catch((e: Error) => {
        throw /^the engine (process stopped|could not run)/.test(e.message) ? new Error(e.message + LOST) : e;
      });
      const ms = opts.timeoutMs;
      if (!ms) return reply;
      let timer: ReturnType<typeof setTimeout> | undefined;
      const deadline = new Promise<never>((_, reject) => {
        timer = setTimeout(() => {
          reject(new Error(`the engine took longer than ${ms / 1000} s and was stopped${LOST}`));
          if (current === me) current = null;
          me.kill();
        }, ms);
      });
      return Promise.race([reply, deadline]).finally(() => clearTimeout(timer));
    },
    close() { closed = true; current?.client.close(); current = null; },
    onError(handler) { listeners.push(handler); },
  };
}
