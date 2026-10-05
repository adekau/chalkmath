/** The Emscripten module the engine's wasm build exports (scripts/build-wasm.sh). */
export interface WasmModule {
  ccall(name: string, ret: string, argTypes: string[], args: unknown[]): unknown;
  cwrap(name: string, ret: string | null, argTypes: string[]): (...a: unknown[]) => unknown;
  UTF8ToString(ptr: number): string;
  stringToUTF8(s: string, ptr: number, max: number): void;
  lengthBytesUTF8(s: string): number;
  _malloc(n: number): number;
  _free(p: number): void;
}

/** `mathengine_call` as a function from a request string to a reply string. The request is written
 *  into memory `malloc` gives, not the wasm stack: `cwrap`'s own `"string"` conversion puts the
 *  argument on the stack, which is the 1 MB the engine recurses on (`-sSTACK_SIZE`), so a large
 *  request would trap before the engine read it, and a smaller one took its size out of what the
 *  engine had left. The reply is read and then handed back to the engine to free. */
export function wasmCall(M: WasmModule): (req: string) => string {
  const call = M.cwrap("mathengine_call", "number", ["number"]) as (p: number) => number;
  const free = M.cwrap("mathengine_free", null, ["number"]) as (p: number) => void;
  return (req) => {
    const n = M.lengthBytesUTF8(req) + 1;
    const p = M._malloc(n);
    if (!p) throw new Error(`the engine is out of memory (a request of ${n} bytes)`);
    let out: number;
    try { M.stringToUTF8(req, p, n); out = call(p); }
    finally { M._free(p); }
    try { return M.UTF8ToString(out); }
    finally { free(out); }
  };
}
