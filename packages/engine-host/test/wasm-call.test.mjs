// The worker's call into the wasm engine, against a stand-in module with a byte array for memory:
// the request goes to the heap (not the stack) as UTF-8, whole, and both strings are freed.
import { test } from "node:test";
import assert from "node:assert/strict";
import { wasmCall } from "../dist/wasm-call.js";

function fakeModule(answer) {
  const mem = new Uint8Array(1 << 16);
  let next = 8;
  const live = new Set();
  const enc = new TextEncoder(), dec = new TextDecoder();
  const cstr = (p) => { let e = p; while (mem[e] !== 0) e++; return dec.decode(mem.subarray(p, e)); };
  const M = {
    seen: [], freed: [],
    lengthBytesUTF8: (s) => enc.encode(s).length,
    stringToUTF8: (s, p, max) => { const b = enc.encode(s); assert.ok(b.length + 1 <= max, "the buffer holds the string and its NUL"); mem.set(b, p); mem[p + b.length] = 0; },
    UTF8ToString: (p) => cstr(p),
    _malloc: (n) => { const p = next; next += n + (8 - (n % 8)) % 8; live.add(p); return p; },
    _free: (p) => { assert.ok(live.has(p), "freed once, something malloc gave"); live.delete(p); M.freed.push(p); },
    cwrap: (name) => name === "mathengine_call"
      ? (p) => { M.seen.push(cstr(p)); const out = M._malloc(1 << 12); M.stringToUTF8(answer(M.seen.at(-1)), out, 1 << 12); return out; }
      : (p) => M._free(p),
    ccall: () => 0,
  };
  return M;
}

test("the request reaches the engine whole, as UTF-8, and the reply comes back; nothing stays allocated", () => {
  const M = fakeModule((req) => `{"jsonrpc":"2.0","id":1,"result":${JSON.stringify(req.length)}}`);
  const call = wasmCall(M);
  const req = '{"jsonrpc":"2.0","id":1,"method":"engine.evaluate","params":{"source":"λx. x ⊢ ℯ^2 — ∑"}}';
  assert.equal(call(req), `{"jsonrpc":"2.0","id":1,"result":${req.length}}`);
  assert.deepEqual(M.seen, [req]);
  assert.equal(M.freed.length, 2);   // the request's buffer and the reply
});

test("a request larger than the wasm stack still goes through (it is on the heap)", () => {
  const M = fakeModule(() => '{"ok":true}');
  const big = "x".repeat(40_000);
  assert.equal(wasmCall(M)(big), '{"ok":true}');
  assert.equal(M.seen[0].length, 40_000);
});

test("an engine that traps frees the request and lets the error through", () => {
  const M = fakeModule(() => "");
  M.cwrap = (name) => name === "mathengine_call" ? () => { throw new RangeError("Maximum call stack size exceeded"); } : (p) => M._free(p);
  assert.throws(() => wasmCall(M)("{}"), /Maximum call stack/);
  assert.equal(M.freed.length, 1);
});
