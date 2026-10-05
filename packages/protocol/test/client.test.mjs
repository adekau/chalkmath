// createClient and serve: every call settles (ARCHITECTURE.md §2, rule 6), whatever the far end sends.
import { test } from "node:test";
import assert from "node:assert/strict";
import { createClient, serve, RpcError } from "../dist/index.js";

/** A transport whose far end the test plays: `reply(text)` delivers a message, `sent` holds what was sent. */
function fakeTransport() {
  const sent = [];
  let handler = () => {};
  let onError = () => {};
  return {
    sent, reply: (m) => handler(m), fail: (e) => onError(e),
    send: (m) => { sent.push(m); }, onMessage: (h) => { handler = h; }, onError: (h) => { onError = h; }, close: () => { sent.push("<closed>"); },
  };
}
const idOf = (m) => JSON.parse(m).id;

test("a reply with the call's id settles it, with the result or an error carrying the code", async () => {
  const t = fakeTransport();
  const c = createClient(t);
  const a = c.call("engine.capabilities", {});
  const b = c.call("engine.evaluate", { sessionId: "s", cellId: "c", source: "x" });
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: idOf(t.sent[1]), error: { code: -32601, message: "unknown method", data: { m: "x" } } }));
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: idOf(t.sent[0]), result: { engine: "e" } }));
  assert.deepEqual(await a, { engine: "e" });
  const e = await b.catch((e) => e);
  assert.ok(e instanceof RpcError);
  assert.equal(e.code, -32601); assert.equal(e.message, "-32601: unknown method"); assert.equal(e.detail, "unknown method"); assert.deepEqual(e.data, { m: "x" });
});

test("a reply that is not JSON-RPC fails the oldest call, and the next reply still finds its call", async () => {
  const t = fakeTransport();
  const c = createClient(t);
  const a = c.call("engine.capabilities", {});
  const b = c.call("engine.capabilities", {});
  t.reply("Stack overflow detected. Aborting.");
  await assert.rejects(a, /not JSON-RPC: Stack overflow/);
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: idOf(t.sent[1]), result: 2 }));
  assert.equal(await b, 2);
});

test("an error reply with no id (the request could not be read) fails the oldest call", async () => {
  const t = fakeTransport();
  const c = createClient(t);
  const a = c.call("engine.capabilities", {});
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: null, error: { code: -32600, message: "request body larger than 1000 bytes" } }));
  const e = await a.catch((e) => e);
  assert.ok(e instanceof RpcError); assert.equal(e.code, -32600); assert.match(e.message, /larger than 1000 bytes/);
  // a notification (no id, no error) is dropped and leaves the calls pending
  const b = c.call("engine.capabilities", {});
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: null, result: 1 }));
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: 999, result: 1 }));
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: idOf(t.sent[1]), result: "b" }));
  assert.equal(await b, "b");
});

test("a send that throws fails that call only, and does not take the next failure meant for another", async () => {
  const t = fakeTransport();
  let broken = true;
  const send = t.send; t.send = (m) => { if (broken) throw new Error("socket closed"); send(m); };
  const c = createClient(t);
  await assert.rejects(c.call("engine.capabilities", {}), /socket closed/);
  broken = false;
  const b = c.call("engine.capabilities", {});
  t.reply("garbage");   // the oldest pending call is b, not the one whose send failed
  await assert.rejects(b, /not JSON-RPC: garbage/);
});

test("closing the client fails what is in flight, and the transport's failure fails everything and is reported", async () => {
  const t = fakeTransport();
  const c = createClient(t);
  const seen = [];
  c.onError((e) => seen.push(e.message));
  const a = c.call("engine.capabilities", {});
  t.fail(new Error("the worker died"));
  await assert.rejects(a, /the worker died/);
  assert.deepEqual(seen, ["the worker died"]);
  const b = c.call("engine.capabilities", {});
  c.close();
  await assert.rejects(b, /connection was closed/);
  assert.equal(t.sent.at(-1), "<closed>");
});

test("serve answers every message: a parse error, a bad request, an engine error with its code, a result", async () => {
  const t = fakeTransport();
  const out = [];
  t.send = (m) => out.push(JSON.parse(m));
  serve(t, { async handle(method, params) {
    if (method === "boom") throw new RpcError(-32601, "unknown method", { method });
    if (method === "throw") throw new Error("plain");
    return { method, params };
  } });
  t.reply("not json");
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: 1 }));
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: 2, method: "boom", params: {} }));
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: 3, method: "throw", params: {} }));
  t.reply(JSON.stringify({ jsonrpc: "2.0", id: 4, method: "ok", params: { a: 1 } }));
  await new Promise((r) => setTimeout(r, 10));
  assert.deepEqual(out, [
    { jsonrpc: "2.0", id: null, error: { code: -32700, message: "Parse error" } },
    { jsonrpc: "2.0", id: null, error: { code: -32600, message: "Invalid Request" } },
    { jsonrpc: "2.0", id: 2, error: { code: -32601, message: "unknown method", data: { method: "boom" } } },
    { jsonrpc: "2.0", id: 3, error: { code: -32000, message: "plain" } },
    { jsonrpc: "2.0", id: 4, result: { method: "ok", params: { a: 1 } } },
  ]);
});
