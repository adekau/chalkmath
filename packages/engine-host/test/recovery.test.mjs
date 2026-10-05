import { test } from "node:test";
import assert from "node:assert/strict";
import { createServer } from "node:http";
import { PassThrough } from "node:stream";
import { createClient } from "@chalkmath/protocol";
import { leanNativeClient } from "../dist/lean-native.js";
import { startServer } from "../dist/server.js";
import { httpTransport, stdioTransport } from "../dist/index.js";

const standIn = new URL("./fixtures/stand-in-engine.mjs", import.meta.url).pathname;

test("native host: an engine that stops fails its call, and the next call starts a new one", async () => {
  const c = leanNativeClient(standIn);
  const { pid } = await c.call("ping", {});
  await assert.rejects(c.call("die", {}), /process stopped \(exit code 3\).*without the sessions it held/);
  const again = await c.call("ping", {});
  assert.notEqual(again.pid, pid);
  c.close();
});

test("native host: a call past the deadline stops the engine instead of blocking every other", async () => {
  const c = leanNativeClient(standIn, { timeoutMs: 300 });
  const { pid } = await c.call("ping", {});
  await assert.rejects(c.call("hang", {}), /took longer than 0.3 s/);
  assert.notEqual((await c.call("ping", {})).pid, pid);
  c.close();
});

test("native host: a reply that is not JSON fails that call, and the engine keeps serving", async () => {
  const c = leanNativeClient(standIn);
  const { pid } = await c.call("ping", {});
  await assert.rejects(c.call("garbage", {}), /not JSON-RPC: Stack overflow/);
  assert.equal((await c.call("ping", {})).pid, pid);
  c.close();
});

test("native host: a missing executable is an error, not a crash", async () => {
  const c = leanNativeClient("/nonexistent/mathengine");
  await assert.rejects(c.call("ping", {}), /could not run/);
  c.close();
});

test("stdio transport: a character split between two chunks of the pipe arrives whole", async () => {
  const stdout = new PassThrough();
  const t = stdioTransport({ stdin: new PassThrough(), stdout });
  const got = new Promise((r) => t.onMessage(r));
  const line = Buffer.from(JSON.stringify({ text: "λ⊢ℯ" }) + "\n");
  const cut = line.indexOf(Buffer.from("⊢")) + 1;   // inside the three bytes of ⊢
  stdout.write(line.subarray(0, cut)); stdout.write(line.subarray(cut));
  assert.equal(JSON.parse(await got).text, "λ⊢ℯ");
});

test("HTTP transport: an error page from a proxy fails the call instead of leaving it pending", async () => {
  const proxy = createServer((_, res) => { res.writeHead(502, { "content-type": "text/html" }); res.end("<h1>Bad Gateway</h1>"); });
  await new Promise((r) => proxy.listen(0, "localhost", r));
  const c = createClient(httpTransport(`http://localhost:${proxy.address().port}`));
  await assert.rejects(c.call("engine.capabilities", {}), /answered HTTP 502 Bad Gateway/);
  proxy.close();
});

test("HTTP host: bodies that are not requests are answered, and the host stays up", async () => {
  const server = startServer(0, standIn, { maxBody: 1000 });
  await new Promise((r) => server.once("listening", r));
  const url = `http://localhost:${server.address().port}`;
  for (const body of ["null", "5", "\"x\"", "{}"]) {
    const r = await fetch(url, { method: "POST", body });
    assert.equal((await r.json()).error.code, -32600, body);
  }
  const big = await fetch(url, { method: "POST", body: "x".repeat(5000) }).catch((e) => e);
  if (!(big instanceof Error)) assert.equal(big.status, 413);   // the host may close the socket first
  const c = createClient(httpTransport(url));
  assert.ok((await c.call("ping", {})).pid > 0);
  server.close();
});
