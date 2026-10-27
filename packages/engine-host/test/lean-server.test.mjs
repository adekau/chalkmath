import { test } from "node:test";
import assert from "node:assert/strict";
import { startLeanServer, rangeTokensOnly, leanThreads } from "../dist/lean-server.js";

// what engine/wasm/server/capabilities.lean prints: the native watchdog's reply
const native = { capabilities: { hoverProvider: true, semanticTokensProvider: { full: true, range: true, legend: { tokenTypes: ["keyword"], tokenModifiers: [] } } }, serverInfo: { name: "Lean 4 Server" } };

test("the in-browser watchdog offers semantic tokens for ranges only", () => {
  const r = rangeTokensOnly(native);
  assert.deepEqual(r.capabilities.semanticTokensProvider, { full: false, range: true, legend: { tokenTypes: ["keyword"], tokenModifiers: [] } });
  assert.equal(r.capabilities.hoverProvider, true);
  assert.deepEqual(r.serverInfo, native.serverInfo);
  assert.equal(native.capabilities.semanticTokensProvider.full, true);   // the reply it was given is left as it is
  assert.deepEqual(rangeTokensOnly({ capabilities: {} }), { capabilities: {} });
});

test("Lean runs a thread per core in a browser, between 2 and 8, and 4 when the browser does not say", () => {
  assert.equal(leanThreads(12), 8);
  assert.equal(leanThreads(6), 6);
  assert.equal(leanThreads(1), 2);
  assert.equal(leanThreads(undefined), 4);
  assert.equal(leanThreads(0), 4);
});

test("and answers `initialize` with that, before Lean starts", () => {
  const sent = [];
  const module = { _leanweb_in_buf: () => 0, _leanweb_in_cap: () => 0, _leanweb_in_w: () => 0, _leanweb_in_r: () => 0 };
  const server = startLeanServer({ module, library: [], initializeResult: native, send: (m) => sent.push(m) });
  server.receive({ jsonrpc: "2.0", id: 1, method: "initialize", params: {} });
  assert.equal(sent.length, 1);
  assert.equal(sent[0].id, 1);
  assert.equal(sent[0].result.capabilities.semanticTokensProvider.full, false);
});

test("Lean's process ending is reported, but not the module's own main returning as Lean starts", () => {
  const exits = [];
  const ring = new SharedArrayBuffer(1 << 16);   // room for the handshake, which nothing reads here
  const module = {
    HEAP32: new Int32Array(ring), HEAPU8: new Uint8Array(ring), ENV: {},
    FS: { mkdirTree() {}, writeFile() {} },
    _leanweb_in_buf: () => 16, _leanweb_in_cap: () => 60000, _leanweb_in_w: () => 0, _leanweb_in_r: () => 4,
    // PROXY_TO_PTHREAD: `main` starts Lean's on a thread and exits with 0 at once
    callMain() { module.leanExit?.(0); },
  };
  const server = startLeanServer({ module, library: [], initializeResult: native, send: () => {}, onExit: (c) => exits.push(c) });
  server.receive({ jsonrpc: "2.0", id: 1, method: "initialize", params: {} });
  server.receive({ jsonrpc: "2.0", method: "textDocument/didOpen", params: { textDocument: { uri: "file:///a.lean", languageId: "lean4", version: 1, text: "" } } });
  assert.deepEqual(exits, []);
  module.leanExit(2);   // the file worker, when the document's imports change
  assert.deepEqual(exits, [2]);
});
