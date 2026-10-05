import { test } from "node:test";
import assert from "node:assert/strict";
import { startLeanServer, rangeTokensOnly } from "../dist/lean-server.js";

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

test("and answers `initialize` with that, before Lean starts", () => {
  const sent = [];
  const module = { _leanweb_in_buf: () => 0, _leanweb_in_cap: () => 0, _leanweb_in_w: () => 0, _leanweb_in_r: () => 0 };
  const server = startLeanServer({ module, library: [], initializeResult: native, send: (m) => sent.push(m) });
  server.receive({ jsonrpc: "2.0", id: 1, method: "initialize", params: {} });
  assert.equal(sent.length, 1);
  assert.equal(sent[0].id, 1);
  assert.equal(sent[0].result.capabilities.semanticTokensProvider.full, false);
});
