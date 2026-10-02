import { spawnSync } from "node:child_process";
const srcs = process.argv.slice(2);
const msgs = srcs.map((s, i) => JSON.stringify({ jsonrpc: "2.0", id: i, method: "engine.evaluate", params: { sessionId: "t", cellId: `c${i}`, source: s, showWork: true } }));
const t0 = Date.now();
const r = spawnSync("engine/.lake/build/bin/mathengine", { input: msgs.join("\n") + "\n", encoding: "utf8", maxBuffer: 1 << 28 });
r.stdout.trim().split("\n").forEach((l, i) => { const j = JSON.parse(l).result; console.log(srcs[i], "=>", j.ok ? j.rendered.text + (j.summary ? `   [${j.summary}]` : "") + `  (${j.derivation?.steps.length} steps)` : `ERROR ${j.error.message}`); });
console.log(`${Date.now() - t0} ms`);
