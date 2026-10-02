import { spawnSync } from "node:child_process";
import { readFileSync, readdirSync } from "node:fs";
const dir = process.argv[2];
const extra = JSON.parse(process.argv[3] ?? "{}");
const run = (ms) => { if (!ms.length) return []; const r = spawnSync("engine/.lake/build/bin/mathengine", { input: ms.map((m, i) => JSON.stringify({ jsonrpc: "2.0", id: i, ...m })).join("\n") + "\n", encoding: "utf8", maxBuffer: 1 << 28 }); return r.stdout.trim().split("\n").map((l) => JSON.parse(l).result); };
let bad = 0;
for (const f of readdirSync(dir).sort()) {
  const cells = JSON.parse(readFileSync(dir + f, "utf8")).cells;
  const msgs = []; const meta = [];
  cells.forEach((c, i) => {
    if (c.type === "exercise" && !c.lean) { msgs.push({ method: "engine.check", params: { sessionId: "s", cellId: `q${i}`, source: c.src } }); meta.push(["solve", c.src]); }
    else if (!c.type) { msgs.push({ method: "engine.evaluate", params: { sessionId: "s", cellId: `c${i}`, source: c.src } }); meta.push(["eval", c.src]); }
  });
  const res = run(msgs);
  const msgs2 = []; const meta2 = [];
  msgs.forEach((m, i) => {
    if (meta[i][0] === "eval") { msgs2.push(m); meta2.push(null); return; }
    if (!res[i].ok) { console.log(`ERR  ${f.slice(0, 2)} ${meta[i][1]}: ${res[i].error.message}`); bad++; return; }
    for (const a of [res[i].rendered.text, ...(extra[meta[i][1]] ?? [])]) { msgs2.push({ method: "engine.check", params: { ...m.params, answer: a } }); meta2.push([meta[i][1], a]); }
  });
  run(msgs2).forEach((r, i) => { if (!meta2[i]) return; if (!r.equivalent) bad++; console.log(`${r.equivalent ? "ok  " : "FAIL"} ${f.slice(0, 2)} ${meta2[i][0]}  ←  ${meta2[i][1]}${r.answer?.ok === false ? "  " + r.answer.error.message : ""}`); });
}
console.log(bad ? `${bad} problems` : "all exercises accept their answers");
