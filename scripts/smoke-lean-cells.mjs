// Lean cells, end to end in Chromium: the bundled notebook (npm run lean-wasm && npm run bundle) opens a
// notebook with Lean cells, Lean (compiled to wasm, in the browser) checks them, the #eval cell shows the
// value computed from the cell above, and with the cursor in a proof the Lean goals tab shows its goals.
//   node scripts/smoke-lean-cells.mjs [screenshot.png]
// Chromium: playwright-core's own, or the executable named by CHROMIUM.
import { chromium } from "playwright-core";
import { createServer } from "node:http";
import { readFileSync, statSync } from "node:fs";
import path from "node:path";

const dist = path.resolve(import.meta.dirname, "../apps/notebook/dist");
const shot = process.argv[2];
const types = { ".html": "text/html", ".js": "text/javascript", ".css": "text/css", ".wasm": "application/wasm", ".json": "application/json", ".svg": "image/svg+xml" };
// the headers a host serving Lean cells sends (or the page's service worker adds): SharedArrayBuffer
const server = createServer((req, res) => {
  const file = path.join(dist, decodeURIComponent(new URL(req.url, "http://x").pathname));
  try { if (!statSync(file).isFile()) throw 0; } catch { res.writeHead(404); res.end(); return; }
  res.writeHead(200, { "content-type": types[path.extname(file)] ?? "application/octet-stream",
    "cross-origin-opener-policy": "same-origin", "cross-origin-embedder-policy": "require-corp" });
  res.end(readFileSync(file));
}).listen(0);
const port = server.address().port;

const doc = { v: 1, n: "lean-cells.chalk", c: [
  { s: "## Lean cells\nDefinitions carry from one Lean cell to the next.", t: "markdown" },
  { s: "def double (n : Nat) : Nat := n + n", t: "lean" },
  { s: "#eval double 21", t: "lean" },
  { s: "diff(x^2 * sin(x), x)" },
  { s: "theorem and_swap (p q : Prop) (hp : p) (hq : q) : q ∧ p := by\n  constructor\n  · exact hq\n  · exact hp", t: "lean" },
] };
const browser = await chromium.launch({ ...(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {}), args: ["--no-sandbox"] });
const page = await browser.newPage({ viewport: { width: 1400, height: 950 } });
page.on("pageerror", (e) => { if (!/^unsupported/.test(e.message)) console.log(`[page error] ${e.message}`); });   // "unsupported": a VS Code API lean4monaco does not provide, harmless
const t0 = Date.now();
await page.goto(`http://localhost:${port}/index.html#nbj=${Buffer.from(JSON.stringify(doc)).toString("base64url")}`);
const checks = [];
const check = (name, ok, detail = "") => { checks.push(ok); console.log(`${ok ? "ok  " : "FAIL"} ${name}${detail ? ` (${detail})` : ""}`); };

check("cross-origin isolated", await page.evaluate(() => self.crossOriginIsolated));
const got42 = await page.waitForFunction(() => [...document.querySelectorAll(".leanmsg .text")].some((e) => e.textContent.trim() === "42"), null, { timeout: 180000 }).then(() => true, () => false);
check("#eval double 21 shows 42 from the cell above", got42, `${Date.now() - t0} ms after load`);
check("the math cell still evaluates", await page.evaluate(() => !!document.querySelector(".cell.done")));

await page.evaluate(() => [...document.querySelectorAll(".ptab")].find((t) => t.textContent.includes("Lean goals"))?.click());
const views = await page.$$(".cell.lean .leanview");
const box = await views[2].boundingBox();
await page.mouse.click(box.x + 200, box.y + 30);   // the theorem's second line, `constructor`
await page.keyboard.press("End");
const goals = await page.waitForFunction(() => {
  const t = document.querySelector(".leaninfo iframe")?.contentDocument?.body?.innerText ?? "";
  return /2 goals/.test(t) && /⊢ q/.test(t) && /⊢ p/.test(t) ? t : false;
}, null, { timeout: 30000 }).then((h) => h.jsonValue(), () => false);
check("the Lean goals tab shows the goals at the cursor", !!goals, goals ? goals.split("\n")[0] : "");
if (shot) await page.screenshot({ path: shot });
await browser.close();
server.close();
process.exit(checks.every(Boolean) ? 0 : 1);
