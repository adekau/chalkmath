// Lean cells, end to end in Chromium: the bundled notebook (npm run lean-wasm && npm run bundle) opens a
// notebook with Lean cells, Lean (compiled to wasm, in the browser) checks them, the #eval cell shows the
// value computed from the cell above, and with the cursor in a proof the Lean goals tab shows its goals.
// A Lean exercise is judged as Lean checks the reader's proof (a sorry, an error, then a proof), and a
// lesson of a course with a Lean prelude proves a theorem with one from the lesson before it.
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
const fetched = [];   // Lean's large files, as the server sent them
const server = createServer((req, res) => {
  if (/lean-(server\.wasm|lib\.pack)/.test(req.url)) fetched.push(req.url.split("?")[0]);
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
  { s: "theorem double_eq (n : Nat) : double n = 2 * n := by", t: "exercise", ln: 1, p: "Prove it.", hs: ["Unfold `double`."], lso: "  unfold double\n  omega" },
] };
// a course whose lessons share their Lean: the second proves a theorem with the first's
const course = { projects: [{ id: "smoke", title: "Smoke course", blurb: "", kind: "course", path: "smoke", leanPrelude: true, lessons: [
  { file: "one.chalk", title: "One", blurb: "" }, { file: "two.chalk", title: "Two", blurb: "" }] }] };
const lessons = {
  "one.chalk": { chalk: 1, name: "one.chalk", scenes: [], cells: [
    { src: "def triple (n : Nat) : Nat := n + n + n", type: "lean", showWork: false, label: null },
    { src: "theorem triple_eq (n : Nat) : triple n = 3 * n := by", type: "exercise", lean: true, leanSolution: "  unfold triple\n  omega", showWork: false, label: null }] },
  "two.chalk": { chalk: 1, name: "two.chalk", scenes: [], cells: [
    { src: "theorem triple_twice (n : Nat) : triple (triple n) = 9 * n := by", type: "exercise", lean: true, leanSolution: "  rw [triple_eq, triple_eq]\n  omega", showWork: false, label: null }] },
};
const browser = await chromium.launch({ ...(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {}), args: ["--no-sandbox", "--disk-cache-size=100000000"] });   // an HTTP cache too small for the library: the worker's store must keep it
const page = await browser.newPage({ viewport: { width: 1400, height: 950 } });
await page.route("**/examples/courses.json*", (r) => r.fulfill({ contentType: "application/json", body: JSON.stringify(course) }));
await page.route("**/examples/smoke/*", (r) => r.fulfill({ contentType: "application/json", body: JSON.stringify(lessons[new URL(r.request().url()).pathname.split("/").pop()]) }));
page.on("pageerror", (e) => { if (!/^unsupported/.test(e.message)) console.log(`[page error] ${e.message}`); });   // "unsupported": a VS Code API lean4monaco does not provide, harmless
// every loading status the page shows, as it shows them
await page.addInitScript(() => {
  const seen = (window.__leanStatus = []);
  new MutationObserver(() => {
    const t = document.querySelector(".leanstatus .leanstate")?.textContent;
    if (t && seen.at(-1) !== t) seen.push(t);
  }).observe(document, { subtree: true, childList: true, characterData: true });
});
const t0 = Date.now();
await page.goto(`http://localhost:${port}/index.html#nbj=${Buffer.from(JSON.stringify(doc)).toString("base64url")}`);
const checks = [];
const check = (name, ok, detail = "") => { checks.push(ok); console.log(`${ok ? "ok  " : "FAIL"} ${name}${detail ? ` (${detail})` : ""}`); };

check("cross-origin isolated", await page.evaluate(() => self.crossOriginIsolated));
const got42 = await page.waitForFunction(() => [...document.querySelectorAll(".leanmsg .text")].some((e) => e.textContent.trim() === "42"), null, { timeout: 180000 }).then(() => true, () => false);
check("#eval double 21 shows 42 from the cell above", got42, `${Date.now() - t0} ms after load`);
const statuses = await page.evaluate(() => window.__leanStatus);
check("the loading status showed the download", statuses.some((t) => /Downloading Lean and its library: [\d.]+ of [\d.]+ MB/.test(t)),
  `${statuses.length} updates, last: ${statuses.at(-1) ?? "none"}`);
await page.waitForFunction(() => !document.querySelector(".leanstatus"), null, { timeout: 60000 }).catch(() => {});
check("and is gone once Lean has checked the notebook", await page.evaluate(() => !document.querySelector(".leanstatus")));
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

// a Lean exercise: the proof it starts with is a sorry; then an error; then a proof
const verdict = (re, cell = ".cell.exercise") => page.waitForFunction(([sel, src]) => new RegExp(src).test(document.querySelector(`${sel} .xc-verdict`)?.textContent ?? ""),
  [cell, re.source], { timeout: 60000 }).then(() => true, () => false);
check("a Lean exercise starts not proved (its sorry)", await verdict(/Not yet: the proof still has a sorry/));
/** Replace the reader's proof, line by line (Escape: no completion takes the newline). */
async function prove(lines, cell = ".cell.exercise") {
  const b = await page.locator(`${cell} .xc-leanproof`).last().boundingBox();
  await page.mouse.click(b.x + 80, b.y + 10);
  await page.keyboard.press("Control+A");
  for (const [k, l] of lines.entries()) {
    if (k) { await page.keyboard.press("Escape"); await page.keyboard.press("Enter"); await page.keyboard.press("Home"); await page.keyboard.press("Shift+End"); }
    await page.keyboard.type(l);
  }
  await page.keyboard.press("Escape");
}
await prove(["  rfl"]);
check("a proof Lean rejects is not proved, with Lean's message", await verdict(/Not yet: Lean reports an error/) && await page.locator(".cell.exercise .leanmsg.error").count() > 0);
await prove(["  unfold double", "  omega"]);
check("a proof Lean accepts is proved", await verdict(/Proved/));
check("and the outline marks it", (await page.locator(".olrow.exercise .num").textContent()) === "✓");

// a course with a Lean prelude: lesson two's theorem is proved with lesson one's
await page.evaluate(() => [...document.querySelectorAll(".menus span")].find((m) => m.textContent === "File")?.click());
await page.locator(".dropdown .item", { hasText: "Courses and examples" }).click();
await page.locator(".crscard", { hasText: "Smoke course" }).click();
await page.locator(".crslesson").nth(1).locator(".crsgo").click();
await page.locator(".lessonbar .lbwhere", { hasText: "Lesson 2 of 2" }).waitFor({ timeout: 30000 });
await prove(["  rw [triple_eq, triple_eq]", "  omega"]);
check("a lesson proves a theorem with the lesson before it's (its Lean prelude)", await verdict(/Proved/));
await page.locator(".tabbar .tab", { hasText: "lean-cells" }).click();

// a reload loads Lean from the browser's store, not the network
fetched.length = 0;
const t1 = Date.now();
await page.reload();
const again = await page.waitForFunction(() => [...document.querySelectorAll(".leanmsg .text")].some((e) => e.textContent.trim() === "42"), null, { timeout: 180000 }).then(() => true, () => false);
check("after a reload, #eval shows 42 again", again, `${Date.now() - t1} ms after reload`);
check("and Lean's large files came from the browser's store", fetched.length === 0, fetched.join(", ") || "nothing downloaded");
const later = await page.evaluate(() => window.__leanStatus);
check("so the status never said it was downloading", !later.some((t) => /Downloading/.test(t)), later.join(" → "));
await browser.close();
server.close();
process.exit(checks.every(Boolean) ? 0 : 1);
