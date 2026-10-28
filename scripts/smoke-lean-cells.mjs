// Lean cells, end to end in Chromium: the bundled notebook (npm run lean-wasm && npm run bundle) opens a
// notebook with Lean cells, Lean (compiled to wasm, in the browser) checks them, the #eval cell shows the
// value computed from the cell above, and with the cursor in a proof the Lean goals tab shows its goals.
// A Lean exercise is judged as Lean checks the reader's proof (a sorry, an error, then a proof), and a
// lesson of a course with a Lean prelude proves a theorem with one from the lesson before it. No error
// escapes into the page while it does.
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
// every error nothing caught: the notebook shows each to the reader ("Something went wrong on the page"),
// so none is harmless (the Lean extension's missing dependency once threw "unsupported" into the page)
const pageErrors = [];
page.on("pageerror", (e) => { pageErrors.push(e.message); console.log(`[page error] ${e.message}`); });
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
check("the top bar says Lean is ready", await page.waitForFunction(() => document.querySelector(".titlebar .leanpill")?.textContent === "Lean · ready", null, { timeout: 30000 }).then(() => true, () => false),
  await page.locator(".titlebar .leanpill").textContent().catch(() => "no pill"));
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

// Lean stops (recursion deeper than a browser thread's stack), says so on the cell, and starts again in the
// page on request, with what was typed after it stopped
const deep = { v: 1, n: "lean-deep.chalk", c: [
  { s: "def deep : Nat → Nat\n  | 0 => 0\n  | n + 1 => deep n + 1", t: "lean" },
  { s: "#eval deep 100000000", t: "lean" },
] };
check("no error escaped into the page", pageErrors.length === 0, pageErrors.join("; "));
await page.goto("about:blank");
await page.goto(`http://localhost:${port}/index.html#nbj=${Buffer.from(JSON.stringify(deep)).toString("base64url")}`);
const stopped = await page.waitForFunction(() => document.querySelector(".cell.lean .leanstate.failed")?.textContent ?? false, null, { timeout: 180000 })
  .then((h) => h.jsonValue(), () => false);
check("Lean stops on recursion deeper than its stack, and says so", !!stopped && /Lean stopped: it ran out of stack/.test(stopped), stopped || "no note");
const leanWorkers = () => page.workers().filter((w) => w.url().includes("lean-server.worker")).length;   // the server and its threads
const before = leanWorkers();
const restart = page.locator(".cell.lean .leanstate.failed button", { hasText: "Restart Lean" }).first();
check("with a button that restarts it", await restart.count() === 1);
const evalView = page.locator(".cell.lean .leanview").nth(1);
const eb = await evalView.boundingBox();
await page.mouse.click(eb.x + 120, eb.y + 10);
await page.keyboard.press("Control+A");
await page.keyboard.type("#eval deep 20");
await page.keyboard.press("Escape");
const t2 = Date.now();
await restart.click();
const twenty = await page.waitForFunction(() => [...document.querySelectorAll(".leanmsg .text")].some((e) => e.textContent.trim() === "20"), null, { timeout: 180000 }).then(() => true, () => false);
check("restarted, Lean checks the notebook as edited since it stopped", twenty, `${Date.now() - t2} ms after the click`);
check("and the cell no longer says Lean stopped", await page.locator(".leanstate.failed").count() === 0);
check("the stopped server's workers are gone", leanWorkers() === before, `${leanWorkers()} of Lean's workers, ${before} before`);
await page.evaluate(() => [...document.querySelectorAll(".ptab")].find((t) => t.textContent.includes("Lean goals"))?.click());
const eb2 = await page.locator(".cell.lean .leanview").nth(1).boundingBox();
await page.mouse.click(eb2.x + 60, eb2.y + 10);
const goals2 = await page.waitForFunction(() => {
  const frames = document.querySelectorAll(".leaninfo iframe");
  const t = frames[0]?.contentDocument?.body?.innerText ?? "";
  return frames.length === 1 && /Notebook\.lean:5:/.test(t) && /\b20\b/.test(t) ? t : false;
}, null, { timeout: 30000 }).then((h) => h.jsonValue(), () => false);
check("and the Lean goals tab follows the new server", !!goals2, goals2 ? goals2.split("\n").slice(0, 3).join(" / ") : await page.evaluate(() => `${document.querySelectorAll(".leaninfo iframe").length} infoviews: ${document.querySelector(".leaninfo iframe")?.contentDocument?.body?.innerText.slice(0, 200)}`));
// imports are loaded once per process: when they change, Lean's file worker exits to be started again, as
// Lean's watchdog does natively; the page starts it again by itself, with the editors as they are
const workersNow = leanWorkers();
const fb = await page.locator(".cell.lean .leanview").first().boundingBox();
await page.mouse.click(fb.x + 120, fb.y + 10);
await page.keyboard.press("Control+Home");
await page.keyboard.type("import Init.Data.List.Lemmas");
await page.keyboard.press("Escape");
await page.keyboard.press("Enter");
const restarted = await page.waitForFunction(() => window.__leanStatus.at(-1) !== undefined && document.querySelector(".leanstatus"), null, { timeout: 30000 }).then(() => true, () => false);
const after = await page.waitForFunction(() => !document.querySelector(".leanstatus") && [...document.querySelectorAll(".leanmsg .text")].some((e) => e.textContent.trim() === "20"), null, { timeout: 120000 }).then(() => true, () => false);
check("a changed import starts Lean again by itself, and it checks the notebook", restarted && after && await page.locator(".leanstate.failed").count() === 0,
  `${await page.locator(".leanstate.failed").allTextContents()}`);
check("in place of the server it had", leanWorkers() === workersNow, `${leanWorkers()} of Lean's workers, ${workersNow} before`);
// the stopped thread's own error (Chromium reports a worker's as the page's) is all, and the page did not take it for its own
const others = pageErrors.filter((m) => !/Maximum call stack size exceeded/.test(m));
check("nothing else went wrong on the page", others.length === 0 && await page.locator(".toast.err").count() === 0,
  [...others, ...await page.locator(".toast.err").allTextContents()].join("; "));

// Lean whose editor did not load (a dropped connection): the cell says so, and Lean loads again on request
await page.close();   // one Lean at a time: each holds over a gigabyte
{
  const retry = await browser.newPage({ viewport: { width: 1400, height: 950 } });
  let dropped = 0;
  await retry.route("**/lean/lean-editor.js*", (r) => (dropped++ ? r.continue() : r.abort("connectionreset")));
  await retry.goto(`http://localhost:${port}/index.html#nbj=${Buffer.from(JSON.stringify(doc)).toString("base64url")}`);
  const note = retry.locator(".cell.lean .leanstate.failed").first();
  const said = await note.waitFor({ timeout: 60000 }).then(() => note.textContent(), () => "");
  check("Lean whose editor did not load says so, with a button to try again", /Lean did not start/.test(said) && await note.locator("button", { hasText: "Try again" }).count() === 1, said);
  await note.locator("button", { hasText: "Try again" }).click();
  const back = await retry.waitForFunction(() => [...document.querySelectorAll(".leanmsg .text")].some((e) => e.textContent.trim() === "42"), null, { timeout: 180000 }).then(() => true, () => false);
  check("and it starts on the second try", back && dropped === 2, `${dropped} requests for the editor`);
  await retry.close();
}

// a course's lessons with their preludes imported from the course's compiled modules (lean/lean-courses.json,
// scripts/lean-courses.mjs), when the bundle has them: in a page of the real courses
const compiled = JSON.parse(readFileSync(path.join(dist, "lean/lean-courses.json"), "utf8"));
if (compiled.crdt && compiled.logic) {
  const course = await browser.newPage({ viewport: { width: 1400, height: 950 } });
  const errors = [];
  course.on("pageerror", (e) => errors.push(e.message));
  const servers = [], ended = [];
  course.on("worker", (w) => { if (/lean-server\.worker/.test(w.url())) { servers.push(w.url()); w.on("close", () => ended.push(w.url())); } });
  const ready = () => course.waitForFunction(() => document.querySelector(".titlebar .leanpill")?.textContent === "Lean · ready", null, { timeout: 240000 }).then(() => true, () => false);
  /** Opens a course link, and waits for Lean to have checked the lesson. */
  const open = async (hash, where, first = false) => {
    const t = Date.now();
    if (first) await course.goto(`http://localhost:${port}/index.html${hash}`);
    else await course.evaluate((h) => { location.hash = h; }, hash);
    await course.locator(".lessonbar .lbwhere", { hasText: where }).first().waitFor({ timeout: 60000 });
    await course.waitForTimeout(1500);
    const ok = await ready();
    return { ok, secs: ((Date.now() - t) / 1000).toFixed(1) };
  };
  const a = await open("#course=crdt&lesson=10&app=1", "Application of lesson 10", true);
  const pack = (u) => decodeURIComponent(new URL(u).searchParams.get("packs") ?? "");
  const leanMessages = () => course.evaluate(() => [...document.querySelectorAll(".leanmsg.error .text")].map((e) => e.textContent));
  const unknown = (await leanMessages()).filter((m) => /unknown (identifier|constant|namespace)|unknown module/.test(m));
  check("CRDT 10a: Lean imports the lessons before it from the course's modules, and checks it", a.ok && pack(servers.at(-1) ?? "") === compiled.crdt.pack && unknown.length === 0,
    `${a.secs} s; packs ${pack(servers.at(-1) ?? "") || "none"}${unknown.length ? `; ${unknown[0]}` : ""}`);
  const workers = servers.length, gone = ended.length;
  const b = await open("#course=crdt&lesson=11", "Lesson 11 of 12");
  const c = await open("#course=crdt&lesson=12", "Lesson 12 of 12");
  check("the next lessons keep the server: the module it has, and the rest of their prelude inline", b.ok && c.ok && servers.length === workers && ended.length === gone,
    `${b.secs} s, ${c.secs} s; ${servers.length - workers} servers started`);
  const d = await open("#course=logic&lesson=4", "Lesson 4 of 9");
  check("another course starts Lean again, with that course's modules", d.ok && pack(servers.at(-1) ?? "") === compiled.logic.pack && ended.length > gone,
    `${d.secs} s; packs ${pack(servers.at(-1) ?? "") || "none"}`);
  check("and nothing went wrong on the page", errors.length === 0, errors.join("; "));
  await course.close();
} else console.log("(the bundle has no courses' modules: npm run bundle with LEAN_WASM_CLI_DIR)");
await browser.close();
server.close();
process.exit(checks.every(Boolean) ? 0 : 1);
