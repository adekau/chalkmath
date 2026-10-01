// `?` lookups, end to end in Chromium: the bundled notebook (npm run bundle) against the native engine
// over HTTP (cd engine && lake build). The model is a stand-in for Chrome's Prompt API
// (window.LanguageModel) that answers each step by its schema, and Wikipedia is intercepted with
// synthetic pages (their numbers follow a formula; they are not real statistics). Checked: a formula
// the model knows is answered with nothing sent anywhere and no question asked; `let V = ?…` defines
// V(B, h); a list is a row; a data question asks before searching, then copies a table into a
// matrix; "Check with a search" finds the formula on a page; and after a reload the saved answers
// are evaluated again without the model or the network.
//   node scripts/smoke-ask.mjs [screenshot.png]
// Chromium: playwright-core's own, or the executable named by CHROMIUM.
import { chromium } from "playwright-core";
import { createServer } from "node:http";
import { readFileSync, statSync } from "node:fs";
import assert from "node:assert/strict";
import path from "node:path";
import { startServer } from "../packages/engine-host/dist/server.js";

const root = path.resolve(import.meta.dirname, "..");
const dist = path.join(root, "apps/notebook/dist");
const shot = process.argv[2];
const types = { ".html": "text/html", ".js": "text/javascript", ".css": "text/css", ".wasm": "application/wasm", ".json": "application/json", ".svg": "image/svg+xml", ".chalk": "application/json" };
const site = createServer((req, res) => {
  const file = path.join(dist, decodeURIComponent(new URL(req.url, "http://x").pathname).replace(/\/$/, "/index.html"));
  try { if (!statSync(file).isFile()) throw 0; } catch { res.writeHead(404); res.end(); return; }
  res.writeHead(200, { "content-type": types[path.extname(file)] ?? "application/octet-stream" });
  res.end(readFileSync(file));
}).listen(0);
const engine = startServer(0, path.join(root, "engine/.lake/build/bin/mathengine"));
await new Promise((r) => engine.once("listening", r));
const base = `http://localhost:${site.address().port}`;
const engineUrl = `http://localhost:${engine.address().port}`;

const rg = (y) => (4 + ((y * 7) % 100) / 100).toFixed(2);
const hr = (y) => (0.8 + ((y * 3) % 60) / 100).toFixed(2);
const YEARS = Array.from({ length: 2025 - 1901 + 1 }, (_, i) => 1901 + i);
const seasons = `<h2>League batting by season</h2><table class="wikitable"><thead><tr><th>Year</th><th>Teams</th><th>R/G</th><th>HR/G</th></tr></thead><tbody>
${YEARS.map((y) => `<tr><td>${y}</td><td>${y < 1961 ? 16 : 30}</td><td>${rg(y)}</td><td>${hr(y)}</td></tr>`).join("")}</tbody></table>`;
const prism = `<p>The volume of a prism is <span class="mwe-math-element"><span style="display: none;"><math alttext="{\\displaystyle V=Bh}"><mi>V</mi></math></span><img class="mwe-math-fallback-image-inline" alt="{\\displaystyle V=Bh}"></span>, where <i>B</i> is the area of the base and <i>h</i> the height.</p>`;

const browser = await chromium.launch({ ...(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {}), args: ["--no-sandbox"] });
const page = await browser.newPage({ viewport: { width: 1180, height: 1400 } });
const offsite = [];
page.on("request", (r) => { const u = new URL(r.url()); if (u.hostname !== "localhost") offsite.push(`${u.host}${u.pathname}`); });
page.on("pageerror", (e) => { throw e; });
const cors = { "access-control-allow-origin": "*", "access-control-allow-headers": "api-user-agent", "access-control-allow-methods": "GET" };
await page.route("https://en.wikipedia.org/**", async (route) => {
  const u = route.request().url();
  if (route.request().method() === "OPTIONS") return route.fulfill({ status: 204, headers: cors });
  if (u.includes("list=search")) {
    const title = /prism/i.test(new URL(u).searchParams.get("srsearch")) ? "Prism (geometry)" : "Batting by season";
    return route.fulfill({ headers: { ...cors, "content-type": "application/json" }, body: JSON.stringify({ query: { search: [{ title, snippet: "" }] } }) });
  }
  if (u.includes("Batting_by_season")) return route.fulfill({ headers: { ...cors, "content-type": "text/html" }, body: seasons });
  if (u.includes("Prism_(geometry)")) return route.fulfill({ headers: { ...cors, "content-type": "text/html" }, body: prism });
  return route.fulfill({ status: 404, headers: cors, body: "" });
});
await page.addInitScript(() => {
  window.__lm = [];
  const reply = (user, schema) => {
    const q = /Question: (.*)/.exec(user)?.[1] ?? "";
    if (schema.required.includes("searches")) {
      return /prism/i.test(q) ? { shape: "formula", subject: "mathematics", known: true, searches: ["prism volume"], columns: ["volume"], rows: "", keywords: ["prism", "volume", "base", "height"] }
        : /primes/i.test(q) ? { shape: "list", subject: "mathematics", known: true, searches: ["prime numbers"], columns: ["prime"], rows: "", keywords: [] }
        : { shape: "table", subject: "the world", known: false, searches: ["MLB runs per game by season"], columns: ["season", "runs per game", "home runs per game"], rows: "one MLB season, 2006 to 2025", keywords: ["year", "R/G", "HR/G"] };
    }
    if (schema.required.includes("expr")) return { found: true, expr: "B*h", params: ["B", "h"], vars: [{ name: "B", meaning: "area of the base" }, { name: "h", meaning: "height" }], quote: /Passages/.test(user) ? "V=Bh" : "V = Bh" };
    if (schema.required.includes("table")) return { table: 0, columns: [0, 2, 3], label: -1, filter: { column: 0, min: 2006, max: 2025 } };
    if (/primes/i.test(q)) return { rows: [2, 3, 5, 7, 11, 13, 17, 19, 23, 29].map((p) => ({ label: "", values: [p] })) };
    return { rows: [] };
  };
  window.LanguageModel = {
    availability: async () => "available",
    create: async () => ({
      prompt: async (user, p) => { window.__lm.push(p.responseConstraint.required[0]); return JSON.stringify(reply(user, p.responseConstraint)); },
      destroy() {},
    }),
  };
});

/** The notebook, on the engine over HTTP (?dev shows the switch). */
async function open() {
  await page.goto(`${base}/?dev`);
  await page.locator(".kernel select").selectOption("http");
  await page.locator("#kurl").fill(engineUrl);
  await page.locator("#kurl").dispatchEvent("change");
  await page.waitForFunction(() => /ready/.test(document.querySelector(".kernel")?.textContent ?? ""), null, { timeout: 20000 });
}
const menu = async (m, item) => { await page.locator(".menus span", { hasText: m }).click(); await page.locator(".dropdown .item", { hasText: item }).click(); };
const cells = () => page.locator(".cell:not(.markdown):not(.section)");
async function run(i, src) {
  const input = cells().nth(i).locator("input.cellin");
  await input.click(); await input.fill(src); await input.press("Enter");
}
/** A cell's output (the engine's LaTeX), error and lookup caption, once it has finished. */
async function out(i) {
  await page.waitForFunction((k) => {
    const c = document.querySelectorAll(".cell:not(.markdown):not(.section)")[k];
    return c && !c.classList.contains("running") && (c.querySelector(".outval") || c.querySelector(".cellerr"));
  }, i, { timeout: 20000 });
  return page.evaluate((k) => {
    const c = document.querySelectorAll(".cell:not(.markdown):not(.section)")[k];
    const tex = c.querySelector(".outval .katex-mathml annotation")?.textContent ?? null;
    return { tex: tex && tex.replace(/\\htmlData\{[^}]*\}/g, "").replace(/[{}\s]/g, ""), err: c.querySelector(".cellerr")?.textContent ?? null, info: c.querySelector(".askinfo")?.innerText ?? "" };
  }, i);
}

try {
  await open();
  await menu("File", "New notebook");

  // a formula the model knows: answered with nothing sent anywhere, and nothing asked
  await run(0, "?what is the formula for volume of a prism?");
  let r = await out(0);
  assert.equal(r.tex, "B\\cdoth");
  assert.match(r.info, /FROM THE MODEL'S KNOWLEDGE/i);
  assert.deepEqual(offsite, []);
  assert.equal(await page.locator(".modal").count(), 0);

  // bound, it is a function of its variables
  await run(1, "let V = ?volume of a prism");
  await out(1);
  await run(2, "V(3, 4.5)");
  assert.equal((await out(2)).tex, "13.5");

  // a list is a row
  await run(3, "?the first ten primes");
  assert.equal((await out(3)).tex, "\\beginbmatrix2&3&5&7&11&13&17&19&23&29\\endbmatrix");

  // data: asked before searching; the table's values copied into a matrix
  await run(4, "let mlb = ?average runs and home runs per game in the MLB for the last 20 years");
  await page.waitForSelector(".modal", { timeout: 20000 });
  assert.match(await page.locator(".modal").innerText(), /search terms the model writes/);
  await page.locator(".modal button.primary", { hasText: "Search" }).click();
  r = await out(4);
  const want = Array.from({ length: 20 }, (_, i) => 2006 + i).map((y) => `${y}&${Number(rg(y))}&${Number(hr(y))}`).join("\\\\");
  assert.equal(r.tex, `\\beginbmatrix${want}\\endbmatrix`);
  assert.match(r.info, /COPIED FROM A TABLE/i);
  assert.match(r.info, /Columns:?\s*Year · R\/G · HR\/G/);
  assert.deepEqual(offsite, ["en.wikipedia.org/w/api.php", "en.wikipedia.org/api/rest_v1/page/html/Batting_by_season"]);

  // "Check with a search": the formula found on a page
  await cells().nth(0).hover();
  await cells().nth(0).locator(".cellacts span", { hasText: "Check with a search" }).click();
  await page.waitForFunction(() => /FORMULA THE SOURCE STATES/i.test(document.querySelector(".askinfo")?.textContent ?? ""), null, { timeout: 20000 });
  r = await out(0);
  assert.equal(r.tex, "B\\cdoth");
  assert.match(r.info, /Prism \(geometry\)/);
  if (shot) { await cells().nth(4).locator(".asktrail summary").click(); await page.mouse.move(0, 0); await page.screenshot({ path: shot, fullPage: true }); }

  // reloaded: the saved answers are evaluated again, without the model or the network
  await page.waitForTimeout(1500);   // the autosave is debounced
  const before = offsite.length;
  await open();
  await menu("Run", "Run all");
  r = await out(4);
  assert.match(r.tex ?? "", /^\\beginbmatrix2006&/);
  assert.equal((await page.evaluate(() => window.__lm)).length, 0);
  assert.equal(offsite.length, before);
  await run(5, "V(2, 10)");
  assert.equal((await out(5)).tex, "20");

  // typeset input: `?` at the start of a cell (or after `let name =`) makes it a question, as text
  await menu("View", "Math input: typeset");
  const typeIn = async (i, keys) => {
    await cells().nth(i).locator(".mi").click();
    await page.keyboard.type(keys);
  };
  await typeIn(6, "?the first ten primes");
  const q = cells().nth(6);
  assert.equal(await q.locator(".mi").count(), 0);
  assert.equal(await q.locator("input.cellin").inputValue(), "?the first ten primes");
  assert.equal(await q.locator(".hl .hq").textContent(), "?");
  await page.keyboard.press("Enter");
  assert.equal((await out(6)).tex, "\\beginbmatrix2&3&5&7&11&13&17&19&23&29\\endbmatrix");
  await typeIn(7, "let P ?the first ten primes");
  assert.equal(await cells().nth(7).locator("input.cellin").inputValue(), "let P = ?the first ten primes");
  await page.keyboard.press("Enter");
  await out(7);
  // anywhere else, `?` is refused with a word rather than dropped
  await typeIn(8, "x+?");
  assert.match(await page.locator(".toasts .toast.err").last().innerText(), /starts a question/);
  if (shot) { await cells().nth(6).scrollIntoViewIfNeeded(); await page.screenshot({ path: shot.replace(/\.png$/, "-typeset.png") }); }
  console.log("smoke-ask: ok");
} finally {
  await browser.close();
  site.close(); engine.close();
}
