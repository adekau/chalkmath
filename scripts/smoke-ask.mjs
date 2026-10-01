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
import { createHash } from "node:crypto";

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
// a stand-in for Ollama on this computer: its /api/chat, answering by the schema in `format`, with the
// CORS headers Ollama sends when OLLAMA_ORIGINS allows the page
const ollamaCalls = [];
const ollama = createServer((req, res) => {
  const cors = { "access-control-allow-origin": req.headers.origin ?? "*", "access-control-allow-headers": "content-type", "access-control-allow-methods": "GET, POST" };
  if (req.method === "OPTIONS") { res.writeHead(204, cors); res.end(); return; }
  if (req.url === "/api/tags") { res.writeHead(200, { ...cors, "content-type": "application/json" }); res.end(JSON.stringify({ models: [{ name: "gemma4:e2b" }] })); return; }
  let body = "";
  req.on("data", (c) => (body += c));
  req.on("end", () => {
    const b = JSON.parse(body);
    ollamaCalls.push({ model: b.model, think: b.think, required: b.format.required });
    const r = b.format.required;
    const reply = r.includes("volume") ? { volume: 24, lookup: false }
      : r.includes("searches") ? { lookup: true, shape: "formula", subject: "mathematics", known: true, searches: ["cube volume"], columns: ["volume"], rows: "", keywords: [] }
      : r.includes("expr") ? { found: true, expr: "s^3", params: ["s"], vars: [{ name: "s", meaning: "side length" }], quote: "V = s^3" } : {};
    res.writeHead(200, { ...cors, "content-type": "application/json" });
    res.end(JSON.stringify({ model: b.model, message: { role: "assistant", content: JSON.stringify(reply) }, done: true }));
  });
}).listen(0);
const ollamaUrl = `http://localhost:${ollama.address().port}`;

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
    // like Chrome: every session created with a monitor reports a "download" at 100%, model or no
    create: async (o) => {
      if (o?.monitor) { const t = new EventTarget(); o.monitor(t); t.dispatchEvent(Object.assign(new Event("downloadprogress"), { loaded: 1 })); }
      return {
        prompt: async (user, p) => {
          window.__lm.push(p.responseConstraint.required[0]);
          // choosing a table takes a moment, as it does for a real model: long enough to read the progress
          if (p.responseConstraint.required.includes("table")) await new Promise((r) => setTimeout(r, 1600));
          return JSON.stringify(reply(user, p.responseConstraint));
        },
        destroy() {},
      };
    },
  };
});

// a stand-in for openrouter.ai: its sign-in page sends the reader back with a code, the code (and the
// PKCE verifier) buy a key, and chat completions answer by the schema, with web search's citations
const orCalls = [];
let orChallenge = "";
await page.context().route("https://openrouter.ai/**", async (route) => {
  const req = route.request(), u = new URL(req.url());
  const cors = { "access-control-allow-origin": "*", "access-control-allow-headers": "authorization, content-type, http-referer, x-title", "access-control-allow-methods": "GET, POST" };
  if (req.method() === "OPTIONS") return route.fulfill({ status: 204, headers: cors });
  if (u.pathname === "/auth") {
    orChallenge = u.searchParams.get("code_challenge");
    assert.equal(u.searchParams.get("code_challenge_method"), "S256");
    return route.fulfill({ status: 302, headers: { location: `${u.searchParams.get("callback_url")}?code=or-code` } });
  }
  const json = (body) => route.fulfill({ headers: { ...cors, "content-type": "application/json" }, body: JSON.stringify(body) });
  if (u.pathname === "/api/v1/auth/keys") {
    const b = req.postDataJSON();
    const ok = b.code === "or-code" && createHash("sha256").update(b.code_verifier).digest("base64url") === orChallenge;
    return ok ? json({ key: "sk-or-v1-test1234", user_id: "u" }) : route.fulfill({ status: 403, headers: cors, body: "{}" });
  }
  if (u.pathname === "/api/v1/models") return json({ data: [{ id: "anthropic/claude-haiku-4.5", name: "Claude Haiku 4.5", supported_parameters: ["structured_outputs"], pricing: { prompt: "0.000001" } }] });
  if (u.pathname === "/api/v1/chat/completions") {
    const b = req.postDataJSON();
    orCalls.push({ auth: req.headers()["authorization"], model: b.model, web: !!b.plugins?.some((p) => p.id === "web"), schema: !!b.response_format });
    const r = b.response_format.json_schema.schema.required;
    const content = r.includes("searches") ? { lookup: true, shape: "number", subject: "the world", known: false, searches: ["Tigers World Series titles"], columns: ["titles"], rows: "", keywords: [] }
      : r.includes("sources") ? { found: true, rows: [[4]], columns: ["World Series titles"], rowLabels: [], formula: { latex: "", expr: "", params: [], vars: [] },
        sources: [{ title: "Detroit Tigers", url: "https://en.wikipedia.org/wiki/Detroit_Tigers", quote: "The Tigers have won four World Series titles" }] } : {};
    return json({ choices: [{ message: { role: "assistant", content: JSON.stringify(content),
      annotations: b.plugins ? [{ type: "url_citation", url_citation: { url: "https://www.mlb.com/tigers/history", title: "Tigers history", content: "World Series titles: 1935, 1945, 1968, 1984 (4)" } }] : [] } }] });
  }
  return route.fulfill({ status: 404, headers: cors, body: "" });
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
  // the progress: the steps done, ticked, then the one under way with its seconds; never a download
  await page.waitForFunction(() => /Choosing among/.test(document.querySelector(".askprog .now")?.textContent ?? ""), null, { timeout: 20000 });
  await page.waitForFunction(() => /\d s/.test(document.querySelector(".askprog .now .secs")?.textContent ?? ""), null, { timeout: 5000 });
  const progress = await cells().nth(4).locator(".askprog").innerText();
  assert.match(progress, /✓ Planning the search\n✓ Searching Wikipedia for “MLB runs per game by season”\n✓ Reading 1 page\nChoosing among 1 table… \d s/);
  assert.doesNotMatch(progress, /download|100%/i);
  if (shot) await cells().nth(4).screenshot({ path: shot.replace(/\.png$/, "-progress.png") });
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

  // Ollama: chosen in the settings, tested there, then answering a lookup
  await menu("Run", "Lookup settings");
  const dialog = page.locator(".modal");
  await dialog.locator("select").first().selectOption("ollama");
  await dialog.getByLabel("Ollama address").fill(ollamaUrl);
  await dialog.getByLabel("Ollama model").fill("gemma4:e2b");
  await dialog.locator("button", { hasText: "Test the model" }).click();
  await page.waitForFunction(() => /answered in/.test(document.querySelector(".modal")?.textContent ?? ""), null, { timeout: 20000 });
  assert.match(await dialog.innerText(), /gemma4:e2b \(Ollama\): answered in \d+\.\d s, correctly/);
  if (shot) await dialog.locator(".modalcard").screenshot({ path: shot.replace(/\.png$/, "-ollama.png") });
  await page.keyboard.press("Escape");
  // the cell left holding `x+` above, emptied
  await cells().nth(8).locator(".mi").click();
  await page.keyboard.press("Control+A"); await page.keyboard.press("Backspace");
  await page.keyboard.type("?volume of a cube");
  await page.keyboard.press("Enter");
  r = await out(8);
  assert.equal(r.tex, "s^3");
  assert.match(r.info, /gemma4:e2b \(Ollama\)/);
  assert.ok(ollamaCalls.length >= 3 && ollamaCalls.every((c) => c.model === "gemma4:e2b" && c.think === false), JSON.stringify(ollamaCalls));

  // OpenRouter: signing in through its window, then a lookup the model answers from its own web search
  await menu("Run", "Lookup settings");
  await dialog.locator("select").first().selectOption("openrouter");
  const [popup] = await Promise.all([page.waitForEvent("popup"), dialog.locator("button", { hasText: "Sign in with OpenRouter" }).click()]);
  await popup.waitForEvent("close", { timeout: 20000 });
  await page.waitForFunction(() => /Signed in \(key …1234\)/.test(document.querySelector(".modal")?.textContent ?? ""), null, { timeout: 10000 });
  await dialog.getByLabel("OpenRouter model").fill("anthropic/claude-haiku-4.5");
  if (shot) await dialog.locator(".modalcard").screenshot({ path: shot.replace(/\.png$/, "-openrouter.png") });
  await page.keyboard.press("Escape");
  await cells().nth(9).locator(".mi").click();
  await page.keyboard.type("?how many world series have the tigers won");
  await page.keyboard.press("Enter");
  r = await out(9);
  assert.equal(r.tex, "4");
  assert.match(r.info, /FOUND BY THE MODEL'S WEB SEARCH/i);
  assert.match(r.info, /Tigers history/);
  assert.match(r.info, /claude-haiku-4\.5 \(OpenRouter\)/);
  assert.equal(orCalls.length, 2, JSON.stringify(orCalls));
  assert.ok(orCalls.every((c) => c.auth === "Bearer sk-or-v1-test1234" && c.model === "anthropic/claude-haiku-4.5" && c.schema), JSON.stringify(orCalls));
  assert.deepEqual(orCalls.map((c) => c.web), [false, true], "only the answer searches the web");
  console.log("smoke-ask: ok");
} finally {
  await browser.close();
  site.close(); engine.close(); ollama.close();
}
