// Math cells, end to end in Chromium: the bundled notebook (npm run bundle) against the native engine
// over HTTP (cd engine && lake build). Each case is typed into a cell and run the way a reader runs it.
// Checked: the engine's answer is the expected one (its text form, as in engine/Tests/golden.tsv), the
// page shows exactly that answer (its LaTeX, as the engine sends it to a client of its own), a session
// carries `let` bindings from one cell to the next, an error shows as the cell's error, and opening a
// cell's work shows the step that produced the answer, under the notebook's name for its rule.
//   node scripts/e2e-math.mjs [screenshot.png]
// Chromium: playwright-core's own, or the executable named by CHROMIUM. The engine: MATHENGINE, or
// engine/.lake/build/bin/mathengine.
import { chromium } from "playwright-core";
import { createServer } from "node:http";
import { readFileSync, statSync } from "node:fs";
import assert from "node:assert/strict";
import path from "node:path";
import { startServer } from "../packages/engine-host/dist/server.js";
import { httpTransport } from "../packages/engine-host/dist/index.js";
import { createClient } from "../packages/protocol/dist/index.js";

/** What to type, the engine's answer as text (or its error), and a step the cell's work must show. */
const CASES = [
  { src: "diff(sin(x)*exp(x), x)", text: "cos(x)*exp(x) + exp(x)*sin(x)", step: "Product rule" },
  { src: "let f = x^2 + 3x", text: "x^2 + 3*x" },
  { src: "diff(f, x)", text: "2*x + 3", step: "Sum rule" },
  { src: "[1,2;3,4] * [5,6;7,8]", text: "[19, 22; 43, 50]", step: "Matrix product" },
  { src: "[1, 2] ./ [3, 10]", text: "[1/3, 1/5]", step: "Entrywise division" },
  { src: "rref([1,2;2,4])", text: "[1, 2; 0, 0]", step: "Add a multiple of a row" },
  { src: "[1,2] * [1,2]", error: "inner dimensions must match" },
];

const root = path.resolve(import.meta.dirname, "..");
const dist = path.join(root, "apps/notebook/dist");
const exe = process.env.MATHENGINE ?? path.join(root, "engine/.lake/build/bin/mathengine");
const shot = process.argv[2];
const types = { ".html": "text/html", ".js": "text/javascript", ".css": "text/css", ".wasm": "application/wasm", ".json": "application/json", ".svg": "image/svg+xml", ".chalk": "application/json" };
const site = createServer((req, res) => {
  const file = path.join(dist, decodeURIComponent(new URL(req.url, "http://x").pathname).replace(/\/$/, "/index.html"));
  try { if (!statSync(file).isFile()) throw 0; } catch { res.writeHead(404); res.end(); return; }
  res.writeHead(200, { "content-type": types[path.extname(file)] ?? "application/octet-stream" });
  res.end(readFileSync(file));
}).listen(0);
const engine = startServer(0, exe);
await new Promise((r) => engine.once("listening", r));
const base = `http://localhost:${site.address().port}`;
const engineUrl = `http://localhost:${engine.address().port}`;

// the same sources in a session of the test's own: what the engine answers, to hold the page to
const reference = createClient(httpTransport(engineUrl));
/** LaTeX as compared: no path annotations, braces or spaces (KaTeX's annotation keeps neither exactly). */
const flat = (tex) => tex.replace(/\\htmlData\{[^}]*\}/g, "").replace(/[{}\s]/g, "");

const browser = await chromium.launch({ ...(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {}), args: ["--no-sandbox"] });
const page = await browser.newPage({ viewport: { width: 1180, height: 1400 } });
// errors before the engine is switched to HTTP are the wasm worker missing from a bundle without it
const pageErrors = [];
let connected = false;
page.on("pageerror", (e) => { if (connected) pageErrors.push(e.message); });

const cells = () => page.locator(".cell:not(.markdown):not(.section)");
async function run(i, src) {
  const input = cells().nth(i).locator("input.cellin");
  await input.click(); await input.fill(src); await input.press("Enter");
}
/** A cell's output (the engine's LaTeX, as KaTeX keeps it) or error, once it has finished. */
async function out(i) {
  await page.waitForFunction((k) => {
    const c = document.querySelectorAll(".cell:not(.markdown):not(.section)")[k];
    return c && !c.classList.contains("running") && (c.querySelector(".outval") || c.querySelector(".cellerr"));
  }, i, { timeout: 30000 });
  return page.evaluate((k) => {
    const c = document.querySelectorAll(".cell:not(.markdown):not(.section)")[k];
    return { tex: c.querySelector(".outval .katex-mathml annotation")?.textContent ?? null, err: c.querySelector(".cellerr")?.textContent ?? null };
  }, i);
}
/** Open a cell's work and read the names of its steps, nested ones included. */
async function work(i) {
  const cell = cells().nth(i);
  await cell.locator(".cellacts [aria-expanded]").click();
  await cell.locator(".work:not(.pending) .step").first().waitFor({ timeout: 30000 });
  return cell.locator(".work .step .rule").allTextContents();
}

let failed = false;
try {
  // the notebook, on the engine over HTTP (?dev shows the switch)
  await page.goto(`${base}/?dev`);
  await page.locator(".kernel select").selectOption("http");
  await page.locator("#kurl").fill(engineUrl);
  await page.locator("#kurl").dispatchEvent("change");
  await page.waitForFunction(() => /ready/.test(document.querySelector(".kernel")?.textContent ?? ""), null, { timeout: 30000 });
  connected = true;
  await page.locator(".menus span", { hasText: "File" }).click();
  await page.locator(".dropdown .item", { hasText: "New notebook" }).click();

  for (const [i, c] of CASES.entries()) {
    const want = await reference.call("engine.evaluate", { sessionId: "e2e-reference", cellId: `r${i}`, source: c.src, paths: true });
    await run(i, c.src);
    const got = await out(i);
    if (c.error) {
      assert.equal(want.ok, false, `${c.src}: the engine answered instead of failing`);
      assert.match(want.error.message, new RegExp(c.error), `${c.src}: the engine's error`);
      assert.ok(got.err?.includes(want.error.message), `${c.src}: the page shows ${JSON.stringify(got)}, not the error ${want.error.message}`);
      console.log(`✓ ${c.src}  ✗ ${want.error.message}`);
      continue;
    }
    assert.equal(want.ok, true, `${c.src}: ${want.error?.message}`);
    assert.equal(want.rendered.text, c.text, `${c.src}: the engine's answer`);
    assert.equal(got.err, null, `${c.src}: the page shows an error`);
    assert.equal(flat(got.tex ?? ""), flat(want.rendered.latex), `${c.src}: the page shows something other than the engine's answer`);
    if (c.step) {
      const steps = await work(i);
      assert.ok(steps.some((s) => s.includes(c.step)), `${c.src}: no "${c.step}" step in ${JSON.stringify(steps)}`);
    }
    console.log(`✓ ${c.src}  = ${c.text}${c.step ? `   (${c.step})` : ""}`);
  }
  assert.deepEqual(pageErrors, [], "errors on the page");
  console.log(`\n${CASES.length} cells, end to end`);
} catch (e) {
  failed = true;
  console.error(e);
} finally {
  if (shot) await page.screenshot({ path: shot, fullPage: true });
  reference.close?.();
  await browser.close();
  engine.close();
  site.close();
}
process.exit(failed ? 1 : 0);
