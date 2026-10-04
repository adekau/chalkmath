// Screenshot a course lesson in Chromium against the native engine (a working aid, not a test):
//   node scripts/shot-lesson.mjs <course-id> <lesson-index> <out-dir> [manipulate-frame-fractions...]
import { chromium } from "playwright-core";
import { createServer } from "node:http";
import { readFileSync, statSync, mkdirSync } from "node:fs";
import path from "node:path";
import { startServer } from "../packages/engine-host/dist/server.js";
const root = path.resolve(path.dirname(new URL(import.meta.url).pathname), "..");
const [courseId, idx, out] = process.argv.slice(2);
mkdirSync(out, { recursive: true });
const dist = path.join(root, "apps/notebook/dist");
const types = { ".html": "text/html", ".js": "text/javascript", ".css": "text/css", ".json": "application/json", ".chalk": "application/json", ".woff2": "font/woff2", ".svg": "image/svg+xml", ".wasm": "application/wasm" };
const site = createServer((req, res) => {
  const file = path.join(dist, decodeURIComponent(new URL(req.url, "http://x").pathname).replace(/\/$/, "/index.html"));
  try { statSync(file); res.writeHead(200, { "content-type": types[path.extname(file)] ?? "application/octet-stream" }); res.end(readFileSync(file)); }
  catch { res.writeHead(404); res.end(); }
}).listen(0);
await new Promise((r) => site.once("listening", r));
const engine = startServer(0, process.env.MATHENGINE ?? path.join(root, "engine/.lake/build/bin/mathengine"));
await new Promise((r) => engine.once("listening", r));
const browser = await chromium.launch({ ...(process.env.CHROMIUM ? { executablePath: process.env.CHROMIUM } : {}), args: ["--no-sandbox"] });
const page = await browser.newPage({ viewport: { width: 1180, height: 1000 } });
page.on("pageerror", (e) => console.log("pageerror:", e.message));
try {
  await page.goto(`http://localhost:${site.address().port}/?dev`);
  await page.locator(".kernel select").selectOption("http");
  await page.locator("#kurl").fill(`http://localhost:${engine.address().port}`);
  await page.locator("#kurl").dispatchEvent("change");
  await page.waitForTimeout(500);
  await page.locator(".menus span", { hasText: "File" }).click();
  await page.locator(".dropdown .item", { hasText: "Courses and examples" }).click();
  const manifest = JSON.parse(readFileSync(path.join(root, "notebooks/courses.json"), "utf8"));
  const course = manifest.projects.find((p) => p.id === courseId);
  await page.locator(".crscard", { has: page.locator(".crstitle", { hasText: course.title }) }).click();
  await page.locator(".crslesson").nth(Number(idx)).locator(".crsgo").click();
  await page.locator(".lessonbar .lbwhere").waitFor({ timeout: 30000 });
  await page.waitForFunction(() => !document.querySelector(".cell.running"), null, { timeout: 120000 });
  await page.waitForTimeout(1500);
  await page.locator("button", { hasText: "Collapse" }).first().click().catch(() => {});
  await page.waitForTimeout(300);
  // the page scrolls inside its main pane: photograph it a screenful at a time
  const pane = await page.evaluateHandle(() => { const c = document.querySelector(".cells"); let e = c; while (e && e.scrollHeight <= e.clientHeight + 1) e = e.parentElement; return e ?? document.scrollingElement; });
  const total = await pane.evaluate((e) => e.scrollHeight);
  const step = await pane.evaluate((e) => e.clientHeight);
  let k = 0;
  for (let y = 0; y < total; y += step - 80, k++) {
    await pane.evaluate((e, y) => { e.scrollTop = y; }, y);
    await page.waitForTimeout(400);
    await page.screenshot({ path: path.join(out, `part${k}.png`) });
  }
  console.log("wrote", k, "screens to", out);
} finally { await browser.close(); engine.close(); site.close(); }
