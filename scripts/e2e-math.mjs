// Math cells, end to end in Chromium: the bundled notebook (npm run bundle) against the native engine
// over HTTP (cd engine && lake build). Each case is typed into a cell and run the way a reader runs it.
// Checked: the engine's answer is the expected one (its text form, as in engine/Tests/golden.tsv), the
// page shows exactly that answer (its LaTeX, as the engine sends it to a client of its own), a session
// carries `let` bindings from one cell to the next, an error shows as the cell's error, and opening a
// cell's work shows the step that produced the answer, under the notebook's name for its rule.
//   node scripts/e2e-math.mjs [screenshot.png]
// Then the notebook's teaching features, in a notebook of their own: a cell out of date when a name it
// read changes, a slider driving the cells below it, work stepped through with the answer held back,
// an exercise written in its editor and answered (wrong, right, and with the work), a Markdown
// callout, a function's usage on hover, a slider played down (h → 0) animating the plot below it with
// its axes held, and a course's lesson opened from the Courses tab, answered, and followed to the next. Each is held to the engine's own answers through a client of the test's.
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

const all = () => page.locator(".cell");
/** Wait until cell `i` (of every kind) shows `latex` as its output. */
async function outIs(i, latex, what) {
  await page.waitForFunction(([k, want]) => {
    const c = document.querySelectorAll(".cell")[k];
    const tex = c?.querySelector(".outval .katex-mathml annotation")?.textContent ?? "";
    const flat = (t) => t.replace(/\\htmlData\{[^}]*\}/g, "").replace(/[{}\s]/g, "");
    return !c?.classList.contains("running") && flat(tex) === want;
  }, [i, flat(latex)], { timeout: 30000 }).catch(async () => {
    const tex = await all().nth(i).locator(".outval .katex-mathml annotation").first().textContent().catch(() => null);
    assert.fail(`${what}: the cell shows ${JSON.stringify(tex)}, not ${JSON.stringify(latex)}`);
  });
}
/** A cell's ⋮ menu item. */
async function cellMenu(i, item) {
  await all().nth(i).hover();
  await all().nth(i).locator(".cellacts .more").click();
  await page.locator(".cellmenu .item", { hasText: item }).first().click();
}
const menu = async (m, item) => { await page.locator(".menus span", { hasText: m }).click(); await page.locator(".dropdown .item", { hasText: item }).first().click(); };
/** The engine's own answer, in a session of the test's that follows the notebook's. */
const ref = (source, k) => reference.call("engine.evaluate", { sessionId: "e2e-features", cellId: `f${k}`, source, paths: true });

/** An animated graph, in a notebook of its own: a slider set to play down, played, and the plot below
 *  it following every frame to the engine's last answer, with the axes it had when the play began. */
async function animatedGraph() {
  await menu("File", "New notebook");
  await run(0, "let h = 2"); await out(0);
  const line = "1 + (2 + h)*(x - 1)";
  await run(1, `plot([x^2, ${line}], x, -0.5, 3)`);
  await page.locator(".cell .plotbox svg").first().waitFor({ timeout: 30000 });
  const svg = all().nth(1).locator(".plotbox svg");
  const ticks = () => svg.locator("text.tl.r").allTextContents();
  const before = await ticks();
  await cellMenu(0, "Show as a slider");
  // the range: from 0.5 to 2 in steps of 0.5, played down (each change redraws the row)
  for (const [k, v] of [[0, "0.5"], [1, "2"], [2, "0.5"]]) {
    await all().nth(0).locator(".sliderrow .sliderbtn", { hasText: "range" }).click();
    const inp = all().nth(0).locator(".sliderrange input[type=number]").nth(k);
    await inp.fill(v); await inp.dispatchEvent("change");
  }
  await all().nth(0).locator(".sliderrow .sliderbtn", { hasText: "range" }).click();
  await all().nth(0).locator(".sliderrange select").selectOption("down");
  const play = all().nth(0).locator(".sliderrow .sliderplay");
  assert.equal((await play.textContent()).trim(), "▶ Play", "the slider has no ▶ Play");
  await play.click();
  await all().nth(0).locator(".sliderrow .sliderplay.on").waitFor({ timeout: 5000 });
  await page.waitForFunction(() => {
    const c = document.querySelectorAll(".cell")[0];
    return c.querySelector("input.cellin")?.value === "let h = 0.5" && !c.querySelector(".sliderplay.on");
  }, null, { timeout: 30000 });
  assert.equal(await all().nth(0).locator(".sliderrow .sliderval").textContent(), "0.5", "the slider shows where the play ended");
  await reference.call("engine.evaluate", { sessionId: "e2e-play", cellId: "h", source: "let h = 0.5" });
  const want = await reference.call("engine.plot", { sessionId: "e2e-play", cellId: "p", source: `plot([x^2, ${line}], x, -0.5, 3)` });
  const label = `Plot of ${want.series.map((s) => s.rendered.text).join(" and ")}`;
  await page.waitForFunction(([want]) => {
    const c = document.querySelectorAll(".cell")[1];
    return !c.classList.contains("running") && c.querySelector(".plotbox svg")?.getAttribute("aria-label")?.startsWith(want);
  }, [label], { timeout: 30000 }).catch(async () => {
    assert.fail(`the plot shows ${JSON.stringify(await svg.getAttribute("aria-label"))}, not the engine's ${JSON.stringify(label)}`);
  });
  assert.deepEqual(await ticks(), before, "the plot's axes moved while the slider played");
  // the plot's own run fits its window to its curves again
  await cellMenu(1, "Run this and below");
  await page.waitForFunction((b) => {
    const t = [...document.querySelectorAll(".cell")[1].querySelectorAll(".plotbox svg text.tl.r")].map((e) => e.textContent);
    return t.length && JSON.stringify(t) !== b;
  }, JSON.stringify(before), { timeout: 30000 });
  console.log("✓ animated graph: h played down from 2 to 0.5, the plot followed with its axes held, then refitted");
}

/** The teaching features, in a fresh notebook, then a course. */
async function features() {
  await menu("File", "New notebook");
  // out of date: a cell that read a name whose value has changed says so, and runs again
  await run(0, "let a = 2"); await out(0);
  await run(1, "diff(sin(a*x), x)");
  await ref("let a = 2", 0);
  await outIs(1, (await ref("diff(sin(a*x), x)", 1)).rendered.latex, "diff with a = 2");
  await run(0, "let a = 3");
  await page.locator(".cell.stale .stalebar code", { hasText: "a" }).first().waitFor({ timeout: 30000 });
  await all().nth(1).locator(".stalebtn", { hasText: "Run again" }).click();
  await ref("let a = 3", 2);
  await outIs(1, (await ref("diff(sin(a*x), x)", 3)).rendered.latex, "diff with a = 3, run again");
  assert.equal(await page.locator(".cell.stale").count(), 0, "a cell is still out of date after running again");
  console.log("✓ out of date: a changed, the cell said so, and ran again");
  // a slider: one step right rewrites the number and runs the cell below
  await cellMenu(0, "Show as a slider");
  await all().nth(0).locator(".sliderrow input[type=range]").focus();
  await page.keyboard.press("ArrowRight");
  await ref("let a = 4", 4);
  await outIs(1, (await ref("diff(sin(a*x), x)", 5)).rendered.latex, "diff after the slider moved to 4");
  assert.equal(await all().nth(0).locator("input.cellin").inputValue(), "let a = 4", "the slider rewrites its cell");
  console.log("✓ slider: a = 4, and the cell below followed");
  // step through: the work comes one step at a time, the answer last
  await cellMenu(1, "Step through the work");
  const c1 = all().nth(1);
  await c1.locator(".stepnext [data-next]").waitFor({ timeout: 30000 });
  assert.equal(await c1.locator(".work .step").count(), 0, "steps shown before the first was asked for");
  assert.equal(await c1.locator(".outheld").count(), 1, "the answer is not held back");
  await c1.locator(".stepnext [data-next]").click();
  assert.equal(await c1.locator(".work .step:not(.sub)").count(), 1, "one step after ▸ First step");
  await c1.locator(".stepnext .stepbtn", { hasText: "Show all" }).click();
  assert.equal(await c1.locator(".outheld").count(), 0, "the answer is still held after Show all");
  await outIs(1, (await ref("diff(sin(a*x), x)", 6)).rendered.latex, "the answer after every step");
  console.log("✓ step through: no steps, then one, then all with the answer");
  // an exercise: written in its editor, answered wrong, right, and with the work itself
  const question = "diff(x^2 * sin(x), x)";
  await menu("Edit", "Add exercise");
  const exI = await all().count() - 1;
  const ex = all().nth(exI);
  await ex.locator(".xc-edit textarea").first().fill("Differentiate $x^2 \\sin x$.");
  await ex.locator(".xc-qin").fill(question);
  await ex.locator(".xc-edit textarea").nth(1).fill("A product.\n\nThe product rule.");
  await ex.locator(".xc-qin").press("Enter");
  await ex.locator(".xc-q .katex").waitFor({ timeout: 30000 });
  const answer = async (a) => {
    await ex.locator(".xc-in").fill(a); await ex.locator(".xc-in").press("Enter");
    await page.waitForFunction(([k, a]) => {
      const c = document.querySelectorAll(".cell")[k];
      return !c.classList.contains("running") && c.querySelector(".xc-verdict:not(.old)") && c.querySelector(".xc-in")?.value === a;
    }, [exI, a], { timeout: 30000 });
    const engine = await reference.call("engine.check", { sessionId: "e2e-features", cellId: "q", source: question, answer: a });
    return { shown: await ex.locator(".xc-verdict").getAttribute("class"), text: await ex.locator(".xc-verdict").textContent(), engine };
  };
  let v = await answer("2x sin(x)");
  assert.equal(v.engine.equivalent, false, "the engine accepted a wrong answer");
  assert.match(v.shown, /wrong/, "the page did not mark the wrong answer");
  v = await answer("x(2 sin(x) + x cos(x))");
  assert.equal(v.engine.equivalent, true, "the engine refused a factored right answer");
  assert.match(v.shown, /right/, `the page did not mark the right answer: ${v.text}`);
  v = await answer(question);
  assert.match(v.shown, /wrong/, "the question itself was accepted as its answer");
  assert.ok(v.text.toLowerCase().includes(v.engine.answer.error.message.toLowerCase()), `the page shows ${JSON.stringify(v.text)}, not the engine's refusal`);
  await ex.locator(".xc-btn", { hasText: "Hint" }).click();
  assert.equal(await ex.locator(".xc-hint").count(), 1, "one hint opened");
  await ex.locator(".xc-btn", { hasText: "Show the solution" }).click();
  await ex.locator(".stepnext [data-next]").waitFor({ timeout: 30000 });
  await ex.locator(".stepnext .stepbtn", { hasText: "Show all" }).click();
  const solution = await reference.call("engine.check", { sessionId: "e2e-features", cellId: "q", source: question, paths: true });
  await outIs(exI, solution.rendered.latex, "the exercise's solution");
  console.log("✓ exercise: wrong, right in another form, the question refused, a hint, the solution stepped through");
  // a Markdown callout
  await menu("Edit", "Add Markdown cell");
  const md = all().nth(await all().count() - 1);
  await md.locator("textarea.mdin").fill("> [!theorem] Product rule\n> $(fg)' = f'g + fg'$");
  await md.locator("textarea.mdin").press("Shift+Enter");
  await md.locator("aside.callout.theorem .calltitle", { hasText: "Product rule" }).waitFor({ timeout: 10000 });
  console.log("✓ callout: a theorem with its title");
  // usage on hover: the name of a command in a cell, after a pause
  const last = await all().count() - 1;
  await all().nth(last).locator("input.cellin").fill("subst(x^2, x, 3)");
  await all().nth(last).locator("input.cellin").press("Enter");
  await outIs(last, (await ref("subst(x^2, x, 3)", 7)).rendered.latex, "subst");
  const name = all().nth(last).locator('.hl .hcmd, .mi [data-hl="hcmd"]').filter({ hasText: "subst" }).first();
  const box = await name.boundingBox();
  await page.mouse.move(box.x + box.width / 2, box.y + box.height / 2);
  await page.locator(".usagetip .umore", { hasText: "subst" }).waitFor({ timeout: 5000 });
  await page.mouse.move(5, 5);
  console.log("✓ usage on hover: subst");
  await animatedGraph();
  // a course: the Courses tab, a lesson opened, answered, and followed to the next
  const manifest = JSON.parse(readFileSync(path.join(root, "notebooks/courses.json"), "utf8"));
  const course = manifest.projects.find((p) => p.kind === "course");
  await menu("File", "Courses and examples");
  await page.locator(".crscard").first().waitFor({ timeout: 10000 });
  assert.equal(await page.locator(".crscard").count(), manifest.projects.length, "one card per project");
  await page.locator(".crscard", { has: page.locator(".crstitle", { hasText: course.title }) }).click();
  assert.equal(await page.locator(".crslesson").count(), course.lessons.length, "one row per lesson");
  await page.locator(".crslesson").first().locator(".crsgo").click();
  await page.locator(".lessonbar .lbwhere", { hasText: `Lesson 1 of ${course.lessons.length}` }).waitFor({ timeout: 30000 });
  const lesson = JSON.parse(readFileSync(path.join(root, "notebooks", course.path, course.lessons[0].file), "utf8"));
  assert.equal(await page.locator(".sidebar .olrow.section").count(), lesson.cells.filter((c) => c.type === "section").length, "the outline lists the lesson's sections");
  const first = lesson.cells.find((c) => c.type === "exercise");
  const lex = page.locator(".cell.exercise").first();
  await lex.locator(".xc-q .katex").waitFor({ timeout: 60000 });
  const expected = await reference.call("engine.check", { sessionId: "e2e-lesson", cellId: "l", source: first.src });
  await lex.locator(".xc-in").fill(expected.rendered.text); await lex.locator(".xc-in").press("Enter");
  await lex.locator(".xc-verdict.right").waitFor({ timeout: 30000 });
  const total = lesson.cells.filter((c) => c.type === "exercise").length;
  await page.locator(".lessonbar .lbstate", { hasText: `1 of ${total} exercises` }).waitFor({ timeout: 10000 });
  await page.locator(".lessonbar .lbbtn", { hasText: "Next" }).click();
  await page.locator(".lessonbar .lbwhere", { hasText: `Lesson 2 of ${course.lessons.length}` }).waitFor({ timeout: 30000 });
  await page.locator(".lessonbar .lbcourse").click();
  await page.locator(".crslesson").first().locator(".crsstate", { hasText: `1 of ${total} exercises` }).waitFor({ timeout: 10000 });
  console.log(`✓ course: ${course.title}, lesson 1 answered (1 of ${total}), lesson 2 opened, progress remembered`);
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
  console.log(`\n${CASES.length} cells, end to end\n`);
  await features();
  assert.deepEqual(pageErrors, [], "errors on the page");
  console.log("\nthe notebook's teaching features, end to end");
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
