import { test } from "node:test";
import assert from "node:assert/strict";
import { lookup, AskError, wikipedia, webSearch, preview, engineText } from "../dist/index.js";

// Synthetic data: the values follow a formula so the tests can say what each row must be. They are
// not real baseball statistics.
const rg = (y) => (4 + ((y * 7) % 100) / 100).toFixed(2);
const hr = (y) => (0.8 + ((y * 3) % 60) / 100).toFixed(2);
const YEARS = Array.from({ length: 2025 - 1901 + 1 }, (_, i) => 1901 + i);

const seasonsPage = `<h2>League batting by season</h2>
<table class="wikitable"><thead><tr><th>Year</th><th>Teams</th><th>R/G</th><th>HR/G</th><th>Notes</th></tr></thead><tbody>
${YEARS.map((y) => `<tr><td>${y}</td><td>${y < 1961 ? 16 : 30}</td><td>${y === 1994 ? "—" : rg(y)}</td><td>${hr(y)}</td><td>${y === 2020 ? "short season" : ""}</td></tr>`).join("\n")}
</tbody></table>
<h2>Awards</h2><table class="wikitable"><tr><th>Award</th><th>Winner</th></tr><tr><td>MVP</td><td>Someone</td></tr></table>
<table class="wikitable"><tr><th>Stadium</th><th>Capacity</th></tr><tr><td>A Park</td><td>40,000</td></tr><tr><td>B Field</td><td>38,500</td></tr></table>`;

const prosePage = `<p>The league's teams averaged 4.52 runs per game in 2019 and hit 1.39 home runs per game that year.</p>
<p>In 2020 the average fell to 4.65 runs per game with 1.28 home runs per game.</p>`;

/** A fetch that answers from a table of URL patterns, and records every URL asked for. */
function fakeFetch(routes) {
  const asked = [];
  const f = async (url) => {
    asked.push(url);
    for (const [re, body] of routes) {
      if (re.test(url)) {
        if (body instanceof Error) throw body;
        const text = typeof body === "string" ? body : JSON.stringify(body);
        return new Response(text, { status: 200, headers: { "content-type": typeof body === "string" ? "text/html" : "application/json" } });
      }
    }
    return new Response("not found", { status: 404 });
  };
  f.asked = asked;
  return f;
}

/** A model that answers each step (told apart by its schema) with a scripted reply. */
function scripted(replies) {
  const calls = [];
  return {
    id: "scripted",
    calls,
    async complete({ schema, user }) {
      const step = schema.required.includes("searches") ? "plan" : schema.required.includes("table") ? "pick" : schema.required.includes("expr") ? "formula"
        : schema.properties.rows.items.required.includes("quote") ? "extract" : "memory";
      calls.push({ step, user });
      const r = replies[step];
      if (r === undefined) throw new Error(`no reply scripted for ${step}`);
      return typeof r === "function" ? r(user) : JSON.stringify(r);
    },
  };
}

const PLAN = { shape: "table", known: false, searches: ["MLB runs per game by season"], columns: ["season", "runs per game", "home runs per game"], rows: "one MLB season, 2006 to 2025", keywords: ["year", "R/G", "HR/G", "runs", "home runs"] };
const wikiRoutes = (page) => [
  [/w\/api\.php.*list=search/, { query: { search: [{ title: "Batting by season", snippet: "<span>runs</span> per game" }] } }],
  [/rest_v1\/page\/html\/Batting_by_season/, page],
];
const opts = (model, fetch, extra = {}) => ({ model, fetch, sources: [wikipedia(fetch)], today: "2026-09-30", ...extra });

test("a table answers: the model picks columns and a year range, the values are copied from the page", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: PLAN, pick: { table: 0, columns: [0, 2, 3], label: -1, filter: { column: 0, min: 2006, max: 2025 } } });
  const progress = [];
  const r = await lookup("average runs and home runs per game in MLB for the last 20 years", { ...opts(model, fetch), onProgress: (l) => progress.push(l) });
  assert.equal(r.via, "table");
  const want = Array.from({ length: 20 }, (_, i) => 2006 + i).map((y) => `${y}, ${Number(rg(y))}, ${Number(hr(y))}`);
  assert.equal(r.source, `[${want.join("; ")}]`);
  assert.deepEqual(r.columns, ["Year", "R/G", "HR/G"]);
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.cites, [{ title: "Batting by season", url: "https://en.wikipedia.org/wiki/Batting_by_season" }]);
  assert.equal(r.rowsAre, "one MLB season, 2006 to 2025");
  assert.equal(r.model, "scripted");
  assert.deepEqual(progress, ["Planning the search", "Searching Wikipedia for “MLB runs per game by season”", "Reading 1 page", "Choosing among 2 tables"]);
  // the awards table has no numbers and is never shown; the batting table is shown first
  const pick = model.calls.find((c) => c.step === "pick").user;
  assert.match(pick, /Table 0, from "Batting by season", "League batting by season", 125 rows/);
  assert.match(pick, /columns: 0: Year; 1: Teams; 2: R\/G; 3: HR\/G; 4: Notes \[text\]/);
  assert.doesNotMatch(pick, /MVP/);
  assert.ok(pick.length < 2500, `the pick prompt is ${pick.length} characters`);
  assert.ok(r.trail.some((l) => /Chose the table “League batting by season” on “Batting by season”: columns Year, R\/G, HR\/G, rows with Year from 2006 to 2025/.test(l)), r.trail.join("\n"));
});

test("a row whose chosen cell is not a number is left out, and the result says so", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: PLAN, pick: { table: 0, columns: [0, 2], label: -1, filter: { column: 0, min: 1990, max: 1999 } } });
  const r = await lookup("runs per game in the 1990s", opts(model, fetch));
  assert.equal(r.source.split(";").length, 9);
  assert.doesNotMatch(r.source, /1994/);
  assert.deepEqual(r.notes, ["1 row was left out because a chosen cell was not a single number."]);
});

test("the model's indices are checked: text columns and out-of-range picks are dropped", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: PLAN, pick: { table: 0, columns: [0, 4, 99, 3], label: 7, filter: { column: 0, min: 2024, max: null } } });
  const r = await lookup("home runs lately", opts(model, fetch));
  assert.equal(r.source, `[2024, ${Number(hr(2024))}; 2025, ${Number(hr(2025))}]`);
  assert.deepEqual(r.columns, ["Year", "HR/G"]);
  assert.equal(r.rowLabels, undefined);
});

test("one value is a number, not a 1×1 matrix", () => {
  assert.equal(engineText([["42"]]), "42");
  assert.equal(engineText([["1", "-2"]]), "[1, -2]");
});

test("no table fits: numbers are lifted from prose, and each is checked against the quoted sentence", async () => {
  const fetch = fakeFetch(wikiRoutes(prosePage));
  const model = scripted({
    plan: PLAN,
    extract: { rows: [
      { label: "2019", values: [2019, 4.52, 1.39], quote: "The league's teams averaged 4.52 runs per game in 2019 and hit 1.39 home runs per game that year." },
      // 4.7 is not what the sentence says
      { label: "2020", values: [2020, 4.7, 1.28], quote: "In 2020 the average fell to 4.65 runs per game with 1.28 home runs per game." },
      // a quote the page does not contain confirms nothing
      { label: "2021", values: [2021, 4.53, 1.22], quote: "In 2021 teams scored 4.53 runs per game and 1.22 home runs per game." },
    ] },
  });
  const r = await lookup("runs and home runs per game, 2019 to 2021", opts(model, fetch));
  assert.equal(r.via, "text");
  assert.equal(r.source, "[2019, 4.52, 1.39; 2020, 4.7, 1.28; 2021, 4.53, 1.22]");
  assert.deepEqual(r.flagged, [[1, 1], [2, 0], [2, 1], [2, 2]]);
  assert.deepEqual(r.cites, [{ title: "Batting by season", url: "https://en.wikipedia.org/wiki/Batting_by_season" }]);
  assert.deepEqual(r.rowLabels, ["2019", "2020", "2021"]);
  assert.match(r.notes[0], /not found in the text/);
});

test("nothing found: the model's memory as a last resort, every value flagged; never when knowledge is off", async () => {
  const fetch = fakeFetch([[/w\/api\.php/, { query: { search: [] } }]]);
  const memory = { rows: [{ label: "2024", values: [2024, 4.39] }, { label: "bad", values: [1] }] };
  const model = scripted({ plan: PLAN, memory });
  const r = await lookup("runs per game in 2024", opts(model, fetch));
  assert.equal(r.via, "memory");
  assert.equal(r.source, "[2024, 4.39]");
  assert.deepEqual(r.flagged, [[0, 0], [0, 1]]);
  assert.deepEqual(r.cites, []);
  assert.match(r.notes[0], /not from a source/);
  await assert.rejects(lookup("runs per game in 2024", opts(scripted({ plan: PLAN, memory }), fetch, { useKnowledge: false })),
    (e) => e instanceof AskError && e.message === "The search found nothing." && e.trail.some((l) => /0 results/.test(l)));
});

test("web search results are read directly when the site allows it, else through the page reader", async () => {
  const fetch = fakeFetch([
    [/^https:\/\/searx\.example\/search\?format=json&q=MLB/, { results: [
      { title: "Open stats", url: "https://open.example/bat", content: "" },
      { title: "Closed stats", url: "https://closed.example/bat", content: "" },
      { title: "Not http", url: "ftp://x/y", content: "" }] }],
    [/^https:\/\/open\.example\/bat$/, "<p>nothing useful</p>"],
    [/^https:\/\/closed\.example\/bat$/, new TypeError("Failed to fetch")],
    [/^https:\/\/reader\.example\/\?url=https%3A%2F%2Fclosed\.example%2Fbat$/, seasonsPage],
  ]);
  const model = scripted({ plan: PLAN, pick: { table: 0, columns: [0, 2], label: -1, filter: { column: 0, min: 2025, max: 2025 } } });
  const r = await lookup("runs per game in 2025", { model, fetch, sources: [webSearch(fetch, "https://searx.example/")], reader: "https://reader.example/?url={url}", today: "2026-09-30", useKnowledge: false });
  assert.equal(r.source, `[2025, ${Number(rg(2025))}]`);
  assert.deepEqual(r.cites, [{ title: "Closed stats", url: "https://closed.example/bat" }]);
  assert.ok(!fetch.asked.some((u) => u.startsWith("ftp:")));
});

test("a source that fails is noted in the trail, and the others still answer", async () => {
  const good = wikiRoutes(seasonsPage);
  const fetch = fakeFetch([[/searx\.broken/, new TypeError("Failed to fetch")], ...good]);
  const model = scripted({ plan: PLAN, pick: { table: 0, columns: [0, 3], label: -1, filter: { column: 0, min: 2025, max: null } } });
  const r = await lookup("home runs per game in 2025", { model, fetch, sources: [webSearch(fetch, "https://searx.broken/search?q={q}&format=json"), wikipedia(fetch)], today: "2026-09-30", useKnowledge: false });
  assert.equal(r.via, "table");
  assert.ok(r.trail.some((l) => /Searching web search for .* failed: Failed to fetch/.test(l)));
});

test("a stop request ends the lookup", async () => {
  const ac = new AbortController();
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: () => { ac.abort(); return JSON.stringify(PLAN); } });
  await assert.rejects(lookup("x", { ...opts(model, fetch), signal: ac.signal }), (e) => e instanceof AskError && e.message === "Stopped.");
});

test("a model reply wrapped in prose or a code fence still reads", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: () => "Sure!\n```json\n" + JSON.stringify(PLAN) + "\n```", pick: () => "<think>hm</think>" + JSON.stringify({ table: 0, columns: [2], label: -1, filter: { column: 0, min: 2025, max: 2025 } }) });
  const r = await lookup("runs per game in 2025", opts(model, fetch));
  assert.equal(r.source, String(Number(rg(2025))));
});

test("a long table's preview shows its first and last rows", () => {
  const t = { caption: "", headers: ["n", "v"], rows: Array.from({ length: 50 }, (_, i) => [String(i), String(i * i)]) };
  const p = preview(t, 3, { title: "Squares", url: "", source: "", tables: [], text: "" });
  assert.equal(p, `Table 3, from "Squares", 50 rows\n  columns: 0: n; 1: v\n  | 0 | 0\n  | 1 | 1\n  | 2 | 4\n  … 44 more rows …\n  | 47 | 2209\n  | 48 | 2304\n  | 49 | 2401`);
});

// --- the model's own knowledge, and shapes other than a table ---------------------------------

const PRISM_PLAN = { shape: "formula", known: true, searches: ["prism volume"], columns: ["volume"], rows: "", keywords: ["prism", "volume", "base", "height"] };
const PRISM = { found: true, expr: "V = B*h", params: ["B", "h"], vars: [{ name: "B", meaning: "area of the base" }, { name: "h", meaning: "height" }, { name: "x", meaning: "not used" }], quote: "V = Bh" };

test("standard knowledge is answered by the model, and nothing is sent anywhere", async () => {
  const fetch = fakeFetch([]);
  let asked = 0;
  const model = scripted({ plan: PRISM_PLAN, formula: PRISM });
  const r = await lookup("what is the formula for the volume of a prism?", { ...opts(model, fetch), beforeSearch: async () => { asked++; return true; } });
  assert.equal(r.shape, "formula");
  assert.equal(r.via, "knowledge");
  assert.equal(r.source, "B*h");
  assert.deepEqual(r.params, ["B", "h"]);
  assert.deepEqual(r.vars, [{ name: "B", meaning: "area of the base" }, { name: "h", meaning: "height" }]);
  assert.equal(r.latex, "V = Bh");
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.cites, []);
  assert.deepEqual(r.notes, ["From the model's knowledge; no source was consulted."]);
  assert.deepEqual(fetch.asked, []);
  assert.equal(asked, 0);
  assert.deepEqual(model.calls.map((c) => c.step), ["plan", "formula"]);
});

test("a known number: one value, not a matrix", async () => {
  const fetch = fakeFetch([]);
  const model = scripted({ plan: { shape: "number", known: true, searches: ["speed of light"], columns: ["speed of light in m/s"], rows: "", keywords: [] },
    memory: { rows: [{ label: "c", values: [299792458] }] } });
  const r = await lookup("speed of light in m/s", opts(model, fetch));
  assert.equal(r.source, "299792458");
  assert.equal(r.via, "knowledge");
  assert.deepEqual(fetch.asked, []);
});

test("“Check with a search”: a formula the page states in LaTeX, matched to the model's translation", async () => {
  const page = `<h2>Volume</h2><p>The volume of a prism is <span class="mwe-math-element"><span style="display: none;"><math alttext="{\\displaystyle V=Bh}"><mi>V</mi></math></span><img class="mwe-math-fallback-image-inline" alt="{\\displaystyle V=Bh}"></span> where <i>B</i> is the base area and <i>h</i> the height.</p>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "Prism (geometry)" }] } }], [/rest_v1\/page\/html\/Prism_\(geometry\)/, page]]);
  const reply = (quote) => ({ ...PRISM, quote });
  const r = await lookup("volume of a prism", { ...opts(scriptedFormula(reply("V=Bh")), fetch), forceSearch: true });
  assert.equal(r.via, "text");
  assert.equal(r.source, "B*h");
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.cites, [{ title: "Prism (geometry)", url: "https://en.wikipedia.org/wiki/Prism_(geometry)" }]);
  assert.ok(r.trail.some((l) => l.includes("Took the formula $V=Bh$ from “Prism (geometry)”")), r.trail.join("\n"));
  // a quote the page does not have is flagged
  const bad = await lookup("volume of a prism", { ...opts(scriptedFormula(reply("V = \\frac{1}{3}Bh")), fetch), forceSearch: true });
  assert.deepEqual(bad.flagged, [[0, 0]]);
  assert.match(bad.notes[0], /could not be matched/);
});

/** A scripted model for the formula path: the plan, then the formula reply (for page or memory). */
function scriptedFormula(reply) {
  return {
    id: "scripted", calls: [],
    async complete({ schema }) { return JSON.stringify(schema.required.includes("searches") ? PRISM_PLAN : reply); },
  };
}

test("searching declined: an answer from memory, flagged, or an error when the model does not know", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const memory = { rows: [{ label: "2024", values: [2024, 4.39] }] };
  const r = await lookup("runs per game in 2024", { ...opts(scripted({ plan: PLAN, memory }), fetch), beforeSearch: async () => false });
  assert.equal(r.via, "memory");
  assert.deepEqual(fetch.asked, []);
  await assert.rejects(lookup("runs per game in 2024", { ...opts(scripted({ plan: PLAN, memory: { rows: [] } }), fetch), beforeSearch: async () => false }),
    (e) => e instanceof AskError && /declined/.test(e.message));
});

test("a model that says it knows, then does not, falls back to searching", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: { ...PLAN, known: true }, memory: { rows: [] }, pick: { table: 0, columns: [2], label: -1, filter: { column: 0, min: 2025, max: 2025 } } });
  const r = await lookup("runs per game in 2025", opts(model, fetch));
  assert.equal(r.via, "table");
  assert.ok(r.trail.includes("The model did not answer from its knowledge after all: searching."));
});

test("a list laid across: one column read down the page becomes a row", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: { ...PLAN, shape: "list" }, pick: { table: 0, columns: [3], label: -1, filter: { column: 0, min: 2023, max: 2025 } } });
  const r = await lookup("home runs per game, 2023 to 2025", opts(model, fetch));
  assert.equal(r.source, `[${[2023, 2024, 2025].map((y) => Number(hr(y))).join(", ")}]`);
});

test("formulas in the engine's syntax", async () => {
  const { checkFormula } = await import("../dist/index.js");
  assert.deepEqual(checkFormula("V = B*h", ["h", "B", "z"]), { expr: "B*h", params: ["h", "B"] });
  assert.deepEqual(checkFormula("4/3 * π * r^3", []), { expr: "4/3 * pi * r^3", params: ["r"] });
  assert.deepEqual(checkFormula("sqrt(a^2 + b^2)", ["a", "b"]), { expr: "sqrt(a^2 + b^2)", params: ["a", "b"] });
  assert.equal(checkFormula("\\frac{1}{2}bh", []), null);
  assert.equal(checkFormula("(a + b", []), null);
  assert.equal(checkFormula("", []), null);
});

test("a saved answer must be one a lookup could produce", async () => {
  const { validAnswer } = await import("../dist/index.js");
  assert.equal(validAnswer("table", "[1, -2.5; 3, 4]"), true);
  assert.equal(validAnswer("number", "42"), true);
  assert.equal(validAnswer("list", "[2, 3, 5]"), true);
  assert.equal(validAnswer("table", "diff(x^2, x)"), false);
  assert.equal(validAnswer("formula", "B*h", ["B", "h"]), true);
  assert.equal(validAnswer("formula", "B*h; x"), false);
  assert.equal(validAnswer("formula", "V = B*h"), false);
});

test("a check of the model's answer that may not search says so, and a stop while asking stops", async () => {
  const fetch = fakeFetch([]);
  const model = scripted({ plan: PRISM_PLAN, formula: PRISM });
  await assert.rejects(lookup("volume of a prism", { ...opts(model, fetch), forceSearch: true, beforeSearch: async () => false }),
    (e) => e instanceof AskError && e.message === "Searching was declined, so the answer could not be checked.");
  const ac = new AbortController();
  await assert.rejects(lookup("runs", { ...opts(scripted({ plan: PLAN }), fetch), signal: ac.signal, beforeSearch: async () => { ac.abort(); return false; } }),
    (e) => e instanceof AskError && e.message === "Stopped.");
});

test("a model that returns partial text when stopped is still stopped", async () => {
  const ac = new AbortController();
  const model = { id: "m", async complete() { ac.abort(); return "{\"sha"; } };
  await assert.rejects(lookup("x", { ...opts(model, fakeFetch([])), signal: ac.signal }), (e) => e instanceof AskError && e.message === "Stopped.");
});
