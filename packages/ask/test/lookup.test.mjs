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
        : schema.required.includes("answers") ? "confirm"
        : schema.properties.rows.items.required.includes("quote") ? "extract" : "memory";
      calls.push({ step, user });
      const r = replies[step];
      if (r === undefined) throw new Error(`no reply scripted for ${step}`);
      return typeof r === "function" ? r(user) : JSON.stringify(r);
    },
  };
}

const PLAN = { shape: "table", subject: "the world", known: false, searches: ["MLB runs per game by season"], columns: ["season", "runs per game", "home runs per game"], rows: "one MLB season, 2006 to 2025", keywords: ["year", "R/G", "HR/G", "runs", "home runs"] };
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
  assert.ok(r.trail.some((l) => /Chose the table “League batting by season” on “Batting by season”: columns Year, R\/G, HR\/G, rows where Year from 2006 to 2025/.test(l)), r.trail.join("\n"));
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

test("no table fits: numbers are lifted from prose; a row stands only when its sentence states its numbers and answers the question", async () => {
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
    confirm: (user) => { assert.match(user, /^1\. values: 2019, 4\.52, 1\.39\. Sentence: "The league's teams/m); assert.doesNotMatch(user, /^2\./m); return JSON.stringify({ answers: [true] }); },
  });
  const r = await lookup("runs and home runs per game, 2019 to 2021", opts(model, fetch));
  assert.equal(r.via, "text");
  assert.equal(r.source, "[2019, 4.52, 1.39]");
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.cites, [{ title: "Batting by season", url: "https://en.wikipedia.org/wiki/Batting_by_season" }]);
  assert.ok(r.trail.includes("Left out 2 rows the model lifted: their numbers are not in the sentence quoted."), r.trail.join("\n"));
});

test("a sentence that states a number but does not answer the question is left out", async () => {
  const page = `<p>The Tigers lost the 1940 World Series to the Cincinnati Reds.</p><p>The Tigers won the 1945 World Series against the Chicago Cubs.</p>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "Detroit Tigers" }] } }], [/rest_v1\/page\/html\/Detroit_Tigers/, page]]);
  const model = scripted({
    plan: { ...PLAN, columns: ["year"], keywords: ["World Series", "won"] },
    extract: { rows: [
      { label: "1940", values: [1940], quote: "The Tigers lost the 1940 World Series to the Cincinnati Reds." },
      { label: "1945", values: [1945], quote: "The Tigers won the 1945 World Series against the Chicago Cubs." },
    ] },
    confirm: { answers: [false, true] },
  });
  const r = await lookup("what years did the tigers win the world series", opts(model, fetch));
  assert.equal(r.source, "1945");
  assert.ok(r.trail.includes("Left out 1 row whose sentence does not answer the question: 1940"), r.trail.join("\n"));
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

const PRISM_PLAN = { shape: "formula", subject: "mathematics", known: true, searches: ["prism volume"], columns: ["volume"], rows: "", keywords: ["prism", "volume", "base", "height"] };
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
  const model = scripted({ plan: { shape: "number", subject: "physical science", known: true, searches: ["speed of light"], columns: ["speed of light in m/s"], rows: "", keywords: [] },
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
  const model = scripted({ plan: { ...PLAN, subject: "mathematics", known: true }, memory: { rows: [] }, pick: { table: 0, columns: [2], label: -1, filter: { column: 0, min: 2025, max: 2025 } } });
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

// --- what a real model got wrong: "?number of world series the tigers have won" -----------------

test("a question about the world is searched for even when the model is sure, and “number of” is one number", async () => {
  const page = `<p>The Detroit Tigers have won four World Series titles, in 1935, 1945, 1968 and 1984.</p>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "Detroit Tigers" }] } }], [/rest_v1\/page\/html\/Detroit_Tigers/, page]]);
  // the model's plan as Gemini Nano wrote it: a list, "known", and the rows field filled with years
  const plan = { shape: "list", subject: "the world", known: true, searches: ["Detroit Tigers World Series titles"], columns: ["Year"],
    rows: "190; 1905; 1911; 1912; 1913; 1918", keywords: ["World Series", "titles"] };
  const model = scripted({ plan, extract: { rows: [{ label: "Year", values: [4], quote: "The Detroit Tigers have won four World Series titles, in 1935, 1945, 1968 and 1984." }] }, confirm: { answers: [true] } });
  const r = await lookup("number of world series the tigers have won", opts(model, fetch));
  assert.equal(r.shape, "number");
  assert.equal(r.via, "text");
  assert.equal(r.source, "4");
  assert.deepEqual(r.flagged, []);
  assert.equal(r.rowsAre, "");
  assert.equal(r.rowLabels, undefined);
  assert.ok(r.trail.includes("The model says it knows this, but questions about the world are searched for."));
  assert.match(model.calls[0].user, /The answer is one number\./);
  assert.ok(!model.calls.some((c) => c.step === "memory"), "the model's memory was not asked");
});

test("the question's own words fix the shape when they can", async () => {
  const { shapeOf } = await import("../dist/index.js");
  assert.equal(shapeOf("number of world series the tigers have won"), "number");
  assert.equal(shapeOf("how many moons does Jupiter have"), "number");
  assert.equal(shapeOf("number of home runs per year for the last 20 years"), null);
  assert.equal(shapeOf("how many runs did each team score"), null);
  assert.equal(shapeOf("what is the formula for volume of a prism?"), "formula");
  assert.equal(shapeOf("the first ten primes"), null);
});

test("numbers spelled out in prose confirm a value", async () => {
  const { numbersIn } = await import("../dist/index.js");
  assert.deepEqual(numbersIn("won four titles, twice in a row, twenty-one games"), [4, 2, 21]);
  assert.ok(numbersIn("someone gone").every((n) => n !== 1), "“one” inside a word is no number");
});

// --- what a real model needed and could not say: rows by their text, and a count ------------------

// a champions table built like Wikipedia's "List of World Series champions" (abridged; the Tigers' wins are real)
const CHAMPS = [[1903, "Boston Americans", "Pittsburgh Pirates"], [1907, "Chicago Cubs", "Detroit Tigers"], [1935, "Detroit Tigers", "Chicago Cubs"],
  [1940, "Cincinnati Reds", "Detroit Tigers"], [1945, "Detroit Tigers", "Chicago Cubs"], [1968, "Detroit Tigers", "St. Louis Cardinals"],
  [1984, "Detroit Tigers", "San Diego Padres"], [2006, "St. Louis Cardinals", "Detroit Tigers"], [2024, "Los Angeles Dodgers", "New York Yankees"]];
const champsPage = `<h2>Results</h2><table class="wikitable"><tr><th>Year</th><th>Winning team</th><th>Losing team</th></tr>
${CHAMPS.map(([y, w, l]) => `<tr><td>${y}</td><td>${w} (AL)</td><td>${l}</td></tr>`).join("")}</table>`;
const champsRoutes = [[/w\/api\.php.*list=search/, { query: { search: [{ title: "List of World Series champions" }] } }], [/rest_v1\/page\/html\/List_of_World_Series_champions/, champsPage]];
const CHAMPS_PLAN = { shape: "table", subject: "the world", known: false, searches: ["World Series champions"], columns: ["Year"], rows: "", keywords: ["World Series", "Tigers"] };

test("“how many”: the rows whose text matches are counted by code, and the count names them", async () => {
  const fetch = fakeFetch(champsRoutes);
  const model = scripted({ plan: CHAMPS_PLAN, pick: { table: 0, columns: [0], label: -1, filter: { column: 0, min: 2023, max: 2025 }, match: { column: 1, text: "Tigers" }, count: true } });
  // the model's year filter (as Gemini Nano wrote it) is dropped: the question names no range
  const r = await lookup("number of world series the tigers have won", opts(model, fetch));
  assert.equal(r.shape, "number");
  assert.equal(r.source, "4");
  assert.ok(r.trail.includes("Dropped the model's filter on Year (from 2023 to 2025): the question names no range."), r.trail.join("\n"));
  const model2 = scripted({ plan: CHAMPS_PLAN, pick: { table: 0, columns: [0], label: -1, filter: { column: -1, min: 2023, max: 2025 }, match: { column: 1, text: "Tigers" }, count: true } });
  const r2 = await lookup("number of world series the tigers have won", opts(model2, fetch));
  assert.equal(r2.source, "4");
  assert.equal(r2.via, "table");
  assert.deepEqual(r2.columns, ["rows where Winning team contains “Tigers”"]);
  assert.deepEqual(r2.notes, ["Counted 4 rows of the table where Winning team contains “Tigers”: 1935, 1945, 1968, 1984."]);
  // the pick prompt shows the model an example of exactly this
  assert.match(model2.calls.find((c) => c.step === "pick").user, /1: Winning team \[text\]/);
});

test("a count is only taken when the question asks how many", async () => {
  const fetch = fakeFetch(champsRoutes);
  const model = scripted({ plan: CHAMPS_PLAN, pick: { table: 0, columns: [0], label: -1, filter: { column: -1, min: null, max: null }, match: { column: 1, text: "tigers" }, count: true } });
  const r = await lookup("what years did the tigers win the world series?", opts(model, fetch));
  assert.equal(r.source, "[1935, 1945, 1968, 1984]", "one column is a list, laid across");
  assert.deepEqual(r.notes, ["Only the rows where Winning team contains “tigers”."]);
});

// --- formulas are read from their LaTeX by code, not translated by the model ---------------------

test("LaTeX as pages write formulas, read into the engine's syntax; what it cannot read is refused", async () => {
  const { texToEngine } = await import("../dist/index.js");
  const read = (t) => texToEngine(t)?.expr ?? null;
  assert.equal(read("A = 2B + Ph"), "2*B + P*h");
  assert.equal(read("{\\displaystyle V=Bh}"), "B*h");
  assert.equal(read("V = \\frac{1}{3}Bh"), "1/3*B*h");
  assert.equal(read("V = \\frac{4}{3}\\pi r^3"), "4/3*pi*r^3");
  assert.equal(read("A=\\pi r^{2}"), "pi*r^2");
  assert.equal(read("c=\\sqrt{a^2+b^2}"), "sqrt(a^2 + b^2)");
  assert.equal(read("A = \\frac{1}{2}(b_1 + b_2)h"), "1/2*(b_1 + b_2)*h");
  assert.equal(read("V = lwh"), "l*w*h");
  assert.equal(read("s = r\\theta"), "r*θ");
  assert.equal(read("y = \\sin x + \\cos(2x)"), "sin(x) + cos(2*x)");
  assert.equal(read("\\sqrt[3]{V}"), "V^(1/3)");
  assert.equal(read("E = mc^2,"), "m*c^2");
  assert.equal(texToEngine("A = 2B + Ph").lhs, "A");
  for (const t of ["x = \\frac{-b \\pm \\sqrt{b^2-4ac}}{2a}", "A = \\sum_{i} a_i", "V = base_area * h", "|x|", "\\int f"]) assert.equal(texToEngine(t), null, t);
});

test("a formula a page states is read from its LaTeX, whatever the model made of it", async () => {
  // Wikipedia's "Area" has a table of surface areas; Gemini Nano chose the prism's row and wrote `{2*B+Ph}`
  const area = `<h2>Surface area</h2><table class="wikitable"><tr><th>Shape</th><th>Formula</th><th>Variables</th></tr>
    <tr><td>Cube</td><td><math alttext="{\\displaystyle 6s^{2}}"></math></td><td>s = side length</td></tr>
    <tr><td>Prism</td><td><math alttext="{\\displaystyle 2B+Ph}"></math></td><td>B = the area of a base, P = the perimeter of a base, h = the height of the prism</td></tr></table>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "Area" }] } }], [/rest_v1\/page\/html\/Area/, area]]);
  const plan = { shape: "formula", subject: "mathematics", known: false, searches: ["triangular prism area formula"], columns: ["area"], rows: "", keywords: ["prism", "area", "surface"] };
  const model = scripted({ plan, formula: { found: true, expr: "{2*B+Ph}", params: ["B", "P", "h"], quote: "2B+Ph",
    vars: [{ name: "B", meaning: "the area of a base" }, { name: "P", meaning: "the perimeter of a base" }, { name: "h", meaning: "the height" }] } });
  const r = await lookup("formula for area of a triangular prism", opts(model, fetch));
  assert.equal(r.via, "text");
  assert.equal(r.source, "2*B + P*h");
  assert.deepEqual(r.params, ["B", "P", "h"]);
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.cites, [{ title: "Area", url: "https://en.wikipedia.org/wiki/Area" }]);
  assert.ok(r.trail.includes("Read $2B+Ph$ as 2*B + P*h"), r.trail.join("\n"));
  assert.ok(!model.calls.some((c) => c.step === "memory" || (c.step === "formula" && !/Passages/.test(c.user))), "memory was not asked");
});

test("from memory, a model's formula with words for names is replaced by its LaTeX when that reads", async () => {
  const fetch = fakeFetch([]);
  const model = scripted({ plan: PRISM_PLAN, formula: { found: true, expr: "base_area*height", params: ["base_area", "height"], vars: [], quote: "V = Bh" } });
  const r = await lookup("volume of a prism", opts(model, fetch));
  assert.equal(r.via, "knowledge");
  assert.equal(r.source, "B*h");
});

// --- what Qwen3 4B got wrong ------------------------------------------------------------------

test("a question that asks to make something is no lookup: nothing is searched", async () => {
  const fetch = fakeFetch([]);
  const model = scripted({ plan: { ...PLAN, lookup: false } });
  await assert.rejects(lookup("random 5x5 matrix", opts(model, fetch)),
    (e) => e instanceof AskError && /make something rather than to look it up \(and the engine has no random numbers\)/.test(e.message));
  // the question's own words decide it even when the model says it is a lookup
  await assert.rejects(lookup("random 5x5 matrix", opts(scripted({ plan: PLAN }), fetch)), (e) => e instanceof AskError);
  assert.deepEqual(fetch.asked, []);
});

test("“how many” that finds one row with a number column chosen answers that row's number, not a count of 1", async () => {
  // Wikipedia's "World Series" has a table of teams' appearances; Qwen3 4B matched the Tigers' row and asked for a count
  const page = `<table class="wikitable"><tr><th>Teams<sup>†</sup></th><th>Apps</th><th>Wins</th><th>Losses</th></tr>
    <tr><td>New York Yankees</td><td>41</td><td>27</td><td>14</td></tr><tr><td>Detroit Tigers</td><td>11</td><td>4</td><td>7</td></tr></table>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "World Series" }] } }], [/rest_v1\/page\/html\/World_Series/, page]]);
  const model = scripted({ plan: CHAMPS_PLAN, pick: { table: 0, columns: [2], label: -1, filter: { column: -1, min: null, max: null }, match: { column: 0, text: "Tigers" }, count: true } });
  const r = await lookup("number of world series the tigers have won", opts(model, fetch));
  assert.equal(r.source, "4");
  assert.deepEqual(r.columns, ["Wins"]);
  assert.ok(r.trail.includes("One row matched, with Wins chosen: its value, not a count of rows."), r.trail.join("\n"));
});

test("a match keeps the rows with the question's words, not text the model copied from one row", async () => {
  // a seasons table; Qwen3 4B matched “Won 1935 World”, which only 1935's row contains
  const seasons = [[1934, "Lost 1934 World Series"], [1935, "Won 1935 World Series"], [1940, "Lost 1940 World Series"], [1945, "Won 1945 World Series"],
    [1968, "Won 1968 World Series"], [1984, "Won 1984 World Series"], [2006, "Lost 2006 World Series"], [2012, "Lost 2012 World Series"]];
  const page = `<table class="wikitable"><tr><th>Season</th><th>Wins</th><th>Postseason</th></tr>${seasons.map(([y, p]) => `<tr><td>${y}</td><td>90</td><td>${p}</td></tr>`).join("")}</table>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "Detroit Tigers" }] } }], [/rest_v1\/page\/html\/Detroit_Tigers/, page]]);
  const model = scripted({ plan: CHAMPS_PLAN, pick: { table: 0, columns: [0], label: -1, filter: { column: -1, min: null, max: null }, match: { column: 2, text: "Won 1935 World" }, count: false } });
  const r = await lookup("what years did the detroit tigers win the world series?", opts(model, fetch));
  assert.equal(r.source, "[1935, 1945, 1968, 1984]");
  const { matchWords } = await import("../dist/index.js");
  assert.deepEqual(matchWords("Won 1935 World"), ["won", "1935", "world"]);
});
