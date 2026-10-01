import { test } from "node:test";
import assert from "node:assert/strict";
import { lookup, evidence, AskError, wikipedia, webSearch, engineText } from "../dist/index.js";

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
      const step = schema.required.includes("searches") ? "plan" : schema.required.includes("expr") ? "formula"
        : schema.required.includes("sources") ? "direct" : "memory";
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

test("one value is a number, not a 1×1 matrix", () => {
  assert.equal(engineText([["42"]]), "42");
  assert.equal(engineText([["1", "-2"]]), "[1, -2]");
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

test("a stop request ends the lookup", async () => {
  const ac = new AbortController();
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: () => { ac.abort(); return JSON.stringify(PLAN); } });
  await assert.rejects(lookup("x", { ...opts(model, fetch), signal: ac.signal }), (e) => e instanceof AskError && e.message === "Stopped.");
});

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

test("searching declined: an answer from memory, flagged, or an error when the model does not know", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const memory = { rows: [{ label: "2024", values: [2024, 4.39] }] };
  const r = await lookup("runs per game in 2024", { ...opts(scripted({ plan: PLAN, memory }), fetch), beforeSearch: async () => false });
  assert.equal(r.via, "memory");
  assert.deepEqual(fetch.asked, []);
  await assert.rejects(lookup("runs per game in 2024", { ...opts(scripted({ plan: PLAN, memory: { rows: [] } }), fetch), beforeSearch: async () => false }),
    (e) => e instanceof AskError && /declined/.test(e.message));
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

test("direct: the model reads the pages and answers in shape; its numbers are found in what it read", async () => {
  const fetch = fakeFetch(champsRoutes);
  const model = scripted({
    plan: CHAMPS_PLAN,
    direct: (user) => {
      // the model is given the page's table as rows of cells
      assert.match(user, /## List of World Series champions \(https:\/\/en\.wikipedia\.org\/wiki\/List_of_World_Series_champions\)/);
      assert.match(user, /1935 \| Detroit Tigers \(AL\) \| Chicago Cubs/);
      return JSON.stringify({ found: true, rows: [[1935], [1945], [1968], [1984]], columns: ["year"], rowLabels: [], formula: { latex: "", expr: "", params: [], vars: [] },
        sources: [{ title: "List of World Series champions", url: "https://en.wikipedia.org/wiki/List_of_World_Series_champions", quote: "1935 Detroit Tigers" }] });
    },
  });
  const r = await lookup("what years did the tigers win the world series", { ...opts(model, fetch) });
  assert.equal(r.source, "[1935, 1945, 1968, 1984]");
  assert.equal(r.via, "text");
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.cites, [{ title: "List of World Series champions", url: "https://en.wikipedia.org/wiki/List_of_World_Series_champions" }]);
  assert.deepEqual(model.calls.map((c) => c.step), ["plan", "direct"]);
});

test("direct: a number the pages do not state is flagged, not dropped", async () => {
  const fetch = fakeFetch(champsRoutes);
  const model = scripted({ plan: CHAMPS_PLAN, direct: { found: true, rows: [[1935], [1945], [1968], [1984], [2006]], columns: ["year"], rowLabels: [], formula: { latex: "", expr: "", params: [], vars: [] }, sources: [] } });
  const r = await lookup("what years did the tigers win the world series", { ...opts(model, fetch) });
  assert.equal(r.source, "[1935, 1945, 1968, 1984, 2006]");
  assert.deepEqual(r.flagged, [], "2006 is on the page (a series the Tigers lost): found, so not flagged; the check is that numbers are real, not that they are right");
  const model2 = scripted({ plan: CHAMPS_PLAN, direct: { found: true, rows: [[1935], [1999]], columns: ["year"], rowLabels: [], formula: { latex: "", expr: "", params: [], vars: [] }, sources: [] } });
  const r2 = await lookup("what years did the tigers win the world series", { ...opts(model2, fetch) });
  assert.deepEqual(r2.flagged, [[0, 1]]);
  assert.match(r2.notes[0], /not in the sources the model read/);
});

test("direct with the model's own web search: one call, its citations the sources", async () => {
  const fetch = fakeFetch([]);
  let searched = 0;
  const model = {
    id: "or-model", calls: [],
    async complete({ schema }) { assert.ok(schema.required.includes("searches"), "only the plan is a plain call"); return JSON.stringify(CHAMPS_PLAN); },
    async search({ user }) {
      searched++;
      assert.match(user, /The answer is one number\./);
      return { text: JSON.stringify({ found: true, rows: [[4]], columns: ["World Series titles"], rowLabels: [], formula: { latex: "", expr: "", params: [], vars: [] },
        sources: [{ title: "Detroit Tigers", url: "https://en.wikipedia.org/wiki/Detroit_Tigers", quote: "The Tigers have won four World Series championships" }] }),
        citations: [{ url: "https://www.mlb.com/tigers/history", title: "Tigers history", content: "four World Series titles (1935, 1945, 1968, 1984)" }] };
    },
  };
  let asked = 0;
  const r = await lookup("how many world series have the tigers won", { ...opts(model, fetch), webSearch: true, beforeSearch: async () => { asked++; return true; } });
  assert.equal(searched, 1);
  assert.equal(asked, 1, "the model's web search is a search: asked first");
  assert.equal(r.source, "4");
  assert.equal(r.via, "search");
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.cites.map((c) => c.url), ["https://www.mlb.com/tigers/history", "https://en.wikipedia.org/wiki/Detroit_Tigers"]);
  assert.deepEqual(fetch.asked, [], "nothing fetched by the notebook itself");
});

test("direct: a formula is read from the LaTeX the model quotes, and checked against the pages", async () => {
  const area = `<table class="wikitable"><tr><th>Shape</th><th>Formula</th></tr><tr><td>Prism</td><td><math alttext="{\\displaystyle 2B+Ph}"></math></td></tr></table>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "Area" }] } }], [/rest_v1\/page\/html\/Area/, area]]);
  const plan = { lookup: true, shape: "formula", subject: "mathematics", known: false, searches: ["prism surface area"], columns: ["area"], rows: "", keywords: [] };
  const model = scripted({ plan, direct: { found: true, rows: [], columns: [], rowLabels: [], formula: { latex: "2B+Ph", expr: "2B+Ph", params: ["B", "P", "h"], vars: [{ name: "P", meaning: "perimeter of the base" }] }, sources: [] } });
  const r = await lookup("formula for the surface area of a prism", { ...opts(model, fetch) });
  assert.equal(r.source, "2*B + P*h");
  assert.deepEqual(r.flagged, []);
});

test("direct: no answer in the pages falls back on memory, flagged", async () => {
  const fetch = fakeFetch(champsRoutes);
  const model = scripted({ plan: CHAMPS_PLAN, direct: { found: false, rows: [], columns: [], rowLabels: [], formula: { latex: "", expr: "", params: [], vars: [] }, sources: [] }, memory: { rows: [{ label: "", values: [4] }] } });
  const r = await lookup("how many world series have the tigers won", { ...opts(model, fetch) });
  assert.equal(r.via, "memory");
  assert.ok(r.trail.includes("The model found no answer in the sources."));
});
const PRISM_PLAN = { shape: "formula", subject: "mathematics", known: true, searches: ["prism volume"], columns: ["volume"], rows: "", keywords: ["prism", "volume", "base", "height"] };

const PRISM = { found: true, expr: "V = B*h", params: ["B", "h"], vars: [{ name: "B", meaning: "area of the base" }, { name: "h", meaning: "height" }, { name: "x", meaning: "not used" }], quote: "V = Bh" };

/** A scripted model for the formula path: the plan, then the formula reply (for page or memory). */
function scriptedFormula(reply) {
  return {
    id: "scripted", calls: [],
    async complete({ schema }) { return JSON.stringify(schema.required.includes("searches") ? PRISM_PLAN : reply); },
  };
}


// --- the model answers from what was found, in the question's shape -------------------------------

const answer = (rows, columns = [], extra = {}) => ({ found: true, rows, columns, rowLabels: [], formula: { latex: "", expr: "", params: [], vars: [] }, sources: [], ...extra });

test("a table: the model reads the rows that fit (the last 20 years among them) and answers; every value is on the page", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const years = Array.from({ length: 20 }, (_, i) => 2006 + i);
  const model = scripted({
    plan: PLAN,
    direct: (user) => {
      assert.match(user, /## Batting by season \(https:\/\/en\.wikipedia\.org\/wiki\/Batting_by_season\)/);
      assert.match(user, /Table: League batting by season\nYear \| Teams \| R\/G \| HR\/G \| Notes/);
      for (const y of [1901, 2006, 2025]) assert.match(user, new RegExp(`\\n${y} \\| `), `the row for ${y} is given`);
      return JSON.stringify(answer(years.map((y) => [y, Number(rg(y)), Number(hr(y))]), ["season", "R/G", "HR/G"]));
    },
  });
  const r = await lookup("average runs and home runs per game in the MLB for the last 20 years", opts(model, fetch));
  assert.equal(r.via, "text");
  assert.equal(r.source, `[${years.map((y) => `${y}, ${Number(rg(y))}, ${Number(hr(y))}`).join("; ")}]`);
  assert.deepEqual(r.flagged, []);
  assert.deepEqual(r.columns, ["season", "R/G", "HR/G"]);
  assert.deepEqual(model.calls.map((c) => c.step), ["plan", "direct"], "no table picking: one call reads and answers");
});

test("the answer in a page's prose is what the model reads, not the likeliest-looking table", async () => {
  // the Detroit Tigers article: a "best seasons" table (which a table-picker once counted, answering 3), and the lead that says four
  const filler = Array.from({ length: 40 }, (_, i) => `<p>Paragraph ${i} about the ballpark, its architecture and its seats in the ${1900 + i}s.</p>`).join("");
  const page = `<p>The Detroit Tigers are an American professional baseball team based in Detroit. The Tigers have won four World Series championships (1935, 1945, 1968, and 1984).</p>${filler}
    <h2>Best seasons</h2><table class="wikitable"><tr><th>Season</th><th>Wins</th><th>Result</th></tr>
    <tr><td>1934</td><td>101</td><td>Lost World Series</td></tr><tr><td>1968</td><td>103</td><td>Won World Series</td></tr><tr><td>1984</td><td>104</td><td>Won World Series</td></tr><tr><td>1935</td><td>93</td><td>Won World Series</td></tr></table>`;
  const fetch = fakeFetch([[/w\/api\.php.*list=search/, { query: { search: [{ title: "Detroit Tigers" }] } }], [/rest_v1\/page\/html\/Detroit_Tigers/, page]]);
  const plan = { lookup: true, shape: "number", subject: "the world", known: true, searches: ["Detroit Tigers World Series titles"], columns: ["World Series titles"], rows: "", keywords: ["World Series", "won", "championships"] };
  const model = scripted({
    plan,
    direct: (user) => {
      assert.match(user, /The Tigers have won four World Series championships \(1935, 1945, 1968, and 1984\)\./);
      assert.doesNotMatch(user, /Paragraph 17 about the ballpark/, "prose that shares no word with the question is left out");
      return JSON.stringify(answer([[4]], ["World Series titles"], { sources: [{ title: "Detroit Tigers", url: "https://en.wikipedia.org/wiki/Detroit_Tigers", quote: "The Tigers have won four World Series championships" }] }));
    },
  });
  const r = await lookup("number of world series the detroit tigers have won", opts(model, fetch));
  assert.equal(r.shape, "number");
  assert.equal(r.source, "4");
  assert.deepEqual(r.flagged, [], "“four” on the page confirms 4");
  assert.ok(r.trail.includes("The model says it knows this, but questions about the world are searched for."));
  assert.ok(!model.calls.some((c) => c.step === "memory"));
});

test("what a model reads: the best passages and rows within its budget, page by page in order", () => {
  const page = (title, text, tables = []) => ({ title, url: `https://x/${title}`, source: "x", text, tables });
  const big = { caption: "Seasons", headers: ["Year", "Runs"], rows: Array.from({ length: 300 }, (_, i) => [String(1800 + i), String(i)]) };
  const plan = { keywords: ["runs"], columns: ["runs"], shape: "table" };
  // a table too big to give whole, whose rows the question cannot tell apart: its first rows and its last
  const e = evidence([page("A", "Nothing here.", [big])], "runs by year", plan, 2000);
  assert.match(e, /^## A \(https:\/\/x\/A\)\nTable: Seasons\nYear \| Runs\n1800 \| 0\n/);
  assert.match(e, /\n2099 \| 299\n\(\d+ rows of this table left out\)$/);
  assert.ok(e.length <= 2000);
  // rows with the question's words are the ones kept
  const teams = { caption: "Champions", headers: ["Year", "Winner"], rows: Array.from({ length: 300 }, (_, i) => [String(1800 + i), i % 50 === 7 ? "Detroit Tigers" : `Team ${i}`]) };
  const e2 = evidence([page("B", "", [teams])], "years the tigers won", { keywords: ["Tigers"], columns: ["year"], shape: "list" }, 2000);
  assert.deepEqual(e2.split("\n").filter((l) => /^\d{4} \|/.test(l)), ["1807 | Detroit Tigers", "1857 | Detroit Tigers", "1907 | Detroit Tigers", "1957 | Detroit Tigers", "2007 | Detroit Tigers", "2057 | Detroit Tigers"]);
  // pages in their order, each part in its page's order, the best first when the budget is short
  const e3 = evidence([page("P1", "Runs were scored in 1900.\nThe weather was fine that summer."), page("P2", "Runs and home runs rose in 1930 and runs fell later.")], "runs", plan, 10000);
  assert.equal(e3, "## P1 (https://x/P1)\nRuns were scored in 1900.\n\n## P2 (https://x/P2)\nRuns and home runs rose in 1930 and runs fell later.");
  assert.equal(evidence([page("Q", "Nothing that matches.")], "runs", plan, 10000), "");
});

test("a single column the model gives is a list, laid across", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: { ...PLAN, shape: "table" }, direct: answer([[Number(hr(2023))], [Number(hr(2024))], [Number(hr(2025))]], ["HR/G"]) });
  const r = await lookup("home runs per game, 2023 to 2025", opts(model, fetch));
  assert.equal(r.source, `[${[2023, 2024, 2025].map((y) => Number(hr(y))).join(", ")}]`);
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
  const model = scripted({ plan: PLAN, direct: (user) => { assert.match(user, /## Closed stats/); return JSON.stringify(answer([[2025, Number(rg(2025))]], ["year", "R/G"], { sources: [{ title: "Closed stats", url: "https://closed.example/bat", quote: "" }] })); } });
  const r = await lookup("runs per game in 2025", { model, fetch, sources: [webSearch(fetch, "https://searx.example/")], reader: "https://reader.example/?url={url}", today: "2026-09-30", useKnowledge: false });
  assert.equal(r.source, `[2025, ${Number(rg(2025))}]`);
  assert.deepEqual(r.cites, [{ title: "Closed stats", url: "https://closed.example/bat" }]);
  assert.ok(!fetch.asked.some((u) => u.startsWith("ftp:")));
});

test("a source that fails is noted in the trail, and the others still answer", async () => {
  const fetch = fakeFetch([[/searx\.broken/, new TypeError("Failed to fetch")], ...wikiRoutes(seasonsPage)]);
  const model = scripted({ plan: PLAN, direct: answer([[Number(hr(2025))]], ["HR/G"]) });
  const r = await lookup("home runs per game in 2025", { model, fetch, sources: [webSearch(fetch, "https://searx.broken/search?q={q}&format=json"), wikipedia(fetch)], today: "2026-09-30", useKnowledge: false });
  assert.equal(r.via, "text");
  assert.ok(r.trail.some((l) => /Searching web search for .* failed: Failed to fetch/.test(l)));
});

test("a model reply wrapped in prose or a code fence still reads", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: () => "Sure!\n```json\n" + JSON.stringify(PLAN) + "\n```", direct: () => "<think>hm</think>" + JSON.stringify(answer([[Number(rg(2025))]])) });
  const r = await lookup("runs per game in 2025", opts(model, fetch));
  assert.equal(r.source, String(Number(rg(2025))));
});

test("a model that says it knows, then does not, falls back to searching", async () => {
  const fetch = fakeFetch(wikiRoutes(seasonsPage));
  const model = scripted({ plan: { ...PLAN, subject: "mathematics", known: true }, memory: { rows: [] }, direct: answer([[Number(rg(2025))]]) });
  const r = await lookup("runs per game in 2025", opts(model, fetch));
  assert.equal(r.via, "text");
  assert.ok(r.trail.includes("The model did not answer from its knowledge after all: searching."));
});
