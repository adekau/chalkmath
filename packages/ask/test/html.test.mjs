import { test } from "node:test";
import assert from "node:assert/strict";
import { readHtml, readMarkdown, readPage, parseNumber, leadingNumber, numbersIn, numberText } from "../dist/index.js";

test("a Wikipedia-style table: grouped headers, spans, footnotes and hidden sort keys", () => {
  const html = `<section><h2 id="x">Year by year<span class="mw-editsection">[edit]</span></h2>
    <p>Scoring fell after 2000.<sup class="reference"><a href="#c1">[1]</a></sup></p>
    <table class="wikitable sortable"><thead>
      <tr><th rowspan="2">Season</th><th colspan="2">Per game</th><th rowspan="2">League</th></tr>
      <tr><th>R/G</th><th>HR/G</th></tr></thead>
      <tbody>
      <tr><td><span data-sort-value="2019" style="display:none">2019</span>2019</td><td>4.83<sup class="reference">[a]</sup></td><td>1.39</td><td rowspan="2">MLB</td></tr>
      <tr><td>2020</td><td>4.65</td><td>1.28</td></tr>
      <tr><td>2021</td><td>&minus;</td><td>1.22</td><td>MLB &amp; friends</td></tr>
    </tbody></table>
    <p>After the table &nbsp;text.</p></section>`;
  const { tables, text } = readHtml(html);
  assert.equal(tables.length, 1);
  const t = tables[0];
  assert.equal(t.caption, "Year by year");
  assert.deepEqual(t.headers, ["Season", "Per game / R/G", "Per game / HR/G", "League"]);
  assert.deepEqual(t.rows, [["2019", "4.83", "1.39", "MLB"], ["2020", "4.65", "1.28", "MLB"], ["2021", "−", "1.22", "MLB & friends"]]);
  assert.equal(text, "Year by year\nScoring fell after 2000.\nAfter the table text.");
});

test("tables without <thead>, a caption, and a nested table", () => {
  const { tables } = readHtml(`<table><caption>Outer</caption><tr><th>a</th><th>b</th></tr><tr><td>1</td><td><table><tr><th>x</th></tr><tr><td>9</td></tr></table></td></tr></table>`);
  assert.equal(tables.length, 2);
  const inner = tables.find((t) => t.headers[0] === "x");
  const outer = tables.find((t) => t.caption === "Outer");
  assert.deepEqual(inner.rows, [["9"]]);
  assert.deepEqual(outer.headers, ["a", "b"]);
  assert.deepEqual(outer.rows, [["1", ""]]);
});

test("scripts, styles and comments are not text", () => {
  const { text, tables } = readHtml(`<html><head><title>T</title><style>p{}</style></head><body><!-- <table><tr><td>1</td></tr></table> --><script>var x = "<p>no</p>";</script><p>yes &#8212; &#x41;</p></body></html>`);
  assert.equal(tables.length, 0);
  assert.equal(text, "yes — A");
});

test("Markdown pipe tables, as a reader service returns pages", () => {
  const md = "# Batting\n\nSome prose with [a link](https://x).\n\n| Year | R/G | HR/G |\n|---|---:|---|\n| 2024 | 4.39 | **1.12** |\n| 2023 | 4.62 |\n";
  const { tables, text } = readMarkdown(md);
  assert.deepEqual(tables, [{ caption: "Batting", headers: ["Year", "R/G", "HR/G"], rows: [["2024", "4.39", "1.12"], ["2023", "4.62", ""]] }]);
  assert.equal(text, "Batting\nSome prose with a link.");
  assert.equal(readPage(md, "text/plain").tables.length, 1);
  assert.equal(readPage("<p>hi</p>", "").text, "hi");
});

test("numbers as tables write them", () => {
  const cases = [["1,234", "1234"], ["−3.50", "-3.5"], ["12.5%", "12.5"], ["4.86[a]", "4.86"], ["$1,000.25", "1000.25"], ["007", "7"], [".5", "0.5"],
    ["1 234", "1234"], ["—", null], ["n/a", null], ["2–3", null], ["3.2M", null], ["", null], ["12,34", null], ["-0", "0"]];
  for (const [s, want] of cases) assert.equal(parseNumber(s), want, s);
  assert.equal(leadingNumber("2005–06"), 2005);
  assert.equal(leadingNumber("1,234 (est.)"), 1234);
  assert.equal(leadingNumber("about 3"), null);
  assert.deepEqual(numbersIn("In 2019 teams scored 4.83 runs, 1,500 more[3]."), [2019, 4.83, 1500]);
  assert.equal(numberText(1e21), "1000000000000000000000");
  assert.equal(numberText(-3), "-3");
  assert.equal(numberText(1e-7), "0.0000001");
  assert.equal(numberText(NaN), null);
});

test("a script's text is not markup: `e<t.length` does not hide the rest of the page", () => {
  const { tables, text } = readHtml(`<script>for(var e=0;e<t.length;e++)x(e)</script><p>Intro</p><STYLE>p<a{}</STYLE><table><tr><th>a</th></tr><tr><td>1</td></tr></table><div hidden>secret</div><p>end</p>`);
  assert.deepEqual(tables.map((t) => t.rows), [[["1"]]]);
  assert.equal(text, "Intro\nend");
});

test("a superscript or a stray space never joins digits into another number", () => {
  const { tables } = readHtml(`<table><tr><th>v</th></tr><tr><td>123<sup>1</sup></td></tr><tr><td>10<sup>6</sup></td></tr><tr><td>H<sub>2</sub>O</td></tr></table>`);
  assert.deepEqual(tables[0].rows.map((r) => r[0]), ["123^{1}", "10^{6}", "H_{2}O"]);
  for (const s of ["123^{1}", "10^{6}", "4 5", "1234 5"]) assert.equal(parseNumber(s), null, s);
  assert.equal(parseNumber("1 234 567"), "1234567");
  assert.equal(parseNumber("1'234"), "1234");
  assert.equal(parseNumber("− 3"), "-3");
});
