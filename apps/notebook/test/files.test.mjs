// Files as values (src/files.ts) and the data table's matrix reader (src/datagrid.ts): the parts that
// are plain code over strings. The modules are TypeScript for the page, so they are bundled first.
import { test } from "node:test";
import assert from "node:assert/strict";
import { build } from "esbuild";
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pathToFileURL } from "node:url";

const dir = mkdtempSync(join(tmpdir(), "chalk-files-"));
async function load(entry) {
  const out = await build({ entryPoints: [new URL(`../src/${entry}`, import.meta.url).pathname], bundle: true, format: "esm", write: false, platform: "neutral" });
  const file = join(dir, entry.replace(/\.ts$/, ".mjs"));
  writeFileSync(file, out.outputFiles[0].text);
  return import(pathToFileURL(file).href);
}
const F = await load("files.ts");
const G = await load("datagrid.ts");

const csv = (data, name = "t.csv") => ({ name, mime: "text/csv", data, origin: { asset: name } });
const svg = { name: "s.svg", mime: "image/svg+xml", data: "<svg><path d='M0 0L1 1'/></svg>", origin: { url: "https://x/s.svg" } };
const png = { name: "p.png", mime: "image/png", data: "iVBORw0KGgo=", binary: true, origin: { asset: "p.png" } };
const planets = csv("planet,mass,period\nMercury,0.330,88.0\nEarth,5.97,365.2\n", "planets.csv");
const nums = csv("1,2\n3,4\n5,6\n", "nums.csv");

/** A scope with the files above: names, attachments and imports; samplePoints draws a diagonal. */
function scope(names = {}) {
  return {
    lookup: (ref) => {
      if (ref.kind === "name") return names[ref.name];
      if (ref.kind === "asset") { const f = { "nums.csv": nums, "p.png": png }[ref.name]; if (!f) throw new Error(`nothing named ⟦${ref.name}⟧`); return f; }
      if (ref.kind === "url") return ref.url === "https://x/s.svg" ? svg : undefined;
      return names[ref.text];
    },
    sample: (_xml, n) => ({ points: Array.from({ length: n }, (_, i) => [i / n, i / n]), paths: 1 }),
  };
}

test("media types: the server's, unless it says nothing and the extension says more", () => {
  assert.equal(F.mimeFor("llama.svg", "text/plain; charset=utf-8"), "image/svg+xml");
  assert.equal(F.mimeFor("data.csv", "text/plain"), "text/csv");
  assert.equal(F.mimeFor("data.csv?raw=1", ""), "text/csv");
  assert.equal(F.mimeFor("photo", "image/png"), "image/png");
  assert.equal(F.mimeFor("x.json", "application/octet-stream"), "application/json");
  assert.equal(F.mimeFor("blob", ""), "application/octet-stream");
  assert.equal(F.kindOf({ mime: "text/csv" }), "table");
  assert.equal(F.kindOf({ mime: "image/png" }), "image");
  assert.equal(F.kindOf({ mime: "application/json" }), "json");
  assert.equal(F.kindOf({ mime: "application/pdf" }), "binary");
});

test("bytes: text kept as text, an SVG recognised whatever it was served as, the rest base64", () => {
  const enc = new TextEncoder();
  const t = F.fileFromBytes("a.csv", "text/csv", enc.encode("a,b\n1,2\n"), { url: "u" });
  assert.equal(t.data, "a,b\n1,2\n"); assert.equal(t.binary, undefined);
  const s = F.fileFromBytes("x", "text/plain", enc.encode("<?xml version='1.0'?>\n<svg xmlns='…'></svg>"), { url: "u" });
  assert.equal(s.mime, "image/svg+xml");
  const b = F.fileFromBytes("p.png", "image/png", new Uint8Array([137, 80, 78, 71]), { asset: "p.png" });
  assert.equal(b.binary, true); assert.equal(b.data, "iVBORw=="); assert.equal(F.fileSize(b), 4);
});

test("CSV: quotes, line breaks in fields, CRLF, a header only when the first row has no numbers", () => {
  assert.deepEqual(F.parseDelimited('a,"b,c","say ""hi"""\r\n1,"x\ny",3\n\n', ","), [["a", "b,c", 'say "hi"'], ["1", "x\ny", "3"]]);
  const t = F.tableOf(planets);
  assert.deepEqual(t.header, ["planet", "mass", "period"]);
  assert.equal(t.rows.length, 2); assert.equal(t.cols, 3);
  assert.deepEqual(F.numericColumns(t), [false, true, true]);
  assert.equal(F.tableOf(nums).header, null);
  // ragged rows are padded; a semicolon file read as such
  assert.deepEqual(F.tableOf(csv("x;y\n1;2\n3\n")).rows, [["1", "2"], ["3", ""]]);
  assert.deepEqual(F.tableOf({ name: "t.tsv", mime: "text/tab-separated-values", data: "a\tb\n1\t2", origin: { asset: "t.tsv" } }).rows, [["1", "2"]]);
});

test("numerals: exact, without exponents", () => {
  assert.equal(F.numeral("1.5e3"), "1500");
  assert.equal(F.numeral("12.5e-3"), "0.0125");
  assert.equal(F.numeral(".5"), "0.5");
  assert.equal(F.numeral("-5."), "-5");
  assert.equal(F.numeral("+007"), "7");
  assert.equal(F.numeral("-0.0"), "0");
  assert.equal(F.numeral("2E+2"), "200");
  assert.equal(F.numeral("n/a"), null);
  assert.equal(F.numeral(""), null);
});

test("a file cell: the file itself, bound or not; anything else is not one", () => {
  const sc = scope({ llama: svg });
  assert.deepEqual(F.fileCellOf('let llama = import("https://x/s.svg")', sc), { bind: "llama", file: svg });
  assert.deepEqual(F.fileCellOf("⟦p.png⟧", sc), { file: png });
  assert.deepEqual(F.fileCellOf("llama", sc), { file: svg });
  assert.equal(F.fileCellOf("x + 1", sc), null);
  assert.equal(F.fileCellOf("samplePoints(llama)", sc), null);
  assert.throws(() => F.fileCellOf("⟦gone.csv⟧", sc), /nothing named ⟦gone.csv⟧/);
});

test("functions on files become numbers before the engine sees the cell", () => {
  const sc = scope({ llama: svg, planets, data: nums });
  let r = F.resolveFiles("epicycles(samplePoints(llama, 4), 2)", sc);
  assert.equal(r.src, "epicycles([0.000, 0.000; 0.250, 0.250; 0.500, 0.500; 0.750, 0.750], 2)");
  assert.match(r.notes[0], /^samplePoints\(llama, 4\): 4 points along 1 path$/);
  assert.equal(F.resolveFiles("let m = matrix(⟦nums.csv⟧)", sc).src, "let m = [1, 2; 3, 4; 5, 6]");
  assert.equal(F.resolveFiles("dimensions(planets)", sc).src, "[2, 3]");
  assert.equal(F.resolveFiles("samplePoints(%)", scope({ "%": svg })).src.split(";").length, 400);
  // `%n` is Out[n] whole, not `%` followed by a number
  const outs = scope({ "%": svg, "%1": nums, "%12": planets });
  assert.equal(F.resolveFiles("dimensions(%1)", outs).src, "[3, 2]");
  assert.equal(F.resolveFiles("dimensions(%12) + %1[[2, 1]]", outs).src, "[2, 3] + 3");
  assert.equal(F.resolveFiles("%3 + 1", outs).src, "%3 + 1");
  assert.throws(() => F.resolveFiles("%1 + 1", outs), /%1 is a file, a CSV, not a number: %1\[\[All, 1\]\], mean\(%1\[\[All, 1\]\]\), matrix\(%1\)/);
  // a function that is not given a file is the engine's (a user's own `row`, say)
  assert.equal(F.resolveFiles("row(3) + matrix", sc).src, "row(3) + matrix");
  // a name that only starts like a file's is not cut
  assert.equal(F.resolveFiles("planetsX + llama2", sc).src, "planetsX + llama2");
});

test("errors say what a file is and what turns it into numbers", () => {
  const sc = scope({ llama: svg, planets, photo: png });
  assert.throws(() => F.resolveFiles("epicycles(llama, 60)", sc), /llama is a file, an SVG image, not a number: samplePoints\(llama\), samplePoints\(llama, 100\) turn it into numbers/);
  assert.throws(() => F.resolveFiles("planets + 1", sc), /planets is a file, a CSV, not a number: planets\[\[All, "mass"\]\], mean\(planets\[\[All, "mass"\]\]\), matrix\(planets\) turn it into numbers/);
  assert.throws(() => F.resolveFiles("samplePoints(photo)", sc), /samplePoints traces the paths of an SVG; photo is a PNG image/);
  assert.throws(() => F.resolveFiles("photo", sc), /nothing turns a PNG image into numbers/);
  assert.throws(() => F.resolveFiles("matrix(planets)", sc), /row 1, column "planet" is "Mercury", not a number/);
  assert.throws(() => F.resolveFiles('planets[["radius"]]', sc), /planets\[\["radius"\]\]: there is no column "radius" \(the columns are "planet", "mass", "period"\)/);
  assert.throws(() => F.resolveFiles("planets[[9]]", sc), /planets\[\[9\]\]: part 9 of 2: the index runs from 1 to 2 \(or -2 to -1\)/);
  assert.throws(() => F.resolveFiles("samplePoints(x^2)", sc), /samplePoints takes a file/);
  assert.throws(() => F.resolveFiles('epicycles(import("https://x/s.svg"))', sc), /import\("https:\/\/x\/s.svg"\) is a file/);
  // a let's own name and a function's parameters are not references to the file
  assert.equal(F.resolveFiles("let llama = 5", sc).src, "let llama = 5");
  assert.equal(F.resolveFiles("let f(planets) = planets^2", sc).src, "let f(planets) = planets^2");
  // nor is a name inside a string
  assert.equal(F.resolveFiles('planets[["llama"]]', scope({ planets: csv("llama\n1\n2\n") })).src, "[1; 2]");
});

test("parts of a table: rows, columns by name or position, spans, lists; numbers go to the engine", () => {
  const sc = scope({ planets, data: nums });
  const r = (src) => F.resolveFiles(src, sc).src;
  assert.equal(r('planets[[All, "period"]]'), "[88; 365.2]");
  assert.equal(r('planets[["mass"]]'), "[0.33; 5.97]");
  assert.equal(r('mean(planets[[All, {"mass", "period"}]])'), "mean([0.33, 88; 5.97, 365.2])");
  assert.equal(r('planets[[2, "period"]]'), "365.2");
  assert.equal(r('planets[[-1, 2;;3]]'), "[5.97, 365.2]");
  assert.equal(r("data[[1;;-1;;2]]"), "[1, 2; 5, 6]");
  assert.equal(r("data[[All, 2]] + 1"), "[2; 4; 6] + 1");
  // a part of numbers is the engine's: the parts after it stay in the source
  assert.equal(r('planets[["period"]][[2]]'), "[88; 365.2][[2]]");
  assert.equal(r("let x = data[[2]]"), "let x = [3, 4]");
  assert.equal(r("matrix(data[[1;;2]])"), "[1, 2; 3, 4]");
  // a part with text in it is a table of the notebook, not numbers
  const t = F.fileCellOf("let inner = planets[[1;;2, 1;;2]]", sc);
  assert.equal(t.bind, "inner");
  assert.equal(t.file.mime, "text/csv");
  assert.deepEqual(F.tableOf(t.file), { header: ["planet", "mass"], rows: [["Mercury", "0.330"], ["Earth", "5.97"]], cols: 2 });
  assert.equal(F.fileCellOf('planets[[2, "planet"]]', sc).file.data, "Earth");
  assert.throws(() => r("planets[[1]] + 1"), /planets\[\[1\]\] is a CSV, not a number/);
  assert.throws(() => r('planets[["mass", 1]]'), /these are counted, not named; give a position from 1/);
  assert.throws(() => r("planets[[1, 2, 3]]"), /a table has two dimensions, rows and columns; 3 indices were given/);
  assert.throws(() => r("planets[[k]]"), /an index of a file's part is a whole number, All, a span a;;b, a list \{i, j\} or a name in quotes; k is not one/);
});

test("parts of JSON: keys and positions level by level, All mapping over a list", () => {
  const j = { name: "j.json", mime: "application/json", data: JSON.stringify({ planets: [{ name: "Mercury", mass: 0.33 }, { name: "Earth", mass: 5.97 }], grid: [[1, 2], [3, 4]], note: "hi" }), origin: { asset: "j.json" } };
  const sc = scope({ j });
  const r = (src) => F.resolveFiles(src, sc).src;
  assert.equal(r('j[["planets", All, "mass"]]'), "[0.33, 5.97]");
  assert.equal(r('j[["planets", 2, "mass"]]'), "5.97");
  assert.equal(r('j[["grid"]]'), "[1, 2; 3, 4]");
  assert.equal(r('j[["grid", All, 1]]'), "[1, 3]");
  const records = F.fileCellOf('j[["planets"]]', sc).file;
  assert.equal(records.mime, "application/json");
  assert.deepEqual(F.jsonTable(JSON.parse(records.data)), { header: ["name", "mass"], rows: [["Mercury", "0.33"], ["Earth", "5.97"]], cols: 2 });
  assert.equal(F.fileCellOf('j[["note"]]', sc).file.data, "hi");
  assert.throws(() => r('j[["moons"]]'), /j\[\["moons"\]\]: there is no key "moons" \(the keys are "planets", "grid", "note"\)/);
  assert.throws(() => r('j[["note", 1]]'), /is a string, which has no parts/);
  assert.equal(F.resolveFiles('dimensions(j[["planets"]])', sc).src, "[2, 2]");
});

test("the data table reads a matrix output, and nothing else", () => {
  const m = "\\htmlData{path=root}{\\begin{bmatrix}\\htmlData{path=0.0}{1} & \\htmlData{path=0.1}{\\frac{1}{2}} \\\\ \\htmlData{path=1.0}{3} & \\htmlData{path=1.1}{4}\\end{bmatrix}}";
  assert.deepEqual(G.matrixEntries(m), [["\\htmlData{path=0.0}{1}", "\\htmlData{path=0.1}{\\frac{1}{2}}"], ["\\htmlData{path=1.0}{3}", "\\htmlData{path=1.1}{4}"]]);
  assert.deepEqual(G.matrixEntries("\\begin{bmatrix}1 \\\\ 2\\end{bmatrix}"), [["1"], ["2"]]);
  // a nested matrix is one entry
  assert.deepEqual(G.matrixEntries("\\begin{bmatrix}\\begin{bmatrix}1 & 2\\end{bmatrix} & 3\\end{bmatrix}"), [["\\begin{bmatrix}1 & 2\\end{bmatrix}", "3"]]);
  assert.equal(G.matrixEntries("\\begin{bmatrix}1\\end{bmatrix} + \\begin{bmatrix}2\\end{bmatrix}"), null);
  assert.equal(G.matrixEntries("x + 1"), null);
  assert.equal(G.matrixEntries("\\htmlData{path=root}{x} + \\htmlData{path=1}{\\begin{bmatrix}1\\end{bmatrix}}"), null);
});

// The notebook's parts of a table and the engine's parts of the same numbers as a matrix must agree,
// errors included: they are one feature on two kinds of value.
import { existsSync } from "node:fs";
const exe = new URL("../../../engine/.lake/build/bin/mathengine", import.meta.url).pathname;
test("parts agree with the engine's la.part", { skip: !existsSync(exe) && "no native engine build" }, async () => {
  const { leanNativeClient } = await import("@chalkmath/engine-host/lean-native");
  const client = leanNativeClient(exe);
  try {
    const grid = csv("1,2,3,4\n5,6,7,8\n9,10,11,12\n", "g.csv");
    const sc = scope({ g: grid });
    const M = "[1, 2, 3, 4; 5, 6, 7, 8; 9, 10, 11, 12]";
    const specs = ["2", "-1", "All, 2", "2, 3", "-1, -2", "1;;2", ";;2", "2;;", "1;;-1;;2", "3;;1;;-1", "{1, 3}", "{3, 1}, {4, 1}",
      "All, 2;;3", "2, All", "1;;3;;2, -1", "4", "0", "-4", "3;;1", "1, 5", "1, 2, 3", "1;;3;;0"];
    const differ = [];
    for (const spec of specs) {
      let ours;
      try { ours = F.resolveFiles(`g[[${spec}]]`, sc).src; } catch (e) {
        // the one message that names what it is a part of
        ours = `<error: ${e.message.replace(/^g\[\[[^\]]*\]\]: /, "").replace("a table has two dimensions, rows and columns;", "a matrix has two dimensions;")}>`;
      }
      const res = await client.call("engine.evaluate", { sessionId: "parts", cellId: spec, source: `${M}[[${spec}]]` });
      const theirs = res.ok ? res.rendered.text : `<error: ${res.error.message}>`;
      if (ours !== theirs) differ.push(`${spec}: notebook ${ours}, engine ${theirs}`);
    }
    assert.deepEqual(differ, []);
  } finally { client.close(); }
});

test("inside [[ ]]: the part being typed, and what can go there", () => {
  let c = F.partContext('mean(planets[[All, "ma');
  assert.deepEqual(c, { base: "planets", specs: ["All"], arg: 1, typed: { text: "ma", start: 19, quoted: true } });
  c = F.partContext("x + t[[2;;3, {1, ");
  assert.equal(c.base, "t"); assert.equal(c.arg, 1); assert.deepEqual(c.typed, { text: "", start: 17, quoted: false });
  c = F.partContext('j[["planets"]][[Al');
  assert.equal(c.base, 'j[["planets"]]'); assert.equal(c.arg, 0); assert.equal(c.typed.text, "Al");
  assert.equal(F.partContext("t[[f("), null);          // a call inside: its arguments are not indices
  assert.equal(F.partContext("[[1, 2]]"), null);       // not after a value: a nested matrix, not a part
  assert.equal(F.partContext("t[[1]] + 2"), null);     // closed
  const sc = scope({ planets });
  const help = F.partHelp(F.fileExprValue("planets", sc), ["All"], 1);
  assert.deepEqual(help.params, ["row", "column"]);
  assert.match(help.blurb, /3 columns: columns 1…3 \(or -3…-1\), All, a;;b, \{i, j\}, or by name: "planet", "mass", "period"/);
  assert.deepEqual(help.names, ["planet", "mass", "period"]);
  assert.match(F.partHelp(F.fileExprValue("planets", sc), [], 0).blurb, /^2 rows: rows 1…2/);
  const j = { name: "j.json", mime: "application/json", data: JSON.stringify({ planets: [{ name: "Mercury", mass: 0.33 }] }), origin: { asset: "j.json" } };
  const sj = scope({ j });
  assert.deepEqual(F.partHelp(F.fileExprValue("j", sj), ["\"planets\"", "All"], 2).names, ["name", "mass"]);
  assert.match(F.partHelp(F.fileExprValue("j", sj), ["\"planets\""], 1).blurb, /^A list of 1: positions 1…1/);
  // a part that is numbers has the engine's shape
  assert.deepEqual(F.fileExprValue('planets[["mass"]]', sc), { kind: "numbers", rows: 2, cols: 1, single: false });
  assert.match(F.partHelp({ kind: "numbers", rows: 3, cols: 4, single: false }, ["1"], 1).blurb, /^A 3×4 matrix: columns 1…4/);
});
