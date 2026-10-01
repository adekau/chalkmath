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
      return ref.text === "%" ? names["%"] : undefined;
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
  assert.equal(F.resolveFiles('column(planets, "period")', sc).src, "[88; 365.2]");
  assert.equal(F.resolveFiles("column(planets, 2) + 1", sc).src, "[0.33; 5.97] + 1");
  assert.equal(F.resolveFiles("row(data, 3)", sc).src, "[5, 6]");
  assert.equal(F.resolveFiles("dimensions(planets)", sc).src, "[2, 3]");
  assert.equal(F.resolveFiles("samplePoints(%)", scope({ "%": svg })).src.split(";").length, 400);
  // a function that is not given a file is the engine's (a user's own `row`, say)
  assert.equal(F.resolveFiles("row(3) + matrix", sc).src, "row(3) + matrix");
});

test("errors say what a file is and what turns it into numbers", () => {
  const sc = scope({ llama: svg, planets, photo: png });
  assert.throws(() => F.resolveFiles("epicycles(llama, 60)", sc), /llama is a file \(SVG image\), not a number: samplePoints\(llama\), samplePoints\(llama, n\) turn it into numbers/);
  assert.throws(() => F.resolveFiles("planets + 1", sc), /planets is a file \(CSV\), not a number: matrix\(planets\)/);
  assert.throws(() => F.resolveFiles("samplePoints(photo)", sc), /samplePoints traces the paths of an SVG; photo is a PNG image/);
  assert.throws(() => F.resolveFiles("photo", sc), /nothing turns PNG image into numbers yet/);
  assert.throws(() => F.resolveFiles("matrix(planets)", sc), /row 1, column "planet" is "Mercury", not a number/);
  assert.throws(() => F.resolveFiles('column(planets, "radius")', sc), /no column "radius" \(the columns are "planet", "mass", "period"\)/);
  assert.throws(() => F.resolveFiles("row(planets, 9)", sc), /the row is a number from 1 to 2/);
  assert.throws(() => F.resolveFiles("samplePoints(x^2)", sc), /samplePoints takes a file/);
  assert.throws(() => F.resolveFiles('epicycles(import("https://x/s.svg"))', sc), /import\("https:\/\/x\/s.svg"\) is a file/);
  // a let's own name and a function's parameters are not references to the file
  assert.equal(F.resolveFiles("let llama = 5", sc).src, "let llama = 5");
  assert.equal(F.resolveFiles("let f(planets) = planets^2", sc).src, "let f(planets) = planets^2");
  // nor is a name inside a string
  assert.equal(F.resolveFiles('column(planets, "llama")', scope({ planets: csv("llama\n1\n") })).src, "[1]");
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
