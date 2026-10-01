/**
 * Files as values: what `import("url")` and `⟦name⟧` stand for in a math cell.
 *
 * A file is kept as it came: its name, its media type and its contents (text, or base64 for
 * binary). A cell whose value is a file shows it by what it is (an image as the image, a CSV or TSV
 * as a table, JSON and other text as text, anything else as a card naming it), and `let x = …` binds
 * the name to the file. Nothing is converted on the way in.
 *
 * The engine deals only in numbers and never sees a file. A part of a file, or a function called on
 * one, is how it becomes numbers, and the notebook evaluates them before the cell is sent:
 * `t[[All, "mass"]]` is a table's column (Mathematica's Part, as the engine reads it on matrices),
 * `j[["planets", All, "mass"]]` a list inside JSON, `samplePoints(svg)` the points along an SVG's
 * paths, `matrix(t)` a table's numbers and `dimensions(t)` its size. A part that is not numbers (rows
 * with text in them, a JSON object) is a value of the notebook like the file it came from. A file
 * anywhere else in a math cell is an error that says what turns it into numbers.
 *
 * Everything here but `svgPoints` (which measures paths in the page) is plain code over strings.
 */

/** A file: attached to the notebook (`⟦name⟧`) or fetched from the web (`import("url")`). */
export interface FileValue {
  name: string;
  /** The media type, without parameters (`text/csv`, `image/png`). */
  mime: string;
  /** The contents: text, or base64 when `binary`. */
  data: string;
  binary?: boolean;
  /** Where it came from: an attachment by name, a URL, or a part of another file (by the
   *  expression that took it, `t[[2;;4]]`). */
  origin: { asset: string } | { url: string } | { derived: string };
}

/** How a file is shown, and which functions apply to it. */
export type FileKind = "image" | "table" | "json" | "text" | "binary";

const EXT_MIME: Record<string, string> = {
  svg: "image/svg+xml", png: "image/png", jpg: "image/jpeg", jpeg: "image/jpeg", gif: "image/gif", webp: "image/webp",
  avif: "image/avif", bmp: "image/bmp", ico: "image/x-icon",
  csv: "text/csv", tsv: "text/tab-separated-values", tab: "text/tab-separated-values",
  json: "application/json", geojson: "application/geo+json",
  txt: "text/plain", md: "text/markdown", tex: "text/x-tex", xml: "application/xml", html: "text/html", htm: "text/html",
  pdf: "application/pdf", zip: "application/zip",
};

/** A file name's extension, lower case, from a name or a URL (its path, not its query). */
function extOf(name: string): string {
  const path = name.replace(/[?#].*$/, "");
  const m = /\.([A-Za-z0-9]+)$/.exec(path);
  return m ? m[1]!.toLowerCase() : "";
}

/** A file's media type: what it was served or picked as, unless that says nothing (a raw file server
 *  sends CSV and SVG as text/plain, a download as octet-stream) and the extension says more. */
export function mimeFor(name: string, given = ""): string {
  const g = given.split(";")[0]!.trim().toLowerCase();
  const byExt = EXT_MIME[extOf(name)];
  if (byExt && (!g || g === "application/octet-stream" || g === "text/plain" || g === "binary/octet-stream")) return byExt;
  return g || byExt || "application/octet-stream";
}

/** Whether a media type is text (kept as text rather than base64). */
export function isTextMime(mime: string): boolean {
  return mime.startsWith("text/") || /[+/](xml|json)$/.test(mime) || mime === "application/javascript";
}

export function kindOf(f: { mime: string }): FileKind {
  const m = f.mime;
  if (m.startsWith("image/")) return "image";
  if (m === "text/csv" || m === "text/tab-separated-values" || m === "application/csv") return "table";
  if (/[+/]json$/.test(m)) return "json";
  if (isTextMime(m)) return "text";
  return "binary";
}

/** A file's contents as text (a binary file read as UTF-8). */
export function fileText(f: FileValue): string {
  if (!f.binary) return f.data;
  const bin = atob(f.data);
  return new TextDecoder().decode(Uint8Array.from(bin, (c) => c.charCodeAt(0)));
}

/** A file's size in bytes. */
export function fileSize(f: FileValue): number {
  if (f.binary) return Math.floor((f.data.length * 3) / 4) - (f.data.endsWith("==") ? 2 : f.data.endsWith("=") ? 1 : 0);
  return new TextEncoder().encode(f.data).length;
}

export function fmtSize(n: number): string {
  if (n < 1024) return `${n} B`;
  if (n < 1024 * 1024) return `${Math.round(n / 1024)} KB`;
  return `${(n / (1024 * 1024)).toFixed(1)} MB`;
}

/** What a media type is called in a caption. */
export function mimeLabel(mime: string): string {
  const known: Record<string, string> = {
    "text/csv": "CSV", "text/tab-separated-values": "TSV", "application/json": "JSON", "image/svg+xml": "SVG image",
    "image/png": "PNG image", "image/jpeg": "JPEG image", "image/gif": "GIF image", "image/webp": "WebP image",
    "text/plain": "text", "text/markdown": "Markdown", "application/pdf": "PDF",
  };
  return known[mime] ?? mime;
}

/** The URL an <img> can show a file at. */
export function dataUrl(f: FileValue): string {
  return f.binary ? `data:${f.mime};base64,${f.data}` : `data:${f.mime};charset=utf-8,${encodeURIComponent(f.data)}`;
}

/** Read fetched bytes as a file: text for text types, base64 otherwise. */
export function fileFromBytes(name: string, mime: string, bytes: Uint8Array, origin: FileValue["origin"]): FileValue {
  // an SVG served as anything at all is still an SVG
  if (!mime.startsWith("image/svg") && isTextMime(mime) || mime === "application/octet-stream") {
    const head = new TextDecoder().decode(bytes.subarray(0, 512));
    if (/^\s*(<\?xml[^>]*>\s*)?(<!--[\s\S]*?-->\s*)*(<!DOCTYPE[^>]*>\s*)?<svg[\s>]/i.test(head)) mime = "image/svg+xml";
  }
  if (isTextMime(mime)) return { name, mime, data: new TextDecoder().decode(bytes), origin };
  let bin = ""; for (let i = 0; i < bytes.length; i += 0x8000) bin += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
  return { name, mime, data: btoa(bin), binary: true, origin };
}

// --- Tables: CSV and TSV ------------------------------------------------------------------------

export interface Table {
  /** The first row, when it names the columns rather than holding data. */
  header: string[] | null;
  /** The data rows, each padded to `cols` fields. */
  rows: string[][];
  cols: number;
}

/** Rows of fields, RFC 4180 style: a field in double quotes may hold the delimiter, line breaks and
 *  `""` for a quote. A trailing empty line is not a row; a byte-order mark is dropped. */
export function parseDelimited(text: string, delim: string): string[][] {
  const rows: string[][] = [];
  let row: string[] = [], field = "", i = 0, quoted = false;
  if (text.charCodeAt(0) === 0xfeff) i = 1;
  for (; i < text.length; i++) {
    const c = text[i]!;
    if (quoted) {
      if (c === '"') { if (text[i + 1] === '"') { field += '"'; i++; } else quoted = false; }
      else field += c;
    } else if (c === '"' && field === "") quoted = true;
    else if (c === delim) { row.push(field); field = ""; }
    else if (c === "\n" || c === "\r") {
      if (c === "\r" && text[i + 1] === "\n") i++;
      row.push(field); rows.push(row); row = []; field = "";
    } else field += c;
  }
  if (field !== "" || row.length) { row.push(field); rows.push(row); }
  // blank lines are not rows
  return rows.filter((r) => r.length > 1 || r[0] !== "");
}

const NUM = /^[+-]?(\d+\.?\d*|\.\d+)([eE][+-]?\d+)?$/;
export const isNumeric = (s: string) => NUM.test(s.trim());

/** A numeric field as a numeral the engine reads: exact (no float rounding), without an exponent
 *  (`1.5e3` is `1500`, `.5` is `0.5`). Null for anything that is not a number. */
export function numeral(s: string): string | null {
  const t = s.trim();
  const m = /^([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/.exec(t);
  if (!m || !NUM.test(t)) return null;
  const sign = m[1] === "-" ? "-" : "";
  let int = m[2] ?? "", frac = m[3] ?? "";
  const exp = Number(m[4] ?? 0);
  if (exp > 0) { frac = frac.padEnd(exp, "0"); int += frac.slice(0, exp); frac = frac.slice(exp); }
  else if (exp < 0) { int = int.padStart(-exp + 1, "0"); frac = int.slice(int.length + exp) + frac; int = int.slice(0, int.length + exp); }
  int = int.replace(/^0+(?=\d)/, "") || "0";
  frac = frac.replace(/0+$/, "");
  const out = frac ? `${int}.${frac}` : int;
  return out === "0" ? "0" : sign + out;
}

const TABLES = new WeakMap<FileValue, Table>();

/** A CSV or TSV file as a table. The first row is a header when it has no numbers in it and there
 *  are rows after it. A comma file whose first line has no comma but semicolons or tabs is read with
 *  those (a spreadsheet's "CSV" in some locales). */
export function tableOf(f: FileValue): Table {
  const hit = TABLES.get(f); if (hit) return hit;
  const text = fileText(f);
  let delim = f.mime === "text/tab-separated-values" ? "\t" : ",";
  if (delim === ",") {
    const first = text.split(/\r?\n/, 1)[0] ?? "";
    if (!first.includes(",")) delim = first.includes("\t") ? "\t" : first.includes(";") ? ";" : ",";
  }
  const all = parseDelimited(text, delim);
  const cols = Math.max(0, ...all.map((r) => r.length));
  const pad = (r: string[]) => r.length < cols ? [...r, ...Array<string>(cols - r.length).fill("")] : r;
  const head = all[0];
  const isHeader = !!head && all.length > 1 && head.every((s) => s.trim() !== "" && !isNumeric(s));
  const t: Table = { header: isHeader ? pad(head.map((s) => s.trim())) : null, rows: (isHeader ? all.slice(1) : all).map(pad), cols };
  TABLES.set(f, t);
  return t;
}

/** Which columns hold only numbers (blank fields aside), for right-aligning them. */
export function numericColumns(t: Table): boolean[] {
  return Array.from({ length: t.cols }, (_, c) => {
    let any = false;
    for (const r of t.rows) { const v = r[c]!.trim(); if (!v) continue; if (!isNumeric(v)) return false; any = true; }
    return any;
  });
}

/** A column's name in messages: its header, or its number. */
const colName = (t: Table, c: number) => t.header?.[c] ? `"${t.header[c]}"` : String(c + 1);

/** The numeral at a data row and column, or an error naming the field. */
function cellNumeral(t: Table, r: number, c: number, what: string): string {
  const v = t.rows[r]![c]!;
  const n = numeral(v);
  if (n === null) throw new Error(`${what}: row ${r + 1}, column ${colName(t, c)} is ${v.trim() ? `"${v.trim()}"` : "empty"}, not a number`);
  return n;
}

// --- Part: x[[…]], Mathematica's indexing, on files ---------------------------------------------
// The engine's `la.part` (engine/MathEngine/LinAlg.lean), mirrored for what the engine cannot hold:
// positions count from 1, a negative one from the end, `All`, spans `a;;b;;s` with both ends
// included, lists `{i, j}`; and, for a table's columns and a JSON object's keys, names in quotes. A
// single index drops its dimension; a span or a list keeps it. A selection that is all numbers goes
// to the engine as a numeral or a matrix (a row stays a row, a column a column); one that is not
// stays a value of the notebook: a smaller table, a piece of JSON, or text.

/** One index of a part, as written. */
export type Spec =
  | { kind: "index"; k: number }
  | { kind: "all" }
  | { kind: "span"; a: number; b: number; step: number }
  | { kind: "list"; items: (number | string)[] }
  | { kind: "name"; name: string };

const INT = /^[+-]?\d+$/;
const STR = /^"([^"]*)"$|^'([^']*)'$/;

/** An index as written inside `[[ ]]`. */
export function parseSpec(text: string): Spec {
  const t = text.trim();
  if (t === "All") return { kind: "all" };
  const str = STR.exec(t);
  if (str) return { kind: "name", name: str[1] ?? str[2]! };
  if (INT.test(t)) return { kind: "index", k: Number(t) };
  if (t.startsWith("{") && t.endsWith("}")) {
    const items = splitArgs(t.slice(1, -1)).map((x) => {
      const s = STR.exec(x);
      if (s) return s[1] ?? s[2]!;
      if (INT.test(x)) return Number(x);
      throw new Error(`a list of indices holds whole numbers or names in quotes; ${x || "an empty item"} is neither`);
    });
    if (!items.length) throw new Error("an empty list of indices selects nothing");
    return { kind: "list", items };
  }
  if (t.includes(";;")) {
    const parts = t.split(";;").map((x) => x.trim());
    if (parts.length > 3 || parts.some((x, i) => x !== "" && !INT.test(x) || (i === 2 && x === ""))) throw new Error(`a span is a;;b or a;;b;;step with whole numbers; ${t} is not one`);
    return { kind: "span", a: parts[0] ? Number(parts[0]) : 1, b: parts[1] ? Number(parts[1]) : -1, step: parts[2] ? Number(parts[2]) : 1 };
  }
  throw new Error(`an index of a file's part is a whole number, All, a span a;;b, a list {i, j} or a name in quotes; ${t} is not one`);
}

/** `partPos` in LinAlg.lean: the position (from 0) index `k` names among `n`. */
export function partPos(n: number, k: number): number {
  if (k === 0) throw new Error("parts count from 1 (and -1 is the last); there is no part 0");
  if (k > 0 && k <= n) return k - 1;
  if (k < 0 && -k <= n) return n + k;
  throw new Error(`part ${k} of ${n}: the index runs from 1 to ${n} (or -${n} to -1)`);
}

/** `spanIndices` in LinAlg.lean: from `i` to `j`, both included, in steps of `st`. */
export function spanIndices(i: number, j: number, st: number): number[] {
  const out: number[] = [];
  if (st > 0) for (let x = i; x <= j; x += st) out.push(x);
  else for (let x = i; x >= j; x += st) out.push(x);
  return out;
}

/** `partSpec` in LinAlg.lean: the positions a spec selects among `n`, and whether it was a single
 *  index. `named` reads a name (a column's header, an object's key), where there are names. */
export function partSpec(n: number, s: Spec, named?: (name: string) => number): { is: number[]; single: boolean } {
  const pos = (x: number | string) => typeof x === "number" ? partPos(n, x) : named ? named(x) : noNames(x);
  switch (s.kind) {
    case "all": return { is: Array.from({ length: n }, (_, i) => i), single: false };
    case "index": return { is: [partPos(n, s.k)], single: true };
    case "name": return { is: [pos(s.name)], single: true };
    case "list": return { is: s.items.map(pos), single: false };
    case "span": {
      if (s.step === 0) throw new Error("the step of a span is a nonzero whole number, not 0");
      const is = spanIndices(partPos(n, s.a), partPos(n, s.b), s.step);
      if (!is.length) throw new Error(`the span ${s.a};;${s.b} selects nothing`);
      return { is, single: false };
    }
  }
}
const noNames = (name: string): never => { throw new Error(`"${name}": these are counted, not named; give a position from 1`); };

/** What a part of a file is: numbers for the engine (a numeral or a matrix literal), or a value of
 *  the notebook. */
export type Picked =
  | { kind: "numbers"; text: string; rows: number; cols: number; single: boolean }
  | { kind: "file"; file: FileValue };

/** A value made by selecting from a file: named by the expression that made it. */
function derived(name: string, mime: string, data: string): FileValue {
  return { name, mime, data, origin: { derived: name } };
}

/** Rows of numerals as the engine's literal: a numeral, a row `[a, b]`, a column `[a; b]` or a matrix. */
function literal(cells: string[][], single: boolean): string {
  if (single) return cells[0]![0]!;
  return `[${cells.map((r) => r.join(", ")).join("; ")}]`;
}

/** A CSV field, quoted when it must be. */
const csvField = (v: string) => /[",\n\r]/.test(v) ? `"${v.replace(/"/g, '""')}"` : v;

/** `t[[rows, columns]]` on a table. One index alone picks rows, unless it is a name (or a list of
 *  names), which picks columns: `t[["mass"]]`. */
function selectTable(f: FileValue, specs: Spec[], what: string): Picked {
  const t = tableOf(f);
  const named = (name: string) => {
    let c = t.header?.indexOf(name) ?? -1;
    if (c < 0) c = t.header?.findIndex((h) => h.toLowerCase() === name.toLowerCase()) ?? -1;
    if (c < 0) throw new Error(t.header ? `${what}: there is no column "${name}" (the columns are ${t.header.map((h) => `"${h}"`).join(", ")})` : `${what}: the table has no header row, so its columns are counted from 1, not named`);
    return c;
  };
  const byName = (s: Spec) => s.kind === "name" || (s.kind === "list" && s.items.every((x) => typeof x === "string"));
  let rowSpec: Spec, colSpec: Spec;
  if (specs.length === 1) [rowSpec, colSpec] = byName(specs[0]!) ? [{ kind: "all" }, specs[0]!] : [specs[0]!, { kind: "all" }];
  else if (specs.length === 2) [rowSpec, colSpec] = [specs[0]!, specs[1]!];
  else throw new Error(`${what}: a table has two dimensions, rows and columns; ${specs.length} indices were given`);
  if (!t.rows.length) throw new Error(`${what}: the table has no data rows`);
  const wrap = <T,>(fn: () => T): T => { try { return fn(); } catch (e) { throw new Error(`${what}: ${e instanceof Error ? e.message.replace(/^[^:]*\[\[[^\]]*\]\]: /, "") : String(e)}`); } };
  const r = wrap(() => partSpec(t.rows.length, rowSpec, (x) => noNames(x)));
  const c = wrap(() => partSpec(t.cols, colSpec, named));
  const cells = r.is.map((i) => c.is.map((j) => t.rows[i]![j]!));
  const nums = cells.map((row) => row.map((v) => numeral(v)));
  if (nums.every((row) => row.every((v) => v !== null))) {
    const n = nums as string[][];
    // a single column keeps its orientation, as the engine's part does
    const shaped = c.single && !r.single ? n.map((row) => [row[0]!]) : r.single && !c.single ? [n[0]!] : n;
    return { kind: "numbers", text: literal(shaped, r.single && c.single), rows: shaped.length, cols: shaped[0]!.length, single: r.single && c.single };
  }
  if (r.single && c.single) return { kind: "file", file: derived(what, "text/plain", cells[0]![0]!) };
  const header = t.header ? c.is.map((j) => t.header![j]!) : null;
  const sub: Table = { header, rows: cells, cols: c.is.length };
  const lines = [...(header ? [header] : []), ...cells].map((row) => row.map(csvField).join(","));
  const file = derived(what, "text/csv", lines.join("\n") + "\n");
  TABLES.set(file, sub);   // the table as selected, not as a header guess would re-read it
  return { kind: "file", file };
}

type Json = null | boolean | number | string | Json[] | { [k: string]: Json };
const isObj = (v: Json): v is { [k: string]: Json } => typeof v === "object" && v !== null && !Array.isArray(v);
const jsonKind = (v: Json) => v === null ? "null" : Array.isArray(v) ? "a list" : typeof v === "object" ? "an object" : typeof v === "string" ? "a string" : typeof v === "number" ? "a number" : "a boolean";

/** Mathematica's Part on nested lists and associations: each index goes one level down; a span,
 *  list or `All` keeps the level and the rest of the indices apply to each element. */
function partJson(v: Json, specs: Spec[]): Json {
  if (!specs.length) return v;
  const [s, ...rest] = specs as [Spec, ...Spec[]];
  if (Array.isArray(v)) {
    const { is, single } = partSpec(v.length, s);
    return single ? partJson(v[is[0]!]!, rest) : is.map((i) => partJson(v[i]!, rest));
  }
  if (isObj(v)) {
    const keys = Object.keys(v);
    const named = (name: string) => {
      const k = keys.indexOf(name);
      if (k < 0) throw new Error(`there is no key "${name}"${keys.length ? ` (the keys are ${keys.slice(0, 12).map((k) => `"${k}"`).join(", ")}${keys.length > 12 ? ", …" : ""})` : ""}`);
      return k;
    };
    const { is, single } = partSpec(keys.length, s, named);
    if (single) return partJson(v[keys[is[0]!]!]!, rest);
    return Object.fromEntries(is.map((i) => [keys[i]!, partJson(v[keys[i]!]!, rest)]));
  }
  throw new Error(`${JSON.stringify(v).slice(0, 40)} is ${jsonKind(v)}, which has no parts`);
}

/** A JSON value as numbers, when it is a number, a list of numbers (a row) or a list of equal lists
 *  of numbers (a matrix). */
function jsonNumbers(v: Json): Picked | null {
  const num = (x: Json) => typeof x === "number" ? numeral(String(x)) : null;
  if (typeof v === "number") { const n = num(v); return n === null ? null : { kind: "numbers", text: n, rows: 1, cols: 1, single: true }; }
  if (!Array.isArray(v) || !v.length) return null;
  if (v.every((x) => typeof x === "number")) return { kind: "numbers", text: literal([v.map((x) => num(x)!)], false), rows: 1, cols: v.length, single: false };
  if (v.every((x) => Array.isArray(x) && x.length === (v[0] as Json[]).length && x.length > 0 && x.every((y) => typeof y === "number"))) {
    const rows = (v as number[][]).map((r) => r.map((x) => num(x)!));
    return { kind: "numbers", text: literal(rows, false), rows: rows.length, cols: rows[0]!.length, single: false };
  }
  return null;
}

/** The parsed JSON of a file (cached). */
const JSONS = new WeakMap<FileValue, Json>();
export function jsonOf(f: FileValue): Json {
  if (JSONS.has(f)) return JSONS.get(f)!;
  let v: Json;
  try { v = JSON.parse(fileText(f)) as Json; } catch (e) { throw new Error(`${f.name} is not valid JSON: ${e instanceof Error ? e.message : String(e)}`); }
  JSONS.set(f, v);
  return v;
}

/** A JSON value that is a list of records (objects of plain values) or of equal lists: a table. */
export function jsonTable(v: Json): Table | null {
  if (!Array.isArray(v) || !v.length) return null;
  const cell = (x: Json | undefined) => x === undefined || x === null ? "" : typeof x === "object" ? JSON.stringify(x) : String(x);
  if (v.every((x) => isObj(x))) {
    const header = [...new Set(v.flatMap((x) => Object.keys(x as object)))];
    if (!header.length) return null;
    return { header, rows: v.map((x) => header.map((k) => cell((x as { [k: string]: Json })[k]))), cols: header.length };
  }
  if (v.every((x) => Array.isArray(x)) && (v as Json[][]).every((x) => !x.some((y) => typeof y === "object" && y !== null))) {
    const cols = Math.max(...(v as Json[][]).map((x) => x.length));
    if (!cols) return null;
    return { header: null, rows: (v as Json[][]).map((x) => Array.from({ length: cols }, (_, j) => cell(x[j]))), cols };
  }
  return null;
}

function selectJson(f: FileValue, specs: Spec[], what: string): Picked {
  let v: Json;
  try { v = partJson(jsonOf(f), specs); } catch (e) { throw new Error(`${what}: ${e instanceof Error ? e.message : String(e)}`); }
  const n = jsonNumbers(v);
  if (n) return n;
  if (typeof v === "string") return { kind: "file", file: derived(what, "text/plain", v) };
  return { kind: "file", file: derived(what, "application/json", JSON.stringify(v, null, 2)) };
}

/** `x[[…]]` on a file. */
function selectFile(f: FileValue, specs: Spec[], what: string): Picked {
  const kind = kindOf(f);
  if (kind === "table") return selectTable(f, specs, what);
  if (kind === "json") return selectJson(f, specs, what);
  throw new Error(`${what}: ${anA(mimeLabel(f.mime))} has no parts${kind === "image" && f.mime === "image/svg+xml" ? `; samplePoints turns it into a matrix, which has` : ""}`);
}
/** "a" or "an" by sound: an acronym is read letter by letter (an SVG, a PNG), a word as written. */
const anA = (w: string) => `${(/^[A-Z]{2}/.test(w) ? /^[AEFHILMNORSX]/.test(w) : /^[aeiou]/i.test(w)) ? "an" : "a"} ${w}`;

// --- File expressions: a reference to a file, then any parts ------------------------------------

/** A reference to a file in a math cell's source. */
export type FileRef =
  | { kind: "asset"; name: string }
  | { kind: "url"; url: string }
  | { kind: "name"; name: string }
  | { kind: "out"; text: string };

/** What the notebook knows when it reads a cell: the files the cell may refer to. */
export interface FileScope {
  /** The file a reference stands for; `undefined` when a name or output is not a file. A missing
   *  attachment or an import not fetched throws with the reason. */
  lookup(ref: FileRef): FileValue | undefined;
  /** An SVG's points along its paths (`svgPoints` in the page). */
  sample(xml: string, n: number): { points: [number, number][]; paths: number };
}

const IDENT = /^[A-Za-z_][A-Za-z0-9_]*$/;

/** The file reference a piece of source is, exactly, if any (not yet looked up). */
export function parseFileRef(s: string): FileRef | null {
  const t = s.trim();
  let m = /^⟦([^⟧]+)⟧$/.exec(t);
  if (m) return { kind: "asset", name: m[1]! };
  m = /^import\(\s*(["'])([^"']*)\1\s*\)$/.exec(t);
  if (m) return { kind: "url", url: m[2]! };
  if (/^%(%*|\d+)$/.test(t)) return { kind: "out", text: t };
  if (IDENT.test(t)) return { kind: "name", name: t };
  return null;
}

/** Where the reference starting at `i` ends (an attachment, an import, an output or a name), or -1.
 *  `%n` is tried before `%`, `%%`: unanchored, `%*` matches nothing and `%12` would end at `%`. */
function refEnd(src: string, i: number): number {
  const rest = src.slice(i);
  const m = /^⟦[^⟧]+⟧/.exec(rest) ?? /^import\(\s*(["'])[^"']*\1\s*\)/.exec(rest) ?? /^%(\d+|%*)/.exec(rest)
    ?? (isIdentChar(src[i - 1]) ? null : /^[A-Za-z_][A-Za-z0-9_]*/.exec(rest));
  return m ? i + m[0].length : -1;
}

/** The parts written after a reference: the text inside each `[[ ]]`, and where they end. */
export function partsAfter(src: string, i: number): { parts: string[]; end: number } {
  const parts: string[] = [];
  let k = i;
  for (;;) {
    let j = k; while (src[j] === " " || src[j] === "\t") j++;
    if (src[j] !== "[" || src[j + 1] !== "[") break;
    const close = matching(src, j);
    if (close < 0 || src[close - 1] !== "]") break;
    parts.push(src.slice(j + 2, close - 1));
    k = close + 1;
  }
  return { parts, end: k };
}

/** A file expression's value: the file, or what its parts select. `x` is how the source wrote it. */
type FileExpr = { x: string; end: number } & ({ kind: "file"; file: FileValue } | { kind: "numbers"; text: string; rows: number; cols: number; single: boolean; rest: string });

/** The file expression starting at `i`, if a file is there: its reference, then the parts that can
 *  be taken from the file. A part of numbers is the engine's, so once a selection is numbers the
 *  parts after it are left in the source for the engine (`t[["mass"]][[2]]`). */
function fileExprAt(src: string, i: number, scope: FileScope, shadow: Set<string>): FileExpr | null {
  const e = refEnd(src, i);
  if (e < 0) return null;
  const ref = parseFileRef(src.slice(i, e))!;
  if (ref.kind === "name" && shadow.has(ref.name)) return null;
  const f = scope.lookup(ref);
  if (!f) return null;
  const { parts, end } = partsAfter(src, e);
  let x = src.slice(i, e);
  let cur: FileValue = f;
  for (let p = 0; p < parts.length; p++) {
    const what = `${x}[[${parts[p]!.trim()}]]`;
    const picked = selectFile(cur, splitArgs(parts[p]!).map(parseSpec), what);
    x = what;
    if (picked.kind === "numbers") {
      const rest = parts.slice(p + 1).map((q) => `[[${q}]]`).join("");
      return { kind: "numbers", text: picked.text, rows: picked.rows, cols: picked.cols, single: picked.single, rest, x, end };
    }
    cur = picked.file;
  }
  return { kind: "file", file: cur, x, end };
}

/** The URLs a cell imports, to fetch before it is read. */
export function importsIn(src: string): string[] {
  return [...src.matchAll(/\bimport\(\s*(["'])([^"']*)\1\s*\)/g)].map((m) => m[2]!);
}

/** A cell whose value is a file: `import("url")`, `⟦name⟧`, a name bound to a file or an output
 *  that is one (`%`), or a part of one that is not numbers (`t[[2;;4]]`), optionally bound with
 *  `let x = …`. */
export function fileCellOf(src: string, scope: FileScope): { bind?: string; file: FileValue } | null {
  const m = /^(\s*(?:let\s+([A-Za-z_][A-Za-z0-9_]*)\s*=)?\s*)([\s\S]*?)\s*$/.exec(src)!;
  const at = m[1]!.length;
  const fe = fileExprAt(src, at, scope, new Set());
  if (!fe || fe.kind !== "file" || src.slice(fe.end).trim()) return null;
  return m[2] ? { bind: m[2], file: fe.file } : { file: fe.file };
}

/** Examples of what a file's caption offers: its parts, with its own column names and keys, and the
 *  functions that turn it into numbers. */
export function helpersFor(f: FileValue, x: string): string[] {
  if (f.mime === "image/svg+xml") return [`samplePoints(${x})`, `samplePoints(${x}, n)`];
  const kind = kindOf(f);
  if (kind === "table") {
    let t: Table;
    try { t = tableOf(f); } catch { return []; }
    const nums = numericColumns(t);
    const c = nums.indexOf(true);
    const col = c >= 0 ? (t.header ? `"${t.header[c]}"` : String(c + 1)) : null;
    return [`${x}[[1]]`, ...(col ? [`${x}[[All, ${col}]]`, `mean(${x}[[All, ${col}]])`] : []), `${x}[[1;;3]]`, `matrix(${x})`, `dimensions(${x})`];
  }
  if (kind === "json") {
    let v: Json;
    try { v = jsonOf(f); } catch { return []; }
    if (isObj(v)) { const k = Object.keys(v)[0]; return k === undefined ? [] : [`${x}[["${k}"]]`]; }
    if (Array.isArray(v) && v.length) {
      const first = v[0]!;
      if (isObj(first)) { const k = Object.keys(first).find((key) => typeof first[key] === "number") ?? Object.keys(first)[0]; return [`${x}[[1]]`, ...(k ? [`${x}[[All, "${k}"]]`] : [])]; }
      return [`${x}[[1]]`, `${x}[[1;;3]]`];
    }
  }
  return [];
}

/** What a file is, for an error that it was used as a number. */
function notANumber(x: string, f: FileValue): Error {
  const helpers = helpersFor(f, x);
  const what = `${x} is ${f.origin && "derived" in f.origin ? "" : "a file, "}${anA(mimeLabel(f.mime))}, not a number`;
  return new Error(helpers.length ? `${what}: ${helpers.slice(0, 3).join(", ")} ${helpers.length === 1 ? "turns" : "turn"} it into numbers` : `${what}, and nothing turns ${anA(mimeLabel(f.mime))} into numbers`);
}

const HELPERS = new Set(["samplePoints", "matrix", "dimensions"]);
const SAMPLES_MAX = 5000;

/** The text of one call of a function on a file: a matrix literal, and a note for the cell's echo. */
function callOnFile(fn: string, x: string, f: FileValue, args: string[], scope: FileScope): { text: string; note: string } {
  const what = `${fn}(${[x, ...args].join(", ")})`;
  if (fn === "samplePoints") {
    if (f.mime !== "image/svg+xml") throw new Error(`${what}: samplePoints traces the paths of an SVG; ${x} is ${anA(mimeLabel(f.mime))}`);
    if (args.length > 1) throw new Error(`${what}: samplePoints takes a file and, optionally, how many points`);
    const n = args.length ? Number(args[0]) : 400;
    if (!Number.isInteger(n) || n < 1 || n > SAMPLES_MAX) throw new Error(`${what}: the number of points is a whole number from 1 to ${SAMPLES_MAX}`);
    const { points, paths } = scope.sample(fileText(f), n);
    return {
      text: `[${points.map(([px, py]) => `${px.toFixed(3)}, ${py.toFixed(3)}`).join("; ")}]`,
      note: `${what}: ${points.length} points along ${paths} path${paths === 1 ? "" : "s"}`,
    };
  }
  if (args.length) throw new Error(`${what}: ${fn} takes one table`);
  // a JSON list of records or of lists reads as a table too
  const t = kindOf(f) === "table" ? tableOf(f) : kindOf(f) === "json" ? jsonTable(jsonOf(f)) : null;
  if (!t) throw new Error(`${what}: ${fn} reads a table (CSV, TSV, or JSON that is a list of records); ${x} is ${anA(mimeLabel(f.mime))}`);
  if (!t.rows.length) throw new Error(`${what}: ${x} has no data rows`);
  if (fn === "dimensions") return { text: `[${t.rows.length}, ${t.cols}]`, note: `${what}: ${t.rows.length} rows, ${t.cols} columns` };
  const rows = t.rows.map((_, r) => Array.from({ length: t.cols }, (_, c) => cellNumeral(t, r, c, what)).join(", "));
  return { text: `[${rows.join("; ")}]`, note: `${what}: the ${t.rows.length} × ${t.cols} table` };
}

/** Where a string literal or an attachment reference ends. */
function skipLiteral(src: string, i: number): number {
  const c = src[i];
  if (c === '"' || c === "'") { const j = src.indexOf(c, i + 1); return j < 0 ? src.length : j + 1; }
  if (c === "⟦") { const j = src.indexOf("⟧", i + 1); return j < 0 ? src.length : j + 1; }
  return i;
}
/** The index of the bracket closing the one at `open`, or -1. */
function matching(src: string, open: number): number {
  let depth = 0;
  for (let i = open; i < src.length; i++) {
    const j = skipLiteral(src, i); if (j !== i) { i = j - 1; continue; }
    const c = src[i]!;
    if ("([{".includes(c)) depth++;
    else if (")]}".includes(c) && --depth === 0) return i;
  }
  return -1;
}
/** A call's arguments (or a part's indices), split at the top-level commas. */
export function splitArgs(s: string): string[] {
  const out: string[] = []; let depth = 0, from = 0;
  for (let i = 0; i < s.length; i++) {
    const j = skipLiteral(s, i); if (j !== i) { i = j - 1; continue; }
    const c = s[i]!;
    if ("([{".includes(c)) depth++; else if (")]}".includes(c)) depth--;
    else if (c === "," && depth === 0) { out.push(s.slice(from, i).trim()); from = i + 1; }
  }
  const last = s.slice(from).trim();
  if (last || out.length) out.push(last);
  return out;
}
const isIdentChar = (c: string | undefined) => !!c && /[A-Za-z0-9_]/.test(c);

/** The cell's source with every file expression that is numbers replaced by them (`t[[All, 2]]`),
 *  and every function called on a file by its value (`samplePoints(svg)`), with a note per
 *  replacement for the cell's echo. A file left anywhere else is an error saying what turns it into
 *  numbers. A `let`'s own name and its function's parameters are not references. */
export function resolveFiles(src: string, scope: FileScope): { src: string; notes: string[] } {
  const notes: string[] = [];
  const def = /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(([^)]*)\))?\s*=/.exec(src);
  const shadow = new Set((def?.[2] ?? "").split(",").map((p) => p.trim()).filter(Boolean));
  let out = def ? def[0] : "";
  for (let i = out.length; i < src.length;) {
    if (src[i] === '"' || src[i] === "'") { const j = skipLiteral(src, i); out += src.slice(i, j); i = j; continue; }
    const id = /^[A-Za-z_][A-Za-z0-9_]*/.exec(src.slice(i))?.[0];
    if (id && !isIdentChar(src[i - 1]) && HELPERS.has(id)) {
      let k = i + id.length; while (src[k] === " " || src[k] === "\t") k++;
      const close = src[k] === "(" ? matching(src, k) : -1;
      if (close > 0) {
        const [first = "", ...rest] = splitArgs(src.slice(k + 1, close));
        const fe = fileExprAt(first, 0, scope, shadow);
        if (fe && fe.end === first.length) {
          if (fe.kind === "file") {
            const r = callOnFile(id, fe.x, fe.file, rest, scope);
            out += r.text; notes.push(r.note); i = close + 1; continue;
          }
          if (fe.rest) throw new Error(`${id}(${first}): take the part of the numbers outside the call`);
          if (id === "matrix") { out += fe.text; notes.push(`${fe.x}: ${fe.single ? "a number" : `${fe.rows} × ${fe.cols}`}`); i = close + 1; continue; }
          if (id === "dimensions") { out += fe.single ? "[]" : `[${fe.rows}, ${fe.cols}]`; notes.push(`dimensions(${fe.x})`); i = close + 1; continue; }
          throw new Error(`samplePoints(${first}): samplePoints takes an SVG; ${fe.x} is numbers already`);
        }
        if (id === "samplePoints") throw new Error(`samplePoints(${first}): samplePoints takes a file, an SVG (import("url"), ⟦name⟧, or a name bound to one)`);
      }
    }
    const fe = fileExprAt(src, i, scope, shadow);
    if (fe) {
      if (fe.kind === "file") throw notANumber(fe.x, fe.file);
      out += (fe.rest && !fe.single ? `${fe.text}${fe.rest}` : fe.rest ? `(${fe.text})${fe.rest}` : fe.text);
      notes.push(`${fe.x}: ${fe.single ? fe.text : `${fe.rows} × ${fe.cols}`}`);
      i = fe.end; continue;
    }
    // not a file: copy the token whole (a name that merely starts like one is not cut)
    const e = refEnd(src, i);
    const step = e > i && !src.startsWith("import(", i) ? e - i : 1;
    out += src.slice(i, i + step); i += step;
  }
  return { src: out, notes };
}

// --- What is known inside `[[ ]]`, for completions and signature help ---------------------------

/** Where a caret at the end of `before` is inside a part `x[[…]]`: the expression the part is taken
 *  from (`x`, with any parts before this one), the indices written before the caret, which index the
 *  caret is in, and the word or quoted name being typed there. Null outside a part, and inside a call
 *  or matrix written within one (`t[[f(`), where the indices are not what is being typed. */
export function partContext(before: string): { base: string; specs: string[]; arg: number; typed: { text: string; start: number; quoted: boolean } } | null {
  type Open = { kind: "part" | "(" | "[" | "{"; pos: number };
  const stack: Open[] = [];
  let quote: number | null = null;
  const ends = (k: number) => { let j = k - 1; while (j >= 0 && (before[j] === " " || before[j] === "\t")) j--; return j >= 0 && /[A-Za-z0-9_)\]⟧%]/.test(before[j]!); };
  for (let i = 0; i < before.length; i++) {
    const c = before[i]!;
    if (c === '"' || c === "'") { const j = before.indexOf(c, i + 1); if (j < 0) { quote = i; break; } i = j; continue; }
    if (c === "⟦") { const j = before.indexOf("⟧", i + 1); if (j < 0) return null; i = j; continue; }
    if (c === "[" && before[i + 1] === "[" && ends(i)) { stack.push({ kind: "part", pos: i }); i++; continue; }
    if (c === "(" || c === "[" || c === "{") { stack.push({ kind: c, pos: i }); continue; }
    if (c === "]" && stack[stack.length - 1]?.kind === "part") {
      if (before[i + 1] !== "]") return null;
      stack.pop(); i++; continue;
    }
    if (c === ")" || c === "]" || c === "}") stack.pop();
  }
  // the innermost open part, with nothing but a list's braces open inside it
  let k = stack.length - 1;
  while (k >= 0 && stack[k]!.kind === "{") k--;
  if (k < 0 || stack[k]!.kind !== "part") return null;
  const open = stack[k]!.pos;
  const base = before.slice(exprStart(before, open), open).trim();
  if (!base) return null;
  const specs = splitArgs(before.slice(open + 2));
  if (!specs.length) specs.push("");
  const typed = quote !== null
    ? { text: before.slice(quote + 1), start: quote, quoted: true }
    : (() => { const m = /[A-Za-z_][A-Za-z0-9_]*$/.exec(before); return { text: m?.[0] ?? "", start: before.length - (m?.[0].length ?? 0), quoted: false }; })();
  return { base, specs: specs.slice(0, -1), arg: specs.length - 1, typed };
}

/** Where the expression that ends just before `pos` starts: a reference (a name, `⟦…⟧`, `import(…)`,
 *  `%`) and the parts after it. */
function exprStart(src: string, pos: number): number {
  let j = pos;
  while (j > 0 && (src[j - 1] === " " || src[j - 1] === "\t")) j--;
  // earlier parts: `]]` back to their `[[`
  while (src[j - 1] === "]" && src[j - 2] === "]") {
    let depth = 0, k = j - 1;
    for (; k >= 0; k--) {
      const c = src[k]!;
      if (c === "]" || c === ")" || c === "}") depth++;
      else if ((c === "[" || c === "(" || c === "{") && --depth === 0) break;
    }
    // k is the outer bracket of the `[[`
    if (k <= 0 || src[k + 1] !== "[") return pos;
    j = k;
    while (j > 0 && (src[j - 1] === " " || src[j - 1] === "\t")) j--;
  }
  const head = src.slice(0, j);
  const m = /(⟦[^⟧]+⟧|import\(\s*(["'])[^"']*\2\s*\)|%(%*|\d+)|[A-Za-z_][A-Za-z0-9_]*)$/.exec(head);
  return m ? j - m[0].length : pos;
}

/** What a file expression is, as a whole: a file (or a part of one), the shape of the numbers a part
 *  selected, or null when the text is not a file expression. Errors say nothing here (null). */
export function fileExprValue(text: string, scope: FileScope): { kind: "file"; file: FileValue } | { kind: "numbers"; rows: number; cols: number; single: boolean } | null {
  try {
    const t = text.trim();
    const fe = fileExprAt(t, 0, scope, new Set());
    if (!fe || fe.end !== t.length) return null;
    if (fe.kind === "file") return { kind: "file", file: fe.file };
    return fe.rest ? null : { kind: "numbers", rows: fe.rows, cols: fe.cols, single: fe.single };
  } catch { return null; }
}

/** What can go in index `arg` of a part of `value`, given the indices before it: the indices' names
 *  for the signature (`row, column`), a line saying what is in range, and the names that can be typed
 *  there (a table's columns, an object's keys). */
export function partHelp(value: { kind: "file"; file: FileValue } | { kind: "numbers"; rows: number; cols: number; single: boolean }, specs: string[], arg: number): { params: string[]; blurb: string; names: string[]; namesAre?: "column" | "key" } | null {
  const range = (n: number, what: string) => `${what} 1…${n} (or -${n}…-1), All, a;;b, {i, j}`;
  if (value.kind === "numbers") {
    if (value.single) return null;
    if (value.rows === 1 || value.cols === 1) {
      const n = Math.max(value.rows, value.cols);
      return { params: ["entry"], blurb: `A ${value.rows === 1 ? "row" : "column"} vector of ${n}: ${range(n, "entries")}.`, names: [] };
    }
    return { params: ["row", "column"], blurb: arg === 0 ? `A ${value.rows}×${value.cols} matrix: ${range(value.rows, "rows")}.` : `A ${value.rows}×${value.cols} matrix: ${range(value.cols, "columns")}.`, names: [] };
  }
  const f = value.file;
  const kind = kindOf(f);
  if (kind === "table") {
    const t = tableOf(f);
    const cols = t.header ? t.header.map((h) => `"${h}"`) : [];
    const colLine = `${range(t.cols, "columns")}${t.header ? `, or by name: ${cols.join(", ")}` : ""}`;
    if (arg === 0) return { params: ["row", "column"], blurb: `${t.rows.length} rows: ${range(t.rows.length, "rows")}. A name alone picks a column.`, names: t.header ?? [], namesAre: "column" };
    if (arg === 1) return { params: ["row", "column"], blurb: `${t.cols} columns: ${colLine}.`, names: t.header ?? [], namesAre: "column" };
    return { params: ["row", "column"], blurb: "A table has two dimensions, rows and columns.", names: [] };
  }
  if (kind === "json") {
    // the level the caret's index applies to: the earlier indices taken, a list's first element
    // standing for all of them after All, a span or a list
    let v: Json;
    try {
      v = jsonOf(f);
      for (const sp of specs) {
        const s = parseSpec(sp);
        if (Array.isArray(v)) { const { is } = partSpec(v.length, s); v = v[is[0]!]!; }
        else if (isObj(v)) { const keys = Object.keys(v); const { is } = partSpec(keys.length, s, (n) => { const k = keys.indexOf(n); if (k < 0) throw new Error(n); return k; }); v = v[keys[is[0]!]!]!; }
        else return null;
      }
    } catch { return null; }
    const params = [...specs.map((_, i) => `i${i + 1}`), "…"];
    params[arg] = Array.isArray(v) ? "position" : isObj(v) ? "key" : "…";
    if (Array.isArray(v)) return { params, blurb: `A list of ${v.length}: ${range(v.length, "positions")}.`, names: [] };
    if (isObj(v)) { const keys = Object.keys(v); return { params, blurb: `An object with ${keys.length} key${keys.length === 1 ? "" : "s"}: ${keys.slice(0, 12).map((k) => `"${k}"`).join(", ")}${keys.length > 12 ? ", …" : ""}.`, names: keys, namesAre: "key" }; }
    return { params, blurb: `${JSON.stringify(v).slice(0, 40)} is ${jsonKind(v)}, which has no parts.`, names: [] };
  }
  return null;
}

// --- SVG paths to points (in the page) -----------------------------------------------------------

/** About `n` points along an SVG's paths at equal arc lengths (the article's `getPointAtLength`
 *  loop), centred, y flipped (SVG's grows downward) and scaled so the larger extent is [-1, 1]. */
export function svgPoints(xml: string, n: number): { points: [number, number][]; paths: number } {
  const doc = new DOMParser().parseFromString(xml, "image/svg+xml");
  const paths = Array.from(doc.querySelectorAll("path"));
  if (!paths.length) throw new Error("the SVG has no <path> elements (shapes, text and images are not traced)");
  // measure in a hidden host SVG so getTotalLength works
  const NS = "http://www.w3.org/2000/svg";
  const host = document.createElementNS(NS, "svg"); host.setAttribute("width", "0"); host.setAttribute("height", "0"); host.style.position = "absolute";
  document.body.append(host);
  const copies = paths.map((p) => { const c = document.createElementNS(NS, "path"); c.setAttribute("d", p.getAttribute("d") ?? ""); host.append(c); return c; });
  const total = copies.reduce((a, c) => a + c.getTotalLength(), 0);
  const pts: [number, number][] = [];
  for (const c of copies) {
    const len = c.getTotalLength(), k = Math.max(1, Math.round((n * len) / (total || 1)));
    for (let i = 0; i < k; i++) { const q = c.getPointAtLength((len * i) / k); pts.push([q.x, q.y]); }
  }
  host.remove();
  const xs = pts.map((p) => p[0]), ys = pts.map((p) => p[1]);
  const cx = (Math.min(...xs) + Math.max(...xs)) / 2, cy = (Math.min(...ys) + Math.max(...ys)) / 2;
  const ext = Math.max(Math.max(...xs) - Math.min(...xs), Math.max(...ys) - Math.min(...ys)) / 2 || 1;
  return { points: pts.map(([x, y]) => [(x - cx) / ext, -(y - cy) / ext]), paths: paths.length };
}
