/**
 * Files as values: what `import("url")` and `⟦name⟧` stand for in a math cell.
 *
 * A file is kept as it came: its name, its media type and its contents (text, or base64 for
 * binary). A cell whose value is a file shows it by what it is (an image as the image, a CSV or TSV
 * as a table, JSON and other text as text, anything else as a card naming it), and `let x = …` binds
 * the name to the file. Nothing is converted on the way in.
 *
 * The engine deals only in numbers and never sees a file. A function called on a file is how it
 * becomes numbers, and the notebook evaluates that call before the cell is sent:
 * `samplePoints(svg)` is the points along an SVG's paths, `matrix(csv)` a table's numbers,
 * `column(csv, "x")` and `row(csv, k)` one column or row, `dimensions(csv)` its size. A file anywhere
 * else in a math cell is an error that names the functions that apply to it.
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
  /** Where it came from: an attachment by name, or a URL. */
  origin: { asset: string } | { url: string };
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

/** A column chosen by number (from 1) or by its header. */
function columnIndex(t: Table, arg: string, what: string): number {
  const s = /^"([^"]*)"$|^'([^']*)'$/.exec(arg);
  if (s) {
    const name = s[1] ?? s[2]!;
    let c = t.header?.indexOf(name) ?? -1;
    if (c < 0) c = t.header?.findIndex((h) => h.toLowerCase() === name.toLowerCase()) ?? -1;
    if (c < 0) throw new Error(t.header ? `${what}: there is no column "${name}" (the columns are ${t.header.map((h) => `"${h}"`).join(", ")})` : `${what}: the table has no header row; give the column's number, 1 to ${t.cols}`);
    return c;
  }
  const k = Number(arg);
  if (!Number.isInteger(k) || k < 1 || k > t.cols) throw new Error(`${what}: the column is a number from 1 to ${t.cols}${t.header ? ", or a name in quotes" : ""}`);
  return k - 1;
}

// --- Functions on files -------------------------------------------------------------------------

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

/** The URLs a cell imports, to fetch before it is read. */
export function importsIn(src: string): string[] {
  return [...src.matchAll(/\bimport\(\s*(["'])([^"']*)\1\s*\)/g)].map((m) => m[2]!);
}

/** A cell whose value is a file: `import("url")`, `⟦name⟧`, a name bound to a file or an output
 *  that is one (`%`), optionally bound with `let x = …`. */
export function fileCellOf(src: string, scope: FileScope): { bind?: string; file: FileValue } | null {
  const m = /^\s*(?:let\s+([A-Za-z_][A-Za-z0-9_]*)\s*=)?\s*([\s\S]*?)\s*$/.exec(src)!;
  const ref = parseFileRef(m[2]!);
  if (!ref) return null;
  const file = scope.lookup(ref);
  if (!file) return null;
  return m[1] ? { bind: m[1], file } : { file };
}

/** The functions that apply to a kind of file, for captions and errors. */
export function helpersFor(kind: FileKind, mime: string, x: string): string[] {
  if (mime === "image/svg+xml") return [`samplePoints(${x})`, `samplePoints(${x}, n)`];
  if (kind === "table") return [`matrix(${x})`, `column(${x}, k)`, `row(${x}, k)`, `dimensions(${x})`];
  return [];
}

/** How a file reference reads in a message: the name it was written as. */
const refText = (ref: FileRef, f: FileValue) => ref.kind === "name" ? ref.name : ref.kind === "out" ? ref.text : f.name;

/** What a file is, for an error that it was used as a number. */
function notANumber(x: string, f: FileValue): Error {
  const helpers = helpersFor(kindOf(f), f.mime, x);
  const what = `${x} is a file (${mimeLabel(f.mime)}), not a number`;
  return new Error(helpers.length ? `${what}: ${helpers.join(", ")} ${helpers.length === 1 ? "turns" : "turn"} it into numbers` : `${what}, and nothing turns ${mimeLabel(f.mime)} into numbers yet`);
}

const HELPERS = new Set(["samplePoints", "matrix", "column", "row", "dimensions"]);
const SAMPLES_MAX = 5000;

/** The text of one call of a function on a file: a matrix literal, and a note for the cell's echo. */
function callOnFile(fn: string, x: string, f: FileValue, args: string[], scope: FileScope): { text: string; note: string } {
  const what = `${fn}(${[x, ...args].join(", ")})`;
  if (fn === "samplePoints") {
    if (f.mime !== "image/svg+xml") throw new Error(`${what}: samplePoints traces the paths of an SVG; ${x} is ${/^[aeiou]/i.test(mimeLabel(f.mime)) ? "an" : "a"} ${mimeLabel(f.mime)}`);
    if (args.length > 1) throw new Error(`${what}: samplePoints takes a file and, optionally, how many points`);
    const n = args.length ? Number(args[0]) : 400;
    if (!Number.isInteger(n) || n < 1 || n > SAMPLES_MAX) throw new Error(`${what}: the number of points is a whole number from 1 to ${SAMPLES_MAX}`);
    const { points, paths } = scope.sample(fileText(f), n);
    return {
      text: `[${points.map(([px, py]) => `${px.toFixed(3)}, ${py.toFixed(3)}`).join("; ")}]`,
      note: `${what}: ${points.length} points along ${paths} path${paths === 1 ? "" : "s"}`,
    };
  }
  if (kindOf(f) !== "table") throw new Error(`${what}: ${fn} reads a table (CSV or TSV); ${x} is ${/^[aeiou]/i.test(mimeLabel(f.mime)) ? "an" : "a"} ${mimeLabel(f.mime)}`);
  const t = tableOf(f);
  if (!t.rows.length) throw new Error(`${what}: ${x} has no data rows`);
  const arity = fn === "column" || fn === "row" ? 1 : 0;
  if (args.length !== arity) throw new Error(`${what}: ${fn} takes ${arity ? `a file and a ${fn === "column" ? "column (a number from 1, or a name in quotes)" : "row number (from 1)"}` : "one file"}`);
  if (fn === "dimensions") return { text: `[${t.rows.length}, ${t.cols}]`, note: `${what}: ${t.rows.length} rows, ${t.cols} columns` };
  if (fn === "matrix") {
    const rows = t.rows.map((_, r) => Array.from({ length: t.cols }, (_, c) => cellNumeral(t, r, c, what)).join(", "));
    return { text: `[${rows.join("; ")}]`, note: `${what}: the ${t.rows.length} × ${t.cols} table` };
  }
  if (fn === "column") {
    const c = columnIndex(t, args[0]!, what);
    return { text: `[${t.rows.map((_, r) => cellNumeral(t, r, c, what)).join("; ")}]`, note: `${what}: column ${colName(t, c)}, ${t.rows.length} values` };
  }
  const k = Number(args[0]);
  if (!Number.isInteger(k) || k < 1 || k > t.rows.length) throw new Error(`${what}: the row is a number from 1 to ${t.rows.length}`);
  return { text: `[${Array.from({ length: t.cols }, (_, c) => cellNumeral(t, k - 1, c, what)).join(", ")}]`, note: `${what}: row ${k} of ${t.rows.length}` };
}

/** Where a string literal, an attachment reference or a call's parentheses end. */
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
/** A call's arguments, split at its top-level commas. */
function splitArgs(s: string): string[] {
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

/** The cell's source with every function called on a file replaced by its value, and a note per
 *  call for the cell's echo. A file left anywhere else is an error saying what turns it into numbers. */
export function resolveFiles(src: string, scope: FileScope): { src: string; notes: string[] } {
  const notes: string[] = [];
  let out = "";
  for (let i = 0; i < src.length;) {
    const j = skipLiteral(src, i);
    if (j !== i) { out += src.slice(i, j); i = j; continue; }
    const id = /^[A-Za-z_][A-Za-z0-9_]*/.exec(src.slice(i))?.[0];
    if (id && !isIdentChar(src[i - 1])) {
      let k = i + id.length; while (src[k] === " " || src[k] === "\t") k++;
      if (HELPERS.has(id) && src[k] === "(") {
        const close = matching(src, k);
        if (close > 0) {
          const [first = "", ...rest] = splitArgs(src.slice(k + 1, close));
          const ref = parseFileRef(first);
          const f = ref && scope.lookup(ref);
          if (f) {
            const r = callOnFile(id, refText(ref, f), f, rest, scope);
            out += r.text; notes.push(r.note); i = close + 1; continue;
          }
          if (id === "samplePoints") throw new Error(`samplePoints(${first}): samplePoints takes a file, an SVG (import("url"), ⟦name⟧, or a name bound to one)`);
        }
      }
      out += id; i += id.length; continue;
    }
    out += src[i]; i++;
  }
  assertNoFiles(out, scope);
  return { src: out, notes };
}

/** Throw if a file is left in a cell's source: as an attachment, an import, a name or an output. A
 *  `let`'s own name and its function's parameters are not references. */
function assertNoFiles(src: string, scope: FileScope) {
  const def = /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(([^)]*)\))?\s*=/.exec(src);
  const params = new Set((def?.[2] ?? "").split(",").map((p) => p.trim()).filter(Boolean));
  const body = def ? src.slice(def[0].length) : src;
  for (const m of body.matchAll(/⟦([^⟧]+)⟧/g)) {
    const f = scope.lookup({ kind: "asset", name: m[1]! });
    if (f) throw notANumber(m[0], f);
  }
  for (const m of body.matchAll(/\bimport\(\s*(["'])([^"']*)\1\s*\)/g)) {
    const f = scope.lookup({ kind: "url", url: m[2]! });
    if (f) throw notANumber(`import("${m[2]}")`, f);
  }
  // names and outputs outside string literals and attachments
  const bare = body.replace(/"[^"]*"|'[^']*'|⟦[^⟧]*⟧/g, (s) => " ".repeat(s.length));
  for (const m of bare.matchAll(/%(%*|\d+)|[A-Za-z_][A-Za-z0-9_]*/g)) {
    if (!m[0].startsWith("%") && (isIdentChar(bare[m.index! - 1]) || params.has(m[0]))) continue;
    const f = scope.lookup(m[0].startsWith("%") ? { kind: "out", text: m[0] } : { kind: "name", name: m[0] });
    if (f) throw notANumber(m[0], f);
  }
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
