/**
 * A `?` question, answered in the engine's own syntax: a number, a list, a table (a matrix), or a
 * formula.
 *
 * The model is small and runs on the reader's machine. It knows the volume of a prism and the speed
 * of light better than it could find them, so the plan it makes first says whether the answer is
 * standard knowledge; if it is, the model answers from what it knows, nothing leaves the machine,
 * the answer says where it came from, and the notebook offers to check it with a search.
 *
 * Data that changes, or is too specific to remember (a season's statistics), is searched for, and
 * there the model is never trusted with a number it would have to remember or copy. Held to a JSON
 * schema, it picks, from previews of the tables the searches found, a table, its columns and a range
 * of rows; when no table fits, it lifts values out of passages, quoting each row; and for a formula
 * it translates one the page states (as LaTeX) into the engine's syntax. The numbers themselves are
 * copied from the page by this code, or checked against the quoted page text, and a formula is shown
 * next to the LaTeX it came from. The model's memory is the last resort, and an answer from it is
 * marked as unsourced throughout.
 */
import { leadingNumber, numberText, numbersIn, numeric, parseNumber } from "./numbers.js";
import { readHit, type Fetch, type Hit, type Page, type Source } from "./sources.js";
import type { Table } from "./html.js";

/** A language model held to a JSON schema. The notebook supplies one (Chrome's built-in model, or a
 *  WebGPU model); tests supply a scripted one. */
export interface Model {
  /** Names the model in the result ("Gemini Nano (Chrome)", "Qwen3-4B"). */
  id: string;
  /** The model's reply to `user` under `system`: JSON text meeting `schema`. */
  complete(req: { system: string; user: string; schema: object; signal?: AbortSignal | undefined }): Promise<string>;
}

export interface AskOptions {
  model: Model;
  sources: Source[];
  fetch: Fetch;
  /** A page reader for sites that refuse cross-origin reads (see `readHit`). */
  reader?: string | undefined;
  /** Let the model answer from its own knowledge: at once when the plan says the answer is standard
   *  knowledge, and as a last resort (flagged) when the sources give nothing. On by default. */
  useKnowledge?: boolean;
  /** Search even when the model says it knows the answer ("Check with a search"). */
  forceSearch?: boolean;
  /** Asked just before the first request leaves the machine; false means no search (the reader
   *  declined). A lookup answered from knowledge never asks. */
  beforeSearch?: () => Promise<boolean>;
  /** YYYY-MM-DD: "the last 20 years" needs it. */
  today: string;
  /** How many search results are read. */
  maxPages?: number;
  onProgress?: (line: string) => void;
  signal?: AbortSignal;
}

/** What the answer is: one number, a list of numbers, a table of numbers, or a formula. */
export type Shape = "number" | "list" | "table" | "formula";
/** Where the answer came from: copied out of a table, lifted from quoted prose (or a quoted formula),
 *  the model's knowledge (standard knowledge it was asked for directly), or its memory (a last resort
 *  after the sources gave nothing). */
export type Via = "table" | "text" | "knowledge" | "memory";

export interface AskResult {
  question: string;
  shape: Shape;
  /** The answer in the engine's syntax: `42`, `[1, 2, 3]`, `[a, b; c, d]`, or an expression `B*h`. */
  source: string;
  /** A formula's variables, in order: `let V = ?…` defines `V(B, h)`. */
  params?: string[];
  /** What a formula's variables mean. */
  vars?: { name: string; meaning: string }[];
  /** The formula as the page writes it (LaTeX), to compare with `source`. */
  latex?: string;
  /** What each column is (numbers). */
  columns: string[];
  /** What each row is (a team, a country), when the source names rows with text; the matrix cannot hold text. */
  rowLabels?: string[];
  /** What a row is, in words ("one MLB season"). */
  rowsAre: string;
  via: Via;
  /** The pages the answer came from. */
  cites: { title: string; url: string }[];
  /** Values not confirmed by a source, as [row, column] of the grid (for a formula, [0, 0] when the
   *  formula was not found in the page). Everything, when `via` is "memory"; nothing when it is
   *  "knowledge", whose label already says no source was consulted. */
  flagged: [number, number][];
  /** Rows left out, and why, and anything else the reader should know. */
  notes: string[];
  /** The searches run and the pages read, for "How this was found". */
  trail: string[];
  model: string;
  /** When it was looked up (YYYY-MM-DD). */
  at: string;
}

export class AskError extends Error {
  constructor(message: string, readonly trail: string[] = []) { super(message); }
}

// ---------------------------------------------------------------------------------------------
// Prompts and schemas. Short, because a browser model's context is ~4k tokens.
// ---------------------------------------------------------------------------------------------

const SHAPES = ["number", "list", "table", "formula"] as const;

const PLAN_SCHEMA = {
  type: "object",
  properties: {
    shape: { type: "string", enum: SHAPES },
    known: { type: "boolean" },
    searches: { type: "array", items: { type: "string" }, minItems: 1, maxItems: 3 },
    columns: { type: "array", items: { type: "string" }, minItems: 1, maxItems: 8 },
    rows: { type: "string" },
    keywords: { type: "array", items: { type: "string" }, maxItems: 12 },
  },
  required: ["shape", "known", "searches", "columns", "rows", "keywords"],
} as const;

const PLAN_SYSTEM = `You plan how to look up an answer for a math notebook. Reply with JSON only:
- shape: "number" for one value (the speed of light), "list" for several values of one kind (the first ten primes), "table" for rows of several values (runs and home runs per season), "formula" for an equation or expression (the volume of a prism).
- known: true if the answer is standard knowledge you are sure of and that does not change: a textbook formula, a physical or mathematical constant, a definition, a well-known fixed fact. false for statistics, records, prices, populations, anything recent, or anything you would have to look up to be exact.
- searches: 1 to 3 short search-engine queries likely to find a page stating this (name the subject, not the math).
- columns: for numbers, what each column holds, in order, e.g. ["season", "runs per game", "home runs per game"], the row key (like a year) first; for a formula, the quantity it gives, e.g. ["volume"].
- rows: what one row is, e.g. "one MLB season, 2006 to 2025", or "" for one value or a formula.
- keywords: words and abbreviations the page might use, e.g. ["year", "R/G", "HR", "runs", "home runs"] or ["prism", "volume", "base area", "height"].`;

const PICK_SCHEMA = {
  type: "object",
  properties: {
    table: { type: "integer" },
    columns: { type: "array", items: { type: "integer" } },
    label: { type: "integer" },
    filter: {
      type: "object",
      properties: { column: { type: "integer" }, min: { type: ["number", "null"] }, max: { type: ["number", "null"] } },
      required: ["column", "min", "max"],
    },
  },
  required: ["table", "columns", "label", "filter"],
} as const;

const PICK_SYSTEM = `You choose which table answers a question. Each table is shown with its numbered columns and its first and last rows.
Reply with JSON only:
- table: the number of the table that best answers the question, or -1 if none has the data.
- columns: column numbers from that table, one for each column the answer needs, in the answer's order. Use only columns that hold numbers.
- label: the number of a text column that names each row (like a team or country) when rows are not keyed by a number, else -1.
- filter: which rows to keep: column is a number column to filter on (like the year), or -1 to keep all rows; min and max bound it (null for no bound). For "the last 20 years" in 2026 that is min 2006, max 2025.`;

const EXTRACT_SCHEMA = {
  type: "object",
  properties: {
    rows: {
      type: "array", maxItems: 60,
      items: {
        type: "object",
        properties: { label: { type: "string" }, values: { type: "array", items: { type: "number" } }, quote: { type: "string" } },
        required: ["label", "values", "quote"],
      },
    },
  },
  required: ["rows"],
} as const;

const EXTRACT_SYSTEM = `You copy numbers out of passages to answer a question. Use only numbers written in the passages; never compute or remember one.
Reply with JSON only: rows, each with label (what the row is), values (one number per answer column, in order) and quote (the exact sentence from a passage that states those numbers).
If the passages do not state the numbers, reply {"rows": []}.`;

const MEMORY_SCHEMA = {
  type: "object",
  properties: {
    rows: { type: "array", maxItems: 60, items: { type: "object", properties: { label: { type: "string" }, values: { type: "array", items: { type: "number" } } }, required: ["label", "values"] } },
  },
  required: ["rows"],
} as const;

const MEMORY_SYSTEM = `Answer a question from what you know, as rows of numbers, one number per answer column, in order (one row with one value for a single number).
If you do not know, reply {"rows": []}. Do not invent precision you do not have.`;

const SYNTAX = `Write the expression in this syntax: + - * / ^ and parentheses; write every product with * (B*h, not Bh); sqrt(x), sin, cos, tan, exp, ln, log, abs; pi for π; decimal numbers.
Variables are letters or words (r, h, base_area); use the page's own letters. The expression is only the right-hand side: no "=" and no name on the left.`;

const FORMULA_SCHEMA = {
  type: "object",
  properties: {
    found: { type: "boolean" },
    expr: { type: "string" },
    params: { type: "array", items: { type: "string" }, maxItems: 8 },
    vars: { type: "array", maxItems: 8, items: { type: "object", properties: { name: { type: "string" }, meaning: { type: "string" } }, required: ["name", "meaning"] } },
    quote: { type: "string" },
  },
  required: ["found", "expr", "params", "vars", "quote"],
} as const;

const FORMULA_SYSTEM = `You find the formula that answers a question in passages where formulas are written in LaTeX between $ signs.
Reply with JSON only:
- found: false if no passage states the formula (then leave the rest empty).
- quote: the formula's LaTeX exactly as written between the $ signs in the passage you used.
- expr: that formula's right-hand side. ${SYNTAX}
- params: the variables of expr, in a natural order, e.g. ["B", "h"].
- vars: what each variable means, from the passage, e.g. [{"name": "B", "meaning": "area of the base"}].`;

const FORMULA_MEMORY_SYSTEM = `Give the standard formula that answers the question, from what you know. Reply with JSON only:
- found: false if you do not know it.
- expr: the formula's right-hand side. ${SYNTAX}
- params: the variables of expr, in a natural order.
- vars: what each variable means.
- quote: the formula in LaTeX, e.g. "V = Bh".`;

// ---------------------------------------------------------------------------------------------

interface Plan { shape: Shape; known: boolean; searches: string[]; columns: string[]; rows: string; keywords: string[] }
interface Found { table: Table; page: Page }

/** The first JSON object in a model's reply (a model may wrap it in prose or a code fence). */
export function parseJson<T>(text: string): T | null {
  const s = text.indexOf("{"), e = text.lastIndexOf("}");
  if (s < 0 || e < s) return null;
  try { return JSON.parse(text.slice(s, e + 1)) as T; } catch { return null; }
}

const words = (s: string) => s.toLowerCase().split(/[^a-z0-9%/]+/).filter((w) => w.length > 1 && !STOP.has(w));
const STOP = new Set(["the", "of", "and", "in", "for", "per", "by", "to", "a", "an", "on", "at", "last", "each", "number", "what", "how", "many", "is", "are", "was", "were", "average", "total", "data", "table", "list", "over", "years", "year", "formula", "equation"]);

/** How well a table might answer: header and caption words that match the plan, numeric columns, and rows. */
export function scoreTable(t: Table, plan: Pick<Plan, "keywords" | "columns">, pageRank: number): number {
  const want = new Set([...plan.keywords.flatMap((k) => [k.toLowerCase(), ...words(k)]), ...plan.columns.flatMap(words)]);
  const head = [t.caption, ...t.headers].join(" ");
  const hw = new Set([...words(head), ...t.headers.map((h) => h.toLowerCase().trim())]);
  let hits = 0;
  for (const w of want) if (hw.has(w)) hits++;
  const numCols = t.headers.filter((_, c) => numericColumn(t, c)).length;
  return hits * 3 + Math.min(numCols, plan.columns.length) * 2 + Math.log2(1 + t.rows.length) - pageRank * 0.5;
}

/** Whether most of a column's cells are numbers. */
function numericColumn(t: Table, c: number): boolean {
  let n = 0, filled = 0;
  for (const r of t.rows) { const s = r[c] ?? ""; if (!s) continue; filled++; if (numeric(s) || leadingNumber(s) !== null) n++; }
  return filled > 0 && n / filled >= 0.6;
}

const cut = (s: string, n: number) => s.length > n ? `${s.slice(0, n - 1)}…` : s;

/** A table as the model sees it: numbered columns, then the first and last rows. */
export function preview(t: Table, i: number, page: Page): string {
  const cols = t.headers.map((h, c) => `${c}: ${cut(h || "(no name)", 28)}${numericColumn(t, c) ? "" : " [text]"}`).slice(0, 14);
  const row = (r: string[]) => `  | ${r.slice(0, 14).map((s) => cut(s, 16)).join(" | ")}`;
  const rows = t.rows.length <= 6 ? t.rows.map(row) : [...t.rows.slice(0, 3).map(row), `  … ${t.rows.length - 6} more rows …`, ...t.rows.slice(-3).map(row)];
  return [`Table ${i}, from "${cut(page.title, 60)}"${t.caption ? `, "${cut(t.caption, 60)}"` : ""}, ${t.rows.length} rows`,
    `  columns: ${cols.join("; ")}${t.headers.length > 14 ? `; … (${t.headers.length} in all)` : ""}`, ...rows].join("\n");
}

/** Build the answer from a chosen table: the chosen columns of the rows the filter keeps, each value
 *  read from the cell's own text. A row with a value that is not a number is left out, and said. */
export function fromTable(t: Table, pick: { columns: number[]; label: number; filter: { column: number; min: number | null; max: number | null } }):
  { rows: string[][]; labels: string[]; skipped: number } {
  const rows: string[][] = [];
  const labels: string[] = [];
  let skipped = 0;
  const f = pick.filter;
  for (const r of t.rows) {
    if (f.column >= 0) {
      const k = leadingNumber(r[f.column] ?? "");
      if (k === null || (f.min !== null && k < f.min) || (f.max !== null && k > f.max)) continue;
    }
    // a key column like a season "2005–06" is read by its leading number; values must be one number
    const vals = pick.columns.map((c) => c === f.column ? (parseNumber(r[c] ?? "") ?? numberText(leadingNumber(r[c] ?? "") ?? NaN)) : parseNumber(r[c] ?? ""));
    if (vals.some((v) => v === null)) { skipped++; continue; }
    rows.push(vals as string[]);
    if (pick.label >= 0) labels.push(r[pick.label] ?? "");
  }
  return { rows, labels, skipped };
}

/** The engine's text for a grid of numbers in the answer's shape: one number alone; a list as a row
 *  `[a, b, c]` (a single column read down the page is laid across); else a matrix. */
export function engineText(rows: string[][], shape: Shape = "table"): string {
  if (rows.length === 1 && rows[0]!.length === 1) return rows[0]![0]!;
  const grid = shape === "list" && rows.every((r) => r.length === 1) ? [rows.map((r) => r[0]!)] : rows;
  return `[${grid.map((r) => r.join(", ")).join("; ")}]`;
}

/** Where a grid's [row, column] went in `engineText`'s layout. */
const placed = (shape: Shape, rows: string[][]) => (rc: [number, number]): [number, number] =>
  shape === "list" && rows.length > 1 && rows.every((r) => r.length === 1) ? [0, rc[0]] : rc;

const norm = (s: string) => s.toLowerCase().replace(/[\s ]+/g, " ").replace(/[“”]/g, "\"").replace(/[‘’]/g, "'").trim();
const squash = (s: string) => s.replace(/\s+/g, "");

/** Passages likely to answer: paragraphs (and, for formulas, table rows) with the plan's words and
 *  digits, or formulas. */
function passages(pages: Page[], plan: Plan, formulas: boolean, budget = 2400): string[] {
  const want = new Set([...plan.keywords.flatMap(words), ...plan.columns.flatMap(words)]);
  const scored: { s: string; score: number }[] = [];
  pages.forEach((p, pi) => {
    const paras = p.text.split("\n");
    if (formulas) for (const t of p.tables) for (const r of t.rows) if (r.some((c) => c.includes("$"))) paras.push(r.map((c, i) => t.headers[i] ? `${t.headers[i]}: ${c}` : c).join("; "));
    for (const para of paras) {
      const marks = formulas ? (para.match(/\$[^$]+\$/g) ?? []).length : (para.match(/\d+/g) ?? []).length;
      if (!marks || para.length < (formulas ? 8 : 30)) continue;
      const hits = words(para).filter((w) => want.has(w)).length;
      if (!hits) continue;
      scored.push({ s: cut(para, 600), score: hits * 2 + Math.min(marks, 6) - pi });
    }
  });
  scored.sort((a, b) => b.score - a.score);
  const out: string[] = [];
  let used = 0;
  for (const { s } of scored) { if (used + s.length > budget) continue; out.push(s); used += s.length; if (out.length >= 8) break; }
  return out;
}

/** Names the engine reads as functions or constants, never a formula's variables. */
const RESERVED = new Set(["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "pi", "e", "i", "conj", "re", "im", "let"]);

/** A model's formula, checked to be an expression in the engine's syntax: its variables, and the
 *  expression, or null. A left-hand side (`V = B*h`) is dropped. */
export function checkFormula(expr: string, params: string[]): { expr: string; params: string[] } | null {
  let e = expr.replace(/π/g, "pi").replace(/·|×/g, "*").replace(/−/g, "-").trim();
  if (e.includes("=")) e = e.slice(e.lastIndexOf("=") + 1).trim();
  if (!e || !/^[A-Za-z0-9_+\-*/^().,\s]+$/.test(e)) return null;
  let depth = 0;
  for (const c of e) { if (c === "(") depth++; else if (c === ")" && --depth < 0) return null; }
  if (depth) return null;
  const ids = [...new Set((e.match(/[A-Za-z_][A-Za-z0-9_]*/g) ?? []).filter((n) => !RESERVED.has(n)))];
  const ok = params.filter((p) => ids.includes(p));
  return { expr: e, params: [...ok, ...ids.filter((n) => !ok.includes(n))] };
}

async function ask(model: Model, system: string, user: string, schema: object, signal?: AbortSignal): Promise<string> {
  if (signal?.aborted) throw new AskError("Stopped.");
  try { return await model.complete({ system, user, schema, signal }); } catch (e) {
    // a model stopped mid-answer throws its own abort error
    if (signal?.aborted) throw new AskError("Stopped.");
    throw e;
  }
}

const plural = (n: number, one: string, many = `${one}s`) => `${n} ${n === 1 ? one : many}`;

export async function lookup(question: string, o: AskOptions): Promise<AskResult> {
  const trail: string[] = [];
  const say = (line: string) => { o.onProgress?.(line); };
  const q = question.trim();

  // 1. the plan
  say("Planning the search");
  const plan0 = parseJson<Partial<Plan>>(await ask(o.model, PLAN_SYSTEM, `Today is ${o.today}.\nQuestion: ${q}`, PLAN_SCHEMA, o.signal));
  const plan: Plan = {
    shape: SHAPES.includes(plan0?.shape as Shape) ? plan0!.shape as Shape : "table",
    known: plan0?.known === true,
    searches: (plan0?.searches ?? []).filter((s) => typeof s === "string" && s.trim()).slice(0, 3),
    columns: (plan0?.columns ?? []).filter((s) => typeof s === "string" && s.trim()),
    rows: typeof plan0?.rows === "string" ? plan0.rows : "",
    keywords: (plan0?.keywords ?? []).filter((s) => typeof s === "string"),
  };
  if (!plan.searches.length) plan.searches = [q];
  if (!plan.columns.length) plan.columns = ["value"];
  trail.push(plan.shape === "formula" ? `Looking for a formula for ${plan.columns[0]}` : `Looking for ${plan.shape === "number" ? "a number" : plan.shape === "list" ? "a list" : "a table"}: ${plan.columns.join(", ")}${plan.rows ? `; a row is ${plan.rows}` : ""}`);
  const base = { question: q, shape: plan.shape, model: o.model.id, at: o.today, rowsAre: plan.rows };

  const knowledge = o.useKnowledge !== false;
  // standard knowledge: the model answers, and nothing is sent anywhere
  if (plan.known && knowledge && !o.forceSearch) {
    const r = await fromKnowledge(q, plan, o, trail, say, false);
    if (r) return { ...base, ...r, trail };
    trail.push("The model did not answer from its knowledge after all: searching.");
  }
  const none = !o.sources.length;
  if (none || (o.beforeSearch && !(await o.beforeSearch()))) {
    trail.push(none ? "No search source is turned on." : "Searching was declined.");
    const r = knowledge && !plan.known ? await fromKnowledge(q, plan, o, trail, say, true) : null;
    if (r) return { ...base, ...r, trail };
    throw new AskError(`${none ? "No search source is turned on" : "Searching was declined"}, and the model does not know the answer.`, trail);
  }
  const { hits, pages } = await gather(plan, o, trail, say);
  const r = plan.shape === "formula" ? await formula(q, plan, pages, o, trail, say) : await numbers(q, plan, pages, o, trail, say);
  if (r) return { ...base, ...r, trail };
  // the last resort: the model's memory, marked as unsourced (a question it called standard
  // knowledge has already been answered, or declined, above; a forced search reports what it found)
  const m = knowledge && (!plan.known || o.forceSearch) ? await fromKnowledge(q, plan, o, trail, say, true) : null;
  if (m) return { ...base, ...m, trail };
  throw new AskError(pages.length ? `The pages found did not have ${plan.shape === "formula" ? "this formula" : "these numbers"}.`
    : hits.length ? "None of the pages found could be read from here." : "The search found nothing.", trail);
}

/** The model's own answer: `fallback` when the sources gave nothing (every value flagged), else
 *  standard knowledge it was asked for directly. */
async function fromKnowledge(q: string, plan: Plan, o: AskOptions, trail: string[], say: Say, fallback: boolean): Promise<Answer | null> {
  const via: Via = fallback ? "memory" : "knowledge";
  say(fallback ? "Answering from the model's memory" : "Answering from the model's knowledge");
  if (plan.shape === "formula") {
    const got = formulaReply(parseJson<FormulaReply>(await ask(o.model, FORMULA_MEMORY_SYSTEM, `Question: ${q}`, FORMULA_SCHEMA, o.signal)), trail);
    if (!got) return null;
    trail.push(fallback ? "Answered from the model's memory: no source had it." : "Answered from the model's knowledge: a standard formula, so nothing was searched.");
    return {
      ...got, columns: plan.columns.slice(0, 1), via, cites: [], flagged: fallback ? [[0, 0]] : [],
      notes: [fallback ? "From the model's memory: no source had this formula. Check it before use." : "From the model's knowledge; no source was consulted."],
    };
  }
  const got = parseJson<{ rows?: { label?: string; values?: number[] }[] }>(await ask(o.model, MEMORY_SYSTEM,
    `Today is ${o.today}.\nQuestion: ${q}\nThe answer's columns: ${plan.columns.join("; ")}${plan.rows ? `\nOne row is ${plan.rows}.` : ""}`, MEMORY_SCHEMA, o.signal));
  const rows: string[][] = [], labels: string[] = [];
  for (const r of got?.rows ?? []) {
    const vals = (r.values ?? []).map((v) => typeof v === "number" ? numberText(v) : null);
    if (!vals.length || vals.some((v) => v === null) || (rows.length && vals.length !== rows[0]!.length)) continue;
    rows.push(vals as string[]); labels.push(r.label ?? "");
  }
  if (!rows.length) return null;
  trail.push(fallback ? "Answered from the model's memory: no source had the numbers." : "Answered from the model's knowledge: standard knowledge, so nothing was searched.");
  return {
    source: engineText(rows, plan.shape), columns: plan.columns.slice(0, rows[0]!.length), ...(labels.some((l) => l) ? { rowLabels: labels } : {}),
    via, cites: [], flagged: fallback ? rows.flatMap((r, i) => r.map((_, c) => [i, c] as [number, number])).map(placed(plan.shape, rows)) : [],
    notes: [fallback ? "From the model's memory, not from a source. A small model often gets numbers wrong: check them before use." : "From the model's knowledge; no source was consulted."],
  };
}

interface FormulaReply { found?: boolean; expr?: string; params?: string[]; vars?: { name?: string; meaning?: string }[]; quote?: string }

/** A formula reply, checked: the expression in the engine's syntax, its variables, their meanings,
 *  and the LaTeX it quotes. */
function formulaReply(r: FormulaReply | null, trail: string[]): { source: string; params: string[]; vars: { name: string; meaning: string }[]; latex: string } | null {
  if (!r?.found || typeof r.expr !== "string") return null;
  const f = checkFormula(r.expr, (r.params ?? []).filter((p) => typeof p === "string"));
  if (!f) { trail.push(`The model's formula “${r.expr}” is not in the engine's syntax.`); return null; }
  const vars = (r.vars ?? []).filter((v) => typeof v?.name === "string" && typeof v.meaning === "string" && f.params.includes(v.name))
    .map((v) => ({ name: v.name!, meaning: v.meaning! }));
  return { source: f.expr, params: f.params, vars, latex: typeof r.quote === "string" ? r.quote.replace(/^\$+|\$+$/g, "").trim() : "" };
}

type Answer = Omit<AskResult, "question" | "shape" | "model" | "at" | "rowsAre" | "trail">;
type Say = (line: string) => void;

/** Search every source with the plan's queries (results interleaved, so each source contributes),
 *  and read the top results. */
async function gather(plan: Plan, o: AskOptions, trail: string[], say: Say): Promise<{ hits: Hit[]; pages: Page[] }> {
  const lists: Hit[][] = [];
  for (const src of o.sources) {
    for (const s of plan.searches.slice(0, 2)) {
      say(`Searching ${src.name} for “${s}”`);
      try {
        const found = await src.search(s, o.signal);
        trail.push(`Searched ${src.name} for “${s}”: ${plural(found.length, "result")}`);
        lists.push(found);
      } catch (e) {
        if (o.signal?.aborted) throw new AskError("Stopped.", trail);
        trail.push(`Searching ${src.name} for “${s}” failed: ${e instanceof Error ? e.message : String(e)}`);
      }
    }
  }
  const hits: Hit[] = [];
  const seen = new Set<string>();
  for (let i = 0; lists.some((l) => i < l.length); i++) {
    for (const l of lists) { const h = l[i]; if (h && !seen.has(h.url)) { seen.add(h.url); hits.push(h); } }
  }
  const top = hits.slice(0, o.maxPages ?? 5);
  if (top.length) say(`Reading ${plural(top.length, "page")}`);
  const read = await Promise.all(top.map((h) => readHit(o.fetch, h, { reader: o.reader, signal: o.signal }).catch(() => null)));
  if (o.signal?.aborted) throw new AskError("Stopped.", trail);
  const pages: Page[] = [];
  read.forEach((p, i) => {
    if (p) { pages.push(p); trail.push(`Read “${p.title}” (${p.url}): ${plural(p.tables.length, "table")}`); }
    else trail.push(`Could not read ${top[i]!.url} from this page${o.reader ? "" : " (no page reader is set)"}`);
  });
  return { hits, pages };
}

/** A number, list or table: from a table (values copied), else prose (values checked against a quote). */
async function numbers(q: string, plan: Plan, pages: Page[], o: AskOptions, trail: string[], say: Say): Promise<Answer | null> {
  // tables: the best few, previewed, one picked by the model; the values copied by code
  const found: (Found & { score: number })[] = [];
  pages.forEach((page, pi) => {
    for (const table of page.tables) {
      if (table.rows.length < 1 || table.headers.length < 1) continue;
      if (!table.headers.some((_, c) => numericColumn(table, c))) continue;
      found.push({ table, page, score: scoreTable(table, plan, pi) });
    }
  });
  found.sort((a, b) => b.score - a.score);
  const shown = found.slice(0, 5);
  if (shown.length) {
    say(`Choosing among ${plural(shown.length, "table")}`);
    const user = `Today is ${o.today}.\nQuestion: ${q}\nThe answer's columns: ${plan.columns.join("; ")}\n\n${shown.map((f, i) => preview(f.table, i, f.page)).join("\n\n")}`;
    const pick = parseJson<{ table: number; columns: number[]; label: number; filter: { column: number; min: number | null; max: number | null } }>(
      await ask(o.model, PICK_SYSTEM, user, PICK_SCHEMA, o.signal));
    const f = pick && Number.isInteger(pick.table) ? shown[pick.table] : undefined;
    if (pick && f) {
      const width = f.table.headers.length;
      const cols = (pick.columns ?? []).filter((c) => Number.isInteger(c) && c >= 0 && c < width && numericColumn(f.table, c));
      const label = Number.isInteger(pick.label) && pick.label >= 0 && pick.label < width && !cols.includes(pick.label) ? pick.label : -1;
      const fc = pick.filter && Number.isInteger(pick.filter.column) && pick.filter.column >= 0 && pick.filter.column < width ? pick.filter.column : -1;
      const num = (v: unknown) => typeof v === "number" && Number.isFinite(v) ? v : null;
      if (cols.length) {
        const { rows, labels, skipped } = fromTable(f.table, { columns: cols, label, filter: { column: fc, min: num(pick.filter?.min), max: num(pick.filter?.max) } });
        const where = `table ${f.table.caption ? `“${f.table.caption}” ` : ""}on “${f.page.title}”`;
        trail.push(`Chose the ${where}: columns ${cols.map((c) => f.table.headers[c] || `#${c}`).join(", ")}${fc >= 0 ? `, rows with ${f.table.headers[fc] || `#${fc}`} ${fmtRange(num(pick.filter.min), num(pick.filter.max))}` : ""}`);
        if (rows.length) {
          const notes: string[] = [];
          if (skipped) notes.push(`${plural(skipped, "row was", "rows were")} left out because a chosen cell was not a single number.`);
          return {
            source: engineText(rows, plan.shape), columns: cols.map((c) => f.table.headers[c] || plan.columns[cols.indexOf(c)] || `column ${c}`),
            ...(labels.length && labels.some((l) => l) ? { rowLabels: labels } : {}),
            via: "table", cites: [{ title: f.page.title, url: f.page.url }], flagged: [], notes,
          };
        }
        trail.push("No row of that table matched the filter.");
      } else trail.push("The model chose no number columns from the tables.");
    } else trail.push("The model found no table with the data.");
  } else if (pages.length) trail.push("No table on the pages read has numbers.");

  // prose: values lifted with a quote, each checked against the page text
  const ps = passages(pages, plan, false);
  if (ps.length) {
    say("Reading passages");
    const user = `Question: ${q}\nThe answer's columns: ${plan.columns.join("; ")}\n\nPassages:\n${ps.map((p, i) => `[${i + 1}] ${p}`).join("\n")}`;
    const got = parseJson<{ rows?: { label?: string; values?: number[]; quote?: string }[] }>(await ask(o.model, EXTRACT_SYSTEM, user, EXTRACT_SCHEMA, o.signal));
    const all = norm(pages.map((p) => p.text).join("\n"));
    const rows: string[][] = [], labels: string[] = [], flagged: [number, number][] = [];
    const cites = new Map<string, { title: string; url: string }>();
    for (const r of got?.rows ?? []) {
      const vals = (r.values ?? []).map((v) => typeof v === "number" ? numberText(v) : null);
      if (!vals.length || vals.some((v) => v === null) || (rows.length && vals.length !== rows[0]!.length)) continue;
      const quote = norm(r.quote ?? "");
      const inPage = quote.length >= 8 && all.includes(quote);
      const said = inPage ? numbersIn(r.quote ?? "") : [];
      const i = rows.length;
      vals.forEach((v, c) => { if (!said.some((n) => Math.abs(n - Number(v)) <= 1e-9 * Math.max(1, Math.abs(n)))) flagged.push([i, c]); });
      rows.push(vals as string[]);
      labels.push(r.label ?? "");
      if (inPage) { const p = pages.find((pg) => norm(pg.text).includes(quote)); if (p) cites.set(p.url, { title: p.title, url: p.url }); }
    }
    if (rows.length) {
      trail.push(`Lifted ${plural(rows.length, "row")} from passages; ${flagged.length ? `${plural(flagged.length, "value")} not found in the quoted text` : "every value found in the quoted text"}`);
      return {
        source: engineText(rows, plan.shape), columns: plan.columns.slice(0, rows[0]!.length), ...(labels.some((l) => l) ? { rowLabels: labels } : {}),
        via: "text", cites: [...cites.values()], flagged: flagged.map(placed(plan.shape, rows)),
        notes: flagged.length ? ["Values marked ⚠ were not found in the text the model quoted: check them before use."] : [],
      };
    }
    trail.push("The passages did not state the numbers.");
  }

  return null;
}

/** A formula: one the pages state in LaTeX, translated by the model. */
async function formula(q: string, plan: Plan, pages: Page[], o: AskOptions, trail: string[], say: Say): Promise<Answer | null> {
  const ps = passages(pages, plan, true);
  if (ps.length) {
    say("Reading formulas");
    const user = `Question: ${q}\n\nPassages:\n${ps.map((p, i) => `[${i + 1}] ${p}`).join("\n")}`;
    const got = formulaReply(parseJson<FormulaReply>(await ask(o.model, FORMULA_SYSTEM, user, FORMULA_SCHEMA, o.signal)), trail);
    if (got) {
      // the quoted LaTeX must be one of the page's formulas, and name the variables the expression uses
      const page = got.latex ? pages.find((p) => [...p.text.matchAll(/\$([^$]+)\$/g), ...p.tables.flatMap((t) => t.rows.flat()).flatMap((c) => [...c.matchAll(/\$([^$]+)\$/g)])]
        .some((m) => squash(m[1]!).includes(squash(got.latex)))) : undefined;
      const letters = got.latex.replace(/\\[A-Za-z]+/g, "");
      const named = got.params.every((p) => letters.includes(p));
      const ok = !!page && named;
      trail.push(page ? `Took the formula $${got.latex}$ from “${page.title}”${named ? "" : `, but it does not use the variable${got.params.length === 1 ? "" : "s"} ${got.params.join(", ")}`}`
        : `The formula the model quoted ($${got.latex}$) is not on the pages read.`);
      return {
        ...got, columns: plan.columns.slice(0, 1), via: "text", cites: page ? [{ title: page.title, url: page.url }] : [], flagged: ok ? [] : [[0, 0]],
        notes: ok ? [] : ["⚠ This formula could not be matched to one on the page: compare it with the source before use."],
      };
    }
    trail.push("The passages did not state the formula.");
  } else if (pages.length) trail.push("The pages read have no formulas about this.");

  return null;
}

function fmtRange(min: number | null, max: number | null): string {
  if (min !== null && max !== null) return `from ${min} to ${max}`;
  if (min !== null) return `from ${min}`;
  if (max !== null) return `up to ${max}`;
  return "(all)";
}
