/**
 * A `?` question, answered in the engine's own syntax: a number, a list, a table (a matrix), or a
 * formula.
 *
 * The model plans first: the shape of the answer, its parts, searches, and whether the answer is
 * standard knowledge of mathematics or physical science (a formula, a constant), which it answers
 * from what it knows; nothing then leaves the machine, the answer says where it came from, and the
 * notebook offers to check it with a search.
 *
 * Anything else is searched for, and the model answers from what was found, in the question's shape:
 * the passages and table rows of the pages read that share the most words with the question, as much
 * as the model can take; or, for a model that can search the web itself, the pages its own search
 * finds. Every number it gives is looked for in what it read and flagged when it is not there, and a
 * formula is read from the LaTeX it quotes by code. The model's memory is the last resort, and an
 * answer from it is marked as unsourced throughout.
 *
 * (An earlier version had a small model pick table columns while code copied the cells. It latched
 * onto the wrong table as often as a model misreads a page, and never read the paragraph that said
 * "the Tigers have won four World Series".)
 */
import { numberText, numbersIn } from "./numbers.js";
import { readHit, type Fetch, type Hit, type Page, type Source } from "./sources.js";
import { texToEngine } from "./tex.js";

/** A language model held to a JSON schema. The notebook supplies one (Chrome's built-in model, or a
 *  WebGPU model); tests supply a scripted one. */
export interface Model {
  /** Names the model in the result ("Gemini Nano (Chrome)", "Qwen3-4B"). */
  id: string;
  /** The model's reply to `user` under `system`: JSON text meeting `schema`. */
  complete(req: { system: string; user: string; schema: object; signal?: AbortSignal | undefined }): Promise<string>;
  /** How much source text, in characters, the model can be given in one question (its context window,
   *  less the prompt and its reply): about 7,000 for a 4k-token browser model, far more for a cloud one. */
  context?: number;
  /** Free what the model holds (a WebGPU model's GPU memory and worker), when it is replaced. */
  unload?(): Promise<void>;
  /** A model that can search the web itself (OpenRouter's web search): the reply, and the pages its
   *  search gave it. */
  search?(req: { system: string; user: string; schema: object; signal?: AbortSignal | undefined }): Promise<{ text: string; citations: { url: string; title: string; content?: string }[] }>;
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
  /** A model that can search the web itself does so instead of the sources. */
  webSearch?: boolean;
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
/** Where the answer came from: the pages read ("text"), the model's own web search, the model's
 *  knowledge (standard knowledge it was asked for directly), or its memory (a last resort after the
 *  sources gave nothing). "table" is an earlier version's: copied out of a table, kept so saved
 *  notebooks still read. */
export type Via = "table" | "text" | "search" | "knowledge" | "memory";

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
/** What a question is about. Only mathematics and physical science are answered from the model's
 *  knowledge without a search: a small model is sure of far more facts about the world than it
 *  gets right (asked how many World Series a team has won, one listed thirty wrong years). */
const SUBJECTS = ["mathematics", "physical science", "the world"] as const;

/** The answer's shape as the question's own words fix it, when they do: "how many …" and "the number
 *  of …" ask for one number (unless "per year", "each", "for the last …" ask for one per row);
 *  "formula" and "equation" ask for a formula. Null leaves the shape to the model. */
export function shapeOf(question: string): Shape | null {
  if (/\b(formulas?|equations?)\b/i.test(question)) return "formula";
  const count = /\b(how many|how much|number of|count of)\b/i.test(question);
  const perRow = /\b(per|each|every|by (year|season|month|decade|country|state|team|player)|over (the|time)|for the (last|past)|between|since|from \d{4}|annual(ly)?|yearly|list|table)\b/i.test(question);
  return count && !perRow ? "number" : null;
}

const PLAN_SCHEMA = {
  type: "object",
  properties: {
    shape: { type: "string", enum: SHAPES },
    lookup: { type: "boolean" },
    subject: { type: "string", enum: SUBJECTS },
    known: { type: "boolean" },
    searches: { type: "array", items: { type: "string" }, minItems: 1, maxItems: 3 },
    columns: { type: "array", items: { type: "string" }, minItems: 1, maxItems: 8 },
    rows: { type: "string" },
    keywords: { type: "array", items: { type: "string" }, maxItems: 12 },
  },
  required: ["lookup", "shape", "subject", "known", "searches", "columns", "rows", "keywords"],
} as const;

const PLAN_SYSTEM = `You plan how to look up an answer for a math notebook. Reply with JSON only:
- lookup: true if the question asks for a fact, data or a formula that exists somewhere. false if it asks to make something up or work something out instead: a random matrix, an example, the derivative of x^2, solving an equation.
- shape: "number" for one value (the speed of light), "list" for several values of one kind (the first ten primes), "table" for rows of several values (runs and home runs per season), "formula" for an equation or expression (the volume of a prism).
- known: true if the answer is standard knowledge you are sure of and that does not change: a textbook formula, a physical or mathematical constant, a definition. false for statistics, records, results, prices, populations, anything recent, or anything you would have to look up to be exact.
- subject: "mathematics" (numbers, sequences, geometry, formulas of mathematics), "physical science" (laws and constants of physics and chemistry), or "the world" (people, places, teams, events, history, economics, sports, anything else).
- searches: 1 to 3 short search-engine queries likely to find a page stating this (name the subject, not the math).
- columns: for numbers, what each column holds, in order, e.g. ["season", "runs per game", "home runs per game"], the row key (like a year) first; for a formula, the quantity it gives, e.g. ["volume"].
- rows: what one row is, e.g. "one MLB season, 2006 to 2025", or "" for one value or a formula.
- keywords: words and abbreviations the page might use, e.g. ["year", "R/G", "HR", "runs", "home runs"] or ["prism", "volume", "base area", "height"].`;

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
Variables are single letters as a textbook writes them (B, P, h, r), b_1 for a subscript, θ for theta; never words. The expression is only the right-hand side: no "=" and no name on the left.`;

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

const FORMULA_MEMORY_SYSTEM = `Give the standard formula that answers the question, from what you know. Reply with JSON only:
- found: false if you do not know it.
- expr: the formula's right-hand side. ${SYNTAX}
- params: the variables of expr, in a natural order.
- vars: what each variable means.
- quote: the formula in LaTeX, e.g. "V = Bh".`;

// ---------------------------------------------------------------------------------------------

interface Plan { lookup: boolean; shape: Shape; subject: string; known: boolean; searches: string[]; columns: string[]; rows: string; keywords: string[] }

/** The first JSON object in a model's reply (a model may wrap it in prose or a code fence). */
export function parseJson<T>(text: string): T | null {
  const s = text.indexOf("{"), e = text.lastIndexOf("}");
  if (s < 0 || e < s) return null;
  try { return JSON.parse(text.slice(s, e + 1)) as T; } catch { return null; }
}

const words = (s: string) => s.toLowerCase().split(/[^a-z0-9%/]+/).filter((w) => w.length > 1 && !STOP.has(w));
const STOP = new Set(["the", "of", "and", "in", "for", "per", "by", "to", "a", "an", "on", "at", "last", "each", "number", "what", "how", "many", "is", "are", "was", "were", "average", "total", "data", "table", "list", "over", "years", "year", "formula", "equation"]);

const cut = (s: string, n: number) => s.length > n ? `${s.slice(0, n - 1)}…` : s;

const IRREGULAR: Record<string, string> = { won: "win", lost: "lose", beaten: "beat", led: "lead", held: "hold", took: "take", made: "make", came: "come", went: "go", got: "get", ran: "run" };

/** A word's plain form, for comparing the question's words with a table's ("won" is "win", "titles" is "title"). */
function stem(w: string): string {
  if (IRREGULAR[w]) return IRREGULAR[w]!;
  return w.length > 4 ? w.replace(/(ies)$/, "y").replace(/(ing|ed|es|s)$/, "") : w;
}

/** The engine's text for a grid of numbers in the answer's shape: one number alone; a list as a row
 *  `[a, b, c]` (a single column read down the page is laid across); else a matrix. */
export function engineText(rows: string[][], shape: Shape = "table"): string {
  if (rows.length === 1 && rows[0]!.length === 1) return rows[0]![0]!;
  const grid = across(shape, rows) ? [rows.map((r) => r[0]!)] : rows;
  return `[${grid.map((r) => r.join(", ")).join("; ")}]`;
}

/** Whether a grid is one column read down the page: a list, laid across as a row (`[a, b, c]`)
 *  whatever shape was planned, since one value per row is a list. */
const across = (_shape: Shape, rows: string[][]) => rows.length > 1 && rows.every((r) => r.length === 1);

/** Where a grid's [row, column] went in `engineText`'s layout. */
const placed = (shape: Shape, rows: string[][]) => (rc: [number, number]): [number, number] => across(shape, rows) ? [0, rc[0]] : rc;

const norm = (s: string) => s.toLowerCase().replace(/[\s\u00a0]+/g, " ").replace(/[“”]/g, "\"").replace(/[‘’]/g, "'").trim();
const squash = (s: string) => s.replace(/\s+/g, "");

/** Names the engine reads as functions or constants, never a formula's variables. */
const RESERVED = new Set(["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "pi", "e", "i", "conj", "re", "im", "let"]);

/** A model's formula, checked to be an expression in the engine's syntax: its variables, and the
 *  expression, or null. A left-hand side (`V = B*h`) is dropped. */
export function checkFormula(expr: string, params: string[]): { expr: string; params: string[] } | null {
  let e = expr.replace(/π/g, "pi").replace(/·|×/g, "*").replace(/−/g, "-").trim();
  if (e.includes("=")) e = e.slice(e.lastIndexOf("=") + 1).trim();
  if (!e || !/^[A-Za-z0-9_\u0391-\u03c9+\-*/^().,\s]+$/.test(e)) return null;
  let depth = 0;
  for (const c of e) { if (c === "(") depth++; else if (c === ")" && --depth < 0) return null; }
  if (depth) return null;
  const ids = [...new Set((e.match(/[A-Za-z_\u0391-\u03c9][A-Za-z0-9_\u0391-\u03c9]*/g) ?? []).filter((n) => !RESERVED.has(n)))];
  const ok = params.filter((p) => ids.includes(p));
  return { expr: e, params: [...ok, ...ids.filter((n) => !ok.includes(n))] };
}

const NUM = String.raw`-?\d+(?:\.\d+)?`;
const GRID = new RegExp(String.raw`^(?:${NUM}|\[${NUM}(?:, ${NUM})*(?:; ${NUM}(?:, ${NUM})*)*\])$`);

/** Whether a saved answer is one this code could have produced: a number, a grid of numbers, or a
 *  formula in the checked syntax. A notebook file is not trusted to carry anything else as an answer. */
export function validAnswer(shape: Shape, source: string, params: string[] = []): boolean {
  if (shape !== "formula") return GRID.test(source);
  const f = checkFormula(source, params);
  return !!f && f.expr === source;
}

async function ask(model: Model, system: string, user: string, schema: object, signal?: AbortSignal): Promise<string> {
  if (signal?.aborted) throw new AskError("Stopped.");
  let reply: string;
  try { reply = await model.complete({ system, user, schema, signal }); } catch (e) {
    // a model stopped mid-answer throws its own abort error
    if (signal?.aborted) throw new AskError("Stopped.");
    throw e;
  }
  // or returns what it had so far
  if (signal?.aborted) throw new AskError("Stopped.");
  return reply;
}

/** Words that ask to make something, which no page holds. */
const MAKE = /\b(random|randomly|generate|make up|invent|an example of|example of a)\b/i;

/** Row names, when they name the rows: two or more different ones (a model may label every row "Year"). */
const named = (labels: string[]): { rowLabels?: string[] } => new Set(labels.filter((l) => l.trim())).size > 1 ? { rowLabels: labels } : {};

const plural = (n: number, one: string, many = `${one}s`) => `${n} ${n === 1 ? one : many}`;

export async function lookup(question: string, o: AskOptions): Promise<AskResult> {
  const trail: string[] = [];
  const say = (line: string) => { o.onProgress?.(line); };
  const q = question.trim();

  // 1. the plan
  say("Planning the search");
  const cue = shapeOf(q);
  const hint = cue === "number" ? "\nThe answer is one number." : cue === "formula" ? "\nThe answer is a formula." : "";
  const plan0 = parseJson<Partial<Plan>>(await ask(o.model, PLAN_SYSTEM, `Today is ${o.today}.\nQuestion: ${q}${hint}`, PLAN_SCHEMA, o.signal));
  const subject = SUBJECTS.includes(plan0?.subject as typeof SUBJECTS[number]) ? plan0!.subject! : "the world";
  const plan: Plan = {
    lookup: plan0?.lookup !== false && !MAKE.test(q),
    shape: cue ?? (SHAPES.includes(plan0?.shape as Shape) ? plan0!.shape as Shape : "table"),
    subject,
    // the model's own knowledge answers only mathematics and physical science
    known: plan0?.known === true && subject !== "the world",
    searches: (plan0?.searches ?? []).filter((s) => typeof s === "string" && s.trim()).slice(0, 3),
    columns: (plan0?.columns ?? []).filter((s) => typeof s === "string" && s.trim()),
    rows: typeof plan0?.rows === "string" ? plan0.rows : "",
    keywords: (plan0?.keywords ?? []).filter((s) => typeof s === "string"),
  };
  // asked to make something rather than find it, there is nothing to look up (asked for a random
  // matrix, a lookup once searched Wikipedia and lifted [1, 2, 3, 4, 5] from an article on ciphers)
  if (!plan.lookup) {
    throw new AskError(`This asks to make something rather than to look it up${/\brandom\b/i.test(q) ? " (and the engine has no random numbers)" : ""}: a lookup finds facts, data and formulas. Write the mathematics in a cell instead.`, ["The model says this is not a lookup: it asks to make or work something out."]);
  }
  if (!plan.searches.length) plan.searches = [q];
  if (!plan.columns.length) plan.columns = ["value"];
  // what a row is, in words: one number or a formula has no rows, and a model that lists values here
  // has not described anything
  if (plan.shape === "number" || plan.shape === "formula" || (plan.rows.match(/\d+/g) ?? []).length > 3) plan.rows = "";
  if (plan0?.known === true && !plan.known) trail.push("The model says it knows this, but questions about the world are searched for.");
  trail.push(plan.shape === "formula" ? `Looking for a formula for ${plan.columns[0]}` : `Looking for ${plan.shape === "number" ? "a number" : plan.shape === "list" ? "a list" : "a table"}: ${plan.columns.join(", ")}${plan.rows ? `; a row is ${plan.rows}` : ""}`);
  const base = { question: q, shape: plan.shape, model: o.model.id, at: o.today, rowsAre: plan.rows };

  const knowledge = o.useKnowledge !== false;
  // standard knowledge: the model answers, and nothing is sent anywhere
  if (plan.known && knowledge && !o.forceSearch) {
    const r = await fromKnowledge(q, plan, o, trail, say, false);
    if (r) return { ...base, ...r, trail };
    trail.push("The model did not answer from its knowledge after all: searching.");
  }
  // a model that searches the web itself needs no source of the notebook's
  const web = !!(o.webSearch && o.model.search);
  const none = !o.sources.length && !web;
  const declined = none || (o.beforeSearch ? !(await o.beforeSearch()) : false);
  if (o.signal?.aborted) throw new AskError("Stopped.", trail);
  if (declined) {
    const why = none ? "No search source is turned on" : "Searching was declined";
    trail.push(`${why}.`);
    // a check of the model's own answer that cannot search has nothing to add
    if (o.forceSearch && plan.known) throw new AskError(`${why}, so the answer could not be checked.`, trail);
    const r = knowledge && !plan.known ? await fromKnowledge(q, plan, o, trail, say, true) : null;
    if (r) return { ...base, ...r, trail };
    throw new AskError(`${why}, and the model does not know the answer.`, trail);
  }
  // a model searching the web itself: one call, its pages its own
  if (web) {
    const r = await direct(q, plan, [], o, trail, say);
    if (r) return { ...base, ...r, trail };
    const m = knowledge && (!plan.known || o.forceSearch) ? await fromKnowledge(q, plan, o, trail, say, true) : null;
    if (m) return { ...base, ...m, trail };
    throw new AskError("The model's web search did not find the answer.", trail);
  }
  const { hits, pages } = await gather(plan, o, trail, say);
  const r = pages.length ? await direct(q, plan, pages, o, trail, say) : null;
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
    const got = formulaReply(parseJson<FormulaReply>(await ask(o.model, FORMULA_MEMORY_SYSTEM, `Question: ${q}`, FORMULA_SCHEMA, o.signal)), trail, false);
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
    source: engineText(rows, plan.shape), columns: plan.columns.slice(0, rows[0]!.length), ...named(labels),
    via, cites: [], flagged: fallback ? rows.flatMap((r, i) => r.map((_, c) => [i, c] as [number, number])).map(placed(plan.shape, rows)) : [],
    notes: [fallback ? "From the model's memory, not from a source. A small model often gets numbers wrong: check them before use." : "From the model's knowledge; no source was consulted."],
  };
}

interface FormulaReply { found?: boolean; expr?: string; params?: string[]; vars?: { name?: string; meaning?: string }[]; quote?: string }

/** A formula reply, checked: the expression in the engine's syntax, its variables, their meanings,
 *  and the LaTeX it quotes. */
/** A textbook's name for a variable: a letter, maybe Greek, maybe with a subscript (`b_1`). */
const TIDY = /^[A-Za-z\u0391-\u03c9](_[A-Za-z0-9]+)?$/;

function formulaReply(r: FormulaReply | null, trail: string[], fromPage: boolean): { source: string; params: string[]; vars: { name: string; meaning: string }[]; latex: string } | null {
  if (!r?.found) return null;
  const latex = typeof r.quote === "string" ? r.quote.replace(/^\$+|\$+$/g, "").trim() : "";
  const order = (r.params ?? []).filter((p) => typeof p === "string");
  const tex = latex ? texToEngine(latex) : null;
  const read = tex ? checkFormula(tex.expr, order) : null;
  const model = typeof r.expr === "string" ? checkFormula(r.expr, order) : null;
  // a formula from a page is read from its LaTeX by code: the model only chose it (asked to translate
  // `2B + Ph`, a small model wrote `{2*B+Ph}`). From memory, the model's expression stands when its
  // names are a textbook's; otherwise its LaTeX is read too.
  const f = fromPage ? read ?? model : model && model.params.every((p) => TIDY.test(p)) ? model : read ?? model;
  if (!f) { trail.push(`Could not read the formula ${latex ? `$${latex}$` : `“${String(r.expr ?? "")}”`} into the engine's syntax.`); return null; }
  if (f === read && latex) trail.push(`Read $${latex}$ as ${f.expr}`);
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

const DIRECT_SCHEMA = {
  type: "object",
  properties: {
    found: { type: "boolean" },
    rows: { type: "array", items: { type: "array", items: { type: "number" } } },
    columns: { type: "array", items: { type: "string" } },
    rowLabels: { type: "array", items: { type: "string" } },
    formula: {
      type: "object",
      properties: {
        latex: { type: "string" }, expr: { type: "string" }, params: { type: "array", items: { type: "string" } },
        vars: { type: "array", items: { type: "object", properties: { name: { type: "string" }, meaning: { type: "string" } }, required: ["name", "meaning"] } },
      },
      required: ["latex", "expr", "params", "vars"],
    },
    sources: { type: "array", items: { type: "object", properties: { title: { type: "string" }, url: { type: "string" }, quote: { type: "string" } }, required: ["title", "url", "quote"] } },
  },
  required: ["found", "rows", "columns", "rowLabels", "formula", "sources"],
} as const;

const DIRECT_SYSTEM = `You answer a question for a math notebook from sources: the passages and table rows given below, or the pages your web search finds. Reply with JSON only.
- found: false if the sources do not answer the question (then leave the rest empty).
- rows: the answer's numbers. One number: [[x]]. A list: one row, [[a, b, c]]. A table: one row per item, one number per column. A formula: [].
  Use only numbers the sources state; a number written in words ("four titles") is that number (4). Never estimate or remember one.
  For "how many", count only what the sources list or state as a count.
- columns: what each column holds. rowLabels: what each row is when rows are named by text (a team, a country), else [].
- formula: for a formula only, else empty: latex as a source writes it; expr the right-hand side in the notebook's syntax. ${SYNTAX}
- sources: the pages you used, each with its title, url and a short exact quote that states the answer.`;

interface DirectReply {
  found?: boolean; rows?: unknown[][]; columns?: string[]; rowLabels?: string[];
  formula?: { latex?: string; expr?: string; params?: string[]; vars?: { name?: string; meaning?: string }[] };
  sources?: { title?: string; url?: string; quote?: string }[];
}

/** The stretches of the pages most likely to hold the answer, as much as `budget` characters allows:
 *  paragraphs, ranked by the question's words they share (a page's first paragraphs, which sum it
 *  up, a little ahead), and tables, ranked by their caption, column names and best row. A table that
 *  does not fit keeps the rows with the question's words, or, when no row has them, its first rows
 *  and as many of its last as fit ("the first ten", "the last 20 years"). Given back page by page,
 *  each in its own order. */
export function evidence(pages: Page[], q: string, plan: Pick<Plan, "keywords" | "columns" | "shape">, budget: number): string {
  const want = new Set([...words(q), ...plan.keywords.flatMap(words), ...plan.columns.flatMap(words)].map(stem));
  // the question's words that can single rows out: not short numbers ("the last 20 years" is no row
  // whose R/G is 4.20), though a year is ("in 1984")
  const asked = new Set(words(q).filter((w) => !/^\d{1,3}$/.test(w)).map(stem));
  const count = (s: string, of: Set<string>) => { const ws = new Set(words(s).map(stem)); let n = 0; for (const w of of) if (ws.has(w)) n++; return n; };
  const hits = (s: string) => count(s, want);
  const formula = plan.shape === "formula";
  interface Unit { page: number; order: number; score: number; text: (room: number) => string }
  const units: Unit[] = [];
  pages.forEach((p, pi) => {
    let order = 0;
    for (const para of p.text.split("\n")) {
      const o = order++;
      const h = hits(para), f = formula && para.includes("$");
      if (para.length < 20 || (!h && !f)) continue;
      const text = cut(para, 900);
      units.push({ page: pi, order: o, score: h * 3 + (/\d/.test(para) ? 1 : 0) + (f ? 3 : 0) + (o < 3 ? 1 : 0) - pi * 0.5, text: () => text });
    }
    for (const t of p.tables) {
      const o = order++;
      const lines = t.rows.map((r) => r.join(" | "));
      // rows are told apart by the question's own words ("tigers"), not the plan's guesses at column
      // names: a "short season" note once made one row of a table of seasons the only one kept
      const rowHits = lines.map((l) => count(l, asked));
      const best = Math.max(0, ...rowHits);
      const f = formula && lines.some((l) => l.includes("$"));
      const score = hits(`${t.caption} ${t.headers.join(" ")}`) * 3 + best * 2 + (f ? 3 : 0) - pi * 0.5;
      if (score <= 0 && !f) continue;
      const head = `Table${t.caption ? `: ${t.caption}` : ""}\n${t.headers.join(" | ")}`;
      units.push({
        page: pi, order: o, score,
        text: (room) => {
          const all = lines.map((_, i) => i);
          const keyed = all.filter((i) => rowHits[i]! > 0);
          const pick = keyed.length && keyed.length < lines.length ? keyed : all;
          const size = (ix: number[]) => ix.reduce((n, i) => n + lines[i]!.length + 1, head.length);
          let ix = pick;
          if (size(ix) > room) {
            // the rows with the question's words, from the top; or the first rows and the last
            const first = pick === all ? pick.slice(0, 10) : [];
            const rest = pick === all ? pick.slice(10).reverse() : pick;
            ix = [...first];
            for (const i of rest) { if (size([...ix, i]) > room) break; ix.push(i); }
            ix.sort((a, b) => a - b);
          }
          const left = lines.length - ix.length;
          return [head, ...ix.map((i) => lines[i]!), ...(left ? [`(${plural(left, "row")} of this table left out)`] : [])].join("\n");
        },
      });
    }
  });
  units.sort((a, b) => b.score - a.score);
  const chosen: { unit: Unit; text: string }[] = [];
  let used = 0;
  for (const u of units) {
    const room = budget - used;
    if (room < 200) break;
    const text = u.text(Math.min(room, Math.floor(budget * 0.6)));
    if (text.length > room) continue;
    chosen.push({ unit: u, text }); used += text.length + 1;
  }
  return pages.map((p, pi) => {
    const mine = chosen.filter((c) => c.unit.page === pi).sort((a, b) => a.unit.order - b.unit.order);
    return mine.length ? [`## ${p.title} (${p.url})`, ...mine.map((c) => c.text)].join("\n") : "";
  }).filter(Boolean).join("\n\n");
}

/** The model's own answer, in the question's shape, from what was found on the pages read (or, with
 *  no pages, from its own web search); every number it gives is looked for in what it read. */
async function direct(q: string, plan: Plan, pages: Page[], o: AskOptions, trail: string[], say: Say): Promise<Answer | null> {
  const ask0 = `Today is ${o.today}.\nQuestion: ${q}\nThe answer is ${plan.shape === "number" ? "one number" : plan.shape === "list" ? "a list" : plan.shape === "formula" ? "a formula" : "a table"}${plan.shape === "table" || plan.shape === "list" ? ` (${plan.columns.join("; ")})` : ""}.`;
  let reply: DirectReply | null;
  /** All that the model read, for looking its numbers up. */
  let readText: string;
  let cites: { title: string; url: string }[];
  if (!pages.length) {
    say(`Searching the web with ${o.model.id}`);
    let got: { text: string; citations: { url: string; title: string; content?: string }[] };
    try { got = await o.model.search!({ system: DIRECT_SYSTEM, user: ask0, schema: DIRECT_SCHEMA, signal: o.signal }); }
    catch (e) { if (o.signal?.aborted) throw new AskError("Stopped.", trail); throw e; }
    if (o.signal?.aborted) throw new AskError("Stopped.", trail);
    reply = parseJson<DirectReply>(got.text);
    const quoted = (reply?.sources ?? []).map((s) => s.quote ?? "");
    readText = [...quoted, ...got.citations.map((c) => c.content ?? "")].join("\n");
    const seen = new Set<string>();
    cites = [...got.citations, ...(reply?.sources ?? []).map((s) => ({ url: s.url ?? "", title: s.title ?? "" }))]
      .filter((c) => /^https?:\/\//.test(c.url) && !seen.has(c.url) && seen.add(c.url)).map((c) => ({ title: c.title || new URL(c.url).host, url: c.url })).slice(0, 8);
    trail.push(`${o.model.id} searched the web: ${plural(got.citations.length, "page")} cited`);
  } else {
    const sources = evidence(pages, q, plan, o.model.context ?? 8000);
    if (!sources) { trail.push("Nothing on the pages read shares a word with the question."); return null; }
    say(`${o.model.id} is reading what was found`);
    reply = parseJson<DirectReply>(await ask(o.model, DIRECT_SYSTEM, `${ask0}\n\nSources:\n${sources}`, DIRECT_SCHEMA, o.signal));
    // what the model was given, not every page whole: a number on a page it did not see came from its
    // memory, and across five pages whole, every small number and every year is somewhere
    readText = sources;
    const used = new Set((reply?.sources ?? []).map((s) => s.url ?? ""));
    const usedPages = pages.filter((p) => used.has(p.url));
    cites = (usedPages.length ? usedPages : pages).map((p) => ({ title: p.title, url: p.url }));
    trail.push(`Gave ${o.model.id} the passages and table rows of the pages read that share the most words with the question (${Math.round(sources.length / 100) / 10}k characters)`);
  }
  if (!reply?.found) { trail.push("The model found no answer in the sources."); return null; }

  if (plan.shape === "formula") {
    const f = reply.formula ?? {};
    const got = formulaReply({ found: true, expr: f.expr ?? "", params: f.params ?? [], vars: f.vars ?? [], quote: f.latex ?? "" }, trail, true);
    if (!got) return null;
    const stated = !!got.latex && squash(readText).includes(squash(got.latex));
    trail.push(stated ? `The formula $${got.latex}$ is in the sources` : `The formula $${got.latex}$ is not written that way in the sources`);
    return {
      ...got, columns: plan.columns.slice(0, 1), via: pages.length ? "text" : "search", cites, flagged: stated ? [] : [[0, 0]],
      notes: stated ? [] : ["⚠ This formula is not written this way in the sources: compare it with them before use."],
    };
  }

  const rows = (reply.rows ?? []).map((r) => (Array.isArray(r) ? r : []).map((v) => typeof v === "number" ? numberText(v) : null));
  if (!rows.length || rows.some((r) => !r.length || r.some((v) => v === null) || r.length !== rows[0]!.length)) {
    trail.push("The model's answer was not a grid of numbers.");
    return null;
  }
  const said = numbersIn(readText);
  const flagged: [number, number][] = [];
  rows.forEach((r, i) => r.forEach((v, c) => { if (!said.some((n) => Math.abs(n - Number(v)) <= 1e-9 * Math.max(1, Math.abs(n)))) flagged.push([i, c]); }));
  const grid = rows as string[][];
  trail.push(`${o.model.id} answered with ${plural(grid.length * grid[0]!.length, "value")}; ${flagged.length ? `${plural(flagged.length, "value")} not found in the sources` : "every value found in the sources"}`);
  const columns = (reply.columns ?? []).filter((c) => typeof c === "string");
  return {
    source: engineText(grid, plan.shape), columns: columns.length ? columns.slice(0, grid[0]!.length) : plan.columns.slice(0, grid[0]!.length),
    ...named((reply.rowLabels ?? []).filter((l) => typeof l === "string").slice(0, grid.length)),
    via: pages.length ? "text" : "search", cites, flagged: flagged.map(placed(plan.shape, grid)),
    notes: flagged.length ? ["Values marked ⚠ are not in the sources the model read: check them before use."] : [],
  };
}
