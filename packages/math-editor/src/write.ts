import { type Atom, type Block, type Stmt, INFIX, isIdChar, isIdStart, isSep, KEYWORDS, merges, showAtom } from "./model.js";

/**
 * The editor's tree → source text, the text the engine is sent.
 *
 * An atom read from text is written as it was spelled (`Src`), with the whitespace that was before
 * it, while it and its neighbours are as they were read, so `write(read(s))` is `s` for every `s`
 * and an edit rewrites only the atoms it touched. A changed or new atom is written afresh: sums,
 * comparisons and connectives spaced (`x + 1`, `p ∧ q`), a space after a comma, and parentheses only
 * where the engine would otherwise read something else — around a fraction something on its left
 * would take into its numerator (`2·(a/b)`, not `2a/b`), around a numerator with a sum in it, and
 * around a denominator or exponent that is more than one factor. For any tree `read` produces,
 * `read(write(t))` is `t` again (`test/`).
 *
 * `spans` maps each atom to the text it produced, so a position the engine reports (an error's
 * span) can be shown on the atoms it covers. `holes` counts empty slots: text with a hole in it is
 * not yet something to send.
 */

export interface Written { text: string; spans: Map<Atom, { start: number; end: number }>; holes: number }

export function write(stmt: Stmt): Written {
  const w = new Writer();
  if (stmt.body.length === 0) w.out = stmt.pad ?? "";
  else { w.root = stmt.body; w.block(stmt.body, ""); }
  return { text: w.out, spans: w.spans, holes: w.holes };
}

/** Shorthand for the text alone. */
export const writeText = (stmt: Stmt) => write(stmt).text;

/** The tree without its spellings: written afresh, the way the editor writes what is typed. */
export function forget(stmt: Stmt): Stmt {
  const strip = (b: Block): Block => b.map((a) => {
    const { src: _, ...rest } = a;
    const c = rest as Atom;
    switch (c.k) {
      case "frac": return { ...c, num: strip(c.num), den: strip(c.den) };
      case "sup": return { ...c, exp: strip(c.exp) };
      case "paren": case "str": case "brace": case "raw": return { ...c, body: strip(c.body) };
      case "call": return { ...c, args: c.args.map(strip) };
      case "matrix": return { ...c, rows: c.rows.map((r) => r.map(strip)) };
      case "part": return { ...c, specs: c.specs.map(strip) };
      case "let": return { ...c, name: strip(c.name), params: c.params && c.params.map(strip) };
      default: return c;
    }
  });
  return { body: strip(stmt.body) };
}

const isCh = (a: Atom | undefined, c?: string): a is Atom & { k: "ch" } => a?.k === "ch" && (c === undefined || a.c === c);

/** The entrywise operators, each one atom (`model.ts`). */
const ENTRYWISE = ["./", ".*"];

/** Is the `-` at `j` a subtraction (something to subtract from on its left) rather than a negation? */
export function binaryMinus(b: Block, j: number): boolean {
  const p = b[j - 1];
  return !!p && p.k !== "let" && !(isCh(p) && (p.c === "+" || p.c === "-" || p.c === "*" || ENTRYWISE.includes(p.c) || isSep(p.c)));
}

/** Is the character at `j` an operator written with a space either side? */
const spaced = (b: Block, j: number) => {
  const a = b[j];
  return isCh(a) && (a.c === "+" || (a.c === "-" && binaryMinus(b, j)) || ENTRYWISE.includes(a.c) || INFIX.has(a.c));
};

/** Does `b` have a sum or difference at its top level? */
const additive = (b: Block) => b.some((a, j) => j > 0 && isCh(a) && (a.c === "+" || (a.c === "-" && binaryMinus(b, j))));

/** Does `b` read as a single `unary` of the grammar — negations, then one factor, then at most one
 *  power? Only then can it be a denominator or an exponent without parentheses. */
function singleUnary(b: Block): boolean {
  let j = 0;
  while (isCh(b[j], "-")) j++;
  const rest = b.slice(j);
  if (rest.length === 0) return false;
  const last = rest[rest.length - 1]!;
  const factor = last.k === "sup" ? rest.slice(0, -1) : rest;
  if (factor.length === 1 && (factor[0]!.k === "call" || factor[0]!.k === "paren" || factor[0]!.k === "matrix" || factor[0]!.k === "brace")) return true;
  if (factor.length === 0 || !factor.every((a) => isCh(a))) return false;
  const s = factor.map((a) => (a as { c: string }).c).join("");
  return /^[0-9]*\.?[0-9]+$/.test(s) || /^%([0-9]+|%*)$/.test(s) || (isIdStart(s[0]!) && Array.from(s).every(isIdChar));
}

/** The first character an atom writes, to decide whether it needs a space after what came before. */
function firstChar(a: Atom): string {
  if (a.src?.text) return a.src.text[0]!;
  switch (a.k) {
    case "ch": return a.c;
    case "call": return a.name[0] ?? "";
    case "let": return "l";
    case "sup": return "^";
    case "matrix": case "part": return "[";
    case "brace": return "{";
    case "raw": return (a.body[0] as { c?: string } | undefined)?.c ?? "";
    case "str": return '"';
    case "asset": return "⟦";
    default: return "(";
  }
}

/** The token of a name around `j`, as the engine lexes the run of characters it is in (`1do` is
 *  1 then `do`), as [start, end); empty where `j` is no name's. */
function runAt(b: Block, j: number): [number, number] {
  const c = (k: number) => (isCh(b[k]) && (b[k] as { c: string }).c.length === 1 ? (b[k] as { c: string }).c : "");
  if (!isIdChar(c(j))) return [j, j];
  let s = j;
  while (s > 0 && isIdChar(c(s - 1))) s--;
  // lex the run forward: numerals, then names, up to the token that holds `j`
  for (let k = s; ;) {
    let e = k + 1;
    if (isIdStart(c(k))) while (isIdChar(c(e))) e++;
    else while (/[0-9]/.test(c(e))) e++;
    if (j < e) return isIdStart(c(k)) ? [k, e] : [j, j];
    k = e;
  }
}
/** Is the run at `j` one of the other worlds' keywords (`when`, `do`)? */
const keywordAt = (b: Block, j: number) => { const [s, e] = runAt(b, j); return e > s && KEYWORDS.has(b.slice(s, e).map((a) => (a as { c: string }).c).join("")); };

const shape = (a: Atom | undefined) => (a ? showAtom(a) : "");

/** Every block an atom holds. */
function slotsOf(a: Atom): Block[] {
  switch (a.k) {
    case "frac": return [a.num, a.den];
    case "sup": return [a.exp];
    case "paren": case "str": case "brace": case "raw": return [a.body];
    case "call": return a.args;
    case "matrix": return a.rows.flat();
    case "part": return a.specs;
    case "let": return [a.name, ...(a.params ?? [])];
    default: return [];
  }
}

/** Was every atom inside `a` read from text (none typed since)? */
const allRead = (a: Atom): boolean => !!a.src && slotsOf(a).every((b) => b.every(allRead));

class Writer {
  out = "";
  /** The cell's top-level row, where a command's head (`cbv:`) can be. */
  root: Block | null = null;
  spans = new Map<Atom, { start: number; end: number }>();
  holes = 0;

  /** A row of atoms; `firstGap` is the space before the first when it is written afresh. */
  block(b: Block, firstGap = "") {
    if (b.length === 0) { this.out += firstGap; this.holes++; return; }
    b.forEach((a, j) => {
      const prev = b[j - 1], next = b[j + 1];
      const src = a.src;
      // the space before an atom is its own while its left neighbour is the one it was read beside
      let gap = src && src.prev === shape(prev) ? src.gap : this.gapBefore(b, j, firstGap);
      // a space where the two sides would lex as one (`x sin(y)`, `x^n y`); characters of one run
      // are written as they are (`xy` is one name)
      if (!gap && j > 0 && !(isCh(a) && isCh(prev)) && merges(this.out, firstChar(a))) gap = " ";
      this.out += gap;
      const start = this.out.length;
      if (src && src.shape === shape(a) && src.prev === shape(prev) && src.next === shape(next) && allRead(a)) {
        this.out += src.text;
        this.spelled(a, start);
        if (a.k === "let" && j === b.length - 1) this.holes++;
      } else this.atom(a, b, j);
      this.spans.set(a, { start, end: this.out.length });
      if (!next && src?.trail !== undefined && src.next === "") this.out += src.trail;
    });
  }

  /** The space before the atom at `j` when it is written afresh. */
  private gapBefore(b: Block, j: number, firstGap: string): string {
    if (j === 0) return firstGap;
    const p = b[j - 1]!;
    if (p.k === "let") return " ";
    if ((p.k === "ch" && p.c === " ") || (b[j]!.k === "ch" && (b[j] as { c: string }).c === " ")) return "";
    // after an operator read from text, the space it had on its left (`p=b`, `p = b`)
    if (spaced(b, j - 1) && p.src && !/\n/.test(p.src.gap)) return p.src.gap;
    if (spaced(b, j) || spaced(b, j - 1)) return " ";
    // a keyword is a word on its own: `when a < 2 do x := 1`
    if ((keywordAt(b, j) && runAt(b, j)[0] === j) || (keywordAt(b, j - 1) && runAt(b, j - 1)[1] === j)) return " ";
    if (isCh(p) && [",", ";", "∀", "∃"].includes(p.c)) return " ";
    // a colon has a space after it (`cbv: t`, `a: inc`), but not a binder's (`λx:A. x`)
    if (isCh(p, ":")) {
      const s = runAt(b, j - 2)[0], q = b[s - 1], first = b[s];
      return (isCh(q) && ["λ", "\\"].includes(q.c)) || (isCh(first) && first.c === "λ") ? "" : " ";
    }
    // a binder's dot (`λx. x`), not a numeral's (`2.5`)
    if (isCh(p, ".") && isCh(b[j - 2]) && isIdChar((b[j - 2] as { c: string }).c) && !/[0-9]/.test((b[j - 2] as { c: string }).c)) return " ";
    return "";
  }

  /** Spans and holes for what an atom's spelling holds, now at `start`. */
  private spelled(a: Atom, start: number) {
    for (const s of slotsOf(a)) {
      // `sin^2(y)`'s power is spelled inside the call before it: its exponent has no place of its own
      if (!a.src!.text) { if (s.length === 0) this.holes++; continue; }
      if (s.length === 0) this.holes++;
      for (const x of s) {
        const from = start + x.src!.start - a.src!.start;
        this.spans.set(x, { start: from, end: from + x.src!.end - x.src!.start });
        this.spelled(x, from);
      }
    }
  }

  /** A slot that must read as one `unary` (a denominator, an exponent). */
  private tight(b: Block) {
    // a negation could go bare (`x^-2` is the engine's x^(-2)) but reads better in parentheses
    if (b.length > 0 && singleUnary(b) && !isCh(b[0], "-")) this.block(b);
    else { this.out += "("; this.block(b); this.out += ")"; }
  }

  /** Slots one after another, `sep` between them and a space after it. */
  private list(bs: Block[], sep: string) {
    bs.forEach((x, i) => { if (i) this.out += sep; this.block(x, i ? " " : ""); });
  }

  private atom(a: Atom, b: Block, j: number) {
    switch (a.k) {
      case "ch": this.out += a.c; return;
      case "frac": {
        // bare only where nothing on the left would join the numerator and no power follows
        const p = b[j - 1], pc = p?.k === "ch" ? p.c : null;
        const bare = b[j + 1]?.k !== "sup" && (!p || p.k === "let" || pc === "+" || (pc === "-" ? binaryMinus(b, j - 1) : pc !== null && (isSep(pc) || keywordAt(b, j - 1) || (pc === " " && keywordAt(b, j - 2)))));
        if (!bare) this.out += "(";
        if (a.num.length > 0 && !additive(a.num)) this.block(a.num);
        else { this.out += "("; this.block(a.num); this.out += ")"; }
        this.out += "/";
        this.tight(a.den);
        if (!bare) this.out += ")";
        return;
      }
      case "sup": this.out += "^"; this.tight(a.exp); return;
      case "paren": this.out += "("; this.block(a.body); this.out += ")"; return;
      case "brace": this.out += "{"; this.block(a.body); this.out += "}"; return;
      case "raw": this.out += a.body.map((c) => (c.k === "ch" ? c.c : "")).join(""); return;
      case "call": this.out += a.name + "("; this.list(a.args, ","); this.out += ")"; return;
      case "let":
        this.out += "let";
        this.block(a.name, " ");
        if (a.params) { this.out += "("; this.list(a.params, ","); this.out += ")"; }
        this.out += " =";
        if (j === b.length - 1) this.holes++;   // a head with no body yet
        return;
      case "part":
        // an index is characters kept as typed (a span, All, a list, a name in quotes)
        this.out += "[[";
        a.specs.forEach((x, i) => {
          if (i) this.out += ", ";
          if (!x.length) this.holes++;
          this.out += x.map((c) => (c.k === "ch" ? c.c : "")).join("");
        });
        this.out += "]]";
        return;
      case "str": this.out += '"' + a.body.map((c) => (c.k === "ch" ? c.c : "")).join("") + '"'; return;
      case "asset": this.out += `⟦${a.name}⟧`; return;
      case "matrix":
        this.out += "[";
        a.rows.forEach((r, i) => { if (i) this.out += ";"; r.forEach((x, k) => { if (k) this.out += ","; this.block(x, i || k ? " " : ""); }); });
        this.out += "]";
        return;
    }
  }
}

/** The atoms a span of the text covers (the engine reports a syntax error's span): the largest ones
 *  it covers whole, else the innermost ones it overlaps; a span at the very end (an unexpected end
 *  of input) is the last atom. */
export function atomsInSpan(stmt: Stmt, span: { start: number; end: number }): Atom[] {
  const { text, spans } = write(stmt);
  const start = span.start, end = Math.max(span.end, span.start + 1);
  const within = (s: { start: number; end: number }, t: { start: number; end: number }) => t.start <= s.start && s.end <= t.end;
  const hits = [...spans].filter(([, s]) => s.start < end && s.end > start);
  const whole = hits.filter(([, s]) => within(s, { start, end }));
  const pick = whole.length
    ? whole.filter(([a, s]) => !whole.some(([b, t]) => b !== a && within(s, t)))
    : hits.filter(([a, s]) => !hits.some(([b, t]) => b !== a && within(t, s)));
  if (!pick.length && start >= text.length && stmt.body.length) return [stmt.body[stmt.body.length - 1]!];
  return pick.map(([a]) => a);
}
