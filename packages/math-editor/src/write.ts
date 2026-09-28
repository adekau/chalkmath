import { type Atom, type Block, type Stmt, isIdChar, isIdStart, merges } from "./model.js";

/**
 * The editor's tree → source text, the text the engine is sent. Parentheses are written only where
 * the engine would otherwise read something else: around a fraction something on its left would
 * take into its numerator (`2·(a/b)`, not `2a/b`), around a numerator with a sum in it, and around a
 * denominator or exponent that is more than one factor. For any tree `read` produces,
 * `read(write(t))` is `t` again (`test/`).
 *
 * `spans` maps each atom to the text it produced, so a position the engine reports (an error's
 * span) can be shown on the atoms it covers. `holes` counts empty slots: text with a hole in it is
 * not yet something to send.
 */

export interface Written { text: string; spans: Map<Atom, { start: number; end: number }>; holes: number }

export function write(stmt: Stmt): Written {
  const w = new Writer();
  if (stmt.let) {
    w.out += `let ${stmt.let.name}`;
    if (stmt.let.params) w.out += `(${stmt.let.params.join(", ")})`;
    w.out += " = ";
  }
  w.block(stmt.body);
  return { text: w.out, spans: w.spans, holes: w.holes };
}

/** Shorthand for the text alone. */
export const writeText = (stmt: Stmt) => write(stmt).text;

const isCh = (a: Atom | undefined, c?: string): a is Atom & { k: "ch" } => a?.k === "ch" && (c === undefined || a.c === c);

/** Is the `-` at `j` a subtraction (something to subtract from on its left) rather than a negation? */
export function binaryMinus(b: Block, j: number): boolean {
  const p = b[j - 1];
  return !!p && !(isCh(p) && "+-*".includes(p.c));
}

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
  if (factor.length === 1 && (factor[0]!.k === "call" || factor[0]!.k === "paren" || factor[0]!.k === "matrix")) return true;
  if (factor.length === 0 || !factor.every((a) => isCh(a))) return false;
  const s = factor.map((a) => (a as { c: string }).c).join("");
  return /^[0-9]*\.?[0-9]+$/.test(s) || /^%([0-9]+|%*)$/.test(s) || (isIdStart(s[0]!) && Array.from(s).every(isIdChar));
}

/** The first character an atom writes, to decide whether it needs a space after what came before. */
function firstChar(a: Atom): string {
  switch (a.k) {
    case "ch": return a.c;
    case "call": return a.name[0] ?? "";
    case "sup": return "^";
    case "matrix": return "[";
    default: return "(";
  }
}

class Writer {
  out = "";
  spans = new Map<Atom, { start: number; end: number }>();
  holes = 0;

  block(b: Block) {
    if (b.length === 0) { this.holes++; return; }
    b.forEach((a, j) => {
      // characters of one run are written as they are (`xy` is one name); anywhere else, a space
      // where the two sides would lex as one (`x sin(y)`, `x^n y`)
      if (j > 0 && !(isCh(a) && isCh(b[j - 1])) && merges(this.out, firstChar(a))) this.out += " ";
      const start = this.out.length;
      this.atom(a, b, j);
      this.spans.set(a, { start, end: this.out.length });
    });
  }

  /** A slot that must read as one `unary` (a denominator, an exponent). */
  private tight(b: Block) {
    // a negation could go bare (`x^-2` is the engine's x^(-2)) but reads better in parentheses
    if (b.length > 0 && singleUnary(b) && !isCh(b[0], "-")) this.block(b);
    else { this.out += "("; this.block(b); this.out += ")"; }
  }

  private atom(a: Atom, b: Block, j: number) {
    switch (a.k) {
      // a sum or difference is written the way people type it, `x + 1`; a negation stays `-x`
      case "ch": this.out += a.c === "+" || (a.c === "-" && binaryMinus(b, j)) ? ` ${a.c} ` : a.c; return;
      case "frac": {
        // bare only where nothing on the left would join the numerator and no power follows
        const p = b[j - 1];
        const bare = b[j + 1]?.k !== "sup" && (!p || isCh(p, "+") || (isCh(p, "-") && binaryMinus(b, j - 1)));
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
      case "call":
        this.out += a.name + "(";
        a.args.forEach((x, i) => { if (i) this.out += ", "; this.block(x); });
        this.out += ")";
        return;
      case "matrix":
        this.out += "[";
        a.rows.forEach((r, i) => {
          if (i) this.out += "; ";
          r.forEach((x, k) => { if (k) this.out += ", "; this.block(x); });
        });
        this.out += "]";
        return;
    }
  }
}
