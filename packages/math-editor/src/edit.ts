import { type Atom, type Block, type Stmt, ch, chars, isAsciiAlpha, isDigit, isIdChar } from "./model.js";
import { slots } from "./notation.js";
import { BUILTIN_FUNCTIONS, lex, ungroup } from "./read.js";
import { binaryMinus, write } from "./write.js";

/**
 * Editing the tree: a caret, the moves, and what each key does. No DOM here: the view (`view.ts`)
 * turns keys into these calls and draws the result.
 *
 * Typing the raw syntax still works: `diff(` opens d/dx with the caret in the body, `,` moves to the
 * next argument (adding one past the last), `)` leaves the call, `[1,2;3,4]` builds the matrix entry
 * by entry, `/` makes a fraction of what the engine would put in its numerator. `\name` then space
 * inserts a symbol or a template (`\frac`, `\sqrt`, `\int`, `\dint`, `\sum`, `\diff`, `\mat2x3`,
 * `\vec3`, `\abs`, `\norm`, `\T`, `\det`, `\dot`) with holes to fill.
 */

export interface Caret { block: Block; i: number }
/** Where a block sits: the atom it is a slot of, and where that atom sits. */
export interface Where { atom: Atom; parent: Block; index: number; slot: number }

/** Symbols the `\` commands insert by default; the notebook passes its own table. */
export const DEFAULT_SYMBOLS: Record<string, string> = {
  pi: "π", e: "ℯ", alpha: "α", beta: "β", gamma: "γ", delta: "δ", eps: "ε", epsilon: "ε", theta: "θ", mu: "μ",
  sigma: "σ", tau: "τ", phi: "φ", psi: "ψ", omega: "ω", Gamma: "Γ", Delta: "Δ", Sigma: "Σ", Omega: "Ω",
};

const call = (name: string, n: number): Atom => ({ k: "call", name, args: Array.from({ length: n }, () => []) });
const grid = (r: number, c: number): Atom => ({ k: "matrix", rows: Array.from({ length: r }, () => Array.from({ length: c }, () => [])) });

/** The structural `\` commands. A size follows some: `\mat2x3`, `\vec3`. */
export const TEMPLATES: Record<string, { what: string; make: (r?: number, c?: number) => Atom }> = {
  frac: { what: "fraction", make: () => ({ k: "frac", num: [], den: [] }) },
  sqrt: { what: "square root", make: () => call("sqrt", 1) },
  abs: { what: "absolute value", make: () => call("abs", 1) },
  norm: { what: "norm", make: () => call("norm", 1) },
  conj: { what: "complex conjugate", make: () => call("conj", 1) },
  diff: { what: "derivative d/dx", make: () => call("diff", 2) },
  dd: { what: "derivative d/dx", make: () => call("diff", 2) },
  int: { what: "integral", make: () => call("integrate", 2) },
  dint: { what: "definite integral", make: () => call("integrate", 4) },
  sum: { what: "sum", make: () => call("sum", 4) },
  det: { what: "determinant", make: () => call("det", 1) },
  T: { what: "transpose", make: () => call("transpose", 1) },
  dot: { what: "dot product", make: () => call("dot", 2) },
  mat: { what: "matrix (\\mat2x3)", make: (r = 2, c = r) => grid(r, c) },
  vec: { what: "column vector (\\vec3)", make: (r = 2) => grid(r, 1) },
};

/** How many argument slots a call opens with when typed as `name(`. */
const ARITY: Record<string, number> = { diff: 2, integrate: 2, sum: 4, dot: 2, subst: 3 };

export class MathEdit {
  caret: Caret;
  /** Functions the session defined: `f(` after `let f(x) = …` is a call. */
  known: readonly string[];
  symbols: Record<string, string>;
  constructor(public stmt: Stmt, opts: { known?: readonly string[]; symbols?: Record<string, string> } = {}) {
    this.caret = { block: stmt.body, i: stmt.body.length };
    this.known = opts.known ?? [];
    this.symbols = opts.symbols ?? DEFAULT_SYMBOLS;
  }

  get root(): Block { return this.stmt.body; }
  get text(): string { return write(this.stmt).text; }

  /** Where `b` sits in the tree, or null for the root. */
  where(b: Block, from: Block = this.root): Where | null {
    for (let index = 0; index < from.length; index++) {
      const atom = from[index]!;
      const ss = slots(atom);
      for (let slot = 0; slot < ss.length; slot++) {
        if (ss[slot] === b) return { atom, parent: from, index, slot };
        const w = this.where(b, ss[slot]!);
        if (w) return w;
      }
    }
    return null;
  }

  /** The caret's block and its ancestors, innermost first, each with where it sits. */
  private *ancestors(): Generator<{ block: Block; w: Where }> {
    let b = this.caret.block;
    for (let w = this.where(b); w; b = w.parent, w = this.where(b)) yield { block: b, w };
  }

  // --- moves -------------------------------------------------------------------------------------

  right(): boolean {
    const { block: b, i } = this.caret;
    if (i < b.length) {
      const s = slots(b[i]!);
      this.caret = s.length ? { block: s[0]!, i: 0 } : { block: b, i: i + 1 };
      return true;
    }
    const w = this.where(b);
    if (!w) return false;
    const s = slots(w.atom);
    this.caret = w.slot + 1 < s.length ? { block: s[w.slot + 1]!, i: 0 } : { block: w.parent, i: w.index + 1 };
    return true;
  }

  left(): boolean {
    const { block: b, i } = this.caret;
    if (i > 0) {
      const s = slots(b[i - 1]!);
      const last = s[s.length - 1];
      this.caret = last ? { block: last, i: last.length } : { block: b, i: i - 1 };
      return true;
    }
    const w = this.where(b);
    if (!w) return false;
    const s = slots(w.atom);
    this.caret = w.slot > 0 ? { block: s[w.slot - 1]!, i: s[w.slot - 1]!.length } : { block: w.parent, i: w.index };
    return true;
  }

  /** Up (−1) or down (1) between a fraction's parts, a matrix's rows, a bound's top and bottom, and
   *  into or out of an exponent. False when there is nowhere to go (the notebook moves to the
   *  neighbouring cell). */
  vertical(dir: -1 | 1): boolean {
    for (const { block: b, w } of this.ancestors()) {
      const a = w.atom;
      let target: Block | undefined;
      if (a.k === "frac") target = dir < 0 ? (b === a.den ? a.num : undefined) : (b === a.num ? a.den : undefined);
      else if (a.k === "matrix") {
        const r = a.rows.findIndex((row) => row.includes(b));
        target = a.rows[r + dir]?.[a.rows[r]!.indexOf(b)];
      } else if (a.k === "call" && a.args.length === 4 && (a.name === "integrate" || a.name === "sum")) {
        // below: ∫'s lower bound, Σ's k = a; above: the upper bound
        const below = a.name === "integrate" ? [a.args[2]] : [a.args[1], a.args[2]];
        if (dir < 0 && below.includes(b)) target = a.args[3];
        if (dir > 0 && b === a.args[3]) target = a.args[2];
      } else if (a.k === "sup" && dir > 0) { this.caret = { block: w.parent, i: w.index + 1 }; return true; }
      if (target) {
        this.caret = { block: target, i: b === this.caret.block ? Math.min(this.caret.i, target.length) : target.length };
        return true;
      }
    }
    if (dir < 0) {
      const { block: b, i } = this.caret;
      const next = b[i], prev = b[i - 1];
      if (next?.k === "sup") { this.caret = { block: next.exp, i: 0 }; return true; }
      if (prev?.k === "sup") { this.caret = { block: prev.exp, i: prev.exp.length }; return true; }
    }
    return false;
  }

  /** The next (1) or previous (−1) empty slot, wrapping around; false when there is none. */
  hole(dir: -1 | 1): boolean {
    const start = this.caret;
    const step = () => (dir > 0 ? this.right() : this.left());
    for (let lap = 0; lap < 2; lap++) {
      while (step()) if (this.caret.block.length === 0 && this.caret.block !== start.block) return true;
      if (dir > 0) this.home(); else this.end();
      if (this.caret.block.length === 0 && this.caret.block !== start.block) return true;
    }
    this.caret = start;
    return false;
  }

  home() { this.caret = { block: this.root, i: 0 }; }
  end() { this.caret = { block: this.root, i: this.root.length }; }

  // --- typing ------------------------------------------------------------------------------------

  /** Just after a symbol a `\` command put in: a letter typed here is a product, not more of the
   *  name (`\pi r` is π·r; `πr` would be one name, as Greek letters are name characters). */
  private glue: Caret | null = null;

  /** One typed character. False when it means nothing here (and nothing changed). */
  type(c: string): boolean {
    const g = this.glue;
    this.glue = null;
    if (g && g.block === this.caret.block && g.i === this.caret.i && isIdChar(c)) this.insert(ch(" "));
    // anything but a letter or digit finishes a `\` command (a space is used up doing it)
    if (!/^[A-Za-z0-9]$/.test(c) && this.command() && c === " ") return true;
    switch (c) {
      case "/": return this.fraction();
      case "^": return this.power();
      case "(": return this.open();
      case ")": return this.close((a) => a.k === "paren" || a.k === "call");
      case "[": return this.insert(grid(1, 1));
      case "]": return this.close((a) => a.k === "matrix");
      case ",": return this.comma();
      case ";": return this.semicolon();
      case " ": return this.space();
    }
    if (isIdChar(c) || "+-*%.\\".includes(c)) return this.insert(ch(c));
    return false;
  }

  /** Put an atom at the caret; a structure takes the caret into its first slot — the first
   *  argument (as typed, `integrate(` then the integrand) or with `onScreen` the first slot on
   *  screen (a `\dint` template fills its bounds first). */
  insert(a: Atom, onScreen = false): boolean {
    const { block: b, i } = this.caret;
    b.splice(i, 0, a);
    const s = a.k === "call" && !onScreen ? a.args : slots(a);
    this.caret = s.length ? { block: s[0]!, i: 0 } : { block: b, i: i + 1 };
    return true;
  }

  /** `/`: the numerator is what the engine would put there — back to a `+` or a subtraction. */
  private fraction(): boolean {
    const { block: b, i } = this.caret;
    let j = i;
    while (j > 0) {
      const a = b[j - 1]!;
      if (a.k === "ch" && (a.c === "+" || (a.c === "-" && binaryMinus(b, j - 1)))) break;
      j--;
    }
    const num = ungroup(b.splice(j, i - j));
    const frac: Atom = { k: "frac", num, den: [] };
    b.splice(j, 0, frac);
    this.caret = { block: num.length ? frac.den : frac.num, i: 0 };
    return true;
  }

  /** `^`: a power of the atom on the left (back into its exponent if it has one). */
  private power(): boolean {
    const { block: b, i } = this.caret;
    const prev = b[i - 1];
    if (prev?.k === "sup") { this.caret = { block: prev.exp, i: prev.exp.length }; return true; }
    // a fraction's power needs its parentheses, as in the text
    if (prev?.k === "frac") b[i - 1] = { k: "paren", body: [prev] };
    return this.insert({ k: "sup", exp: [] });
  }

  /** `(`: a call if the name before it is a function, else a group. */
  private open(): boolean {
    const { block: b, i } = this.caret;
    let j = i;
    while (j > 0 && b[j - 1]!.k === "ch" && isIdChar((b[j - 1] as { c: string }).c)) j--;
    const run = b.slice(j, i).map((a) => (a as { c: string }).c).join("");
    const last = run ? lex(run).filter((t) => t.kind !== "eof").pop() : undefined;
    if (last?.kind === "id" && last.stop === Array.from(run).length && (BUILTIN_FUNCTIONS.includes(last.s) || this.known.includes(last.s))) {
      const n = Array.from(last.s).length;
      b.splice(i - n, n);
      this.caret = { block: b, i: i - n };
      return this.insert(call(last.s, ARITY[last.s] ?? 1));
    }
    return this.insert({ k: "paren", body: [] });
  }

  /** `)` or `]`: out of the innermost enclosing group, call or matrix. A group that is the whole
   *  denominator or exponent (`(x+1)/(x-1)`, `x^(2n)`) was only there for the text: the bar or the
   *  raised position shows it, so its parentheses go, and the caret leaves the fraction or power
   *  too, as the text's `)` ended it. */
  private close(match: (a: Atom) => boolean): boolean {
    for (const { w } of this.ancestors()) {
      if (!match(w.atom)) continue;
      const a = w.atom, slot = w.parent, outer = this.where(slot);
      if (a.k === "paren" && slot.length === 1 && outer && ((outer.atom.k === "frac" && slot === outer.atom.den) || outer.atom.k === "sup")) {
        slot.splice(0, 1, ...a.body);
        this.caret = { block: outer.parent, i: outer.index + 1 };
        return true;
      }
      this.caret = { block: w.parent, i: w.index + 1 };
      return true;
    }
    return false;
  }

  /** `,`: the next argument or entry, making one past the last. */
  private comma(): boolean {
    for (const { block: b, w } of this.ancestors()) {
      const a = w.atom;
      if (a.k === "call") {
        const k = a.args.indexOf(b);
        if (k + 1 >= a.args.length) a.args.push([]);
        this.caret = { block: a.args[k + 1]!, i: 0 };
        return true;
      }
      if (a.k === "matrix") {
        const r = a.rows.findIndex((row) => row.includes(b));
        const c = a.rows[r]!.indexOf(b);
        if (c + 1 >= a.rows[r]!.length) for (const row of a.rows) row.push([]);
        this.caret = { block: a.rows[r]![c + 1]!, i: 0 };
        return true;
      }
    }
    return false;
  }

  /** `;`: a new matrix row below this one. */
  private semicolon(): boolean {
    for (const { block: b, w } of this.ancestors()) {
      const a = w.atom;
      if (a.k !== "matrix") continue;
      const r = a.rows.findIndex((row) => row.includes(b));
      const row: Block[] = Array.from({ length: a.rows[r]!.length }, () => []);
      a.rows.splice(r + 1, 0, row);
      this.caret = { block: row[0]!, i: 0 };
      return true;
    }
    return false;
  }

  /** After a name or numeral a space is the product (`x y`); elsewhere it means nothing. */
  private space(): boolean {
    if (this.pendingCommand()) return false;   // an unknown `\name` stays as typed, to be fixed
    const prev = this.caret.block[this.caret.i - 1];
    return prev?.k === "ch" && isIdChar(prev.c) ? this.insert(ch(" ")) : false;
  }

  /** The `\name` just before the caret, if there is one: its text and where it starts. */
  pendingCommand(): { name: string; start: number } | null {
    const { block: b, i } = this.caret;
    let j = i;
    while (j > 0 && b[j - 1]!.k === "ch" && (isAsciiAlpha((b[j - 1] as { c: string }).c) || isDigit((b[j - 1] as { c: string }).c))) j--;
    const bs = b[j - 1];
    if (!(bs?.k === "ch" && bs.c === "\\")) return null;
    return { name: b.slice(j, i).map((a) => (a as { c: string }).c).join(""), start: j - 1 };
  }

  /** Replace a finished `\name` with its symbol or template. False when there is none (or no such name). */
  command(): boolean {
    const p = this.pendingCommand();
    if (!p) return false;
    const { block: b, i } = this.caret;
    const sym = this.symbols[p.name];
    const m = /^([A-Za-z]+?)(\d+)?(?:x(\d+))?$/.exec(p.name);
    const t = m && TEMPLATES[m[1]!];
    if (!sym && !t) return false;
    b.splice(p.start, i - p.start);
    this.caret = { block: b, i: p.start };
    if (sym) {
      b.splice(p.start, 0, ...chars(sym));
      this.caret.i += Array.from(sym).length;
      this.glue = { ...this.caret };
      return true;
    }
    return this.insert(t!.make(m![2] ? +m![2] : undefined, m![3] ? +m![3] : undefined), true);
  }

  // --- deleting ----------------------------------------------------------------------------------

  /** Backspace: a character goes; a structure is entered from its end, and goes once it is empty. At
   *  the start of a group or a one-argument call the wrapper goes and its contents stay. */
  backspace(): boolean {
    const { block: b, i } = this.caret;
    if (i > 0) {
      const a = b[i - 1]!;
      const s = slots(a);
      if (s.every((x) => x.length === 0)) { b.splice(i - 1, 1); this.caret = { block: b, i: i - 1 }; return true; }
      const last = s[s.length - 1]!;
      this.caret = { block: last, i: last.length };
      return true;
    }
    const w = this.where(b);
    if (!w) return false;
    const s = slots(w.atom);
    if (s.every((x) => x.length === 0) || (w.slot === 0 && (w.atom.k === "paren" || (w.atom.k === "call" && s.length === 1)))) {
      w.parent.splice(w.index, 1, ...s.flat());
      this.caret = { block: w.parent, i: w.index };
      return true;
    }
    this.caret = w.slot > 0 ? { block: s[w.slot - 1]!, i: s[w.slot - 1]!.length } : { block: w.parent, i: w.index };
    return true;
  }

  /** Delete: the character after the caret; a structure is entered from its start, and goes once empty. */
  deleteForward(): boolean {
    const { block: b, i } = this.caret;
    const a = b[i];
    if (!a) return false;
    const s = slots(a);
    if (s.every((x) => x.length === 0)) { b.splice(i, 1); return true; }
    this.caret = { block: s[0]!, i: 0 };
    return true;
  }
}
