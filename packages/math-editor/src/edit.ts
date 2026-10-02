import { type Atom, type Block, type Stmt, ch, chars, isAsciiAlpha, isDigit, isIdChar } from "./model.js";
import { notated, slots } from "./notation.js";
import { BUILTIN_FUNCTIONS, lex, read, ungroup } from "./read.js";
import { binaryMinus, write, writeText } from "./write.js";

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
/** A selection: atoms `start` to `end` (exclusive) of one block. */
export interface Selection { block: Block; start: number; end: number }
/** A caret as indices from the root (atom, slot, …, then the position), to survive a tree replaced by undo. */
interface CaretPath { steps: [number, number][]; i: number }
interface Snapshot { json: string; caret: CaretPath }
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
export const TEMPLATES: Record<string, { what: string; glyph: string; make: (r?: number, c?: number) => Atom }> = {
  frac: { what: "fraction", glyph: "a⁄b", make: () => ({ k: "frac", num: [], den: [] }) },
  sqrt: { what: "square root", glyph: "√", make: () => call("sqrt", 1) },
  abs: { what: "absolute value", glyph: "|x|", make: () => call("abs", 1) },
  norm: { what: "norm", glyph: "‖v‖", make: () => call("norm", 1) },
  conj: { what: "complex conjugate", glyph: "z̄", make: () => call("conj", 1) },
  diff: { what: "derivative", glyph: "d/dx", make: () => call("diff", 2) },
  dd: { what: "derivative", glyph: "d/dx", make: () => call("diff", 2) },
  int: { what: "integral", glyph: "∫", make: () => call("integrate", 2) },
  dint: { what: "definite integral", glyph: "∫ₐᵇ", make: () => call("integrate", 4) },
  sum: { what: "sum", glyph: "Σ", make: () => call("sum", 4) },
  det: { what: "determinant", glyph: "|A|", make: () => call("det", 1) },
  T: { what: "transpose", glyph: "Mᵀ", make: () => call("transpose", 1) },
  dot: { what: "dot product", glyph: "u·v", make: () => call("dot", 2) },
  mat: { what: "matrix, \\mat2x3 for 2×3", glyph: "[ ]", make: (r = 2, c = r) => grid(r, c) },
  vec: { what: "column vector, \\vec3 for 3", glyph: "[⋮]", make: (r = 2) => grid(r, 1) },
};

/** Does the atom before a `[[` end a value a part can be taken of: a name or numeral, a call, a group,
 *  a matrix, an output reference, another part? */
const valueEnds = (a: Atom | undefined): boolean =>
  !!a && (a.k === "ch" ? isIdChar(a.c) || a.c === "%" : a.k === "call" || a.k === "paren" || a.k === "matrix" || a.k === "part");

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

  /** The other end of the selection, when there is one (the caret is the end that moves). */
  anchor: Caret | null = null;

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

  // --- undo --------------------------------------------------------------------------------------

  private undoStack: Snapshot[] = [];
  private redoStack: Snapshot[] = [];
  /** What the last edit was, while the caret has not moved since: a run of typed letters or of
   *  deletions is one step to undo. */
  private run: "type" | "delete" | null = null;
  private depth = 0;

  private pathOf(c: Caret): CaretPath {
    const steps: [number, number][] = [];
    let b = c.block;
    for (let w = this.where(b); w; b = w.parent, w = this.where(b)) steps.unshift([w.index, w.slot]);
    return { steps, i: c.i };
  }
  private caretAtPath(p: CaretPath): Caret {
    let b = this.root;
    for (const [index, slot] of p.steps) {
      const s = b[index] && slots(b[index]!)[slot];
      if (!s) return { block: b, i: b.length };
      b = s;
    }
    return { block: b, i: Math.min(p.i, b.length) };
  }
  private snapshot(): Snapshot { return { json: JSON.stringify(this.stmt), caret: this.pathOf(this.caret) }; }
  /** Put a snapshot back into the same objects (the view and the notebook hold on to them). */
  private restore(snap: Snapshot) {
    const st = JSON.parse(snap.json) as Stmt;
    this.stmt.body.splice(0, this.stmt.body.length, ...st.body);
    this.caret = this.caretAtPath(snap.caret);
    this.anchor = null;
    this.run = null;
  }

  /** Run an edit as one undo step; `changed` false (or a tree that came out the same) records nothing. */
  private mutate(kind: "type" | "delete" | "struct", fn: () => boolean): boolean {
    if (this.depth > 0) return fn();
    const coalesce = kind !== "struct" && this.run === kind && !this.anchor;
    const snap = coalesce ? null : this.snapshot();
    this.depth++;
    let changed: boolean;
    try { changed = fn(); } finally { this.depth--; }
    if (!changed || (snap && JSON.stringify(this.stmt) === snap.json)) return changed;
    if (snap) { this.undoStack.push(snap); if (this.undoStack.length > 500) this.undoStack.shift(); }
    this.redoStack = [];
    this.run = kind === "struct" ? null : kind;
    return true;
  }

  undo(): boolean {
    const snap = this.undoStack.pop();
    if (!snap) return false;
    this.redoStack.push(this.snapshot());
    this.restore(snap);
    return true;
  }
  redo(): boolean {
    const snap = this.redoStack.pop();
    if (!snap) return false;
    this.undoStack.push(this.snapshot());
    this.restore(snap);
    return true;
  }
  /** The caret was put somewhere by other means (a click): the next edit is a step of its own. */
  moved() { this.run = null; }

  // --- selection ---------------------------------------------------------------------------------

  /** Positions from the root down to `c`: at each level the block and the index in it (of the atom
   *  holding the level below, or the caret itself at the last level). */
  private chain(c: Caret): { block: Block; i: number }[] {
    const out = [{ block: c.block, i: c.i }];
    let b = c.block;
    for (let w = this.where(b); w; b = w.parent, w = this.where(b)) out.unshift({ block: w.parent, i: w.index });
    return out;
  }

  /** The selected atoms: the smallest block holding both ends, from the one end to the other, whole
   *  atoms wherever an end is inside one. */
  selection(): Selection | null {
    if (!this.anchor) return null;
    const a = this.chain(this.anchor), c = this.chain(this.caret);
    let k = 0;
    while (k + 1 < a.length && k + 1 < c.length && a[k + 1]!.block === c[k + 1]!.block) k++;
    const block = a[k]!.block;
    const span = (ch: { i: number }[]) => (ch.length > k + 1 ? [ch[k]!.i, ch[k]!.i + 1] : [ch[k]!.i, ch[k]!.i]);
    const [s1, e1] = span(a), [s2, e2] = span(c);
    const start = Math.min(s1!, s2!), end = Math.max(e1!, e2!);
    return start < end ? { block, start, end } : null;
  }
  /** Start a selection at the caret if there is none (Shift held while moving). */
  extend() { if (!this.anchor) this.anchor = { ...this.caret }; }
  /** Drop the selection; with `toward`, the caret goes to that end of it first (← and → on a selection). */
  collapse(toward?: -1 | 1): boolean {
    const s = this.selection();
    this.anchor = null;
    if (!s || !toward) return false;
    this.caret = { block: s.block, i: toward < 0 ? s.start : s.end };
    this.run = null;
    return true;
  }
  selectAll() { this.anchor = { block: this.root, i: 0 }; this.caret = { block: this.root, i: this.root.length }; }
  /** The selection as source text (what Copy puts on the clipboard). */
  selectedText(): string {
    const s = this.selection();
    return s ? writeText({ body: s.block.slice(s.start, s.end) }) : "";
  }
  /** Remove the selected atoms; the caret goes where they were. */
  deleteSelection(): boolean {
    const s = this.selection();
    this.anchor = null;
    if (!s) return false;
    return this.mutate("struct", () => {
      s.block.splice(s.start, s.end - s.start);
      this.caret = { block: s.block, i: s.start };
      return true;
    });
  }

  /** The innermost call around the caret that shows as `name(args)` — a command, or a function the
   *  session defined — with the argument the caret is in (for signature help). Calls drawn in their
   *  own notation show their slots already. */
  callContext(): { name: string; arg: number; firstArg: string } | null {
    for (const { block, w } of this.ancestors()) {
      const a = w.atom;
      if (a.k !== "call" || notated(a)) continue;
      return { name: a.name, arg: a.args.indexOf(block), firstArg: writeText({ body: a.args[0] ?? [] }) };
    }
    return null;
  }

  // --- moves -------------------------------------------------------------------------------------

  right(): boolean {
    this.run = null;
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
    this.run = null;
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
    this.run = null;
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

  /** An empty slot, or the body of a `let` head that has none yet. */
  private atHole(c: Caret, from: Caret): boolean {
    if (c.block === from.block && c.i === from.i) return false;
    return c.block.length === 0 ? c.block !== from.block : c.i === c.block.length && c.block[c.i - 1]?.k === "let";
  }

  /** The next (1) or previous (−1) empty slot, wrapping around; false when there is none. */
  hole(dir: -1 | 1): boolean {
    const start = this.caret;
    const step = () => (dir > 0 ? this.right() : this.left());
    for (let lap = 0; lap < 2; lap++) {
      while (step()) if (this.atHole(this.caret, start)) return true;
      if (dir > 0) this.home(); else this.end();
      if (this.atHole(this.caret, start)) return true;
    }
    this.caret = start;
    return false;
  }

  home() { this.run = null; this.caret = { block: this.root, i: 0 }; }
  end() { this.run = null; this.caret = { block: this.root, i: this.root.length }; }

  // --- typing ------------------------------------------------------------------------------------

  /** Just after a symbol a `\` command put in: a letter typed here is a product, not more of the
   *  name (`\pi r` is π·r; `πr` would be one name, as Greek letters are name characters). */
  private glue: Caret | null = null;

  /** One typed character. False when it means nothing here (and nothing changed). With a selection,
   *  `/` makes it a numerator, `(` puts it in parentheses, and `@` puts it in parentheses with a box
   *  in front for a function's name; anything else replaces it. */
  type(c: string): boolean {
    const sel = this.selection();
    if (sel && (c === "/" || c === "(" || c === "@")) {
      this.anchor = null;
      return this.mutate("struct", () => {
        const atoms = sel.block.splice(sel.start, sel.end - sel.start);
        const a: Atom = c === "/" ? { k: "frac", num: ungroup(atoms), den: [] } : { k: "paren", body: atoms, ...(c === "@" ? { head: true } : {}) };
        sel.block.splice(sel.start, 0, a);
        // `@` leaves the caret in front, for the function's name (Mathematica's prefix `f@x`)
        this.caret = c === "/" ? { block: (a as { den: Block }).den, i: 0 } : { block: sel.block, i: sel.start + (c === "@" ? 0 : 1) };
        return true;
      });
    }
    if (sel) return this.mutate("struct", () => { this.deleteSelection(); this.typeOne(c); return true; });
    return this.mutate(isIdChar(c) ? "type" : "struct", () => this.typeOne(c));
  }

  private typeOne(c: string): boolean {
    const hw = this.where(this.caret.block);
    if (hw?.atom.k === "let") return this.typeInHead(c, hw.atom, hw);
    if (hw?.atom.k === "part") return this.typeInPart(c, hw.atom, hw);
    // in quotes every character is the text's; the closing quote leaves it
    if (hw?.atom.k === "str") {
      if (c === '"') { this.caret = { block: hw.parent, i: hw.index + 1 }; return true; }
      if (c.length !== 1 || c === "\n") return false;
      this.caret.block.splice(this.caret.i, 0, ch(c));
      this.caret = { block: this.caret.block, i: this.caret.i + 1 };
      return true;
    }
    if (c === " " && this.startHead()) return true;
    const g = this.glue;
    this.glue = null;
    if (g && g.block === this.caret.block && g.i === this.caret.i && isIdChar(c)) this.insert(ch(" "));
    // anything but a letter or digit finishes a `\` command (a space is used up doing it)
    if (!/^[A-Za-z0-9]$/.test(c) && this.command() && c === " ") return true;
    // `.` then `/` or `*` is an entrywise operator, one atom: the engine lexes `./` so even after a digit
    const dot = this.caret.block[this.caret.i - 1];
    if ((c === "/" || c === "*") && dot?.k === "ch" && dot.c === ".") {
      this.caret.block.splice(this.caret.i - 1, 1, ch("." + c));
      return true;
    }
    switch (c) {
      case "/": return this.fraction();
      case "^": return this.power();
      case "(": return this.open();
      case ")": return this.close((a) => a.k === "paren" || a.k === "call");
      case "[": {
        // `[[` after a value: the empty matrix the first `[` made becomes a part, `x[[`
        if (hw?.atom.k === "matrix" && hw.atom.rows.length === 1 && hw.atom.rows[0]!.length === 1 && !this.caret.block.length && valueEnds(hw.parent[hw.index - 1])) {
          const part: Atom = { k: "part", specs: [[]] };
          hw.parent.splice(hw.index, 1, part);
          this.caret = { block: part.specs[0]!, i: 0 };
          return true;
        }
        return this.insert(grid(1, 1));
      }
      // the second `]` of a part's `]]`, after the first left it
      case "]": return this.caret.block[this.caret.i - 1]?.k === "part" ? true : this.close((a) => a.k === "matrix");
      case ",": return this.comma();
      case '"': return this.insert({ k: "str", body: [] });
      case ";": return this.semicolon();
      case " ": return this.space();
      case "@": {
        // with nothing selected, an empty group to name a function in front of
        this.caret.block.splice(this.caret.i, 0, { k: "paren", body: [], head: true });
        return true;
      }
    }
    if (isIdChar(c) || "+-*%.\\".includes(c)) return this.insert(ch(c));
    return false;
  }

  /** Typing in an index of a part: its characters as typed. `,` goes on to the next index (outside a
   *  list's braces and a quoted name) and `]` leaves the part; within quotes every character is the
   *  name's. */
  private typeInPart(c: string, part: Atom & { k: "part" }, w: Where): boolean {
    const b = this.caret.block, i = this.caret.i;
    const before = b.slice(0, i).map((a) => (a.k === "ch" ? a.c : "")).join("");
    const quoted = (before.match(/"/g)?.length ?? 0) % 2 === 1;
    const put = () => { b.splice(i, 0, ch(c)); this.caret = { block: b, i: i + 1 }; return true; };
    if (quoted) return c.length === 1 && c !== "\n" ? put() : false;
    const braces = (before.match(/\{/g)?.length ?? 0) - (before.match(/\}/g)?.length ?? 0);
    if (c === "," && braces <= 0) {
      const k = part.specs.indexOf(b);
      part.specs.splice(k + 1, 0, b.splice(i));
      this.caret = { block: part.specs[k + 1]!, i: 0 };
      return true;
    }
    if (c === "]") { this.caret = { block: w.parent, i: w.index + 1 }; return true; }
    if (c === " ") return true;   // spaces in an index mean nothing outside a name in quotes
    return isIdChar(c) || '-+;{},".'.includes(c) ? put() : false;
  }

  /** `let` then a space at the start of the input: the head, with the caret in its name. */
  private startHead(): boolean {
    const { block, i } = this.caret;
    const word = block.slice(0, 3).map((a) => (a.k === "ch" ? a.c : "")).join("");
    if (block !== this.root || i !== 3 || word !== "let") return false;
    const head: Atom = { k: "let", name: [], params: null };
    block.splice(0, 3, head);
    this.caret = { block: head.name, i: 0 };
    return true;
  }

  /** Typing in a `let` head: a name's characters; `(` opens the parameters and `,` adds one; a space,
   *  `=` or `)` go on to the body. */
  private typeInHead(c: string, head: Atom & { k: "let" }, w: Where): boolean {
    const b = this.caret.block;
    const body = () => { this.caret = { block: w.parent, i: w.index + 1 }; return true; };
    if (isIdChar(c)) { b.splice(this.caret.i, 0, ch(c)); this.caret = { block: b, i: this.caret.i + 1 }; return true; }
    if (b === head.name) {
      if (c === "(") { head.params ??= [[]]; this.caret = { block: head.params[0]!, i: 0 }; return true; }
      return (c === " " || c === "=") && b.length > 0 ? body() : false;
    }
    if (c === ",") {
      const ps = head.params!, k = ps.indexOf(b);
      if (k + 1 >= ps.length) ps.push([]);
      this.caret = { block: ps[k + 1]!, i: 0 };
      return true;
    }
    return c === ")" || c === "=" ? body() : false;
  }

  /** Put an atom at the caret; a structure takes the caret into its first slot — the first
   *  argument (as typed, `integrate(` then the integrand) or with `onScreen` the first slot on
   *  screen (a `\dint` template fills its bounds first). */
  insert(a: Atom, onScreen = false): boolean {
    return this.mutate("struct", () => { if (this.selection()) this.deleteSelection(); return this.insertOne(a, onScreen); });
  }
  private insertOne(a: Atom, onScreen: boolean): boolean {
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
      if (a.k === "let" || (a.k === "ch" && (a.c === "+" || (a.c === "-" && binaryMinus(b, j - 1))))) break;
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

  /** `(`: a call if the name before it is a function, else a group. Typed before existing atoms,
   *  it takes them all in, as `(` does in the text, with its `)` left open until one is typed:
   *  `expand(` in front of `(x+5)(2x+3)` wraps the product. */
  private open(): boolean {
    const { block: b, i } = this.caret;
    const f = this.fnBefore(b, i);
    if (f) {
      const n = f.n;
      b.splice(i - n, n);
      this.caret = { block: b, i: i - n };
      const c = call(f.name, ARITY[f.name] ?? 1) as Atom & { k: "call" };
      const rest = b.splice(this.caret.i);
      if (rest.length) { c.args[0] = rest; c.open = true; }
      return this.insert(c);
    }
    const rest = b.splice(i);
    return this.insert(rest.length ? { k: "paren", body: rest, open: true } : { k: "paren", body: [] });
  }

  /** Whether the atom before `i` in `b` is a name's character. */
  private nameAt(b: Block, i: number): boolean {
    const p = b[i - 1];
    return p?.k === "ch" && isIdChar(p.c);
  }

  /** The function name that ends at `i` in `b`, as the text lexes it (`2sin` ends in `sin`), with
   *  its length; null when what ends there is not a name, or names no function. */
  private fnBefore(b: Block, i: number): { name: string; n: number } | null {
    let j = i;
    while (j > 0 && b[j - 1]!.k === "ch" && isIdChar((b[j - 1] as { c: string }).c)) j--;
    const run = b.slice(j, i).map((a) => (a as { c: string }).c).join("");
    const last = run ? lex(run).filter((t) => t.kind !== "eof").pop() : undefined;
    // a function's own body may call it: `let f(n) = … f(n - 1)`
    const head = this.root[0]?.k === "let" && this.root[0].params ? this.root[0].name.map((a) => (a as { c: string }).c).join("") : null;
    if (last?.kind !== "id" || last.stop !== Array.from(run).length) return null;
    if (!(BUILTIN_FUNCTIONS.includes(last.s) || this.known.includes(last.s) || last.s === head)) return null;
    return { name: last.s, n: Array.from(last.s).length };
  }

  /** A function's name typed in front of a group (`norm` before `(v/2)`) makes it the function's
   *  call, as the text reads it. Not while the caret is in or at the end of the name, where the name
   *  may still be growing (`sin` into `sinh`, `N` into `norm`); `all` settles those too (the input
   *  is left). The caret and the selection's anchor keep their places. True if anything changed. */
  settle(all = false, b: Block = this.root): boolean {
    let changed = false;
    for (let j = 0; j < b.length; j++) {
      const a = b[j]!;
      for (const x of slots(a)) changed = this.settle(all, x) || changed;
      if (a.k !== "paren" || a.open) continue;
      let start = j;
      while (start > 0 && this.nameAt(b, start)) start--;
      if (!all && this.caret.block === b && this.caret.i >= start && this.caret.i <= j) continue;
      if (a.head) { delete a.head; changed = true; }
      const f = this.fnBefore(b, j);
      if (!f) continue;
      const at = j - f.n;
      b.splice(at, f.n + 1, { k: "call", name: f.name, args: [a.body] });
      for (const p of [this.caret, this.anchor]) {
        if (p?.block !== b || p.i <= at) continue;
        p.i = p.i > j ? p.i - f.n : at;
      }
      j = at;
      changed = true;
    }
    return changed;
  }

  /** Place every `)` still open (the input is left: the text had them all along). */
  closeAll(b: Block = this.root) {
    for (const a of b) {
      if ((a.k === "paren" || a.k === "call") && a.open) delete a.open;
      for (const s of slots(a)) this.closeAll(s);
    }
  }

  /** `)` or `]`: out of the innermost enclosing group, call or matrix. A group that is the whole
   *  denominator or exponent (`(x+1)/(x-1)`, `x^(2n)`) was only there for the text: the bar or the
   *  raised position shows it, so its parentheses go, and the caret leaves the fraction or power
   *  too, as the text's `)` ended it. */
  private close(match: (a: Atom) => boolean): boolean {
    let inner: Where | null = null;   // the level below, on the way up from the caret
    for (const { block: b, w } of this.ancestors()) {
      if (!match(w.atom)) { inner = w; continue; }
      const a = w.atom;
      // an open group ends where its `)` is typed: what follows goes back out after it
      if ((a.k === "paren" || a.k === "call") && a.open) {
        delete a.open;
        if (b === (a.k === "paren" ? a.body : a.args[a.args.length - 1])) {
          const cut = b === this.caret.block ? this.caret.i : inner!.index + 1;
          w.parent.splice(w.index + 1, 0, ...b.splice(cut));
        }
        this.caret = { block: w.parent, i: w.index + 1 };
        return true;
      }
      const slot = w.parent, outer = this.where(slot);
      if (a.k === "paren" && slot.length === 1 && outer && ((outer.atom.k === "frac" && slot === outer.atom.den) || outer.atom.k === "sup")) {
        slot.splice(0, 1, ...a.body);
        this.caret = { block: outer.parent, i: outer.index + 1 };
        return true;
      }
      this.caret = { block: w.parent, i: w.index + 1 };
      return true;
    }
    // `)` just after an open group places its `)` where it already is
    const prev = this.caret.block[this.caret.i - 1];
    if (prev && (prev.k === "paren" || prev.k === "call") && prev.open && match(prev)) { delete prev.open; return true; }
    return false;
  }

  /** `,`: the next argument or entry, making one past the last. */
  private comma(): boolean {
    for (const { block: b, w } of this.ancestors()) {
      const a = w.atom;
      if (a.k === "call") {
        // in the middle of an argument, what follows the caret starts the next one, as in the text
        const k = a.args.indexOf(b);
        const rest = b === this.caret.block ? b.splice(this.caret.i) : [];
        if (rest.length || k + 1 >= a.args.length) a.args.splice(k + 1, 0, rest);
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

  /** The name the caret is at the end of (not a `\name`, not inside a part's index), and where it
   *  starts: what a function name being typed would complete. */
  nameBefore(): { name: string; start: number } | null {
    const { block: b, i } = this.caret;
    if (this.where(b)?.atom.k === "part" || this.pendingCommand()) return null;
    const next = b[i];
    if (next?.k === "ch" && isIdChar(next.c)) return null;
    let j = i;
    while (j > 0 && b[j - 1]!.k === "ch" && isIdChar((b[j - 1] as { c: string }).c)) j--;
    // the run as the engine lexes it (`2pla` is 2·pla): its last token, if a name
    const run = b.slice(j, i).map((a) => (a as { c: string }).c).join("");
    const last = run ? lex(run).filter((t) => t.kind !== "eof").pop() : undefined;
    if (last?.kind !== "id" || last.stop !== Array.from(run).length || !/^[A-Za-z_]/.test(last.s)) return null;
    return { name: last.s, start: i - Array.from(last.s).length };
  }

  /** When the caret is in an index of a part: the cell's text up to the caret (as it will be written),
   *  and what is being typed there (a word, or a name from its opening quote). */
  partBefore(): { text: string; typed: string; start: number; quoted: boolean } | null {
    const { block: b, i } = this.caret;
    const w = this.where(b);
    if (w?.atom.k !== "part") return null;
    const part = w.atom;
    const span = write(this.stmt).spans.get(part);
    if (!span) return null;
    const chars = (x: Block) => x.map((a) => (a.k === "ch" ? a.c : "")).join("");
    const k = part.specs.indexOf(b);
    const here = chars(b.slice(0, i));
    const text = writeText(this.stmt).slice(0, span.start) + "[[" + part.specs.slice(0, k).map(chars).map((x) => x + ", ").join("") + here;
    const q = here.lastIndexOf('"');
    const quoted = (here.match(/"/g)?.length ?? 0) % 2 === 1;
    if (quoted) return { text, typed: here.slice(q + 1), start: q, quoted };
    const m = /[A-Za-z_][A-Za-z0-9_]*$/.exec(here);
    return { text, typed: m?.[0] ?? "", start: i - (m?.[0].length ?? 0), quoted };
  }

  /** Put `insert` (a quoted name, `All`) in place of what is being typed in a part's index, and a
   *  closing quote already there with it. */
  completeIndex(insert: string): boolean {
    const p = this.partBefore();
    if (!p) return false;
    return this.mutate("struct", () => {
      const { block: b, i } = this.caret;
      const closing = insert.startsWith('"') && b[i]?.k === "ch" && (b[i] as { c: string }).c === '"' ? 1 : 0;
      b.splice(p.start, i - p.start + closing, ...chars(insert));
      this.caret = { block: b, i: p.start + Array.from(insert).length };
      return true;
    });
  }

  /** Replace the name before the caret with `name` and (`call`) open its call, as typing the rest
   *  and `(` would. */
  completeName(name: string, call = true): boolean {
    const p = this.nameBefore();
    if (!p) return false;
    return this.mutate("struct", () => {
      const { block: b } = this.caret;
      b.splice(p.start, p.name.length, ...chars(name));
      this.caret = { block: b, i: p.start + Array.from(name).length };
      return call ? this.typeOne("(") : true;
    });
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
  command(): boolean { return this.pendingCommand() ? this.mutate("struct", () => this.commandOne()) : false; }
  private commandOne(): boolean {
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

  /** Pasted text: structure when it reads as an expression (a whole `let` into an empty input
   *  becomes the cell's head too), otherwise typed a character at a time. One step to undo. */
  paste(text: string): boolean {
    return this.mutate("struct", () => {
      if (this.selection()) this.deleteSelection();
      const r = text.trim() ? read(text, this.known) : null;
      const { block, i } = this.caret;
      // a `let` head goes only at the very start of an input that has none
      const head = r?.ok && r.stmt.body[0]?.k === "let";
      if (r?.ok && (!head || (block === this.root && i === 0 && this.root[0]?.k !== "let"))) {
        block.splice(i, 0, ...r.stmt.body);
        this.caret = { block, i: i + r.stmt.body.length };
        return true;
      }
      let any = false;
      for (const c of text) any = this.typeOne(c) || any;
      return any;
    });
  }

  // --- deleting ----------------------------------------------------------------------------------

  /** Backspace: a character goes; a structure is entered from its end, and goes once it is empty.
   *  Right after a group's `)` (or a call's), the `)` goes as it would in the text: the group opens
   *  again and takes in what follows. At the start of a group its `(` goes and the contents stay; at
   *  the start of a call drawn as `name(…)`, the name stays too (`sin(x` → `sinx`), and one drawn
   *  in its own notation (√, |x|) leaves its contents. */
  backspace(): boolean {
    if (this.selection()) return this.deleteSelection();
    return this.mutate("delete", () => this.backspaceOne());
  }
  private backspaceOne(): boolean {
    const { block: b, i } = this.caret;
    // in the empty name box `@` left: undo the `@`, the group's contents back where they were
    const g = b[i];
    if (g?.k === "paren" && g.head && !this.nameAt(b, i)) {
      b.splice(i, 1, ...g.body);
      return true;
    }
    if (i > 0) {
      const a = b[i - 1]!;
      if ((a.k === "paren" || (a.k === "call" && !notated(a))) && !a.open) {
        const last = a.k === "paren" ? a.body : a.args[a.args.length - 1]!;
        const at = last.length;
        last.push(...b.splice(i));
        a.open = true;
        this.caret = { block: last, i: at };
        return true;
      }
      const s = slots(a);
      if (s.every((x) => x.length === 0)) { b.splice(i - 1, 1); this.caret = { block: b, i: i - 1 }; return true; }
      const last = s[s.length - 1]!;
      this.caret = { block: last, i: last.length };
      return true;
    }
    const w = this.where(b);
    if (!w) return false;
    if (w.atom.k === "let" && w.slot > 0 && b.length === 0) {
      // an empty parameter goes (and with the last one, the parentheses)
      const ps = w.atom.params!;
      ps.splice(w.slot - 1, 1);
      if (!ps.length) w.atom.params = null;
      const prev = slots(w.atom)[w.slot - 1]!;
      this.caret = { block: prev, i: prev.length };
      return true;
    }
    // at the start of an empty column (`[1, |]`) or row, the `,` or `;` before it goes, as in the text
    if (w.atom.k === "matrix" && b.length === 0) {
      const rows = w.atom.rows, r = rows.findIndex((row) => row.includes(b)), c = rows[r]!.indexOf(b);
      if (c > 0 && rows.every((row) => row[c]!.length === 0)) {
        for (const row of rows) row.splice(c, 1);
        const prev = rows[r]![c - 1]!;
        this.caret = { block: prev, i: prev.length };
        return true;
      }
      if (c === 0 && r > 0 && rows[r]!.every((x) => x.length === 0)) {
        rows.splice(r, 1);
        const prev = rows[r - 1]![rows[r - 1]!.length - 1]!;
        this.caret = { block: prev, i: prev.length };
        return true;
      }
    }
    // and at the start of an empty argument after the first (`f(a, |)`), its `,`
    if (w.atom.k === "call" && !notated(w.atom) && w.slot > 0 && b.length === 0) {
      w.atom.args.splice(w.slot, 1);
      const prev = w.atom.args[w.slot - 1]!;
      this.caret = { block: prev, i: prev.length };
      return true;
    }
    const s = slots(w.atom);
    if (w.slot === 0 && w.atom.k === "call" && !notated(w.atom) && (w.atom.args.length === 1 || s.every((x) => x.length === 0))) {
      const name = chars(w.atom.name);
      w.parent.splice(w.index, 1, ...name, ...w.atom.args[0]!);
      this.caret = { block: w.parent, i: w.index + name.length };
      return true;
    }
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
    if (this.selection()) return this.deleteSelection();
    return this.mutate("delete", () => this.deleteForwardOne());
  }
  private deleteForwardOne(): boolean {
    const { block: b, i } = this.caret;
    const a = b[i];
    if (!a) return false;
    const s = slots(a);
    if (s.every((x) => x.length === 0)) { b.splice(i, 1); return true; }
    this.caret = { block: s[0]!, i: 0 };
    return true;
  }
}

/** The template a `\name` at the end of `text` asks for (`\frac`, `\mat2x3`), with where it starts. */
export function templateAt(text: string): { name: string; start: number; make: () => Atom } | null {
  const m = /\\([A-Za-z]+?)(\d+)?(?:x(\d+))?$/.exec(text);
  const t = m && TEMPLATES[m[1]!];
  if (!m || !t) return null;
  return { name: m[1]!, start: m.index, make: () => t.make(m[2] ? +m[2] : undefined, m[3] ? +m[3] : undefined) };
}

/** A template asked for in a cell's text: `before` ends with the `\name`, `after` follows the caret.
 *  The cell as a tree with the template where the command was and the caret in its first slot, or
 *  null when the text around it does not read (the cell stays text). The text is read with a
 *  placeholder name in the command's place, so the template lands where it was typed, whatever
 *  surrounds it: `rref(\mat2x2)`, `1 + \frac`. */
export function templateInText(before: string, after: string, opts: { known?: readonly string[]; symbols?: Record<string, string> } = {}): MathEdit | null {
  const t = templateAt(before);
  if (!t) return null;
  const PH = "__template__";
  const r = read(`${before.slice(0, t.start)} ${PH} ${after}`, opts.known);
  if (!r.ok) return null;
  const find = (b: Block): Caret | null => {
    for (let i = 0; i + PH.length <= b.length; i++) {
      if (Array.from(PH).every((c, k) => { const a = b[i + k]; return a?.k === "ch" && a.c === c; })) return { block: b, i };
    }
    for (const a of b) for (const s of slots(a)) { const c = find(s); if (c) return c; }
    return null;
  };
  const at = find(r.stmt.body);
  if (!at) return null;
  at.block.splice(at.i, PH.length);
  // the space the reader kept between the placeholder and a name beside it goes with it
  const sp = (a: Atom | undefined) => a?.k === "ch" && a.c === " ";
  if (sp(at.block[at.i - 1])) { at.block.splice(at.i - 1, 1); at.i--; } else if (sp(at.block[at.i])) at.block.splice(at.i, 1);
  const e = new MathEdit(r.stmt, opts);
  e.caret = at;
  e.insert(t.make(), true);
  return e;
}
