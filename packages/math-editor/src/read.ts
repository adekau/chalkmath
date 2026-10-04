import { type Atom, type Block, type Src, type Stmt, ch, isConst, isDigit, isIdChar, isIdStart, isSep, KEYWORDS, merges, MULTI_OPS, showAtom } from "./model.js";

/**
 * Source text → the editor's tree. Every text reads: what the grammar cannot structure becomes a
 * `raw` atom of its characters, so any cell can be shown and edited typeset.
 *
 * For math this is the engine's grammar (`engine/MathEngine/Parser.lean`) rule for rule — the same
 * tokens, precedence and implicit products — building notation instead of an `Expr`. It has to agree
 * with the engine exactly: a fraction drawn where the engine reads a product would be the input
 * interpretation lying. The golden corpus checks that it does (`test/`).
 *
 * The other worlds (logic, order, systems, λ) have grammars of their own, but their notation is math
 * between separators: `∀ n ∈ 1..10, n^2 ≥ 2n` is `n^2` and `2n` between `∀ n ∈ 1..10,` and `≥`. So a
 * cell is read as a row of math expressions with any operator the math grammar does not have
 * (`∧ → ≤ := , ; :`, the ASCII spellings `-> <= &&`, a newline) kept between them as a character.
 * In such a cell the keywords (`when`, `do`, `in`, …) end a product as the separators do, and a name
 * written against `(` is a call (`closure(R, transitive)`), as in those grammars.
 *
 * Each atom records where it came from (`Src`), which `write.ts` uses to give back the text exactly.
 * What the tree drops: the parentheses a fraction bar or an exponent already shows (`(a+b)/(c+d)`,
 * `x^(2n)`) and those around a lone fraction (`2(a/b)`), and whitespace, except between two names or
 * a name and a numeral, where it is the product (`x y`). Both live on in the atoms' spellings.
 */

export interface ReadError { message: string; span: { start: number; end: number } }
/** `ok`: the text read as structure. Otherwise `stmt` holds it as a `raw` atom and `error` says why. */
export type ReadResult = { ok: true; stmt: Stmt } | { ok: false; error: ReadError; stmt: Stmt };

/** `builtinFunctions` in `Parser.lean`: a name followed by `(` is a call only if it is one of these
 *  or a function the session defined (`known`); otherwise it is a product, `f·(x)`. */
export const BUILTIN_FUNCTIONS = ["sin", "cos", "tan", "sec", "csc", "cot", "arcsin", "arccos", "arctan", "exp", "ln", "log", "sqrt", "abs", "conj", "re", "im",
  "diff", "simplify", "expand", "factor", "N", "det", "rref", "transpose", "solve", "subst", "integrate", "plot",
  "sign", "dot", "norm", "sum", "exptotrig", "epicycles", "dft", "manipulate", "column",
  "total", "mean", "variance", "stdev", "min", "max", "median"];

/** `powerFunctions`: `sin^2(y)` is `sin(y)^2` for these, and `sin^-1(y)` is `sin(y)^-1`. */
const POWER_FNS = ["sin", "cos", "tan", "sec", "csc", "cot", "arcsin", "arccos", "arctan", "exp", "ln", "log", "sqrt", "abs"];

/** The math grammar's operators; any other is another world's, a separator here. */
const MATH_OPS = new Set(["+", "-", "*", "/", "^", "(", ")", "[", "]", ",", ";", "%", "./", ".*"]);

/** `str`: text in quotes. `ws`: the whitespace before the token. */
type TokKind = "num" | "id" | "op" | "str" | "asset" | "eof";
interface Tok { kind: TokKind; s: string; start: number; stop: number; ws: string }

class Fail { constructor(readonly error: ReadError) {} }
const fail = (message: string, t: { start: number; stop: number }): never => { throw new Fail({ message, span: { start: t.start, end: t.stop } }); };

/** `lex` in `Parser.lean`, made total: a character the math grammar has no token for is an operator
 *  of its own, and the other worlds' operators of several characters are one each. Positions count
 *  characters, as the engine's do. */
export function lex(src: string): Tok[] {
  const cs = Array.from(src);
  const out: Tok[] = [];
  let i = 0, ws = "";
  const push = (kind: TokKind, s: string, start: number, stop: number) => { out.push({ kind, s, start, stop, ws }); ws = ""; };
  while (i < cs.length) {
    const c = cs[i]!;
    if (c === " " || c === "\t" || c === "\r") { ws += c; i++; continue; }
    if (c === "\n") { push("op", "\n", i, i + 1); i++; continue; }
    if (c === "." && cs[i + 1] === ".") { push("op", "..", i, i + 2); i += 2; continue; }
    if (isDigit(c) || (c === "." && isDigit(cs[i + 1] ?? ""))) {
      let j = i;
      while (j < cs.length && isDigit(cs[j]!)) j++;
      if (cs[j] === "." && isDigit(cs[j + 1] ?? "")) { j++; while (j < cs.length && isDigit(cs[j]!)) j++; }
      push("num", cs.slice(i, j).join(""), i, j);
      i = j;
    } else if (isIdStart(c)) {
      let j = i;
      while (j < cs.length && isIdChar(cs[j]!)) j++;
      push("id", cs.slice(i, j).join(""), i, j);
      i = j;
    } else if (c === "⟦" && cs.indexOf("⟧", i) > i) {
      // a file attached to the notebook: `⟦name⟧`, which the notebook reads before the engine
      const j = cs.indexOf("⟧", i);
      push("asset", cs.slice(i + 1, j).join(""), i, j + 1);
      i = j + 1;
    } else if (c === '"' && cs.indexOf('"', i + 1) > i) {
      const j = cs.indexOf('"', i + 1);
      push("str", cs.slice(i, j + 1).join(""), i, j + 1);
      i = j + 1;
    } else if (c === "." && (cs[i + 1] === "/" || cs[i + 1] === "*")) {
      // `./` and `.*`, the entrywise operators: a `.` before a digit was a numeral above
      push("op", c + cs[i + 1], i, i + 2);
      i += 2;
    } else {
      // `<-` is a message's arrow (`b <- m`), but `x<-1` compares with -1
      const m = MULTI_OPS.find((o) => cs.slice(i, i + o.length).join("") === o && !(o === "<-" && /[0-9.]/.test(cs[i + 2] ?? "")));
      const s = m ?? c;
      push("op", s, i, i + Array.from(s).length);
      i += Array.from(s).length;
    }
  }
  push("eof", "", cs.length, cs.length);
  return out;
}

/** Read a cell. `known` lists the functions the session has defined (`let f(x) = …`). Never fails:
 *  text that does not read as structure is a `raw` atom (and `ok` is false). */
export function read(src: string, known: readonly string[] = []): ReadResult {
  const cs = Array.from(src);
  if (!src.trim()) return { ok: true, stmt: { body: [], ...(src ? { pad: src } : {}) } };
  try {
    const toks = lex(src);
    const stmt = new Reader(toks, known, cs).stmt();
    finish(stmt.body, cs);
    return { ok: true, stmt };
  } catch (e) {
    if (!(e instanceof Fail)) throw e;
    return { ok: false, error: e.error, stmt: rawStmt(cs) };
  }
}

/** The whole text as one `raw` atom, its characters as typed. */
function rawStmt(cs: string[]): Stmt {
  const body = cs.map((c, i) => ({ ...ch(c), src: { start: i, end: i + 1, text: c, gap: "", shape: "", prev: "", next: "" } }));
  const raw: Atom = { k: "raw", body };
  raw.src = { start: 0, end: cs.length, text: cs.join(""), gap: "", shape: "", prev: "", next: "" };
  const stmt = { body: [raw] };
  finish(stmt.body, cs);
  return stmt;
}

/** A fraction's numerator and denominator and an exponent show their own grouping: `(a+b)/c`
 *  keeps `a+b` and drops the parentheses (all of them: `((a+b))/c` is the same fraction). */
export const ungroup = (b: Block): Block => { const a = b[0]; return b.length === 1 && a?.k === "paren" ? ungroup(a.body) : b; };

/** Append `more` to `out` as an implicit product, with a space between them where the text has one
 *  (`x y`, `f (x)`, a λ-term's `(λx. x) y`) or where the two would lex as one. */
function juxtapose(out: Block, more: Block, spaced = false) {
  const b = more[0];
  const last = out[out.length - 1];
  // after a separator (`∧`, `,`, `:`) a space is the text's look, not a product's
  if (spaced && last && !(last.k === "ch" && (last.c === " " || last.c === "." || isSep(last.c) || "+-*".includes(last.c) || last.c === "./" || last.c === ".*")) && last.k !== "let") { out.push(ch(" "), ...more); return; }
  let run = "";
  // the run of a name's or numeral's characters it would join (an operator ends it: `1..10`)
  for (let j = out.length - 1; j >= 0; j--) { const a = out[j]!; if (a.k !== "ch" || a.c.length > 1 || isSep(a.c)) break; run = a.c + run; }
  if (run && b?.k === "ch" && merges(run, b.c)) out.push(ch(" "));
  out.push(...more);
}

/** The shape of an atom, or "" for none: what `Src` compares. */
export const shapeOf = (a: Atom | undefined) => (a ? showAtom(a) : "");

/** After reading: each atom's shape and its neighbours' (`Src`), the spelling of a product's space
 *  (the whitespace it stands for), and the whitespace after a block's last atom. */
function finish(b: Block, cs: string[]) {
  b.forEach((a, j) => {
    for (const s of slotsOf(a)) {
      finish(s, cs);
      // an atom that starts where its container does (a numerator's first) has its space outside
      if (s[0]?.src && a.src && s[0].src.start === a.src.start) s[0].src.gap = "";
    }
    if (a.k === "ch" && a.c === " " && !a.src) {
      // a product's space spells the whitespace between its neighbours
      const p = b[j - 1]?.src, n = b[j + 1]?.src;
      if (p && n) { a.src = { start: p.end, end: n.start, text: n.gap, gap: "", shape: "", prev: "", next: "" }; n.gap = ""; }
    }
  });
  b.forEach((a, j) => {
    if (!a.src) return;
    a.src.shape = shapeOf(a); a.src.prev = shapeOf(b[j - 1]); a.src.next = shapeOf(b[j + 1]);
  });
}

/** Every block an atom holds, in any order (for the passes over the tree). */
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

class Reader {
  private i = 0;
  private known: string[];
  /** The cell has an operator the math grammar does not: it is another world's. */
  private loose = false;
  constructor(private toks: Tok[], known: readonly string[], private cs: string[]) { this.known = [...known]; }

  private peek(k = 0): Tok { return this.toks[this.i + k] ?? this.toks[this.toks.length - 1]!; }
  private prev(): Tok | undefined { return this.i === 0 ? undefined : this.toks[this.i - 1]; }
  private next(): Tok { const t = this.peek(); this.i++; return t; }
  private isOp(t: Tok, s: string) { return t.kind === "op" && t.s === s; }
  private expectOp(s: string) { const t = this.next(); if (!this.isOp(t, s)) fail(`expected '${s}'`, t); return t; }
  private keyword(t: Tok) { return this.loose && t.kind === "id" && KEYWORDS.has(t.s); }
  private startsAtom(t: Tok) {
    return (t.kind === "num" || (t.kind === "id" && !this.keyword(t)) || this.isOp(t, "(") || this.isOp(t, "[") || this.isOp(t, "{") || this.isOp(t, "%") || (t.kind === "op" && isConst(t.s))
      || (this.loose && (t.kind === "str" || t.kind === "asset")));
  }
  private startsTerm(t: Tok) { return this.startsAtom(t) || this.isOp(t, "-") || t.kind === "str" || t.kind === "asset"; }
  private isFn(name: string) { return BUILTIN_FUNCTIONS.includes(name) || this.known.includes(name); }

  /** An atom spelled by the tokens from `t0` to `t1`. */
  private at<A extends Atom>(a: A, t0: Tok, t1: Tok = t0): A & { src: Src } {
    a.src = { start: t0.start, end: t1.stop, text: this.cs.slice(t0.start, t1.stop).join(""), gap: t0.ws, shape: "", prev: "", next: "" };
    return a as A & { src: Src };
  }
  /** The characters of a token, each an atom spelled by its own character. */
  private charsOf(t: Tok, s = t.s): Atom[] {
    // an operator is one atom, however many characters spell it (`./`, `->`, `:=`)
    if (t.kind === "op") {
      const a = ch(s);
      a.src = { start: t.start, end: t.stop, text: s, gap: t.ws, shape: "", prev: "", next: "" };
      return [a];
    }
    return Array.from(s, (c, k) => {
      const a = ch(c);
      a.src = { start: t.start + k, end: t.start + k + 1, text: c, gap: k ? "" : t.ws, shape: "", prev: "", next: "" };
      return a;
    });
  }
  /** The whitespace before the token that follows the last atom of a block, as its trail. */
  private trail(b: Block) { const a = b[b.length - 1]; if (a?.src) a.src.trail = this.peek().ws; }

  stmt(): Stmt {
    let head: Atom | null = null;
    const t = this.peek();
    if (t.kind === "id" && t.s === "let") {
      this.next();
      const name = this.next();
      if (name.kind !== "id") fail("expected a name after 'let'", name);
      let params: Tok[] | null = null;
      if (this.isOp(this.peek(), "(")) {
        this.next();
        params = [];
        for (;;) {
          const x = this.next();
          if (x.kind !== "id") fail("expected a parameter name", x);
          params.push(x);
          const sep = this.next();
          if (this.isOp(sep, ")")) break;
          if (!this.isOp(sep, ",")) fail("expected ',' or ')' in the parameter list", sep);
        }
      }
      const eq = this.expectOp("=");
      // inside the body the function may call itself
      this.known.unshift(name.s);
      head = this.at({ k: "let", name: this.charsOf(name), params: params && params.map((p) => this.charsOf(p)) }, t, eq);
    }
    this.loose = this.toks.slice(this.i).some((x) => x.kind === "op" && !MATH_OPS.has(x.s));
    const body = this.seq(new Set());
    const all = head ? [head, ...body] : body;
    this.trail(all);
    return { body: all };
  }

  /** A row of math expressions with separators between them, up to a token in `stops` (or the end).
   *  A closing bracket that closes nothing here is an error. */
  private seq(stops: Set<string>): Block {
    const out: Block = [];
    for (;;) {
      const t = this.peek();
      if (t.kind === "eof" || (t.kind === "op" && stops.has(t.s))) break;
      if (this.startsTerm(t)) { juxtapose(out, this.expr(), !!t.ws); continue; }
      if (this.keyword(t)) { juxtapose(out, this.charsOf(this.next()), !!t.ws); continue; }
      if (t.kind === "op" && (t.s === ")" || t.s === "]" || t.s === "}")) fail(`unexpected '${t.s}'`, t);
      if (t.kind === "op" && (t.s === "(" || t.s === "[" || t.s === "{")) fail(`unexpected '${t.s}'`, t);
      // a separator: `+` or `*` with nothing on its left too (`¬p`, `+x`)
      out.push(...this.charsOf(this.next()));
    }
    return out;
  }

  private expr(): Block {
    const out = this.term();
    for (;;) {
      const t = this.peek();
      if (this.isOp(t, "+") || this.isOp(t, "-")) {
        this.next();
        out.push(...this.charsOf(t));
        // with nothing after it yet (`x +`), the operator stands alone, as while typing
        if (this.startsTerm(this.peek())) out.push(...this.term());
      } else break;
    }
    return out;
  }

  private term(): Block {
    const t0 = this.peek();
    let out = this.unary();
    for (;;) {
      const t = this.peek();
      if (this.isOp(t, "*") || this.isOp(t, "./") || this.isOp(t, ".*")) {
        // `./` and `.*` are one atom each, an operator like `*`; the fraction bar is `/` alone
        this.next();
        out.push(...this.charsOf(t));
        if (this.startsTerm(this.peek())) out.push(...this.unary());
      } else if (this.isOp(t, "/")) {
        this.next();
        const den = this.startsTerm(this.peek()) ? this.unary() : [];
        // the numerator is the whole term so far, as the engine reads it: `2x/3` is (2x)/3
        out = [this.at({ k: "frac", num: ungroup(out), den: ungroup(den) }, t0, this.prev()!)];
      } else if (this.startsAtom(t)) juxtapose(out, this.unary(), !!t.ws);
      else break;
    }
    return out;
  }

  private unary(): Block {
    if (this.isOp(this.peek(), "-")) {
      const t = this.next();
      return [...this.charsOf(t), ...(this.startsTerm(this.peek()) ? this.unary() : [])];
    }
    return this.power();
  }

  private power(): Block {
    const t0 = this.peek();
    let b = this.atom();
    // `m[[2]]`, Mathematica's Part, any number of times: binds tighter than `^`
    while (this.isOp(this.peek(0), "[") && this.isOp(this.peek(1), "[")) b = [...b, this.part()];
    if (this.isOp(this.peek(), "^")) {
      const caret = this.next();
      // `sin^2(y)^3`: the atom was already a power; group it so the next one applies to all of it
      if (b[b.length - 1]?.k === "sup") b = [this.at({ k: "paren", body: b }, t0, this.toks[this.i - 2]!)];
      const exp = this.startsTerm(this.peek()) ? this.unary() : [];
      return [...b, this.at({ k: "sup", exp: ungroup(exp) }, caret, this.prev()!)];
    }
    return b;
  }

  private atom(): Block {
    const t = this.next();
    switch (t.kind) {
      case "num": return this.charsOf(t);
      case "id": {
        const neg = this.isOp(this.peek(1), "-");
        const k = neg ? 1 : 0;
        const powFn = POWER_FNS.includes(t.s) && this.isOp(this.peek(0), "^") && this.peek(1 + k).kind === "num" && this.isOp(this.peek(2 + k), "(");
        if (powFn) {
          this.next();
          const minus = neg ? this.next() : null;
          const n = this.next();
          this.next();
          const call = this.at({ k: "call", name: t.s, args: this.callArgs() }, t, this.prev()!);
          // the call spells `sin^2(y)` whole; the power it shows after it spells nothing of its own
          const sup: Atom = { k: "sup", exp: [...(minus ? this.charsOf(minus) : []), ...this.charsOf(n)] };
          sup.src = { start: call.src!.end, end: call.src!.end, text: "", gap: "", shape: "", prev: "", next: "" };
          return [call, sup];
        }
        if (this.isOp(this.peek(), "(") && (this.isFn(t.s) || (this.loose && !this.peek().ws) || this.commaGroup())) {
          this.next();
          return [this.at({ k: "call", name: t.s, args: this.callArgs() }, t, this.prev()!)];
        }
        return this.charsOf(t);   // a name, or a constant: π, pi, i, ℯ
      }
      case "op": {
        if (isConst(t.s)) return this.charsOf(t);
        if (t.s === "(") {
          const e = this.seq(new Set([")"]));
          this.trail(e);
          const close = this.expectOp(")");
          // a lone fraction is its own group; its parentheses come back only where they are needed
          if (e.length === 1 && e[0]!.k === "frac" && !this.isOp(this.peek(), "^")) {
            const f = e[0]!;
            f.src = { ...f.src!, start: t.start, end: close.stop, text: this.cs.slice(t.start, close.stop).join(""), gap: t.ws };
            return e;
          }
          return [this.at({ k: "paren", body: e }, t, close)];
        }
        if (t.s === "{") {
          const e = this.seq(new Set(["}"]));
          this.trail(e);
          return [this.at({ k: "brace", body: e }, t, this.expectOp("}"))];
        }
        if (t.s === "%") {
          const n = this.peek();
          if (n.kind === "num" && n.start === t.stop && /^[0-9]+$/.test(n.s)) { this.next(); return [...this.charsOf(t), ...this.charsOf(n)]; }
          const out: Atom[] = this.charsOf(t);
          while (this.isOp(this.peek(), "%")) out.push(...this.charsOf(this.next()));
          return out;
        }
        if (t.s === "[") {
          const rows: Block[][] = [];
          const stops = new Set([",", ";", "]"]);
          for (;;) {
            const cell = () => { const e = this.seq(stops); this.trail(e); return e; };
            const row = [cell()];
            while (this.isOp(this.peek(), ",")) { this.next(); row.push(cell()); }
            rows.push(row);
            if (this.isOp(this.peek(), ";")) this.next(); else break;
          }
          const close = this.expectOp("]");
          const w = rows[0]?.length ?? 0;
          if (rows.some((r) => r.length !== w)) fail("ragged matrix rows", t);
          return [this.at({ k: "matrix", rows }, t, close)];
        }
        return fail(`unexpected '${t.s}'`, t);
      }
      // text in quotes, and an attached file: the notebook's (`import("url")`, `⟦data.csv⟧`)
      case "str": {
        const body = this.charsOf({ ...t, start: t.start + 1, ws: "" }, t.s.slice(1, -1));
        return [this.at({ k: "str", body }, t)];
      }
      case "asset": return [this.at({ k: "asset", name: t.s }, t)];
      case "eof": return fail("unexpected end of input", t);
    }
  }

  /** Is the group at `(` one with a `,` at its top level? Then a name before it is a call: a product
   *  has no commas. */
  private commaGroup(): boolean {
    let depth = 0;
    for (let k = this.i; k < this.toks.length; k++) {
      const t = this.toks[k]!;
      if (t.kind !== "op") { if (t.kind === "eof") return false; continue; }
      if ("([{".includes(t.s)) depth++;
      else if (")]}".includes(t.s)) { depth--; if (depth === 0) return false; }
      else if (depth === 1 && (t.s === "," || t.s === ";")) return true;
    }
    return false;
  }

  /** A part's indices, after its `[[`, each kept as the characters typed (consumes the `]]`). */
  private part(): Atom {
    const open = this.next(); this.next();
    const specs: Block[] = [];
    let from = this.peek(), depth = 0;
    const cut = (to: Tok) => {
      // the index's characters as typed, the spaces around it in the part's spelling
      const raw = this.cs.slice(from.start, to.start).join("");
      const lead = raw.length - raw.trimStart().length;
      specs.push(this.charsOf({ ...from, start: from.start + lead, ws: "" }, raw.trim()).map((a) => { a.src!.gap = ""; return a; }));
    };
    for (;;) {
      const t = this.peek();
      if (t.kind === "eof") fail("expected ']]' to close the part", open);
      if (depth === 0 && this.isOp(t, ",")) { cut(t); this.next(); from = this.peek(); continue; }
      if (depth === 0 && this.isOp(t, "]")) {
        if (!this.isOp(this.peek(1), "]")) fail("expected ']]' to close the part", t);
        cut(t); this.next();
        const close = this.next();
        return this.at({ k: "part", specs }, open, close);
      }
      if (t.kind === "op" && "([{".includes(t.s)) depth++;
      else if (t.kind === "op" && ")]}".includes(t.s)) depth--;
      this.next();
    }
  }

  private callArgs(): Block[] {
    const args: Block[] = [];
    const stops = new Set([",", ")"]);
    const arg = () => { const e = this.seq(stops); this.trail(e); return e; };
    if (!this.isOp(this.peek(), ")")) {
      args.push(arg());
      while (this.isOp(this.peek(), ",")) { this.next(); args.push(arg()); }
    }
    this.expectOp(")");
    return args;
  }
}
