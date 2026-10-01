import { type Atom, type Block, type Stmt, ch, chars, isDigit, isIdChar, isIdStart, merges } from "./model.js";

/**
 * Source text → the editor's tree. This is the engine's grammar (`engine/MathEngine/Parser.lean`)
 * rule for rule — the same tokens, precedence, implicit products and error messages — building
 * notation instead of an `Expr`. It has to agree with the engine exactly: a fraction drawn where the
 * engine reads a product would be the input interpretation lying. The golden corpus checks that it
 * does (`test/`).
 *
 * What the tree keeps and drops: parentheses are kept, except the ones a fraction bar or an exponent
 * already shows (`(a+b)/(c+d)`, `x^(2n)`) and the ones around a lone fraction (`2(a/b)`), which the
 * writer puts back where they are needed. Whitespace is dropped, except between two names or a name
 * and a numeral, where it is the product (`x y`).
 */

export interface ReadError { message: string; span: { start: number; end: number } }
export type ReadResult = { ok: true; stmt: Stmt } | { ok: false; error: ReadError };

/** `builtinFunctions` in `Parser.lean`: a name followed by `(` is a call only if it is one of these
 *  or a function the session defined (`known`); otherwise it is a product, `f·(x)`. */
export const BUILTIN_FUNCTIONS = ["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "conj", "re", "im",
  "diff", "simplify", "expand", "factor", "N", "det", "rref", "transpose", "solve", "subst", "integrate", "plot",
  "sign", "dot", "norm", "sum", "exptotrig", "epicycles", "dft",
  "total", "mean", "variance", "stdev", "min", "max", "median"];

/** `sin^2(y)` is `sin(y)^2` for these. */
const POWER_FNS = ["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs"];

type TokKind = "num" | "id" | "op" | "eof";
interface Tok { kind: TokKind; s: string; start: number; stop: number }

class Fail { constructor(readonly error: ReadError) {} }
const fail = (message: string, t: { start: number; stop: number }): never => { throw new Fail({ message, span: { start: t.start, end: t.stop } }); };

/** `lex` in `Parser.lean`. Positions count characters, as the engine's do. */
export function lex(src: string): Tok[] {
  const cs = Array.from(src);
  const out: Tok[] = [];
  let i = 0;
  while (i < cs.length) {
    const c = cs[i]!;
    if (c === " " || c === "\t" || c === "\n" || c === "\r") { i++; continue; }
    if (isDigit(c) || (c === "." && isDigit(cs[i + 1] ?? ""))) {
      let j = i;
      while (j < cs.length && isDigit(cs[j]!)) j++;
      if (cs[j] === "." && isDigit(cs[j + 1] ?? "")) { j++; while (j < cs.length && isDigit(cs[j]!)) j++; }
      out.push({ kind: "num", s: cs.slice(i, j).join(""), start: i, stop: j });
      i = j;
    } else if (isIdStart(c)) {
      let j = i;
      while (j < cs.length && isIdChar(cs[j]!)) j++;
      out.push({ kind: "id", s: cs.slice(i, j).join(""), start: i, stop: j });
      i = j;
    } else if ("+-*/^()[],;=%{}".includes(c)) {
      out.push({ kind: "op", s: c, start: i, stop: i + 1 });
      i++;
    } else fail(`unexpected character '${c}'`, { start: i, stop: i + 1 });
  }
  out.push({ kind: "eof", s: "", start: cs.length, stop: cs.length });
  return out;
}

/** Read a cell. `known` lists the functions the session has defined (`let f(x) = …`). */
export function read(src: string, known: readonly string[] = []): ReadResult {
  try {
    return { ok: true, stmt: new Reader(lex(src), known).stmt() };
  } catch (e) {
    if (e instanceof Fail) return { ok: false, error: e.error };
    throw e;
  }
}

/** A fraction's numerator and denominator and an exponent show their own grouping: `(a+b)/c`
 *  keeps `a+b` and drops the parentheses (all of them: `((a+b))/c` is the same fraction). */
export const ungroup = (b: Block): Block => { const a = b[0]; return b.length === 1 && a?.k === "paren" ? ungroup(a.body) : b; };

/** Append `more` to `out` as an implicit product, keeping a space where the two would lex as one. */
function juxtapose(out: Block, more: Block) {
  const b = more[0];
  let run = "";
  for (let j = out.length - 1; j >= 0; j--) { const a = out[j]!; if (a.k !== "ch") break; run = a.c + run; }
  if (run && b?.k === "ch" && merges(run, b.c)) out.push(ch(" "));
  out.push(...more);
}

class Reader {
  private i = 0;
  private known: string[];
  constructor(private toks: Tok[], known: readonly string[]) { this.known = [...known]; }

  private peek(k = 0): Tok { return this.toks[this.i + k] ?? this.toks[this.toks.length - 1]!; }
  private prev(): Tok | undefined { return this.i === 0 ? undefined : this.toks[this.i - 1]; }
  private next(): Tok { const t = this.peek(); this.i++; return t; }
  private isOp(t: Tok, s: string) { return t.kind === "op" && t.s === s; }
  private expectOp(s: string) { const t = this.next(); if (!this.isOp(t, s)) fail(`expected '${s}'`, t); }
  private startsAtom(t: Tok) { return t.kind === "num" || t.kind === "id" || this.isOp(t, "(") || this.isOp(t, "[") || this.isOp(t, "%"); }
  private isFn(name: string) { return BUILTIN_FUNCTIONS.includes(name) || this.known.includes(name); }

  stmt(): Stmt {
    let stmt: Stmt;
    const t = this.peek();
    if (t.kind === "id" && t.s === "let") {
      this.next();
      const name = this.next();
      if (name.kind !== "id") fail("expected a name after 'let'", name);
      let params: string[] | null = null;
      if (this.isOp(this.peek(), "(")) {
        this.next();
        params = [];
        for (;;) {
          const x = this.next();
          if (x.kind !== "id") fail("expected a parameter name", x);
          params.push(x.s);
          const sep = this.next();
          if (this.isOp(sep, ")")) break;
          if (!this.isOp(sep, ",")) fail("expected ',' or ')' in the parameter list", sep);
        }
      }
      this.expectOp("=");
      // inside the body the function may call itself
      this.known.unshift(name.s);
      stmt = { body: [{ k: "let", name: chars(name.s), params: params && params.map(chars) }, ...this.expr()] };
    } else stmt = { body: this.expr() };
    const end = this.peek();
    if (end.kind !== "eof") fail(`unexpected '${end.s}'`, end);
    return stmt;
  }

  private expr(): Block {
    const out = this.term();
    for (;;) {
      const t = this.peek();
      if (this.isOp(t, "+") || this.isOp(t, "-")) { this.next(); out.push(ch(t.s), ...this.term()); }
      else break;
    }
    return out;
  }

  private term(): Block {
    let out = this.unary();
    for (;;) {
      const t = this.peek();
      if (this.isOp(t, "*")) { this.next(); out.push(ch("*"), ...this.unary()); }
      else if (this.isOp(t, "/")) {
        this.next();
        const den = this.unary();
        // the numerator is the whole term so far, as the engine reads it: `2x/3` is (2x)/3
        out = [{ k: "frac", num: ungroup(out), den: ungroup(den) }];
      } else if (this.startsAtom(t) && !(t.kind === "num" && this.prev()?.kind === "num")) juxtapose(out, this.unary());
      else break;
    }
    return out;
  }

  private unary(): Block {
    if (this.isOp(this.peek(), "-")) { this.next(); return [ch("-"), ...this.unary()]; }
    return this.power();
  }

  private power(): Block {
    let b = this.atom();
    // `m[[2]]`, Mathematica's Part, has no typeset form yet: the cell stays text
    if (this.isOp(this.peek(0), "[") && this.isOp(this.peek(1), "[")) fail("a part m[[…]] is edited as text", this.peek(0));
    if (this.isOp(this.peek(), "^")) {
      this.next();
      // `sin^2(y)^3`: the atom was already a power; group it so the next one applies to all of it
      if (b[b.length - 1]?.k === "sup") b = [{ k: "paren", body: b }];
      return [...b, { k: "sup", exp: ungroup(this.unary()) }];
    }
    return b;
  }

  private atom(): Block {
    const t = this.next();
    switch (t.kind) {
      case "num": return chars(t.s);
      case "id": {
        const powFn = POWER_FNS.includes(t.s) && this.isOp(this.peek(0), "^") && this.peek(1).kind === "num" && this.isOp(this.peek(2), "(");
        if (powFn) {
          this.next();
          const n = this.next();
          this.next();
          return [{ k: "call", name: t.s, args: this.callArgs() }, { k: "sup", exp: chars(n.s) }];
        }
        if (this.isOp(this.peek(), "(") && this.isFn(t.s)) {
          this.next();
          return [{ k: "call", name: t.s, args: this.callArgs() }];
        }
        return chars(t.s);   // a name, or a constant: π, pi, i, ℯ
      }
      case "op": {
        if (t.s === "(") {
          const e = this.expr();
          this.expectOp(")");
          // a lone fraction is its own group; its parentheses come back only where they are needed
          if (e.length === 1 && e[0]!.k === "frac" && !this.isOp(this.peek(), "^")) return e;
          return [{ k: "paren", body: e }];
        }
        if (t.s === "%") {
          const n = this.peek();
          if (n.kind === "num" && n.start === t.stop && /^[0-9]+$/.test(n.s)) { this.next(); return chars("%" + n.s); }
          const out: Atom[] = [ch("%")];
          while (this.isOp(this.peek(), "%")) { this.next(); out.push(ch("%")); }
          return out;
        }
        if (t.s === "[") {
          const rows: Block[][] = [];
          for (;;) {
            const row = [this.expr()];
            while (this.isOp(this.peek(), ",")) { this.next(); row.push(this.expr()); }
            rows.push(row);
            if (this.isOp(this.peek(), ";")) this.next(); else break;
          }
          this.expectOp("]");
          const w = rows[0]?.length ?? 0;
          if (rows.some((r) => r.length !== w)) fail("ragged matrix rows", t);
          return [{ k: "matrix", rows }];
        }
        if (t.s === "{") return fail("braces list the indices of a part, as in m[[{1, 3}]]", t);
        return fail(`unexpected '${t.s}'`, t);
      }
      case "eof": return fail("unexpected end of input", t);
    }
  }

  private callArgs(): Block[] {
    const args: Block[] = [];
    if (!this.isOp(this.peek(), ")")) {
      args.push(this.expr());
      while (this.isOp(this.peek(), ",")) { this.next(); args.push(this.expr()); }
    }
    this.expectOp(")");
    return args;
  }
}
