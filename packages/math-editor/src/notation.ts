import { type Atom, type Block, type Stmt, isDigit, isIdChar, isIdStart } from "./model.js";

/**
 * The editor's tree → LaTeX for KaTeX. Anything with a well-known notation shows in it — d/dx, ∫,
 * Σ, √, |x|, ‖v‖, z̄, Mᵀ, u·v, a determinant's bars — and the LaTeX follows the engine's printer
 * (`Print.lean`, `latexTarget`) wherever the engine prints the same thing, so an input looks like
 * the outputs under it.
 *
 * `wrap` lets the view tag what it needs to find again on screen (the editor wraps each atom in
 * `\htmlData` to place its caret); it is given the atoms a piece of LaTeX stands for — usually one,
 * several when a name is a single glyph (`pi` is π). `hole` draws an empty slot.
 */

export interface NotationOptions {
  wrap?: (atoms: Atom[], latex: string) => string;
  hole?: (b: Block) => string;
}

const GREEK: Record<string, string> = {
  "π": "\\pi", "α": "\\alpha", "β": "\\beta", "γ": "\\gamma", "δ": "\\delta", "ε": "\\varepsilon", "θ": "\\theta",
  "λ": "\\lambda", "μ": "\\mu", "σ": "\\sigma", "τ": "\\tau", "φ": "\\varphi", "ψ": "\\psi", "ω": "\\omega",
  "Γ": "\\Gamma", "Δ": "\\Delta", "Θ": "\\Theta", "Λ": "\\Lambda", "Σ": "\\Sigma", "Φ": "\\Phi", "Ω": "\\Omega",
  "ℯ": "e",
};
/** Spelled-out names the engine prints as one glyph. */
const GLYPH_NAMES: Record<string, string> = { pi: "\\pi", alpha: "\\alpha", beta: "\\beta", theta: "\\theta", lambda: "\\lambda" };
const NAMED_FNS = ["sin", "cos", "tan", "exp", "ln", "log"];

export function toLatex(stmt: Stmt, opts: NotationOptions = {}): string {
  return new Notation(opts).block(stmt.body);
}

/** A name on its own, the way the engine prints a variable: one letter italic, longer ones as one
 *  italic word, `x_1` with its subscript. */
function nameLatex(s: string): string {
  if (GLYPH_NAMES[s]) return GLYPH_NAMES[s]!;
  const cs = Array.from(s);
  const u = cs.indexOf("_");
  const head = (u < 0 ? cs : cs.slice(0, u)).map(charLatex);
  const base = head.length > 1 ? `\\mathit{${head.join("")}}` : head.join("");
  return u < 0 ? base : `${base}_{${cs.slice(u + 1).map(charLatex).join("")}}`;
}
const charLatex = (c: string) => GREEK[c] ?? (c === "_" ? "\\_" : c === "'" ? "'" : c);

type Token = { kind: "name" | "num" | "op"; atoms: Atom[] };

/** Split a run of characters into the engine's tokens, so a name is shown as one word. */
function tokens(run: (Atom & { k: "ch" })[]): Token[] {
  const out: Token[] = [];
  let i = 0;
  while (i < run.length) {
    const c = run[i]!.c;
    let j = i + 1;
    let kind: Token["kind"] = "op";
    if (isIdStart(c)) { kind = "name"; while (j < run.length && isIdChar(run[j]!.c)) j++; }
    else if (isDigit(c) || c === ".") { kind = "num"; while (j < run.length && (isDigit(run[j]!.c) || run[j]!.c === ".")) j++; }
    else if (c === "%") { kind = "op"; while (j < run.length && (isDigit(run[j]!.c) || run[j]!.c === "%")) j++; }
    out.push({ kind, atoms: run.slice(i, j) });
    i = j;
  }
  return out;
}

class Notation {
  private wrap: (atoms: Atom[], latex: string) => string;
  private hole: (b: Block) => string;
  constructor(opts: NotationOptions) {
    this.wrap = opts.wrap ?? ((_, s) => s);
    this.hole = opts.hole ?? (() => "\\square");
  }

  block(b: Block): string {
    if (b.length === 0) return this.hole(b);
    let s = "";
    let j = 0;
    while (j < b.length) {
      const a = b[j]!;
      if (a.k === "ch") {
        const run: (Atom & { k: "ch" })[] = [];
        while (j < b.length && b[j]!.k === "ch") run.push(b[j++] as Atom & { k: "ch" });
        s += tokens(run).map((t) => this.token(t)).join("");
        continue;
      }
      s += this.atom(a);
      j++;
    }
    // a `let` head with no body yet: the body's place, drawn as an empty slot
    if (b[b.length - 1]?.k === "let") s += this.hole(b);
    return s;
  }

  private chars(atoms: Atom[], f: (c: string) => string): string {
    return atoms.map((a) => this.wrap([a], f((a as { c: string }).c))).join("");
  }

  private token(t: Token): string {
    const text = t.atoms.map((a) => (a as { c: string }).c).join("");
    if (t.kind === "name") {
      if (GLYPH_NAMES[text]) return this.wrap(t.atoms, GLYPH_NAMES[text]!);
      const u = t.atoms.findIndex((a) => (a as { c: string }).c === "_");
      const head = u < 0 ? t.atoms : t.atoms.slice(0, u);
      const inner = this.chars(head, charLatex);
      let s = head.length > 1 ? `\\mathit{${inner}}` : inner;
      // `x_1`: the underscore is where the subscript starts, not a character on screen
      if (u >= 0) s += this.wrap([t.atoms[u]!], "") + `_{${this.chars(t.atoms.slice(u + 1), charLatex)}}`;
      return `{${s}}`;
    }
    if (t.kind === "num") return this.chars(t.atoms, (c) => c);
    // a `\` is a command still being typed (`\frac` before its space)
    return this.chars(t.atoms, (c) => (c === "*" ? "\\cdot " : c === " " ? "\\," : c === "%" ? "\\%" : c === "\\" ? "\\backslash " : c));
  }

  /** A slot shown in parentheses unless it is one factor already. */
  private operand(b: Block): string {
    const s = this.block(b);
    const one = b.length === 1 && b[0]!.k !== "ch" && b[0]!.k !== "frac" && b[0]!.k !== "sup";
    const word = b.length > 0 && b.every((a) => a.k === "ch") && tokens(b as (Atom & { k: "ch" })[]).length === 1;
    return one || word || b.length === 0 ? s : `\\left(${s}\\right)`;
  }

  private atom(a: Atom): string {
    switch (a.k) {
      case "ch": return this.token({ kind: "op", atoms: [a] });
      case "frac": return this.wrap([a], `\\frac{${this.block(a.num)}}{${this.block(a.den)}}`);
      // the power attaches to what precedes it in the LaTeX as in the text; the tag goes inside
      case "sup": return `^{${this.wrap([a], this.block(a.exp))}}`;
      case "paren": return this.wrap([a], `\\left(${this.block(a.body)}\\right)`);
      case "matrix": return this.wrap([a], this.matrix(a.rows, "bmatrix"));
      case "call": return this.wrap([a], this.call(a));
      case "let": {
        const params = a.params ? `\\left(${a.params.map((p) => this.block(p)).join(",\\,")}\\right)` : "";
        return this.wrap([a], `\\mathrm{let}\\;${this.block(a.name)}${params}\\;=\\;`);
      }
    }
  }

  private matrix(rows: Block[][], env: string): string {
    return `\\begin{${env}}` + rows.map((r) => r.map((x) => this.block(x)).join(" & ")).join(" \\\\ ") + `\\end{${env}}`;
  }

  private call(a: Atom & { k: "call" }): string {
    const b = a.args;
    const x = (i: number) => this.block(b[i]!);
    const n = b.length;
    switch (`${a.name}/${n}`) {
      case "sqrt/1": return `\\sqrt{${x(0)}}`;
      case "abs/1": return `\\left|${x(0)}\\right|`;
      case "norm/1": return `\\left\\lVert ${x(0)}\\right\\rVert`;
      case "conj/1": return `\\overline{${x(0)}}`;
      case "re/1": return `\\operatorname{Re}\\left(${x(0)}\\right)`;
      case "im/1": return `\\operatorname{Im}\\left(${x(0)}\\right)`;
      case "sign/1": return `\\operatorname{sgn}\\left(${x(0)}\\right)`;
      case "diff/2": return `\\frac{d}{d${x(1)}}\\left(${x(0)}\\right)`;
      case "diff/3": return `\\frac{d^{${x(2)}}}{d{${x(1)}}^{${x(2)}}}\\left(${x(0)}\\right)`;
      case "integrate/2": return `\\int ${x(0)} \\, d${x(1)}`;
      case "integrate/4": return `\\int_{${x(2)}}^{${x(3)}} ${x(0)} \\, d${x(1)}`;
      case "sum/4": return `\\sum_{${x(1)}=${x(2)}}^{${x(3)}} ${x(0)}`;
      case "det/1": {
        const m = b[0]![0];
        if (b[0]!.length === 1 && m?.k === "matrix") return this.wrap([m], this.matrix(m.rows, "vmatrix"));
        return `\\det\\left(${x(0)}\\right)`;
      }
      case "transpose/1": return `{${this.operand(b[0]!)}}^{\\mathsf{T}}`;
      case "dot/2": return `${this.operand(b[0]!)} \\cdot ${this.operand(b[1]!)}`;
    }
    const args = b.map((_, i) => x(i)).join(", ");
    if (NAMED_FNS.includes(a.name)) return `\\${a.name}\\left(${args}\\right)`;
    // a function the session defined is a name like any other; the rest are commands
    const head = BUILTINS.has(a.name) ? `\\operatorname{${a.name}}` : nameLatex(a.name);
    return `${head}\\left(${args}\\right)`;
  }
}

const BUILTINS = new Set(["simplify", "expand", "factor", "N", "det", "rref", "transpose", "solve", "subst", "plot",
  "dot", "norm", "sum", "exptotrig", "epicycles", "dft", "diff", "integrate", "sign", "sqrt", "abs", "conj", "re", "im"]);

/** An atom's slots in the order they sit on screen, left to right and then top to bottom, which is
 *  the order the arrow keys walk them: d/dx (f) is x then f; ∫ₐᵇ f dx is a, b, f, x; Σ is k, a, b,
 *  then the body. Must agree with the LaTeX above. */
export function slots(a: Atom): Block[] {
  switch (a.k) {
    case "ch": return [];
    case "frac": return [a.num, a.den];
    case "sup": return [a.exp];
    case "paren": return [a.body];
    case "matrix": return a.rows.flat();
    case "let": return [a.name, ...(a.params ?? [])];
    case "call": {
      const b = a.args;
      switch (`${a.name}/${b.length}`) {
        case "diff/2": return [b[1]!, b[0]!];
        case "diff/3": return [b[2]!, b[1]!, b[0]!];
        case "integrate/4": return [b[2]!, b[3]!, b[0]!, b[1]!];
        case "sum/4": return [b[1]!, b[2]!, b[3]!, b[0]!];
        default: return b;
      }
    }
  }
}
