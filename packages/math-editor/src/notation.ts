import { type Atom, type Block, type Stmt, isConst, isDigit, isIdChar, isIdStart, KEYWORDS, lineIndent } from "./model.js";

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
  /** Which output a relative reference (`%`, `%%`) stands for, when the host knows: the one the
   *  cell's output used, or (`pending`: the cell is being edited, or has not run) the one a run
   *  now would use. */
  outRef?: (ref: string) => { label: number; pending?: boolean } | null;
  /** A highlight class for a token, by what it is where it stands: a call's name, a variable bound
   *  by the call or `let` head around it (`diff(f, x)`'s x, `let f(x)`'s x), any other name, or a
   *  numeral. Null leaves it plain. The notation tags it `\\htmlData{hl=…}` for the host's colours. */
  classify?: (text: string, as: "call" | "bound" | "name" | "num" | "keyword") => string | null;
}

/** Commands whose argument at this index is a variable bound over the call (the notebook's
 *  highlighter has the same list). */
const BINDERS: Record<string, number> = { diff: 1, integrate: 1, plot: 1, epicycles: 1, sum: 1, subst: 1, manipulate: 1 };

/** An output reference's tag: `%` is `p1`, `%%` is `p2`, `%3` is `n3` (a `data-out` the view reads back). */
export const outTag = (ref: string) => (/^%\d+$/.test(ref) ? `n${ref.slice(1)}` : `p${ref.length}`);
export const outRefOf = (tag: string) => (tag[0] === "n" ? `%${tag.slice(1)}` : "%".repeat(+tag.slice(1)));

const GREEK: Record<string, string> = {
  "π": "\\pi", "α": "\\alpha", "β": "\\beta", "γ": "\\gamma", "δ": "\\delta", "ε": "\\varepsilon", "ζ": "\\zeta",
  "η": "\\eta", "θ": "\\theta", "ι": "\\iota", "κ": "\\kappa", "λ": "\\lambda", "μ": "\\mu", "ν": "\\nu", "ξ": "\\xi",
  "ρ": "\\rho", "σ": "\\sigma", "τ": "\\tau", "φ": "\\varphi", "χ": "\\chi", "ψ": "\\psi", "ω": "\\omega",
  "Γ": "\\Gamma", "Δ": "\\Delta", "Θ": "\\Theta", "Λ": "\\Lambda", "Ξ": "\\Xi", "Π": "\\Pi", "Σ": "\\Sigma",
  "Φ": "\\Phi", "Ψ": "\\Psi", "Ω": "\\Omega",
  "ℯ": "e",
};
/** Operators as they are drawn: the other worlds' glyphs, and their ASCII spellings drawn as the
 *  glyphs they stand for (`->` is →, `&&` is ∧, `<=` is ≤), so the text keeps what was typed and the
 *  typeset input shows what it means. */
const OPS: Record<string, string> = {
  "*": "\\cdot ", "./": "\\oslash ", ".*": "\\odot ", " ": "\\,", "%": "\\%", "\\": "\\backslash ",
  "∧": "\\land ", "∨": "\\lor ", "¬": "\\lnot ", "→": "\\to ", "↔": "\\leftrightarrow ", "⇒": "\\Rightarrow ",
  "∀": "\\forall ", "∃": "\\exists ", "∈": "\\in ", "∉": "\\notin ", "≤": "\\le ", "≥": "\\ge ", "≠": "\\ne ",
  "∣": "\\mid ", "⊢": "\\vdash ", "⊤": "\\top ", "⊥": "\\bot ", "←": "\\leftarrow ", "↦": "\\mapsto ", "×": "\\times ",
  "⊆": "\\subseteq ", "⊂": "\\subset ", "∪": "\\cup ", "∩": "\\cap ",
  "->": "\\to ", "<->": "\\leftrightarrow ", "=>": "\\to ", "&&": "\\land ", "||": "\\lor ", "/\\": "\\land ", "\\/": "\\lor ",
  "!": "\\lnot ", "~": "\\lnot ", "<=": "\\le ", ">=": "\\ge ", "!=": "\\ne ", "==": "=", ":=": "\\coloneqq ", "<-": "\\leftarrow ",
  "|-": "\\vdash ", "|": "\\mid ", "..": "{..}", ":": "\\mathpunct{:}", ";": "\\mathpunct{;}", "&": "\\&", "#": "\\#", "$": "\\$",
};
/** The ASCII spellings drawn as another glyph (`->` as →): notation the text does not show. */
const ASCII_GLYPHS = new Set(["->", "<->", "=>", "&&", "||", "/\\", "\\/", "<=", ">=", "!=", ":=", "<-", "|-"]);
/** A character atom as LaTeX: its glyph, or the character itself (TeX's specials as text). */
const opLatex = (c: string) => OPS[c] ?? (/^[\\{}_^~&#$]$/.test(c) ? textChar(c) : c);

/** Spelled-out names the engine prints as one glyph. */
const GLYPH_NAMES: Record<string, string> = { pi: "\\pi", alpha: "\\alpha", beta: "\\beta", theta: "\\theta", lambda: "\\lambda" };

export function toLatex(stmt: Stmt, opts: NotationOptions = {}): string {
  return new Notation(opts).block(stmt.body);
}

/** A character of a quoted name, as text (TeX's specials escaped). */
const textChar = (c: string) => c === " " ? "\\ " : /[\\{}$%#&_^~]/.test(c) ? `\\text{\\char${c.codePointAt(0)}}` : `\\text{${c}}`;

// a glyph's command in braces, so a letter after it is not taken into it (`{\\lambda}x`)
const charLatex = (c: string) => (GREEK[c] ? `{${GREEK[c]}}` : c === "_" ? "\\_" : c === "'" ? "'" : c);

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
  private outRef: NonNullable<NotationOptions["outRef"]>;
  private classify: NonNullable<NotationOptions["classify"]>;
  /** The names bound where the notation is now (a binder's variable, a head's parameters). */
  private bound: string[] = [];
  /** How deep in exponents and bounds the notation is now: there a fraction stays script-size. */
  private script = 0;
  /** How many fractions the notation is inside now. */
  private fracs = 0;
  constructor(opts: NotationOptions) {
    this.wrap = opts.wrap ?? ((_, s) => s);
    this.hole = opts.hole ?? (() => "\\square");
    this.outRef = opts.outRef ?? (() => null);
    this.classify = opts.classify ?? (() => null);
  }

  private tag(cls: string | null, latex: string) { return cls ? `\\htmlData{hl=${cls}}{${latex}}` : latex; }
  /** A keyword or a function's name: a word as typed, not a variable, so the host draws it in its
   *  text face (upright, the text input's font) rather than math italic. */
  private word(latex: string) {
    // at full size a word is the text input's size; in a script or a small fraction it shrinks with it
    return `\\htmlData{word=${this.script || this.fracs >= 3 ? "s" : "1"}}{${latex}}`;
  }
  /** A fraction. An input is read and clicked into, so nested fractions shrink gently where a
   *  textbook would drop a size per level: the first two levels full size, then 90%, 80%, and 70%
   *  at the deepest. Each is padded a little either side, so every bar is longer than the bars
   *  inside it and a stack of them still shows which bar divides what. In an exponent or a bound a
   *  fraction stays script-size, as there. */
  private frac(a: Atom & { k: "frac" }): string {
    if (this.script) return `\\frac{${this.block(a.num)}}{${this.block(a.den)}}`;
    const size = FRAC_SIZES[Math.min(this.fracs, FRAC_SIZES.length - 1)];
    this.fracs++;
    try {
      const part = (b: Block) => `\\,${size}${this.block(b)}\\,`;
      return `\\dfrac{${part(a.num)}}{${part(a.den)}}`;
    } finally { this.fracs--; }
  }

  /** A slot in an exponent or a bound (script size). */
  private scripted(b: Block): string {
    this.script++;
    try { return this.block(b); } finally { this.script--; }
  }
  /** A call drawn as its display name (`sgn` for `sign`) set as a word, against its parentheses. */
  private named(a: Atom & { k: "call" }, shown: string): string {
    return this.called(this.tag(this.classify(a.name, "call"), this.word(`\\mathrm{${shown}}`)), a.args.map((x) => this.block(x)).join(", "), a.open);
  }
  /** A call: its name, then its arguments in parentheses, grouped (`call`) so the view can set the
   *  name level with the middle of the parentheses when they stretch. */
  private called(head: string, args: string, open?: boolean): string {
    return `\\htmlData{call=1}{${head}{${this.parens(args, open, true)}}}`;
  }
  /** Parentheses around `inner`; an open group's `)` is drawn faint where it would go. They are set
   *  at text size and tagged (`pg` the group, `pd` each side) for the view to stretch over what they
   *  hold: TeX's `\\left(` centres a paren on the math axis, so around a stack of fractions deeper
   *  than it is tall it reaches as far above the stack as the stack goes below. */
  private parens(inner: string, open?: boolean, call = false) {
    return this.delims(inner, "(", ")", call ? "c" : "1", open);
  }
  /** Delimiters the view fits to what they hold, as `parens`: `pk` says how it draws them (a paren,
   *  `abs`'s bars, `norm`'s double bars). */
  private delims(inner: string, l: string, r: string, group: string, open?: boolean, kind?: string) {
    const pk = kind ? `, pk=${kind}` : "";
    return `\\htmlData{pg=${group}${pk}}{\\htmlData{pd=o}{${l}}${inner}\\htmlData{pd=c${open ? ", open=1" : ""}}{${r}}}`;
  }

  block(b: Block): string {
    if (b.length === 0) return this.hole(b);
    // a function's parameters are bound over its whole cell
    const head = b[0]?.k === "let" && b[0].params ? b[0].params.map(nameOf).filter((n): n is string => !!n) : [];
    this.bound.push(...head);
    try { return this.blockInner(b); } finally { this.bound.length -= head.length; }
  }

  private blockInner(b: Block): string {
    // a block of several lines (a system's declarations) is drawn as its lines, left-aligned; each
    // line break is an atom at the end of its line, for the caret
    const breaks = b.flatMap((a, j) => (a.k === "ch" && a.c === "\n" ? [j] : []));
    if (breaks.length) {
      const lines: string[] = [];
      let from = 0;
      for (const j of [...breaks, b.length]) {
        const line = b.slice(from, j);
        // an indented line keeps its indent, also once something is typed at its start
        const indent = (from ? lineIndent(b, from) : line[0]?.src?.gap) ? "\\quad " : "";
        lines.push(indent + (line.length ? this.row(line) : "") + (j < b.length ? this.wrap([b[j]!], "") : ""));
        from = j + 1;
      }
      return `\\begin{array}{l}${lines.join(" \\\\ ")}\\end{array}`;
    }
    return this.row(b);
  }

  private row(b: Block): string {
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
      s += this.atom(a, b[j - 1]);
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
    // the other worlds' keywords (`when`, `do`, `in`) are words, as `let` is
    if (t.kind === "name" && KEYWORDS.has(text)) return this.tag(this.classify(text, "keyword"), this.wrap(t.atoms, `\\;${this.word(`\\mathrm{${text}}`)}\\;`));
    if (t.kind === "name") {
      const cls = this.classify(text, this.bound.includes(text) ? "bound" : "name");
      return this.tag(cls, this.name(t, text));
    }
    if (t.kind === "num") return this.tag(this.classify(text, "num"), this.chars(t.atoms, (c) => c));
    return this.op(t, text);
  }

  private name(t: Token, text: string): string {
    if (GLYPH_NAMES[text]) return this.wrap(t.atoms, GLYPH_NAMES[text]!);
    const u = t.atoms.findIndex((a) => (a as { c: string }).c === "_");
    const head = u < 0 ? t.atoms : t.atoms.slice(0, u);
    const inner = this.chars(head, charLatex);
    let s = head.length > 1 ? `\\mathit{${inner}}` : inner;
    // `x_1`: the underscore is where the subscript starts, not a character on screen
    if (u >= 0) s += this.wrap([t.atoms[u]!], "") + `_{${this.chars(t.atoms.slice(u + 1), charLatex)}}`;
    return `{${s}}`;
  }

  private op(t: Token, text: string): string {
    // an output reference is one chip. `%17` names one output for good, drawn %₁₇. `%` and `%%`
    // mean the last output and the one before it whenever the cell runs, so they are drawn as
    // typed, in a chip of their own (`rel`), with the output the cell's output used faint (`now`)
    // beside them, or, while it is edited or before it has run, an arrow to the one a run would
    // use (`next`)
    if (text[0] === "%") {
      if (/^%\d+$/.test(text)) return this.wrap(t.atoms, `\\htmlData{out=${outTag(text)}}{\\%_{${text.slice(1)}}}`);
      const r = this.outRef(text);
      const n = !r ? "" : r.pending ? `_{\\htmlData{next=1}{\\to ${r.label}}}` : `_{\\htmlData{now=1}{${r.label}}}`;
      return this.wrap(t.atoms, `\\htmlData{out=${outTag(text)}, rel=1}{${text.replace(/%/g, "\\%")}${n}}`);
    }
    // a `\` is a command still being typed (`\frac` before its space)
    return this.chars(t.atoms, opLatex);
  }

  /** A slot shown in parentheses unless it is one factor already. */
  private operand(b: Block): string {
    const s = this.block(b);
    const one = b.length === 1 && b[0]!.k !== "ch" && b[0]!.k !== "frac" && b[0]!.k !== "sup";
    const word = b.length > 0 && b.every((a) => a.k === "ch") && tokens(b as (Atom & { k: "ch" })[]).length === 1;
    return one || word || b.length === 0 ? s : this.parens(s);
  }

  private atom(a: Atom, prev?: Atom): string {
    switch (a.k) {
      case "ch": return this.token({ kind: "op", atoms: [a] });
      case "frac": return this.wrap([a], this.frac(a));
      // the power attaches to what precedes it in the LaTeX as in the text; the tag goes inside
      case "sup": return `^{${this.wrap([a], this.scripted(a.exp))}}`;
      case "paren": {
        // `@`'s box for the function's name, until one is typed there
        const box = a.head && !(prev?.k === "ch" && isIdChar(prev.c)) ? "\\htmlData{fh=1}{\\square}" : "";
        return this.wrap([a], box + this.parens(this.block(a.body), a.open));
      }
      case "matrix": return this.wrap([a], this.matrix(a.rows, "bmatrix"));
      // Part, as the engine prints it: m⟦2, 1;;3⟧
      case "part": return this.wrap([a], `\\llbracket ${a.specs.map((x) => this.spec(x)).join(",\\,")}\\rrbracket `);
      // text in quotes, each character its own (for the caret), and an attached file as a chip
      case "str": return this.wrap([a], `\\text{“}${a.body.length ? a.body.map((x) => this.wrap([x], textChar((x as { c: string }).c))).join("") : this.hole(a.body)}\\text{”}`);
      // a set's braces, fitted to what they hold as parentheses are
      case "brace": return this.wrap([a], this.delims(this.block(a.body), "\\{", "\\}", "1"));
      // text no grammar here reads: its characters as typed, in the text face
      case "raw": return this.wrap([a], a.body.length ? a.body.map((x) => this.wrap([x], x.k === "ch" && x.c === "\n" ? "\\\\" : textChar((x as { c: string }).c))).join("") : this.hole(a.body));
      case "asset": return this.wrap([a], `\\htmlData{asset=1}{\\boxed{${Array.from(a.name).map(textChar).join("")}}}`);
      case "call": return this.wrap([a], this.call(a));
      case "let": {
        // `let f(x) =` names a function, so its name is a word like a call's; `let a =` names a value
        const kw = this.tag(this.classify("let", "keyword"), this.word("\\mathrm{let}"));
        if (!a.params) return this.wrap([a], `${kw}\\;${this.block(a.name)}\\;=\\;`);
        const params = `{${this.parens(a.params.map((p) => this.block(p)).join(",\\,"))}}`;
        return this.wrap([a], `${kw}\\;${this.word(this.block(a.name))}${params}\\;=\\;`);
      }
    }
  }

  /** One index of a part, from its characters: positions and names as elsewhere, `All` upright, a
   *  span's `;;`, a list's braces, and a name in quotes as text. */
  private spec(b: Block): string {
    if (!b.length) return this.hole(b);
    let s = "";
    let j = 0;
    while (j < b.length) {
      const a = b[j] as Atom & { k: "ch" };
      if (a.c === '"') {
        // the quoted name, up to and including its closing quote
        let k = j + 1;
        while (k < b.length && (b[k] as { c: string }).c !== '"') k++;
        const inner = b.slice(j + 1, k) as (Atom & { k: "ch" })[];
        s += this.wrap([a], "\\text{“}") + inner.map((x) => this.wrap([x], textChar(x.c))).join("");
        if (k < b.length) s += this.wrap([b[k]!], "\\text{”}");
        j = k + 1;
        continue;
      }
      if (a.c === "{" || a.c === "}") { s += this.wrap([a], a.c === "{" ? "\\{" : "\\}"); j++; continue; }
      if (a.c === ";") { s += this.wrap([a], "{;}"); j++; continue; }
      if (a.c === ",") { s += this.wrap([a], ",\\,"); j++; continue; }
      // a run of anything else reads as the engine's tokens do: names, numerals, a minus
      const run: (Atom & { k: "ch" })[] = [];
      while (j < b.length && !'"{};,'.includes((b[j] as { c: string }).c)) run.push(b[j++] as Atom & { k: "ch" });
      s += tokens(run).map((t) => {
        const text = t.atoms.map((x) => (x as { c: string }).c).join("");
        return t.kind === "name" && text === "All" ? this.wrap(t.atoms, this.word("\\mathrm{All}")) : this.token(t);
      }).join("");
    }
    return s;
  }

  private matrix(rows: Block[][], env: string): string {
    return `\\begin{${env}}` + rows.map((r) => r.map((x) => this.block(x)).join(" & ")).join(" \\\\ ") + `\\end{${env}}`;
  }

  private call(a: Atom & { k: "call" }): string {
    // a binder's variable is bound over the whole call: `diff(x^2, x)`
    const i = BINDERS[a.name], v = i === undefined ? null : nameOf(a.args[i] ?? []);
    if (v) this.bound.push(v);
    try { return this.callInner(a); } finally { if (v) this.bound.pop(); }
  }

  private callInner(a: Atom & { k: "call" }): string {
    const b = a.args;
    const x = (i: number) => this.block(b[i]!);
    const n = b.length;
    switch (`${a.name}/${n}`) {
      case "sqrt/1": return `\\sqrt{${x(0)}}`;
      case "abs/1": return this.delims(x(0), "\\lvert ", "\\rvert ", "1", false, "abs");
      case "norm/1": return this.delims(x(0), "\\lVert ", "\\rVert ", "1", false, "norm");
      case "conj/1": return `\\overline{${x(0)}}`;
      // names shown as the textbook writes them, but names all the same: words, like `sin(`
      case "re/1": return this.named(a, "Re");
      case "im/1": return this.named(a, "Im");
      case "sign/1": return this.named(a, "sgn");
      case "diff/2": return `\\frac{d}{d${x(1)}}${this.parens(x(0))}`;
      case "diff/3": return `\\frac{d^{${this.scripted(b[2]!)}}}{d{${x(1)}}^{${this.scripted(b[2]!)}}}${this.parens(x(0))}`;
      case "integrate/2": return `\\int ${x(0)} \\, d${x(1)}`;
      case "integrate/4": return `\\int_{${this.scripted(b[2]!)}}^{${this.scripted(b[3]!)}} ${x(0)} \\, d${x(1)}`;
      case "sum/4": return `\\sum_{${this.scripted(b[1]!)}=${this.scripted(b[2]!)}}^{${this.scripted(b[3]!)}} ${x(0)}`;
      case "det/1": {
        const m = b[0]![0];
        if (b[0]!.length === 1 && m?.k === "matrix") return this.wrap([m], this.matrix(m.rows, "vmatrix"));
        return this.called(this.word("\\mathrm{det}"), x(0), a.open);
      }
      case "transpose/1": return `{${this.operand(b[0]!)}}^{\\mathsf{T}}`;
      case "dot/2": return `${this.operand(b[0]!)} \\cdot ${this.operand(b[1]!)}`;
    }
    const args = b.map((_, i) => x(i)).join(", ");
    // the name as typed, in the text face, right against its parentheses as in the text (`\\sin` and
    // `\\operatorname` are operators, which KaTeX spaces off from the `(`)
    const head = `\\mathrm{${Array.from(a.name).map(charLatex).join("")}}`;
    return this.called(this.tag(this.classify(a.name, "call"), this.word(head)), args, a.open);
  }
}

/** The size of a fraction's parts by how many fractions it is inside (KaTeX's sizes are absolute). */
const FRAC_SIZES = ["", "", "\\small ", "\\footnotesize ", "\\scriptsize "];

/** The name a slot holds when it is just one name (`x`, `k`), else null. */
function nameOf(b: Block): string | null {
  if (!b.length || !b.every((a) => a.k === "ch")) return null;
  const ts = tokens(b as (Atom & { k: "ch" })[]);
  return ts.length === 1 && ts[0]!.kind === "name" ? b.map((a) => (a as { c: string }).c).join("") : null;
}

/** Does a block show anything the text could not — a fraction, a power, a matrix, or a call drawn in
 *  its own notation? Where it does not (`epicycles(llama, 60)`), the notebook's Auto mode keeps the
 *  cell as highlighted text. */
export function hasNotation(b: Block): boolean {
  return b.some((a) => (a.k === "ch" && ASCII_GLYPHS.has(a.c)) || a.k === "frac" || a.k === "sup" || a.k === "matrix" || a.k === "part" || (a.k === "call" && notated(a)) || slots(a).some(hasNotation));
}

/** Calls drawn in their own notation (d/dx, ∫, Σ, √, bars, …) rather than as `name(args)`; must
 *  agree with `Notation.call`. */
const NOTATED = new Set(["sqrt/1", "abs/1", "norm/1", "conj/1", "re/1", "im/1", "sign/1", "diff/2", "diff/3",
  "integrate/2", "integrate/4", "sum/4", "det/1", "transpose/1", "dot/2"]);
export const notated = (a: Atom & { k: "call" }) => NOTATED.has(`${a.name}/${a.args.length}`);

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
    case "part": return a.specs;
    case "str": case "brace": case "raw": return [a.body];
    case "asset": return [];
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
