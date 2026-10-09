/**
 * The visual editor's tree. A cell's source text stays the only thing saved and sent to the engine;
 * this is a view of that text, read from it (`read.ts`) and written back to it (`write.ts`) only when
 * the reader edits in visual mode. The tree carries notation, never meaning: `diff(f, x)` is a call
 * named `diff` whatever it shows as, and what the text means is the engine's parse of it.
 *
 * Text and tree are one source shown two ways. Every text reads as a tree (what the grammar cannot
 * structure is a `raw` atom of its characters), and the tree writes back to exactly the text it was
 * read from: an atom read from text keeps its spelling and the space before it (`src`), and the
 * writer reuses them while the atom and its neighbours are as they were read. Only what an edit
 * touched is written afresh.
 *
 * A block is a row of atoms; an empty block is a hole. Characters are atoms of their own so a caret
 * can sit between any two of them. `/`, `^`, `(`, `)`, `[`, `]`, `{` and `}` never appear as
 * characters: a fraction, a power, a group, a call's arguments and a matrix's entries are structure.
 * `,` and `;` are characters only where they separate nothing structural (`{a, b}`, `poset(…; a<b)`).
 */

export type Block = Atom[];

/** Where an atom came from in the text it was read from: its spelling (`start`, `end` index the
 *  source's characters), the whitespace before it and, for the last atom of a block, after it, and
 *  the shapes it and its neighbours had then (`show`), which say whether the spelling still holds. */
export interface Src { start: number; end: number; text: string; gap: string; trail?: string; shape: string; prev: string; next: string }

export type Atom = AtomKind & { src?: Src };
type AtomKind =
  /** One character of a numeral, a name, an operator (`+ - *`), an output reference (`%`), or a
   *  space: the product of two names (`x y`), which written together would be one name (`xy`).
   *  The entrywise operators `./` and `.*` are the two atoms of two characters: one operator each. */
  | { k: "ch"; c: string }
  /** `num / den`. The numerator is everything the `/` takes on its left: `2x/3` is 2x over 3. */
  | { k: "frac"; num: Block; den: Block }
  /** A power of the atom before it: `x^2` is the character `x` followed by `sup [2]`. */
  | { k: "sup"; exp: Block }
  /** `open`: typed before existing atoms, the group took in everything to its right and its `)`
   *  is not placed yet (drawn faint); typing `)` places it. Editing state only: the text is the same. */
  | { k: "paren"; body: Block; open?: boolean;
      /** `head`: put in by `@`, which wraps the selection for a function to be named in front of it:
       *  until the caret leaves, an empty box there shows where the name goes, and the name (once it
       *  names a function) makes the group that function's call. Editing state only, as `open`. */
      head?: boolean }
  /** `name(args)`: a builtin or a function the session defined. How it shows (d/dx, ∫, |·|) is
   *  `notation.ts`'s choice; the tree only knows the name. */
  | { k: "call"; name: string; args: Block[]; open?: boolean }
  | { k: "matrix"; rows: Block[][] }
  /** `[[i, j]]`, Mathematica's Part, of the atom before it (like `sup`, it attaches on the left). Each
   *  index is a slot of characters kept as typed: `2;;-1`, `All`, `{1, 3}`, a name in quotes. */
  | { k: "part"; specs: Block[] }
  /** `"…"`: text, its characters kept as typed (`/` is a slash here, not a fraction). The engine has
   *  no strings; the notebook reads them where it gives them a meaning (`import("url")`). */
  | { k: "str"; body: Block }
  /** `{…}`: a set, as the order and logic worlds write one (`{a, b, c}`, `∃ n ∈ {4, 6}`). */
  | { k: "brace"; body: Block }
  /** Text no grammar here structures (an unclosed group, a question), its characters kept as typed. */
  | { k: "raw"; body: Block }
  /** `⟦name⟧`: a file attached to the notebook, one chip. */
  | { k: "asset"; name: string }
  /** `let name =` or `let f(x, y) =`: the cell's head, only ever first in the body. The name and the
   *  parameters are slots like any other, so the caret goes through them. */
  | { k: "let"; name: Block; params: Block[] | null };

/** A cell: its body, which may start with a `let` head. `pad`: the whitespace of a cell that has
 *  nothing else. */
export interface Stmt { body: Block; pad?: string }

/** A cell's `let` head as text: the name and the parameters (null for `let name =`). */
export function letHead(stmt: Stmt): { name: string; params: string[] | null } | null {
  const h = stmt.body[0];
  if (h?.k !== "let") return null;
  const text = (b: Block) => b.map((a) => (a.k === "ch" ? a.c : "")).join("");
  return { name: text(h.name), params: h.params ? h.params.map(text) : null };
}

export const ch = (c: string): Atom => ({ k: "ch", c });
export const chars = (s: string): Atom[] => Array.from(s, ch);

/** The line of a block of several lines (a system's declarations) that the position `i` is on: its
 *  atoms are `from` up to `to`, the line break that ends it (or the block's end). A position just
 *  before a break is the end of its line, one just after it the start of the next. */
export function lineOf(b: Block, i: number): { from: number; to: number } {
  let from = i, to = i;
  while (from > 0 && !isBreak(b[from - 1])) from--;
  while (to < b.length && !isBreak(b[to])) to++;
  return { from, to };
}
export const isBreak = (a: Atom | undefined) => a?.k === "ch" && a.c === "\n";

/** Calls whose parentheses hold one body, not arguments: a system's declarations (`Systems.lean`),
 *  where a `,` separates an action's updates (`do a := x, p := write`). */
export const BODY_CALLS = new Set(["system"]);

// --- the lexer's character classes, as the engine has them (`Parser.lean`, `lex`) ---------------

/** Greek α … ω (and the capitals between) and the script ℯ are name characters. */
export const isGreek = (c: string) => { const v = c.codePointAt(0)!; return (0x391 <= v && v <= 0x3c9) || c === "ℯ"; };
/** Lean's `Char.isAlpha` / `isDigit` are ASCII only. */
export const isAsciiAlpha = (c: string) => /^[A-Za-z]$/.test(c);
export const isDigit = (c: string) => /^[0-9]$/.test(c);
export const isIdStart = (c: string) => isAsciiAlpha(c) || c === "_" || isGreek(c);
export const isIdChar = (c: string) => isAsciiAlpha(c) || isDigit(c) || c === "_" || c === "'" || isGreek(c);

/** The other worlds' operators of more than one character, longest first: each is one atom, as the
 *  entrywise `./` and `.*` are. The engine publishes each world's glyphs (`capabilities.worlds`) and
 *  the host adds them with `configureLexicon`; this is the list as of this build, which the test
 *  `lexicon.test.mjs` holds equal to the engine's. */
export const MULTI_OPS: string[] = ["<->", ":=", "->", "<-", "=>", "&&", "||", "/\\", "\\/", "<=", ">=", "!=", "==", "|-", ".."];
/** Operators that stand between two things with a space either side when written afresh: comparisons,
 *  connectives, arrows, definitions. (`+`, a subtraction and the entrywise operators are spaced too.) */
export const INFIX = new Set(["=", "<", ">", "@", "≤", "≥", "≠", "∣", "|", "∈", "∉", "⊆", "⊂", "∪", "∩", "∧", "∨", "→", "↔", "⇒", "⊢", "←", "↦", "×",
  "<->", ":=", "->", "<-", "=>", "&&", "||", "/\\", "\\/", "<=", ">=", "!=", "==", "|-"]);
/** Constants the logic world writes as glyphs: values, not operators. */
export const isConst = (c: string) => c === "⊤" || c === "⊥";
/** Words the other worlds use as keywords. In a cell of those worlds they end a product: in
 *  `when a/2 < 1 do`, `a` alone is the numerator. As of this build (see `MULTI_OPS`); the engine's
 *  published keywords are added by `configureLexicon`. */
export const KEYWORDS = new Set(["var", "in", "init", "action", "when", "do", "fair", "strong", "forall", "exists",
  "and", "or", "not", "implies", "iff", "true", "false"]);

/** Take the worlds' lexicon from the engine (`capabilities.worlds`): their keywords end a product as
 *  the built-in ones do, and their operators of several characters are one atom each. The built-in
 *  lists stay, so a reader without an engine behaves as this build was tested; how an operator is
 *  spaced when written afresh (`INFIX`) is the editor's choice, not the engine's. */
export function configureLexicon(worlds: readonly { keywords?: readonly string[]; glyphs?: readonly string[] }[]): void {
  for (const w of worlds) {
    for (const k of w.keywords ?? []) if (/^[A-Za-z_][A-Za-z0-9_']*$/.test(k)) KEYWORDS.add(k);
    for (const g of w.glyphs ?? []) if (Array.from(g).length > 1 && !/\s/.test(g) && !MULTI_OPS.includes(g)) MULTI_OPS.push(g);
  }
  MULTI_OPS.sort((a, b) => b.length - a.length);
}
/** A character atom that separates rather than computes: anything but a name's or numeral's
 *  character, `%`, a constant, `+ - *` and the entrywise operators. */
export const isSep = (c: string) => !(isIdChar(c) || c === "." || c === "%" || c === " " || isConst(c) || "+-*".includes(c) || c === "./" || c === ".*");

/** Would `next` written right after `before` lex differently from `before next`? A name swallows a
 *  name or a numeral after it (`x y` → `xy`, `x 2` → `x2`), a numeral a numeral, and `%` reads an
 *  adjacent numeral as Out[n]. A digit ends a name or a numeral depending on the token it is in
 *  (`x2` against `2`), so this looks at the whole last token of `before`. */
export function merges(before: string, next: string): boolean {
  const cs = Array.from(before);
  let i = cs.length;
  while (i > 0 && (isIdChar(cs[i - 1]!) || cs[i - 1] === ".")) i--;
  if (i === cs.length) return cs[i - 1] === "%" && isDigit(next);
  // lex the trailing run forward, as the engine would: a numeral, then possibly a name
  let j = i, last: "name" | "num" = "num";
  while (j < cs.length) {
    if (isIdStart(cs[j]!)) { last = "name"; while (j < cs.length && isIdChar(cs[j]!)) j++; }
    else { last = "num"; j++; while (j < cs.length && (isDigit(cs[j]!) || cs[j] === ".")) j++; }
  }
  return last === "name" ? isIdChar(next) : isDigit(next) || next === ".";
}

/** The indent of the line that starts at `j` of `b`, just after a line break: the space before the
 *  atom read first on that line, wherever typing at the line's start has since put it (whatever is
 *  typed there takes the indent over). Undefined for a line no atom of which was read first on it. */
export function lineIndent(b: Block, j: number): string | undefined {
  for (let k = j; k < b.length; k++) {
    const a = b[k]!;
    if (a.k === "ch" && a.c === "\n") return undefined;
    if (a.src?.prev === "\n") return a.src.gap;
  }
  return undefined;
}

/** Structural equality, for tests and for the editor's "did this edit change anything". */
export function sameBlock(a: Block, b: Block): boolean {
  return a.length === b.length && a.every((x, i) => sameAtom(x, b[i]!));
}
export function sameAtom(a: Atom, b: Atom): boolean {
  switch (a.k) {
    case "ch": return b.k === "ch" && a.c === b.c;
    case "frac": return b.k === "frac" && sameBlock(a.num, b.num) && sameBlock(a.den, b.den);
    case "sup": return b.k === "sup" && sameBlock(a.exp, b.exp);
    case "paren": return b.k === "paren" && sameBlock(a.body, b.body);
    case "call": return b.k === "call" && a.name === b.name && a.args.length === b.args.length && a.args.every((x, i) => sameBlock(x, b.args[i]!));
    case "matrix": return b.k === "matrix" && a.rows.length === b.rows.length &&
      a.rows.every((r, i) => r.length === b.rows[i]!.length && r.every((x, j) => sameBlock(x, b.rows[i]![j]!)));
    case "part": return b.k === "part" && a.specs.length === b.specs.length && a.specs.every((x, i) => sameBlock(x, b.specs[i]!));
    case "str": return b.k === "str" && sameBlock(a.body, b.body);
    case "brace": return b.k === "brace" && sameBlock(a.body, b.body);
    case "raw": return b.k === "raw" && sameBlock(a.body, b.body);
    case "asset": return b.k === "asset" && a.name === b.name;
    case "let": return b.k === "let" && sameBlock(a.name, b.name) && (a.params === null ? b.params === null
      : b.params !== null && a.params.length === b.params.length && a.params.every((x, i) => sameBlock(x, b.params![i]!)));
  }
}
export const sameStmt = (a: Stmt, b: Stmt): boolean => sameBlock(a.body, b.body);

/** A compact rendering of a tree for tests and debugging: `(frac [2 x] [3])`. */
export function show(b: Block): string {
  return "[" + b.map(showAtom).join(" ") + "]";
}
export function showAtom(a: Atom): string {
  switch (a.k) {
    case "ch": return a.c === " " ? "␣" : a.c;
    case "frac": return `(frac ${show(a.num)} ${show(a.den)})`;
    case "sup": return `(^ ${show(a.exp)})`;
    case "paren": return `(paren ${show(a.body)})`;
    case "call": return `(${a.name} ${a.args.map(show).join(" ")})`;
    case "matrix": return `(matrix ${a.rows.map((r) => r.map(show).join(" ")).join(" ; ")})`;
    case "part": return `(part ${a.specs.map(show).join(" ")})`;
    case "str": return `(str ${show(a.body)})`;
    case "brace": return `(brace ${show(a.body)})`;
    case "raw": return `(raw ${show(a.body)})`;
    case "asset": return `⟦${a.name}⟧`;
    case "let": return `(let ${show(a.name)}${a.params ? " " + a.params.map(show).join(" ") : ""})`;
  }
}
