/**
 * The visual editor's tree. A cell's source text stays the only thing saved and sent to the engine;
 * this is a view of that text, read from it (`read.ts`) and written back to it (`write.ts`) only when
 * the reader edits in visual mode. The tree carries notation, never meaning: `diff(f, x)` is a call
 * named `diff` whatever it shows as, and what the text means is the engine's parse of it.
 *
 * A block is a row of atoms; an empty block is a hole. Characters are atoms of their own so a caret
 * can sit between any two of them. `/`, `^`, `(`, `)`, `[`, `]`, `,` and `;` never appear as
 * characters: a fraction, a power, a group, a call's arguments and a matrix's entries are structure.
 */

export type Block = Atom[];

export type Atom =
  /** One character of a numeral, a name, an operator (`+ - *`), an output reference (`%`), or a
   *  space: the product of two names (`x y`), which written together would be one name (`xy`). */
  | { k: "ch"; c: string }
  /** `num / den`. The numerator is everything the `/` takes on its left: `2x/3` is 2x over 3. */
  | { k: "frac"; num: Block; den: Block }
  /** A power of the atom before it: `x^2` is the character `x` followed by `sup [2]`. */
  | { k: "sup"; exp: Block }
  | { k: "paren"; body: Block }
  /** `name(args)`: a builtin or a function the session defined. How it shows (d/dx, ∫, |·|) is
   *  `notation.ts`'s choice; the tree only knows the name. */
  | { k: "call"; name: string; args: Block[] }
  | { k: "matrix"; rows: Block[][] }
  /** `let name =` or `let f(x, y) =`: the cell's head, only ever first in the body. The name and the
   *  parameters are slots like any other, so the caret goes through them. */
  | { k: "let"; name: Block; params: Block[] | null };

/** A cell: its body, which may start with a `let` head. */
export interface Stmt { body: Block }

/** A cell's `let` head as text: the name and the parameters (null for `let name =`). */
export function letHead(stmt: Stmt): { name: string; params: string[] | null } | null {
  const h = stmt.body[0];
  if (h?.k !== "let") return null;
  const text = (b: Block) => b.map((a) => (a.k === "ch" ? a.c : "")).join("");
  return { name: text(h.name), params: h.params ? h.params.map(text) : null };
}

export const ch = (c: string): Atom => ({ k: "ch", c });
export const chars = (s: string): Atom[] => Array.from(s, ch);

// --- the lexer's character classes, as the engine has them (`Parser.lean`, `lex`) ---------------

/** Greek α … ω (and the capitals between) and the script ℯ are name characters. */
export const isGreek = (c: string) => { const v = c.codePointAt(0)!; return (0x391 <= v && v <= 0x3c9) || c === "ℯ"; };
/** Lean's `Char.isAlpha` / `isDigit` are ASCII only. */
export const isAsciiAlpha = (c: string) => /^[A-Za-z]$/.test(c);
export const isDigit = (c: string) => /^[0-9]$/.test(c);
export const isIdStart = (c: string) => isAsciiAlpha(c) || c === "_" || isGreek(c);
export const isIdChar = (c: string) => isAsciiAlpha(c) || isDigit(c) || c === "_" || c === "'" || isGreek(c);

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
    case "let": return b.k === "let" && sameBlock(a.name, b.name) && (a.params === null ? b.params === null
      : b.params !== null && a.params.length === b.params.length && a.params.every((x, i) => sameBlock(x, b.params![i]!)));
  }
}
export const sameStmt = (a: Stmt, b: Stmt): boolean => sameBlock(a.body, b.body);

/** A compact rendering of a tree for tests and debugging: `(frac [2 x] [3])`. */
export function show(b: Block): string {
  return "[" + b.map(showAtom).join(" ") + "]";
}
function showAtom(a: Atom): string {
  switch (a.k) {
    case "ch": return a.c === " " ? "␣" : a.c;
    case "frac": return `(frac ${show(a.num)} ${show(a.den)})`;
    case "sup": return `(^ ${show(a.exp)})`;
    case "paren": return `(paren ${show(a.body)})`;
    case "call": return `(${a.name} ${a.args.map(show).join(" ")})`;
    case "matrix": return `(matrix ${a.rows.map((r) => r.map(show).join(" ")).join(" ; ")})`;
    case "let": return `(let ${show(a.name)}${a.params ? " " + a.params.map(show).join(" ") : ""})`;
  }
}
