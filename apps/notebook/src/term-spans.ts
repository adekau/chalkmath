import { lex } from "@chalkmath/math-editor";

/**
 * Where each subterm of a cell's input interpretation came from in its source text. The engine
 * renders the input with every subterm tagged by its path (`\htmlData{path=0.1}`) but does not say
 * where in the text a subterm was written, so the page finds out: the interpretation's leaves (names,
 * numbers) are the source's names and numbers, in the same order when taken in path order, so each
 * leaf is matched to its token, and a subterm spans its leaves' tokens, widened to whole brackets,
 * to the call it is the argument list of, or to the `not`/`-` in front of it.
 *
 * A prototype's approximation (a leaf the parser made up, `-1` in `a - b`, matches nothing and is
 * skipped); the exact answer is the parser recording each node's span.
 */

export interface Span { start: number; end: number }
export interface TermSpan {
  path: string;
  parent: string | null;
  children: string[];
  /** The subterm's own text; `outer` adds the parentheses that only group it. Null: not found. */
  inner: Span | null;
  outer: Span | null;
}

type Range = [number, number];   // token indices, inclusive

const PREFIX = new Set(["-", "+", "not", "¬", "!", "~"]);
const POSTFIX = new Set(["!", "'"]);
const OPENERS: Record<string, string> = { "(": ")", "[": "]", "{": "}" };

const comps = (p: string) => (p === "root" ? [] : p.split(".").map(Number));
function preorder(a: string, b: string) {
  const x = comps(a), y = comps(b);
  for (let k = 0; k < Math.min(x.length, y.length); k++) if (x[k] !== y[k]) return x[k]! - y[k]!;
  return x.length - y.length;
}

/** `nodes`: every tagged subterm of the rendering, with its text as shown. `symbols`: the `\name`
 *  spellings of symbols (`pi` → `π`), so a name typed as a word matches the symbol shown. */
export function termSpans(src: string, nodes: { path: string; text: string }[], symbols: Record<string, string> = {}): Map<string, TermSpan> {
  const toks = lex(src).filter((t) => t.kind !== "eof");
  const paths = new Set(nodes.map((n) => n.path));
  paths.add("root");
  const text = new Map(nodes.map((n) => [n.path, n.text]));
  const out = new Map<string, TermSpan>();
  for (const p of paths) out.set(p, { path: p, parent: null, children: [], inner: null, outer: null });
  // the nearest tagged ancestor is the parent (the printer leaves some nodes untagged: `-x`'s product)
  for (const p of paths) {
    if (p === "root") continue;
    let c = comps(p), parent = "root";
    while (c.length > 1) { c = c.slice(0, -1); if (paths.has(c.join("."))) { parent = c.join("."); break; } }
    out.get(p)!.parent = parent;
    out.get(parent)!.children.push(p);
  }
  for (const n of out.values()) n.children.sort(preorder);

  // brackets, matched
  const match: number[] = toks.map(() => -1);
  const stack: number[] = [];
  toks.forEach((t, i) => {
    if (t.kind !== "op") return;
    if (OPENERS[t.s]) stack.push(i);
    else if (Object.values(OPENERS).includes(t.s)) {
      const j = stack.pop();
      if (j !== undefined && OPENERS[toks[j]!.s] === t.s) { match[i] = j; match[j] = i; }
    }
  });
  const s = (i: number) => toks[i]?.s;
  const isId = (i: number) => toks[i]?.kind === "id";
  const operand = (i: number) => !!toks[i] && (toks[i]!.kind === "num" || toks[i]!.kind === "id" && !PREFIX.has(toks[i]!.s) || s(i) === ")" || s(i) === "]");

  const balance = ([a, b]: Range): Range => {
    for (let moved = true; moved;) {
      moved = false;
      for (let i = a; i <= b; i++) {
        const m = match[i]!;
        if (m >= 0 && (m < a || m > b)) { a = Math.min(a, m); b = Math.max(b, m); moved = true; }
      }
    }
    return [a, b];
  };
  const topComma = ([a, b]: Range) => {
    for (let i = a, d = 0; i <= b; i++) {
      if (match[i]! > i) d++; else if (match[i]! >= 0 && match[i]! < i) d--;
      else if (d === 0 && s(i) === ",") return true;
    }
    return false;
  };
  /** The parentheses that only group (not a call's, not an index's). */
  const widen = ([a, b]: Range): Range => {
    while (s(a - 1) === "(" && match[a - 1] === b + 1 && !(isId(a - 2) && !PREFIX.has(s(a - 2)!)) && s(a - 2) !== ")" && s(a - 2) !== "]") { a--; b++; }
    return [a, b];
  };

  // leaves to tokens, in path order
  const same = (tok: string, shown: string) => tok === shown || symbols[tok] === shown;
  const ranges = new Map<string, { inner: Range; outer: Range } | null>();
  let next = 0;
  for (const p of [...paths].sort(preorder)) {
    if (out.get(p)!.children.length || p === "root") continue;
    const shown = (text.get(p) ?? "").replace(/[\s​]/g, "").replace(/−/g, "-");
    let k = next;
    while (k < toks.length && !((toks[k]!.kind === "num" || toks[k]!.kind === "id" || toks[k]!.kind === "str") && same(toks[k]!.s, shown))) k++;
    if (k < toks.length) { ranges.set(p, { inner: [k, k], outer: widen([k, k]) }); next = k + 1; }
    else ranges.set(p, null);
  }

  // the rest, innermost first
  const byDepth = [...paths].filter((p) => p !== "root" && out.get(p)!.children.length).sort((a, b) => comps(b).length - comps(a).length);
  for (const p of byDepth) {
    const kids = out.get(p)!.children.map((c) => ranges.get(c)).filter((r): r is { inner: Range; outer: Range } => !!r);
    if (!kids.length) { ranges.set(p, null); continue; }
    let r = balance([Math.min(...kids.map((k) => k.outer[0])), Math.max(...kids.map((k) => k.outer[1]))]);
    const sameAsChild = kids.some((k) => k.outer[0] === r[0] && k.outer[1] === r[1]);
    if (sameAsChild || topComma(r)) {
      if (s(r[0] - 1) === "(" && match[r[0] - 1] === r[1] + 1 && isId(r[0] - 2)) r = [r[0] - 2, r[1] + 1];   // a call: name(args)
      else if (sameAsChild && PREFIX.has(s(r[0] - 1) ?? "") && !operand(r[0] - 2)) r = [r[0] - 1, r[1]];   // not p, -x
      else if (sameAsChild && POSTFIX.has(s(r[1] + 1) ?? "")) r = [r[0], r[1] + 1];   // n!
    }
    ranges.set(p, { inner: r, outer: widen(r) });
  }
  // the root is the whole input, after a `let name =` head
  let first = 0;
  if (s(0) === "let") { const eq = toks.findIndex((t) => t.s === "=" || t.s === ":="); if (eq >= 0) first = eq + 1; }
  if (first < toks.length) ranges.set("root", { inner: [first, toks.length - 1], outer: [first, toks.length - 1] });

  const chars = (r: Range): Span => ({ start: toks[r[0]]!.start, end: toks[r[1]]!.stop });
  for (const [p, r] of ranges) if (r) { const n = out.get(p)!; n.inner = chars(r.inner); n.outer = chars(r.outer); }
  return out;
}

const splice = (src: string, at: Span, by: string) => { const cs = Array.from(src); return cs.slice(0, at.start).join("") + by + cs.slice(at.end).join(""); };
/** Spacing an edit left doubled, and parentheses left around one name (`(q) implies r`). */
const tidy = (s: string) => s.replace(/ {2,}/g, " ").replace(/\(\s+/g, "(").replace(/\s+\)/g, ")").replace(/\s+,/g, ",")
  .replace(/(^|[^\p{L}\p{N}_)\]])\(([\p{L}\p{N}_.]+)\)/gu, "$1$2").trim();

/** The source without the subterm at `path`, and the operator or comma that joined it to its
 *  neighbour: `p and q implies r` without `q` is `p implies r`. A subterm that is its parent's only
 *  part (`p` in `not p`, `x` in `sin(x)`) takes the parent with it. Null: not found in the text. */
export function deleteTerm(src: string, spans: Map<string, TermSpan>, path: string): string | null {
  const n = spans.get(path);
  if (!n?.outer) return null;
  if (path === "root") return tidy(splice(src, n.outer, ""));
  const parent = spans.get(n.parent!)!;
  const sibs = parent.children.map((c) => spans.get(c)!).filter((c) => c.outer).sort((a, b) => a.outer!.start - b.outer!.start);
  if (sibs.length < 2) return deleteTerm(src, spans, parent.path);
  const k = sibs.indexOf(n);
  const cut = k > 0 ? { start: sibs[k - 1]!.outer!.end, end: n.outer.end } : { start: n.outer.start, end: sibs[1]!.outer!.start };
  return tidy(splice(src, cut, ""));
}

/** The source with the subterm at `path` replaced by `by`, in parentheses unless it is one piece
 *  (a name, a number, a call, a group), so it stays one subterm: `q` → `a or b` in `p and q` is
 *  `p and (a or b)`. */
export function replaceTerm(src: string, spans: Map<string, TermSpan>, path: string, by: string): string | null {
  const n = spans.get(path);
  if (!n?.outer) return null;
  const t = by.trim();
  const whole = (x: string) => { let d = 0; for (const [i, c] of Array.from(x).entries()) { if (c === "(") d++; if (c === ")") { d--; if (d === 0 && i < Array.from(x).length - 1) return false; } } return d === 0; };
  const piece = /^[\p{L}\p{N}_.']+$/u.test(t) || (/^[\p{L}_][\p{L}\p{N}_]*\(.*\)$/u.test(t) && whole(t.slice(t.indexOf("(")))) || (t.startsWith("(") && t.endsWith(")") && whole(t));
  // a whole argument needs no parentheses of its own: `sin(y + z)`, not `sin((y + z))`
  const cs = Array.from(src);
  const before = cs.slice(0, n.outer.start).join("").trimEnd().slice(-1), after = cs.slice(n.outer.end).join("").trimStart()[0] ?? "";
  const alone = (before === "(" || before === ",") && (after === ")" || after === ",");
  return splice(src, n.outer, path === "root" || piece || alone ? t : `(${t})`);
}
