import { KEYWORDS, lex } from "@chalkmath/math-editor";

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
/** Each subterm's place in the source, and whether the reading is the input itself: every name and
 *  number written appears in it. A world's summary of its input is not (`system(…)` read as its
 *  variables and actions, its declarations gone), and must not stand in for it. */
export interface Reading { spans: Map<string, TermSpan>; faithful: boolean }
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
/** Words that are operators, not names: a reading shows them as symbols, never as leaves. */
const WORD_OPS = new Set(["and", "or", "not", "implies", "iff", "xor", "forall", "exists", "in"]);
/** The calls the reading draws as notation rather than by name: d/dx, ∫, √, |·|, Σ, eˣ, z̄. */
const DRAWN = new Set(["diff", "integrate", "sqrt", "abs", "sum", "exp", "conj"]);
/** Constants the reading shows as symbols. */
const WORD_SYMS: Record<string, string> = { true: "⊤", false: "⊥" };

const comps = (p: string) => (p === "root" ? [] : p.split(".").map(Number));
function preorder(a: string, b: string) {
  const x = comps(a), y = comps(b);
  for (let k = 0; k < Math.min(x.length, y.length); k++) if (x[k] !== y[k]) return x[k]! - y[k]!;
  return x.length - y.length;
}

/** `nodes`: every tagged subterm of the rendering, with its text as shown. `symbols`: the `\name`
 *  spellings of symbols (`pi` → `π`), so a name typed as a word matches the symbol shown. */
export function termSpans(src: string, nodes: { path: string; text: string }[], symbols: Record<string, string> = {}): Reading {
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

  // what the reading is of: the input after a `let name =` or `let f(x) =` head
  let first = 0;
  if (s(0) === "let") { const eq = toks.findIndex((t) => t.s === "=" || t.s === ":="); if (eq >= 0) first = eq + 1; }

  // leaves to tokens, in path order (a reading of one number or name is a leaf itself)
  // the reading shows Euler's number as a plain e, however it was typed
  const same = (tok: string, shown: string) => tok === shown || symbols[tok] === shown || WORD_SYMS[tok] === shown || (tok === "ℯ" && shown === "e");
  const matched = new Set<number>();
  const ranges = new Map<string, { inner: Range; outer: Range } | null>();
  let next = first;
  for (const p of [...paths].sort(preorder)) {
    if (out.get(p)!.children.length) continue;
    const shown = (text.get(p) ?? "").replace(/[\s​]/g, "").replace(/−/g, "-");
    // a leaf is one token, or a literal the reading shows whole: `7/10` (as a fraction), `-3`
    const at = (k: number): number => {
      const t = toks[k]!, u = toks[k + 1], v = toks[k + 2];
      if ((t.kind === "num" || t.kind === "id" || t.kind === "str") && same(t.s, shown)) return k;
      // KaTeX sets a fraction's denominator first in its text
      if (t.kind === "num" && u?.s === "/" && v?.kind === "num" && (t.s + v.s === shown || v.s + t.s === shown)) return k + 2;
      if (t.s === "-" && u?.kind === "num" && `-${u.s}` === shown && !operand(k - 1)) return k + 1;
      return -1;
    };
    let k = next, end = -1;
    while (k < toks.length && (end = at(k)) < 0) k++;
    if (end >= 0) { ranges.set(p, { inner: [k, end], outer: widen([k, end]) }); for (let j = k; j <= end; j++) matched.add(j); next = end + 1; }
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
  if (first < toks.length) ranges.set("root", { inner: [first, toks.length - 1], outer: [first, toks.length - 1] });

  const chars = (r: Range): Span => ({ start: toks[r[0]]!.start, end: toks[r[1]]!.stop });
  for (const [p, r] of ranges) if (r) { const n = out.get(p)!; n.inner = chars(r.inner); n.outer = chars(r.outer); }
  // every number and name after the head is in the reading (the words that are operators or a
  // world's keywords are shown as notation, not as leaves), every call by its name or its notation
  // (`divisors(12)` read as `12` is not the input), and nothing else is: a `%` read as the output it
  // names, say
  const whole = (text.get("root") ?? "").replace(/\s/g, "");
  const leaves = [...paths].filter((p) => !out.get(p)!.children.length);
  const faithful = leaves.every((p) => ranges.get(p)) && toks.every((t, k) => k < first || matched.has(k) || t.kind === "op" || t.kind === "str" || t.kind === "asset"
    || (t.kind === "id" && (WORD_OPS.has(t.s) || KEYWORDS.has(t.s) || (s(k + 1) === "(" && (DRAWN.has(t.s) || whole.includes(t.s))))));
  return { spans: out, faithful };
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
