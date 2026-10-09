/**
 * The notebook's two smallest helpers, shared by its modules: an element with a class and text, and
 * KaTeX's HTML for a LaTeX string, kept in a bounded memo.
 */
import katex from "katex";

export const h = (tag: string, cls?: string, text?: string) => {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
};

/** The one trusted KaTeX command is `\htmlData`, which carries the engine's subterm paths. LaTeX can
 *  come from a file someone else wrote (saved outputs render before any re-run), and a blanket
 *  `trust: true` would let it add `\href{javascript:…}`, arbitrary styles, or remote images. */
export const TRUST_PATHS = (ctx: { command: string }) => ctx.command === "\\htmlData";
/** KaTeX's HTML for a LaTeX string, kept: a cell's output and steps are typeset again whenever the
 *  cells are rebuilt (a cell added, a section folded), and most of them have not changed. The memo
 *  is bounded; past the bound it starts over. */
const TEX_MEMO = new Map<string, string>();
const TEX_MEMO_MAX = 4000;
export const tex = (s: string, paths = false) => {
  const key = (paths ? "p" : "n") + s;
  const hit = TEX_MEMO.get(key);
  if (hit !== undefined) return hit;
  const html = katex.renderToString(s, { throwOnError: false, trust: paths ? TRUST_PATHS : false, strict: false, displayMode: false });
  if (TEX_MEMO.size >= TEX_MEMO_MAX) TEX_MEMO.clear();
  TEX_MEMO.set(key, html);
  return html;
};
