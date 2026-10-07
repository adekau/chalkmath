import katex from "katex";
import { MathEdit, TEMPLATES, type Caret } from "./edit.js";
import { isBreak, lineOf, type Atom, type Block, type Stmt } from "./model.js";
import { outRefOf, slots, toLatex } from "./notation.js";
import { read } from "./read.js";
import { atomsInSpan, write } from "./write.js";

/**
 * The visual input on a page. The tree is drawn by KaTeX — the LaTeX of `notation.ts` with every atom
 * and every hole tagged by `\htmlData`, so stretchy brackets, matrices and big operators come from
 * KaTeX and the input looks like the outputs — and the caret is a line drawn over it, placed from
 * the tagged boxes. Keys arrive in a hidden textarea, which also takes IME composition and a
 * phone's keyboard.
 *
 * Import from `@chalkmath/math-editor/view` (it needs a DOM; the rest of the package does not).
 */

export interface MathInputOptions {
  /** An editor to show, caret and undo history included (a template just opened in the cell's text). */
  edit?: MathEdit;
  /** Functions the session defined. */
  known?: readonly string[];
  /** The `\` symbols (the notebook passes its own table). */
  symbols?: Record<string, string>;
  /** The accessible name, e.g. "Cell 3, math input". */
  label?: string;
  /** After every edit: the source text, and how many slots are still empty. */
  onChange?(text: string, holes: number): void;
  /** Enter (after a pending `\\name` has been finished). */
  onEnter?(): void;
  /** The input took the focus, or lost it. */
  onFocus?(): void;
  onBlur?(): void;
  /** The caret moved or the text changed (signature help follows the caret). */
  onCaret?(): void;
  /** ↑ or ↓ with nowhere to go inside the input. */
  onLeave?(dir: -1 | 1): void;
  /** A key, before the input handles it; return true to take it (a completion menu's arrows). */
  onKey?(ev: KeyboardEvent): boolean;
  /** What an output reference (`%`, `%%`, `%3`) stands for: the output's number (shown beside a
   *  relative one) and its text (for the tooltip). `editing`: the input has the focus, so a relative
   *  one should say what a run now would use; the host also says so (`pending`) when the cell has
   *  not run. */
  outRef?(ref: string, editing: boolean): { label: number; value?: string; pending?: boolean } | null;
  /** Highlight classes for tokens (see `NotationOptions.classify`); the page styles `[data-hl=…]`. */
  classify?(text: string, as: "call" | "bound" | "name" | "num" | "keyword"): string | null;
  /** The functions whose names start with what is being typed, for the completion list (the host
   *  knows its commands and the session's functions); none, no list for plain names. */
  functions?(prefix: string): { name: string; what: string; call?: boolean }[];
  /** In an index of a part (`t[[All, "ma`): the names that can go there (a table's columns, an
   *  object's keys, `All`), given the cell's text up to the caret. */
  partNames?(before: string): { name: string; what: string }[];
  /** A paste, before the input reads it: the host takes it (an image, an SVG) by preventing its default. */
  onPaste?(ev: ClipboardEvent): void;
}

/** The styles the input needs; added to the page once. Colours come from the page's `--mi-*`
 *  properties where it sets them. */
export const MATH_INPUT_CSS = `
.mi { position:relative; display:inline-block; min-width:2em; min-height:1.4em; padding:2px 4px; cursor:text; outline:none; }
.mi-math .katex { font-size:1.15em; }
.mi-math [data-h], .mi-math [data-fh] { color:var(--mi-hole, #8a8a8a); }
.mi-caret { position:absolute; width:1.5px; background:var(--mi-caret, currentColor); pointer-events:none; display:none; }
.mi.focused .mi-caret { display:block; animation:mi-blink 1.06s steps(1) infinite; }
.mi.focused { box-shadow:0 0 0 1px var(--mi-focus, #6b8afd); border-radius:4px; }
.mi.focused .mi-math [data-h].mi-here { color:var(--mi-caret, currentColor); }
.mi-cmd { color:var(--mi-cmd, #b0662c); }
.mi-math .mi-err { background:var(--mi-err-bg, rgba(192,57,43,0.12)); box-shadow:0 2px 0 var(--mi-err, #c0392b); border-radius:2px 2px 0 0; }
.mi-math [data-word], .mi-math [data-word] * { font-family:var(--mi-word-font, ui-monospace, SFMono-Regular, Menlo, Consolas, monospace) !important; font-style:normal !important; }
.mi-math [data-word="1"] { font-size:var(--mi-word-size, 0.8em); }
.mi-math [data-word="s"] { font-size:0.8em; }
.mi-math .mi-tall { display:inline-block; }
.mi-math .mi-lift { position:relative; }
.mi-math .mi-tall > * { display:none; }
.mi-math .mi-tall > svg { display:block; position:static; width:100%; height:100%; stroke:none; }
.mi-math [data-open] { opacity:0.35; }
.mi-math [data-out] { background:var(--mi-chip, rgba(107,138,253,0.14)); border-radius:4px; padding:0 2px; }
.mi-math [data-out][data-rel] { background:transparent; outline:1px dashed var(--mi-chip-edge, rgba(107,138,253,0.6)); outline-offset:-1px; }
.mi-math [data-now] { opacity:0.55; }
.mi-math [data-next] { color:var(--mi-next, var(--mi-cmd, #b0662c)); }
.mi-math .mi-sel { background:var(--mi-sel, rgba(107,138,253,0.28)); border-radius:2px; }
.mi-ta { position:absolute; left:0; top:0; width:1px; height:1px; opacity:0; padding:0; border:0; resize:none; overflow:hidden; }
@keyframes mi-blink { 50% { opacity:0; } }
@media (prefers-reduced-motion: reduce) { .mi.focused .mi-caret { animation:none; } }
`;

function addStyles(doc: Document) {
  if (doc.getElementById("mi-styles")) return;
  const s = doc.createElement("style");
  s.id = "mi-styles";
  s.textContent = MATH_INPUT_CSS;
  doc.head.append(s);
}

let measure: CanvasRenderingContext2D | null | undefined;

/** The ink of an element's own text (a glyph's box is its font's line, taller than the glyph), or the
 *  box of a rule or a drawing; null for anything else. */
function inkOf(el: Element): { top: number; bottom: number; baseline: number } | null {
  const r = el.getBoundingClientRect();
  if (r.height <= 0) return null;
  if (el.tagName.toLowerCase() === "svg" || el.classList.contains("frac-line")) return { top: r.top, bottom: r.bottom, baseline: r.bottom };
  const text = [...el.childNodes].filter((n) => n.nodeType === Node.TEXT_NODE).map((n) => n.textContent).join("");
  if (!text.trim()) return null;
  const cs = getComputedStyle(el);
  measure ??= document.createElement("canvas").getContext("2d");
  if (!measure) return { top: r.top, bottom: r.bottom, baseline: r.bottom };
  measure.font = `${cs.fontStyle} ${cs.fontWeight} ${cs.fontSize} ${cs.fontFamily}`;
  const m = measure.measureText(text);
  if (!m.fontBoundingBoxAscent) return { top: r.top, bottom: r.bottom, baseline: r.bottom };
  const baseline = r.top + m.fontBoundingBoxAscent;
  return { top: baseline - m.actualBoundingBoxAscent, bottom: baseline + m.actualBoundingBoxDescent, baseline };
}

/** A paren `w` by `h` px as an SVG, drawn as TeX draws a tall one: a hook at each end and, when it
 *  is tall enough, a straight stroke between them. */
function paren(left: boolean, w: number, h: number, em: number): SVGSVGElement {
  const t = 0.075 * em, tip = 0.035 * em;
  const hook = Math.min(h / 2, 1.1 * em);
  const x0 = 0.08 * em, x1 = w - 0.06 * em, xi = x0 + t;
  const X = (x: number) => (left ? x : w - x).toFixed(2), Y = (y: number) => y.toFixed(2);
  const P = (x: number, y: number) => `${X(x)} ${Y(y)}`;
  const d = [
    `M${P(x1, 0)}`,
    `C${P(x1 - (x1 - x0) * 0.55, hook * 0.25)} ${P(x0, hook * 0.55)} ${P(x0, hook)}`,
    `L${P(x0, h - hook)}`,
    `C${P(x0, h - hook * 0.55)} ${P(x1 - (x1 - x0) * 0.55, h - hook * 0.25)} ${P(x1, h)}`,
    `L${P(x1, h - tip)}`,
    `C${P(x1 - (x1 - xi) * 0.5, h - hook * 0.35)} ${P(xi, h - hook * 0.6)} ${P(xi, h - hook)}`,
    `L${P(xi, hook)}`,
    `C${P(xi, hook * 0.6)} ${P(x1 - (x1 - xi) * 0.5, hook * 0.35)} ${P(x1, tip)}`,
    "Z",
  ].join(" ");
  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("width", String(w)); svg.setAttribute("height", String(h));
  svg.setAttribute("viewBox", `0 0 ${w} ${h}`);
  svg.setAttribute("aria-hidden", "true");
  const path = document.createElementNS(ns, "path");
  path.setAttribute("d", d);
  path.setAttribute("fill", "currentColor");
  svg.append(path);
  return svg;
}

/** `abs`'s bars (one line) or `norm`'s (two), `w` by `h` px, as an SVG. */
function bars(n: 1 | 2, w: number, h: number, em: number): SVGSVGElement {
  const t = 0.056 * em, gap = 0.2 * em;
  const xs = n === 1 ? [w / 2] : [w / 2 - gap / 2, w / 2 + gap / 2];
  const ns = "http://www.w3.org/2000/svg";
  const svg = document.createElementNS(ns, "svg");
  svg.setAttribute("width", String(w)); svg.setAttribute("height", String(h));
  svg.setAttribute("viewBox", `0 0 ${w} ${h}`);
  svg.setAttribute("aria-hidden", "true");
  for (const x of xs) {
    const r = document.createElementNS(ns, "rect");
    r.setAttribute("x", (x - t / 2).toFixed(2)); r.setAttribute("y", "0");
    r.setAttribute("width", t.toFixed(2)); r.setAttribute("height", h.toFixed(2));
    r.setAttribute("fill", "currentColor");
    svg.append(r);
  }
  return svg;
}

/** KaTeX may run only the one command the input emits; its LaTeX is built from the tree, but a name
 *  in it came from a file. */
const TRUST = (ctx: { command: string }) => ctx.command === "\\htmlData";

interface Box { x: number; top: number; bottom: number }

export class MathInput {
  readonly el: HTMLElement;
  readonly edit: MathEdit;
  private math: HTMLElement;
  private caretEl: HTMLElement;
  private ta: HTMLTextAreaElement;
  private atomEl = new Map<Atom, { el: HTMLElement; k: number; n: number }>();
  private holeEl = new Map<Block, HTMLElement>();
  private composing = false;
  /** The engine's error span on the last run, marked on the atoms it covers until the next edit. */
  private errSpan: { start: number; end: number } | null = null;
  /** A mouse drag in progress: where it started. */
  private drag: Caret | null = null;
  /** How far an atom drawn with fitted parens or bars reaches above and below its line, for the
   *  caret beside it (a KaTeX span's own box is its line). Kept by `fitParens`. */
  private tallOf = new Map<HTMLElement, { up: number; down: number }>();
  /** The input has the focus (it is being edited). */
  private get editing() { return this.el.classList.contains("focused"); }
  /** Whether the parens were last fitted with the input on screen. */
  private fitted = false;
  private resizer: ResizeObserver | undefined;
  /** The `\\` suggestions under the caret: the names that start with what has been typed. */
  /** The completion list: `\` commands, or (`fn`) functions for the name being typed. */
  private comp: { items: { name: string; what: string; glyph: string; fn?: boolean; index?: boolean; call?: boolean }[]; index: number; box: HTMLElement; picked?: boolean } | null = null;
  /** Esc closed the suggestions for this command; they come back when it changes. */
  private compDismissed: string | null = null;

  /** An input for `src`, or null when the text is not this grammar (the cell stays raw). */
  /** The input for a cell's text: any text, since every text reads (what has no structure as raw
   *  text), and it writes back as it was. */
  static fromSource(src: string, opts: MathInputOptions = {}): MathInput {
    return new MathInput(read(src, opts.known).stmt, opts);
  }

  constructor(stmt: Stmt, private opts: MathInputOptions = {}) {
    addStyles(document);
    this.edit = opts.edit ?? new MathEdit(stmt, { ...(opts.known ? { known: opts.known } : {}), ...(opts.symbols ? { symbols: opts.symbols } : {}) });
    this.el = document.createElement("div");
    this.el.className = "mi";
    this.math = document.createElement("div");
    this.math.className = "mi-math";
    this.caretEl = document.createElement("div");
    this.caretEl.className = "mi-caret";
    this.ta = document.createElement("textarea");
    this.ta.className = "mi-ta";
    this.ta.autocapitalize = "off"; this.ta.spellcheck = false;
    this.ta.setAttribute("autocorrect", "off"); this.ta.setAttribute("autocomplete", "off");
    this.el.append(this.math, this.caretEl, this.ta);
    this.ta.addEventListener("focus", () => {
      this.el.classList.add("focused");
      // a relative output reference says, while the input is edited, what a run now would use
      if (this.math.querySelector("[data-rel]")) this.render(); else this.place();
      this.opts.onFocus?.();
    });
    this.ta.addEventListener("blur", () => {
      this.el.classList.remove("focused");
      this.hideSuggestions();
      // leaving the input places every `)` still open, as the text had them all along
      this.edit.closeAll();
      this.edit.settle(true);
      this.render();
      this.opts.onBlur?.();
    });
    this.ta.addEventListener("keydown", (ev) => this.key(ev));
    // the parens are fitted by measuring, so again once the input is on screen and its fonts are in
    this.resizer = new ResizeObserver(() => { if (!this.fitted) this.layout(); });
    this.resizer.observe(this.math);
    void document.fonts?.ready.then(() => this.layout());
    this.ta.addEventListener("compositionstart", () => { this.composing = true; });
    this.ta.addEventListener("compositionend", () => { this.composing = false; this.typed(); });
    this.ta.addEventListener("input", () => { if (!this.composing) this.typed(); });
    // Copy and Cut take the selection (or, with none, the whole input) as source text
    this.ta.addEventListener("copy", (ev) => { ev.clipboardData?.setData("text/plain", this.edit.selectedText() || this.text); ev.preventDefault(); });
    this.ta.addEventListener("cut", (ev) => {
      ev.preventDefault();
      if (!this.edit.selection()) return;
      ev.clipboardData?.setData("text/plain", this.edit.selectedText());
      this.edit.deleteSelection();
      this.changed();
    });
    this.ta.addEventListener("paste", (ev) => {
      this.opts.onPaste?.(ev);
      if (ev.defaultPrevented) return;
      const t = ev.clipboardData?.getData("text/plain");
      if (!t) return;
      ev.preventDefault();
      if (this.edit.paste(t)) this.changed();
    });
    // a click puts the caret; a drag selects; Shift+click extends the selection
    this.el.addEventListener("mousedown", (ev) => {
      ev.preventDefault();
      const c = this.caretAt(ev.clientX, ev.clientY);
      if (c) {
        if (ev.shiftKey) this.edit.extend(); else this.edit.anchor = null;
        this.edit.caret = c;
        this.edit.moved();
        this.drag = ev.shiftKey ? this.edit.anchor : { ...c };
      }
      this.focus(false);
      this.place();
      const move = (m: MouseEvent) => {
        const to = this.drag && this.caretAt(m.clientX, m.clientY);
        if (!to || !this.drag) return;
        this.edit.anchor = to.block === this.drag.block && to.i === this.drag.i ? null : this.drag;
        this.edit.caret = to;
        this.place();
      };
      const up = () => { this.drag = null; document.removeEventListener("mousemove", move); document.removeEventListener("mouseup", up); };
      document.addEventListener("mousemove", move);
      document.addEventListener("mouseup", up);
    });
    this.render();
  }

  get text(): string { return write(this.edit.stmt).text; }
  /** How many slots are still empty: text with a hole is not yet something to run. */
  get holes(): number { return write(this.edit.stmt).holes; }
  /** Focus the input, scrolling it into view (a click on it passes `scroll: false`: it is in view). */
  focus(scroll = true) {
    this.ta.focus({ preventScroll: true });
    if (scroll) this.el.scrollIntoView({ block: "nearest" });
  }

  // --- drawing -----------------------------------------------------------------------------------

  render() {
    const tagged: Atom[][] = [];
    const holes: Block[] = [];
    const latex = toLatex(this.edit.stmt, {
      wrap: (atoms, s) => { tagged.push(atoms); return `\\htmlData{a=${tagged.length - 1}}{${s}}`; },
      hole: (b) => { holes.push(b); return `\\htmlData{h=${holes.length - 1}}{\\square}`; },
      outRef: (ref) => this.opts.outRef?.(ref, this.editing) ?? null,
      ...(this.opts.classify ? { classify: (t: string, as: "call" | "bound" | "name" | "num" | "keyword") => this.opts.classify!(t, as) } : {}),
    });
    // display-size fractions and operators, as a textbook (and Symbolab) set an input, but left-aligned
    katex.render(`\\displaystyle ${latex}`, this.math, { throwOnError: false, trust: TRUST, strict: false, displayMode: false });
    this.fitParens();
    this.atomEl.clear(); this.holeEl.clear();
    // a slot drawn twice (dⁿ/dxⁿ shows n twice) is found at its first place
    for (const el of this.math.querySelectorAll<HTMLElement>("[data-a]")) {
      const atoms = tagged[+el.dataset["a"]!]!;
      atoms.forEach((a, k) => { if (!this.atomEl.has(a)) this.atomEl.set(a, { el, k, n: atoms.length }); });
    }
    for (const el of this.math.querySelectorAll<HTMLElement>("[data-h]")) {
      const b = holes[+el.dataset["h"]!]!;
      if (!this.holeEl.has(b)) this.holeEl.set(b, el);
    }
    // a `\\name` still being typed shows as a command, not as letters of a name
    const p = this.edit.pendingCommand();
    if (p) for (const a of this.edit.caret.block.slice(p.start, this.edit.caret.i)) this.atomEl.get(a)?.el.classList.add("mi-cmd");
    if (this.errSpan) for (const a of atomsInSpan(this.edit.stmt, this.errSpan)) this.atomEl.get(a)?.el.classList.add("mi-err");
    for (const el of this.math.querySelectorAll<HTMLElement>("[data-out]")) {
      const ref = outRefOf(el.dataset["out"]!);
      const r = this.opts.outRef?.(ref, this.editing);
      if (!r) continue;
      const out = `%${r.label}${r.value ? ` = ${r.value}` : ""}`;
      // a relative reference says what it means, and that it follows the outputs
      const what = `${ref}: the ${ref.length === 1 ? "last output" : `output ${ref.length} back`} when the cell runs`;
      el.title = !el.dataset["rel"] ? out : r.pending ? `${what}; run now, it takes ${out}` : `${what}; this output used ${out}`;
    }
    const text = this.text;
    this.ta.setAttribute("aria-label", `${this.opts.label ?? "Math input"}: ${text || "empty"}`);
    this.place();
  }

  /** Fit the parens to what they hold and place the caret. The input does this itself once it is on
   *  screen, a frame later; a host that has just put it there and wants its height now (to keep the
   *  page from moving) can call it. */
  layout() { this.fitParens(); this.place(); }

  /** Stretch each group's parentheses (or bars) over what it holds, where that is taller than a paren. KaTeX's
   *  `\\left(` would centre them on the math axis instead, so a stack of fractions that goes further
   *  below the axis than above it would get parens reaching as far above it again, over nothing. */
  private fitParens() {
    for (const d of this.math.querySelectorAll<HTMLElement>(".mi-tall")) {
      d.classList.remove("mi-tall");
      for (const p of ["width", "height", "vertical-align"]) d.style.removeProperty(p);
      d.querySelector(":scope > svg")?.remove();
    }
    for (const w of this.math.querySelectorAll<HTMLElement>(".mi-lift")) {
      w.classList.remove("mi-lift");
      w.style.removeProperty("top");
    }
    this.tallOf.clear();
    this.fitted = this.math.getClientRects().length > 0;
    if (!this.fitted) return;
    try { this.fitGroups(); } finally { this.measureTall(); }
  }

  private measureTall() {
    for (const el of this.math.querySelectorAll<HTMLElement>("[data-a]")) {
      const ts = el.querySelectorAll(".mi-tall");
      if (!ts.length) continue;
      const r = el.getBoundingClientRect();
      let top = r.top, bottom = r.bottom;
      for (const t of ts) { const q = t.getBoundingClientRect(); top = Math.min(top, q.top); bottom = Math.max(bottom, q.bottom); }
      this.tallOf.set(el, { up: r.top - top, down: bottom - r.bottom });
    }
  }

  private fitGroups() {
    // the innermost first, so an outer group measures its inner groups' parens as fitted
    for (const g of [...this.math.querySelectorAll<HTMLElement>("[data-pg]")].reverse()) {
      const sides = [...g.querySelectorAll<HTMLElement>("[data-pd]")].filter((d) => d.parentElement?.closest("[data-pg]") === g);
      const open = sides.find((d) => d.dataset["pd"] === "o"), close = sides.find((d) => d.dataset["pd"] === "c");
      const glyph = open && inkOf(open.querySelector("*") ?? open);
      if (!open || !close || !glyph) continue;
      let top = Infinity, bottom = -Infinity;
      for (const el of g.querySelectorAll<Element>("*")) {
        if (open.contains(el) || close.contains(el)) continue;
        const r = inkOf(el);
        if (r) { top = Math.min(top, r.top); bottom = Math.max(bottom, r.bottom); }
      }
      const em = parseFloat(getComputedStyle(open).fontSize) || 16;
      if (!(top < glyph.top - 0.05 * em || bottom > glyph.bottom + 0.05 * em)) continue;
      // a little past what they hold, as TeX's do, and never shorter than the plain paren
      top = Math.min(top - 0.1 * em, glyph.top); bottom = Math.max(bottom + 0.1 * em, glyph.bottom);
      const h = bottom - top;
      const kind = g.dataset["pk"];
      // bars keep their width; a paren grows a little wider as it grows taller
      const w = kind ? open.getBoundingClientRect().width : Math.min(Math.max(0.39 * em, 0.28 * em + 0.07 * h), 0.8 * em);
      for (const d of [open, close]) {
        // an inline block the paren's size, set on the line where it is drawn, so the input's
        // height takes it in (its baseline, with no line inside, is its bottom edge)
        d.classList.add("mi-tall");
        d.style.width = `${w}px`;
        d.style.height = `${h}px`;
        d.style.verticalAlign = `${glyph.baseline - bottom}px`;
        d.append(kind ? bars(kind === "norm" ? 2 : 1, w, h, em) : paren(d === open, w, h, em));
      }
      // a call's name level with the middle of its parentheses, not down on the line under a stack
      const name = g.dataset["pg"] === "c" ? g.closest("[data-call]")?.querySelector<HTMLElement>("[data-word]") : null;
      const inks = name ? [...name.querySelectorAll("*")].map(inkOf).filter((r) => !!r) : [];
      if (name && inks.length) {
        const mid = (Math.min(...inks.map((r) => r.top)) + Math.max(...inks.map((r) => r.bottom))) / 2;
        name.classList.add("mi-lift");
        name.style.top = `${(top + bottom) / 2 - mid}px`;
      }
    }
  }

  /** An atom's box on screen; a piece of a glyph that stands for several atoms (`pi` is π) gets its share. */
  private rect(a: Atom): DOMRect | null {
    const e = this.atomEl.get(a);
    if (!e) return null;
    let r = e.el.getBoundingClientRect();
    const t = this.tallOf.get(e.el);
    if (t) r = new DOMRect(r.left, r.top - t.up, r.width, r.height + t.up + t.down);
    if (e.n === 1) return r;
    const w = r.width / e.n;
    return new DOMRect(r.left + w * e.k, r.top, w, r.height);
  }

  /** Where the caret at `c` is drawn, in viewport coordinates. `rects` keeps a block's atoms' boxes
   *  across the positions of one search (`caretAt` asks for every position: measured per position,
   *  a block of n atoms was read n² times, on every move of a drag). */
  private box(c: Caret, rects?: Map<Block, (DOMRect | null)[]>): Box | null {
    const b = c.block;
    if (b.length === 0) {
      const h = this.holeEl.get(b);
      if (!h) return null;
      const r = h.getBoundingClientRect();
      return { x: r.left + r.width / 2, top: r.top, bottom: r.bottom };
    }
    let rs = rects?.get(b);
    if (rs === undefined) {
      rs = b.map((a) => this.rect(a));
      rects?.set(b, rs);
    }
    // a block of several lines (a system's declarations): the caret is as tall as its own line, and
    // a click finds the line it is on. A line break ends its line: the position before it is that
    // line's end, the one after it the next line's start
    const { from, to } = lineOf(b, c.i);
    const known = rs.slice(from, to + 1).filter((r): r is DOMRect => !!r && r.height > 0);
    if (!known.length) {
      // the empty last line, after a break: under the line before it, where its lines start
      const above = from > 0 ? this.box({ block: b, i: from - 1 }, rects) : null;
      const left = Math.min(...rs.filter((r): r is DOMRect => !!r && r.height > 0).map((r) => r.left));
      return above && Number.isFinite(left) ? { x: left, top: above.bottom, bottom: 2 * above.bottom - above.top } : null;
    }
    const top = Math.min(...known.map((r) => r.top)), bottom = Math.max(...known.map((r) => r.bottom));
    const at = rs[c.i], before = c.i > from ? rs[c.i - 1] : undefined;
    const x = at ? at.left : before ? before.right : known[known.length - 1]!.right;
    return { x, top, bottom };
  }

  /** Draw the caret, and mark the hole it is in. */
  private place() {
    // a name typed in front of a group becomes its call once the caret has left the name
    if (this.edit.settle()) { this.render(); return; }
    this.math.querySelector(".mi-here")?.classList.remove("mi-here");
    for (const el of this.math.querySelectorAll(".mi-sel")) el.classList.remove("mi-sel");
    const sel = this.edit.selection();
    if (sel) for (const a of sel.block.slice(sel.start, sel.end)) this.atomEl.get(a)?.el.classList.add("mi-sel");
    const bx = this.box(this.edit.caret);
    if (!bx) { this.caretEl.style.display = "none"; return; }
    this.caretEl.style.removeProperty("display");
    const o = this.el.getBoundingClientRect();
    this.caretEl.style.left = `${bx.x - o.left - 0.75}px`;
    this.caretEl.style.top = `${bx.top - o.top}px`;
    this.caretEl.style.height = `${Math.max(bx.bottom - bx.top, 8)}px`;
    if (this.edit.caret.block.length === 0) this.holeEl.get(this.edit.caret.block)?.classList.add("mi-here");
    this.ta.style.left = this.caretEl.style.left;   // an IME's candidate window opens at the caret
    this.ta.style.top = this.caretEl.style.top;
    if (this.el.classList.contains("focused")) this.opts.onCaret?.();
  }

  /** Every caret position, for a click at height `y` to choose among. In a block of several lines
   *  only the line nearest `y` takes part, with what is inside it: a click beyond a short line's end
   *  is that line's, not the longer line's under it. */
  private *positions(y: number, rects: Map<Block, (DOMRect | null)[]>, b: Block = this.edit.root): Generator<Caret> {
    let from = 0, to = b.length;
    if (b.some(isBreak)) {
      let best = Infinity;
      for (let i = 0; i <= b.length; i = lineOf(b, i).to + 1) {
        const bx = this.box({ block: b, i }, rects);
        const d = !bx ? Infinity : y < bx.top ? bx.top - y : y > bx.bottom ? y - bx.bottom : 0;
        if (d < best) { best = d; ({ from, to } = lineOf(b, i)); }
      }
    }
    for (let i = from; i <= to; i++) yield { block: b, i };
    for (const a of b.slice(from, to)) for (const s of slots(a)) yield* this.positions(y, rects, s);
  }

  /** The caret position nearest a point: among those whose line the point is on, the nearest across;
   *  among equals, the innermost (the smallest line). */
  caretAt(x: number, y: number): Caret | null {
    let best: { c: Caret; cost: number; h: number } | null = null;
    const rects = new Map<Block, (DOMRect | null)[]>();
    for (const c of this.positions(y, rects)) {
      const bx = this.box(c, rects);
      if (!bx) continue;
      const dy = y < bx.top ? bx.top - y : y > bx.bottom ? y - bx.bottom : 0;
      const cost = Math.abs(x - bx.x) + 4 * dy;
      const h = bx.bottom - bx.top;
      if (!best || cost < best.cost - 0.5 || (Math.abs(cost - best.cost) <= 0.5 && h < best.h)) best = { c, cost, h };
    }
    return best?.c ?? null;
  }

  // --- keys --------------------------------------------------------------------------------------

  private typed() {
    const s = this.ta.value;
    this.ta.value = "";
    if (!s) return;
    for (const c of s) this.edit.type(c);
    this.changed();
  }

  /** An edit from outside the keyboard (a keypad button): run it on the editor and redraw. */
  apply(fn: (e: MathEdit) => boolean) {
    if (fn(this.edit)) this.changed(); else this.place();
  }

  /** Mark where the engine's error is (its span into the text), or clear the mark. */
  markError(span: { start: number; end: number } | null) { this.errSpan = span; this.render(); }

  private changed() {
    this.edit.restructure();
    this.errSpan = null;
    this.render();
    this.suggest();
    this.opts.onChange?.(this.text, this.holes);
  }

  // --- the `\\` suggestions ------------------------------------------------------------------------

  /** Show what the pending `\\name` could become: the symbols (one row per symbol, under the first
   *  name that matches) and the templates. */
  private suggest() {
    const p = this.edit.pendingCommand();
    if (!p) return this.suggestFunctions();
    if (p.name === this.compDismissed || !this.el.classList.contains("focused")) { this.hideSuggestions(); return; }
    this.compDismissed = null;
    const q = p.name, ql = q.toLowerCase();
    const seen = new Set<string>();
    const items: { name: string; what: string; glyph: string; fn?: boolean }[] = [];
    for (const [name, sym] of Object.entries(this.edit.symbols)) {
      if (!name.toLowerCase().startsWith(ql) || seen.has(sym)) continue;
      seen.add(sym);
      items.push({ name, what: "symbol", glyph: sym });
    }
    for (const [name, t] of Object.entries(TEMPLATES)) if (name.toLowerCase().startsWith(ql)) items.push({ name, what: t.what, glyph: t.glyph });
    // an exact name first, then case-exact prefixes, then the rest
    const rank = (n: string) => (n === q ? 0 : n.startsWith(q) ? 1 : 2);
    items.sort((a, b) => rank(a.name) - rank(b.name));
    this.showSuggestions(items);
  }

  /** A name being typed that starts a function's: the functions, as the text input lists them; in
   *  an index of a part, the names that can go there. */
  private suggestFunctions() {
    const pb = this.edit.partBefore();
    if (pb) {
      if (!this.opts.partNames || !this.el.classList.contains("focused")) { this.hideSuggestions(); return; }
      const q = pb.typed.toLowerCase();
      const items = this.opts.partNames(pb.text)
        .filter((n) => (n.name === "All" ? !pb.quoted && "all".startsWith(q) && q.length > 0 : n.name.toLowerCase().startsWith(q)))
        .map((n) => ({ name: n.name, what: n.what, glyph: "", fn: true, index: true }));
      this.showSuggestions(items);
      return;
    }
    const p = this.edit.nameBefore();
    if (!p || !this.opts.functions || p.name === this.compDismissed || !this.el.classList.contains("focused")) { this.hideSuggestions(); return; }
    this.compDismissed = null;
    const items = this.opts.functions(p.name).filter((f) => f.name !== p.name).map((f) => ({ name: f.name, what: f.what, glyph: "", fn: true, call: f.call !== false }));
    this.showSuggestions(items);
  }

  private showSuggestions(items: { name: string; what: string; glyph: string; fn?: boolean; index?: boolean; call?: boolean }[]) {
    if (!items.length) { this.hideSuggestions(); return; }
    this.hideSuggestions();
    const box = document.createElement("div");
    box.className = "completions mi-completions";
    box.setAttribute("role", "listbox");
    this.comp = { items: items.slice(0, 9), index: 0, box };
    this.drawSuggestions();
    document.body.append(box);
    const c = this.caretEl.getBoundingClientRect();
    box.style.position = "fixed";
    box.style.left = `${Math.max(8, Math.min(c.left - 8, window.innerWidth - box.offsetWidth - 8))}px`;
    box.style.top = `${c.bottom + 6}px`;
  }

  private drawSuggestions() {
    const cp = this.comp;
    if (!cp) return;
    cp.box.innerHTML = "";
    cp.items.forEach((it, i) => {
      const row = document.createElement("div");
      row.className = `comprow${it.fn ? "" : " symrow"}${i === cp.index ? " on" : ""}`;
      row.setAttribute("role", "option");
      row.setAttribute("aria-selected", String(i === cp.index));
      const n = document.createElement("span"); n.className = "n"; n.textContent = it.index && it.name !== "All" ? `"${it.name}"` : it.fn ? it.name : `\\${it.name}`;
      const h = document.createElement("span"); h.className = "h"; h.textContent = it.what;
      row.append(n, h);
      if (!it.fn) { const g = document.createElement("span"); g.className = "sym"; g.textContent = it.glyph; row.append(g); }
      row.addEventListener("mousedown", (ev) => { ev.preventDefault(); cp.index = i; this.acceptSuggestion(); });
      cp.box.append(row);
    });
    const foot = document.createElement("div");
    foot.className = "compfoot";
    // a function or a name is taken by Enter only once picked (Enter otherwise runs the cell)
    foot.textContent = cp.items[0]?.fn ? "Tab to accept · ↑↓ then Enter · Esc to dismiss" : "Tab or Enter to accept · Esc to dismiss";
    cp.box.append(foot);
  }

  private hideSuggestions() { this.comp?.box.remove(); this.comp = null; }
  /** Let the input go: its completion popup (on the page's body, not in the input) and its observer. */
  dispose() { this.hideSuggestions(); this.resizer?.disconnect(); }

  /** Replace the pending `\\name` with the chosen one and finish it. */
  private acceptSuggestion() {
    const cp = this.comp;
    if (!cp) return;
    const item = cp.items[cp.index]!;
    if (item.index) { this.hideSuggestions(); if (this.edit.completeIndex(item.name === "All" ? "All" : `"${item.name}"`)) this.changed(); return; }
    if (item.fn) { this.hideSuggestions(); if (this.edit.completeName(item.name, item.call)) this.changed(); return; }
    const p = this.edit.pendingCommand();
    if (!p) return;
    const name = item.name;
    const { block } = this.edit.caret;
    block.splice(p.start + 1, p.name.length, ...Array.from(name, (c) => ({ k: "ch" as const, c })));
    this.edit.caret = { block, i: p.start + 1 + name.length };
    this.edit.command();
    this.changed();
  }

  private key(ev: KeyboardEvent) {
    if (this.opts.onKey?.(ev)) return;
    if (this.composing) return;
    const mod = ev.ctrlKey || ev.metaKey, k = ev.key.toLowerCase();
    if (mod && !ev.altKey && (k === "z" || k === "y" || k === "a")) {
      ev.preventDefault();
      if (k === "a") { this.edit.selectAll(); this.place(); return; }
      const redo = k === "y" || ev.shiftKey;
      if (redo ? this.edit.redo() : this.edit.undo()) this.changed();
      return;
    }
    if (mod || ev.altKey) return;
    const cp = this.comp;
    if (cp) {
      const n = cp.items.length;
      if (ev.key === "ArrowDown" || ev.key === "ArrowUp") {
        ev.preventDefault();
        cp.index = (cp.index + (ev.key === "ArrowDown" ? 1 : n - 1)) % n;
        cp.picked = true;
        this.drawSuggestions();
        return;
      }
      // a function is taken by Enter only once picked with the arrows (Enter otherwise runs the cell,
      // as in the text input); a `\\name` cannot run as typed, so Enter finishes it
      if (ev.key === "Tab" || (ev.key === "Enter" && (cp.picked || !cp.items[0]?.fn))) { ev.preventDefault(); this.acceptSuggestion(); return; }
      if (ev.key === "Enter") this.hideSuggestions();
      if (ev.key === "Escape") { ev.preventDefault(); this.compDismissed = this.edit.pendingCommand()?.name ?? this.edit.nameBefore()?.name ?? null; this.hideSuggestions(); return; }
    }
    const e = this.edit;
    let moved = true, edited = false;
    // Shift extends the selection with any move; without it, a move drops the selection (← and →
    // go to its ends)
    const isMove = /^(Arrow(Left|Right|Up|Down)|Home|End)$/.test(ev.key);
    if (isMove && ev.shiftKey) e.extend();
    else if (isMove && e.selection() && (ev.key === "ArrowLeft" || ev.key === "ArrowRight")) {
      e.collapse(ev.key === "ArrowLeft" ? -1 : 1);
      ev.preventDefault(); this.place(); return;
    } else if (isMove) e.anchor = null;
    switch (ev.key) {
      case "ArrowLeft": e.left(); break;
      case "ArrowRight": e.right(); break;
      case "ArrowUp": case "ArrowDown": {
        const dir = ev.key === "ArrowUp" ? -1 : 1;
        if (!e.vertical(dir)) { ev.preventDefault(); if (!ev.shiftKey) this.opts.onLeave?.(dir); return; }
        break;
      }
      case "Home": e.home(); break;
      case "End": e.end(); break;
      case "Escape": if (!e.selection()) return; e.anchor = null; break;
      case "Backspace": edited = e.backspace(); break;
      case "Delete": edited = e.deleteForward(); break;
      case "Tab":
        // a pending `\name` finishes; otherwise the next empty slot — and with none, Tab leaves the input
        if (e.command()) edited = true;
        else if (!e.hole(ev.shiftKey ? -1 : 1)) return;
        break;
      case "Enter":
        ev.preventDefault();
        if (e.command()) { this.changed(); return; }
        // Shift+Enter starts a new line (a system's next declaration), as in the text
        if (ev.shiftKey) { if (e.type("\n")) this.changed(); return; }
        this.opts.onEnter?.();
        return;
      default: moved = false;
    }
    if (!moved) return;
    ev.preventDefault();
    if (edited) this.changed(); else { this.place(); this.suggest(); }
  }
}
