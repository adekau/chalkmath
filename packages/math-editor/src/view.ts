import katex from "katex";
import { MathEdit, TEMPLATES, type Caret } from "./edit.js";
import type { Atom, Block, Stmt } from "./model.js";
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
  /** What an output reference (`%`, `%%`, `%3`) stands for: its number, and the output's text for
   *  a tooltip. Without it, `%n` shows its number and `%` stays as typed. */
  outRef?(ref: string): { label: number; value?: string } | null;
  /** Highlight classes for tokens (see `NotationOptions.classify`); the page styles `[data-hl=…]`. */
  classify?(text: string, as: "call" | "bound" | "name" | "num" | "keyword"): string | null;
  /** A paste, before the input reads it: the host takes it (an image, an SVG) by preventing its default. */
  onPaste?(ev: ClipboardEvent): void;
}

/** The styles the input needs; added to the page once. Colours come from the page's `--mi-*`
 *  properties where it sets them. */
export const MATH_INPUT_CSS = `
.mi { position:relative; display:inline-block; min-width:2em; min-height:1.4em; padding:2px 4px; cursor:text; outline:none; }
.mi-math .katex { font-size:1.15em; }
.mi-math [data-h] { color:var(--mi-hole, #8a8a8a); }
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
.mi-math .mi-tall > * { display:none; }
.mi-math .mi-tall > svg { display:block; position:static; width:100%; height:100%; stroke:none; }
.mi-math [data-open] { opacity:0.35; }
.mi-math [data-out] { background:var(--mi-chip, rgba(107,138,253,0.14)); border-radius:4px; padding:0 2px; }
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
  /** Whether the parens were last fitted with the input on screen. */
  private fitted = false;
  /** The `\\` suggestions under the caret: the names that start with what has been typed. */
  private comp: { items: { name: string; what: string; glyph: string }[]; index: number; box: HTMLElement } | null = null;
  /** Esc closed the suggestions for this command; they come back when it changes. */
  private compDismissed: string | null = null;

  /** An input for `src`, or null when the text is not this grammar (the cell stays raw). */
  static fromSource(src: string, opts: MathInputOptions = {}): MathInput | null {
    if (!src.trim()) return new MathInput({ body: [] }, opts);
    const r = read(src, opts.known);
    return r.ok ? new MathInput(r.stmt, opts) : null;
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
    this.ta.addEventListener("focus", () => { this.el.classList.add("focused"); this.place(); this.opts.onFocus?.(); });
    this.ta.addEventListener("blur", () => {
      this.el.classList.remove("focused");
      this.hideSuggestions();
      // leaving the input places every `)` still open, as the text had them all along
      this.edit.closeAll();
      this.render();
      this.opts.onBlur?.();
    });
    this.ta.addEventListener("keydown", (ev) => this.key(ev));
    // the parens are fitted by measuring, so again once the input is on screen and its fonts are in
    new ResizeObserver(() => { if (!this.fitted) this.refit(); }).observe(this.math);
    void document.fonts?.ready.then(() => this.refit());
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
      outRef: (ref) => this.opts.outRef?.(ref)?.label ?? null,
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
      const r = this.opts.outRef?.(outRefOf(el.dataset["out"]!));
      if (r) el.title = `Out[${r.label}]${r.value ? ` = ${r.value}` : ""}`;
    }
    const text = this.text;
    this.ta.setAttribute("aria-label", `${this.opts.label ?? "Math input"}: ${text || "empty"}`);
    this.place();
  }

  private refit() { this.fitParens(); this.place(); }

  /** Stretch each group's parentheses over what it holds, where that is taller than a paren. KaTeX's
   *  `\\left(` would centre them on the math axis instead, so a stack of fractions that goes further
   *  below the axis than above it would get parens reaching as far above it again, over nothing. */
  private fitParens() {
    for (const d of this.math.querySelectorAll<HTMLElement>(".mi-tall")) {
      d.classList.remove("mi-tall");
      for (const p of ["width", "height", "vertical-align"]) d.style.removeProperty(p);
      d.querySelector(":scope > svg")?.remove();
    }
    this.fitted = this.math.getClientRects().length > 0;
    if (!this.fitted) return;
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
      const w = Math.min(Math.max(0.39 * em, 0.28 * em + 0.07 * h), 0.8 * em);
      for (const d of [open, close]) {
        // an inline block the paren's size, set on the line where it is drawn, so the input's
        // height takes it in (its baseline, with no line inside, is its bottom edge)
        d.classList.add("mi-tall");
        d.style.width = `${w}px`;
        d.style.height = `${h}px`;
        d.style.verticalAlign = `${glyph.baseline - bottom}px`;
        d.append(paren(d === open, w, h, em));
      }
    }
  }

  /** An atom's box on screen; a piece of a glyph that stands for several atoms (`pi` is π) gets its share. */
  private rect(a: Atom): DOMRect | null {
    const e = this.atomEl.get(a);
    if (!e) return null;
    const r = e.el.getBoundingClientRect();
    if (e.n === 1) return r;
    const w = r.width / e.n;
    return new DOMRect(r.left + w * e.k, r.top, w, r.height);
  }

  /** Where the caret at `c` is drawn, in viewport coordinates. */
  private box(c: Caret): Box | null {
    const b = c.block;
    if (b.length === 0) {
      const h = this.holeEl.get(b);
      if (!h) return null;
      const r = h.getBoundingClientRect();
      return { x: r.left + r.width / 2, top: r.top, bottom: r.bottom };
    }
    const rs = b.map((a) => this.rect(a));
    const known = rs.filter((r): r is DOMRect => !!r && r.height > 0);
    if (!known.length) return null;
    const top = Math.min(...known.map((r) => r.top)), bottom = Math.max(...known.map((r) => r.bottom));
    const at = rs[c.i], before = rs[c.i - 1];
    const x = at ? at.left : before ? before.right : known[known.length - 1]!.right;
    return { x, top, bottom };
  }

  /** Draw the caret, and mark the hole it is in. */
  private place() {
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

  /** Every caret position, for a click to choose among. */
  private *positions(b: Block = this.edit.root): Generator<Caret> {
    for (let i = 0; i <= b.length; i++) yield { block: b, i };
    for (const a of b) for (const s of slots(a)) yield* this.positions(s);
  }

  /** The caret position nearest a point: among those whose line the point is on, the nearest across;
   *  among equals, the innermost (the smallest line). */
  caretAt(x: number, y: number): Caret | null {
    let best: { c: Caret; cost: number; h: number } | null = null;
    for (const c of this.positions()) {
      const bx = this.box(c);
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
    if (!p || p.name === this.compDismissed || !this.el.classList.contains("focused")) { this.hideSuggestions(); return; }
    this.compDismissed = null;
    const q = p.name, ql = q.toLowerCase();
    const seen = new Set<string>();
    const items: { name: string; what: string; glyph: string }[] = [];
    for (const [name, sym] of Object.entries(this.edit.symbols)) {
      if (!name.toLowerCase().startsWith(ql) || seen.has(sym)) continue;
      seen.add(sym);
      items.push({ name, what: "symbol", glyph: sym });
    }
    for (const [name, t] of Object.entries(TEMPLATES)) if (name.toLowerCase().startsWith(ql)) items.push({ name, what: t.what, glyph: t.glyph });
    // an exact name first, then case-exact prefixes, then the rest
    const rank = (n: string) => (n === q ? 0 : n.startsWith(q) ? 1 : 2);
    items.sort((a, b) => rank(a.name) - rank(b.name));
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
      row.className = `comprow symrow${i === cp.index ? " on" : ""}`;
      row.setAttribute("role", "option");
      row.setAttribute("aria-selected", String(i === cp.index));
      const n = document.createElement("span"); n.className = "n"; n.textContent = `\\${it.name}`;
      const h = document.createElement("span"); h.className = "h"; h.textContent = it.what;
      const g = document.createElement("span"); g.className = "sym"; g.textContent = it.glyph;
      row.append(n, h, g);
      row.addEventListener("mousedown", (ev) => { ev.preventDefault(); cp.index = i; this.acceptSuggestion(); });
      cp.box.append(row);
    });
    const foot = document.createElement("div");
    foot.className = "compfoot";
    foot.textContent = "Tab or Enter to accept · Esc to dismiss";
    cp.box.append(foot);
  }

  private hideSuggestions() { this.comp?.box.remove(); this.comp = null; }

  /** Replace the pending `\\name` with the chosen one and finish it. */
  private acceptSuggestion() {
    const cp = this.comp, p = this.edit.pendingCommand();
    if (!cp || !p) return;
    const name = cp.items[cp.index]!.name;
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
        this.drawSuggestions();
        return;
      }
      if (ev.key === "Tab" || ev.key === "Enter") { ev.preventDefault(); this.acceptSuggestion(); return; }
      if (ev.key === "Escape") { ev.preventDefault(); this.compDismissed = this.edit.pendingCommand()?.name ?? null; this.hideSuggestions(); return; }
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
        this.opts.onEnter?.();
        return;
      default: moved = false;
    }
    if (!moved) return;
    ev.preventDefault();
    if (edited) this.changed(); else { this.place(); this.suggest(); }
  }
}
