import katex from "katex";
import { MathEdit, type Caret } from "./edit.js";
import type { Atom, Block, Stmt } from "./model.js";
import { slots, toLatex } from "./notation.js";
import { read } from "./read.js";
import { write } from "./write.js";

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
  /** Functions the session defined. */
  known?: readonly string[];
  /** The `\` symbols (the notebook passes its own table). */
  symbols?: Record<string, string>;
  /** The accessible name, e.g. "Cell 3, math input". */
  label?: string;
  /** After every edit: the source text, and how many slots are still empty. */
  onChange?(text: string, holes: number): void;
  /** Enter. */
  onEnter?(): void;
  /** ↑ or ↓ with nowhere to go inside the input. */
  onLeave?(dir: -1 | 1): void;
  /** A key, before the input handles it; return true to take it (a completion menu's arrows). */
  onKey?(ev: KeyboardEvent): boolean;
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

  /** An input for `src`, or null when the text is not this grammar (the cell stays raw). */
  static fromSource(src: string, opts: MathInputOptions = {}): MathInput | null {
    if (!src.trim()) return new MathInput({ body: [] }, opts);
    const r = read(src, opts.known);
    return r.ok ? new MathInput(r.stmt, opts) : null;
  }

  constructor(stmt: Stmt, private opts: MathInputOptions = {}) {
    addStyles(document);
    this.edit = new MathEdit(stmt, { ...(opts.known ? { known: opts.known } : {}), ...(opts.symbols ? { symbols: opts.symbols } : {}) });
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
    this.ta.addEventListener("focus", () => { this.el.classList.add("focused"); this.place(); });
    this.ta.addEventListener("blur", () => this.el.classList.remove("focused"));
    this.ta.addEventListener("keydown", (ev) => this.key(ev));
    this.ta.addEventListener("compositionstart", () => { this.composing = true; });
    this.ta.addEventListener("compositionend", () => { this.composing = false; this.typed(); });
    this.ta.addEventListener("input", () => { if (!this.composing) this.typed(); });
    this.ta.addEventListener("copy", (ev) => { ev.clipboardData?.setData("text/plain", this.text); ev.preventDefault(); });
    this.ta.addEventListener("paste", (ev) => {
      const t = ev.clipboardData?.getData("text/plain");
      if (t === undefined) return;
      ev.preventDefault();
      for (const c of t) this.edit.type(c);
      this.changed();
    });
    this.el.addEventListener("mousedown", (ev) => {
      ev.preventDefault();
      const c = this.caretAt(ev.clientX, ev.clientY);
      if (c) this.edit.caret = c;
      this.focus();
      this.place();
    });
    this.render();
  }

  get text(): string { return write(this.edit.stmt).text; }
  focus() { this.ta.focus({ preventScroll: true }); }

  // --- drawing -----------------------------------------------------------------------------------

  render() {
    const tagged: Atom[][] = [];
    const holes: Block[] = [];
    const latex = toLatex(this.edit.stmt, {
      wrap: (atoms, s) => { tagged.push(atoms); return `\\htmlData{a=${tagged.length - 1}}{${s}}`; },
      hole: (b) => { holes.push(b); return `\\htmlData{h=${holes.length - 1}}{\\square}`; },
    });
    // display-size fractions and operators, as a textbook (and Symbolab) set an input, but left-aligned
    katex.render(`\\displaystyle ${latex}`, this.math, { throwOnError: false, trust: TRUST, strict: false, displayMode: false });
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
    const text = this.text;
    this.ta.setAttribute("aria-label", `${this.opts.label ?? "Math input"}: ${text || "empty"}`);
    this.place();
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

  private changed() {
    this.render();
    this.opts.onChange?.(this.text, write(this.edit.stmt).holes);
  }

  private key(ev: KeyboardEvent) {
    if (this.opts.onKey?.(ev)) return;
    if (ev.ctrlKey || ev.metaKey || ev.altKey || this.composing) return;
    const e = this.edit;
    let moved = true, edited = false;
    switch (ev.key) {
      case "ArrowLeft": e.left(); break;
      case "ArrowRight": e.right(); break;
      case "ArrowUp": case "ArrowDown": {
        const dir = ev.key === "ArrowUp" ? -1 : 1;
        if (!e.vertical(dir)) { ev.preventDefault(); this.opts.onLeave?.(dir); return; }
        break;
      }
      case "Home": e.home(); break;
      case "End": e.end(); break;
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
    if (edited) this.changed(); else this.place();
  }
}
