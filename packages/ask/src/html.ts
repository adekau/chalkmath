/**
 * Tables and prose out of a fetched page, without a DOM: the lookup runs where `DOMParser` may not
 * (a worker, Node's tests), and what it needs from a page is small — every table as a grid of cell
 * texts, and the running text around them. HTML is read by a tolerant tag scanner; a page a reader
 * service returned as Markdown has its pipe tables read instead.
 */

export interface Table {
  /** The table's caption, or the nearest heading above it. */
  caption: string;
  /** One name per column: the header rows' texts for that column, joined. */
  headers: string[];
  /** Data rows, each as wide as `headers` (spans are expanded into every cell they cover). */
  rows: string[][];
}

export interface PageContent {
  tables: Table[];
  /** The page's prose, one paragraph per line, tables left out. */
  text: string;
}

const VOID = new Set(["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"]);
/** Elements whose text is not the page's: scripts, styles, and the footnote markers and hidden sort
 *  keys a table cell carries next to its value (`<sup class="reference">[3]</sup>`). */
const SKIP_TAGS = new Set(["script", "style", "noscript", "template", "svg", "head", "title"]);
const BLOCK = new Set(["p", "div", "li", "ul", "ol", "dl", "dt", "dd", "section", "article", "header", "footer",
  "h1", "h2", "h3", "h4", "h5", "h6", "blockquote", "pre", "figure", "figcaption", "br", "hr", "table", "tr"]);

const ENTITIES: Record<string, string> = {
  amp: "&", lt: "<", gt: ">", quot: "\"", apos: "'", nbsp: " ", ensp: " ", emsp: " ", thinsp: " ", hairsp: " ",
  minus: "−", ndash: "–", mdash: "—", times: "×", middot: "·", hellip: "…", deg: "°", plusmn: "±", frac12: "½",
  lsquo: "‘", rsquo: "’", ldquo: "“", rdquo: "”", dagger: "†", Dagger: "‡", sect: "§", para: "¶", shy: "", zwj: "", zwnj: "",
};

export function decodeEntities(s: string): string {
  return s.replace(/&(#x[0-9a-fA-F]+|#[0-9]+|[A-Za-z][A-Za-z0-9]*);/g, (m, e: string) => {
    if (e[0] === "#") {
      const n = e[1] === "x" || e[1] === "X" ? parseInt(e.slice(2), 16) : parseInt(e.slice(1), 10);
      return Number.isFinite(n) && n > 0 && n < 0x110000 ? String.fromCodePoint(n) : m;
    }
    return ENTITIES[e] ?? m;
  });
}

/** A formula's LaTeX without the `{\displaystyle …}` wrapper Wikipedia puts around it. */
function texOf(alt: string): string {
  const t = decodeEntities(alt).trim();
  const m = /^\{\\(?:display|text)style\s*([\s\S]*)\}$/.exec(t);
  return (m ? m[1]! : t).replace(/\s+/g, " ").trim();
}

const clean = (s: string) => s.replace(/[\s\u00a0\u2000-\u200b\u202f]+/g, " ").trim();

function attr(attrs: string, name: string): string | null {
  const m = new RegExp(`(?:^|\\s)${name}\\s*=\\s*(?:"([^"]*)"|'([^']*)'|([^\\s>]+))`, "i").exec(attrs);
  return m ? (m[1] ?? m[2] ?? m[3] ?? "") : null;
}

/** Whether an element's content is left out of the text: footnote markers, hidden sort keys, edit links. */
function skipped(tag: string, attrs: string): boolean {
  if (SKIP_TAGS.has(tag)) return true;
  const cls = attr(attrs, "class") ?? "";
  if (/\b(reference|mw-ref|sortkey|mw-editsection|noprint|mw-cite-backlink)\b/.test(cls)) return true;
  const style = attr(attrs, "style") ?? "";
  if (/display\s*:\s*none/i.test(style)) return true;
  return /(?:^|\s)hidden(?:[\s=/]|$)/i.test(attrs) && tag !== "input";
}

interface CellDraft { text: string; th: boolean; rowspan: number; colspan: number }
interface TableDraft { caption: string; heading: string; rows: { cells: CellDraft[]; head: boolean }[]; inHead: boolean; captionOpen: boolean }

/** Every table in an HTML page, and its prose. Nested tables are tables of their own. */
export function readHtml(html: string): PageContent {
  const tables: Table[] = [];
  const stack: TableDraft[] = [];
  let skipDepth = 0;
  const skipStack: string[] = [];
  let cell: CellDraft | null = null;
  const cellStack: (CellDraft | null)[] = [];
  let prose = "";
  let heading = "";
  let headingOpen = false;
  let headingText = "";
  let lastFormula = "";

  const emit = (text: string) => {
    if (skipDepth) return;
    if (text.trim()) lastFormula = "";
    const t = cur()?.captionOpen ? null : cell;
    if (cur()?.captionOpen) cur()!.caption += text;
    else if (t) t.text += text;
    else if (!stack.length) prose += text;
    if (headingOpen) headingText += text;
  };
  const cur = () => stack[stack.length - 1];
  const re = /<!--[\s\S]*?-->|<(\/?)([a-zA-Z][a-zA-Z0-9-]*)((?:[^>"']|"[^"]*"|'[^']*')*)>/g;
  let last = 0;
  for (let m = re.exec(html); m; m = re.exec(html)) {
    if (m.index > last) emit(decodeEntities(html.slice(last, m.index)));
    last = re.lastIndex;
    if (!m[2]) continue;   // a comment
    const close = m[1] === "/";
    const tag = m[2].toLowerCase();
    const attrs = m[3] ?? "";
    const selfClosing = /\/\s*$/.test(attrs);
    // a formula keeps its LaTeX (MathML's alttext, or the alt of Wikipedia's fallback image) as `$…$`;
    // the MathML itself is skipped, and a fallback image repeating the formula just shown is not repeated
    if (!close && (tag === "math" || (tag === "img" && /mwe-math-fallback/.test(attr(attrs, "class") ?? "")))) {
      const latex = texOf(attr(attrs, tag === "math" ? "alttext" : "alt") ?? "");
      const hidden = skipDepth > 0;
      if (latex && latex !== lastFormula) {
        if (hidden) { skipDepth = 0; emit(` $${latex}$ `); skipDepth = skipStack.length; } else emit(` $${latex}$ `);
        lastFormula = latex;
      }
      if (tag === "math" && !hidden && !selfClosing) { skipStack.push(tag); skipDepth++; }
      continue;
    }
    if (skipDepth) {
      if (!close && !VOID.has(tag) && !selfClosing && tag === skipStack[skipStack.length - 1]) { skipStack.push(tag); skipDepth++; }
      else if (close && tag === skipStack[skipStack.length - 1]) { skipStack.pop(); skipDepth--; }
      continue;
    }
    // a script's or style's text is not markup (`a<b` in code is no tag): skip to its closing tag
    if (!close && (tag === "script" || tag === "style") && !selfClosing) {
      const end = html.toLowerCase().indexOf(`</${tag}`, re.lastIndex);
      const gt = end < 0 ? -1 : html.indexOf(">", end);
      re.lastIndex = last = gt < 0 ? html.length : gt + 1;
      continue;
    }
    if (!close && !VOID.has(tag) && !selfClosing && skipped(tag, attrs)) { skipStack.push(tag); skipDepth++; continue; }
    if (/^h[1-6]$/.test(tag)) {
      if (!close) { headingOpen = true; headingText = ""; }
      else { headingOpen = false; heading = clean(headingText); }
    }
    // a superscript or subscript is marked, so `123<sup>1</sup>` can never read as the number 1231
    if (tag === "sup") emit(close ? "}" : "^{");
    else if (tag === "sub") emit(close ? "}" : "_{");
    if (BLOCK.has(tag)) emit("\n");
    else if (tag === "td" || tag === "th") emit(" ");
    switch (tag) {
      case "table":
        if (!close) { cellStack.push(cell); cell = null; stack.push({ caption: "", heading, rows: [], inHead: false, captionOpen: false }); }
        else if (stack.length) { const t = stack.pop()!; cell = cellStack.pop() ?? null; const done = finishTable(t); if (done) tables.push(done); }
        break;
      case "caption": if (cur()) cur()!.captionOpen = !close; break;
      case "thead": if (cur()) cur()!.inHead = !close; break;
      case "tr":
        if (cur() && !close) { cur()!.rows.push({ cells: [], head: cur()!.inHead }); cell = null; }
        break;
      case "td": case "th":
        if (!cur()) break;
        if (!close) {
          const t = cur()!;
          if (!t.rows.length) t.rows.push({ cells: [], head: t.inHead });
          const span = (n: string) => { const v = parseInt(attr(attrs, n) ?? "1", 10); return Number.isFinite(v) && v > 0 ? Math.min(v, 200) : 1; };
          cell = { text: "", th: tag === "th", rowspan: span("rowspan"), colspan: span("colspan") };
          t.rows[t.rows.length - 1]!.cells.push(cell);
        } else cell = null;
        break;
    }
  }
  if (last < html.length) emit(decodeEntities(html.slice(last)));
  while (stack.length) { const done = finishTable(stack.pop()!); if (done) tables.push(done); }
  const text = prose.split("\n").map(clean).filter((l) => l.length > 0).join("\n");
  return { tables, text };
}

/** Lay a table's cells out on a grid (spans fill every position they cover) and split off its header rows. */
function finishTable(t: TableDraft): Table | null {
  const grid: { text: string; th: boolean }[][] = [];
  const headRow: boolean[] = [];
  t.rows.forEach((row, r) => {
    grid[r] ??= [];
    headRow[r] = row.head;
    let c = 0;
    for (const cellDraft of row.cells) {
      while (grid[r]![c]) c++;
      const text = clean(cellDraft.text);
      for (let dr = 0; dr < cellDraft.rowspan && r + dr < t.rows.length; dr++) {
        grid[r + dr] ??= [];
        for (let dc = 0; dc < cellDraft.colspan; dc++) grid[r + dr]![c + dc] = { text, th: cellDraft.th };
      }
      c += cellDraft.colspan;
    }
  });
  const width = Math.max(0, ...grid.map((r) => r.length));
  if (width < 1 || !grid.length) return null;
  const rows = grid.map((r) => Array.from({ length: width }, (_, i) => r[i] ?? { text: "", th: false }));
  // leading rows that are all headers (or sit in <thead>) name the columns
  let h = 0;
  while (h < rows.length - 1 && (headRow[h] || rows[h]!.every((c) => c.th || !c.text))) h++;
  const headers = Array.from({ length: width }, (_, i) => {
    const parts: string[] = [];
    for (let r = 0; r < h; r++) { const s = rows[r]![i]!.text; if (s && parts[parts.length - 1] !== s) parts.push(s); }
    return parts.join(" / ");
  });
  return { caption: clean(t.caption) || t.heading, headers, rows: rows.slice(h).map((r) => r.map((c) => c.text)).filter((r) => r.some((s) => s)) };
}

/** Pipe tables in Markdown (what reader services return), and the rest as prose. */
export function readMarkdown(md: string): PageContent {
  const lines = md.split(/\r?\n/);
  const tables: Table[] = [];
  const prose: string[] = [];
  let heading = "";
  const cells = (l: string) => l.trim().replace(/^\|/, "").replace(/\|$/, "").split("|").map((c) => clean(stripMd(c)));
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i]!;
    const hm = /^#{1,6}\s+(.*)$/.exec(l);
    if (hm) { heading = clean(stripMd(hm[1]!)); prose.push(heading); continue; }
    if (/^\s*\|/.test(l) && i + 1 < lines.length && /^\s*\|?\s*:?-{2,}:?\s*(\|\s*:?-{2,}:?\s*)*\|?\s*$/.test(lines[i + 1]!)) {
      const headers = cells(l);
      const rows: string[][] = [];
      i += 2;
      while (i < lines.length && /^\s*\|/.test(lines[i]!)) {
        const r = cells(lines[i]!);
        rows.push(Array.from({ length: headers.length }, (_, k) => r[k] ?? ""));
        i++;
      }
      i--;
      tables.push({ caption: heading, headers, rows });
      continue;
    }
    const t = clean(stripMd(l));
    if (t) prose.push(t);
  }
  return { tables, text: prose.join("\n") };
}

/** Markdown links, images and emphasis, down to their text. */
function stripMd(s: string): string {
  return s.replace(/!\[[^\]]*\]\([^)]*\)/g, "").replace(/\[([^\]]*)\]\([^)]*\)/g, "$1").replace(/(\*\*|__|\*|_|`)/g, "");
}

/** A page's content, read as HTML or Markdown by what it looks like. */
export function readPage(body: string, contentType = ""): PageContent {
  const html = /html|xml/i.test(contentType) || /^\s*<(!doctype|html|head|body|div|section|table|p\b)/i.test(body) || /<table[\s>]/i.test(body);
  return html ? readHtml(body) : readMarkdown(body);
}
