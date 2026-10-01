/**
 * The data table: an output display for many rows. A CSV file and a large matrix are the same
 * thing to read (rows and columns, too many to typeset at once), so they share it: a scrolling
 * box with the column names (or numbers) and the row numbers held in view, rows added as the reader
 * scrolls to them.
 */

export interface GridSource {
  rows: number;
  cols: number;
  /** Column labels; absent, the columns are numbered from 1. */
  header?: readonly string[] | null;
  /** A cell's content: text, or HTML when `html` is set (typeset entries). */
  cell(r: number, c: number): string;
  html?: boolean;
  /** Columns of numbers, aligned right. */
  numeric?: readonly boolean[];
  /** What the table is, for a screen reader. */
  label: string;
}

const CHUNK = 100;

/** A data table. `onRows` sees each batch of rows as it is added (to wire typeset entries). */
export function dataGrid(src: GridSource, onRows?: (rows: HTMLElement[]) => void): HTMLElement {
  const box = document.createElement("div");
  box.className = "dgrid";
  box.tabIndex = 0;   // scrollable by keyboard
  box.setAttribute("role", "region");
  box.setAttribute("aria-label", src.label);
  const table = document.createElement("table");
  const head = document.createElement("tr");
  const corner = document.createElement("th"); corner.className = "dg-no"; head.append(corner);
  for (let c = 0; c < src.cols; c++) {
    const th = document.createElement("th");
    th.textContent = src.header?.[c] ?? String(c + 1);
    th.title = th.textContent;
    th.scope = "col";
    if (src.numeric?.[c]) th.className = "dg-num";
    head.append(th);
  }
  const thead = document.createElement("thead"); thead.append(head);
  const tbody = document.createElement("tbody");
  table.append(thead, tbody);
  box.append(table);

  const more = document.createElement("div");
  more.className = "dg-more";
  let shown = 0;
  const add = () => {
    const to = Math.min(src.rows, shown + CHUNK);
    const batch: HTMLElement[] = [];
    for (let r = shown; r < to; r++) {
      const tr = document.createElement("tr");
      const no = document.createElement("th"); no.className = "dg-no"; no.scope = "row"; no.textContent = String(r + 1);
      tr.append(no);
      for (let c = 0; c < src.cols; c++) {
        const td = document.createElement("td");
        const v = src.cell(r, c);
        if (src.html) td.innerHTML = v;
        else { td.textContent = v; if (v.length > 24) td.title = v; }
        if (src.numeric?.[c]) td.className = "dg-num";
        tr.append(td);
      }
      tbody.append(tr); batch.push(tr);
    }
    shown = to;
    onRows?.(batch);
    if (shown < src.rows) {
      more.textContent = `${shown.toLocaleString()} of ${src.rows.toLocaleString()} rows: scroll for more`;
      box.append(more);
    } else more.remove();
  };
  add();
  if (shown < src.rows) {
    // the next rows come in as the last ones shown scroll into view
    const io = new IntersectionObserver((es) => { if (es.some((e) => e.isIntersecting)) { add(); if (shown >= src.rows) io.disconnect(); } }, { root: box, rootMargin: "200px" });
    io.observe(more);
  }
  return box;
}

/** The entries of a LaTeX output that is one matrix and nothing else, row by row, each still with
 *  its path annotations; null for anything else (a sum of matrices, a matrix inside a term). */
export function matrixEntries(latex: string): string[][] | null {
  let s = latex.trim();
  // the whole output may be wrapped as one selectable term: \htmlData{path=root}{…}
  for (;;) {
    const m = /^\\htmlData\{[^{}]*\}\{/.exec(s);
    if (!m || closeOf(s, m[0].length - 1) !== s.length - 1) break;
    s = s.slice(m[0].length, -1).trim();
  }
  const BEGIN = "\\begin{bmatrix}", END = "\\end{bmatrix}";
  if (!s.startsWith(BEGIN) || !s.endsWith(END)) return null;
  const body = s.slice(BEGIN.length, s.length - END.length);
  const rows: string[][] = [[]];
  let depth = 0, env = 0, from = 0;
  for (let i = 0; i < body.length; i++) {
    const c = body[i]!;
    if (c === "\\") {
      if (body.startsWith("\\begin{", i)) env++;
      else if (body.startsWith("\\end{", i)) { if (--env < 0) return null; }
      else if (body[i + 1] === "\\" && depth === 0 && env === 0) { rows[rows.length - 1]!.push(body.slice(from, i).trim()); rows.push([]); from = i + 2; }
      i++;
      continue;
    }
    if (c === "{") depth++;
    else if (c === "}") depth--;
    else if (c === "&" && depth === 0 && env === 0) { rows[rows.length - 1]!.push(body.slice(from, i).trim()); from = i + 1; }
  }
  if (depth !== 0 || env !== 0) return null;
  rows[rows.length - 1]!.push(body.slice(from).trim());
  const cols = rows[0]!.length;
  return rows.every((r) => r.length === cols) ? rows : null;
}

/** The index of the brace closing the one at `open`. */
function closeOf(s: string, open: number): number {
  let depth = 0;
  for (let i = open; i < s.length; i++) {
    if (s[i] === "\\") { i++; continue; }
    if (s[i] === "{") depth++;
    else if (s[i] === "}" && --depth === 0) return i;
  }
  return -1;
}
