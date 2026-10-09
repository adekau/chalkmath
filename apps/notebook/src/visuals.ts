/**
 * The visuals the notebook draws (ARCHITECTURE.md §5): the engine sends a visual spec, `{kind, data}`,
 * beside a value, and this module turns each kind it knows into HTML or SVG. `VISUALS` is the one
 * registry: a kind's check (a reply's or a file's data has the shape the kind needs), its renderer, and,
 * for a visual that places the work's steps on itself, how the steps are marked. A kind not here is left
 * out; a new kind is one entry. Nothing here knows about cells: the notebook decides what to draw when.
 */
import type { KnownVisual, HasseData, TruthTableData, DigraphData, OpTableData, ContextTableData, TypingNode, TypingTreeData, SpacetimeData } from "@chalkmath/protocol";
import { h, tex } from "./dom.js";

/** The visuals this notebook draws (ARCHITECTURE.md §5), one entry per kind: how a reply's or a
 *  file's data is checked before it is a cell's, how it is drawn, and, for a visual that places the
 *  work's steps on itself, how the steps are marked. A kind the engine sends that is not here is left
 *  out; a new kind is one entry. */
export type VisualOf<K extends KnownVisual["kind"]> = Extract<KnownVisual, { kind: K }>;
export interface VisualRenderer<K extends KnownVisual["kind"]> {
  check(d: Record<string, unknown>): boolean;
  render(data: VisualOf<K>["data"]): Node[];
  /** The visual stands in for the value: the answer is the picture (a poset's Hasse diagram). */
  replacesValue?: boolean;
  /** The visual places the work's steps on itself: it shows while the answer is held, with the
   *  answer's own marks taken out (`held`), and is marked as the steps are revealed (`mark`). */
  placed?(data: VisualOf<K>["data"]): boolean;
  held?(data: VisualOf<K>["data"]): VisualOf<K>["data"];
  mark?(box: HTMLElement, data: VisualOf<K>["data"], trail: number[], cur: number | undefined, held: boolean): void;
}
export const VISUALS: { [K in KnownVisual["kind"]]: VisualRenderer<K> } = {
  "order.hasse": {
    check: (d) => Array.isArray(d["nodes"]) && Array.isArray(d["covers"]),
    render: (d) => [hasseSvg(d)], replacesValue: true,
  },
  "logic.truthtable": {
    check: (d) => Array.isArray(d["vars"]) && Array.isArray(d["rows"]) && typeof (d["formula"] as { latex?: unknown } | undefined)?.latex === "string",
    render: (d) => [truthTable(d)],
  },
  "relation.digraph": {
    check: (d) => Array.isArray(d["nodes"]) && Array.isArray(d["edges"]) && Array.isArray(d["bad"]) && Array.isArray(d["added"]),
    render: (d) => [digraphSvg(d), digraphLegend(d)],
    placed: (d) => !!d.steps,
    held: (d) => ({ ...d, bad: [], added: [] }),
    mark: (box, d, trail, cur) => markGraphSteps(box, d, trail, cur),
  },
  "algebra.optable": {
    check: (d) => Array.isArray(d["elems"]) && Array.isArray(d["rows"]) && Array.isArray(d["marks"]),
    render: (d) => [opTable(d)],
  },
  "context.table": {
    check: (d) => Array.isArray(d["objects"]) && Array.isArray(d["attributes"]) && Array.isArray(d["has"]),
    render: (d) => [contextTable(d)],
  },
  "typing.tree": {
    check: (d) => typeof (d["root"] as { latex?: unknown } | undefined)?.latex === "string",
    render: (d) => [typingTree(d)],
  },
  "replicas.spacetime": {
    check: (d) => Array.isArray(d["lanes"]) && Array.isArray(d["events"]) && Array.isArray(d["messages"]) && Array.isArray(d["steps"]),
    render: (d) => [spacetimeSvg(d)],
    placed: () => true,
    mark: (box, d, trail, cur, held) => markSpacetime(box, d, held ? trail : [], cur, held),
  },
};
/** A visual's renderer, its kind's. The data is the kind's own (`KnownVisual` pairs them). */
export const rendererOf = (v: KnownVisual) => VISUALS[v.kind] as unknown as VisualRenderer<KnownVisual["kind"]>;
export const visualPlaced = (v: KnownVisual) => !!rendererOf(v).placed?.(v.data);

/** The visuals this notebook knows how to draw, from a reply or a file: others are left out. */
export function knownVisuals(vs: unknown): KnownVisual[] {
  if (!Array.isArray(vs)) return [];
  return vs.filter((v): v is KnownVisual => {
    const d = (v as { data?: Record<string, unknown> } | null)?.data;
    if (!d) return false;
    const kind = (v as { kind?: unknown }).kind;
    const r = typeof kind === "string" && Object.hasOwn(VISUALS, kind) ? (VISUALS[kind as KnownVisual["kind"]] as VisualRenderer<KnownVisual["kind"]>) : null;
    return !!r && r.check(d);
  });
}

/** A visual, boxed and captioned as a plot is. */
export function visualBox(v: KnownVisual): HTMLElement {
  const box = h("div", "visualbox");
  box.dataset["kind"] = v.kind;
  box.append(...rendererOf(v).render(v.data));
  return box;
}

/** A Hasse diagram: elements in layers by height, covers as edges, nothing else. */
function hasseSvg(d: { nodes: { name: string; height: number }[]; covers: [string, string][] }): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const layers = new Map<number, string[]>();
  for (const n of d.nodes) layers.set(n.height, [...(layers.get(n.height) ?? []), n.name]);
  const H = Math.max(0, ...d.nodes.map((n) => n.height));
  const widest = Math.max(1, ...[...layers.values()].map((l) => l.length));
  const cw = Math.max(70, Math.min(120, 520 / widest)), w = Math.max(240, widest * cw + 40), rowH = 64, h = (H + 1) * rowH + 24;
  const pos = new Map<string, [number, number]>();
  for (const [ht, names] of layers) names.forEach((name, i) => pos.set(name, [20 + (i + 0.5) * ((w - 40) / names.length), h - 12 - (ht + 0.5) * rowH]));
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", `Hasse diagram of ${d.nodes.length} elements${d.covers.length ? `; covers: ${d.covers.map(([a, b]) => `${a} below ${b}`).join(", ")}` : ""}`);
  svg.setAttribute("viewBox", `0 0 ${w} ${h}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(h));
  for (const [a, b] of d.covers) {
    const p = pos.get(a), q = pos.get(b); if (!p || !q) continue;
    const l = document.createElementNS(NS, "line");
    l.setAttribute("x1", String(p[0])); l.setAttribute("y1", String(p[1])); l.setAttribute("x2", String(q[0])); l.setAttribute("y2", String(q[1]));
    l.setAttribute("class", "hedge"); svg.append(l);
  }
  for (const [name, [x, y]] of pos) {
    const c = document.createElementNS(NS, "circle");
    c.setAttribute("cx", String(x)); c.setAttribute("cy", String(y)); c.setAttribute("r", "5"); c.setAttribute("class", "hnode"); svg.append(c);
    const t = document.createElementNS(NS, "text");
    t.setAttribute("x", String(x + 9)); t.setAttribute("y", String(y - 7)); t.setAttribute("class", "hlabel"); t.textContent = name; svg.append(t);
  }
  return svg;
}

/** Mark where steps of the work are on a state graph: the trail of steps so far, and the current one
 *  (its arrow, or its state when it takes none). A step's arrow shows its own mark class too, so a
 *  marked transition keeps its colour under the trail. */
function markGraphSteps(box: HTMLElement, d: DigraphData, trail: number[], cur: number | undefined) {
  box.querySelectorAll(".redge.trail, .redge.cur, .rlabel.trail, .rlabel.cur, .hnode.cur").forEach((x) => x.classList.remove("trail", "cur"));
  box.querySelectorAll<SVGPathElement>(".redge").forEach((p) => {
    const cls = p.classList.contains("bad") ? "-bad" : p.classList.contains("added") ? "-added" : "";
    p.setAttribute("marker-end", `url(#rel-arrow${cls})`);
  });
  const mark = (k: number, cls: "trail" | "cur") => {
    const m = d.steps?.[k];
    if (!m) return;
    if (m.edge) {
      const want = JSON.stringify(m.edge);
      box.querySelectorAll<SVGPathElement>(".redge").forEach((p) => {
        if (p.getAttribute("data-edge") !== want) return;
        p.classList.add(cls);
        if (cls === "cur") p.setAttribute("marker-end", "url(#rel-arrow-cur)");
      });
      box.querySelectorAll(".rlabel").forEach((t) => { if (t.getAttribute("data-edge") === want) t.classList.add(cls); });
    }
    const at = m.node ?? (cls === "cur" ? m.edge?.[1] : undefined);
    if (at !== undefined) box.querySelectorAll(".hnode").forEach((c) => { if (c.getAttribute("data-node") === at) c.classList.add(cls); });
  };
  for (const k of trail) mark(k, "trail");
  if (cur !== undefined) mark(cur, "cur");
}

/** A replica simulation as a space-time diagram: a lane per replica, left to right in the order of
 *  events, a dot per event (its label above, the replica's state in its tooltip and, when short,
 *  below), an arrow per message from the event that sent it to the one that delivered it. */
function spacetimeSvg(d: SpacetimeData): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const longest = Math.max(1, ...d.lanes.map((x) => x.length));
  // a column is as wide as the longest label or state shown under a dot (a long state goes in the tooltip only)
  const shownLen = Math.max(1, ...d.events.map((e) => Math.max(e.label.length, e.state.length <= 18 ? e.state.length : 0)));
  const left = longest * 8 + 24, colW = Math.max(64, Math.min(140, shownLen * 6.4 + 16)), laneH = 62, top = 30;
  const w = left + Math.max(1, d.events.length) * colW + 24, hgt = top + d.lanes.length * laneH;
  const laneY = (l: string) => top + Math.max(0, d.lanes.indexOf(l)) * laneH + 14;
  const ex = (i: number) => left + 20 + i * colW;
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", `${d.lanes.length} replicas, ${d.events.length} events, ${d.messages.length} messages`);
  svg.setAttribute("viewBox", `0 0 ${w} ${hgt}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(hgt));
  svg.classList.add("spacetime");
  const defs = document.createElementNS(NS, "defs");
  const m = document.createElementNS(NS, "marker");
  m.setAttribute("id", "st-arrow"); m.setAttribute("viewBox", "0 0 10 10"); m.setAttribute("refX", "9"); m.setAttribute("refY", "5");
  m.setAttribute("markerWidth", "6"); m.setAttribute("markerHeight", "6"); m.setAttribute("orient", "auto-start-reverse");
  const head = document.createElementNS(NS, "path"); head.setAttribute("d", "M0,0 L10,5 L0,10 z"); head.setAttribute("class", "sthead");
  m.append(head); defs.append(m); svg.append(defs);
  for (const l of d.lanes) {
    const y = laneY(l);
    const t = document.createElementNS(NS, "text");
    t.setAttribute("x", "8"); t.setAttribute("y", String(y + 4)); t.setAttribute("class", "stlane"); t.textContent = l; svg.append(t);
    const ln = document.createElementNS(NS, "line");
    ln.setAttribute("x1", String(left)); ln.setAttribute("x2", String(w - 12)); ln.setAttribute("y1", String(y)); ln.setAttribute("y2", String(y));
    ln.setAttribute("class", "stline"); svg.append(ln);
  }
  d.messages.forEach(([a, b], k) => {
    const ea = d.events[a], eb = d.events[b]; if (!ea || !eb) return;
    const x1 = ex(a), y1 = laneY(ea.lane), x2 = ex(b), y2 = laneY(eb.lane);
    const len = Math.hypot(x2 - x1, y2 - y1) || 1;
    const p = document.createElementNS(NS, "line");
    p.setAttribute("x1", String(x1 + (x2 - x1) * 6 / len)); p.setAttribute("y1", String(y1 + (y2 - y1) * 6 / len));
    p.setAttribute("x2", String(x2 - (x2 - x1) * 7 / len)); p.setAttribute("y2", String(y2 - (y2 - y1) * 7 / len));
    p.setAttribute("class", "stmsg"); p.setAttribute("marker-end", "url(#st-arrow)");
    p.setAttribute("data-from", String(a)); p.setAttribute("data-to", String(b)); p.setAttribute("data-msg", String(k));
    svg.append(p);
  });
  d.events.forEach((e, i) => {
    const g = document.createElementNS(NS, "g");
    g.setAttribute("data-event", String(i)); g.setAttribute("class", "stev");
    const x = ex(i), y = laneY(e.lane);
    const c = document.createElementNS(NS, "circle");
    c.setAttribute("cx", String(x)); c.setAttribute("cy", String(y)); c.setAttribute("r", "5"); c.setAttribute("class", "stdot");
    const title = document.createElementNS(NS, "title"); title.textContent = `${e.lane}: ${e.label} → ${e.state}`; c.append(title);
    const lab = document.createElementNS(NS, "text");
    lab.setAttribute("x", String(x)); lab.setAttribute("y", String(y - 10)); lab.setAttribute("text-anchor", "middle"); lab.setAttribute("class", "stlabel");
    lab.textContent = e.label;
    g.append(c, lab);
    if (e.state.length <= 18) {
      const st = document.createElementNS(NS, "text");
      st.setAttribute("x", String(x)); st.setAttribute("y", String(y + 19)); st.setAttribute("text-anchor", "middle"); st.setAttribute("class", "ststate");
      st.textContent = e.state; g.append(st);
    }
    svg.append(g);
  });
  return svg;
}

/** Mark a space-time diagram's events for the steps of the work: the steps so far as a trail, the
 *  current one's events; while the answer is held back, the events of later steps are hidden. */
function markSpacetime(box: HTMLElement, d: SpacetimeData, trail: number[], cur: number | undefined, held: boolean) {
  const evs = (ks: number[]) => new Set(ks.flatMap((k) => d.steps[k] ?? []));
  // every step up to the current one has happened, a folded one (a delivery that changed nothing) too
  const upTo = cur === undefined ? -1 : cur;
  const shown = held ? evs(d.steps.map((_, k) => k).filter((k) => k <= upTo)) : evs(trail);
  const now = evs(cur === undefined ? [] : [cur]);
  box.querySelectorAll<SVGGElement>("[data-event]").forEach((g) => {
    const i = Number(g.getAttribute("data-event"));
    g.classList.toggle("trail", shown.has(i) && !now.has(i));
    g.classList.toggle("cur", now.has(i));
    g.style.display = held && !shown.has(i) ? "none" : "";
  });
  box.querySelectorAll<SVGLineElement>("[data-msg]").forEach((l) => {
    const to = Number(l.getAttribute("data-to"));
    l.classList.toggle("cur", now.has(to));
    l.style.display = held && !shown.has(to) ? "none" : "";
  });
}

/** A typing derivation as a proof tree: each judgment under a bar, its premises above, the rule to the
 *  bar's right. Var has no premises, so its bar stands alone. */
function typingTree(d: TypingTreeData): HTMLElement {
  const wrap = h("div", "typingtree");
  wrap.setAttribute("role", "img");
  wrap.setAttribute("aria-label", `Typing derivation of ${d.root.text}`);
  const node = (n: TypingNode, depth: number): HTMLElement => {
    const el = h("div", "ptnode");
    if (n.premises.length) {
      const prem = h("div", "ptprem");
      // a deep tree is cut off rather than drawn past any width
      if (depth < 12) for (const p of n.premises) prem.append(node(p, depth + 1));
      else prem.append(h("span", "ptmore", "⋮"));
      el.append(prem);
    }
    const concl = h("div", "ptconc");
    concl.title = n.text;
    concl.innerHTML = tex(n.latex);
    concl.append(h("span", "ptrule", n.rule));
    el.append(concl);
    return el;
  };
  const tree = h("div", "pttree");
  tree.append(node(d.root, 0));
  wrap.append(tree);
  if (d.legend?.length) {
    const lg = h("div", "ptlegend");
    for (const l of d.legend) { const row = h("div"); row.title = l.text; row.innerHTML = tex(l.latex); lg.append(row); }
    wrap.append(lg);
  }
  return wrap;
}

/** An operation's table: the row's element times the column's, the marked cells (a law failing) shaded. */
function opTable(d: OpTableData): HTMLElement {
  const t = h("table", "truthtable optable");
  t.setAttribute("aria-label", `Operation table on ${d.elems.length} elements${d.marks.length ? `; marked: ${d.marks.map(([a, b]) => `${a} · ${b}`).join(", ")}` : ""}`);
  const marked = new Set(d.marks.map(([a, b]) => `${a}\u0000${b}`));
  const head = h("tr");
  head.append(h("th", "optcorner", "·"));
  for (const y of d.elems) head.append(h("th", undefined, y));
  const thead = h("thead"); thead.append(head); t.append(thead);
  const body = h("tbody");
  d.rows.forEach((row, i) => {
    const x = d.elems[i] ?? "";
    const tr = h("tr");
    tr.append(h("th", "oprow", x));
    row.forEach((v, j) => tr.append(h("td", marked.has(`${x}\u0000${d.elems[j] ?? ""}`) ? "opmark" : "", v)));
    body.append(tr);
  });
  t.append(body);
  return t;
}

/** A formal context: a row per object, a column per attribute, × where the object has it. */
function contextTable(d: ContextTableData): HTMLElement {
  const t = h("table", "truthtable ctxtable");
  t.setAttribute("aria-label", `A context of ${d.objects.length} objects and ${d.attributes.length} attributes`);
  const head = h("tr");
  head.append(h("th"));
  for (const a of d.attributes) head.append(h("th", undefined, a));
  const thead = h("thead"); thead.append(head); t.append(thead);
  const body = h("tbody");
  d.objects.forEach((o, i) => {
    const tr = h("tr");
    tr.append(h("th", "oprow", o));
    (d.has[i] ?? []).forEach((b) => tr.append(h("td", undefined, b ? "×" : "")));
    body.append(tr);
  });
  t.append(body);
  return t;
}

/** A truth table: a column per variable, then the formula; T and F, the formula's false rows marked. */
function truthTable(d: TruthTableData): HTMLElement {
  const t = h("table", "truthtable");
  t.setAttribute("aria-label", `Truth table of ${d.formula.text}: ${d.rows.length} rows`);
  const head = h("tr");
  for (const v of d.vars) { const th = h("th"); th.innerHTML = tex(v); head.append(th); }
  const fth = h("th", "ttf"); fth.innerHTML = tex(d.formula.latex); head.append(fth);
  const thead = h("thead"); thead.append(head); t.append(thead);
  const body = h("tbody");
  for (const row of d.rows) {
    const tr = h("tr", row[row.length - 1] ? "" : "ttfalse");
    row.forEach((b, i) => tr.append(h("td", i === row.length - 1 ? "ttf" : "", b ? "T" : "F")));
    body.append(tr);
  }
  t.append(body);
  return t;
}

/** A relation as a directed graph: elements on a circle, a pair as an arrow (a loop for `x R x`). The
 *  arrows that show a property failing are marked, and the ones a closure added are dashed. A state
 *  graph is drawn in rows instead, each state a box with its name in it, the arrows ending at the
 *  boxes' edges (a loop on a box's right side) and labelled with the actions that take them. */
function digraphSvg(d: DigraphData): SVGSVGElement {
  const NS = "http://www.w3.org/2000/svg";
  const n = d.nodes.length;
  const longest = Math.max(1, ...d.nodes.map((x) => x.length));
  const layered = !!d.layers && d.layers.length === n;
  const labels = d.labels?.length === d.edges.length ? d.labels : undefined;
  // a state's box: half its width (the name's, at the label's 11px code font) and half its height
  const half = (name: string): [number, number] => [name.length * 3.35 + 8, 10];
  const pos = new Map<string, [number, number]>();
  let w: number, hgt: number;
  if (layered) {
    // a state graph: the initial states on top, each row one step further on
    const rows = new Map<number, string[]>();
    d.nodes.forEach((name, i) => { const l = d.layers![i]!; rows.set(l, [...(rows.get(l) ?? []), name]); });
    const widest = Math.max(1, ...[...rows.values()].map((r) => r.length));
    // a column holds a box, with room on its right for a loop and the loop's label, and labelled
    // arrows want room beside them
    const boxW = 2 * half("x".repeat(longest))[0];
    const loopW = Math.max(0, ...d.edges.map(([a, b], k) => (a === b ? 2 * (26 + (labels?.[k]?.length ?? 0) * 6) : 0)));
    const colW = Math.max(70, boxW + 28, boxW + loopW, labels ? Math.max(0, ...labels.map((x) => x.length)) * 6 + 40 : 0), rowH = labels ? 84 : 74;
    w = Math.max(240, widest * colW + 40); hgt = Math.max(0, ...rows.keys()) * rowH + 48;
    for (const [l, names] of rows) names.forEach((name, k) => pos.set(name, [20 + (k + 0.5) * ((w - 40) / names.length), 24 + l * rowH]));
  } else {
    const r = n <= 1 ? 0 : Math.max(60, Math.min(150, 26 * n)), pad = Math.max(60, longest * 6.6 + 24);
    w = 2 * r + 2 * pad; hgt = 2 * r + 90;
    d.nodes.forEach((name, i) => {
      const a = -Math.PI / 2 + (2 * Math.PI * i) / Math.max(1, n);
      pos.set(name, [w / 2 + r * Math.cos(a), hgt / 2 + r * Math.sin(a)]);
    });
  }
  const key = ([a, b]: [string, string]) => `${a}\u0000${b}`;
  const bad = new Set(d.bad.map(key)), added = new Set(d.added.map(key)), all = new Set(d.edges.map(key));
  const svg = document.createElementNS(NS, "svg");
  svg.setAttribute("role", "img");
  svg.setAttribute("aria-label", `A relation on ${n} element${n === 1 ? "" : "s"}${d.edges.length ? `; pairs: ${d.edges.map(([a, b], k) => `${a} to ${b}${labels?.[k] ? ` by ${labels[k]}` : ""}`).join("; ")}` : ", no pairs"}`);
  svg.setAttribute("viewBox", `0 0 ${w} ${hgt}`); svg.setAttribute("width", String(w)); svg.setAttribute("height", String(hgt));
  const defs = document.createElementNS(NS, "defs");
  for (const cls of ["", "bad", "added", "cur"]) {
    const m = document.createElementNS(NS, "marker");
    m.setAttribute("id", `rel-arrow${cls ? `-${cls}` : ""}`); m.setAttribute("viewBox", "0 0 10 10"); m.setAttribute("refX", "9"); m.setAttribute("refY", "5");
    // a marker scales with its arrow's stroke: the current arrow is drawn thicker, so its head is set smaller
    const mw = cls === "cur" ? "4.5" : "7";
    m.setAttribute("markerWidth", mw); m.setAttribute("markerHeight", mw); m.setAttribute("orient", "auto-start-reverse");
    const path = document.createElementNS(NS, "path"); path.setAttribute("d", "M0,0 L10,5 L0,10 z"); path.setAttribute("class", `rhead ${cls}`);
    m.append(path); defs.append(m);
  }
  svg.append(defs);
  // the labels go on top of every arrow, so one arrow does not cross out another's label
  const texts: SVGTextElement[] = [];
  d.edges.forEach((e, ei) => {
    const [a, b] = e;
    const p = pos.get(a), q = pos.get(b); if (!p || !q) return;
    const cls = bad.has(key(e)) ? "bad" : added.has(key(e)) ? "added" : "";
    const path = document.createElementNS(NS, "path");
    // where the label goes, and which way it reads from there
    let at: [number, number, "start" | "middle" | "end"];
    if (layered && a === b) {
      // a loop on the box's right side, its label past it
      const rx = p[0] + half(a)[0], y = p[1];
      path.setAttribute("d", `M${rx},${y - 5} C${rx + 26},${y - 20} ${rx + 26},${y + 20} ${rx + 2},${y + 5}`);
      at = [rx + 24, y + 4, "start"];
    } else if (layered) {
      // from box edge to box edge; bend a pair drawn both ways apart, and edges within a row or back up it
      const dx = q[0] - p[0], dy = q[1] - p[1], len = Math.hypot(dx, dy) || 1, ux = dx / len, uy = dy / len;
      const bend = all.has(key([b, a])) ? 14 : q[1] <= p[1] ? 26 : 0;
      const mx = (p[0] + q[0]) / 2 - uy * bend, my = (p[1] + q[1]) / 2 + ux * bend;
      // where the line from a box's centre toward the curve's control point leaves the box
      const edge = (c: [number, number], name: string, gap: number): [number, number] => {
        const [hw, hh] = half(name), ex = mx - c[0], ey = my - c[1], el = Math.hypot(ex, ey) || 1;
        const t = Math.min(ex ? hw / Math.abs(ex / el) : Infinity, ey ? hh / Math.abs(ey / el) : Infinity) + gap;
        return [c[0] + (ex / el) * t, c[1] + (ey / el) * t];
      };
      const [x1, y1] = edge(p, a, 1), [x2, y2] = edge(q, b, 2);
      path.setAttribute("d", `M${x1},${y1} Q${mx},${my} ${x2},${y2}`);
      // the curve's midpoint; a bent arrow's label is outside its bend, clear of the arrow beside it
      const nx = -uy * Math.sign(bend), ny = ux * Math.sign(bend), cx = (x1 + 2 * mx + x2) / 4 + 5 * nx, cy = (y1 + 2 * my + y2) / 4 + 5 * ny;
      at = [cx, cy + (ny > 0.3 ? 10 : ny < -0.3 ? -2 : 4), nx > 0.3 ? "start" : nx < -0.3 ? "end" : "middle"];
    } else if (a === b) {
      // a loop, outward from the centre
      const ang = Math.atan2(p[1] - hgt / 2, p[0] - w / 2) || -Math.PI / 2;
      const cx = p[0] + 18 * Math.cos(ang), cy = p[1] + 18 * Math.sin(ang);
      const s1 = [p[0] + 7 * Math.cos(ang - 0.6), p[1] + 7 * Math.sin(ang - 0.6)], s2 = [p[0] + 7 * Math.cos(ang + 0.6), p[1] + 7 * Math.sin(ang + 0.6)];
      path.setAttribute("d", `M${s1[0]},${s1[1]} Q${cx + 14 * Math.cos(ang - 1.2)},${cy + 14 * Math.sin(ang - 1.2)} ${cx},${cy} Q${cx + 14 * Math.cos(ang + 1.2)},${cy + 14 * Math.sin(ang + 1.2)} ${s2[0]},${s2[1]}`);
      // past the loop's far end
      const c = Math.cos(ang);
      at = [p[0] + 30 * c, p[1] + 30 * Math.sin(ang) + 4, c < -0.3 ? "end" : c > 0.3 ? "start" : "middle"];
    } else {
      // stop short of the nodes; bend when the reverse pair is drawn too, so the two do not overlap
      const dx = q[0] - p[0], dy = q[1] - p[1], len = Math.hypot(dx, dy) || 1, ux = dx / len, uy = dy / len;
      const x1 = p[0] + ux * 8, y1 = p[1] + uy * 8, x2 = q[0] - ux * 9, y2 = q[1] - uy * 9;
      const bend = all.has(key([b, a])) ? 14 : 0;
      const mx = (x1 + x2) / 2 - uy * bend, my = (y1 + y2) / 2 + ux * bend;
      path.setAttribute("d", `M${x1},${y1} Q${mx},${my} ${x2},${y2}`);
      at = [(x1 + 2 * mx + x2) / 4, (y1 + 2 * my + y2) / 4 + 4, "middle"];
    }
    path.setAttribute("class", `redge ${cls}`);
    path.setAttribute("marker-end", `url(#rel-arrow${cls ? `-${cls}` : ""})`);
    path.setAttribute("data-edge", JSON.stringify(e));
    svg.append(path);
    const label = labels?.[ei];
    if (label) {
      const t = document.createElementNS(NS, "text");
      t.setAttribute("x", String(at[0])); t.setAttribute("y", String(at[1])); t.setAttribute("text-anchor", at[2]);
      t.setAttribute("class", `rlabel ${cls}`); t.setAttribute("data-edge", JSON.stringify(e)); t.textContent = label;
      texts.push(t);
    }
  });
  svg.append(...texts);
  for (const [name, [x, y]] of pos) {
    const t = document.createElementNS(NS, "text");
    if (layered) {
      // a box with the name in it
      const [hw, hh] = half(name), r = document.createElementNS(NS, "rect");
      r.setAttribute("x", String(x - hw)); r.setAttribute("y", String(y - hh)); r.setAttribute("width", String(2 * hw)); r.setAttribute("height", String(2 * hh));
      r.setAttribute("rx", "5"); r.setAttribute("class", "hnode"); r.setAttribute("data-node", name); svg.append(r);
      t.setAttribute("x", String(x)); t.setAttribute("y", String(y + 4)); t.setAttribute("text-anchor", "middle");
    } else {
      const c = document.createElementNS(NS, "circle");
      c.setAttribute("cx", String(x)); c.setAttribute("cy", String(y)); c.setAttribute("r", "5"); c.setAttribute("class", "hnode"); c.setAttribute("data-node", name); svg.append(c);
      // outward from the centre, past the node's loop when it has one
      const out = Math.atan2(y - hgt / 2, x - w / 2) || -Math.PI / 2, dist = d.edges.some(([a, b]) => a === name && b === name) ? 40 : 14;
      t.setAttribute("x", String(x + dist * Math.cos(out) - (Math.cos(out) < -0.3 ? name.length * 6.6 : 4))); t.setAttribute("y", String(y + dist * Math.sin(out) + 4));
    }
    t.setAttribute("class", "hlabel"); t.textContent = name; svg.append(t);
  }
  return svg;
}

/** What the marked arrows mean, when there are any. */
function digraphLegend(d: DigraphData): HTMLElement {
  const cap = h("div", "plotcap");
  const pairs = (ps: [string, string][]) => ps.map(([a, b]) => `${a}→${b}`).join(", ");
  if (d.bad.length) cap.append(h("span", "legend relbad", `marked: ${pairs(d.bad)}`), " ");
  if (d.added.length) cap.append(h("span", "legend reladded", `added: ${pairs(d.added)}`));
  return cap;
}
