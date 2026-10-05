// Scenes: a storyboard played in the notebook's flow, a picture in the plane told in beats, the way an
// animated explainer is (Manim's scenes, 3Blue1Brown's videos), but as a cell of a book: it plays when
// it scrolls into view, it can be stepped beat by beat and scrubbed, and its text is the notebook's.
//
// A scene cell's source is a short script. Lines declare the scene's clock and its objects, and lines
// starting with `>` are its beats, in order:
//
//   clock t from 0 to 2pi                     the variable the scene animates, and its range
//   view -1.5, 1.5, -1.2, 1.2                 optional window (x0, x1, y0, y1); otherwise it fits
//   let M = (1 - t)*[1, 0; 0, 1] + t*A        a name for an expression, written in for it below
//   C = curve(exp(i*s), s, 0, 2pi) faint      a curve traced by its own parameter
//   P = point(exp(i*t))                       a point that moves with the clock
//   R = arrow(0, P)                           arrows and segments join points or expressions
//   W = trace(P)                              the path P has drawn since W was shown
//   L = label(P, "e^{it}")                    TeX beside a point
//   E = eq(exp(i*pi))                         an expression above the picture; `work` steps it
//   V = point(A*[1; 1])                       a point given as a vector, [x, y] or [x; y]
//   G = grid((1-t)*[1,0;0,1] + t*A)           the plane's grid as a matrix moves it
//   S = poly(0, [1, 0], [1, 1], [0, 1])       a filled polygon through points
//   K = line(0, V)                            the whole line through two points
//   D = value(det(A), "\det A = ")            a number that moves with the clock, above the picture
//   > show C, P, R | The unit circle, and a point on it.
//   > show W; play t to 2pi in 4s | Walk once round.
//   > work E | Euler's formula at $t = \pi$.
//
// Object styles follow the closing parenthesis: `faint`, `dashed`, `thick`, `color 1`…`color 6`. A
// beat is actions separated by `;` (`show`, `hide`, `play`, `wait`, `work`) and, after `|`, a caption
// in Markdown. Objects no beat shows or hides are there from the start. Wherever a point is wanted
// (an arrow's ends, a label's place, a polygon's corners) a point object or an expression will do,
// and the expression may be a complex number or a vector of two entries: the plane is ℂ, and a vector
// `v` is the point `v[[1]] + i*v[[2]]`, which is how the engine is asked for it. Which expressions
// are vectors is the engine's to say, asked with the script's numbers before anything is sampled.
//
// The page owns no mathematics here either: every expression is the engine's, every coordinate one of
// its samples (`engine.plot` over the clock for a point, `engine.manipulate` for a curve that moves
// with it, `engine.check` for numbers and an equation's steps, all `quiet`, so a scene is never an
// evaluation). What this module adds is what a storyboard needs: which objects show when, the clock's
// value over time, interpolation between the engine's samples, and the window. It is plain code, apart
// from the page, so it can be tested in Node.

export type Kind = "point" | "curve" | "graph" | "arrow" | "segment" | "line" | "poly" | "grid" | "trace" | "label" | "eq" | "value";
export interface Style { faint: boolean; dashed: boolean; thick: boolean; color: number | null }
export interface SceneObj { name: string; kind: Kind; args: string[]; style: Style; line: number }
export type Action =
  | { kind: "show" | "hide"; names: string[] }
  | { kind: "play"; from: string | null; to: string; dur: number }
  | { kind: "wait"; dur: number }
  | { kind: "work"; name: string; dur: number | null };
export interface Beat { actions: Action[]; caption: string; line: number }
export interface SceneSpec {
  clock: { name: string; from: string; to: string };
  /** The script's own names, each with the expression (its earlier names written in) it stands for. */
  lets: Record<string, string>;
  view: string[] | null;
  axes: boolean;
  objects: SceneObj[];
  beats: Beat[];
}
/** A mistake in a scene's script, or an engine error on one of its expressions, at a line (from 1). */
export class SceneError extends Error {
  constructor(message: string, readonly line: number) { super(message); }
}

/** How many arguments each object takes; a polygon takes three corners or more. */
const ARITY: Record<Kind, number> = { point: 1, curve: 4, graph: 4, arrow: 2, segment: 2, line: 2, poly: 3, grid: 1, trace: 1, label: 2, eq: 1, value: 2 };
const KINDS = Object.keys(ARITY) as Kind[];
const NAME = /^[A-Za-z_][A-Za-z0-9_]*$/;
/** How long a show or hide fades, and a play or work takes when its beat does not say. */
export const FADE = 0.6, PLAY = 3, STEP = 1.1;

/** Split at top-level commas: not inside parentheses, brackets or quotes. */
export function splitArgs(s: string): string[] {
  const out: string[] = [];
  let depth = 0, quoted = false, cur = "";
  for (const c of s) {
    if (c === '"') quoted = !quoted;
    if (!quoted && (c === "(" || c === "[" || c === "{")) depth++;
    if (!quoted && (c === ")" || c === "]" || c === "}")) depth--;
    if (c === "," && depth === 0 && !quoted) { out.push(cur.trim()); cur = ""; } else cur += c;
  }
  if (cur.trim() || out.length) out.push(cur.trim());
  return out;
}

/** The index of the parenthesis that closes the one at `open`, or -1. */
function closing(s: string, open: number): number {
  let depth = 0, quoted = false;
  for (let i = open; i < s.length; i++) {
    const c = s[i];
    if (c === '"') quoted = !quoted;
    if (quoted) continue;
    if (c === "(") depth++;
    if (c === ")" && --depth === 0) return i;
  }
  return -1;
}

const seconds = (s: string | undefined, line: number): number | null => {
  if (s === undefined) return null;
  const m = /^([0-9]*\.?[0-9]+)\s*s$/.exec(s.trim());
  if (!m) throw new SceneError(`a duration is seconds, like 2s, not "${s.trim()}"`, line);
  return Number(m[1]);
};

function parseStyle(words: string, line: number): Style {
  const style: Style = { faint: false, dashed: false, thick: false, color: null };
  const ws = words.trim() ? words.trim().split(/\s+/) : [];
  for (let k = 0; k < ws.length; k++) {
    const w = ws[k]!;
    if (w === "faint" || w === "dashed" || w === "thick") style[w] = true;
    else if (w === "color" && /^[1-6]$/.test(ws[k + 1] ?? "")) style.color = Number(ws[++k]) - 1;
    else throw new SceneError(`unknown style "${w}": faint, dashed, thick, or color 1 to 6`, line);
  }
  return style;
}

function parseAction(a: string, line: number, clock: string): Action {
  let m: RegExpExecArray | null;
  if ((m = /^(show|hide)\s+(.+)$/.exec(a))) {
    const names = m[2]!.split(/[\s,]+/).filter(Boolean);
    return { kind: m[1] as "show" | "hide", names };
  }
  if ((m = /^play\s+([A-Za-z_]\w*)\s+(?:from\s+(.+?)\s+)?to\s+(.+?)(?:\s+in\s+(\S+))?$/.exec(a))) {
    if (m[1] !== clock) throw new SceneError(`the scene's clock is ${clock}, not ${m[1]}`, line);
    return { kind: "play", from: m[2] ?? null, to: m[3]!, dur: seconds(m[4], line) ?? PLAY };
  }
  if ((m = /^wait\s+(\S+)$/.exec(a))) return { kind: "wait", dur: seconds(m[1], line)! };
  if ((m = /^work\s+([A-Za-z_]\w*)(?:\s+in\s+(\S+))?$/.exec(a))) return { kind: "work", name: m[1]!, dur: seconds(m[2], line) };
  throw new SceneError(`a beat's actions are show, hide, play, wait and work; not "${a}"`, line);
}

/** Read a scene's script. */
export function parseScene(src: string): SceneSpec {
  const spec: SceneSpec = { clock: { name: "t", from: "0", to: "1" }, lets: {}, view: null, axes: true, objects: [], beats: [] };
  const lines = src.split("\n");
  // the clock first, wherever it is written: a beat's `play` names it
  lines.forEach((raw, i) => {
    const m = /^\s*clock\s+([A-Za-z_]\w*)\s+from\s+(.+?)\s+to\s+(.+?)\s*$/.exec(raw);
    if (m) spec.clock = { name: m[1]!, from: m[2]!, to: m[3]! };
    else if (/^\s*clock\b/.test(raw)) throw new SceneError("write the clock as: clock t from 0 to 2pi", i + 1);
  });
  // then the names, each written in for where it is used: the engine sees whole expressions
  const letLines: Record<string, number> = {};
  lines.forEach((raw, i) => {
    if (!/^\s*let\b/.test(raw)) return;
    const m = /^\s*let\s+([A-Za-z_]\w*)\s*=\s*(.+?)\s*$/.exec(raw);
    if (!m) throw new SceneError("write a name as: let M = [1, 2; 3, 4]", i + 1);
    if (m[1] === spec.clock.name) throw new SceneError(`${m[1]} is the scene's clock`, i + 1);
    if (m[1]! in spec.lets) throw new SceneError(`${m[1]} is already a name`, i + 1);
    spec.lets[m[1]!] = withLets(spec, m[2]!);
    letLines[m[1]!] = i + 1;
  });
  lines.forEach((raw, i) => {
    const line = i + 1, s = raw.trim();
    if (!s || s.startsWith("#") || s.startsWith("clock") || /^let\b/.test(s)) return;
    if (s.startsWith(">")) {
      const body = s.slice(1);
      const bar = body.indexOf("|");
      const acts = (bar < 0 ? body : body.slice(0, bar)).split(";").map((a) => a.trim()).filter(Boolean);
      spec.beats.push({ actions: acts.map((a) => parseAction(a, line, spec.clock.name)), caption: bar < 0 ? "" : body.slice(bar + 1).trim(), line });
      return;
    }
    if (s === "axes" || s === "noaxes") { spec.axes = s === "axes"; return; }
    if (s.startsWith("view")) {
      const v = splitArgs(s.slice(4));
      if (v.length !== 4 || v.some((x) => !x)) throw new SceneError("write the window as: view x0, x1, y0, y1", line);
      spec.view = v;
      return;
    }
    const m = /^([A-Za-z_]\w*)\s*=\s*([a-z]+)\s*\(/.exec(s);
    if (!m) throw new SceneError(`expected an object (P = point(…)), a beat (> …), clock or view, not "${s}"`, line);
    const name = m[1]!, kind = m[2] as Kind;
    if (!KINDS.includes(kind)) throw new SceneError(`unknown object "${kind}": ${KINDS.join(", ")}`, line);
    if (name === spec.clock.name) throw new SceneError(`${name} is the scene's clock`, line);
    if (spec.objects.some((o) => o.name === name)) throw new SceneError(`${name} is already an object`, line);
    if (name in spec.lets) throw new SceneError(`${name} is already a name (line ${letLines[name]})`, line);
    const open = m[0].length - 1, close = closing(s, open);
    if (close < 0) throw new SceneError("a parenthesis is not closed", line);
    const args = splitArgs(s.slice(open + 1, close)).map((a) => a.startsWith('"') ? a : withLets(spec, a));
    if (kind === "poly" ? args.length < 3 || args.some((a) => !a) : args.length !== ARITY[kind] || args.some((a) => !a))
      throw new SceneError(kind === "poly" ? "poly takes three corners or more" : `${kind} takes ${ARITY[kind]} argument${ARITY[kind] > 1 ? "s" : ""}`, line);
    spec.objects.push({ name, kind, args, style: parseStyle(s.slice(close + 1), line), line });
  });
  // every name a beat or an object refers to is an object of the right kind
  const byName = new Map(spec.objects.map((o) => [o.name, o]));
  for (const o of spec.objects) {
    if (o.kind === "trace" && byName.get(o.args[0]!)?.kind !== "point") throw new SceneError(`trace follows a point, and ${o.args[0]} is not one`, o.line);
    if ((o.kind === "label" || o.kind === "value") && !/^".*"$/.test(o.args[1]!))
      throw new SceneError(`${o.kind === "label" ? "a label's" : "a value's"} text is TeX in quotes: ${o.kind}(${o.args[0]}, "z")`, o.line);
  }
  for (const b of spec.beats) for (const a of b.actions) {
    const names = a.kind === "show" || a.kind === "hide" ? a.names : a.kind === "work" ? [a.name] : [];
    for (const n of names) if (!byName.has(n)) throw new SceneError(`there is no object ${n}`, b.line);
    if (a.kind === "work" && byName.get(a.name)!.kind !== "eq") throw new SceneError(`work steps an equation (eq), and ${a.name} is not one`, b.line);
  }
  return spec;
}

/** Whether `e` is one bracketed literal, `[x, y]`, and not, say, `[x, y][[1]]`. */
function isVectorLiteral(e: string): boolean {
  if (!e.startsWith("[")) return false;
  let depth = 0;
  for (let i = 0; i < e.length; i++) {
    if (e[i] === "[") depth++;
    if (e[i] === "]" && --depth === 0) return i === e.length - 1;
  }
  return false;
}
/** A vector as a point of the plane, the complex number its two entries make. */
export const vectorPoint = (v: string) => `(${v})[[1]] + i*(${v})[[2]]`;
/** The image of the `j`th basis vector under a 2×2 matrix: its `j`th column, as a point. */
export const columnPoint = (m: string, j: 1 | 2) => `(${m})[[1, ${j}]] + i*(${m})[[2, ${j}]]`;
/** The expression an object is anchored at, as written: a point object's, or an expression of its own. */
const written = (spec: SceneSpec, arg: string) => spec.objects.find((o) => o.name === arg && o.kind === "point")?.args[0] ?? arg;
/** An expression with the script's names written in, each as the parenthesized expression it stands for. */
function withLets(spec: SceneSpec, e: string): string {
  let out = e;
  for (const [name, val] of Object.entries(spec.lets)) out = out.replace(new RegExp(`(?<![A-Za-z0-9_])${name}(?![A-Za-z0-9_])`, "g"), () => `(${val})`);
  return out;
}

/** Where an object is anchored, as the expression the engine samples: a complex number as written,
 *  a vector (a literal, or one of `vectors`, those the engine said are) as the point it makes. */
export function anchorOf(spec: SceneSpec, arg: string, vectors: readonly string[] = []): string {
  const e = written(spec, arg);
  return isVectorLiteral(e) || vectors.includes(e) ? vectorPoint(e) : e;
}
/** The anchors an object is drawn from, as written. */
function anchorsOf(o: SceneObj): string[] {
  switch (o.kind) {
    case "point": return [o.name];
    case "arrow": case "segment": case "line": case "poly": return o.args;
    case "label": case "trace": return [o.args[0]!];
    default: return [];
  }
}
/** The point expressions an object is drawn from, each sampled over the clock. */
function pointsOf(spec: SceneSpec, o: SceneObj, vectors: readonly string[]): string[] {
  if (o.kind === "grid") return [columnPoint(o.args[0]!, 1), columnPoint(o.args[0]!, 2)];
  return anchorsOf(o).map((a) => anchorOf(spec, a, vectors));
}

/** One question for the engine. `key` names it in the replies. */
export interface Request { key: string; method: "engine.plot" | "engine.manipulate" | "engine.check"; source: string; showWork?: boolean }
/** Frames a moving curve is sampled at, over the clock. */
export const FRAMES = 61;

/** What is asked first: the numbers a script names (the clock's range, where a play goes, the
 *  window), since the frames of a moving curve are taken at their values; and what each point's
 *  expression is, since a vector is sampled as the point it makes. */
export function numberRequests(spec: SceneSpec): Request[] {
  const out = new Map<string, Request>();
  const num = (e: string) => out.set(`num:${e}`, { key: `num:${e}`, method: "engine.check", source: `N(${e})` });
  num(spec.clock.from); num(spec.clock.to);
  for (const v of spec.view ?? []) num(v);
  for (const b of spec.beats) for (const a of b.actions) if (a.kind === "play") { num(a.to); if (a.from) num(a.from); }
  for (const o of spec.objects) for (const a of anchorsOf(o)) {
    const e = written(spec, a);
    if (!isVectorLiteral(e) && !/^-?[0-9.]+$/.test(e)) out.set(`is:${e}`, { key: `is:${e}`, method: "engine.check", source: e });
  }
  return [...out.values()];
}

/** Whether the engine's text is a vector of two entries, `[a, b]` or `[a; b]`. */
export function isPair(text: string): boolean {
  if (!isVectorLiteral(text)) return false;
  const rows = splitTop(text.slice(1, -1), ";").map((r) => splitArgs(r));
  return rows.length === 1 ? rows[0]!.length === 2 : rows.length === 2 && rows.every((r) => r.length === 1);
}
/** Split at a separator outside parentheses and brackets. */
function splitTop(s: string, sep: string): string[] {
  const out: string[] = [];
  let depth = 0, cur = "";
  for (const c of s) {
    if (c === "(" || c === "[") depth++;
    if (c === ")" || c === "]") depth--;
    if (c === sep && depth === 0) { out.push(cur); cur = ""; } else cur += c;
  }
  out.push(cur);
  return out;
}

/** The point expressions the engine said are vectors of two entries. An expression it refused is
 *  left as written, for its sample to report the refusal at its line. */
export function vectorsOf(replies: Record<string, unknown>): string[] {
  return Object.entries(replies).filter(([key, r]) => {
    const text = (r as Record<string, any> | undefined)?.["rendered"]?.text;
    return key.startsWith("is:") && typeof text === "string" && isPair(text);
  }).map(([key]) => key.slice(3));
}

/** What the engine made of the script's numbers. */
export function numbersOf(spec: SceneSpec, replies: Record<string, unknown>): Record<string, number> {
  const numbers: Record<string, number> = {};
  for (const key of Object.keys(replies)) if (key.startsWith("num:")) {
    const text = reply(spec, replies, key)["rendered"]?.text as string;
    const v = Number(text);
    if (!Number.isFinite(v)) throw new SceneError(`${key.slice(4)} is not a real number (it is ${text})`, lineOf(spec, key));
    numbers[key.slice(4)] = v;
  }
  return numbers;
}

/** The samples a scene needs, once its numbers are known. `movesWithClock(expr)`: whether an
 *  expression mentions the clock (the page reads the identifiers with the editor's lexer). */
export function sampleRequests(spec: SceneSpec, movesWithClock: (expr: string) => boolean, numbers: Record<string, number>, vectors: readonly string[] = []): Request[] {
  const out = new Map<string, Request>();
  const { name: t, from, to } = spec.clock;
  const sample = (pre: string, e: string) => out.set(`${pre}:${e}`, { key: `${pre}:${e}`, method: "engine.plot", source: `plot(${e}, ${t}, ${from}, ${to})` });
  for (const o of spec.objects) {
    for (const e of pointsOf(spec, o, vectors)) sample("pt", e);
    if (o.kind === "value") sample("val", o.args[0]!);
    if (o.kind === "curve" || o.kind === "graph") {
      const [e, s, a, b] = o.args as [string, string, string, string];
      const body = `plot(${e}, ${s}, ${a}, ${b})`;
      // manipulate's frames are exact values: the clock's range as the numbers the engine gave
      out.set(`cv:${o.name}`, movesWithClock(o.args.join(","))
        ? { key: `cv:${o.name}`, method: "engine.manipulate", source: `manipulate(${body}, ${t}, ${numbers[from]}, ${numbers[to]}, ${FRAMES})` }
        : { key: `cv:${o.name}`, method: "engine.plot", source: body });
    }
    if (o.kind === "eq") out.set(`eq:${o.name}`, { key: `eq:${o.name}`, method: "engine.check", source: o.args[0]!, showWork: true });
  }
  return [...out.values()];
}

/** The line of the script a request came from, for an error on it. */
function lineOf(spec: SceneSpec, key: string): number {
  const e = key.slice(key.indexOf(":") + 1);
  // a point is sampled as written or, a vector, as the point it makes: either way it is this object's
  const uses = (o: SceneObj) => { const ws = anchorsOf(o).map((a) => written(spec, a)); return ws.includes(e) || pointsOf(spec, o, []).includes(e) || pointsOf(spec, o, ws).includes(e); };
  const o = spec.objects.find((o) => `cv:${o.name}` === key || `eq:${o.name}` === key || o.args.includes(e) || uses(o));
  if (o) return o.line;
  if (spec.view?.includes(e)) return 1;
  const b = spec.beats.find((b) => b.actions.some((a) => a.kind === "play" && (a.to === e || a.from === e)));
  return b?.line ?? 1;
}

/** A reply, or the SceneError the engine's refusal makes at the request's line. */
function reply(spec: SceneSpec, replies: Record<string, unknown>, key: string): Record<string, any> {
  const r = replies[key] as Record<string, any> | undefined;
  if (!r) throw new SceneError(`no reply for ${key}`, lineOf(spec, key));
  if (r["ok"] === false || r["error"]) throw new SceneError(r["error"]?.message ?? "the engine refused this expression", lineOf(spec, key));
  return r;
}

export type XY = [number, number] | null;
type Series = { points: [number, number | null][]; parametric?: boolean };
/** A sample as a point in the plane: a complex value's real and imaginary parts, a real value on the
 *  real axis (`asGraph`: a function's `(x, y)`). */
const toXY = (s: Series, asGraph = false): XY[] => s.points.map(([a, b]) =>
  b === null ? null : s.parametric || asGraph ? [a, b] : [b, 0]);

/** The clock's value over time: held between plays, eased across one. */
export interface Play { t0: number; t1: number; v0: number; v1: number }
export interface Timeline {
  total: number;
  beats: { start: number; end: number; caption: string }[];
  plays: Play[];
  /** When each object shown or hidden by a beat appears (`on`) or goes; objects absent are always on. */
  vis: Record<string, { t: number; on: boolean }[]>;
  /** When each equation's work runs. */
  works: Record<string, { t0: number; t1: number }[]>;
}
export interface SceneData {
  spec: SceneSpec;
  clock: { from: number; to: number };
  window: [number, number, number, number];
  /** The point expressions that are vectors, sampled as the points they make. */
  vectors: string[];
  /** A point's samples over the clock's range, by its expression. */
  points: Record<string, XY[]>;
  /** A value's samples over the clock's range, by its expression. */
  values: Record<string, (number | null)[]>;
  /** A curve's samples: one set, or one per frame of the clock. */
  curves: Record<string, { pts: XY[] } | { frames: { value: number; pts: XY[] }[] }>;
  /** An equation as typed, then each step's term, as the engine prints them (TeX). */
  eqs: Record<string, string[]>;
  timeline: Timeline;
}

const ease = (p: number) => p < 0.5 ? 2 * p * p : 1 - Math.pow(-2 * p + 2, 2) / 2;
const clamp01 = (x: number) => x < 0 ? 0 : x > 1 ? 1 : x;
/** Long enough to read a caption: a moment, and a little more for each word. */
export const readingTime = (caption: string) => caption ? 1.4 + 0.33 * caption.split(/\s+/).length : 0.8;

/** Lay the beats out in time. `numbers` is what the engine made of each number the script names. */
export function compile(spec: SceneSpec, numbers: Record<string, number>, eqSteps: Record<string, number>): Timeline {
  const tl: Timeline = { total: 0, beats: [], plays: [], vis: {}, works: {} };
  let at = 0, clock = numbers[spec.clock.from]!;
  for (const b of spec.beats) {
    let len = readingTime(b.caption);
    for (const a of b.actions) {
      switch (a.kind) {
        case "show": case "hide":
          for (const n of a.names) (tl.vis[n] ??= []).push({ t: at, on: a.kind === "show" });
          len = Math.max(len, FADE);
          break;
        case "play": {
          const v0 = a.from !== null ? numbers[a.from]! : clock, v1 = numbers[a.to]!;
          tl.plays.push({ t0: at, t1: at + a.dur, v0, v1 });
          clock = v1;
          len = Math.max(len, a.dur);
          break;
        }
        case "wait": len = Math.max(len, a.dur); break;
        case "work": {
          const dur = a.dur ?? STEP * Math.max(1, eqSteps[a.name] ?? 1);
          (tl.works[a.name] ??= []).push({ t0: at, t1: at + dur });
          len = Math.max(len, dur);
          break;
        }
      }
    }
    tl.beats.push({ start: at, end: at + len, caption: b.caption });
    at += len;
  }
  // a scene with no beats plays its clock once, everything shown
  if (!spec.beats.length) {
    tl.plays.push({ t0: 0, t1: PLAY, v0: numbers[spec.clock.from]!, v1: numbers[spec.clock.to]! });
    tl.beats.push({ start: 0, end: PLAY, caption: "" });
    at = PLAY;
  }
  tl.total = Math.max(at, 0.001);
  return tl;
}

/** The clock's value at time `t`. */
export function clockAt(tl: Timeline, start: number, t: number): number {
  let v = start;
  for (const p of tl.plays) {
    if (t >= p.t1) v = p.v1;
    else if (t > p.t0) return p.v0 + (p.v1 - p.v0) * ease((t - p.t0) / (p.t1 - p.t0));
    else break;
  }
  return v;
}

/** How visible an object is at time `t`, 0 to 1. */
export function opacityAt(tl: Timeline, name: string, t: number): number {
  const ev = tl.vis[name];
  if (!ev || !ev.length) return 1;
  // shown from the start when its first beat hides it; otherwise it waits for its first `show`
  let o = ev[0]!.on ? 0 : 1;
  for (const e of ev) {
    if (t < e.t) break;
    const p = clamp01((t - e.t) / FADE);
    o = e.on ? Math.max(o, p) : Math.min(o, 1 - p);
  }
  return o;
}

/** A path's sample at clock value `c` over [from, to], between the two samples either side. */
export function sampleAt(pts: XY[], from: number, to: number, c: number): XY {
  if (!pts.length) return null;
  if (to === from) return pts[0]!;
  const f = clamp01((c - from) / (to - from)) * (pts.length - 1);
  const i = Math.floor(f), j = Math.min(pts.length - 1, i + 1), u = f - i;
  const a = pts[i]!, b = pts[j]!;
  if (!a || !b) return a ?? b;
  return [a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u];
}

/** Gather the engine's replies (to `numberRequests` and `sampleRequests`) into the scene's data.
 *  Throws a SceneError on the first expression the engine refused, at its line. */
export function build(spec: SceneSpec, replies: Record<string, unknown>): SceneData {
  const get = (key: string) => reply(spec, replies, key);
  const numbers = numbersOf(spec, replies);
  const clock = { from: numbers[spec.clock.from]!, to: numbers[spec.clock.to]! };
  const points: Record<string, XY[]> = {};
  const curves: SceneData["curves"] = {};
  const eqs: Record<string, string[]> = {};
  const values: Record<string, (number | null)[]> = {};
  const vectors = vectorsOf(replies);
  // the first curve of a plot reply; a reply with none is the engine refusing, said at the object's line
  const series0 = (key: string, r: Record<string, unknown> = get(key)): Series => {
    const s = (r["series"] as Series[] | undefined)?.[0];
    if (!s || !Array.isArray(s.points)) throw new SceneError(`the engine gave no samples for ${key.slice(key.indexOf(":") + 1)}`, lineOf(spec, key));
    return s;
  };
  for (const key of Object.keys(replies)) {
    if (key.startsWith("pt:")) points[key.slice(3)] = toXY(series0(key));
    if (key.startsWith("val:")) {
      const s = series0(key);
      if (s.parametric) throw new SceneError(`a value is a real number, and ${key.slice(4)} is not`, lineOf(spec, key));
      values[key.slice(4)] = s.points.map(([, b]) => b);
    }
    if (key.startsWith("cv:")) {
      const r = get(key), o = spec.objects.find((o) => o.name === key.slice(3))!, graph = o.kind === "graph";
      curves[o.name] = r["frames"]
        ? { frames: (r["frames"] as { value: number; plot: Record<string, unknown> }[]).map((f) => ({ value: f.value, pts: toXY(series0(key, f.plot), graph) })) }
        : { pts: toXY(series0(key), graph) };
    }
    if (key.startsWith("eq:")) {
      const r = get(key);
      const texs = [r["inputRendered"]?.latex as string, ...((r["derivation"]?.steps ?? []) as { afterRendered?: { latex: string } }[]).map((s) => s.afterRendered?.latex), r["rendered"]?.latex as string]
        .filter((x): x is string => !!x);
      eqs[key.slice(3)] = texs.filter((x, i) => i === 0 || x !== texs[i - 1]);
    }
  }
  const timeline = compile(spec, numbers, Object.fromEntries(Object.entries(eqs).map(([n, t]) => [n, t.length - 1])));
  return { spec, clock, window: windowOf(spec, numbers, points, curves), vectors, points, values, curves, eqs, timeline };
}

/** The scene's window: the one its script gives, or everything it ever draws, with a margin. */
function windowOf(spec: SceneSpec, numbers: Record<string, number>, points: Record<string, XY[]>, curves: SceneData["curves"]): [number, number, number, number] {
  if (spec.view) return spec.view.map((v) => numbers[v]!) as [number, number, number, number];
  let x0 = Infinity, x1 = -Infinity, y0 = Infinity, y1 = -Infinity;
  const add = (p: XY) => { if (p && Number.isFinite(p[0]) && Number.isFinite(p[1])) { x0 = Math.min(x0, p[0]); x1 = Math.max(x1, p[0]); y0 = Math.min(y0, p[1]); y1 = Math.max(y1, p[1]); } };
  for (const ps of Object.values(points)) ps.forEach(add);
  for (const c of Object.values(curves)) ("pts" in c ? [c.pts] : c.frames.map((f) => f.pts)).forEach((ps) => ps.forEach(add));
  if (!Number.isFinite(x0)) return [-1, 1, -1, 1];
  const pad = Math.max(x1 - x0, y1 - y0, 1e-6) * 0.1;
  return [x0 - pad, x1 + pad, y0 - pad, y1 + pad];
}

/** What to draw for one object at one moment. */
export type Item =
  | { name: string; kind: "path"; pts: XY[]; style: Style; opacity: number }
  | { name: string; kind: "dot"; at: [number, number]; style: Style; opacity: number }
  | { name: string; kind: "arrow" | "segment"; from: [number, number]; to: [number, number]; style: Style; opacity: number }
  | { name: string; kind: "label"; at: [number, number]; tex: string; style: Style; opacity: number }
  /** The whole line through two points. */
  | { name: string; kind: "line"; from: [number, number]; to: [number, number]; style: Style; opacity: number }
  | { name: string; kind: "poly"; pts: [number, number][]; style: Style; opacity: number }
  /** The grid the matrix with columns `e1`, `e2` makes of the plane's: the lines `k e1 + s e2` and `s e1 + k e2`. */
  | { name: string; kind: "grid"; e1: [number, number]; e2: [number, number]; style: Style; opacity: number };
/** An equation at one moment: a morph from one TeX to the next at progress `p`. */
export interface EqState { name: string; from: string | null; to: string; p: number; opacity: number }
export interface Frame { time: number; clock: number; beat: number; items: Item[]; eqs: EqState[] }

/** A value as a reader takes it in while it moves: two decimals, no trailing zeros, no `-0`. */
export function formatValue(x: number): string {
  const r = Math.round(x * 100) / 100;
  return (Object.is(r, -0) ? 0 : r).toFixed(2).replace(/\.?0+$/, "");
}

/** A curve's samples at clock value `c`: its own, or its frames either side blended. */
function curveAt(data: SceneData, name: string, c: number): XY[] {
  const cv = data.curves[name]!;
  if ("pts" in cv) return cv.pts;
  const fs = cv.frames;
  if (fs.length === 1) return fs[0]!.pts;
  const { from, to } = data.clock;
  const f = clamp01(to === from ? 0 : (c - from) / (to - from)) * (fs.length - 1);
  const i = Math.floor(f), j = Math.min(fs.length - 1, i + 1), u = f - i;
  const A = fs[i]!.pts, B = fs[j]!.pts;
  if (A.length !== B.length) return u < 0.5 ? A : B;
  return A.map((a, k) => { const b = B[k]; return a && b ? [a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u] : null; });
}

/** Everything the scene shows at time `time`. */
export function frameAt(data: SceneData, time: number): Frame {
  const { spec, timeline: tl } = data;
  const t = Math.max(0, Math.min(tl.total, time));
  const clock = clockAt(tl, data.clock.from, t);
  const beat = Math.max(0, tl.beats.findIndex((b) => t < b.end || b === tl.beats[tl.beats.length - 1]));
  const pointAt = (expr: string, c = clock) => sampleAt(data.points[expr] ?? [], data.clock.from, data.clock.to, c);
  const anchor = (arg: string) => anchorOf(spec, arg, data.vectors);
  const items: Item[] = [];
  const eqs: EqState[] = [];
  for (const o of spec.objects) {
    const opacity = opacityAt(tl, o.name, t);
    if (opacity <= 0) continue;
    const base = { name: o.name, style: o.style, opacity };
    if (o.kind === "point") { const p = pointAt(anchor(o.name)); if (p) items.push({ ...base, kind: "dot", at: p }); }
    if (o.kind === "line") {
      const a = pointAt(anchor(o.args[0]!)), b = pointAt(anchor(o.args[1]!));
      if (a && b) items.push({ ...base, kind: "line", from: a, to: b });
    }
    if (o.kind === "poly") {
      const ps = o.args.map((a) => pointAt(anchor(a)));
      if (ps.every((p) => p)) items.push({ ...base, kind: "poly", pts: ps as [number, number][] });
    }
    if (o.kind === "grid") {
      const e1 = pointAt(columnPoint(o.args[0]!, 1)), e2 = pointAt(columnPoint(o.args[0]!, 2));
      if (e1 && e2) items.push({ ...base, kind: "grid", e1, e2 });
    }
    if (o.kind === "curve" || o.kind === "graph") items.push({ ...base, kind: "path", pts: curveAt(data, o.name, clock) });
    if (o.kind === "arrow" || o.kind === "segment") {
      const a = pointAt(anchor(o.args[0]!)), b = pointAt(anchor(o.args[1]!));
      if (a && b) items.push({ ...base, kind: o.kind, from: a, to: b });
    }
    if (o.kind === "label") { const p = pointAt(anchor(o.args[0]!)); if (p) items.push({ ...base, kind: "label", at: p, tex: o.args[1]!.slice(1, -1) }); }
    if (o.kind === "trace") {
      const expr = anchor(o.args[0]!);
      const pts = data.points[expr] ?? [];
      // from where the clock was when the trace was shown to where it is now
      const shown = (tl.vis[o.name] ?? []).filter((e) => e.on && e.t <= t).pop();
      const c0 = shown ? clockAt(tl, data.clock.from, shown.t) : data.clock.from;
      const [lo, hi] = c0 <= clock ? [c0, clock] : [clock, c0];
      const { from, to } = data.clock, n = pts.length - 1;
      const idx = (c: number) => to === from ? 0 : clamp01((c - from) / (to - from)) * n;
      const path: XY[] = [pointAt(expr, lo)];
      for (let k = Math.ceil(idx(lo)); k <= Math.floor(idx(hi)); k++) path.push(pts[k] ?? null);
      path.push(pointAt(expr, hi));
      items.push({ ...base, kind: "path", pts: path });
    }
    if (o.kind === "eq") {
      const texs = data.eqs[o.name] ?? [];
      if (!texs.length) continue;
      let state: EqState = { name: o.name, from: null, to: texs[0]!, p: 1, opacity };
      for (const w of tl.works[o.name] ?? []) {
        if (t >= w.t1) state = { ...state, from: null, to: texs[texs.length - 1]!, p: 1 };
        else if (t > w.t0) {
          const k = texs.length - 1, f = ((t - w.t0) / (w.t1 - w.t0)) * k;
          const j = Math.min(k - 1, Math.floor(f));
          state = { ...state, from: texs[j]!, to: texs[j + 1]!, p: f - j };
        }
      }
      eqs.push(state);
    }
    if (o.kind === "value") {
      const v = sampleAt((data.values[o.args[0]!] ?? []).map((x) => x === null ? null : [x, 0]), data.clock.from, data.clock.to, clock);
      if (v) eqs.push({ name: o.name, from: null, to: `${o.args[1]!.slice(1, -1)}${formatValue(v[0])}`, p: 1, opacity });
    }
  }
  return { time: t, clock, beat, items, eqs };
}
