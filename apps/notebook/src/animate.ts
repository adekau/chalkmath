// Manipulate: the frames the engine computed for `manipulate(e, p, from, to)`, shown one at a time
// under a slider, and played. The engine evaluates every frame in one reply, so moving the slider or
// playing never waits for it. A plot's frames share the plot's grid of its variable, so while it
// plays the page draws between two neighbouring frames by blending their samples, which makes the
// motion smooth with a few dozen frames; at rest, and wherever the slider stops, it shows the
// engine's own frame. The plain code is here, apart from the page, so it can be tested in Node.

/** The samples a plot draws: `[x, y]` pairs, `y` null where the curve has no finite value. */
export interface Sampled { series: { points: [number, number | null][]; parametric?: boolean }[]; terms?: unknown[] }

/** The vertical window a plot is drawn in: the values' range with its tails trimmed (so an
 *  asymptote does not flatten the rest), the axis included, and a margin. */
export function plotYRange(p: Sampled): [number, number] {
  const ys = p.series.flatMap((s) => s.points.map((q) => q[1])).filter((y): y is number => y !== null).sort((a, b) => a - b);
  if (!ys.length) return [-1, 1];
  const lo = ys[Math.floor(ys.length * 0.02)]!, hi = ys[Math.ceil(ys.length * 0.98) - 1]!;
  let y0 = Math.min(lo, 0), y1 = Math.max(hi, 0);
  if (y1 - y0 < 1e-9) { y0 -= 1; y1 += 1; }
  const pad = (y1 - y0) * 0.08;
  return [y0 - pad, y1 + pad];
}

/** One window for every frame of a manipulated plot, so the axes hold still and what moves is the
 *  curve: the frames' samples taken together. Null when a frame is a curve in the plane or epicycles,
 *  whose window is fitted to both axes at once. */
export function framesWindow(frames: Sampled[]): [number, number] | null {
  if (!frames.length || frames.some((f) => f.terms?.length || f.series.some((s) => s.parametric))) return null;
  return plotYRange({ series: frames.flatMap((f) => f.series) });
}

/** Whether two frames can be blended: the same curves, sampled at the same points. */
export const blendable = (a: Sampled, b: Sampled) =>
  a.series.length === b.series.length && a.series.every((s, i) => !s.parametric && s.points.length === b.series[i]!.points.length);

/** The samples between frames `a` (t = 0) and `b` (t = 1): each value blended; a gap in either is a gap. */
export function blend<S extends Sampled["series"][number]>(a: { series: S[] }, b: Sampled, t: number): S[] {
  return a.series.map((s, i) => ({
    ...s,
    points: s.points.map(([x, ya], j) => {
      const yb = b.series[i]!.points[j]![1];
      return [x, ya === null || yb === null ? null : ya + (yb - ya) * t] as [number, number | null];
    }),
  }));
}

/** How long one play from the first frame to the last lasts: about 120 ms a frame, within 2.5–6 s. */
export const playMs = (frames: number) => Math.min(6000, Math.max(2500, frames * 120));

/** Where a play is, `elapsed` ms after it started at position `start`: a position in [0, n − 1]
 *  (fractional between frames), moving at the pace `playMs` sets, and stopping at the last frame. */
export function playPosition(start: number, elapsed: number, frames: number): number {
  const last = frames - 1;
  if (last <= 0) return 0;
  return Math.min(last, start + (elapsed / playMs(frames)) * last);
}

/** A calculation as one line of LaTeX: `name = w₀ = w₁ = … = value`, from the part with the
 *  parameter put in to its value (the engine's steps). A long one keeps its start and its last
 *  steps, with `⋯` between. Without a calculation it is the value alone (after the name). */
export function workLine(work: string[] | undefined, value: string, name?: string, max = 6): string {
  let chain = work && work.length > 1 ? work : [value];
  if (chain.length > max) chain = [chain[0]!, "\\cdots", ...chain.slice(-(max - 2))];
  const label = name === undefined ? [] : [name.length === 1 ? name : `\\mathrm{${name}}`];
  return [...label, ...chain].join(" = ");
}
