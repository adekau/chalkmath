// Animated graphs: a slider played from one end of its range to the other, and the window a plot
// keeps while a slider drives it. The animation is the slider moving on its own; each frame is a run
// of the cells that depend on it, as a drag would make, so whatever follows a slider (a plot, a
// number, a matrix) animates with no more than a slider to set up. The plain code is here, apart
// from the page, so it can be tested in Node.

/** A slider's range, and which way ▶ Play moves it (toward `max` unless `play` is "down"). */
export interface SliderRange { min: number; max: number; step: number; play?: "up" | "down" }

/** The decimals a number is written with: `0.05` has 2, `3` none. */
const decimals = (x: number) => {
  const s = String(x), e = /e-(\d+)$/.exec(s);
  if (e) return Number(e[1]) + (s.split("e")[0]!.split(".")[1]?.length ?? 0);
  return s.split(".")[1]?.length ?? 0;
};

/** A number as a slider writes it: no float noise from the step arithmetic. */
export function sliderNum(x: number, step: number, min = 0): number {
  const d = Math.max(0, -Math.floor(Math.log10(step) + 1e-9), decimals(min));
  return Number(x.toFixed(Math.min(10, d)));
}

/** At most this many frames in one play: a fine range is stepped through in strides. */
export const MAX_FRAMES = 120;
/** A play lasts about this long, each frame held between `FRAME_MS`. */
export const PLAY_MS = 6000;
export const FRAME_MS: [number, number] = [60, 400];

/** The positions ▶ Play moves a slider through, from `value` to the end it plays toward. A slider
 *  already at that end starts over from the other one; the last frame is always the end itself. */
export function playFrames(sl: SliderRange, value: number): number[] {
  const n = Math.max(1, Math.round((sl.max - sl.min) / sl.step));
  const down = sl.play === "down";
  const at = (k: number) => sliderNum(Math.min(sl.max, sl.min + k * sl.step), sl.step, sl.min);
  const end = down ? 0 : n;
  let i = Math.min(n, Math.max(0, Math.round((value - sl.min) / sl.step)));
  const frames: number[] = [];
  if (i === end) { i = down ? n : 0; frames.push(at(i)); }
  const stride = Math.max(1, Math.ceil(n / MAX_FRAMES));
  for (;;) {
    i = down ? Math.max(end, i - stride) : Math.min(end, i + stride);
    frames.push(at(i));
    if (i === end) break;
  }
  return frames;
}

/** How long each of `count` frames is held: the play lasts about `PLAY_MS`. */
export const frameMs = (count: number) => Math.min(FRAME_MS[1], Math.max(FRAME_MS[0], PLAY_MS / Math.max(1, count)));

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

/** Whether a plot can keep a window: a graph `y = f(x)`, not a curve in the plane or epicycles,
 *  whose window is fitted to both axes at once. */
export const holdsWindow = (p: Sampled) => !p.terms?.length && !p.series.some((s) => s.parametric);

/** The window a plot keeps while a slider drives it: the one it had, widened to take in the new
 *  curves, and never narrowed, so the axes hold still and a curve's motion is the curve's. */
export function holdWindow(held: [number, number] | null | undefined, p: Sampled): [number, number] | null {
  if (!holdsWindow(p)) return null;
  const next = plotYRange(p);
  return held ? [Math.min(held[0], next[0]), Math.max(held[1], next[1])] : next;
}
