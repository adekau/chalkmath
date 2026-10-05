// A scene cell as a Manim script (https://www.manim.community): the same storyboard, rendered as a
// video by Manim on the reader's computer. The script carries the engine's samples as data, so the
// video shows what the notebook shows: every coordinate in it is one the engine gave, and Python only
// interpolates between them, as the page does (scene.ts). The clock is a ValueTracker; each object is
// redrawn from the samples at the clock's value, with an opacity of its own that the beats fade; each
// beat is one AnimationGroup of its fades, its play of the clock and its equation's work, held for as
// long as the beat lasts in the notebook, with its caption at the foot of the frame.
//
// It is plain code, apart from the page, so it can be tested in Node (and the script rendered).

import { anchorOf, clockAt, columnPoint, FADE, formatValue, type SceneData, type SceneObj, type XY } from "./scene.js";

/** The scene palette in the dark theme: the accent, then the curve colours (`color 1`…`color 6`). */
export const PALETTE = ["#e2872f", "#6ea0e0", "#8fbf5a", "#d67fb8", "#57bdb1", "#b9b4c8"];
const BACKGROUND = "#1f1f1c", AXIS = "#6b6a63", INK = "#e8e4d8";
/** Manim's frame, in its units: 16:9, eight high. */
const FRAME_W = 128 / 9, FRAME_H = 8;

/** A Python string literal: JSON's escapes are Python's too. */
const py = (s: string) => JSON.stringify(s);
const num = (x: number) => Number.isFinite(x) ? String(+x.toFixed(5)) : "None";
const pts = (ps: XY[]) => `[${ps.map((p) => p ? `(${num(p[0])}, ${num(p[1])})` : "None").join(", ")}]`;

/** A Python class name for a scene: `Circles and rotation` → `CirclesAndRotation`. */
export const className = (name: string) => {
  const c = name.replace(/[^A-Za-z0-9]+/g, " ").trim().split(" ").map((w) => w.charAt(0).toUpperCase() + w.slice(1)).join("").slice(0, 40);
  return /^[A-Za-z]/.test(c) ? c : `Scene${c}`;
};

/** A caption's Markdown as LaTeX text: its math kept, `**bold**` and `*emphasis*` made LaTeX's, the
 *  characters LaTeX reserves escaped outside the math. */
export function captionTex(md: string): string {
  let out = "";
  for (const [k, part] of md.split(/(\$\$[^$]+\$\$|\$[^$]+\$)/).entries()) {
    if (k % 2) { out += part.startsWith("$$") ? `$${part.slice(2, -2)}$` : part; continue; }
    out += part
      .replace(/\\([\\`*_$\[\]()#!])/g, "$1")
      .replace(/[&%#_]/g, (c) => `\\${c}`)
      .replace(/\*\*([^*]+)\*\*/g, "\\textbf{$1}")
      .replace(/\*([^*]+)\*/g, "\\emph{$1}")
      .replace(/`([^`]+)`/g, "\\texttt{$1}")
      .replace(/‹([^›]+)›/g, "\\texttt{$1}");
  }
  return out;
}

/** The Python a Manim user runs to render the scene: `manim -pqh <file>.py <ClassName>`. */
export function manimOfScene(data: SceneData, name: string): string {
  const { spec, timeline: tl } = data;
  const [x0, x1, y0, y1] = data.window;
  const objs = spec.objects;
  const colour = (o: SceneObj) => PALETTE[(o.style.color ?? objs.indexOf(o) % PALETTE.length)]!;
  const anchor = (a: string) => anchorOf(spec, a, data.vectors);
  // every point expression any object is drawn from, numbered for the data tables
  const pointKeys = Object.keys(data.points);
  const P = (expr: string) => `PTS[${pointKeys.indexOf(expr)}]`;
  const L: string[] = [];
  const w = (s = "") => L.push(s);

  w(`# ${name}: a ChalkMath scene, exported for Manim (https://www.manim.community).`);
  w(`# Render it with:  manim -pqh ${className(name).toLowerCase()}.py ${className(name)}`);
  w("# Every coordinate below is one the ChalkMath engine sampled; the script only interpolates between them.");
  w("from manim import *");
  w("import numpy as np");
  w("");
  w(`config.background_color = ${py(BACKGROUND)}`);
  w(`FROM, TO = ${num(data.clock.from)}, ${num(data.clock.to)}`);
  w(`X0, X1, Y0, Y1 = ${num(x0)}, ${num(x1)}, ${num(y0)}, ${num(y1)}`);
  w(`S = min(${num(FRAME_W - 0.8)} / (X1 - X0), ${num(FRAME_H - 0.8)} / (Y1 - Y0))`);
  w("CX, CY = (X0 + X1) / 2, (Y0 + Y1) / 2");
  w("");
  w("def at(x, y):");
  w("    return np.array([(x - CX) * S, (y - CY) * S, 0.0])");
  w("");
  w("def sample(ps, c):");
  w("    \"\"\"A path's sample at clock value c, between the two samples either side (None in a gap).\"\"\"");
  w("    if not ps: return None");
  w("    if TO == FROM: return ps[0]");
  w("    f = min(max((c - FROM) / (TO - FROM), 0.0), 1.0) * (len(ps) - 1)");
  w("    i = int(np.floor(f)); j = min(len(ps) - 1, i + 1); u = f - i");
  w("    a, b = ps[i], ps[j]");
  w("    if a is None or b is None: return a if a is not None else b");
  w("    return (a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u)");
  w("");
  w("def frames_at(frames, c):");
  w("    \"\"\"A moving curve at clock value c: its frames either side, blended.\"\"\"");
  w("    if len(frames) == 1: return frames[0]");
  w("    f = min(max((c - FROM) / (TO - FROM) if TO != FROM else 0.0, 0.0), 1.0) * (len(frames) - 1)");
  w("    i = int(np.floor(f)); j = min(len(frames) - 1, i + 1); u = f - i");
  w("    A, B = frames[i], frames[j]");
  w("    if len(A) != len(B): return A if u < 0.5 else B");
  w("    return [None if a is None or b is None else (a[0] + (b[0] - a[0]) * u, a[1] + (b[1] - a[1]) * u) for a, b in zip(A, B)]");
  w("");
  w("def polyline(ps, colour, width, opacity, dashed=False):");
  w("    \"\"\"The runs of a path between its gaps, as lines.\"\"\"");
  w("    g = VGroup(); run = []");
  w("    for p in list(ps) + [None]:");
  w("        if p is not None and np.isfinite(p[0]) and np.isfinite(p[1]): run.append(at(*p)); continue");
  w("        if len(run) > 1:");
  w("            m = VMobject(stroke_color=colour, stroke_width=width, stroke_opacity=opacity).set_points_as_corners(run)");
  w("            g.add(DashedVMobject(m, num_dashes=max(2, int(m.get_arc_length() * 6))) if dashed else m)");
  w("        run = []");
  w("    return g");
  w("");
  w("def fmt(x):");
  w("    \"\"\"A value as the notebook shows it: two decimals at most, no -0.\"\"\"");
  w("    r = round(x * 100) / 100");
  w("    s = (\"%.2f\" % (0.0 if r == 0 else r)).rstrip(\"0\").rstrip(\".\")");
  w("    return s");
  w("");
  w("# the engine's samples of each point over the clock's range");
  w(`PTS = [`);
  for (const k of pointKeys) w(`    ${pts(data.points[k]!)},  # ${k.replace(/\n/g, " ")}`);
  w("]");
  const curveObjs = objs.filter((o) => o.kind === "curve" || o.kind === "graph");
  if (curveObjs.length) {
    w("# each curve's samples: one path, or one per frame of the clock");
    w("CURVES = {");
    for (const o of curveObjs) {
      const cv = data.curves[o.name]!;
      w(`    ${py(o.name)}: [${("pts" in cv ? [cv.pts] : cv.frames.map((f) => f.pts)).map(pts).join(", ")}],`);
    }
    w("}");
  }
  const valueObjs = objs.filter((o) => o.kind === "value");
  if (valueObjs.length) {
    w("# each value's samples over the clock's range");
    w("VALUES = {");
    for (const o of valueObjs) w(`    ${py(o.name)}: [${(data.values[o.args[0]!] ?? []).map((v) => v === null ? "None" : num(v)).join(", ")}],`);
    w("}");
  }
  const eqObjs = objs.filter((o) => o.kind === "eq");
  if (eqObjs.length) {
    w("# each equation as typed, then the engine's steps");
    w("EQS = {");
    for (const o of eqObjs) w(`    ${py(o.name)}: [${(data.eqs[o.name] ?? []).map(py).join(", ")}],`);
    w("}");
  }
  w("");
  w("");
  w(`class ${className(name)}(Scene):`);
  w("    def construct(self):");
  w("        clock = ValueTracker(FROM)");
  w("        c = clock.get_value");
  w("        # the axes, with a tick at each whole number while they are far enough apart to read");
  w("        axes = VGroup()");
  w(`        if ${spec.axes ? "True" : "False"}:`);
  w("            HX, HY = config.frame_width / 2 / S, config.frame_height / 2 / S");
  w(`            if CY - HY < 0 < CY + HY: axes.add(Line(at(CX - HX, 0), at(CX + HX, 0), stroke_color=${py(AXIS)}, stroke_width=1.5))`);
  w(`            if CX - HX < 0 < CX + HX: axes.add(Line(at(0, CY - HY), at(0, CY + HY), stroke_color=${py(AXIS)}, stroke_width=1.5))`);
  w("            if S >= 0.5:");
  w("                for k in range(int(np.ceil(CX - HX)), int(np.floor(CX + HX)) + 1):");
  w(`                    if k: axes.add(Line(at(k, 0) + 0.06 * DOWN, at(k, 0) + 0.06 * UP, stroke_color=${py(AXIS)}, stroke_width=1.5))`);
  w("                for k in range(int(np.ceil(CY - HY)), int(np.floor(CY + HY)) + 1):");
  w(`                    if k: axes.add(Line(at(0, k) + 0.06 * LEFT, at(0, k) + 0.06 * RIGHT, stroke_color=${py(AXIS)}, stroke_width=1.5))`);
  w("        self.add(axes)");
  w("        reach = np.hypot(X1 - X0, Y1 - Y0) * 2 + np.hypot(CX, CY)");
  w("        # how visible each object is; the beats fade these");
  w("        op = {}");
  w("        top = []  # the equations and values above the picture, in order");
  w("        trace_from = {}  # where the clock was when each trace was shown");

  const layer = (o: SceneObj) => o.kind === "grid" ? 0 : o.kind === "poly" ? 1 : o.kind === "point" ? 3 : o.kind === "label" ? 4 : 2;
  for (const o of [...objs].sort((a, b) => layer(a) - layer(b))) {
    const col = py(colour(o));
    const width = o.style.thick ? 6 : o.style.faint ? 2.5 : 4;
    const sOp = o.style.faint ? 0.38 : 1;
    const start = tl.vis[o.name]?.[0]?.on ? 0 : 1;   // hidden until its first `show`; there until its first `hide`
    const v = `op[${py(o.name)}]`;
    w(`        ${v} = ValueTracker(${start})  # ${o.kind} ${o.name}`);
    const redraw = (body: string[]) => {
      w(`        def draw_${o.name}():`);
      for (const b of body) w(`            ${b}`);
      w(`        self.add(always_redraw(draw_${o.name}))`);
    };
    switch (o.kind) {
      case "point":
        redraw([`p = sample(${P(anchor(o.name))}, c())`,
          `if p is None or ${v}.get_value() <= 0: return VMobject()`,
          `return Dot(at(*p), radius=${o.style.thick ? 0.11 : 0.08}, color=${col}).set_opacity(${v}.get_value() * ${sOp})`]);
        break;
      case "curve": case "graph":
        redraw([`if ${v}.get_value() <= 0: return VMobject()`,
          `return polyline(frames_at(CURVES[${py(o.name)}], c()), ${col}, ${width}, ${v}.get_value() * ${sOp}, ${o.style.dashed ? "True" : "False"})`]);
        break;
      case "arrow": case "segment": case "line": {
        const [a, b] = [P(anchor(o.args[0]!)), P(anchor(o.args[1]!))];
        const body = [`a, b = sample(${a}, c()), sample(${b}, c())`, `if a is None or b is None or ${v}.get_value() <= 0: return VMobject()`];
        if (o.kind === "arrow") body.push(
          `if np.hypot(b[0] - a[0], b[1] - a[1]) * S < 1e-3: return VMobject()`,
          `return Arrow(at(*a), at(*b), buff=0, color=${col}, stroke_width=${width}, max_tip_length_to_length_ratio=0.35, max_stroke_width_to_length_ratio=20).set_opacity(${v}.get_value() * ${sOp})`);
        else if (o.kind === "segment") body.push(
          `return ${o.style.dashed ? "DashedLine" : "Line"}(at(*a), at(*b), color=${col}, stroke_width=${width}).set_opacity(${v}.get_value() * ${sOp})`);
        else body.push(
          `d = np.array(b) - np.array(a); n = np.hypot(*d)`,
          `if n < 1e-12: return VMobject()`,
          `u = d / n * reach`,
          `return ${o.style.dashed ? "DashedLine" : "Line"}(at(a[0] - u[0], a[1] - u[1]), at(a[0] + u[0], a[1] + u[1]), color=${col}, stroke_width=${width}).set_opacity(${v}.get_value() * ${sOp})`);
        redraw(body);
        break;
      }
      case "poly":
        redraw([`ps = [sample(p, c()) for p in [${o.args.map((a) => P(anchor(a))).join(", ")}]]`,
          `if any(p is None for p in ps) or ${v}.get_value() <= 0: return VMobject()`,
          `return Polygon(*[at(*p) for p in ps], color=${col}, stroke_width=2).set_fill(${col}, opacity=${v}.get_value() * ${o.style.faint ? 0.1 : 0.2}).set_stroke(opacity=${v}.get_value() * ${o.style.faint ? 0.4 : 1})`]);
        break;
      case "grid":
        redraw([`e1, e2 = sample(${P(columnPoint(o.args[0]!, 1))}, c()), sample(${P(columnPoint(o.args[0]!, 2))}, c())`,
          `if e1 is None or e2 is None or ${v}.get_value() <= 0: return VMobject()`,
          "(a, cc), (b, d) = e1, e2; det = a * d - b * cc; K = 60",
          "if abs(det) > 1e-9:",
          "    HX, HY = config.frame_width / 2 / S, config.frame_height / 2 / S",
          "    K = min(60, int(np.ceil(max(max(abs((d * x - b * y) / det), abs((a * y - cc * x) / det)) for x in (CX - HX, CX + HX) for y in (CY - HY, CY + HY)))) + 1)",
          "g = VGroup()",
          "for k in range(-K, K + 1):",
          "    for (u0, w0), (u1, w1) in (((k, -K), (k, K)), ((-K, k), (K, k))):",
          `        g.add(Line(at(u0 * a + w0 * b, u0 * cc + w0 * d), at(u1 * a + w1 * b, u1 * cc + w1 * d), color=${col}, stroke_width=${o.style.faint ? 1.2 : 1.6} if k else 3, stroke_opacity=${v}.get_value() * (${o.style.faint ? "0.18 if k else 0.35" : "0.42 if k else 0.8"})))`,
          "return g"]);
        break;
      case "trace": {
        const pt = P(anchor(o.args[0]!));
        w(`        trace_from[${py(o.name)}] = ${tl.vis[o.name]?.[0]?.on ? "None" : "FROM"}`);
        redraw([`c0 = trace_from[${py(o.name)}]`,
          `if c0 is None or ${v}.get_value() <= 0: return VMobject()`,
          "lo, hi = sorted((c0, c()))",
          `ps = ${pt}; n = len(ps) - 1`,
          "idx = lambda x: 0 if TO == FROM else min(max((x - FROM) / (TO - FROM), 0.0), 1.0) * n",
          `path = [sample(ps, lo)] + [ps[k] for k in range(int(np.ceil(idx(lo))), int(np.floor(idx(hi))) + 1)] + [sample(ps, hi)]`,
          `return polyline(path, ${col}, ${width}, ${v}.get_value() * ${sOp}, ${o.style.dashed ? "True" : "False"})`]);
        break;
      }
      case "label":
        redraw([`p = sample(${P(anchor(o.args[0]!))}, c())`,
          `if p is None or ${v}.get_value() <= 0: return VMobject()`,
          `return MathTex(${py(o.args[1]!.slice(1, -1))}, color=${col}, font_size=34).next_to(at(*p), UR, buff=0.08).set_opacity(${v}.get_value())`]);
        break;
      case "value":
        w(`        top.append(${py(o.name)})`);
        redraw([`x = sample([(y, 0) if y is not None else None for y in VALUES[${py(o.name)}]], c())`,
          `if x is None or ${v}.get_value() <= 0: return VMobject()`,
          `m = MathTex(${py(o.args[1]!.slice(1, -1))} + fmt(x[0]), color=${py(INK)}, font_size=44)`,
          `m.move_to(UP * (config.frame_height / 2 - 0.55 - 0.75 * top.index(${py(o.name)})))`,
          `return m.add_background_rectangle(color=${py(BACKGROUND)}, opacity=0.8, buff=0.12).set_opacity(${v}.get_value())`]);
        break;
      case "eq":
        // an equation is its current term, swapped as its work runs; it fades with its visibility
        w(`        top.append(${py(o.name)})`);
        break;
    }
  }
  if (eqObjs.length) {
    w("        eq_now = {}");
    w("        def eq_tex(name, k):");
    w(`            return MathTex(EQS[name][k], color=${py(INK)}, font_size=44).move_to(UP * (config.frame_height / 2 - 0.55 - 0.75 * top.index(name)))`);
    for (const o of eqObjs) {
      w(`        eq_now[${py(o.name)}] = eq_tex(${py(o.name)}, 0)`);
      if (!tl.vis[o.name]?.length) w(`        self.add(eq_now[${py(o.name)}])`);
    }
  }
  w(`        caption = VMobject()`);
  w("");

  // the beats, in the notebook's time
  tl.beats.forEach((beat, k) => {
    const b = spec.beats[k];
    const len = beat.end - beat.start;
    w(`        # beat ${k + 1}${beat.caption ? `: ${beat.caption.replace(/\n/g, " ").slice(0, 70)}` : ""}`);
    w("        anims = []");
    // how long the beat's animations run together; the rest of the beat is held
    let busy = 0.3;
    if (beat.caption) {
      w(`        new_caption = Tex(${py(`\\parbox{12cm}{\\centering ${captionTex(beat.caption)}}`)}, color=${py(INK)}, font_size=30).to_edge(DOWN, buff=0.25)`);
      w(`        new_caption.add_background_rectangle(color=${py(BACKGROUND)}, opacity=0.85, buff=0.12)`);
      w("        anims += [FadeOut(caption, run_time=0.3), FadeIn(new_caption, run_time=0.3)]");
      w("        caption = new_caption");
    } else w("        anims.append(FadeOut(caption, run_time=0.3)); caption = VMobject()");
    const acts = b?.actions ?? [];
    const worked = new Set(acts.flatMap((a) => a.kind === "work" ? [a.name] : []));
    for (const a of acts) {
      if (a.kind === "show" || a.kind === "hide") for (const n of a.names) {
        const o = objs.find((x) => x.name === n)!;
        busy = Math.max(busy, FADE);
        // an equation shown and worked in one beat fades in as its work begins (below)
        if (o.kind === "eq") { if (!(a.kind === "show" && worked.has(n))) w(`        anims.append(${a.kind === "show" ? "FadeIn" : "FadeOut"}(eq_now[${py(n)}], run_time=${num(FADE)}))`); }
        else w(`        anims.append(op[${py(n)}].animate(run_time=${num(FADE)}, rate_func=linear).set_value(${a.kind === "show" ? 1 : 0}))`);
        if (o.kind === "trace" && a.kind === "show") w(`        trace_from[${py(n)}] = ${num(clockAt(tl, data.clock.from, beat.start))}`);
      }
      if (a.kind === "play") {
        const p = tl.plays.find((p) => Math.abs(p.t0 - beat.start) < 1e-9)!;
        if (a.from !== null) w(`        clock.set_value(${num(p.v0)})`);
        w(`        anims.append(clock.animate(run_time=${num(a.dur)}, rate_func=rate_functions.ease_in_out_quad).set_value(${num(p.v1)}))`);
        busy = Math.max(busy, a.dur);
      }
      if (a.kind === "wait") busy = Math.max(busy, a.dur);
      if (a.kind === "work") {
        const wk = (tl.works[a.name] ?? []).find((x) => Math.abs(x.t0 - beat.start) < 1e-9);
        const steps = (data.eqs[a.name]?.length ?? 1) - 1;
        const shown = acts.some((x) => x.kind === "show" && x.names.includes(a.name));
        if (wk && steps > 0) {
          const per = (wk.t1 - wk.t0) / steps;
          w(`        steps = [eq_tex(${py(a.name)}, k) for k in range(1, ${steps + 1})]`);
          w(`        anims.append(Succession(${shown ? `FadeIn(eq_now[${py(a.name)}], run_time=${num(FADE)}), ` : ""}*[TransformMatchingShapes(x, y, run_time=${num(per)}) for x, y in zip([eq_now[${py(a.name)}]] + steps[:-1], steps)]))`);
          w(`        eq_now[${py(a.name)}] = steps[-1]`);
          busy = Math.max(busy, (shown ? FADE : 0) + (wk.t1 - wk.t0));
        } else if (shown) w(`        anims.append(FadeIn(eq_now[${py(a.name)}], run_time=${num(FADE)}))`);
      }
    }
    w("        self.play(AnimationGroup(*anims, lag_ratio=0))");
    if (len - busy > 0.01) w(`        self.wait(${num(len - busy)})`);
    w("");
  });
  w("        self.wait(1)");
  return L.join("\n") + "\n";
}
