/**
 * A formula as a page writes it in LaTeX, read into the engine's syntax: `2B + Ph` → `2*B + P*h`,
 * `\frac{1}{2}bh` → `(1)/(2)*b*h`, `\pi r^2 h` → `pi*r^(2)*h`.
 *
 * Translating LaTeX is mechanical, and a small model does it badly (asked for `2B + Ph` it wrote
 * `{2*B+Ph}`, where `Ph` is one name), so code does it. The reading follows LaTeX's own conventions:
 * letters side by side are a product, a subscript belongs to the name before it (`b_1`), braces
 * group. Anything else — sums, integrals, absolute values, units in `\text` with spaces — is refused
 * rather than guessed: the lookup then says it could not read the formula.
 */

const GREEK: Record<string, string> = {
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε", zeta: "ζ", eta: "η", theta: "θ", vartheta: "θ",
  iota: "ι", kappa: "κ", lambda: "λ", mu: "μ", nu: "ν", xi: "ξ", rho: "ρ", sigma: "σ", tau: "τ", upsilon: "υ", phi: "φ",
  varphi: "φ", chi: "χ", psi: "ψ", omega: "ω", Gamma: "Γ", Delta: "Δ", Theta: "Θ", Lambda: "Λ", Xi: "Ξ", Sigma: "Σ",
  Phi: "Φ", Psi: "Ψ", Omega: "Ω",
};
const FUNCTIONS = new Set(["sin", "cos", "tan", "ln", "log", "exp"]);
/** Commands that only space or size: nothing to read. */
const IGNORED = new Set([",", ";", ":", "!", " ", "quad", "qquad", "displaystyle", "textstyle", "left", "right", "big", "Big", "bigl", "bigr", "Bigl", "Bigr"]);
/** Commands whose argument is a name, typeset some way: `\text{base}` is the name `base`. */
const NAMING = new Set(["text", "mathrm", "mathit", "mathbf", "operatorname", "boldsymbol", "mathsf", "textit", "textrm"]);

type Tok = { k: "num" | "id"; v: string } | { k: "fn"; v: string } | { k: "op"; v: string } | { k: "open" } | { k: "close" };

class Refused extends Error {}

/** The formula's right-hand side in engine syntax, with the name on its left when it has one, or
 *  null when the LaTeX holds something this reader does not read. */
export function texToEngine(tex: string): { expr: string; lhs: string } | null {
  try {
    let s = tex.trim().replace(/^\{\\(?:display|text)style\s*([\s\S]*)\}$/, "$1").replace(/[.,;]+\s*$/, "").trim();
    // the right-hand side: after the last `=` at the top level (`V = \frac{1}{3}Bh`, `A = P = …`)
    let depth = 0, eq = -1, firstEq = -1;
    for (let i = 0; i < s.length; i++) {
      const c = s[i]!;
      if (c === "{") depth++; else if (c === "}") depth--;
      else if (c === "=" && depth === 0) { eq = i; if (firstEq < 0) firstEq = i; }
    }
    const lhs = firstEq >= 0 ? s.slice(0, firstEq).trim() : "";
    if (eq >= 0) s = s.slice(eq + 1);
    const toks = read(s);
    if (!toks.length) return null;
    return { expr: join(toks), lhs };
  } catch (e) {
    if (e instanceof Refused) return null;
    throw e;
  }
}

/** The tokens of a stretch of LaTeX. */
function read(s: string): Tok[] {
  const out: Tok[] = [];
  let i = 0;
  /** A braced group's contents, or the one character or command that stands as an argument. */
  const arg = (): string => {
    while (s[i] === " ") i++;
    if (s[i] === "{") {
      let d = 0;
      const start = i;
      for (; i < s.length; i++) { if (s[i] === "{") d++; else if (s[i] === "}" && --d === 0) { i++; return s.slice(start + 1, i - 1); } }
      throw new Refused();
    }
    if (s[i] === "\\") { const m = /^\\([A-Za-z]+|.)/.exec(s.slice(i)); if (!m) throw new Refused(); i += m[0].length; return m[0]; }
    if (i >= s.length) throw new Refused();
    return s[i++]!;
  };
  /** A group's tokens, in parentheses when there is more than one (`r^{2}` is `r^2`). */
  const group = (inner: string): Tok[] => { const t = read(inner); return t.length === 1 ? t : [{ k: "open" }, ...t, { k: "close" }]; };
  while (i < s.length) {
    const c = s[i]!;
    if (/\s|~/.test(c)) { i++; continue; }
    if (/[0-9.]/.test(c)) {
      const m = /^\d*\.?\d+/.exec(s.slice(i));
      if (!m) throw new Refused();
      out.push({ k: "num", v: m[0] }); i += m[0].length; continue;
    }
    if (/[A-Za-z]/.test(c)) {
      // letters side by side are a product (`lwh`), but a word is not: `base` is no b·a·s·e
      if (/^[A-Za-z]{4,}/.test(s.slice(i))) throw new Refused();
      out.push({ k: "id", v: c }); i++; continue;
    }
    if (c === "+" || c === "-" || c === "*" || c === "/") { out.push({ k: "op", v: c }); i++; continue; }
    if (c === "−") { out.push({ k: "op", v: "-" }); i++; continue; }
    if (c === "(" || c === "[") { out.push({ k: "open" }); i++; continue; }
    if (c === ")" || c === "]") { out.push({ k: "close" }); i++; continue; }
    if (c === "{") { out.push(...group(arg())); continue; }
    if (c === "^") { i++; out.push({ k: "op", v: "^" }, ...group(arg())); continue; }
    if (c === "_") {
      i++;
      const sub = arg().replace(/\\(?:text|mathrm)\{([^}]*)\}/g, "$1");
      const prev = out[out.length - 1];
      if (!prev || prev.k !== "id" || !/^[A-Za-z0-9]+$/.test(sub)) throw new Refused();
      prev.v += `_${sub}`;
      continue;
    }
    if (c === "\\") {
      const m = /^\\([A-Za-z]+|.)/.exec(s.slice(i));
      if (!m) throw new Refused();
      i += m[0].length;
      const name = m[1]!;
      if (IGNORED.has(name)) continue;   // `\left(` and `\right)`: the delimiter that follows is read as itself
      if (name === "frac" || name === "dfrac" || name === "tfrac") {
        const num = arg(), den = arg();
        out.push(...group(num), { k: "op", v: "/" }, ...group(den));
        continue;
      }
      if (name === "sqrt") {
        let index: string | null = null;
        if (s[i] === "[") { const end = s.indexOf("]", i); if (end < 0) throw new Refused(); index = s.slice(i + 1, end); i = end + 1; }
        const body = arg();
        if (index === null) out.push({ k: "fn", v: "sqrt" }, { k: "open" }, ...read(body), { k: "close" });
        else out.push(...group(body), { k: "op", v: "^" }, { k: "open" }, { k: "num", v: "1" }, { k: "op", v: "/" }, ...group(index), { k: "close" });
        continue;
      }
      if (name === "pi") { out.push({ k: "id", v: "pi" }); continue; }
      if (GREEK[name]) { out.push({ k: "id", v: GREEK[name]! }); continue; }
      if (name === "cdot" || name === "times" || name === "ast") { out.push({ k: "op", v: "*" }); continue; }
      if (name === "div") { out.push({ k: "op", v: "/" }); continue; }
      if (FUNCTIONS.has(name)) {
        out.push({ k: "fn", v: name });
        // `\sin x` and `\sin{x}` are sin(x); `\sin(x)` carries its own parentheses
        while (s[i] === " ") i++;
        if (s[i] !== "(") out.push({ k: "open" }, ...read(arg()), { k: "close" });
        continue;
      }
      if (NAMING.has(name)) {
        const word = arg().trim();
        if (!/^[A-Za-z][A-Za-z0-9]*$/.test(word)) throw new Refused();
        out.push({ k: "id", v: word });
        continue;
      }
      throw new Refused();
    }
    throw new Refused();
  }
  return out;
}

/** The tokens as engine text, a `*` between things written side by side (`2B`, `Ph`, `r^2 h`, `(a)(b)`). */
function join(toks: Tok[]): string {
  let out = "";
  let depth = 0;
  toks.forEach((t, n) => {
    const prev = toks[n - 1];
    const ends = prev && (prev.k === "num" || prev.k === "id" || prev.k === "close");
    const starts = t.k === "num" || t.k === "id" || t.k === "open" || t.k === "fn";
    if (ends && starts) out += "*";
    if (t.k === "open") { out += "("; depth++; }
    else if (t.k === "close") { if (--depth < 0) throw new Refused(); out += ")"; }
    else if (t.k === "op") out += t.v === "+" || t.v === "-" ? ` ${t.v} ` : t.v;
    else out += t.v;
  });
  if (depth) throw new Refused();
  return out.replace(/^ - /, "-").trim();
}
