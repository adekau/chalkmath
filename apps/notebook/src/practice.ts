/**
 * Practice: exercises made to order, one generator per topic. An exercise that names a topic offers
 * another question of its kind (↻ Another one), as many as the reader wants.
 *
 * A generator writes a question, the source an author would have typed, with its prompt and hints;
 * it never computes the answer. The engine evaluates the question (its value is the answer) and
 * checks the reader's against it, as for any exercise. A generator may work backwards from what it
 * wants the question to be (a system of equations from the solution it should have, a puzzle kept
 * only when exactly one assignment solves it), but what the reader is told is right is the engine's.
 *
 * Generators are seeded: the same seed gives the same question, so a test can send every topic's
 * questions to the engine (`test/practice.test.mjs`) and know each one has an answer.
 */

/** A generated exercise: what an author writes for one (`ex(question, prompt, hints)`). */
export interface Practice { src: string; prompt: string; hints?: string[]; hideQuestion?: boolean }
export interface Topic { id: string; title: string; area: string; make: (r: Rand) => Practice }

// --- randomness ---------------------------------------------------------------------------------

export interface Rand { int(lo: number, hi: number): number; pick<T>(xs: readonly T[]): T; chance(p: number): boolean; shuffle<T>(xs: readonly T[]): T[] }
/** A seeded generator (mulberry32): the same seed, the same draws. */
export function rand(seed: number): Rand {
  let s = seed >>> 0;
  const next = () => {
    s = (s + 0x6d2b79f5) >>> 0;
    let t = s;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const int = (lo: number, hi: number) => lo + Math.floor(next() * (hi - lo + 1));
  return {
    int,
    pick: (xs) => xs[int(0, xs.length - 1)]!,
    chance: (p) => next() < p,
    shuffle: (xs) => { const a = [...xs]; for (let i = a.length - 1; i > 0; i--) { const j = int(0, i); [a[i], a[j]] = [a[j]!, a[i]!]; } return a; },
  };
}
/** A nonzero integer in `lo..hi`. */
const nz = (r: Rand, lo: number, hi: number) => { let n = 0; while (n === 0) n = r.int(lo, hi); return n; };

// --- logic: formulas over p, q, r ---------------------------------------------------------------

type Fm = { k: "v"; n: string } | { k: "not"; a: Fm } | { k: "and" | "or" | "imp" | "iff"; a: Fm; b: Fm };
const v = (n: string): Fm => ({ k: "v", n });
const not = (a: Fm): Fm => ({ k: "not", a });
const bin = (k: "and" | "or" | "imp" | "iff") => (a: Fm, b: Fm): Fm => ({ k, a, b });
const and = bin("and"), or = bin("or"), imp = bin("imp"), iff = bin("iff");
const GLYPH = { and: "∧", or: "∨", imp: "→", iff: "↔" } as const;
const TEX = { and: "\\land", or: "\\lor", imp: "\\to", iff: "\\leftrightarrow" } as const;
/** As typed in a cell: every binary part inside another in parentheses. */
function show(f: Fm, inner = false): string {
  if (f.k === "v") return f.n;
  if (f.k === "not") return `¬${show(f.a, true)}`;
  const s = `${show(f.a, true)} ${GLYPH[f.k]} ${show(f.b, true)}`;
  return inner ? `(${s})` : s;
}
function tex(f: Fm, inner = false): string {
  if (f.k === "v") return f.n;
  if (f.k === "not") return `\\lnot ${tex(f.a, true)}`;
  const s = `${tex(f.a, true)} ${TEX[f.k]} ${tex(f.b, true)}`;
  return inner ? `(${s})` : s;
}
/** Its value under an assignment: used only to choose a puzzle with exactly one solution. */
function holds(f: Fm, env: Record<string, boolean>): boolean {
  switch (f.k) {
    case "v": return env[f.n]!;
    case "not": return !holds(f.a, env);
    case "and": return holds(f.a, env) && holds(f.b, env);
    case "or": return holds(f.a, env) || holds(f.b, env);
    case "imp": return !holds(f.a, env) || holds(f.b, env);
    case "iff": return holds(f.a, env) === holds(f.b, env);
  }
}
/** Distinct variables for a schema's A, B, C, each possibly negated: renaming and negating
 *  variables keeps a tautology one and a non-tautology not one. */
function literals(r: Rand, n: number): Fm[] {
  return r.shuffle(["p", "q", "r"]).slice(0, n).map((x) => (r.chance(0.25) ? not(v(x)) : v(x)));
}
/** A random formula in p, q, r of the given depth, every variable a leaf somewhere if it can be. */
function formula(r: Rand, depth: number): Fm {
  const go = (d: number): Fm => {
    if (d === 0 || (d === 1 && r.chance(0.2))) return r.chance(0.2) ? not(v(r.pick(["p", "q", "r"]))) : v(r.pick(["p", "q", "r"]));
    if (r.chance(0.15)) return not(go(d - 1));
    // two sides alike (`q → q`) make a part that says nothing
    let a = go(d - 1), b = go(d - 1);
    while (show(a).replace(/¬/g, "") === show(b).replace(/¬/g, "")) b = go(d - 1);
    return bin(r.pick(["and", "or", "imp", "iff", "and", "or", "imp"] as const))(a, b);
  };
  for (;;) {
    const f = go(depth);
    const vars = new Set(show(f).match(/[pqr]/g));
    if (vars.size >= 2 && f.k !== "not" && f.k !== "v") return f;
  }
}

type Schema = (a: Fm, b: Fm, c: Fm) => Fm;
/** Tautologies, and the near misses a student mistakes for them. */
const TAUT: [Schema, boolean][] = [
  [(a, b) => imp(a, imp(b, a)), true],
  [(a, b) => or(imp(a, b), imp(b, a)), true],
  [(a, b) => imp(imp(imp(a, b), a), a), true],
  [(a, b) => imp(and(a, b), a), true],
  [(a, b) => iff(imp(a, b), imp(not(b), not(a))), true],
  [(a, b) => iff(not(and(a, b)), or(not(a), not(b))), true],
  [(a, b, c) => imp(and(imp(a, b), imp(b, c)), imp(a, c)), true],
  [(a, b) => imp(and(a, imp(a, b)), b), true],
  [(a, b) => imp(imp(a, b), imp(b, a)), false],
  [(a, b) => imp(imp(a, b), imp(not(a), not(b))), false],
  [(a, b) => imp(or(a, b), a), false],
  [(a, b) => iff(not(and(a, b)), and(not(a), not(b))), false],
  [(a, b, c) => imp(imp(a, or(b, c)), imp(a, b)), false],
  [(a, b) => imp(and(b, imp(a, b)), a), false],
];
/** Laws, and the slips made with them: the two sides and whether they are equivalent. */
const EQUIV: [Schema, Schema, boolean][] = [
  [(a, b) => not(and(a, b)), (a, b) => or(not(a), not(b)), true],
  [(a, b) => not(and(a, b)), (a, b) => and(not(a), not(b)), false],
  [(a, b) => not(or(a, b)), (a, b) => and(not(a), not(b)), true],
  [(a, b) => imp(a, b), (a, b) => or(not(a), b), true],
  [(a, b) => imp(a, b), (a, b) => imp(not(b), not(a)), true],
  [(a, b) => imp(a, b), (a, b) => imp(b, a), false],
  [(a, b) => not(imp(a, b)), (a, b) => and(a, not(b)), true],
  [(a, b) => not(imp(a, b)), (a, b) => imp(not(a), not(b)), false],
  [(a, b, c) => and(a, or(b, c)), (a, b, c) => or(and(a, b), and(a, c)), true],
  [(a, b, c) => and(a, or(b, c)), (a, b, c) => or(and(a, b), c), false],
  [(a, b, c) => imp(a, imp(b, c)), (a, b, c) => imp(and(a, b), c), true],
  [(a, b, c) => imp(imp(a, b), c), (a, b, c) => imp(a, imp(b, c)), false],
  [(a, b) => iff(a, b), (a, b) => or(and(a, b), and(not(a), not(b))), true],
  [(a, b) => iff(a, b), (a, b) => or(imp(a, b), imp(b, a)), false],
];

const PEOPLE = [{ name: "Ann", v: "a" }, { name: "Bob", v: "b" }, { name: "Cy", v: "c" }];
type Person = (typeof PEOPLE)[number];
/** What an islander can say, about the others in the puzzle: the words, and what they say as a formula. */
function claims(s: Person, all: Person[]): { words: string; fm: Fm }[] {
  const others = all.filter((p) => p !== s), out: { words: string; fm: Fm }[] = [];
  for (const o of others) {
    out.push({ words: `${o.name} is a knave.`, fm: not(v(o.v)) });
    out.push({ words: `${o.name} is a knight.`, fm: v(o.v) });
    out.push({ words: `${o.name} and I are of the same kind.`, fm: iff(v(s.v), v(o.v)) });
    out.push({ words: `${o.name} and I are of different kinds.`, fm: not(iff(v(s.v), v(o.v))) });
    out.push({ words: `${o.name} and I are both knaves.`, fm: and(not(v(s.v)), not(v(o.v))) });
    out.push({ words: `At least one of ${o.name} and me is a knave.`, fm: or(not(v(s.v)), not(v(o.v))) });
    out.push({ words: `If I am a knight, so is ${o.name}.`, fm: imp(v(s.v), v(o.v)) });
  }
  if (others.length === 2) {
    const [o, t] = others as [Person, Person];
    out.push({ words: `${o.name} or ${t.name} is a knave.`, fm: or(not(v(o.v)), not(v(t.v))) });
    out.push({ words: `Exactly one of ${o.name} and ${t.name} is a knight.`, fm: not(iff(v(o.v), v(t.v))) });
    out.push({ words: `${o.name} and ${t.name} are both knights.`, fm: and(v(o.v), v(t.v)) });
  }
  return out;
}
function knights(r: Rand): Practice {
  for (;;) {
    const ps = PEOPLE.slice(0, r.chance(0.6) ? 2 : 3);
    const said = ps.map((s) => ({ s, ...r.pick(claims(s, ps)) }));
    const each = said.map((x) => iff(v(x.s.v), x.fm)), whole = each.reduce((x, y) => and(x, y));
    // a puzzle has exactly one answer: the one assignment of knights and knaves the statements allow
    let solutions = 0;
    for (let m = 0; m < 1 << ps.length; m++) if (holds(whole, Object.fromEntries(ps.map((p, k) => [p.v, !!(m & (1 << k))])))) solutions++;
    if (solutions !== 1) continue;
    const names = ps.map((p) => p.name), vars = ps.map((p) => `$${p.v}$`);
    const list = (xs: string[]) => (xs.length === 2 ? `${xs[0]} and ${xs[1]}` : `${xs.slice(0, -1).join(", ")} and ${xs[xs.length - 1]}`);
    return {
      src: `sat(${each.map((f) => show(f, true)).join(" ∧ ")})`,
      prompt: `Knights always tell the truth and knaves always lie; each person is one or the other. You meet ${list(names)}. ${said.map((x) => `${x.s.name} says "${x.words}"`).join(" ")}\n\nWho is a knight and who is a knave? With ${list(ps.map((p) => `$${p.v}$ for "${p.name} is a knight"`))}, give the assignment to ${list(vars)}, such as \`{${ps.map((p) => `${p.v} = false`).join(", ")}}\` (all knaves).`,
      hints: [
        ...said.map((x) => `${x.s.name}'s statement: what ${x.s.name} says is $${tex(x.fm)}$, and it is true exactly when ${x.s.name} is a knight: $${x.s.v} \\leftrightarrow ${tex(x.fm, true)}$.`),
        `Try each person as a knight in turn, and see which statements that forces.`,
      ],
      hideQuestion: true,
    };
  }
}

// --- calculus -----------------------------------------------------------------------------------

/** `c x^n` as typed: `3x^2`, `-x`, `5`. */
function mono(c: number, n: number, first: boolean): string {
  const sign = c < 0 ? (first ? "-" : " - ") : first ? "" : " + ";
  const a = Math.abs(c);
  const body = n === 0 ? `${a}` : `${a === 1 ? "" : a}${n === 1 ? "x" : `x^${n}`}`;
  return sign + body;
}
/** A polynomial from its terms [coefficient, power], highest power first. */
const poly = (terms: [number, number][]) => terms.map(([c, n], k) => mono(c, n, k === 0)).join("");
const polyTex = (terms: [number, number][]) => poly(terms).replace(/\^(\d+)/g, "^{$1}");
function randPoly(r: Rand, maxDeg: number, maxTerms: number, lo = -9, hi = 9): [number, number][] {
  const powers = r.shuffle([...Array(maxDeg + 1).keys()]).slice(0, r.int(2, maxTerms)).sort((a, b) => b - a);
  if (powers[0]! < 2) powers.unshift(r.int(2, maxDeg));
  return powers.map((n) => [nz(r, lo, hi), n]);
}
/** `kx`, `x^2`, `x^2 + 1`, … : the inside of a chain (`sums`: only a sum, inside a power). */
function inner(r: Rand, sums = false): string {
  const k = r.int(2, 5), c = nz(r, -4, 4), plus = `${c < 0 ? "-" : "+"} ${Math.abs(c)}`;
  return r.pick([...(sums ? [] : [`${k}x`, `x^2`, `x^3`]), `x^2 ${plus}`, `${k}x ${plus}`]);
}

// --- λ-calculus ---------------------------------------------------------------------------------

/** Combinators and how many arguments they take before they are done. */
const COMBS: [string, number][] = [
  ["λx. x", 1], ["λx. λy. x", 2], ["λx. λy. y", 2], ["λf. λx. f (f x)", 2], ["λf. λx. λy. f y x", 3],
  ["λf. λg. λx. f (g x)", 3], ["λx. λy. λz. x z (y z)", 3], ["λx. λf. f x", 2], ["λx. x x", 1],
];
const TYPED: string[] = [
  "λx. x", "λx. λy. x", "λx. λy. y", "λf. λx. f x", "λf. λx. f (f x)", "λx. λf. f x", "λf. λx. λy. f y x",
  "λf. λg. λx. f (g x)", "λf. λg. λx. g (f x)", "λx. λy. λz. x z (y z)", "λf. λx. λy. f x (f x y)", "λp. λq. λx. p (q x) x",
];

// --- the topics ---------------------------------------------------------------------------------

const vec = (r: Rand, n: number, lo = -5, hi = 5) => `[${Array.from({ length: n }, () => r.int(lo, hi)).join(", ")}]`;
const mat = (rows: number[][]) => `[${rows.map((row) => row.join(", ")).join("; ")}]`;

// --- chemistry: reactions with one balancing each, the reactants then the products --------------

const REACTIONS: [string[], string[]][] = [
  [["CH4", "O2"], ["CO2", "H2O"]], [["C3H8", "O2"], ["CO2", "H2O"]], [["C2H6", "O2"], ["CO2", "H2O"]],
  [["C4H10", "O2"], ["CO2", "H2O"]], [["C6H12O6", "O2"], ["CO2", "H2O"]], [["H2", "O2"], ["H2O"]],
  [["Fe", "O2"], ["Fe2O3"]], [["Al", "O2"], ["Al2O3"]], [["N2", "H2"], ["NH3"]], [["KClO3"], ["KCl", "O2"]],
  [["Na", "H2O"], ["NaOH", "H2"]], [["Ca(OH)2", "HCl"], ["CaCl2", "H2O"]], [["Al", "HCl"], ["AlCl3", "H2"]],
  [["Fe2O3", "CO"], ["Fe", "CO2"]], [["NH3", "O2"], ["NO", "H2O"]],
];
/** The atoms in one molecule of a formula: `Ca(OH)2` is Ca 1, O 2, H 2. */
function atoms(f: string): Map<string, number> {
  const out = new Map<string, number>();
  let i = 0;
  const num = () => { const m = /^\d+/.exec(f.slice(i)); if (!m) return 1; i += m[0].length; return Number(m[0]); };
  const group = (): Map<string, number> => {
    const g = new Map<string, number>();
    while (i < f.length && f[i] !== ")") {
      let part: Map<string, number>;
      if (f[i] === "(") { i++; part = group(); i++; }
      else { const m = /^[A-Z][a-z]?/.exec(f.slice(i))!; i += m[0].length; part = new Map([[m[0], 1]]); }
      const k = num();
      for (const [e, n] of part) g.set(e, (g.get(e) ?? 0) + n * k);
    }
    return g;
  };
  for (const [e, n] of group()) out.set(e, n);
  return out;
}
const grid = (r: Rand, n: number, m: number, lo: number, hi: number) => Array.from({ length: n }, () => Array.from({ length: m }, () => r.int(lo, hi)));
/** `2x - y = 3` in LaTeX, from its coefficients. */
const lin = (a: number, b: number, e: number) => `${mono(a, 1, true)}${mono(b, 1, false).replace("x", "y")} = ${e}`;
const cpx = (a: number, b: number) => `${a} ${b < 0 ? "-" : "+"} ${Math.abs(b) === 1 ? "" : Math.abs(b)}i`;

export const TOPICS: Topic[] = [
  { id: "logic.taut", area: "Logic", title: "Tautology or not", make: (r) => {
    const [s] = r.pick(TAUT), [a, b, c] = literals(r, 3);
    return { src: `taut(${show(s(a!, b!, c!))})`, prompt: "Is this formula a tautology, true in every row of its truth table?",
      hints: ["An implication fails only with a true premise and a false conclusion: look for a row like that.", "If you find a row where it is false, the answer is false."] };
  } },
  { id: "logic.equiv", area: "Logic", title: "Equivalent or not", make: (r) => {
    const [x, y] = r.pick(EQUIV), [a, b, c] = literals(r, 3);
    const [p, q] = r.chance(0.5) ? [x(a!, b!, c!), y(a!, b!, c!)] : [y(a!, b!, c!), x(a!, b!, c!)];
    return { src: `equiv(${show(p)}, ${show(q)})`, prompt: "Are these two formulas equivalent, true in exactly the same rows?",
      hints: ["Look for a row where one is true and the other false; one such row is enough for false."] };
  } },
  { id: "logic.sat", area: "Logic", title: "A satisfying assignment", make: (r) => ({
    src: `sat(${show(formula(r, 2))})`, prompt: "Find an assignment that makes the formula true, or answer `false` if there is none.",
    hints: ["Work from the outside in: what must each part be for the whole to be true?"] }) },
  { id: "logic.falsify", area: "Logic", title: "A counterexample", make: (r) => ({
    src: `falsify(${show(formula(r, 2))})`, prompt: "Find an assignment that makes the formula false, or answer `false` if there is none.",
    hints: ["An implication is false only when its premise is true and its conclusion false; a conjunction when either part is false."] }) },
  ...(["nnf", "cnf", "dnf"] as const).map((form): Topic => ({
    id: `logic.${form}`, area: "Logic", title: form === "nnf" ? "Negation normal form" : form === "cnf" ? "Conjunctive normal form" : "Disjunctive normal form",
    make: (r) => ({ src: `${form}(${show(formula(r, 2))})`,
      prompt: form === "nnf" ? "Rewrite the formula in negation normal form: only ∧, ∨ and negations of variables."
        : form === "cnf" ? "Rewrite the formula in conjunctive normal form: an ∧ of clauses, each an ∨ of literals."
        : "Rewrite the formula in disjunctive normal form: an ∨ of terms, each an ∧ of literals.",
      hints: ["First remove → and ↔: $p \\to q \\equiv \\lnot p \\lor q$.", "Push negations in with De Morgan's laws, then distribute."] }),
  })),
  { id: "logic.knights", area: "Logic", title: "Knights and knaves", make: knights },
  { id: "logic.minimize", area: "Logic", title: "The smallest DNF", make: (r) => ({
    src: `minimize(${show(formula(r, 2))})`, prompt: "Find the smallest DNF with the same truth table: the fewest terms, then the fewest literals.",
    hints: ["Read off the true rows, then merge two terms that differ in one variable: $(x \\land y) \\lor (x \\land \\lnot y) \\equiv x$.", "Keep only the terms some true row needs."] }) },

  { id: "calculus.power", area: "Calculus", title: "Derivatives of polynomials", make: (r) => ({
    src: `diff(${poly(randPoly(r, 5, 3))}, x)`, prompt: "Differentiate.", hints: ["Term by term: the derivative of $x^n$ is $n x^{n-1}$, and of a constant $0$."] }) },
  { id: "calculus.product", area: "Calculus", title: "The product rule", make: (r) => ({
    src: `diff(${r.pick(["x", "x^2", "x^3", "2x", "3x^2"])} * ${r.pick(["sin(x)", "cos(x)", "exp(x)", "ln(x)"])}, x)`, prompt: "Differentiate.",
    hints: ["The product rule: $(fg)' = f'g + fg'$."] }) },
  { id: "calculus.chain", area: "Calculus", title: "The chain rule", make: (r) => {
    const src = r.pick([() => `sin(${inner(r)})`, () => `cos(${inner(r)})`, () => `exp(${inner(r)})`, () => `(${inner(r, true)})^${r.int(2, 4)}`])();
    return { src: `diff(${src}, x)`, prompt: "Differentiate.", hints: ["The chain rule: the outer function's derivative at the inside, times the inside's derivative."] };
  } },
  { id: "calculus.slope", area: "Calculus", title: "Slopes of tangent lines", make: (r) => {
    const p = randPoly(r, 3, 3, -5, 5), a = r.int(-3, 3);
    return { src: `subst(diff(${poly(p)}, x), x, ${a})`, prompt: `What is the slope of $y = ${polyTex(p)}$ at $x = ${a}$?`,
      hints: ["The slope is the derivative, evaluated at the point."], hideQuestion: true };
  } },
  { id: "calculus.antiderivative", area: "Calculus", title: "Antiderivatives", make: (r) => {
    // a power whose antiderivative has a whole coefficient, and a function of kx
    const n = r.int(1, 4), c = (n + 1) * nz(r, -3, 3), k = r.int(2, 4);
    const terms = r.shuffle([mono(c, n, true), r.pick([`sin(${k}x)`, `cos(${k}x)`, `exp(${k}x)`])]);
    return { src: `integrate(${terms.join(" + ").replace("+ -", "- ")}, x)`,
      prompt: "Find an antiderivative (leave out the constant).", hints: ["Guess, differentiate, fix: the derivative of $x^{n+1}$ is $(n+1)x^n$.", "For $\\cos(kx)$, $\\sin(kx)/k$: divide by the inner derivative."] };
  } },
  { id: "calculus.definite", area: "Calculus", title: "Definite integrals", make: (r) => {
    const a = r.int(-1, 2), b = a + r.int(1, 3);
    return { src: `integrate(${poly(randPoly(r, 2, 3, -4, 4))}, x, ${a}, ${b})`, prompt: "Evaluate the integral.", hints: ["Find an antiderivative $F$; the answer is $F(b) - F(a)$."] };
  } },
  { id: "calculus.complex", area: "Calculus", title: "Multiplying complex numbers", make: (r) => ({
    src: `(${cpx(nz(r, -5, 5), nz(r, -5, 5))})*(${cpx(nz(r, -5, 5), nz(r, -5, 5))})`, prompt: "Multiply, and give the answer as $a + bi$.",
    hints: ["Expand as for any product of sums, then use $i^2 = -1$."] }) },

  { id: "linear-algebra.dot", area: "Linear algebra", title: "Dot products", make: (r) => {
    const n = r.int(2, 3);
    return { src: `dot(${vec(r, n)}, ${vec(r, n)})`, prompt: "Compute the dot product.", hints: ["Multiply entry by entry, and add."] };
  } },
  { id: "linear-algebra.matvec", area: "Linear algebra", title: "A matrix times a vector", make: (r) => ({
    src: `${mat(grid(r, 2, 2, -4, 4))}*${mat(grid(r, 2, 1, -4, 4))}`, prompt: "Multiply.", hints: ["Each entry of the result is a row of the matrix dotted with the vector."] }) },
  { id: "linear-algebra.matmul", area: "Linear algebra", title: "Matrix products", make: (r) => ({
    src: `${mat(grid(r, 2, 2, -3, 4))}*${mat(grid(r, 2, 2, -3, 4))}`, prompt: "Multiply.", hints: ["Entry $(i, j)$ is row $i$ of the first dotted with column $j$ of the second."] }) },
  { id: "linear-algebra.det2", area: "Linear algebra", title: "2×2 determinants", make: (r) => ({
    src: `det(${mat(grid(r, 2, 2, -6, 6))})`, prompt: "Compute the determinant.", hints: ["$ad - bc$."] }) },
  { id: "linear-algebra.det3", area: "Linear algebra", title: "3×3 determinants", make: (r) => ({
    src: `det(${mat(grid(r, 3, 3, -2, 3))})`, prompt: "Compute the determinant.", hints: ["Expand along a row or column with zeros in it."] }) },
  { id: "linear-algebra.rref", area: "Linear algebra", title: "Solving 2×2 systems", make: (r) => {
    // the system is made from the solution it should have, with an invertible matrix
    let a = 0, b = 0, c = 0, d = 0;
    while (a * d - b * c === 0) [a, b, c, d] = [r.int(-3, 3), r.int(-3, 3), r.int(-3, 3), r.int(-3, 3)];
    const x = r.int(-4, 4), y = r.int(-4, 4), e = a * x + b * y, f = c * x + d * y;
    const row = (p: number, q: number, s: number) => (p === 0 ? `${mono(q, 1, true).replace("x", "y")} = ${s}` : q === 0 ? `${mono(p, 1, true)} = ${s}` : lin(p, q, s));
    return { src: `rref(${mat([[a, b, e], [c, d, f]])})`, prompt: `Solve $${row(a, b, e)},\\ ${row(c, d, f)}$ by reducing the augmented matrix. Give the reduced matrix.`,
      hints: [`The augmented matrix is \`${mat([[a, b, e], [c, d, f]])}\`.`, "Make a leading 1 in the first row, clear the column below it, then work up."], hideQuestion: true };
  } },

  { id: "linear-algebra.balance", area: "Linear algebra", title: "Balancing chemical equations", make: (r) => {
    const [left, right] = r.pick(REACTIONS);
    // the reactants in another order sometimes: the same reaction, another matrix
    const ls = r.chance(0.5) ? r.shuffle(left) : left, all = [...ls, ...right];
    const counts = all.map(atoms), elements = [...new Set(counts.flatMap((c) => [...c.keys()]))];
    const m = elements.map((e) => all.map((f, j) => (counts[j]!.get(e) ?? 0) * (j < ls.length ? 1 : -1)));
    const chem = (fs: string[]) => fs.map((f) => `\\mathrm{${f.replace(/(\d+)/g, "_{$1}")}}`).join(" + ");
    return { src: `nullspace(${mat(m)})`, prompt: `Balance $${chem(ls)} \\to ${chem(right)}$: give the coefficients, in the order written and in the smallest whole numbers, as a column $[a; b; \\ldots]$.`,
      hints: [`One row per element (${elements.join(", ")}), one column per compound: the atoms of the element in it, negative for the products. The coefficients are the null space.`,
        "Reduce the matrix, set the free variable to 1, and multiply by the smallest number that clears the fractions."], hideQuestion: true };
  } },

  { id: "lambda.beta", area: "λ-calculus", title: "β-reduction", make: (r) => {
    const [f, n] = r.pick(COMBS);
    const args = Array.from({ length: n }, () => r.pick(["a", "b", "c", "(λy. y)", "(λx. λy. x)"]));
    return { src: `(${f}) ${args.join(" ")}`, prompt: "Reduce to normal form.", hints: ["Application groups to the left: substitute the first argument first."] };
  } },
  { id: "lambda.church", area: "λ-calculus", title: "Church numerals and booleans", make: (r) => {
    const n = () => r.int(0, 3), b = () => r.pick(["true", "false"]);
    const src = r.pick([() => `add ${n()} ${n()}`, () => `mul ${r.int(1, 3)} ${r.int(1, 3)}`, () => `succ ${n()}`, () => `iszero ${n()}`,
      () => `not ${b()}`, () => `and ${b()} ${b()}`, () => `or ${b()} ${b()}`])();
    return { src, prompt: "Reduce, and give the answer as a numeral, `true` or `false`.", hints: ["Unfold the definitions, then reduce: a numeral $n$ applies $f$ $n$ times."] };
  } },
  { id: "lambda.infer", area: "λ-calculus", title: "Type inference", make: (r) => ({
    src: `infer: ${r.pick(TYPED)}`, prompt: "Infer the most general type.",
    hints: ["Give each bound variable a type variable, write an equation for each application, and solve them."] }) },
];
const BY_ID = new Map(TOPICS.map((t) => [t.id, t]));
export const topicOf = (id: string | undefined) => (id ? BY_ID.get(id) : undefined);

/** Topic `id`'s question for `seed`, or null for a topic there is no generator for. */
export function generate(id: string, seed: number): Practice | null {
  const t = BY_ID.get(id);
  return t ? t.make(rand(seed)) : null;
}
