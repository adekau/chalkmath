/**
 * The engine's worlds (`engine/MathEngine/World.lean`) as the notebook knows them: which cell sources
 * belong to which world, and each world's lexicon (its commands, keywords and glyphs), for labelling
 * a cell before the engine has read it, for the typeset input (which names are calls) and for the
 * highlighter. The engine publishes the list in `engine.capabilities.worlds`; `FALLBACK_WORLDS` is
 * the list as of this build, for an engine that predates it, and `test/worlds.test.mjs` holds it
 * equal to what the native engine publishes.
 *
 * No DOM here, so the module is tested in Node.
 */
import type { WorldInfo } from "@chalkmath/protocol";

/** The worlds as of this build; the engine's own list replaces it when the engine starts. */
export const FALLBACK_WORLDS: WorldInfo[] = [
  { id: "system", label: "Transition systems",
    commands: ["system", "states", "invariant", "inductive", "reach", "deadlock", "trace", "ctl", "eventually", "refines", "replicas", "rules", "rewrite", "terminates", "critical"],
    keywords: ["var", "in", "init", "action", "when", "do", "fair", "strong"],
    glyphs: [":=", "<-", "->", "∧", "∨", "¬", "=", "≠", "<", ">", "≤", "≥", "..", ";", ":", "\n"],
    names: [],
    markers: [] },
  { id: "poset", label: "Order theory",
    commands: ["poset", "divisors", "subsets", "chain", "map", "hasse", "join", "meet", "sup", "inf", "upper", "lower", "lattice", "top", "bottom", "le", "maximal", "minimal", "monotone", "lfp", "gfp", "fixpoints", "rel", "kernel", "reflexive", "symmetric", "antisymmetric", "transitive", "equivalence", "preorder", "closure", "classes", "finer", "wellfounded", "measure", "op", "joinop", "meetop", "table", "associative", "commutative", "idempotent", "semilattice", "identity", "fold", "order", "distributive", "complement", "complemented", "boolean", "product", "galois", "closureop", "context", "concepts", "secure", "events", "clocks", "concurrent"],
    keywords: [],
    glyphs: ["<", "->", "=", "|", "..", "{", "}"],
    names: [],
    markers: [] },
  { id: "logic", label: "Logic",
    commands: ["truthtable", "taut", "sat", "falsify", "equiv", "nnf", "cnf", "dnf"],
    keywords: ["and", "or", "not", "implies", "iff", "forall", "exists", "in"],
    glyphs: ["∧", "∨", "¬", "→", "↔", "⊤", "⊥", "∀", "∃", "∈", "≤", "≥", "≠", "<->", "->", "=>", "&&", "/\\", "||", "\\/", "<=", ">=", "!=", "==", "!", "~", "..", ","],
    names: ["prime", "even", "odd", "true", "false"],
    markers: ["¬", "∧", "∨", "→", "↔", "⊤", "⊥", "∀", "∃", "<->", "->", "&&", "||", "forall", "exists"] },
  { id: "lambda", label: "λ-calculus",
    commands: ["normal", "cbn", "cbv", "applicative", "eta", "fv", "db", "alpha", "subst", "type", "infer"],
    keywords: [],
    glyphs: ["λ", "\\", ".", ":=", "->", "→", "⊢", "|-", ":"],
    names: ["true", "false", "and", "or", "not", "if", "zero", "succ", "add", "mul", "pow", "iszero", "pair", "fst", "snd", "id", "const", "K", "S", "I", "omega", "Y"],
    markers: ["λ", "\\", ":="] },
  { id: "math", label: "Algebra",
    commands: ["sin", "cos", "tan", "sec", "csc", "cot", "arcsin", "arccos", "arctan", "sinh", "cosh", "tanh", "exp", "ln", "log", "sqrt", "abs", "conj", "re", "im", "arg", "diff", "simplify", "expand", "factor", "N", "det", "rref", "transpose", "solve", "subst", "integrate", "plot", "sign", "dot", "norm", "sum", "exptotrig", "epicycles", "dft", "manipulate", "column", "total", "mean", "variance", "stdev", "min", "max", "median"],
    keywords: [],
    glyphs: [],
    names: [],
    markers: [] },
];

let WORLDS: readonly WorldInfo[] = FALLBACK_WORLDS;

/** Take the engine's list (`capabilities.worlds`); an engine without one keeps the fallback. */
export function setWorlds(ws: readonly WorldInfo[] | undefined): void {
  WORLDS = ws?.length ? ws : FALLBACK_WORLDS;
}
export const worlds = (): readonly WorldInfo[] => WORLDS;
export const worldById = (id: string): WorldInfo | undefined => WORLDS.find((w) => w.id === id);

/** The worlds beside algebra, in the order the engine asks them. */
const others = () => WORLDS.filter((w) => w.id !== "math");
const esc = (s: string) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

/** `[let name =] cmd(` for one of `cmds`. */
export function commandRegex(cmds: readonly string[]): RegExp {
  return new RegExp(`^(let\\s+\\w+\\s*=\\s*)?(${cmds.map(esc).join("|")})\\s*\\(`);
}
const regexes = new Map<string, RegExp>();
const cmdRe = (w: WorldInfo) => { let r = regexes.get(w.id); if (!r || !cmdRe.worlds || cmdRe.worlds !== WORLDS) { regexes.clear(); cmdRe.worlds = WORLDS; r = commandRegex(w.commands); regexes.set(w.id, r); } return r; };
cmdRe.worlds = undefined as readonly WorldInfo[] | undefined;

/** A λ-command: a command word, an optional step count, then a colon (`type: …`; `type := …` is a
 *  definition). The engine's `Lam.commandHead`. */
export function lambdaCommand(src: string): boolean {
  const lam = worldById("lambda");
  if (!lam) return false;
  return new RegExp(`^(${lam.commands.map(esc).join("|")})\\s*(\\d+\\s*)?:(?!=)`).test(src.trim());
}

/** The engine's `Lam.lex` succeeds: identifiers (Greek letters too), numerals, λ or backslash, `.`,
 *  parentheses, `:` and arrows. Each token is taken whole, as the lexer does. */
const LAMBDA_LEXES = /^(?:[ \t\r\n.():λ\\→]|->|[0-9]+(?![0-9])|[A-Za-z_\u0391-\u03A9\u03B1-\u03C9][A-Za-z0-9_'\u0391-\u03A9\u03B1-\u03C9]*(?![A-Za-z0-9_'\u0391-\u03A9\u03B1-\u03C9]))*$/;

/** A λ-cell without a λ (the engine's `Lam.isLambdaSource`): its first word is a λ-definition, the
 *  session's (`defs`) or the Church library's, it has no parenthesis or goes on after a space —
 *  `fst (pair a b)` — and it lexes as a λ-term (`S + 1` is arithmetic). */
export function lambdaHeaded(src: string, defs: (name: string) => boolean): boolean {
  const s = src.trim();
  const w = s.split(" ")[0] ?? "";
  const lam = worldById("lambda");
  if (w === "let" || !(lam?.names.includes(w) || defs(w))) return false;
  return (!s.includes("(") || s.includes(" ")) && LAMBDA_LEXES.test(s);
}

/** Does a source carry one of a world's markers: a glyph anywhere, or a word at its head? */
function marked(w: WorldInfo, src: string): boolean {
  const head = src.trim().split(/\s+/)[0] ?? "";
  const first = /^(?:let\s+\w+\s*=\s*)?(\w+)/.exec(src.trim())?.[1] ?? head;
  return w.markers.some((m) => (/^[A-Za-z_]+$/.test(m) ? first === m : src.includes(m)));
}

/** The world a source belongs to, by its id, or null for algebra: the engine's `worldFor`, as far as
 *  the page can tell before the engine answers. A λ-command is the λ-world's whatever else it holds;
 *  otherwise the worlds are asked in the engine's order, each by its commands and markers, the λ-world
 *  last and also by a known definition at the head (`defs`, the session's λ-names). */
export function worldOf(src: string, defs: (name: string) => boolean = () => false): string | null {
  const s = src.trim();
  if (!s) return null;
  if (lambdaCommand(s)) return "lambda";
  const hasLambda = /[λ\\]/.test(s);
  for (const w of others()) {
    if (w.id === "lambda") {
      if (hasLambda || /:=/.test(s) || lambdaHeaded(s, defs)) return "lambda";
      continue;
    }
    // a λ-term is not a logic cell, whatever glyphs it holds (the engine's isLogicSource says the same)
    if (w.id === "logic" && hasLambda) continue;
    if (cmdRe(w).test(s) || marked(w, s)) return w.id;
  }
  return null;
}

/** The other worlds' commands and predicates: names the typeset input and the highlighter make calls
 *  of when `(` follows (a λ-command is written `word:`, so the λ-world's are left out). */
export function worldFns(): string[] {
  return others().flatMap((w) => (w.id === "lambda" ? [] : [...w.commands, ...w.names]));
}

/** Every keyword of every world: the words the highlighter and the editor set apart. */
export function worldKeywords(): Set<string> {
  return new Set(WORLDS.flatMap((w) => w.keywords));
}

/** The keywords of the world a cell's source is in (a system's clauses, a quantifier's words), for the
 *  highlighter to mark; none for algebra and the λ-calculus. */
export function keywordsOf(src: string): Set<string> {
  const w = worldOf(src);
  return new Set(w && w !== "lambda" ? worldById(w)?.keywords ?? [] : []);
}
