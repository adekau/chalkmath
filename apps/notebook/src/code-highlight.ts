/**
 * Syntax highlighting for a Markdown cell's fenced code: ```ts, ```lean, ```python, ```json, and
 * ```chalk for ChalkMath itself (the notebook registers the math cells' own highlighter for it).
 *
 * A language is a list of rules tried in order where the last token ended; the first that matches
 * gives the next token and its class. The result is text and classes, never HTML: the Markdown
 * renderer builds the spans itself. The classes are the math cells' (`hkw`, `hnum`, `hstr`, …), so
 * code blocks take the same colours, plus `hcom` for comments and `htype` for types. A language not
 * listed here gives `null`, and its block stays plain text.
 */

/** A token of a code block: its text and its class (`""` for plain text). */
export interface CodeTok { cls: string; text: string }
export type Highlighter = (src: string) => CodeTok[];

/** A rule: a pattern (matched at the current position), and the class of what it matches — or, for
 *  a word, a function of the word and the text after it. */
type Rule = [RegExp, string | ((word: string, rest: string) => string)];

const words = (s: string) => new Set(s.split(/\s+/).filter(Boolean));

/** Highlight with `rules`; text no rule matches is plain, one character at a time. */
function lexer(rules: Rule[]): Highlighter {
  const sticky = rules.map(([re, cls]): Rule => [new RegExp(re.source, `${re.flags.replace(/[gy]/g, "")}y`), cls]);
  return (src) => {
    const out: CodeTok[] = [];
    const push = (cls: string, text: string) => {
      const last = out[out.length - 1];
      if (last && last.cls === cls) last.text += text; else out.push({ cls, text });
    };
    for (let i = 0; i < src.length;) {
      let hit = false;
      for (const [re, cls] of sticky) {
        re.lastIndex = i;
        const m = re.exec(src);
        if (!m || !m[0]) continue;
        push(typeof cls === "string" ? cls : cls(m[0], src.slice(i + m[0].length)), m[0]);
        i += m[0].length; hit = true; break;
      }
      if (!hit) push("", src[i++]!);
    }
    return out;
  };
}

/** A word's class from the language's word lists; a word before `(` is a call, a capitalised one a type. */
function wordClass(kw: Set<string>, consts: Set<string>, types: Set<string>) {
  return (w: string, rest: string) =>
    kw.has(w) ? "hkw" : consts.has(w) ? "hconst" : types.has(w) || /^[A-Z]/.test(w) ? "htype" : /^\s*\(/.test(rest) ? "hfn" : "";
}

const NUM = /0[xX][\da-fA-F_]+|0[bB][01_]+|(?:\d[\d_]*\.?[\d_]*|\.\d[\d_]*)(?:[eE][+-]?\d+)?n?/;
const PUN = /[()[\]{};,.]/;
const OP = /[-+*/%=<>!&|^~?:@]+/;

const TS = lexer([
  [/\/\/[^\n]*/, "hcom"],
  [/\/\*[\s\S]*?(?:\*\/|$)/, "hcom"],
  [/"(?:[^"\\\n]|\\.)*"?|'(?:[^'\\\n]|\\.)*'?|`(?:[^`\\]|\\[\s\S])*`?/, "hstr"],
  [NUM, "hnum"],
  [/[A-Za-z_$][\w$]*/, wordClass(
    words(`abstract as async await break case catch class const continue debugger declare default delete do else enum export
      extends finally for from function get if implements import in infer instanceof interface is keyof let namespace new of
      private protected public readonly return satisfies set static super switch this throw try type typeof var void while with yield`),
    words("true false null undefined NaN Infinity"),
    words("string number boolean bigint symbol object unknown any never"))],
  [PUN, "hpun"],
  [OP, "hop"],
]);

const PYTHON = lexer([
  [/#[^\n]*/, "hcom"],
  [/[rRbBfFuU]{0,2}(?:"""[\s\S]*?(?:"""|$)|'''[\s\S]*?(?:'''|$)|"(?:[^"\\\n]|\\.)*"?|'(?:[^'\\\n]|\\.)*'?)/, "hstr"],
  [NUM, "hnum"],
  [/@[A-Za-z_][\w.]*/, "hcmd"],
  [/[A-Za-z_]\w*/, wordClass(
    words(`and as assert async await break class continue def del elif else except finally for from global if import in is
      lambda match case nonlocal not or pass raise return try while with yield`),
    words("True False None self"),
    words("int float complex str bool list dict set tuple bytes object type"))],
  [PUN, "hpun"],
  [OP, "hop"],
]);

/** Lean 4: commands and term keywords, tactics after `by`, `--` and `/- … -/` comments, Unicode notation. */
const LEAN_KW = words(`def theorem lemma example abbrev instance structure class inductive where deriving namespace section end
  open variable universe import noncomputable partial private protected mutual axiom set_option attribute macro syntax
  notation infix infixl infixr prefix postfix let have show from fun λ match with if then else do return by at calc
  termination_by decreasing_by Type Sort Prop`);
const LEAN_TACTICS = words(`intro intros exact apply refine rfl simp simp_all rw rewrite omega decide cases rcases obtain induction
  constructor left right exists use contradiction exfalso assumption trivial unfold norm_num linarith ring field_simp
  specialize subst split by_cases by_contra push_neg aesop sorry admit next case all_goals any_goals repeat first try
  funext ext congr symm calc show change generalize revert clear injection nofun nomatch`);
const LEAN = lexer([
  [/--[^\n]*/, "hcom"],
  [/\/-[\s\S]*?(?:-\/|$)/, "hcom"],
  [/"(?:[^"\\\n]|\\.)*"?|'(?:[^'\\\n]|\\.)'/, "hstr"],
  [/\d+(?:\.\d+)?/, "hnum"],
  [/[A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w'!?.Ͱ-Ͽ₀-ₜ]*/, (w) =>
    LEAN_KW.has(w) ? "hkw" : LEAN_TACTICS.has(w) ? "hcmd" : w === "True" || w === "False" || w === "true" || w === "false" ? "hconst" : /^[A-Z]/.test(w) ? "htype" : ""],
  [/[()[\]{}⟨⟩,]/, "hpun"],
  [/[-+*/%=<>!&|^~:;@·∘→←↔∀∃¬∧∨≤≥≠∈∉⊆×]+/u, "hop"],
]);

const JSON_ = lexer([
  [/"(?:[^"\\\n]|\\.)*"?(?=\s*:)/, "hdef"],
  [/"(?:[^"\\\n]|\\.)*"?/, "hstr"],
  [/-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/, "hnum"],
  [/true|false|null/, "hconst"],
  [/[[\]{}:,]/, "hpun"],
]);

const LANGS = new Map<string, Highlighter>();
/** Name a highlighter for one or more fence languages (`ts`, `typescript`, …); case is ignored. */
export function registerLanguage(names: string[], hl: Highlighter) { for (const n of names) LANGS.set(n.toLowerCase(), hl); }
registerLanguage(["ts", "typescript", "tsx", "js", "javascript", "jsx", "mjs"], TS);
registerLanguage(["py", "python"], PYTHON);
registerLanguage(["lean", "lean4"], LEAN);
registerLanguage(["json"], JSON_);

/** The languages a fence can name, for the documentation. */
export const languages = (): string[] => [...LANGS.keys()];

/** The tokens of `src` in the fence's language `lang`, or `null` when it has no highlighter. */
export function highlightCode(lang: string, src: string): CodeTok[] | null {
  const hl = LANGS.get(lang.toLowerCase());
  return hl ? hl(src) : null;
}
