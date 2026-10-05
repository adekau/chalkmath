/**
 * Numbers as tables and prose write them, read into the decimal text the engine's parser takes
 * (`[0-9]*.?[0-9]+`, a leading `-`): `1,234` → `1234`, `−3.5` → `-3.5`, `12.5%` → `12.5`, `4.86[a]` → `4.86`.
 * A value that is not one number (`—`, `n/a`, `2–3`) is null: the lookup leaves that row out rather
 * than guess.
 */

const FOOTNOTE = /\[[^\]]{1,8}\]/g;
const MARKS = /[*†‡§¶#]+/g;
/** A space, thin space or apostrophe between digit groups of three: `1 234 567`, `1'234`. */
const GROUP = /(\d)[\s\u00a0\u2009\u202f'](?=\d{3}(?!\d))/g;

/** The text with footnotes and marks removed, digit-group spaces closed up, the minus signs made
 *  ASCII. Other spaces stay, so `4 5` is not read as 45; a superscript (`10^{6}`, as the page reader
 *  marks it) stays too, so it is not read as 106. */
function strip(s: string): string {
  return s.replace(FOOTNOTE, "").replace(MARKS, "").trim().replace(GROUP, "$1").replace(/^[−–—‒]\s*/, "-").replace(/^\+/, "");
}

/** Normalize `digits[.digits]` (commas as thousands separators already checked) to the engine's form. */
function canon(neg: boolean, int: string, frac: string | undefined): string {
  const i = int.replace(/,/g, "").replace(/^0+(?=\d)/, "") || "0";
  const f = frac ? frac.replace(/0+$/, "") : "";
  const body = f ? `${i}.${f}` : i;
  return neg && body !== "0" ? `-${body}` : body;
}

const STRICT = /^(-)?[$€£¥]?(\d{1,3}(?:,\d{3})+|\d+)?(?:\.(\d+))?(%|[kKmMbB]n?)?$/;

/** The one number a cell holds, or null. Currency signs and a trailing `%` are allowed (the column
 *  name says what the unit is); a magnitude suffix (`3.2M`) is not expanded and so is refused. */
export function parseNumber(s: string): string | null {
  const t = strip(s);
  const m = STRICT.exec(t);
  if (!m || (!m[2] && !m[3])) return null;
  if (m[4] && m[4] !== "%") return null;
  return canon(!!m[1], m[2] ?? "0", m[3]);
}

/** The number a cell starts with: for keys like a season `2005–06` or `1,234 (est.)`. */
export function leadingNumber(s: string): number | null {
  const m = /^(-)?(\d{1,3}(?:,\d{3})+|\d+)(?:\.(\d+))?/.exec(strip(s));
  return m ? Number(canon(!!m[1], m[2]!, m[3])) : null;
}

const WORDS: Record<string, number> = {
  zero: 0, one: 1, two: 2, three: 3, four: 4, five: 5, six: 6, seven: 7, eight: 8, nine: 9, ten: 10,
  eleven: 11, twelve: 12, thirteen: 13, fourteen: 14, fifteen: 15, sixteen: 16, seventeen: 17, eighteen: 18, nineteen: 19,
  twenty: 20, thirty: 30, forty: 40, fifty: 50, sixty: 60, seventy: 70, eighty: 80, ninety: 90,
  once: 1, twice: 2, thrice: 3, single: 1, double: 2, triple: 3,
};

/** Every number written in a stretch of prose, as numbers (for checking a quote says what was
 *  extracted): numerals, and the small ones prose spells out ("four titles", "twenty-one", "twice"). */
export function numbersIn(s: string): number[] {
  const out: number[] = [];
  for (const m of s.toLowerCase().matchAll(/\b([a-z]+)(?:-([a-z]+))?\b/g)) {
    const a = WORDS[m[1]!], b = m[2] ? WORDS[m[2]] : undefined;
    if (a === undefined) continue;
    out.push(b !== undefined && a >= 20 && a % 10 === 0 && b > 0 && b < 10 ? a + b : a);
  }
  const re = /[−–-]?\d{1,3}(?:,\d{3})+(?:\.\d+)?|[−–-]?\d*\.?\d+/g;
  // `1 234 567` (a thin space, or a space the page reader made of one) is one number, as `strip` reads it
  const t = s.replace(FOOTNOTE, "").replace(GROUP, "$1");
  for (let m = re.exec(t); m; m = re.exec(t)) {
    const n = Number(m[0].replace(/,/g, "").replace(/^[−–]/, "-"));
    if (Number.isFinite(n)) { out.push(n); if (n < 0) out.push(-n); }   // "2005-2024" reads as 2005 and -2024
  }
  return out;
}

/** A JSON number (from a model) as engine text, never in exponent notation. */
export function numberText(n: number): string | null {
  if (!Number.isFinite(n)) return null;
  if (Number.isInteger(n)) return BigInt(n).toString();
  const s = String(n);
  if (!/e/i.test(s)) return s;
  return n.toFixed(20).replace(/0+$/, "").replace(/\.$/, "");
}

/** Whether a cell mostly holds numbers. */
export const numeric = (s: string) => parseNumber(s) !== null;
