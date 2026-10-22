/**
 * Whether a Lean proof, as the reader wrote it, leaves something unproved: a `sorry` or an `admit`
 * in its code. What is commented out (`-- sorry`, `/- sorry -/`, nested block comments too) or
 * quoted (`"sorry"`) is not code, so it does not count.
 */
export function leavesSorry(proof: string): boolean {
  return /\b(sorry|admit)\b/.test(leanCode(proof));
}

/** Lean's ways out of proving something: an axiom asserted, code trusted without a proof
 *  (`native_decide`, `implemented_by`, `extern`), or `unsafe` code. A definition exercise refuses
 *  them in the reader's definition and proof alike. */
const ESCAPES = ["axiom", "native_decide", "implemented_by", "extern", "unsafe"];
export function escapesIn(src: string): string[] {
  const code = leanCode(src);
  return ESCAPES.filter((w) => new RegExp(`(^|[^\\w.])${w}(?![\\w])`).test(code));
}

/** What a definition uses that its exercise rules out (`forbid`): a name (`Nat.mul`, `mul`, matched
 *  as a whole name or the last part of one, so `mul` finds `Nat.mul`) or a symbol (`*`), in its code
 *  (comments and strings aside). A check of the definition's form, not a proof of it: it catches the
 *  shortcut written down, not every way round it. */
export function forbiddenIn(src: string, forbid: string[]): string[] {
  const code = leanCode(src);
  const esc = (t: string) => t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return forbid.filter((t) => /^[\w.']+$/.test(t)
    ? new RegExp(`(^|[^\\w'])${esc(t)}(?![\\w'])`).test(code)
    : code.includes(t));
}

/** A Lean source with its comments and string literals blanked out, the rest as it was. */
export function leanCode(src: string): string {
  let out = "", i = 0, depth = 0;
  while (i < src.length) {
    const two = src.slice(i, i + 2);
    if (depth > 0) {
      if (two === "/-") { depth++; i += 2; }
      else if (two === "-/") { depth--; i += 2; }
      else { if (src[i] === "\n") out += "\n"; i++; }
      if (depth === 0) out += " ";
    } else if (two === "/-") { depth = 1; i += 2; }
    else if (two === "--") { while (i < src.length && src[i] !== "\n") i++; }
    else if (src[i] === '"') {
      i++;
      while (i < src.length && src[i] !== '"') i += src[i] === "\\" ? 2 : 1;
      i++; out += " ";
    } else { out += src[i]; i++; }
  }
  return out;
}
