/**
 * Whether a Lean proof, as the reader wrote it, leaves something unproved: a `sorry` or an `admit`
 * in its code. What is commented out (`-- sorry`, `/- sorry -/`, nested block comments too) or
 * quoted (`"sorry"`) is not code, so it does not count.
 */
export function leavesSorry(proof: string): boolean {
  return /\b(sorry|admit)\b/.test(leanCode(proof));
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
