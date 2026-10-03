// What a course's later lessons need of an earlier lesson's Lean. A course's prelude is elaborated each
// time one of its lessons opens, in the browser's wasm Lean, so it leaves out the commands that only
// show something: they cannot be referred to, and they cost (an `#eval` compiles and runs its term).
// Shared by the notebook (apps/notebook/src/app.ts) and the CI check (scripts/notebooks/check-lean.mjs),
// so that CI checks the prelude the page gives.

/** Top-level commands that only show something. */
const SHOW_ONLY = /^(#eval|#print|#check|#reduce|#guard_msgs|#guard|example)\b/;

/** The block-comment depth after a line, from the depth before it. Strings are skipped; a `--` ends
 *  the line's code. */
function depthAfter(line, depth) {
  for (let i = 0; i < line.length; i++) {
    if (depth === 0 && line[i] === '"') {
      for (i++; i < line.length && line[i] !== '"'; i++) if (line[i] === "\\") i++;
      continue;
    }
    if (depth === 0 && line.startsWith("--", i)) break;
    if (line.startsWith("/-", i)) { depth++; i++; continue; }
    if (depth > 0 && line.startsWith("-/", i)) { depth--; i++; }
  }
  return depth;
}

/**
 * The Lean `src` without its show-only commands (`#eval`, `#print`, `#check`, `#reduce`, `#guard`,
 * `#guard_msgs`, `example`), each with the doc comment in front of it and a `set_option … in` before
 * it. A command is the lines from one that starts at column 0, outside a block comment, to the next.
 * @param {string} src
 * @returns {string}
 */
export function leanForPrelude(src) {
  /** @type {string[][]} */
  const chunks = [];
  let depth = 0;
  for (const line of src.split("\n")) {
    if (!chunks.length || (depth === 0 && line !== "" && !/^\s/.test(line))) chunks.push([line]);
    else chunks[chunks.length - 1].push(line);
    depth = depthAfter(line, depth);
  }
  const drop = chunks.map((c) => SHOW_ONLY.test(c[0]));
  for (let k = chunks.length - 1; k > 0; k--) {
    const prev = chunks[k - 1][0];
    if (drop[k] && (prev.startsWith("/--") || /^set_option\b.*\bin\s*$/.test(prev))) drop[k - 1] = true;
  }
  return chunks.filter((_, k) => !drop[k]).map((c) => c.join("\n")).join("\n");
}
