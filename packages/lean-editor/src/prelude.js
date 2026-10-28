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

/** `src` as its commands: a command is the lines from one that starts at column 0, outside a block comment,
 *  to the next. @param {string} src @returns {string[][]} */
function commands(src) {
  /** @type {string[][]} */
  const chunks = [];
  let depth = 0;
  for (const line of src.split("\n")) {
    if (!chunks.length || (depth === 0 && line !== "" && !/^\s/.test(line))) chunks.push([line]);
    else chunks[chunks.length - 1].push(line);
    depth = depthAfter(line, depth);
  }
  return chunks;
}

/**
 * The Lean `src` without its show-only commands (`#eval`, `#print`, `#check`, `#reduce`, `#guard`,
 * `#guard_msgs`, `example`), each with the doc comment in front of it and a `set_option … in` before
 * it. A command is the lines from one that starts at column 0, outside a block comment, to the next.
 * @param {string} src
 * @returns {string}
 */
export function leanForPrelude(src) {
  const chunks = commands(src);
  const drop = chunks.map((c) => SHOW_ONLY.test(c[0]));
  for (let k = chunks.length - 1; k > 0; k--) {
    const prev = chunks[k - 1][0];
    if (drop[k] && (prev.startsWith("/--") || /^set_option\b.*\bin\s*$/.test(prev))) drop[k - 1] = true;
  }
  return chunks.filter((_, k) => !drop[k]).map((c) => c.join("\n")).join("\n");
}

/** A notebook's Lean as the page puts it in its Lean file, in order: its Lean cells, and its Lean exercises,
 *  each the statement and a proof (`proof`: the author's, else `start`; a definition exercise, the author's
 *  definition before them).
 * @param {{ type: string; src: string; lean?: boolean; leanSolution?: string; leanDefSolution?: string }[]} cells
 * @returns {string[]} */
export function authorLean(cells, start = "  sorry") {
  return cells.flatMap((c) => c.type === "lean" ? [c.src]
    : c.type === "exercise" && c.lean && c.src.trim() ? [`${c.leanDefSolution ? `${c.leanDefSolution}\n\n` : ""}${c.src}\n${c.leanSolution ?? start}`] : []);
}

/** What a lesson adds to its course's prelude: its Lean (`authorLean`) without the commands that only show
 *  something, under a comment with its title; null when it has no Lean.
 * @param {string} title @param {Parameters<typeof authorLean>[0]} cells @returns {string | null} */
export function preludePart(title, cells) {
  const lean = authorLean(cells);
  return lean.length ? `-- ${title}\n${leanForPrelude(lean.join("\n\n"))}` : null;
}

/** A course's prelude for the lesson after `parts` (one per lesson, in order; null: no Lean). @param {(string | null)[]} parts */
export const preludeOf = (parts) => parts.filter((x) => x !== null).join("\n\n");

/** The commands of `src` that set the scope the commands after them are elaborated in: namespaces and
 *  sections and their `end`, `open`, `variable`, `universe`, `set_option` (not their `… in` forms, which
 *  belong to the one command after them). A module imported in place of `src` brings its declarations but
 *  not this, so it is replayed after the import. @param {string} src @returns {string} */
export function scopeOf(src) {
  return commands(src)
    .map((c) => c.join("\n").trimEnd())
    .filter((c) => /^(namespace|section|end|open|variable|universe|set_option|noncomputable section)\b/.test(c) && !/\bin$/.test(c))
    .join("\n");
}

/** A short hash of a string (cyrb53), to tell whether a prelude is the one a module was compiled from.
 * @param {string} s @returns {string} */
export function textHash(s) {
  let h1 = 0xdeadbeef, h2 = 0x41c6ce57;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    h1 = Math.imul(h1 ^ c, 2654435761); h2 = Math.imul(h2 ^ c, 1597334677);
  }
  h1 = Math.imul(h1 ^ (h1 >>> 16), 2246822507) ^ Math.imul(h2 ^ (h2 >>> 13), 3266489909);
  h2 = Math.imul(h2 ^ (h2 >>> 16), 2246822507) ^ Math.imul(h1 ^ (h1 >>> 13), 3266489909);
  return (4294967296 * (2097151 & h2) + (h1 >>> 0)).toString(16).padStart(14, "0");
}

/** The module holding a course's first `m` lessons' Lean: `ChalkCourse.<Course>.L<m>`.
 * @param {string} course @param {number} m @returns {string} */
export function moduleName(course, m) {
  const c = course.split(/[^A-Za-z0-9]/).filter(Boolean).map((w) => w[0].toUpperCase() + w.slice(1)).join("");
  return `ChalkCourse.${/^[A-Za-z]/.test(c) ? c : `C${c}`}.L${String(m).padStart(2, "0")}`;
}

/** Module `m` of a course: lesson `m`'s part, after an import of module `m - 1` and the scope the lessons
 *  before it leave (`scopeOf`). @param {string} course @param {(string | null)[]} parts @param {number} m */
export function moduleSource(course, parts, m) {
  const before = m > 1 ? `import ${moduleName(course, m - 1)}\n${scopeOf(preludeOf(parts.slice(0, m - 1)))}\n` : "";
  return `${before}${parts[m - 1] ?? ""}\n`;
}

/** What the page needs to know of module `m`: its name, the prelude it stands for (its length and hash), and
 *  the scope that prelude leaves. @param {string} course @param {(string | null)[]} parts @param {number} m */
export function moduleEntry(course, parts, m) {
  const text = preludeOf(parts.slice(0, m));
  return { name: moduleName(course, m), length: text.length, hash: textHash(text), scope: scopeOf(text) };
}

/** `prelude` with as much of it as module `entry` holds imported instead: the import, the scope replayed,
 *  then the rest of it as it is. Null when the prelude does not start with the module's text (it was saved
 *  from an older course, say). @param {{ name: string; length: number; hash: string; scope: string }} entry
 *  @param {string} prelude @returns {string | null} */
export function importedPrelude(entry, prelude) {
  const head = prelude.slice(0, entry.length), rest = prelude.slice(entry.length);
  if (textHash(head) !== entry.hash || (rest && entry.length && !rest.startsWith("\n\n"))) return null;
  const tail = entry.length ? rest.slice(2) : rest;
  return `import ${entry.name}\n${entry.scope}${tail ? `\n\n${tail}` : ""}`;
}
