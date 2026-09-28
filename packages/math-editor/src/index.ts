/**
 * @chalkmath/math-editor — the notebook's visual math input: a tree of notation read from a cell's
 * source text and written back to it. The source stays what is saved and sent; the engine's parse of
 * it is what runs.
 */
export * from "./model.js";
export { read, lex, ungroup, BUILTIN_FUNCTIONS, type ReadResult, type ReadError } from "./read.js";
export { write, writeText, atomsInSpan, type Written } from "./write.js";
export { toLatex, slots, outTag, outRefOf, type NotationOptions } from "./notation.js";
export { MathEdit, TEMPLATES, DEFAULT_SYMBOLS, type Caret, type Where } from "./edit.js";
