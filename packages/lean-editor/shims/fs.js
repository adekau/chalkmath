// `fs` for the Lean 4 extension in a browser: an in-memory filesystem (lean4monaco's setup overrides fs
// with memfs). Resolved in place of `fs` by scripts/lean-bundle.mjs.
import { fs } from "memfs";
export default fs;
export const promises = fs.promises;
export const constants = fs.constants;
export const { existsSync, readFileSync, writeFileSync, statSync, lstatSync, readdirSync, mkdirSync, realpathSync,
  createReadStream, createWriteStream, watch, access, stat, readFile, writeFile } = fs;
