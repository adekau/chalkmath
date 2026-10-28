// Bundles Lean cells into apps/notebook/dist/lean/ (called by bundle.mjs):
//   lean-editor.js          packages/lean-editor: lean4monaco (the VS Code editor and the Lean 4 extension),
//                           loaded by the notebook only when a notebook has Lean cells
//   workers/*.js            the editor's two workers (Monaco's, TextMate's), bundled on their own
//   assets/, infoview/      files the bundle reaches by URL, and the infoview's own files
//   lean-server.worker.js   Lean's language server host (packages/engine-host/src/worker-lean-server.ts)
//   lean-courses.json, courses/<course>-<hash>.pack.gz
//                           the courses' Lean preludes as modules (scripts/lean-courses.mjs), when the wasm
//                           Lean's command-line driver is there (LEAN_WASM_CLI_DIR)
//   lean-server.js, lean-server.wasm.gz, lean-lib.pack.gz.<n>, lean-initialize.json
//                           Lean itself, from scripts/build-lean-wasm-compiler.sh (or its release, fetched
//                           into LEAN_WASM_DIR), when that build exists. The wasm is shipped gzipped and
//                           the library in parts, so no file is over 64 MB and neither depends on the
//                           host compressing it; the worker decompresses both as they arrive.
// lean4monaco documents a Vite setup; the three things it needs from a bundler are done here for esbuild:
// Node polyfills (with `fs` an in-memory filesystem), `new URL('<file>', import.meta.url)` assets, and
// the workers.
import { build } from "esbuild";
import { nodeModulesPolyfillPlugin } from "esbuild-plugins-node-modules-polyfill";
import { createHash } from "node:crypto";
import { cpSync, existsSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import path from "node:path";
import { gzipSync } from "node:zlib";
import { buildCourseModules } from "./lean-courses.mjs";

const require = createRequire(import.meta.url);
const WORKERS = {
  "monaco-editor/esm/vs/editor/editor.worker.js": "editor.worker.js",
  "@codingame/monaco-vscode-textmate-service-override/worker": "textmate.worker.js",
};
// The infoview's iframe is written with document.write, so it resolves URLs against the page: its
// root-absolute `/infoview/` paths become the page-relative directory the files are copied to.
const INFOVIEW = "./lean/infoview/";

const LEAN_FILES = ["lean-server.js", "lean-server.wasm", "lean-lib.pack.gz", "lean-initialize.json"];
const PART = 64 << 20;
/** Where Lean itself is: LEAN_WASM_DIR (the release, unpacked), else where scripts/build-lean-wasm-compiler.sh
 *  put it; null when it has not been built. */
export function leanBuild() {
  const ver = readFileSync("engine/lean-toolchain", "utf8").trim().replace(/.*:v/, "");
  const dir = process.env.LEAN_WASM_DIR || `engine/toolchains/lean-${ver}-wasm32/compiler`;
  return LEAN_FILES.every((f) => existsSync(`${dir}/${f}`)) ? dir : null;
}

/** Where the wasm Lean's command-line driver and its 32-bit library are (bin/lean.js, lib/lean): LEAN_WASM_CLI_DIR
 *  (the release's lean-wasm-cli.tar.gz, unpacked), else where scripts/build-lean-wasm-compiler.sh put them. */
export function leanCompiler() {
  const ver = readFileSync("engine/lean-toolchain", "utf8").trim().replace(/.*:v/, "");
  const dir = process.env.LEAN_WASM_CLI_DIR || `engine/toolchains/lean-${ver}-wasm32/compiler`;
  return existsSync(`${dir}/bin/lean.js`) && existsSync(`${dir}/lib/lean/Init.olean`) ? path.resolve(dir) : null;
}

export async function bundleLean({ out, define, minify, nonce }) {
  mkdirSync(`${out}/assets`, { recursive: true });
  const importMetaUrl = {
    name: "import-meta-url",
    setup(b) {
      b.onLoad({ filter: /node_modules.*\.js$/ }, (args) => {
        let code = readFileSync(args.path, "utf8");
        if (!code.includes("import.meta.url") && !code.includes('"/infoview/')) return;
        code = code.replace(/\bnew\s+URL\s*\(\s*(['"`])([^'"`$]+)\1\s*,\s*import\.meta\.url\s*\)/g, (m, _q, spec) => {
          if (WORKERS[spec]) return `new URL("./workers/${WORKERS[spec]}", import.meta.url)`;
          let file;
          try { file = spec.startsWith(".") ? path.resolve(path.dirname(args.path), spec) : require.resolve(spec, { paths: [path.dirname(args.path)] }); }
          catch { return m; }
          const ext = path.extname(file);
          const name = `${path.basename(file, ext)}-${createHash("sha1").update(readFileSync(file)).digest("hex").slice(0, 8)}${ext}`;
          cpSync(file, `${out}/assets/${name}`);
          return `new URL("./assets/${name}", import.meta.url)`;
        });
        return { contents: code.replaceAll('"/infoview/', `"${INFOVIEW}`), loader: "js" };
      });
    },
  };
  const fsShim = { name: "fs-memfs", setup(b) {
    b.onResolve({ filter: /^(node:)?fs(\/promises)?$/ }, () => ({ path: path.resolve("packages/lean-editor/shims/fs.js") }));
  } };
  const common = { bundle: true, format: "esm", target: "es2022", logLevel: "warning", minify, legalComments: "linked",
    loader: { ".ttf": "file", ".woff": "file", ".woff2": "file", ".svg": "file", ".png": "file", ".wasm": "file" },
    define: { ...define, "process.env.NODE_ENV": '"production"' } };
  await build({ ...common, entryPoints: { "lean-editor": "packages/lean-editor/src/index.ts" }, outdir: out,
    assetNames: "assets/[name]-[hash]",
    plugins: [fsShim, importMetaUrl, nodeModulesPolyfillPlugin({ globals: { process: true, Buffer: true }, fallback: "empty" })] });
  for (const [spec, name] of Object.entries(WORKERS))
    await build({ ...common, entryPoints: [require.resolve(spec)], outfile: `${out}/workers/${name}` });
  mkdirSync(`${out}/infoview`, { recursive: true });
  cpSync(path.dirname(require.resolve("@leanprover/infoview/package.json")) + "/dist", `${out}/infoview`, { recursive: true });
  // es-module-shims (inside webview.js) detects the browser's module features with an inline script in a
  // hidden iframe, which a Content-Security-Policy without 'unsafe-inline' refuses (and the infoview then
  // never loads). It marks its inline scripts with esmsInitOptions.nonce: the build's nonce, which
  // bundle.mjs puts in the page's script-src. (Pinned lean4monaco 1.1.16; a version that sets the options
  // differently fails here rather than leaving a blank infoview.)
  const ESMS = "esmsInitOptions={shimMode:!0}";
  const webview = readFileSync(require.resolve("lean4monaco/dist/webview/webview.js"), "utf8");
  if (!webview.includes(ESMS)) throw new Error("lean-bundle: es-module-shims' options not found in webview.js");
  writeFileSync(`${out}/infoview/webview.js`,
    webview.replace(ESMS, `esmsInitOptions={shimMode:!0,nonce:${JSON.stringify(nonce)}}`).replaceAll('"/infoview/', `"${INFOVIEW}`));

  const lean = leanBuild();
  let parts = 0;
  /** What the worker loads, in order, with sizes, and an id of their contents: the worker keeps them in
   *  Cache Storage under that id, so a deploy that does not change Lean reuses what a browser has. */
  const files = { id: "", sizes: {} };
  for (const f of readdirSync(out)) if (/^lean-(server\.wasm|lib\.pack)/.test(f)) rmSync(`${out}/${f}`);
  if (lean) {
    cpSync(`${lean}/lean-initialize.json`, `${out}/lean-initialize.json`);
    // Lean's process ending, told to the host (lean-server.ts `leanExit`): the module is built to keep running
    // after `exit` (its threads serve the server), so Emscripten calls no `onExit`, and a server whose file
    // worker exited to be started again (its imports changed) would only stop answering
    const glue = readFileSync(`${lean}/lean-server.js`, "utf8");
    const EXIT = "function _proc_exit(code) {\n  if (ENVIRONMENT_IS_PTHREAD) return proxyToMainThread(0, 0, 1, code);\n";
    if (glue.split(EXIT).length !== 2) throw new Error("lean-bundle: Emscripten's _proc_exit not found in lean-server.js");
    writeFileSync(`${out}/lean-server.js`, glue.replace(EXIT, `${EXIT}  Module["leanExit"]?.(code);\n`));
    const wasm = gzipSync(readFileSync(`${lean}/lean-server.wasm`), { level: 9 });
    const lib = readFileSync(`${lean}/lean-lib.pack.gz`);
    const id = createHash("sha256");
    const add = (name, data) => { writeFileSync(`${out}/${name}`, data); files.sizes[name] = data.length; id.update(name).update(data); };
    add("lean-server.wasm.gz", wasm);
    for (let at = 0; at < lib.length; at += PART) add(`lean-lib.pack.gz.${parts++}`, lib.subarray(at, at + PART));
    files.id = id.digest("hex").slice(0, 16);
  } else console.log("lean: Lean itself has not been built (npm run lean-wasm); Lean cells will say so");
  // the courses' preludes as modules (scripts/lean-courses.mjs), compiled by the same Lean's command-line
  // driver: without it, or without Lean, a lesson elaborates its prelude inline, as before
  const compiler = leanCompiler();
  const courses = lean && compiler ? await buildCourseModules(compiler, out) : null;
  if (!courses) {
    rmSync(`${out}/courses`, { recursive: true, force: true });
    writeFileSync(`${out}/lean-courses.json`, "{}");
    if (lean) console.log("lean: no command-line Lean (LEAN_WASM_CLI_DIR: the release's lean-wasm-cli.tar.gz, unpacked); the courses' preludes stay inline");
  }
  await build({ ...common, format: "iife", entryPoints: ["packages/engine-host/src/worker-lean-server.ts"], outfile: `${out}/lean-server.worker.js`,
    define: { ...common.define, __LEAN_LIB_PARTS__: String(parts), __LEAN_FILES__: JSON.stringify(files) } });
  console.log(`lean: ${readdirSync(out).join(" ")}`);
}
