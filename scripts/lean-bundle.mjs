// Bundles Lean cells into apps/notebook/dist/lean/ (called by bundle.mjs):
//   lean-editor.js          packages/lean-editor: lean4monaco (the VS Code editor and the Lean 4 extension),
//                           loaded by the notebook only when a notebook has Lean cells
//   workers/*.js            the editor's two workers (Monaco's, TextMate's), bundled on their own
//   assets/, infoview/      files the bundle reaches by URL, and the infoview's own files
//   lean-server.worker.js   Lean's language server host (packages/engine-host/src/worker-lean-server.ts)
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
  let parts = 0, download = 0;
  for (const f of readdirSync(out)) if (/^lean-(server\.wasm|lib\.pack)/.test(f)) rmSync(`${out}/${f}`);
  if (lean) {
    for (const f of ["lean-server.js", "lean-initialize.json"]) cpSync(`${lean}/${f}`, `${out}/${f}`);
    const wasm = gzipSync(readFileSync(`${lean}/lean-server.wasm`), { level: 9 });
    writeFileSync(`${out}/lean-server.wasm.gz`, wasm);
    const lib = readFileSync(`${lean}/lean-lib.pack.gz`);
    download = wasm.length + lib.length;
    for (let at = 0; at < lib.length; at += PART) writeFileSync(`${out}/lean-lib.pack.gz.${parts++}`, lib.subarray(at, at + PART));
  } else console.log("lean: Lean itself has not been built (npm run lean-wasm); Lean cells will say so");
  await build({ ...common, format: "iife", entryPoints: ["packages/engine-host/src/worker-lean-server.ts"], outfile: `${out}/lean-server.worker.js`,
    define: { ...common.define, __LEAN_LIB_PARTS__: String(parts), __LEAN_DOWNLOAD_BYTES__: String(download) } });
  console.log(`lean: ${readdirSync(out).join(" ")}`);
}
