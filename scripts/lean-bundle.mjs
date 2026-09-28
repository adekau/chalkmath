// Bundles Lean cells into apps/notebook/dist/lean/ (called by bundle.mjs):
//   lean-editor.js          packages/lean-editor: lean4monaco (the VS Code editor and the Lean 4 extension),
//                           loaded by the notebook only when a notebook has Lean cells
//   workers/*.js            the editor's two workers (Monaco's, TextMate's), bundled on their own
//   assets/, infoview/      files the bundle reaches by URL, and the infoview's own files
//   lean-server.worker.js   Lean's language server host (packages/engine-host/src/worker-lean-server.ts)
//   lean-server.{js,wasm}, lean-lib.pack.gz, lean-initialize.json
//                           Lean itself, from scripts/build-lean-wasm-compiler.sh, when that build exists
// lean4monaco documents a Vite setup; the three things it needs from a bundler are done here for esbuild:
// Node polyfills (with `fs` an in-memory filesystem), `new URL('<file>', import.meta.url)` assets, and
// the workers.
import { build } from "esbuild";
import { nodeModulesPolyfillPlugin } from "esbuild-plugins-node-modules-polyfill";
import { createHash } from "node:crypto";
import { cpSync, existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";
import path from "node:path";

const require = createRequire(import.meta.url);
const WORKERS = {
  "monaco-editor/esm/vs/editor/editor.worker.js": "editor.worker.js",
  "@codingame/monaco-vscode-textmate-service-override/worker": "textmate.worker.js",
};
// The infoview's iframe is written with document.write, so it resolves URLs against the page: its
// root-absolute `/infoview/` paths become the page-relative directory the files are copied to.
const INFOVIEW = "./lean/infoview/";

export async function bundleLean({ out, define, minify }) {
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
  writeFileSync(`${out}/infoview/webview.js`,
    readFileSync(require.resolve("lean4monaco/dist/webview/webview.js"), "utf8").replaceAll('"/infoview/', `"${INFOVIEW}`));

  await build({ ...common, format: "iife", entryPoints: ["packages/engine-host/src/worker-lean-server.ts"], outfile: `${out}/lean-server.worker.js` });
  const ver = readFileSync("engine/lean-toolchain", "utf8").trim().replace(/.*:v/, "");
  const lean = `engine/toolchains/lean-${ver}-wasm32/compiler`;
  const files = ["lean-server.js", "lean-server.wasm", "lean-lib.pack.gz", "lean-initialize.json"];
  if (files.every((f) => existsSync(`${lean}/${f}`))) for (const f of files) cpSync(`${lean}/${f}`, `${out}/${f}`);
  else console.log(`lean: no build of Lean itself in ${lean} (scripts/build-lean-wasm-compiler.sh); Lean cells will say so`);
  console.log(`lean: ${readdirSync(out).join(" ")}`);
}
