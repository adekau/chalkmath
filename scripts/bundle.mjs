// Bundles the Lean/wasm worker glue and the notebook page into apps/notebook/dist (static, self-hostable).
import { build } from "esbuild";
import { bundleLean } from "./lean-bundle.mjs";
import { cpSync, mkdirSync, readFileSync, writeFileSync } from "node:fs";
// A build stamp on every asset URL, so a browser never keeps yesterday's engine.
const BUILD = Date.now().toString(36);
const define = { __BUILD_ID__: JSON.stringify(BUILD) };
mkdirSync("apps/notebook/dist", { recursive: true });
// minified, with a linked source map so an error a reader reports still has file and line
const out = { bundle: true, target: "es2022", logLevel: "info", define, minify: true, sourcemap: "linked" };
await build({ ...out, entryPoints: ["apps/notebook/src/app.ts"], format: "esm", outfile: "apps/notebook/dist/app.js" });
// KaTeX's stylesheet and the fonts, served from the page's own origin (apps/notebook/src/fonts.css)
await build({ entryPoints: ["apps/notebook/src/fonts.css"], bundle: true, minify: true, outfile: "apps/notebook/dist/style.css", logLevel: "info",
  loader: { ".woff2": "file", ".woff": "file", ".ttf": "file" }, assetNames: "fonts/[name]-[hash]" });
cpSync("apps/notebook/assets", "apps/notebook/dist", { recursive: true });   // logo.svg and any other static asset
cpSync("notebooks", "apps/notebook/dist/examples", { recursive: true });       // File › Examples, and the welcome notebook
// the licenses of everything the page ships (the fonts' OFL requires its text to travel with them)
mkdirSync("apps/notebook/dist/licenses", { recursive: true });
for (const [from, to] of [
  ["LICENSE", "ChalkMath-LICENSE.txt"], ["NOTICE", "NOTICE.txt"], ["TRADEMARKS.md", "TRADEMARKS.md"],
  ["node_modules/katex/LICENSE", "KaTeX-LICENSE.txt"],
  ["node_modules/@fontsource/inter/LICENSE", "Inter-OFL.txt"],
  ["node_modules/@fontsource-variable/literata/LICENSE", "Literata-OFL.txt"],
  ["node_modules/@fontsource/jetbrains-mono/LICENSE", "JetBrainsMono-OFL.txt"],
]) cpSync(from, `apps/notebook/dist/licenses/${to}`);
writeFileSync("apps/notebook/dist/index.html", readFileSync("apps/notebook/index.html", "utf8").replace(/src="app\.js"/, `src="app.js?v=${BUILD}"`).replace(/href="style\.css"/, `href="style.css?v=${BUILD}"`));
console.log("→ serve apps/notebook/dist with any static server (e.g. `npx serve apps/notebook/dist`)");
await build({ ...out, entryPoints: ["packages/engine-host/src/worker-lean.ts"], format: "iife", outfile: "apps/notebook/dist/engine-lean.worker.js" });
// Lean cells: the editor, the infoview and Lean's language server (scripts/lean-bundle.mjs)
await bundleLean({ out: "apps/notebook/dist/lean", define, minify: true });
