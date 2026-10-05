// Bundles the Lean/wasm worker glue and the notebook page into apps/notebook/dist (static, self-hostable).
import { build } from "esbuild";
import { bundleLean, leanBuild } from "./lean-bundle.mjs";
import { cpSync, existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { createHash, randomBytes } from "node:crypto";
import { execSync } from "node:child_process";
// The build: the commit it was made from, for the About box and error reports; outside CI, a working
// tree with changes not committed is a build of its own.
const git = (cmd) => { try { return execSync(`git ${cmd}`, { stdio: ["ignore", "pipe", "ignore"] }).toString().trim(); } catch { return ""; } };
const commit = (git("rev-parse HEAD") || process.env.GITHUB_SHA || "").slice(0, 7);
const BUILD = commit ? (!process.env.CI && git("status --porcelain") ? `${commit}+${Date.now().toString(36)}` : commit) : Date.now().toString(36);
// whether this copy includes Lean itself (the Lean cells' server), which a separate, long build makes
const define = { __BUILD_ID__: JSON.stringify(BUILD), __LEAN_BUILT__: JSON.stringify(!!leanBuild()) };
// Every file the page loads by URL carries `?v=` and a hash of its contents, so a browser fetches it
// again when it changed and keeps it across deploys that did not (the engine's wasm, the Lean editor):
// the files are built in the order they refer to each other, each hashed once it is written, and the
// hashes handed to the builds that load them as `__ASSET_VERSIONS__` (apps/notebook/src/version.ts).
const DIST = "apps/notebook/dist";
const versions = {};
const version = (file) => { if (existsSync(`${DIST}/${file}`)) versions[file] = createHash("sha256").update(readFileSync(`${DIST}/${file}`)).digest("base64url").slice(0, 10); };
const withVersions = () => ({ ...define, __ASSET_VERSIONS__: JSON.stringify(versions) });
// The one inline script the page allows: es-module-shims' feature detection in Lean's infoview, which
// marks its scripts with this nonce (scripts/lean-bundle.mjs). A new one each build.
const NONCE = randomBytes(18).toString("base64");
mkdirSync(DIST, { recursive: true });
// minified, with a linked source map so an error a reader reports still has file and line
const out = { bundle: true, target: "es2022", logLevel: "info", define, minify: true, sourcemap: "linked" };
// KaTeX's stylesheet and the fonts, served from the page's own origin (apps/notebook/src/fonts.css)
await build({ entryPoints: ["apps/notebook/src/fonts.css"], bundle: true, minify: true, outfile: `${DIST}/style.css`, logLevel: "info",
  loader: { ".woff2": "file", ".woff": "file", ".ttf": "file" }, assetNames: "fonts/[name]-[hash]" });
cpSync("apps/notebook/assets", DIST, { recursive: true });   // logo.svg and any other static asset
cpSync("notebooks", `${DIST}/examples`, { recursive: true, filter: (src) => !/[\\/]golden([\\/]|$)/.test(src) });   // the courses, the examples and the welcome notebook (the golden outcomes are CI's)
// the licenses of everything the page ships (the fonts' OFL requires its text to travel with them)
mkdirSync(`${DIST}/licenses`, { recursive: true });
for (const [from, to] of [
  ["LICENSE", "ChalkMath-LICENSE.txt"], ["NOTICE", "NOTICE.txt"], ["TRADEMARKS.md", "TRADEMARKS.md"],
  ["node_modules/katex/LICENSE", "KaTeX-LICENSE.txt"],
  ["node_modules/@mlc-ai/web-llm/LICENSE", "WebLLM-LICENSE.txt"],
  ["node_modules/@fontsource/inter/LICENSE", "Inter-OFL.txt"],
  ["node_modules/@fontsource-variable/literata/LICENSE", "Literata-OFL.txt"],
  ["node_modules/@fontsource/jetbrains-mono/LICENSE", "JetBrainsMono-OFL.txt"],
]) cpSync(from, `${DIST}/licenses/${to}`);
// the engine (scripts/build-wasm.sh, when it has been built), then the worker that loads it
for (const f of ["engine-lean.js", "engine-lean.wasm"]) version(f);
await build({ ...out, define: withVersions(), entryPoints: ["packages/engine-host/src/worker-lean.ts"], format: "iife", outfile: `${DIST}/engine-lean.worker.js` });
// `?` lookups' WebGPU model (WebLLM), loaded only when a lookup needs it and Chrome's built-in model is
// not there (apps/notebook/src/ask-cells.ts); the model itself runs in the worker
await build({ ...out, entryPoints: ["apps/notebook/src/webllm.ts"], format: "esm", outfile: `${DIST}/ask/webllm.js` });
await build({ ...out, entryPoints: ["apps/notebook/src/webllm-worker.ts"], format: "esm", outfile: `${DIST}/ask/webllm-worker.js` });
// Lean cells: the editor, the infoview and Lean's language server (scripts/lean-bundle.mjs)
await bundleLean({ out: `${DIST}/lean`, define, minify: true, nonce: NONCE });
// everything the page loads by URL, versioned, then the page
for (const f of ["engine-lean.worker.js", "ask/webllm.js", "ask/webllm-worker.js", "lean/lean-editor.js", "lean/lean-server.worker.js"]) version(f);
const files = (dir) => readdirSync(`${DIST}/${dir}`, { withFileTypes: true }).flatMap((e) => e.isDirectory() ? files(`${dir}/${e.name}`) : [`${dir}/${e.name}`]);
for (const f of files("examples")) version(f);
await build({ ...out, define: withVersions(), entryPoints: ["apps/notebook/src/app.ts"], format: "esm", outfile: `${DIST}/app.js` });
version("app.js"); version("style.css");
writeFileSync(`${DIST}/index.html`, readFileSync("apps/notebook/index.html", "utf8")
  .replace("script-src 'self'", `script-src 'self' 'nonce-${NONCE}'`).replace(/src="app\.js"/, `src="app.js?v=${versions["app.js"]}"`).replace(/href="style\.css"/, `href="style.css?v=${versions["style.css"]}"`));
console.log(`build ${BUILD}: ${Object.keys(versions).length} files versioned`);
console.log("→ serve apps/notebook/dist with any static server (e.g. `npx serve apps/notebook/dist`)");
