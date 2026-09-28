// Bundles the demo page: `npm run demo -w packages/math-editor`, then open demo/index.html.
import { build } from "esbuild";
await build({
  entryPoints: [new URL("demo.ts", import.meta.url).pathname], bundle: true, format: "esm", outdir: new URL("dist", import.meta.url).pathname,
  loader: { ".woff2": "file", ".woff": "file", ".ttf": "file" }, logLevel: "info",
});
