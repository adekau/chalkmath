# ChalkMath

A math notebook for learning, from linear algebra to Calc IV, that shows its work: every
answer comes with the steps that produced it, and any piece of a result can be clicked to see
which rule made it. It runs entirely in your browser; nothing you type is sent anywhere, except the
search terms of a `?` lookup that needs a search, and only once you allow it, or, if you choose a
cloud model through OpenRouter for lookups, the questions you ask it (ARCHITECTURE.md §4c).

This repository also holds *Show Your Work*, the zero-to-hero book written from building it.
One math engine in Lean 4, verified, compiled to native (server / CLI) and wasm (web worker).
The TypeScript reference engine it was ported from was deleted after M2; its answers live on in
`engine/Tests/golden.tsv`.

```
packages/protocol       JSON-RPC contract + Transport abstraction (the seam everything hangs on)
packages/engine-host    transports (worker / HTTP / WebSocket / stdio), HTTP host over the native engine, wasm worker glue
engine/                 Lean engine: syntax, semantics, verified rewriter + rules, JSON, RPC, C shim, tests + golden
proofs/                 separate Lake package, Mathlib only here: ℝ semantics and the rules' real soundness theorems
apps/notebook           the notebook: "Notebook - GitHub" structure with the "Notebook - Cloud9" palette
design/                 the Claude Design export the shell is built from (.dc.html artboards)
book/                   SPIKE-RESULTS.md (milestone 0, done), M1-BRIEF.md (current), TRACKING.md
scripts/                bundle.mjs (esbuild), build-wasm.sh (Lean → C → emcc), build-lean-wasm-runtime.sh (leanrt + Init for wasm32, from source)
packages/lean-editor    Lean cells: the VS Code editor + Lean 4 extension (lean4monaco) on Lean's own server, compiled to wasm
packages/ask            `?` lookups: a local model plans, searches Wikipedia or the web, and answers as engine source (number, list, matrix, formula)
```

`npm install && npm run build && npm test` — TS. `cd engine && lake build && lake test` — Lean (toolchain
pinned in `engine/lean-toolchain`, currently v4.34.1; policy: latest stable). `npm run wasm` —
builds the Lean runtime + Init for wasm32 from source on first run (~10 min, cached under
`engine/toolchains/`), then links `apps/notebook/dist/engine-lean.{js,wasm}`; see `book/SPIKE-RESULTS.md`.
Needs emsdk (`emcc`), elan, git.

`npm run lean-wasm` — Lean itself (compiler and language server) for wasm32, for Lean cells: ~1.5–2 h cold,
cached under `engine/toolchains/` (or unpack a `lean-wasm-*` release and set `LEAN_WASM_DIR` to it); `npm run bundle` then includes it, and `npm run smoke:lean` checks it in
Node and Chromium (set `CHROMIUM` to a browser executable if playwright-core's own is not installed). Without
it, Lean cells say the build has no Lean. See ARCHITECTURE.md §4b.

`node scripts/notebooks/drive.mjs --check notebooks/*.chalk` — every example notebook's cells against the
answers it was written with (`notebooks/golden/`, errors a notebook shows on purpose included); after an engine
change that alters one deliberately, `--update` rewrites them. CI runs it.

`npm run smoke:ask` — `?` lookups end to end in Chromium, against the native engine (`lake build`) and the
bundle, with a stand-in model and synthetic pages. See ARCHITECTURE.md §4c.

`cd proofs && lake exe cache get && lake build` — the theorems (Mathlib; the cache download is
~5 GB, and Mathlib never enters the engine — `npm run check:engine` enforces that).

## License

The code is open source under the [Apache License 2.0](LICENSE): use it, change it, host it, with
credit to ChalkMath ([NOTICE](NOTICE)). The name and logo are covered by the
[trademark policy](TRADEMARKS.md): host ChalkMath and call it ChalkMath, but give a modified version
its own name and say it is based on ChalkMath. The book in `book/` is licensed under
[Creative Commons Attribution 4.0](book/LICENSE).
