# Architecture

Decisions that outlive any milestone. Milestone-specific plans live in `book/`.

## 1. The spine

One math engine, written in Lean 4, compiled to native (CLI, stdio server) and to wasm32
(web worker). Every host is a shim around one pure function `handle : String → String`
(`engine/MathEngine/Rpc.lean`). The frontend talks to *some* engine through
`packages/protocol` and never learns which one beyond `engine.capabilities`.

The TypeScript reference engine the Lean engine was ported from was deleted after M2 (last present
in commit 680e360). Its test suite lives on in `engine/Tests/Main.lean`
and its answers on a 147-source corpus in `engine/Tests/golden.tsv`, produced by a wire-level
differential test with zero mismatches.

## 2. Protocol rules

1. Everything crossing the boundary is plain JSON: `WireExpr`, `Rendered`, `Derivation`.
2. Transport is abstract (worker `postMessage`, HTTP, WebSocket, stdio). It moves JSON-RPC 2.0
   messages and does not know what they mean.
3. Expressions are trees with *paths* (child-index lists). Paths are the provenance key that lets
   the frontend map "the thing I selected" back to "the step that produced it".
4. The engine is stateful per session (a notebook), stateless across sessions.
5. New capabilities are added as optional fields, never by changing existing ones, so an old
   frontend keeps working against a new engine and vice versa.

## 3. The engine

- `Expr` is deliberately small (`num var add mul pow fn matrix`). Subtraction, division and
  negation are derived forms; the printer recovers the notation. Operators with no node of their
  own are calls: MATLAB's entrywise `A ./ B` and `A .* B` parse to `ediv(A, B)` and `emul(A, B)`
  (`la.ediv`, `la.emul`), so `/` and `*` keep their matrix meaning, `A·B⁻¹` and the product. Fewer node kinds means fewer
  rewrite rules and fewer proof cases.
- **Numbers.** `Q` wraps core Lean's `Rat` (normalized by construction) plus a presentation-only
  "approximate" flag. Mathlib's `ℚ` *is* that `Rat`, so the identification is `rfl`
  (`proofs/Proofs/Q.lean`). There is nothing to prove about the arithmetic; what must be proven is
  how the engine uses it, which is the per-rule soundness theorems.
- **Show work is not reconstructed after the fact.** Rewriting records every rule firing as a
  `Step` with the whole term before and after and the path where it fired. The derivation *is*
  the computation, viewed as data.
- **Work costs what is read.** Every step carries the whole term before and after it, so the
  derivation of a big term is quadratic in it: 200 steps on a 100-row table were 10 MB of reply.
  Two things keep it in proportion without capping it. A run of rewrites inside one matrix's entries
  is one step, `la.entrywise`, whose nested steps carry the entry alone (`buildSteps`), so an
  entrywise computation is linear in the matrix and reads as a textbook writes it, `2A` then the
  arithmetic of each entry. And the notebook asks for a derivation's *outline* (each step's rule,
  explanation and path, and whether it prints the same before and after) and fetches the terms
  with `engine.steps` when a cell's work is opened; the session already keeps every cell's
  derivation, for `explain`, so nothing is computed twice and nothing is left out.
- **Termination is a proof obligation, not a budget.** A rule bundles a proof that it strictly
  decreases a measure; `normalize` is well-founded on that measure and never `partial`. The
  verified `simplify` uses one additive measure (`Rewrite.lean`). The whole notebook pipeline —
  commands, `diff.*`, `la.*`, `simp.*`, the two parity rules, the radical rules — uses the six-tier ordering of
  `Order.lean` and the innermost rewriter `normalizeT` (`Terminate.lean`), whose obligation is
  conditional: a rule must decrease the ordering *on a node whose children are already normal*.
  That hypothesis is what lets the product rule duplicate its body. The theorem is
  `pipelineOrdered` (`PipelineOrder.lean`), one lemma per rule. Rules that delegate to unverified
  code (commands, matrix arithmetic) have their outputs *checked* for the tier they must decrease
  rather than proved. There is no step budget anywhere: `expand` distributes by a total function
  (`Expand.dist`, proved sound over ℝ in `proofs/Proofs/Expand.lean`) and the pipeline collects
  the result.
- **Elimination is verified over ℚ by construction.** `LinAlgQ.lean` writes Gauss–Jordan as a
  list of the three elementary row operations, each invertible (the degenerate parameters are the
  identity), and proves `sol_rref`: the reduced matrix has the input's solution set. The `rref`
  command replays those operations into its steps when every entry is a numeral; symbolic entries
  fall back to the simplifier-driven algorithm, whose steps are named `la.row-*.symbolic` and
  reported unverified. That the result is in reduced row echelon form is `rref_isRref`
  (`LinAlgRref.lean`), a column-by-column invariant.
- **Radicals take the form the ordering can afford.** `2√2` as a term is `2 · 2^(1/2)`, heavier
  than `8^(1/2)` under any bounded numeral weight, so the engine's normal form is the single power
  `2^(3/2)` (a sixth tier, the magnitudes of integer numerals, orders that step), radicals with the
  same square-free part collect in sums and same-index radicals multiply in products (both decrease
  `M`), and the printer displays the single-power form the textbook way. `√a = a^(1/2)` is a
  silent rule where the two print alike and a visible `simp.radical` step where they do not
  (`√18` shows as `3√2`); the arithmetic the textbook writes out (`√32 = (2^5)^(1/2) = 2^2 · 2^(1/2)`)
  lives in the explanations, since those intermediate forms are heavier than the input and could
  not be steps. `RadicalRules.lean`.
- **The λ-calculus is a second world in the same engine.** `Lambda.lean` has its own terms, parser
  and normal-order β-reducer; terms are encoded into `Expr` for the wire, so selection, explanation
  and origin tracking work unchanged. The de Bruijn view is computed with every step. Reduction is
  on fuel, the one budget in the engine, because normalization is undecidable; `Ω` is refused.
- **Finite order theory is a third world.** `Poset.lean` decides everything over lists — closure,
  the partial-order check, covers, bounds, join and meet, lattices, monotone maps, fixed points by
  the Kleene chain — and `PosetProofs.lean` proves the decisions mean the textbook Props. Values
  are encoded into `Expr`; the notebook draws Hasse diagrams from the covers.
- **Plots are sampled by the engine and drawn by the notebook.** `engine.plot` simplifies the
  function under the session, records the cell, and returns a uniform sample with `null` where the
  value is not finite; the notebook's SVG and the studio's graph shot are presentation only.
- **Integration is checked, not found.** `Antiderivative.lean` guesses an antiderivative with a
  few textbook rules and proves nothing; `cmdIntegrate` differentiates the guess with the pipeline
  and accepts it only if the normal form is the integrand itself. `cmdIntegrate_spec` states that;
  `proofs/Proofs/Integrate.lean` reads it as `deriv F = f` wherever the differentiation shown is
  sound, which the statuses of its steps report. Because a rule set cannot contain a rule that
  normalizes with that set, the pipeline is `pipelineRulesWith norm`, generic in the checker's
  normalizer, and `Integrate.lean` closes the knot: the checker is the pipeline with nested
  `integrate` refused, and the notebook's pipeline is the pipeline with that checker.
- **An exercise is checked by normal forms.** `engine.check` (`Exercise.lean`) evaluates a question
  like any cell (its value is the expected answer, its derivation the worked solution) and reduces the
  reader's answer too; the two are equivalent when their canonical forms are equal — the integration
  check's `identNorm` and `dist`, normalized — as two λ-terms are β-equivalent when they reduce to the
  same normal form (λ answers are compared by their de Bruijn terms). "Not equivalent" is "not shown
  equivalent". An answer that calls the question's own commands (`diff` for a `diff` question) is
  refused, and a check is not an evaluation: no `In[n]`, no binding, `%` untouched.
- **Soundness is a fold, over whichever semantics you bring.** `RewriteSound.normalize_sound_for`
  is stated for an abstract `Congruence` (reflexive, transitive, a congruence under `withChildren`,
  invariant under `canon`). Supply those four facts for a new semantics and normalization's
  soundness follows without touching the rewriter. The integer fragment and ℝ are two instances.
- **Semantics are added in layers, never edited.** `eval?` (integer fragment, M1) ⊂ `evalR` (ℝ, M3) ⊂ `evalD` (ℝ with
  derivatives, M4), each with a theorem that the previous one is a restriction of it. A new layer extends rather than
  replaces because the earlier theorems are stated against the earlier semantics; widening in place would silently
  restate them. It is also forced here: `evalR` cannot interpret `diff`, whose second child is a binder that `Expr`
  does not distinguish from a value, and a semantics reading it breaks the congruence M3's fold needs.
- **A rule that needs a side condition says so.** Over ℝ, `simp.collect-powers` and part of
  `simp.function` are only sound away from `0` (see `book/TRACKING.md`, M3). The engine keeps the
  usual computer-algebra behaviour; `proofs/` states the hypothesis and *proves* that no
  unconditional theorem exists. Silence is not an option: either a rule has an unconditional
  theorem or its condition is written down.
- **Two packages.** `engine/` is executable code and goes into the wasm build: it imports Init
  (Std/Batteries allowed) and never Mathlib. `proofs/` is theorems only, may be `noncomputable`,
  requires `engine/` and (from M3) Mathlib. `scripts/check-engine-deps.sh` enforces the split.

## 4. Adding a math area (group theory, category theory, ...)

The rewriter, derivations, paths and the protocol are module-agnostic: they work on any tree
with `children`/`withChildren`. What a module brings is:

| Concern | Where it plugs in |
|---|---|
| Syntax (literals like a cycle `(1 2 3)`, new commands) | parser extension + reserved `fn` names |
| Node kinds | today: `fn name args` with a module-reserved name; when a second module lands, `Expr` gains typed node kinds per module rather than growing the closed inductive ad hoc |
| Rules with explanations | a `RuleSet` with its own measure and obligations |
| Semantics and proofs | a module in `proofs/` (the engine computes; `proofs/` interprets) |
| Rendering | printer cases (text/LaTeX) plus *visual specs* (§5) |

Explanations are Markdown with `$latex$`, carried on every step. A module that cannot explain a
rule in one sentence has the rule at the wrong granularity.

## 4a. The notebook shell

`apps/notebook` implements the second export of the "Notebook - GitHub" artboard, checked in under
`design/v2/` (the first export, and the Cloud9 palette the shell briefly used, remain under
`design/`). Two palettes — warm dark and paper light — are token sets on `html[data-theme]` in
`index.html`; the toggle in the title bar persists the choice in `localStorage`. The cells sit on a
"paper" whose grain and mottle are inline SVG turbulence filters, and are set in Literata; the
chrome around them stays in the system sans. Re-skinning is a change to the token blocks.

The page owns no mathematics. It does not parse, print, or simplify: every expression on screen is
LaTeX the engine produced, every rule name and explanation is the engine's, and the proof status
beside each step comes from `engine.capabilities.ruleStatus` rather than a list in the frontend
that could drift from `proofs/`. The one thing the page derives from source text is a cell's *kind*
label, which is presentation only.

The visual math input (`packages/math-editor`) is the one exception to "does not parse", and it
reads notation, not meaning. A cell's source text stays what is saved and what the engine is sent.
The editor reads that text into a tree of notation (fractions, powers, calls, matrices) by the
engine's own grammar, shows it, and writes it back to text when the reader edits. What the text
means is still the engine's parse of it. The reader has to agree with `Parser.lean` exactly, or the
input would show a fraction where the engine reads a product, and its tests hold it to that: every
golden source and notebook cell is round-tripped and, against the native engine, has to mean the
same thing before and after.

**Manim Studio** is the third tab. "→ Scene" on an evaluated cell turns its derivation into shots:
the statement, then each step's `afterRendered` term (an optional field on `Step`, per protocol
rule 5). The page adds what a storyboard needs and nothing more — order, on/off, an animation name,
a duration — previews a shot by matching KaTeX glyphs between consecutive terms (longest common
subsequence, then interpolated position and opacity, a browser-side stand-in for
`TransformMatchingTex`), and prints the Python a Manim user would run. Rendering the video is
Manim's job, outside the browser.

**Courses** (File › Courses and examples) opens a tab beside the studio that lists *projects*:
notebooks that belong together, either a course (lessons read in order) or a collection. They are
`notebooks/courses.json` and `notebooks/courses/<course>/*.chalk`, generated by
`scripts/notebooks/mk-courses.mjs` and served under `examples/`. A lesson opens in its own tab with its
place in the project (`project` in the file), a bar with the previous and next lessons, and its
exercises answered, which the page remembers per lesson in local storage. The lessons are built from
what the shell offers for teaching: exercise cells (checked by `engine.check`, §3), steps held back
to be revealed one at a time, sliders on `let n = number` that re-run the cells out of date because of
them, and Markdown callouts. Every lesson's answers are pinned in `notebooks/golden/` and checked in CI.

**Help › Documentation** opens a tab beside the studio: a guide to the notebook (cells, input,
reading the work, files, lookups and their set-up, Lean cells, the studio) and the reference pages.
The pages are Markdown in `src/docs.ts`, drawn by the Markdown cells' renderer; their tables (the
symbols and templates, the shortcuts, the example notebooks) are built from the lists the notebook
itself uses. Every function has a page of its own, laid out as Mathematica's are — usage lines,
details, examples in sections, related functions — from `src/reference.ts`, which is also where
completion, signature help and the sidebar's command list read their entries. A page holds only the
examples' inputs: the engine evaluates each section in a session of its own when the page is shown,
so the outputs are this engine's and cannot go stale (a section that reads a file or asks a question
is shown as inputs, with *Open in a notebook*).

## 4b. Lean cells

A Lean cell is Lean 4 itself, checked as you type, in the browser: the VS Code editor with the Lean 4
extension (lean4monaco, pinned) as its input, what Lean reports on its lines as its output, and the
infoview — goals at the cursor — in the panel's Lean goals tab. It is the one part of the notebook that
does not go through the engine's protocol: the engine answers `engine.*` for math cells, Lean's own
language server answers LSP for Lean cells.

- **Lean compiled to wasm32.** `scripts/build-lean-wasm-compiler.sh` (`npm run lean-wasm`) builds the whole
  compiler — parser, elaborator, kernel, IR interpreter, language server — from the C the host `lean` emits
  for the tagged sources, linked statically with Emscripten. Lean's IR interpreter finds compiled code by
  name; a static link has no dynamic symbol table, so a generated table (name hash → address,
  `scripts/lean-wasm-symtab.py`) stands in for `dlsym`. An `.olean` is a memory image with pointer-sized
  fields, so the library is compiled again, by the wasm `lean` under Node, into 32-bit oleans
  (`scripts/lean-wasm-oleans.py`; Init today). The patches to Lean's sources are in
  `engine/wasm/lean-compiler-emscripten.patch`, the upstream findings in `engine/wasm/UPSTREAM.md`.
- **The server in a web worker.** `engine/wasm/server/LeanWorker.lean` runs Lean's file worker with
  stdin/stdout over a shared-memory queue (`leanweb.c`); `packages/engine-host/src/lean-server.ts` plays
  Lean's watchdog for one document (answers `initialize` with the reply Lean's own watchdog gives, printed
  at build time; drops the cross-file index traffic). The server is threaded: it reads LSP while
  elaboration runs in tasks. So the page must be cross-origin isolated, which a static host gets from
  `coi-sw.js`, a service worker registered the first time a notebook has a Lean cell (one reload). In a
  browser each thread is a worker and one started beyond the pre-created pool is not ready in time, so
  the pool is large (32) and Lean's own pool is capped (4).
- **One document per notebook.** The notebook's Lean cells, in order, are the stretches of one Lean file
  between separator comment lines; each cell's editor is a Monaco view of that one model that hides every
  other line (`packages/lean-editor`). Definitions carry from cell to cell, editing a cell re-elaborates
  it and the cells after it, and every position the extension and the infoview use is real — nothing is
  translated between cells and file.
- **Cost.** Nothing loads until a notebook has a Lean cell. Then, compressed: the editor (~3 MB), the
  server (~24 MB) and Init's 32-bit oleans (~114 MB: their private parts, proofs included, are most of it,
  and an ordinary file's implicit `import Init` needs them), once per browser: the worker keeps the large
  files in Cache Storage under an id of their contents (a browser's HTTP cache will not hold entries that
  size, and the files' URLs change with every deploy), so they are downloaded again only when Lean changes. The site gets Lean from a
  release `lean-wasm.yml` publishes whenever Lean's build inputs change (`scripts/lean-wasm-key.sh` names it),
  so a deploy does not spend two hours building it.

## 4c. Lookups (`?` cells)

A math cell that starts with `?` is a question — `?volume of a cone`, `?the first ten primes`,
`let mlb = ?MLB runs and home runs per game for the last 20 years` — answered by a language model
running on the reader's machine, as *source text* the engine then evaluates like any other cell: a
number, a list `[a, b, c]`, a matrix, or a formula (`B*h`; `let V = ?…` defines `V(B, h)`). So the
page still owns no mathematics: the answer is engine input, parsed and normalized by the engine, and
everything after it keeps its steps. The pipeline is `packages/ask`; the notebook's side (models,
settings, the cell) is `apps/notebook/src/ask-cells.ts`.

- **The model plans first.** It says what shape the answer has, names its parts, writes searches,
  names the subject, and says whether the answer is standard knowledge. Standard knowledge of
  mathematics or physical science (a formula, a constant) it answers itself, and nothing leaves the
  machine; the answer is labelled "from the model's knowledge" and the cell offers *Check with a
  search*. A question about the world (teams, people, places, events) is always searched for: a small
  model is sure of far more such facts than it gets right. Where the question's words fix the
  shape ("how many", "the number of", "formula"), they decide it, not the model.
- **The model answers from what was found, in the question's shape.** It is given the stretches of
  the pages read most likely to hold the answer: paragraphs ranked by the question's words they share
  (a page's opening paragraphs, which sum it up, a little ahead) and tables ranked by caption, column
  names and best row, as much as the model's context takes (about 7,000 characters for a 4k-token
  browser model, 30,000 for a cloud one). A table too big for that keeps the rows with the question's
  own words, or its first rows and its last. Held to a JSON schema, the model answers with the
  numbers (or the formula), its sources and a quote; or a model that can search the web itself
  (OpenRouter's web search) does, and its citations are the sources.
- **What the model says is checked, not trusted.** Every number it gives is looked for in what it
  read (a number written in words counts) and flagged ⚠ when it is not there. A formula is read from
  the LaTeX it quotes by code (`tex.ts`), never from the model's translation, and flagged when the
  pages do not write it that way. A question that asks to make something (a random matrix) is no
  lookup and is refused before any search. The model's memory is the last resort, and an answer
  from it is flagged throughout.
- **Why not have the model pick and code copy.** An earlier version showed a small model previews of
  the tables found and had it choose a table, columns and a row range while code copied the cells,
  to keep it from inventing numbers. It chose the wrong table as often as a model misreads a page
  (asked how many World Series the Tigers have won, it counted a table of their best seasons), and
  it read the prose last, though the article's opening said "four". Reading what was found and
  checking the numbers works better with every model tried.
- **Sources are generic, not per subject.** Wikipedia (no key, and it allows other origins) and, if
  the reader sets one, a SearXNG-style endpoint that queries Google, DuckDuckGo, Bing and Brave.
  Most sites refuse cross-origin reads, so a web result is read directly when it allows that and
  otherwise through a page reader the reader configures (`scripts/ask-proxy/worker.js` is one).
  Google's Custom Search API closes on 2027-01-01 and DuckDuckGo has no results API, so neither is
  built in.
- **Models.** Chrome's built-in model (the Prompt API) where the browser has it; elsewhere a WebGPU
  model through WebLLM, bundled separately (`dist/ask/`) and loaded only when a lookup needs it, its
  weights downloaded once from Hugging Face; or, chosen in the settings, a model Ollama serves on
  the reader's own computer (`/api/chat`, held to the schema by its `format`), which can be larger
  than a browser holds; or a cloud model through OpenRouter on the reader's own account (signed in
  with OpenRouter's OAuth PKCE flow from a window that returns to `openrouter-callback.html`, the
  key kept in the browser). Settings has a *Test the model* button that times one small question.
- **What is sent.** With a model on the reader's computer, only a search sends anything: the search
  terms the model wrote, to the sources. With OpenRouter, the question and what was found go to
  OpenRouter and the model's provider. Never the notebook. The first search asks first.
- **Saved with the cell.** The answer, its shape, where it came from and how it was found are saved
  in the `.chalk` file, so running the notebook again evaluates the saved answer without asking
  again; *Look up again* asks afresh.

## 5. Visuals

The engine never draws. It emits **visual specs**: declarative JSON next to `rendered`
(`EvaluateResult.visuals`, reserved in the protocol, empty until a module uses it): a Cayley
table, a graph, a commutative diagram, sampled plot data, a matrix heat map. The frontend owns
rendering (SVG/canvas/WebGL) and can offer several renderers for one spec. This keeps the engine
pure and portable (wasm has no canvas), keeps proofs about what is *shown* possible (the spec is
data the engine can reason about), and lets exports (§6) reuse the same specs.

## 6. Export

Text and LaTeX come from the engine (`Rendered`). Everything else is a consumer of the wire data,
implemented outside the engine:

- images: render LaTeX (KaTeX/MathJax) or a visual spec to SVG/PNG in the frontend or a headless host;
- manim / animation: a generator from `Derivation` JSON, using each step's whole-term `before`/`after`
  and `path` to animate the rewrite. This is why derivations stay complete and why origin tracking
  (`Origin.lean`, M6) matters beyond `explain`: morphing a subterm needs to know it is "the same"
  subterm. `explain` traces a position backwards through the steps — its own origin outside a
  redex (a theorem), the equal subterms of the redex inside the contractum, or *created* — and
  reports one relation per step (`created` / `copied` / `contains`).

Export formats are added as packages under `packages/` (e.g. `packages/export-manim`); the engine
does not change.

## 7. Toolchain

Lean is pinned in `engine/lean-toolchain` and `proofs/lean-toolchain` (kept equal). Policy: the
latest stable Lean for which a **Mathlib release tag** exists, bumped manually, with
`proofs/lakefile.toml`'s Mathlib `rev` bumped in the same commit. Pin to the tag, not to `master`:
Mathlib master tracks release candidates (it was on `v4.34.0-rc2` while stable was `v4.33.1`), and
the tag `vX.Y.Z` is exactly the Mathlib that targets `leanprover/lean4:vX.Y.Z`.

Mathlib lives only in `proofs/`. `lake exe cache get` there fetches prebuilt oleans (~5 GB;
building from source takes hours). The wasm runtime is built from source for the pinned tag
(`scripts/build-lean-wasm-runtime.sh`, results in `book/SPIKE-RESULTS.md`), cached under
`engine/toolchains/<tag>` and keyed by tag.
