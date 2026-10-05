# ChalkMath

The layout and design are in `ARCHITECTURE.md`; build and test commands are in `README.md`.

## Definition of done for a new feature

A feature (new syntax, a new rule or command, a new notebook capability) is not done until it has
all four of the following, in the same change:

1. **Documentation.** Update whatever the feature touches:
   - syntax: the grammar comment at the top of `engine/MathEngine/Parser.lean`;
   - anything a notebook user can type: its page in `apps/notebook/src/reference.ts` (usage,
     details, runnable examples, see-also), and the step label in the rule-name map in
     `apps/notebook/src/app.ts`;
   - a rewrite rule: its status and note in `ruleStatus` (`engine/MathEngine/Rpc.lean`) and the
     same row in `book/chapters/A-rule-table.tex`. Keep the status honest: `verified` only when a
     theorem (or a definition) backs it;
   - a design decision or a new kind of thing: `ARCHITECTURE.md`.
2. **Proofs, where relevant.** Every rule added to the notebook pipeline must have its termination
   obligation in `engine/MathEngine/PipelineOrder.lean`: a `dec_*` theorem, the rule in
   `mem_pipeline_iff`, and its case in `pipelineOrderedWith` (the `rcases` count changes too). A rule
   with a real or complex meaning gets a soundness theorem in `proofs/Proofs/` (Mathlib). Matrix
   rules go through `checkedLit`, which checks their outputs rather than proving them.
3. **Tests.** Engine behaviour goes in `engine/Tests/golden.tsv` (source, tab, printed answer or
   `<error: …>`), and parser or printer details in `engine/Tests/Main.lean`. New syntax also has to
   be mirrored in the visual editor's reader (`packages/math-editor/src/read.ts` copies
   `Parser.lean` rule for rule), with tests in `packages/math-editor/test/`.
4. **End-to-end tests.** A user-facing feature adds a case to `CASES` in `scripts/e2e-math.mjs`
   (`npm run e2e`, run in CI). It types the source into a math cell of the bundled notebook in
   Chromium, against the native engine over HTTP, and checks the engine's answer as text, that the
   page shows exactly that answer, and, given `step`, that the cell's work shows a step by that
   name. Errors are checked too (`error`). A notebook feature beyond a math cell's answer (a cell
   kind, an action, a tab) adds a check to `features()` in the same script, held to the engine's own
   answers through the test's reference client. Next to it:
   - `packages/math-editor/test/engine.test.mjs` sends every `golden.tsv` source and every bundled
     notebook cell through the editor's reader and writer and then to the native engine, checking
     that the text the editor writes back means what the source meant (no browser);
   - CI evaluates every cell of `notebooks/welcome.chalk` against the native engine, and holds every
     example notebook and course lesson to its golden outcomes in `notebooks/golden/`
     (`scripts/notebooks/drive.mjs --check`; `--update` after a deliberate change);
   - `lean-cells.yml` runs every notebook's and lesson's Lean through Lean in Chromium
     (`scripts/notebooks/check-lean-browser.mjs`): Lean that native Lean accepts can still run a browser
     thread out of stack, so run it on a change to a notebook's Lean;
   - `npm run smoke:lean` and `npm run smoke:ask` drive Lean cells and `?` lookups in Chromium. They
     are run by hand and are not in CI; run them when a change touches those.

Before pushing: `cd engine && lake build && lake test`, then `npm run build && npm test && npm run typecheck`,
then `npm run bundle && npm run e2e`.
If any of these could not be run, say so plainly rather than reporting the change as tested.
