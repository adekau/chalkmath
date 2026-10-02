# ChalkMath

The layout and design are in `ARCHITECTURE.md`; build and test commands are in `README.md`.

## Definition of done for a new feature

A feature (new syntax, a new rule or command, a new notebook capability) is not done until it has
all four of the following, in the same change:

1. **Documentation.** Update whatever the feature touches:
   - syntax: the grammar comment at the top of `engine/MathEngine/Parser.lean`;
   - anything a notebook user can type: the `DOCS` reference list in `apps/notebook/src/app.ts`
     (signature, blurb, runnable examples), and the step label in the rule-name map there;
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
4. **End-to-end tests.** What exists today:
   - `packages/math-editor/test/engine.test.mjs` sends every `golden.tsv` source and every bundled
     notebook cell through the editor's reader and writer and then to the native engine over stdio.
     It checks that the text the editor writes back means what the source meant. A new golden line
     is covered by it automatically.
   - CI evaluates every cell of `notebooks/welcome.chalk` against the native engine
     (`scripts/notebooks/drive.mjs`).
   - The browser smoke tests, `npm run smoke:lean` and `npm run smoke:ask`, use Playwright and
     Chromium against the bundled notebook. They are run by hand and are not in CI.

   There is no browser end-to-end test of a math cell yet. Until there is, a feature's end-to-end
   coverage is its golden lines (run through `engine.test.mjs`), plus a manual browser check when
   the change touches the notebook UI. Say which of these you did.

Before pushing: `cd engine && lake build && lake test`, then `npm run build && npm test && npm run typecheck`.
If any of these could not be run, say so plainly rather than reporting the change as tested.
