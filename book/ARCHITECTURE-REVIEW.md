# Architecture review, October 2026

A review of how the design in `ARCHITECTURE.md` has held up as the scope grew: the visual editor and
its read view, the typeset input cells, and the five worlds beside algebra. Every claim names the
file it was read from. The findings were written first; **what was done about them** is at the end.

## Verdict

The spine holds. One pure `handle : String → String`, JSON over an abstract transport, paths as the
provenance key, visual specs instead of drawing, text as a cell's one source: each of these has
absorbed the worlds, the scenes, Lean cells, lookups and the typeset input without bending. The
visual editor in particular is a clean package: a 190-line model, a reader that mirrors
`Parser.lean`, and a bijection test over every golden source and every notebook cell.

What has not kept pace is **registration**. A world, a visual kind or a saved field is known to the
system by being named in a dozen places across four packages, and the places agree today only
because someone copied carefully. The notebook's single file is where every concern meets. None of
this is a correctness problem now; all of it is the thing that makes the next world cost more than
the last one.

The findings below are in the order I would fix them. The first two are small and remove the live
drift risk; the rest are refactors that the golden outcomes already guard.

## 1. The worlds are a routing chain, not a module

`ARCHITECTURE.md` §4 says that "when a second module lands, `Expr` gains typed node kinds per
module". Five have landed (λ, order, logic, systems, and relations and algebra within order), and the
mechanism is still the one it describes as temporary:

- **Routing is an ordered chain of predicates**, written twice. `evaluateCore`
  (`engine/MathEngine/Rpc.lean:476`) tests `Sys.isSystemSource`, then `Ord.isOrderSource`, then
  `Logic.isLogicSource`, then `isLambdaCell`, with a λ-command exception in front because a
  `type:` command holds a connective. `checkAnswer` (`engine/MathEngine/Exercise.lean:316`) repeats
  the same chain, exception included. Each predicate is written a different way: order lexes
  (`Poset.lean:340`), logic splits on spaces and scans for glyphs (`Logic.lean:357`), systems takes
  an alphanumeric prefix (`Session.lean:1047`), λ scans for characters and counts `:=`
  (`Lambda.lean:495`). The order matters and nothing states why beyond the one comment.
- **Four result records and four reply builders.** `LamResult`, `OrdResult`, `LogicResult`,
  `SysResult` (`Session.lean`) each carry `name`, `value`, `derivation` and then their own extras;
  `evaluateLambda`, `evaluateOrder`, `evaluateLogic`, `evaluateSystem` (`Rpc.lean:316–430`) each
  assemble `ok`, `kind`, `value`, `rendered`, the visuals, `workFields` and `bound` by hand, in
  slightly different orders, and only two of them send `summary`.
- **The session has a binding list per world**: `env`, `fns`, `lambdas`, `posets`, `pmaps`, `rels`,
  `ops`, `ctxs`, `systems`, `trss`, `formulas` (`Session.lean:30–50`). A rebinding clears the name
  from the list it lands in and no other (every `filter (·.1 != n)` in the file is per list). So
  `let F = p ∧ q` followed by `let F = system(…)` leaves `F` in `formulas` as well, and a later
  `taut(F)` finds the old formula. I could not run the engine in this session to confirm the
  behaviour, but the code has no cross-list clearing.
- **Every world's values share one flat `fn` namespace** with user functions: `.fn "set"`,
  `.fn "pair"`, `.fn "rel"`, `.fn "poset"`, `.fn "λ"`, `.fn "@"`, `.fn "∧"`. There is no reserved
  list, so whether `let set(x) = …` collides is decided by whichever rule or printer case matches
  first. (Unverified for the same reason.)

**Proposal.** One `World` structure in the engine and a list of them:

```lean
structure World where
  id        : String                       -- "lambda", "order", "logic", "system"
  commands  : List String                  -- the heads that claim a cell
  keywords  : List String                  -- `when`, `do`, `init`, … (for the editor)
  glyphs    : List String                  -- `∧`, `→`, `:=`, … (for the editor and the notebook)
  claims    : Session → String → Bool
  evaluate  : Session → String → String → Session × Except Err WorldResult
  check     : Session → String → String → Option String → Session × Except Err CheckResult
  unbind    : Session → String → Session   -- forget a name in this world
```

with one `WorldResult` (`value`, `derivation`, `bound?`, `summary?`, `visuals : List Visual`,
`extras : Json`) and one reply builder. `evaluateCore` becomes `worlds.find? (·.claims s src)`;
the λ-first rule becomes the list's order, in one place. A binding calls every world's `unbind`
before it binds. None of this touches a proof: the proofs are about each world's functions, which
stay as they are. The golden corpus and `notebooks/golden/` guard the refactor.

The encoding question (typed node kinds versus `fn` with reserved names) can wait; what cannot is
a reserved-name check at `let`, which is a one-line parser change once the `World` list exists to
read the names from.

## 2. The notebook re-derives world membership by regex

`apps/notebook/src/app.ts:132–166` hand-copies the engine's lists: `ORDER_CELL`, `LOGIC_CELL`
and `SYSTEM_CELL` copy `Ord.commands`, `Logic.commands` and `Sys.commands`; `LAMBDA_CMD` copies
`Lam.commandWords`; `CHURCH` copies `Lam.churchDefs`; `LAMBDA_LEXES` is a regex transcription of
`Lam.lex`. I diffed the three command lists against the engine's: they match today. Nothing checks
that they do, and the engine's `capabilities` reply (`Rpc.lean:236`) publishes only a flat
`features` array, so the notebook has no way to ask.

The copies are then used three more times:

- `WORLD_FNS` (`app.ts:4030`) is built by regex-parsing the *source of the regex*, to tell the
  typeset input which names make calls;
- `cellKind` (`app.ts:168`) labels cells with a third vocabulary ("order", "λ-term") beside the
  engine's reply kinds ("poset", "lambda") and the exercise verdict wording picks a "world" from
  the same regexes (`app.ts:5770`);
- the editor carries its own copies: `KEYWORDS`, `MULTI_OPS`, `INFIX`, `BODY_CALLS`, `isConst`
  (`packages/math-editor/src/model.ts`). A sixth world that adds a keyword (`where`, say) silently
  makes `where` a variable in a product in the typeset input, with no test failing.

**Proposal.** Publish the lexicon from the engine as an optional capability (protocol rule 5):

```ts
capabilities.worlds?: { id: string; label: string; commands: string[]; keywords: string[]; glyphs: string[] }[]
```

The notebook keeps its regexes as the fallback for an older engine, and one test asserts they equal
what the native engine publishes (the editor's `engine.test.mjs` already has the plumbing). The
editor takes the lexicon through `MathInputOptions`, as it already takes `known`. The three
vocabularies for a cell's kind collapse to the engine's `id` plus a label from the same record.

## 3. Visual kinds are a closed union in four places

Six kinds exist. Each is named in the protocol's `KnownVisual` union, the notebook's `knownVisuals`
validator (`app.ts:3585`), the `visualBox` renderer switch (`app.ts:3763`), and, for the two that
place steps, `cellVisuals` and `markSteps` (`app.ts:3732–3760`): nineteen mentions in `app.ts`.
Beside them are three things that are drawn but are not visuals: `hasse` (a field of `WorldExtras`,
drawn by `hasseSvg` in the cell and again in the reference pages at `app.ts:6857`, cleared in two
places), `plot` and `manip`. §5 of `ARCHITECTURE.md` lists the six and not `hasse`.

**Proposal.** A registry in the notebook, one entry per kind:

```ts
const VISUALS: Record<string, { check(data: unknown): boolean; render(data): HTMLElement;
                                mark?(box, data, trail, cur, held): void }>
```

`knownVisuals`, `visualBox` and the step marking read it; "ignores a kind it does not know" holds
by construction. Fold `hasse` into `visuals` as `order.hasse` (the engine sends both for one
release; rule 5 again) and drop the field. `plot` and `manip` have their own replies and can stay.

## 4. The notebook's one file is where every concern meets

`apps/notebook/src/app.ts` is 8,408 lines and 349 top-level functions; it grew by 550 lines over the
last 60 commits and was touched by 8 of the last 30. The costs that scale with it:

- **`Cell` is a flat record of some sixty optional fields** across eight concerns (`app.ts:240–358`):
  result, work, world extras, plot, manipulate, scene, file, lookup, Lean, exercise, slider, visual
  input, read view. Everything a reply gives is a sibling of everything the reader did, so
  `clearResult` (`app.ts:2785`) is a hand-kept list of what to delete, and the comment on it says
  why it exists: fields used to survive some paths and not others.
- **The file format is an inline type**: `ChalkFile.cells` is one line of 30 optional fields
  (`app.ts:1306`), read back by a hand-written loader that checks each field by hand
  (`cellsFromFile`, `app.ts:1415`), and written by a hand-written serializer (`app.ts:1345`). A new
  saved field is three edits that must agree, and nothing but a reader's file tells you when they
  do not.
- The helper modules show the pattern that works: `scene.ts`, `files.ts`, `ask-cells.ts`,
  `lean-cells.ts`, `term-spans.ts` each own one concern with an explicit interface, and the section
  headers already in `app.ts` (the visual input, the read view, files, projects, docs, the studio,
  exercises) are the seams.

**Proposal**, in three independent steps:

1. `cell.result` holds everything a reply put there (`outLatex`, `outText`, `echoLatex`, `steps`,
   `outline`, `error`, `visuals`, `summary`, world extras, `warnings`); `clearResult` becomes one
   `delete`. The save and load code move with it.
2. A named `CellRecord` type and a table-driven loader: one row per field with its validator, so the
   loader, the serializer and the type are generated from one list. The field-by-field checking that
   makes a damaged record an empty cell stays; it just stops being written by hand.
3. Split `app.ts` along its own section headers as those sections are next touched, starting with the
   typeset input and read view (lines 4022–5030, about a thousand lines with a clear boundary:
   `Cell`, `S`, `refreshInput`, `runCell`). No big-bang move.

## 5. The visual editor is sound; its world knowledge is the one thing to watch

What is right: the model carries notation and never meaning; every text reads; `write(read(s)) = s`
is tested on the whole corpus; written-afresh text is sent to the native engine and checked to mean
the same. Templates, arity and the drawn notations are math-only tables in the editor
(`edit.ts:38`, `notation.ts`) and need nothing from the worlds.

Three small duplications to fold:

- `BINDERS` is defined identically in `packages/math-editor/src/notation.ts:29` and
  `apps/notebook/src/app.ts:7927`; `DRAWN` in `term-spans.ts:37` is a hand list of the calls
  `notation.ts` draws as notation. Export both from the editor.
- `BUILTIN_FUNCTIONS` and `POWER_FNS` in `read.ts` copy `Parser.lean`'s lists. These are held by the
  engine test, so they are safe; they would be safer as part of the published lexicon in §2.
- The world lexicon in `model.ts`, covered in §2.

The `loose` mode of the reader (any operator the math grammar lacks switches the whole cell to
"math between separators", `read.ts:186`) is the right generalization and will take a sixth world
unchanged, provided its keywords and operators arrive through the lexicon rather than the table.

## 6. The read view is a prototype on the wrong side of the wire

`term-spans.ts` says so in its header: the engine tags each subterm of `inputRendered` with its
path but not with where it was written, so the page re-lexes the source and matches the reading's
leaves to the source's tokens in path order. The approximations are listed there (a leaf the parser
made up matches nothing; a reading is `faithful` only when every written name and number appears in
it, so a `system` cell gets no subterm toolbar), and the exact answer is named: the parser records
each node's span.

`Expr` has no slot for a span and should not get one (the proofs are about `Expr`). The parser can
return a side table instead, `List (Path × Nat × Nat)`, built while it builds the term, and
`engine.evaluate` can send it as an optional `inputSpans` next to `inputRendered`. Then `faithful`
means "the engine sent spans", the toolbar works for every world whose parser records them, and the
180 lines of matching heuristics go. This is the one change in this review that adds to the
protocol; it is additive.

## 7. Tests

The engine's corpus covers the worlds well: of 516 golden sources, 26 are λ, 56 are logic, and
systems, replicas, rewriting and relations each have a handful (`engine/Tests/golden.tsv`). The
course golden outcomes (`notebooks/golden/`) carry the rest. The editor's read-write and engine
tests run over every notebook cell, worlds included.

The thin end is the browser. Of about seventy end-to-end cases (`scripts/e2e-math.mjs`), seven are
other-world cells, and none checks that a visual was drawn: a truth table, a state graph with its
step marks, a spacetime diagram, a typing tree. These exist only in the page, so only the e2e run
can see them. One `features()` check per visual kind (the box is present, has the rows or nodes the
engine sent, and the step mark moves when a step is clicked) is the missing coverage, and would be
the test that guards §3.

## 8. Documents

- `ARCHITECTURE.md` §4's table describes worlds as a future; §3 describes five that exist. Rewrite
  §4 as what a world is (the `World` record of §1) and what it must bring, and list the places a
  world touches until the code makes it one place: engine (`World` entry, `ruleStatus`), protocol
  (`capabilities.worlds`), notebook (reference `Area` and pages, step labels), editor (nothing, once
  §2 lands), tests (golden block, e2e case, a `features()` check per visual).
- §5 says six visual kinds exist; `hasse` is a seventh in all but name. Fix with §3.
- `CLAUDE.md`'s definition of done covers a rule and a syntax; add a world and a visual kind as two
  more kinds of thing, with the lists above. That is the cheapest generalization available: write the
  touch points down until there are fewer of them.

## Not urgent, noted

- `scripts/notebooks/mk-courses.mjs` is 6,700 lines of JavaScript that builds the lessons; the
  `.chalk` files are generated. It works, and `drive.mjs --check` holds every cell to its outcome.
  The limit it sets is that a lesson cannot be edited in the notebook and round-tripped back. When
  that is wanted, the lessons become the source and the script becomes a linter.
- `apps/notebook/index.html` carries about 800 lines of CSS and is the second most-touched file; a
  stylesheet of its own would make the diffs legible, nothing more.

## Suggested order

| Step | Finding | Size | What it removes |
|---|---|---|---|
| 1 | §2 publish the world lexicon; assert the copies equal it | small | live drift risk in notebook and editor |
| 2 | §3 visual registry; fold `hasse` | small | four-place edits per kind |
| 3 | §1 `World` record; one reply builder; `unbind` | medium, no proof changes | the routing chain, written twice; the stale-binding case |
| 4 | §4.1–4.2 `cell.result`; `CellRecord` with a table loader | medium | hand-kept clear/save/load lists |
| 5 | §6 `inputSpans` from the parser | medium | the read view's heuristics; worlds without a toolbar |
| 6 | §4.3 split `app.ts` at its seams | as sections are touched | the one-file integration point |

## What was done

Acted on in the same branch, in the review's order:

1. **§2, done.** `engine.capabilities.worlds` publishes each world's id, label, commands, keywords,
   glyphs, names and markers (`World.lean`, `worldsJson`). The notebook's `worlds.ts` is generated from
   the engine's output and held equal to it by `apps/notebook/test/worlds.test.mjs`; the regexes in
   `app.ts` are gone, and `cellKind`, the typeset input's call names, the highlighter and the exercise
   verdict read `worlds.ts`. The editor adds the engine's keywords and operators to its own
   (`configureLexicon`); `lexicon.test.mjs` holds its lists equal to the engine's, and found the
   editor's `weak` keyword had no engine behind it. The reference test's hand copy went too.
2. **§3, done.** `VISUALS` in `apps/notebook/src/visuals.ts` is the one registry (check, render,
   `replacesValue`, `placed`, `held`, `mark`). The Hasse diagram is the `order.hasse` visual, drawn
   through the registry and standing in for the value as before; the `hasse` field stays on the wire
   for one release and `Cell.hasse` is gone. `features()` in the e2e script checks it and the context
   table, so every kind is now checked in the browser.
3. **§1, done.** `World.lean`: the five records, `worldFor`, one `worldReply`, `evaluateIn`;
   `checkAnswer` routes the same way. `Session.unbind` clears a name from every world when another
   world rebinds it; a world rebinding its own name still sees the old value. A function may not take
   a command's or a wire value's name (`reservedFnNames`); a value may (`let reach = …` is in a
   lesson). `engine/Tests/Main.lean` has `worldTests` for each of these. No proof changed.
4. **§4.2, done; §4.1 not.** `CellRecord` is a named type and `CELL_FIELDS` one table of rows (load
   with its check, save), driving `cellsFromFile` and `cellToRecord`; the exercise helpers folded into
   it. The file format is unchanged, field order included. Grouping the reply's fields under
   `cell.result` was not done: it is a rename across a hundred sites with no behaviour behind it, and
   `clearResult` already is the one place.
5. **§6, not done.** The round-trip proofs (`RoundTrip.lean`) are stated against the parser's
   functions as they are, so a parser that records each node's span is a design of its own (a
   span-annotated return type, or a separate annotated parser kept equal to this one by test), not a
   change to make alongside the rest. `term-spans.ts` stays as it is, prototype note included.
6. **§4.3, begun.** Two seams taken: `visuals.ts` (the renderers and the registry, 500 lines) and
   `dom.ts` (`h`, `tex`), both without DOM state of their own; `app.ts` is 7,900 lines. The typeset
   input and read view (about a thousand lines) are the next seam; they reach into `S`, `Cell` and
   the cell lifecycle, so they want an explicit interface first.
7. **§8, done.** `ARCHITECTURE.md` §4 now describes a world as the record it is and lists what a new
   one touches; §5 lists `order.hasse` and the registry; §4a names the modules beside `app.ts` and
   the field table. `CLAUDE.md`'s definition of done gains a world, a visual kind and a saved field.
