/**
 * Help › Documentation: the guide to using the notebook, and the reference pages around the
 * notebook's own vocabulary. The pages are Markdown the notebook's own renderer draws (the
 * Markdown cells' renderer, so `$…$` is mathematics), with parts the page fills in itself: examples
 * to run, and the tables that live with the code they describe (the commands, the symbols, the
 * keyboard shortcuts, the example notebooks), so they cannot drift from it.
 *
 * Links between pages are `#doc:<id>`, to a function's page `#fn:<name>` (reference.ts); `#do:<action>`
 * opens part of the notebook (a dialog, a notebook). `{origin}` is this page's origin, which an Ollama set-up needs.
 */

/** A piece of a page: Markdown, a row of inputs to try (each runs in the notebook), or a table the
 *  page builds from the notebook's own lists. */
export type DocPart = string | { try: string[] } | { insert: "functions" | "symbols" | "shortcuts" | "examples" };

export interface DocPage { id: string; title: string; group: "Guide" | "Reference"; parts: DocPart[] }

/** A page's Markdown: code is written ‹like this› (a template literal cannot hold backticks). */
const md = (s: TemplateStringsArray) => String.raw(s).replace(/‹([^‹›\n]*)›/g, "`$1`");

export const DOC_PAGES: DocPage[] = [
  {
    id: "start", title: "Getting started", group: "Guide", parts: [md`
# Getting started

ChalkMath is a notebook for mathematics that **shows its work**. Type an expression into a cell and press **Enter**: the answer comes back with every step that produced it, each named and explained the way a textbook would, and with whether that step is proved correct.

Everything runs in your browser. The engine is compiled to WebAssembly and runs on your machine; nothing you type is sent to a server ([Privacy](#doc:privacy) says exactly what can leave it).

## Your first cell

Click into the empty cell at the bottom of a notebook, type an expression, and press **Enter**.`,
      { try: ["diff(x^2 * sin(x), x)", "expand((x+1)^3)", "integrate(x^2 + sin(x), x)"] },
      md`
Each of those buttons runs its input in the notebook. What comes back:

- **The answer** beside ‹Out[n]›, typeset. Arithmetic is exact: fractions stay fractions and roots stay roots, and ‹N(…)› gives a decimal when you want one.
- **The work**: the ‹▸ Work› button beside the cell (it shows when you hover) unfolds the steps, each a named rule with its explanation. View › Show all work unfolds every cell.
- **Where each piece came from**: click any part of the answer, a single term or a whole fraction, and the Explanation panel says which rule made it and traces it back through the steps ([Reading the work](#doc:work)).

## Where to go next

- [Notebooks and cells](#doc:notebooks): the kinds of cell, running them, naming values with ‹let›.
- [Typing math](#doc:typing): typeset input, ‹\›-symbols and templates, completion.
- [Lookups](#doc:ask): a cell that starts with ‹?› asks a question (‹?volume of a cone›) and a model answers it as mathematics the engine evaluates.
- [Functions and commands](#doc:functions): a page for everything the engine knows, with worked examples.
- The [welcome notebook](#do:welcome) is a short tour with one section per area; the [example notebooks](#doc:examples) go further.
`],
  },
  {
    id: "notebooks", title: "Notebooks and cells", group: "Guide", parts: [md`
# Notebooks and cells

A notebook is a list of cells, run top to bottom against one engine session. Each open notebook has its own tab at the top and its own session, so names defined in one do not leak into another. The **+** after the tabs opens a new one. A tab shows the notebook's name without its ‹.chalk›, cut short with ‹…› when it is long (point at the tab for the whole name). With many open, the tabs narrow and then scroll sideways (the mouse wheel scrolls them), and the **⌄** after them lists every open notebook. The middle mouse button closes a tab. Manim Studio, the courses and this documentation stay at the right while they are open. With no notebook open, the **welcome** tab takes their place: it starts a new notebook, opens one saved in this browser or a file, and links to the tour, the courses, this documentation and [Manim Studio](#do:studio).

## Kinds of cell

- **Math cells** (the default) hold one expression or definition for the engine.
- **Markdown cells** hold prose with mathematics in ‹$…$› ([Markdown cells](#doc:markdown)).
- **Sections** are headings that group the cells below them, up to the next section. A section folds away (click its marker, or ⋮ › Fold section) and runs as a group (Run › Run section). The sidebar's outline lists them, numbered, with the cells of the section you are reading and how many of each section's exercises you have answered; **Every cell** lists them all.
- **Lean cells** are Lean 4 itself, checked as you type ([Lean cells](#doc:lean)).
- **Exercises** ask the reader a question and check the answer ([Exercises](#doc:exercises)).
- **Scenes** are pictures told in beats, played as they scroll into view: points, curves and equations the engine samples, with a caption for each beat ([Scenes](#doc:scenes)).

Add one with **+ Cell** in the toolbar, from the Edit menu, or by hovering between two cells: ‹+ cell› inserts a math cell there and ‹▾› offers the other kinds. The ⋮ menu at the end of a cell's actions changes its kind, moves, duplicates or deletes it, copies its input, its output or its output as LaTeX, and sends its derivation to [Manim Studio](#doc:studio).

## Running

- **Enter** runs the cell; **▶ Run** in the toolbar runs the active cell, **▶▶ All** runs every cell in order.
- A cell that has run is labelled ‹In[n]› and its answer ‹Out[n]›, numbered in the order they ran, as in Mathematica. A cell waiting its turn shows ‹In[*]›.
- Changing a cell does not re-run the cells below it; they keep their answers until you run them. When ‹let› gives a name a new value, every cell that used the old one is marked **out of date**, its answer dimmed, with **Run again** and **Run this and below** (also in Run › Run this cell and below, and the cell's ⋮ menu).
- **■ Stop** (or Kernel › Interrupt) stops an evaluation that is taking too long. Kernel › Restart kernel starts a fresh session; Restart and run all rebuilds it from the cells.

## Names, functions and earlier answers

‹let› binds a name for the rest of the notebook, or defines a function of its parameters. ‹%› is the previous answer, ‹%%› the one before it and ‹%n› is ‹Out[n]›.`,
      { try: ["let f = x^3 - 3x", "diff(f, x, 2)", "let sq(x) = x^2 + 1", "diff(sq(x), x)", "diff(%, x)"] },
      md`
## Sliders

A cell that binds a name to a number, ‹let n = 3›, can be a slider: its ⋮ menu › **Show as a slider**. Moving it rewrites the number, runs the cell, and runs every cell below that used ‹n›, and the cells that used what those defined, in order. **range** sets where it starts and ends and its step. A plot or an ‹epicycles› drawing that depends on ‹n› follows the slider.

## Animating with manipulate

‹manipulate(e, p, from, to)› is Mathematica's ‹Manipulate›: its output is ‹e› with a slider for ‹p› and **▶ Play**, all in the one cell. The engine works out ‹e› for 40 values of ‹p› at once (a fifth argument sets how many), so the slider moves as fast as you drag it and a play is smooth. ‹e› can be anything a cell can be: a plot animates, keeping its axes still, and a derivative or a sum shows its calculation at each ‹p›, from ‹e› with ‹p› put in to its value. ‹column(e₁, e₂, …)›, Mathematica's ‹Column›, puts several things under the one slider: ‹manipulate(column(plot([f, L], x, 0, 3), m, L), h, 2, 0.05)› draws the curves and works out ‹m› and ‹L› at the same ‹h›, each labelled with its name. ‹from› can be larger than ‹to›: the slider starts at ‹from›, so ‹h, 1, 0.01› plays ‹h› down toward ‹0›. Use a slider on a ‹let› when several cells should follow one number; use ‹manipulate› to animate one result.

## What a cell shows

- **The input interpretation**: under the input, the engine's own reading of what you typed (with ‹%› and named values filled in), so you can see it read what you meant. View › Input interpretation hides it.
- **The kind** of cell (derivative, integral, matrix, …) as a small badge beside the input.
- **Output forms**: a matrix or a list can be shown as a bracketed or parenthesised matrix, a grid, a table or the input form (the text you would type), chosen from the small menu beside ‹Out[n]›, like Mathematica's ‹//MatrixForm›.
- **Plots and drawings**: ‹plot› and ‹epicycles› draw beside the answer; a file shows as what it is: an image, a table, text ([Saving, sharing and files](#doc:files)).

## Layout

The **sidebar** (Ctrl/⌘+B, or the rail at the left) shows the notebook's outline or the list of engine commands; hovering a command shows its documentation, clicking it puts an example in the active cell. The **panel** below the notebook holds the Explanation of whatever you clicked and, when the notebook has Lean cells, the Lean goals. View has the rest: light or dark, the size of the mathematics, and the input settings.
`],
  },
  {
    id: "typing", title: "Typing math", group: "Guide", parts: [md`
# Typing math

A math cell takes its input in one of two ways, and both are the same text underneath (it is the text that is saved and that the engine reads). Switching between them never changes a character, and an edit in either changes only what it touches. Any math cell can be typeset, a formula, a system or a λ-term as well as a calculation:

- **Typeset**: you read and edit the mathematics as it would be written on paper, with empty slots to fill in.
- **Text**: the expression as you would type it, highlighted, ‹integrate(x/(x^2 + 1), x)›.

View › Math input chooses for every cell: **automatic** (the default) typesets a cell that has notation to show (a fraction, a power, a root, an integral, a sum, a matrix) and keeps plain text for the rest; **typeset** and **text** use one for all. The **Text** / **Visual** button beside a cell, or **Ctrl/⌘+Shift+M**, switches that one cell.

## In typeset input

- ‹/› starts a fraction and ‹^› a power; the arrow keys move through the slots and **Tab** goes to the next empty one.
- A backslash name followed by space inserts a template: ‹\frac›, ‹\sqrt›, ‹\int› (an integral), ‹\dint› (a definite one), ‹\sum›, ‹\diff›, ‹\mat2x3› (a 2×3 matrix), ‹\vec3›, … ([the full list](#doc:symbols)). In a text cell the same names turn the cell typeset.
- **Shift+Enter** starts a new line, for a system's declarations, as in the text.
- Text that does not read yet (an unclosed bracket) shows as it is typed until it does.
- **@** wraps the selection in parentheses with a slot in front for a function's name: select ‹v›, press @, type ‹norm›.

## Symbols

Type ‹\› and a name, then space or Tab, for a symbol: ‹\pi› is π, ‹\lam› is λ, ‹\e› is ℯ, ‹\theta› is θ, and for logic ‹\and› is ∧, ‹\or› is ∨, ‹\not› is ¬, ‹\to› is →, ‹\forall› is ∀, ‹\in› is ∈, ‹\le› is ≤. The names are Lean's, so ‹\land›, ‹\wedge› and the like work too. Typing ‹\› alone lists them all and narrows as you type. They work the same in a typeset cell, where ASCII spellings also show as their glyphs: ‹->› as →, ‹&&› as ∧, ‹<=› as ≤ (the text keeps what you typed). [Symbols and templates](#doc:symbols) has the table.

## Help while typing

- **Completion**: **Tab** completes a command's name, a ‹\›-symbol, or inside ‹t[[…]]› a table's column name or a JSON key.
- **Usage on hover**: rest the pointer on a command's or a function's name in a cell, and after a moment its usage lines show, with a link to its page.
- **Signature help**: inside a call, the command's signature shows above the cell with the argument you are in highlighted. View › Signature help turns it off; Esc hides it for that call.
- **Syntax highlighting** colours numbers, commands, your own definitions and bound variables (the ‹k› of a sum, the ‹x› of a derivative). View › Syntax highlighting turns it off.
- **The math keypad** (View › Math keypad, on by default on a phone) puts fractions, powers, roots, integrals and the common symbols above the keyboard.

The grammar itself, operators, matrices and parts, is under [Syntax](#doc:syntax).
`],
  },
  {
    id: "work", title: "Reading the work", group: "Guide", parts: [md`
# Reading the work

Every answer is the end of a derivation: the engine rewrites your input one rule at a time, and each rewrite is a step you can read. Nothing is simplified in the page; every expression on screen is the engine's, and so is every rule name and explanation.

## Steps

‹▸ Work (n)› beside a cell unfolds its steps. Each step names its rule (‹product_rule›, ‹power_rule›, …), says in a sentence what it did, and shows the term after it, with the part it changed highlighted (hover a highlighted part to see what it was before). A command that delegates work, such as ‹rref› with its row operations or ‹integrate› with its guess and check, nests those steps under its own.

View › Show all work and Hide all work set every cell at once; View › Hide work in opened notebooks keeps files and links folded when they open.

## Stepping through

A cell can hold its work back so you can try each step yourself first: its ⋮ menu › **Step through the work**. The steps then come one at a time with ‹▸ Next step›, and the answer stays a ‹?› until the last one shows (click the ‹?› to see everything at once). ‹↺ Step through again› hides them again.

Writing a lesson, reveal as many steps as the reader should start with and choose ⋮ › **Begin with n steps shown**: the notebook saves that, so a worked example can stop just before the step you want the reader to find.

## Clicking an answer

Any part of an answer, of the input interpretation or of a step can be clicked. The panel's **Explanation** then shows:

- **Selection**: the subterm, and for a command its documentation.
- **Derivation trail**: the steps up to that point, with the ones that created the selected term marked, so you can follow a single coefficient back to the rule that produced it.
- **Proof status**: whether the rules that made it are proved sound.

## Proof status

ChalkMath's rules are proved correct in Lean 4 against a semantics of the expressions. Each rule, and so each step, carries one of four statuses:

- **verified** (a filled dot): the rule has an unconditional soundness theorem; the step preserves the value, always.
- **conditional**: the theorem has a side condition (a denominator that is not zero, say), and that the condition is needed is itself proved.
- **checked** (a hollow dot): a guess whose result a later step verifies. [‹integrate›](#fn:integrate)'s antiderivative is one: the engine differentiates it and answers only if that gives your function back, so the check is the proof.
- **unverified**: no theorem yet.

A step that delegates work is only as verified as the weakest step under it. A cell that mentions ‹i› is read over the complex numbers and shows each rule's status over ℂ, where it may differ (a rule proved over ℝ only is unverified there).
`],
  },
  {
    id: "exercises", title: "Exercises", group: "Guide", parts: [md`
# Exercises

An exercise asks a question and checks the reader's answer. Its **question** is an input for the engine, such as ‹diff(x^2 * sin(x), x)›: the question's value is the answer, and its work is the solution. The reader never sees either until they ask.

## Answering

Type an answer in the box as you would in a cell (‹2x sin(x) + x^2 cos(x)›) and press **Enter** or **Check**. The engine reduces your answer and the question's value to a **normal form** and compares the two, the way two λ-terms are equal when they reduce to the same normal form. So ‹x(2 sin(x) + x cos(x))› is right too: written differently, it reduces to the same thing.

- A wrong answer shows what it reduces to, so you can see where it parts from the answer.
- An answer may not do the question's work: for a ‹diff› question, ‹diff(…)› is not an answer. The elementary functions (‹sin›, ‹exp›, ‹sqrt›, …) are always allowed.
- For a λ-calculus question, the answer must be a normal form already; it is compared up to the names of its bound variables (α-equivalence).
- "Not yet" means the engine could not show the two equal. The normal form decides the identities it applies (distributing products, $\cos^2 = 1 - \sin^2$, $(e^u)^k = e^{ku}$), not every identity there is.

**Hint** opens the author's hints one at a time. **Show the solution** steps through the engine's own work on the question, one step at a time, with the answer last ([Stepping through](#doc:work)).

## Writing one

Add an exercise from Edit › Add exercise or the ‹▾› between cells. Its editor has a **prompt** (Markdown, what the reader is asked to do), the **question**, and **hints** (a blank line between two). The question is shown typeset under the prompt unless you untick that, for a prompt that says it in words ("the slope of $x^3$ at $x = 2$" for ‹subst(diff(x^3, x), x, 2)›). **✎ Edit** opens the editor again; **✓ Done** (or Shift+Enter) closes it.

An exercise is not an evaluation: it takes no ‹In[n]› and ‹%› still means the cell before it. It sees the names defined above it, so a question can use them.

## Lean exercises

A **Lean exercise** asks for a proof. Its statement is Lean, such as ‹theorem and_swap (p q : Prop) (h : p ∧ q) : q ∧ p := by›, and you write the proof below it, in a Lean editor of its own. You cannot change the statement. Lean checks your proof as you type, with the notebook's Lean cells above it in scope; with the cursor in the proof, the panel's **Lean goals** tab shows what is left to prove.

- It starts as ‹sorry›, which Lean accepts as "not proved yet": the exercise says so until the proof has none.
- When Lean rejects the proof, its message shows under the editor.
- **✓ Proved** means Lean accepts the declaration, statement and proof, with nothing left as ‹sorry›.
- **Show a proof** shows the author's, to compare with yours.

Add one from Edit › Add Lean exercise or the ‹▾› between cells. Its editor has the prompt, the **statement** (ending with ‹:= by›), the **starting proof** (indented; ‹sorry› if empty), **a proof** of your own, and the hints. Your proof is required for a notebook that ships with ChalkMath: CI checks it (‹scripts/notebooks/check-lean.mjs›).
`],
  },
  {
    id: "files", title: "Saving, sharing and files", group: "Guide", parts: [md`
# Saving, sharing and files

## Saving

- **File › Save** (Ctrl/⌘+S) keeps the notebook in this browser's storage under its name; **Save as…** (Ctrl/⌘+Shift+S) gives it another. The first save of an untitled notebook asks for a name, and a name already saved here is pointed out before it is replaced. **Open…** lists the notebooks saved here.
- Open tabs are kept as you work and come back when you reload the page, unsaved changes included; a tab with unsaved changes shows its name in italics, with a dot where its **×** is (a ‹*› after the name on a touch screen). A lesson from the Courses tab is never unsaved: it keeps your work on its own ([Courses and examples](#doc:examples)).
- Browser storage belongs to this browser on this machine. Clearing the site's data clears it, and a private window forgets it. To keep a notebook, or move it to another machine, export it.

## Files and links

- **File › Export to file…** downloads the notebook as a ‹.chalk› file (JSON: the cells, their outputs and steps, the studio's scenes and any attachments). **Import from file…** opens one.
- **File › Copy link to notebook** puts the whole notebook in a link, compressed into the part after ‹#›, which never reaches a server. A link carries the cells but not their outputs: the engine recomputes them when it opens. Attachments make a link long, and some apps cut long links; send the file instead.
- When a notebook opens, its cells run so the engine's session matches what is shown. Run › Run notebooks when opened turns that off: the outputs it was saved with show until you press Run all, and nothing is fetched.

## Data in a notebook

**File › Attach file…**, or pasting a file into a cell, attaches it to the notebook; it is saved with it. A cell refers to it as ‹⟦name⟧›, and ‹import("url")› fetches one from the web (the server has to allow other sites to read it). A file is a value, shown by what it is: an image as the image, a CSV or TSV as a table, JSON and other text as text.

Its parts turn it into numbers: ‹t[[All, "mass"]]› is a table's column, ‹j[["key"]]› a JSON value, ‹matrix(t)› a table's numbers and ‹samplePoints(svg)› points along an SVG's paths.`,
      { try: ["let planets = import(\"examples/data/planets.csv\")", "planets[[All, \"period\"]]", "mean(planets[[All, \"mass\"]])"] },
      md`
See [‹import›](#fn:import), [‹part›](#fn:part), [‹matrix›](#fn:matrix) and [‹samplePoints›](#fn:samplePoints).
`],
  },
  {
    id: "markdown", title: "Markdown cells", group: "Guide", parts: [md`
# Markdown cells

A Markdown cell holds prose: notes, explanations, a worked example in words. Add one from Edit › Add Markdown cell or the ‹▾› between cells.

- **Shift+Enter** or **Esc** renders it; **Enter** on the rendering, or a double-click, edits it again. In the editor, Enter is a new line.
- Mathematics goes in ‹$…$› inline and ‹$$…$$› on its own lines, written in LaTeX: ‹$\int_0^1 x^2\,dx = \tfrac13$› is $\int_0^1 x^2\,dx = \tfrac13$.

What it understands:

- ‹#› to ‹######› headings, ‹*emphasis*› and ‹**strong**›, code in backticks
- lists (‹-› or ‹1.›), ‹>› quotes, ‹---› rules, and fenced code blocks (a line of three backticks before and after)
- links ‹[text](https://…)› and images ‹![caption](https://…)›; an image alone in a paragraph is a figure with its caption under it
- an attached file by name, ‹⟦name⟧›: an image shows as the image, a table as a table
- callouts, the blocks a lesson is built from: a quote whose first line is ‹[!kind]›, with an optional title after it, such as ‹> [!theorem] Fundamental theorem of calculus›. The kinds are **definition**, **theorem** (also lemma, corollary, proposition), **proof** (ends with ∎), **example**, **try** (Try it), **mistake** (Common mistake; also warning), **note** (also tip) and **summary** (also goal)

An image from another site is loaded from that site when the cell is shown.
`],
  },
  {
    id: "ask", title: "Lookups: ? cells", group: "Guide", parts: [md`
# Lookups: ? cells

A math cell that starts with ‹?› is a question. A language model answers it as **mathematics the engine then evaluates**: a number, a list, a matrix or table, or a formula. So the answer is ordinary input, and everything you do with it afterwards still shows its work.

- ‹?volume of a cone› gives a formula, ‹B*h/3› with what each letter stands for.
- ‹?the first ten primes› gives a list.
- ‹?speed of light in m/s› gives a number.
- ‹let mlb = ?MLB runs and home runs per game for the last 20 years› gives a table, bound to ‹mlb›.

With ‹let›, a formula becomes a function of its letters: after ‹let V = ?volume of a cone›, ‹V(3, 4)› is a number and ‹diff(V(B, h), h)› a derivative.

## Where the answer comes from

The model first decides what kind of answer the question wants and whether it is standard knowledge.

- **Standard mathematics and science** (a formula, a constant) it answers itself, and nothing leaves your machine. The answer is labelled *From the model's knowledge*, and **⌕ Check with a search** looks for a source.
- **A question about the world** (teams, people, places, events) is always searched for: Wikipedia, and your own web search if you set one. The model is given the parts of the pages most likely to hold the answer and answers from them, citing what it used.
- If nothing is found, the model's memory is the last resort, labelled *From the model's memory: unsourced*.

## Checking it

What the model says is checked, not trusted. Every number in the answer is looked for in the pages it read, and one that is not there is marked ⚠. A formula is read from the LaTeX the source writes, not from the model's retelling of it. Under the answer, the label says where it came from with links to the sources, a line says what the rows and columns are, and **How this was found** lists every search and page read.

A question that asks to *make* something (a random matrix) is not a lookup and is refused; write it as mathematics instead.

## Saved with the notebook

The answer, and how it was found, is saved in the cell. Running the notebook again uses the saved answer without asking again; **↻ Look up again** asks afresh. A lookup in progress shows its steps as it goes; **■ Stop** stops it.

## Setting up

Lookups work without setting anything up in a browser that has a model ([Setting up lookups](#doc:ask-setup) says which), and the first one that needs a search asks before it sends anything. The model, the sources and the rest are in [Run › Lookup settings](#do:ask-settings).
`],
  },
  {
    id: "ask-setup", title: "Setting up lookups", group: "Guide", parts: [md`
# Setting up lookups

Everything here is in [Run › Lookup settings](#do:ask-settings), kept in this browser. **Test the model** there runs one small question on the model chosen and says how long it took and whether it got it right; a lookup asks three to five such questions.

## Choosing a model

**Automatic** (the default) uses Chrome's built-in model where the browser has one, else a WebGPU model. The dialog says which of the two this browser has.

### Chrome's built-in model

Gemini Nano, through Chrome's Prompt API. Chrome downloads and keeps it itself; this page downloads nothing. It is small and fast enough for formulas and simple facts, and the weakest of the choices at reading pages.

### A WebGPU model

A model that runs on your graphics card through WebLLM, in any browser with WebGPU. It is downloaded from Hugging Face the first time a lookup needs it, then kept by the browser. Choose the size under **WebGPU model**: from Qwen3 1.7B (about 2 GB of GPU memory) to Qwen3.5 9B (about 6.4 GB). It has to fit in the card's own memory; the 8B and 9B models read pages much better.

### Ollama, on this computer

[Ollama](https://ollama.com) serves models on your own machine, which can be larger than a browser can hold, and nothing leaves the machine but searches.

1. Install Ollama and pull a model: ‹ollama pull gemma4:e2b› (larger models read better and answer more slowly).
2. Start it so this page may call it: ‹OLLAMA_ORIGINS={origin} ollama serve›.
3. In Lookup settings choose **Ollama**, check the address (‹http://localhost:11434› by default) and pick the model; the list fills from what Ollama has.

Chrome may ask to let this page reach devices on your network; allow it.

### OpenRouter, a cloud model

[OpenRouter](https://openrouter.ai) runs many cloud models, paid on your own account. Choose **OpenRouter**, then **Sign in with OpenRouter**: a window signs you in and hands this page a key, kept in this browser (**Sign out** forgets it). Any model that takes a schema for its reply works; a fast, inexpensive one is plenty (the default is Claude Haiku). Free models are limited to a few requests a minute and often busy.

**Let the model search the web** uses OpenRouter's web search instead of Wikipedia and your search, at about a cent a lookup.

With OpenRouter, your question and the pages read go to OpenRouter and the model's provider. Your notebook never does.

## Sources

- **Answer from the model's knowledge**: lets standard formulas and constants be answered without a search, and the model's memory be the last resort. Off, every lookup searches.
- **Search Wikipedia**: on by default. It needs no key and allows other sites to read it.
- **Web search**: the address of a [SearXNG](https://docs.searxng.org) instance, or anything that answers its JSON (a URL, or one with ‹{q}› where the terms go). It searches Google, DuckDuckGo, Bing and Brave for you. It must have JSON output turned on and allow this page's origin, ‹{origin}›, to read it (CORS).
- **Page reader**: most sites do not let another page read them, so a page found by a web search is read through a reader you run, given as a URL with ‹{url}›. ‹scripts/ask-proxy/worker.js› in the ChalkMath repository is one, a Cloudflare Worker; its comments say how to deploy it.
- **Search without asking**: the first lookup that needs a search asks before sending anything. Turn this on to stop asking.
`],
  },
  {
    id: "lean", title: "Lean cells", group: "Guide", parts: [md`
# Lean cells

A Lean cell is [Lean 4](https://lean-lang.org) itself, running in your browser: definitions and proofs are checked as you type them, with the editor and messages of VS Code's Lean extension. Add one from Edit › Add Lean cell.

- **What is left to prove**: put the cursor in a proof and the panel's **Lean goals** tab shows the goals there, as Lean's infoview does.
- **One file**: a notebook's Lean cells, in order, are one Lean file. A definition in one cell is known in the cells after it, and editing a cell re-checks it and the cells below.
- **Messages**: errors, warnings and ‹#eval› / ‹#check› output show under the cell's lines.
- **Library**: Lean's core library (‹Init›). Mathlib is not available in the browser.

## The first time

Nothing for Lean loads until a notebook has a Lean cell. Then the editor and Lean's server download, about 140 MB compressed, once per browser: they are kept, and downloaded again only when ChalkMath updates Lean. Lean needs the page to be *cross-origin isolated*, so the first time, the page reloads once to turn that on; your tabs come back as they were.

The example notebook *Order and lattices* has its proofs in Lean cells.
`],
  },
  {
    id: "scenes", title: "Scenes", group: "Guide", parts: [md`
# Scenes

A scene is a picture told in beats, the way an animated explainer is: a point walks round a circle while a caption says what to look at, a derivation morphs one step into the next, a path tightens onto a curve. It sits in the notebook like any cell, plays once when most of it scrolls into view, and can be paused, scrubbed and stepped beat by beat (‹⏮› ‹⏭›, or the arrow keys; Space plays and pauses). With reduced motion asked for, it waits for ‹▶›.

Every coordinate is the engine's: each object is sampled with ‹plot› or ‹manipulate›, and each equation's steps come from the engine, so what a scene shows is what the mathematics says. The samples are quiet: a scene takes no ‹In[n]› and leaves ‹%› alone. It can use the names the cells above it bind.

## Writing one

Add a scene from **+ Cell** ‹▾› or **Edit › Add scene**, write its script, and press **Shift+Enter**. Double-click a scene (or **✎ Edit**) to change it; a mistake is reported at its line.
`, "```\nclock t from 0 to 2pi\nC = curve(exp(i*s), s, 0, 2pi) faint\nP = point(exp(i*t))\nR = arrow(0, P)\nL = label(P, \"e^{it}\")\nW = trace(P)\nE = eq(diff(exp(i*t), t))\n> show C, P, R, L | A point on the unit circle.\n> show W; play t to 2pi in 4s | Once round.\n> show E; work E | Its velocity, step by step.\n```", md`

The first line names the scene's **clock**, the variable it animates, and its range. Then the objects, one per line, each with a name:

| Object | What it draws |
| --- | --- |
| ‹point(z)› | a dot at ‹z›: a complex number (a real one sits on the real axis), or a vector ‹[x, y]› |
| ‹curve(z, s, a, b)› | the curve ‹z› traces as ‹s› runs from ‹a› to ‹b› |
| ‹graph(f, x, a, b)› | the graph of ‹y = f(x)› |
| ‹arrow(A, B)›, ‹segment(A, B)› | from ‹A› to ‹B›: point names or expressions |
| ‹line(A, B)› | the whole line through ‹A› and ‹B› |
| ‹poly(A, B, C, …)› | a filled polygon with those corners |
| ‹grid(M)› | the plane's grid as the $2 \times 2$ matrix ‹M› moves it: the lines through ‹M›'s images of the whole-number points |
| ‹trace(P)› | the path the point ‹P› has drawn since the trace appeared |
| ‹label(A, "TeX")› | TeX beside a point |
| ‹eq(e)› | an expression above the picture, as the engine prints it |
| ‹value(e, "TeX")› | a real number above the picture, read off as the clock moves: ‹value(det(M), "\det = ")› |

Wherever a point goes, a vector does: the plane is $\mathbb{C}$, and a vector of two entries, ‹[x, y]›, ‹[x; y]› or anything the engine evaluates to one, such as ‹A*[1; 0]›, is the point $x + iy$.

‹let M = (1 - t)*[1, 0; 0, 1] + t*A› names an expression for the lines below it; the name is written in, in parentheses, wherever it is used. That matrix is the usual way to animate one: it is the identity when ‹t› is ‹0› and ‹A› when it is ‹1›, so ‹grid(M)› and ‹point(M*[1; 0])› move from where they are to where ‹A› sends them.

Any of them may use the clock, and then it moves. After the closing parenthesis come styles: ‹faint›, ‹dashed›, ‹thick›, ‹color 1› to ‹color 6›. ‹view x0, x1, y0, y1› fixes the window (otherwise it takes in everything the scene ever draws, with equal scales on both axes, so a circle is a circle), and ‹noaxes› leaves out the axes.

## Beats

Each line starting with ‹>› is a beat: actions separated by ‹;›, then ‹|› and a caption in Markdown. A beat lasts as long as its longest action, and at least long enough to read its caption.

- ‹show A, B› fades objects in; ‹hide A› fades them out. An object no beat mentions is there from the start.
- ‹play t to 2pi in 4s› moves the clock (from where it is, or ‹from …›), eased at both ends.
- ‹work E› steps an ‹eq› through the engine's derivation, each term morphing into the next.
- ‹wait 2s› holds.

The calculus course's lesson *Circles, exponentials and rotation* is told mostly in scenes, and the linear algebra course uses them for the plane: vectors tip to tail, a matrix moving the grid, the product as one map after another, row operations turning lines about their crossing, the determinant as an area, and eigenvectors.
`],
  },
  {
    id: "studio", title: "Manim Studio", group: "Guide", parts: [md`
# Manim Studio

[Manim](https://www.manim.community) is the Python library behind many animated mathematics videos. Manim Studio turns a derivation into a storyboard for it: each step becomes a shot, the term morphing into the next.

1. Run a cell, then choose **Send to scene** from its ⋮ menu (a new scene, or an existing one). The statement and each step's term become shots.
2. Sending a derivation opens the studio's tab; **View › Manim Studio** (or Help, or the welcome tab) opens it too, and its **×** closes it. Each shot can be turned off, given an animation (‹TransformMatchingTex›, ‹TransformMatchingShapes›, ‹FadeTransform›, ‹Write› or ‹Create›) and a duration.
3. **▶ Play** previews the scene in the page, matching glyphs between terms the way ‹TransformMatchingTex› does.
4. The Python for the scene is beside it. Copy it into a file and render it with Manim on your computer, with the command shown (‹manim -pqh scene.py›).

The page writes only the storyboard; rendering the video is Manim's job, outside the browser. Scenes are saved with the notebook: the studio shows the current notebook's, and none while no notebook is open.
`],
  },
  {
    id: "examples", title: "Courses and examples", group: "Guide", parts: [md`
# Courses and examples

Notebooks that come with ChalkMath, grouped into **projects**: a **course** is a sequence of lessons that build on each other, with exercises the engine checks; a **collection** is notebooks to explore in any order. File › Courses and examples opens the **Courses** tab, which lists them all.

A lesson opens in its own tab with a bar above it: the course it belongs to, where it is in it, how many of its exercises you have answered, and **‹ Previous** and **Next ›**. The Courses tab remembers, in this browser, which lessons you have opened and finished.

A lesson keeps your work in this browser as you go: your answers, the hints you have shown and anything you change come back when you open it again, from the Courses tab or with **‹ Previous** and **Next ›**, even after closing its tab. So a lesson's tab is never marked unsaved and there is nothing to save; File › Save says so, and **Save as…** makes a notebook of your own from it. **Start over**, in the bar once you have worked in a lesson, clears your work and opens it as it came. If a lesson has changed since you worked on it, it opens as it is now, with your answers to the exercises it still has carried over.

In a course that builds one Lean development across its lessons, each lesson's Lean sees the Lean of the lessons before it: their Lean cells, and their Lean exercises with the author's proofs. So a definition from lesson 1, or a theorem proved there, can be used in lesson 3.
`, { insert: "examples" }],
  },
  {
    id: "privacy", title: "Privacy", group: "Guide", parts: [md`
# Privacy

The engine runs in your browser, and notebooks are kept in this browser's storage until you export them. What you type is not sent to a server. The page loads nothing from other sites except what you ask for:

- an ‹import("url")› cell fetches that URL;
- an image in a Markdown cell is loaded from its site;
- a ‹?› lookup that searches sends the search terms the model wrote to Wikipedia and, if you set them, your web search and page reader. The first search asks first. Never the notebook;
- with OpenRouter chosen for lookups, the question and the pages read go to OpenRouter and the model's provider;
- a WebGPU lookup model is downloaded from Hugging Face, once; Lean, the first time a notebook has a Lean cell, from this site.

A notebook link carries the notebook after the ‹#›, which browsers do not send to the server.
`],
  },
  {
    id: "syntax", title: "Syntax", group: "Reference", parts: [md`
# Syntax

The language is small and close to what you would write by hand. A cell is one expression, or a definition:

- ‹let name = e› names a value; ‹let f(x, y) = e› defines a function.
- ‹+ - * / ^› with the usual precedence; ‹^› groups to the right, and ‹-x^2› is $-(x^2)$.
- **Implicit multiplication**: ‹2x›, ‹2(x+1)›, ‹x y› and ‹2pi› multiply. Two numbers side by side (‹3 4›) are an error.
- **Calls**: ‹name(a, b)› for a command or a function you defined; any other name before ‹(› is a variable times a parenthesis.
- **Constants**: ‹pi› or π, ‹i› the imaginary unit, ‹ℯ› (‹\e›) Euler's number; ‹exp(x)› is $e^x$.
- **Matrices and vectors** row by row, commas between entries and semicolons between rows: ‹[1, 2; 3, 4]›. A list is one row, ‹[a, b, c]›.
- [**Parts**](#fn:part), as Mathematica writes them: ‹m[[2]]›, ‹m[[i, j]]›, ‹m[[All, 1]]›, spans ‹a;;b› and ‹a;;b;;step›, a list of positions ‹{i, j}›, and column names for tables, ‹t[[All, "mass"]]›.
- [**Earlier answers**](#fn:%): ‹%›, ‹%%›, ‹%n›.
- **Files**: ‹⟦name⟧› is an attached file, ‹import("url")› one from the web.
- **Questions**: a cell starting with ‹?›, or ‹let x = ?…› ([Lookups](#doc:ask)).

Some areas have their own notation:

- [**λ-calculus**](#fn:lambda): a cell with a λ (‹\lam›) or a backslash is a λ-term. ‹λx. e› abstracts, application is juxtaposition, ‹λx y. e› binds two, digits are Church numerals and ‹name := term› defines.
- [**Orders**](#fn:poset): ‹poset({a, b, c}; a<b, a<c)› is a partial order from its relation, ‹map(P; a->b)› a map on one.
`],
  },
  {
    id: "functions", title: "Functions and commands", group: "Reference", parts: [md`
# Functions and commands

Every function and notation, by area. Each has a page: what it does, the details, and examples whose outputs this engine computes as you read them. Search the contents for a name to go straight to its page.
`, { insert: "functions" }],
  },
  {
    id: "symbols", title: "Symbols and templates", group: "Reference", parts: [md`
# Symbols and templates

Type a backslash and a name, then space or Tab. Typing ‹\› alone lists them and narrows as you type.
`, { insert: "symbols" }],
  },
  {
    id: "shortcuts", title: "Keyboard shortcuts", group: "Reference", parts: [md`
# Keyboard shortcuts

Ctrl on Windows and Linux is ⌘ on a Mac.
`, { insert: "shortcuts" }],
  },
];
