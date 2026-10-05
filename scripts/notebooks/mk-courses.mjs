// node scripts/notebooks/mk-courses.mjs
// Generates the courses: notebooks/courses/<course>/<nn-lesson>.chalk and notebooks/courses.json, the
// list of projects the Courses tab shows (the courses, then the example notebooks as a collection).
// A lesson is short: a goal, worked examples to step through, a slider where a picture moves, and
// exercises the engine checks by normal form. Every cell is checked against the engine by
// `drive.mjs --check` (notebooks/golden/), so a lesson cannot quietly stop working.
// Inline code is written ‹like this› (template literals cannot hold backticks).
import { readFileSync, writeFileSync, mkdirSync } from "node:fs";

const r = String.raw;
const code = (text) => text.replace(/‹([^‹›\n]*)›/g, "`$1`").trim();

/** A lesson being written: its cells, added in order. */
function lesson() {
  const cells = [];
  return {
    cells,
    sec: (title) => cells.push({ src: title, type: "section", showWork: false, label: null }),
    md: (text) => cells.push({ src: code(text), type: "markdown", showWork: false, label: null }),
    /** A math cell. `work`: show the steps; `step`: step through them from that many; `slider`: [min, max, step]. */
    m: (src, o = {}) => cells.push({
      src, showWork: !!(o.work || o.step !== undefined), label: null,
      ...(o.step !== undefined ? { stepwise: o.step } : {}),
      ...(o.slider ? { slider: { min: o.slider[0], max: o.slider[1], step: o.slider[2] }, mode: "raw" } : {}),
    }),
    /** An exercise: the question (its value is the answer), the prompt, the hints. */
    ex: (question, prompt, hints = [], o = {}) => cells.push({
      src: question, type: "exercise", prompt: code(prompt), ...(hints.length ? { hints: hints.map(code) } : {}),
      ...(o.hide ? { hideQuestion: true } : {}), showWork: false, label: null,
    }),
    /** A Lean cell. */
    lean: (src) => cells.push({ src, type: "lean", showWork: false, label: null }),
    /** A scene: a picture told in beats (apps/notebook/src/scene.ts), its script as the cell's source. */
    sc: (script) => cells.push({ src: script.trim(), type: "scene", showWork: false, label: null }),
    /** A Lean exercise: the statement (ending `:= by`), the prompt, the author's proof (required: CI checks
     *  it), the hints, and `o.start`, the proof the reader starts from (`sorry` if absent). */
    lx: (statement, prompt, proof, hints = [], o = {}) => cells.push({
      src: statement, type: "exercise", lean: true, prompt: code(prompt), leanSolution: proof,
      ...(o.start ? { leanStart: o.start } : {}), ...(hints.length ? { hints: hints.map(code) } : {}), showWork: false, label: null,
    }),
  };
}

const courses = [];
/** A course: its lessons are written by `build`, one call of `add(file, title, blurb, write)` each.
 *  `o.leanPrelude`: each lesson's Lean sees the Lean of the lessons before it. */
function course(id, title, blurb, level, build, o = {}) {
  const lessons = [];
  build((file, ltitle, lblurb, write) => {
    const L = lesson();
    write(L);
    lessons.push({ file, title: ltitle, blurb: lblurb, cells: L.cells });
  });
  courses.push({ id, title, blurb, level, lessons, ...(o.leanPrelude ? { leanPrelude: true } : {}) });
}

// ---------------------------------------------------------------------------------------------------
/** Lesson 5's picture of induction: a row of dominoes, the step an arrow from each to the next, the base case a push. */
const dominoScene = (() => {
  const N = 8, ks = [...Array(N).keys()];
  const names = (p, n = N) => ks.slice(0, n).map((k) => `${p}${k}`).join(", ");
  return [
    `clock t from -1 to ${N + 1}`, "noaxes", `view -1.5, ${N + 0.5}, -0.8, 2.6`,
    // domino k tips over around t = k, until it leans on the next one
    ...ks.map((k) => `D${k} = segment(${k}, ${k} + 1.6*exp(i*(pi/2 - 0.675/(1 + exp(-8*(t - ${k})))))) thick color 1`),
    ...ks.map((k) => `L${k} = label(${k} - 0.35i, "P(${k})")`),
    ...ks.slice(0, N - 1).map((k) => `K${k} = arrow(${k + 0.15} + 2i, ${k + 0.85} + 2i) color 4`),
    "A = arrow(-1.2 + 1.4i, -0.1 + 1.4i) thick color 2",
    `> show ${names("D")}, ${names("L")} | A domino for each statement: $P(0)$, $P(1)$, $P(2)$, and so on. A domino down is a statement proved.`,
    `> show ${names("K", N - 1)} | The step, $P(n) \\to P(n+1)$ for every $n$: each domino stands where its fall knocks over the next. By itself it knocks nothing over.`,
    `> show A; play t to ${N + 1} in 6s | The base case: push the first. Then each falls in turn, however far along the line it stands.`,
  ].join("\n");
})();
/** Lesson 5's odd numbers as layers of a square: layer k is the 2k − 1 dots with max(x, y) = k − 1. */
const oddSquareScene = (() => {
  const layers = [1, 2, 3, 4, 5].map((k) => {
    const dots = [];
    for (let a = 0; a < k; a++) for (let b = 0; b < k; b++) if (Math.max(a, b) === k - 1) dots.push([`Q${k}_${dots.length}`, `point(${a} + ${b}i) thick color ${k}`]);
    return dots;
  });
  const show = (...ks) => ks.flatMap((k) => layers[k - 1].map(([n]) => n)).join(", ");
  return [
    "noaxes", "view -1, 5, -1, 5",
    ...layers.flat().map(([n, d]) => `${n} = ${d}`),
    `> show ${show(1)} | $1$.`,
    `> show ${show(2)} | Three more dots, round a corner: $1 + 3 = 4$, a $2 \\times 2$ square.`,
    `> show ${show(3)} | Five more: $1 + 3 + 5 = 9$, a $3 \\times 3$ square.`,
    `> show ${show(4, 5)} | Each odd number wraps the square in one more layer: the $n \\times n$ square plus $2n + 1$ dots is the $(n+1) \\times (n+1)$ one.`,
  ].join("\n");
})();

course("logic", "Logic and proof technique",
  "Propositions and truth tables, normal forms, proofs as Lean tactics, quantifiers, three kinds of induction, relations and well-founded termination: the toolkit every later course uses.",
  "Discrete mathematics", (add) => {

  add("01-truth-tables.chalk", "Propositions and truth tables", "Why “if … then” is defined the way it is, truth tables, tautologies, and satisfying assignments as witnesses.", ({ sec, md, m, ex }) => {
    sec("Propositions and truth tables");
    md(r`
> [!goal]
> Decide whether a formula is always, sometimes or never true, and point to the row that shows it.
`);
    md(r`
> [!try]
> "If it rains, I bring an umbrella." Four days: rain and an umbrella, rain and none, dry and an umbrella, dry and none. On which of them did I break my word?
`);
    md(r`Only on the second. The promise says nothing about dry days, so they cannot break it. Hold on to that: it is what "if … then" means in logic.`);
    md(r`
> [!definition] Proposition, connective
> A **proposition** is a statement that is either true or false. Variables $p, q, r$ stand for propositions, and **connectives** build bigger ones: $\lnot p$ (not), $p \land q$ (and), $p \lor q$ (or), $p \to q$ (if … then), $p \leftrightarrow q$ (if and only if). $\top$ is true and $\bot$ is false.
`);
    md(r`Type the glyphs, or their ASCII spellings: ‹!p›, ‹p && q›, ‹p || q›, ‹p -> q›, ‹p <-> q›, ‹true›, ‹false›. A cell with a connective in it is a logic cell.`);
    m("p && q -> p");
    md(r`A connective is defined by its value for each combination of values of its parts. For "and" and "or" there is nothing to argue about:`);
    m("truthtable(p ∧ q)");
    m("truthtable(p ∨ q)");
    sec(`What "if … then" has to mean`);
    md(r`$p \to q$ is false when $p$ is true and $q$ false: rain and no umbrella. The rows with $p$ false are settled by how mathematics uses "if … then". "Every multiple of 4 is even" means: for every $n$, if $4 \mid n$ then $n$ is even. That is true, so the implication must be true for every $n$, the ones that are not multiples of 4 included. Read ‹∀ n ∈ 1..12› as "for every $n$ from 1 to 12" (lesson 4 is about it):`);
    m("∀ n ∈ 1..12, 4 ∣ n → even(n)");
    md(r`
> [!try]
> Two natural guesses for "if $p$ then $q$" are "$p$ and $q$" and "$p$ if and only if $q$". Predict the $n$ at which each one makes this true statement false, then look.
`);
    m("∀ n ∈ 1..12, 4 ∣ n ∧ even(n)", { work: true });
    m("∀ n ∈ 1..12, 4 ∣ n ↔ even(n)", { work: true });
    md(r`"And" fails at $n = 1$, where $p$ and $q$ are both false; "if and only if" fails at $n = 2$, where $p$ is false and $q$ true. For "every multiple of 4 is even" to come out true, both of those rows must be true. The table is forced: false in the one row that breaks the promise, true in the other three.`);
    md(r`
> [!definition] Implication
> $p \to q$ is false exactly when $p$ is true and $q$ is false. When $p$ is false it is true whatever $q$ is (**vacuously** true): a dry day keeps the promise.
`);
    m("truthtable(p → q)");
    sec("Truth tables");
    md(r`A formula's **truth table** lists every assignment of true and false to its variables, one row each, with the formula's value. One variable needs 2 rows, two need 4.`);
    md(r`
> [!try]
> How many rows does a formula in $p$, $q$ and $r$ need? One in 10 variables?
`);
    m("truthtable((p → q) ∧ (q → r) → (p → r))");
    md(r`Each new variable doubles the count, since every old row appears once with it true and once with it false: $n$ variables make $2^n$ rows, and 10 make 1024. This formula is true in all 8 rows: if $p$ gives $q$ and $q$ gives $r$, then $p$ gives $r$, whatever $p$, $q$ and $r$ say.`);
    sec("Tautologies and counterexamples");
    md(r`
> [!definition] Tautology, satisfiable, contradiction
> A formula is a **tautology** when every row is true, **satisfiable** when some row is, and a **contradiction** when none is. A row where it is false is a **counterexample**; a row where it is true is a **witness**.
`);
    md(r`
> [!try]
> $(p \to q) \lor (q \to p)$ says "of any two statements, one implies the other". That sounds false. Is it a tautology? Decide before you look.
`);
    md(r`‹taut› decides by the table; when the answer is ⊥, the step names a row that falsifies the formula.`);
    m("taut((p → q) ∨ (q → p))", { work: true });
    md(r`It is: if $q$ is true then $p \to q$ is, and if $q$ is false then $q \to p$ is. The implication of logic asks only about truth values, never about a connection between $p$ and $q$. A single implication is not a tautology, and the step shows the row that breaks it:`);
    m("taut(p → q)", { work: true });
    md(r`‹sat› gives a witness, as a map from each variable to its value, or ⊥ when there is none; ‹falsify› gives a counterexample the same way.`);
    m("sat((p ∨ q) ∧ ¬p)", { work: true });
    m("sat(p ∧ ¬p)");
    m("falsify(p ∧ q → r)");
    sec("The converse and the contrapositive");
    md(r`
> [!mistake]
> A common slip is to read $p \to q$ as saying $q \to p$ as well (the **converse**). "If $n$ is divisible by 4 then $n$ is even" is true; "if $n$ is even then $n$ is divisible by 4" is not ($n = 2$). ‹equiv› decides whether two formulas have the same table, and names a row where they differ:
`);
    m("equiv(p → q, q → p)", { work: true });
    md(r`What does follow is the **contrapositive** $\lnot q \to \lnot p$: if $q$ failed, $p$ cannot have held, or the promise was broken. That is why a proof "suppose not $q$ … then not $p$" proves $p \to q$.`);
    m("equiv(p → q, ¬q → ¬p)");
    sec("Exercises");
    md(r`Answer ‹true› or ‹false› (or ⊤, ⊥) for ‹taut› and ‹equiv›. For ‹sat› and ‹falsify›, give an assignment, as a map such as ‹{p ↦ true, q ↦ false}› or as a conjunction of literals such as ‹p ∧ ¬q›; any assignment that works is right. Where a formula is asked for, any formula with the right truth table is right.`);
    ex("taut(p → (q → p))", r`Is $p \to (q \to p)$ a tautology?`, [
      r`The only way an implication fails is a true premise and a false conclusion. Can $q \to p$ be false while $p$ is true?`,
    ]);
    ex("taut((p → q) → (¬p → ¬q))", r`Is $(p \to q) \to (\lnot p \to \lnot q)$ a tautology? (This is the converse in disguise.)`, [
      r`Look for $p$ false and $q$ true.`,
    ]);
    ex("falsify((p → q) → p)", r`Find a counterexample to $(p \to q) \to p$: an assignment that makes it false.`, [
      r`The conclusion $p$ has to be false. What does that make $p \to q$?`,
    ]);
    ex("equiv(¬(p → q), p ∧ ¬q)", r`Are $\lnot(p \to q)$ and $p \land \lnot q$ equivalent?`, [
      r`$p \to q$ is false in exactly one row.`,
    ]);
    ex("¬(p ↔ q)", r`Invent a connective: write a formula that is true when exactly one of $p$, $q$ is true ("exclusive or").`, [
      r`"At least one" is $p \lor q$. Which row of $p \lor q$ is true but should not be?`,
      r`Rule that row out: $(p \lor q) \land \lnot(\ldots)$.`,
    ], { hide: true });
    sec("Knights and knaves");
    md(r`
> [!example] A puzzle as a satisfiability question
> On an island, knights always tell the truth and knaves always lie. $A$ says "$B$ is a knave". $B$ says "$A$ and I are of the same kind". Let $a$ mean "$A$ is a knight" and $b$ mean "$B$ is a knight". What a knight says is true and what a knave says is false, so each statement is equivalent to its speaker being a knight: $a \leftrightarrow \lnot b$ and $b \leftrightarrow (a \leftrightarrow b)$.
`);
    ex("sat((a ↔ ¬b) ∧ (b ↔ (a ↔ b)))", r`Who is a knight and who is a knave? Answer with an assignment to $a$ and $b$, such as ‹{a ↦ true, b ↦ false}›.`, [
      r`Try $b$ true: then $a \leftrightarrow b$ must be true, so $a$ is true. Does $a \leftrightarrow \lnot b$ hold?`,
      r`So $b$ is false. Then $a \leftrightarrow b$ must be false.`,
    ], { hide: true });
    md(r`
> [!summary]
> A connective is its truth table, and the table of $\to$ is forced: it is the only one that makes "every multiple of 4 is even" true. A formula is decided by its table: true in every row (a tautology), in some row (satisfiable, with a witness), or in none (a contradiction). One row is a counterexample, and one is enough.
`);
    md(r`This lesson went from a formula to its table. The next goes the other way: given any table at all, is there a formula that has it?`);
  });

  add("02-normal-forms.chalk", "Equivalence and normal forms", "A formula for any truth table, read off its rows; then the laws of logic as rewrites: negation normal form, CNF and DNF, one law a step.", ({ sec, md, m, ex }) => {
    sec("Equivalence and normal forms");
    md(r`
> [!goal]
> Write down a formula for any truth table, then reach the same normal forms from a formula by the laws of logic, one law a step.
`);
    md(r`Lesson 1 went from a formula to its table. Here is a table with no formula:`);
    md(r`
$$\begin{array}{ccc|c} p & q & r & \ ? \\ \hline T & T & T & F \\ T & T & F & T \\ T & F & T & T \\ T & F & F & F \\ F & T & T & F \\ F & T & F & F \\ F & F & T & F \\ F & F & F & T \end{array}$$
`);
    md(r`
> [!try]
> Find a formula with this table. Better: a method that works for any table.
`);
    sec("A formula for any table");
    md(r`Take one true row, $p, q, r = T, T, F$. The formula $p \land q \land \lnot r$ is true in that row and in no other: each literal pins down one variable. Write one such formula for each true row and join them with $\lor$. The result is true exactly when one of them is, which is exactly in the true rows:`);
    m("truthtable((p ∧ q ∧ ¬r) ∨ (p ∧ ¬q ∧ r) ∨ (¬p ∧ ¬q ∧ ¬r))");
    md(r`Nothing in that used this particular table. So every truth table has a formula, built from $\lnot$, $\land$ and $\lor$ alone (a table with no true row gets $\bot$).`);
    md(r`
> [!definition] Literal, term, clause, DNF, CNF
> A **literal** is a variable or its negation. A **term** is an $\land$ of literals and a **clause** an $\lor$ of them. A formula is in **disjunctive normal form** (DNF) when it is an $\lor$ of terms, as the one just built is, and in **conjunctive normal form** (CNF) when it is an $\land$ of clauses.
`);
    md(r`The same works upside down. A clause can be false in exactly one row: $\lnot p \lor \lnot q \lor \lnot r$ is false only at $T, T, T$. One such clause for each false row, joined with $\land$, rules out the false rows and nothing else: a CNF. So every formula is equivalent to one in DNF and to one in CNF.`);
    md(r`
> [!definition] Logical equivalence
> $\varphi \equiv \psi$ when $\varphi$ and $\psi$ have the same value under every assignment: the same truth table. Replacing a part of a formula by an equivalent one does not change the value of the whole.
`);
    sec("Without the table");
    md(r`Reading off rows costs a term per true row, and a formula in 20 variables has $2^{20} = 1048576$ rows. The laws of logic work on the formula instead. Each replaces a part by an equivalent part, and each is checked once and for all by a table of a few rows.`);
    md(r`
> [!theorem] The laws used below
> $p \to q \equiv \lnot p \lor q$, $\quad p \leftrightarrow q \equiv (p \to q) \land (q \to p)$, $\quad \lnot\lnot p \equiv p$,
>
> De Morgan: $\lnot(p \land q) \equiv \lnot p \lor \lnot q$ and $\lnot(p \lor q) \equiv \lnot p \land \lnot q$,
>
> distribution: $p \lor (q \land r) \equiv (p \lor q) \land (p \lor r)$ and $p \land (q \lor r) \equiv (p \land q) \lor (p \land r)$.
`);
    md(r`The first is lesson 1's table of $\to$ read as a formula: false only when $p$ is true and $q$ false. Each law is proved in Lean over the booleans, and the engine's normal forms are proved to keep the value of the formula (the dot next to each step).`);
    sec("Negation normal form");
    md(r`
> [!definition] Negation normal form (NNF)
> No $\to$ or $\leftrightarrow$, and $\lnot$ only directly on variables. Get there by eliminating the arrows, then pushing each negation inward with De Morgan's laws until it reaches a variable, cancelling double negations on the way.
`);
    md(r`Step through it: say which law comes next before you press ‹▸ Next step›.`);
    m("nnf(¬(p ∧ (q ∨ ¬r)))", { step: 0 });
    m("nnf(¬(p → q))", { work: true });
    md(r`
> [!mistake]
> The natural guess is that $\lnot$ just moves inside: $\lnot(p \land q) \equiv \lnot p \land \lnot q$. But "not both" is weaker than "neither". The engine finds the row where they differ:
`);
    m("equiv(¬(p ∧ q), ¬p ∧ ¬q)", { work: true });
    md(r`At $p$ true and $q$ false, "not both" holds and "neither" does not. De Morgan's law is the repair: the $\land$ turns into $\lor$, since "not both" means "at least one fails".`);
    sec("Conjunctive and disjunctive normal form");
    md(r`From NNF, distribute $\lor$ over $\land$ for CNF (or $\land$ over $\lor$ for DNF), as $a(b + c) = ab + ac$ in arithmetic, except that here each distributes over the other. A clause that contains both $p$ and $\lnot p$ is always true and drops out; so does a term with both, which is always false.`);
    m("cnf(p ∨ (q ∧ r))", { work: true });
    m("cnf(p ↔ q)", { step: 0 });
    m("dnf(p ↔ q)", { step: 0 });
    md(r`The DNF lists the two true rows of the table of $p \leftrightarrow q$, both false or both true, reached without the table.`);
    md(r`
> [!note] Why CNF, and its cost
> A CNF is a list of constraints that must all hold, each satisfied by any one of its literals. SAT solvers, which decide satisfiability for formulas with millions of variables, take their input in CNF. Distribution has a price, though: each further pair joined by $\lor$ doubles the clauses.
`);
    m("cnf((p ∧ q) ∨ (r ∧ s) ∨ (t ∧ u))");
    md(r`Three pairs give $2^3 = 8$ clauses, and $n$ pairs $2^n$. Solvers avoid that by naming subformulas with new variables (the Tseitin encoding), which keeps satisfiability rather than equivalence.`);
    sec("Exercises");
    md(r`Your answer must be in the form asked for and equivalent to the formula. Equivalence is decided by truth table, so a "not yet" is definite: the answer differs from the formula in some row.`);
    ex("nnf(¬(p ∨ ¬q))", r`Put $\lnot(p \lor \lnot q)$ in negation normal form.`, [
      r`De Morgan: $\lnot(a \lor b) \equiv \lnot a \land \lnot b$.`,
      r`Then $\lnot\lnot q \equiv q$.`,
    ]);
    ex("nnf(p → q)", r`Write $p \to q$ without $\to$: in negation normal form.`, [r`$p \to q$ fails only when $p$ is true and $q$ false.`]);
    ex("cnf((p ∧ q) ∨ r)", r`Put $(p \land q) \lor r$ in conjunctive normal form.`, [r`Distribute $\lor r$ over the $\land$: each conjunct gets its own $\lor r$.`]);
    ex("dnf(p ∧ (q ∨ r))", r`Put $p \land (q \lor r)$ in disjunctive normal form.`, [r`Distribute $p \land$ over the $\lor$.`]);
    ex("cnf(¬(p ∧ q) ∧ (p ∨ q))", r`Put $\lnot(p \land q) \land (p \lor q)$ in CNF. (It says "exactly one of $p$, $q$".)`, [
      r`Only the first part needs work: De Morgan.`,
    ]);
    ex("dnf((p ∧ q) ∨ (q ∧ r) ∨ (p ∧ r))", r`The **majority** of $p$, $q$, $r$ is true when at least two of them are. Write it in DNF, from its truth table or from the words.`, [
      r`Its true rows are $T, T, T$, then $T, T, F$, then $T, F, T$, then $F, T, T$: one term each.`,
      r`Or shorter: any two being true is enough, and a term need not mention the third variable.`,
    ], { hide: true });
    md(r`
> [!summary]
> Every truth table has a formula: the $\lor$ of its true rows (a DNF), or the $\land$ of clauses that rule out its false rows (a CNF). The laws of logic reach the same forms from a formula without its table: NNF pushes negations onto the variables, and distributing gives CNF or DNF.
`);
    md(r`Tables and laws decide formulas about $p$ and $q$. Neither can check a statement about every number, which has infinitely many rows. The next lesson builds proofs instead, step by step, and has Lean check them.`);
  });

  add("03-natural-deduction.chalk", "Proofs as Lean tactics", "Natural deduction in Lean: what it takes to prove each connective and what you can do with one, and proofs as programs.", ({ sec, md, m, lean, lx }) => {
    sec("Proofs as Lean tactics");
    md(r`
> [!goal]
> Prove propositional statements in Lean by asking, for each connective, what it takes to prove one and what you can do with one.
`);
    md(r`A truth table checks a formula by trying every row. That stops working for "every natural number $n$ satisfies $n + 0 = n$": the rows never end. A **proof** derives a statement by rules instead, each a small step that is obviously valid, and Lean checks every step. What should the rules be?`);
    sec("What each connective needs");
    md(r`
> [!try]
> To convince someone of $p \land q$, what must you hand them? If someone hands you a proof of $p \land q$, what can you get out of it? Ask the same of $p \lor q$ and of $p \to q$ before reading on.
`);
    md(r`
- $p \land q$: hand over a proof of each, a pair. Given one, you can take either half.
- $p \lor q$: hand over a proof of one of them, saying which. Given one, you do not know which side you have, so you must finish the job in both cases.
- $p \to q$: hand over a method that turns any proof of $p$ into a proof of $q$; to build it, assume $p$ and derive $q$. Given one and a proof of $p$, apply it and get $q$.
- $\lnot p$ is $p \to \bot$: a method that turns any proof of $p$ into a contradiction.
`);
    md(r`
> [!definition] Introduction and elimination
> Natural deduction is these answers written as rules: for each connective, how to **introduce** it (prove it) and how to **eliminate** it (use it). In Lean, ‹intro› assumes the premise of $\to$, and applying ‹h hp› uses one; ‹constructor› or ‹⟨hp, hq⟩› builds $\land$, and ‹h.1›, ‹h.2› take it apart; ‹left› and ‹right› build $\lor$, and ‹cases› uses it.
`);
    lean(r`example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · exact hp
  · exact hq

example (p q : Prop) : p ∧ q → q := by
  intro h
  exact h.2

example (p q : Prop) : p → p ∨ q := by
  intro hp
  left
  exact hp`);
    md(r`Put the cursor after a tactic to see the goal it leaves: the hypotheses above the line, what is left to prove below it.`);
    sec("Exercises");
    md(r`Replace ‹sorry› with a proof. Lean checks it as you type; the exercise is done when Lean accepts it with nothing left unproved.`);
    lx(r`theorem and_swap' (p q : Prop) : p ∧ q → q ∧ p := by`, r`Prove that $\land$ commutes.`, r`  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩`, [r`‹intro ⟨hp, hq⟩› takes the conjunction apart as it introduces it.`, r`‹exact ⟨hq, hp⟩› builds the conjunction the other way round.`]);
    lx(r`theorem or_swap' (p q : Prop) : p ∨ q → q ∨ p := by`, r`Prove that $\lor$ commutes.`, r`  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq`, [r`After ‹intro h›, ‹cases h› gives two goals: one with ‹hp : p›, one with ‹hq : q›.`, r`‹Or.inr hp› proves ‹q ∨ p› from ‹p›.`]);
    lx(r`theorem modus_tollens (p q : Prop) : (p → q) → ¬q → ¬p := by`, r`Prove *modus tollens*: if $p$ implies $q$ and $q$ is false, then $p$ is false.`, r`  intro hpq hnq hp
  exact hnq (hpq hp)`, [r`‹¬p› is ‹p → False›, so ‹intro› can take a proof of ‹p› too.`, r`‹hpq hp› is a proof of ‹q›, and ‹hnq› turns it into ‹False›.`]);
    lx(r`theorem curry' (p q r : Prop) : (p ∧ q → r) → (p → q → r) := by`, r`Prove that a function of a pair can take its arguments one at a time.`, r`  intro h hp hq
  exact h ⟨hp, hq⟩`, [r`Introduce all three hypotheses, then feed ‹h› the pair.`]);
    lx(r`theorem not_or_split (p q : Prop) : ¬(p ∨ q) → ¬p ∧ ¬q := by`, r`Prove one of De Morgan's laws: if neither $p \lor q$, then not $p$ and not $q$.`, r`  intro h
  exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩`, [r`A proof of ‹¬p› is a function from ‹p› to ‹False›.`, r`Given ‹hp : p›, ‹Or.inl hp› proves ‹p ∨ q›, which ‹h› refutes.`]);
    sec("Proofs are programs");
    md(r`
> [!note] Curry–Howard
> "A method that turns any proof of $p$ into a proof of $q$" is a function, and in Lean it is one: the term ‹fun hp => h (Or.inl hp)› from the last exercise takes a proof of $p$ to a proof of $\bot$. A proof of $p \land q$ is a pair. Propositions are types and proofs are their values; checking a proof is type checking. The λ-calculus courses come back to this.
`);
    lean(r`example (p q : Prop) : p ∧ q → q ∧ p := fun ⟨hp, hq⟩ => ⟨hq, hp⟩`);
    md(r`
> [!mistake]
> It is natural to expect every tautology to have a proof by these rules. $\lnot\lnot p \to p$ is a tautology:
`);
    m("taut(¬¬p → p)");
    md(r`Yet the rules above give no proof of it. A proof of $\lnot\lnot p$ is a function that turns refutations of $p$ into contradictions, and nothing in it is evidence for $p$. It needs one more principle, the excluded middle (‹Classical.em p : p ∨ ¬p›), or proof by contradiction:`);
    lean(r`theorem dne (p : Prop) : ¬¬p → p := by
  intro h
  exact Classical.byContradiction h`);
    md(r`
> [!summary]
> Each connective's rules say what it takes to prove it and what you can do with it, and Lean's tactics are those rules. A proof of an implication is a function; a proof of a conjunction is a pair. Excluded middle is the one extra principle classical logic adds.
`);
    md(r`So far every statement was about $p$ and $q$. Most statements in mathematics are about every number, or some number. The next lesson adds $\forall$ and $\exists$.`);
  });

  add("04-quantifiers.chalk", "Predicates and quantifiers", "∀ as a long ∧ and ∃ as a long ∨: counterexamples and witnesses, negation by De Morgan, the order of quantifiers, and quantifiers in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Predicates and quantifiers");
    md(r`
> [!goal]
> Read $\forall$ as a long $\land$ and $\exists$ as a long $\lor$; find the counterexample or the witness; negate them; prove simple ones in Lean.
`);
    md(r`"Every multiple of 4 is even", "some prime is even": statements like these are about a whole set of things at once. Over a small set they are formulas you already know. "For every $n$ in $\{1, 2, 3\}$, $n^2 \ge 2n$" says three things joined by $\land$:`);
    m("∀ n ∈ {1, 2, 3}, n^2 ≥ 2n", { work: true });
    m("(1^2 ≥ 2*1) ∧ (2^2 ≥ 2*2) ∧ (3^2 ≥ 2*3)");
    md(r`
> [!definition] Quantifiers
> $\forall n \in S,\ \varphi(n)$ says $\varphi$ holds for every $n$ in $S$: over $S = \{1, 2, 3\}$ it is $\varphi(1) \land \varphi(2) \land \varphi(3)$. $\exists n \in S,\ \varphi(n)$ says it holds for at least one: $\varphi(1) \lor \varphi(2) \lor \varphi(3)$. So a $\forall$ is refuted by one false case, a **counterexample**, and an $\exists$ is proved by one true case, a **witness**.
`);
    md(r`Over a finite set the engine checks every element in order, and names the one that decided. Type ‹forall n in 1..10, …› or the glyphs; the body can compare numbers and use ‹prime›, ‹even›, ‹odd› and ‹∣› (divides).`);
    m("∀ n ∈ 1..10, n^2 ≥ n", { work: true });
    m("∀ n ∈ 1..10, n^2 ≥ 2n", { work: true });
    m("∃ n ∈ {4, 6, 9, 11}, prime(n)", { work: true });
    sec("Negation");
    md(r`
> [!try]
> What is "not every $n$ has $\varphi(n)$", written without a $\lnot$ in front? Write it as $\lnot(\varphi(1) \land \varphi(2) \land \varphi(3))$ and use De Morgan from lesson 2.
`);
    md(r`
> [!theorem] Negating a quantifier
> $\lnot \forall n,\ \varphi(n) \equiv \exists n,\ \lnot\varphi(n)$ and $\lnot \exists n,\ \varphi(n) \equiv \forall n,\ \lnot\varphi(n)$: "not every" is "some not", and "none" is "every not". It is De Morgan's law for a long $\land$ or $\lor$.
`);
    m("¬(∀ n ∈ 1..10, n^2 ≥ 2n)");
    m("∃ n ∈ 1..10, ¬(n^2 ≥ 2n)", { work: true });
    md(r`The witness of the second is the counterexample of the first: $n = 1$.`);
    sec("The order of quantifiers");
    md(r`
> [!mistake]
> Swapping two quantifiers looks harmless and is not. "Every $n$ has some $m$ different from it" is true; "some $m$ is different from every $n$" is false, since that $m$ would have to differ from itself.
`);
    m("∀ n ∈ 1..6, ∃ m ∈ 1..6, m ≠ n");
    m("∃ m ∈ 1..6, ∀ n ∈ 1..6, m ≠ n");
    md(r`Read them as a game. In $\forall n\, \exists m$ your opponent picks $n$ first and you answer with an $m$ that may depend on it. In $\exists m\, \forall n$ you must commit to one $m$ before seeing any $n$, which is harder.`);
    sec("Checking is not proving");
    md(r`
> [!mistake]
> A statement about every natural number is not proved by checking some of them. Euler noticed that $n^2 + n + 41$ is prime for $n = 1, 2, 3, \dots$, a long way:
`);
    m("∀ n ∈ 1..39, prime(n^2 + n + 41)");
    m("∀ n ∈ 1..40, prime(n^2 + n + 41)", { work: true });
    md(r`At $n = 40$ it is $40^2 + 40 + 41 = 41^2$. Thirty-nine checks passed and the fortieth failed. Checking finds counterexamples; only a proof covers every $n$.`);
    sec("Exercises");
    md(r`Answer ‹true› or ‹false›.`);
    ex("∀ n ∈ 1..20, prime(n) → odd(n)", r`Is every prime between 1 and 20 odd?`, [r`One prime is even.`]);
    ex("∃ n ∈ 3..30, n^2 = 2^n", r`Is there an $n$ between 3 and 30 with $n^2 = 2^n$?`, [r`Try small powers of 2.`]);
    ex("∀ n ∈ 1..12, 3 ∣ n^3 - n", r`Does 3 divide $n^3 - n$ for every $n$ from 1 to 12?`, [r`Factor it: $n^3 - n = (n-1)\,n\,(n+1)$. What is true of three consecutive numbers?`]);
    ex("∀ n ∈ 1..10, n^2 ≤ 2^n", r`Is $n^2 \le 2^n$ for every $n$ from 1 to 10?`, [r`Compute both sides for $n = 3$.`]);
    ex("∀ n ∈ 1..10, ∃ m ∈ 1..10, m > n", r`Play the game: for every $n$ from 1 to 10, is there an $m$ from 1 to 10 with $m > n$?`, [r`Which $n$ has no answer inside $1..10$? Over all natural numbers the answer would change.`]);
    sec("Quantifiers in Lean");
    md(r`Over all natural numbers there is no finite $\land$ to check, so Lean asks for proofs, built the way lesson 3's were. A proof of $\exists n, P(n)$ is a pair: the witness and a proof that it works. A proof of $\forall n, P(n)$ is a function taking any $n$ to a proof of $P(n)$.`);
    lean(r`example : ∃ n : Nat, n * n = 16 := ⟨4, rfl⟩

example : ∀ n : Nat, n + 0 = n := fun _ => rfl`);
    lx(r`theorem exists_sq_36 : ∃ n : Nat, n * n = 36 := by`, r`Give a witness.`, r`  exact ⟨6, rfl⟩`, [r`‹exact ⟨w, rfl⟩›, with the right ‹w›.`]);
    lx(r`theorem forall_and_left (α : Type) (P Q : α → Prop) : (∀ x, P x ∧ Q x) → ∀ x, P x := by`, r`If every $x$ has both properties, every $x$ has the first.`, r`  intro h x
  exact (h x).1`, [r`‹intro h x›, then ‹h x› is a proof of ‹P x ∧ Q x›.`]);
    lx(r`theorem not_exists_forall (α : Type) (P : α → Prop) : (¬ ∃ x, P x) → ∀ x, ¬ P x := by`, r`Prove one half of negating $\exists$: if no $x$ has $P$, every $x$ lacks it.`, r`  intro h x hx
  exact h ⟨x, hx⟩`, [r`‹¬ P x› is ‹P x → False›: introduce the proof ‹hx› too.`, r`Then ‹⟨x, hx⟩› proves the ‹∃› that ‹h› denies.`]);
    md(r`
> [!summary]
> $\forall$ is a long $\land$ and $\exists$ a long $\lor$: one counterexample refutes a $\forall$, one witness proves an $\exists$, and negation swaps them by De Morgan's law. Their order changes the meaning. Over a finite set both can be checked; over all numbers they must be proved.
`);
    md(r`Euler's polynomial passed 39 checks and still failed. How can a finite argument cover every natural number? The next lesson's answer is induction.`);
  });

  add("05-induction.chalk", "Induction on the natural numbers", "Why checking is not enough, and induction as a recipe that produces a proof for any n: dominoes, sums, and proofs in Lean.", ({ sec, md, m, ex, lean, lx, sc }) => {
    sec("Induction on the natural numbers");
    md(r`
> [!goal]
> Prove a statement for every natural number from two finite pieces: a base case and a step from $n$ to $n + 1$.
`);
    md(r`Euler's polynomial passed 39 checks before it failed. Fermat did worse: $2^{2^n} + 1$ is prime for $n = 0, 1, 2, 3, 4$ (it is 3, 5, 17, 257 and 65537), and he believed it always was.`);
    m("∀ n ∈ 0..4, prime(2^(2^n) + 1)");
    m("(2^(2^5) + 1) / 641");
    md(r`Euler found that the very next one, $2^{32} + 1 = 4294967297$, is $641 \times 6700417$. No number of checks proves a statement about every $n$. So what could?`);
    sec("A step instead of a list");
    md(r`Is $1 + 2 + \cdots + n = \dfrac{n(n+1)}{2}$? Drag ‹n› and compare.`);
    m("let n = 5", { slider: [1, 30, 1] });
    m("sum(k, k, 1, n)");
    m("n(n+1)/2");
    m("∀ n ∈ 1..20, sum(k, k, 1, n) = n(n+1)/2");
    md(r`Twenty more checks. Instead, show how each case gives the next. If the sum up to $k$ is $\frac{k(k+1)}{2}$, the sum up to $k + 1$ adds $k + 1$, and the formula should then give $\frac{(k+1)(k+2)}{2}$. The difference is zero for every $k$:`);
    m("expand(k(k+1)/2 + (k+1) - (k+1)(k+2)/2)");
    md(r`That one identity, with the case $n = 1$ ($1 = \frac{1 \cdot 2}{2}$), is a proof for every $n$. For $n = 1000$, start at 1 and apply the step 999 times: the argument is a recipe that produces the proof for any $n$ you name.`);
    sc(dominoScene);
    md(r`
> [!theorem] Induction
> If $P(0)$ holds, and $P(n)$ implies $P(n + 1)$ for every $n$, then $P(n)$ holds for every natural number $n$.
`);
    md(r`
> [!mistake]
> Both halves are needed, and the step alone can look convincing. Let $P(n)$ say $n = n + 1$. If $n = n + 1$ then, adding 1, $n + 1 = n + 2$: the step holds for every $n$. But $P(0)$ says $0 = 1$, so no domino is ever pushed, and $P(n)$ is false for every $n$.
`);
    md(r`
> [!note] Why it works
> Every $n$ is reached from $0$ by finitely many steps of $+1$. In Lean this is not an axiom but the way ‹Nat› is defined: a natural number is ‹zero› or ‹succ n›, and the ‹induction› tactic is the recursion that follows that definition.
`);
    md(r`In Lean, define the sum by recursion and prove the formula (doubled, to stay in ‹Nat›):`);
    lean(r`def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

#eval (List.range 8).map sumTo

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [sumTo, Nat.mul_add, ih]
    grind`);
    md(r`The ‹succ› case has the **induction hypothesis** ‹ih : 2 * sumTo k = k * (k + 1)› and must prove the formula for ‹k + 1›. Unfolding ‹sumTo› once and using ‹ih› leaves the identity above, which ‹grind› finishes.`);
    sec("Odd numbers");
    md(r`
> [!try]
> Add up the first few odd numbers: $1$, $1 + 3$, $1 + 3 + 5$, $1 + 3 + 5 + 7$. Guess the formula, then find its induction step in the picture.
`);
    sc(oddSquareScene);
    md(r`The sum of the first $n$ odd numbers is $n^2$, and the picture is the induction step: $n^2 + (2n + 1) = (n + 1)^2$.`);
    sec("Exercises");
    md(r`First check, then prove. Answer ‹true› or ‹false›:`);
    ex("∀ n ∈ 1..15, 2^n ≥ n + 1", r`Is $2^n \ge n + 1$ for $n$ from 1 to 15?`, []);
    ex("∀ n ∈ 1..20, sum(2k - 1, k, 1, n) = n^2", r`Is the sum of the first $n$ odd numbers $n^2$, for $n$ up to 20?`, [r`$1 = 1$, $1 + 3 = 4$, $1 + 3 + 5 = 9$.`]);
    lx(r`def oddSum : Nat → Nat
  | 0 => 0
  | n + 1 => oddSum n + (2 * n + 1)

theorem oddSum_eq (n : Nat) : oddSum n = n * n := by`, r`Prove that the sum of the first $n$ odd numbers is $n^2$.`, r`  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [oddSum, ih]
    grind`, [r`‹induction n with›, then a case for ‹zero› and one for ‹succ k ih›.`, r`In the ‹succ› case, ‹simp only [oddSum, ih]› leaves ‹k * k + (2 * k + 1) = (k + 1) * (k + 1)›: the picture's step.`]);
    lx(r`theorem lt_two_pow' (n : Nat) : n + 1 ≤ 2 ^ n := by`, r`Prove $n + 1 \le 2^n$ for every $n$.`, r`  induction n with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega`, [r`The step: from $k + 1 \le 2^k$, show $k + 2 \le 2^k \cdot 2$.`, r`‹rw [Nat.pow_succ]› turns ‹2 ^ (k + 1)› into ‹2 ^ k * 2›; then ‹omega› treats ‹2 ^ k› as a number.`]);
    md(r`
> [!summary]
> Induction proves $P(n)$ for every $n$ from a base case and a step: a recipe that builds the proof for any $n$ you name. Checking cases finds mistakes; the step is the proof. In Lean, ‹induction› splits the goal into those two cases and hands the step its hypothesis.
`);
    md(r`The step here only ever used the case just before. To show 12 has a prime factor, 11 is no help; 12's factors 2, 3, 4 and 6 are. The next lesson lets the step use any smaller case.`);
  });

  add("06-strong-induction.chalk", "Strong induction", "When the step needs more than the case before: prime factors, making change, and why strong induction, weak induction and well-ordering are one principle.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Strong induction");
    md(r`
> [!goal]
> Prove statements whose step needs any smaller case, not just the one before, and see why that is no stronger than ordinary induction.
`);
    md(r`Try ordinary induction on "every $n \ge 2$ has a prime factor". The step assumes 11 has a prime factor and must show that 12 does. That is no help: 12 is $2 \times 6$, and the cases that help are its factors, which can be anywhere below it.`);
    md(r`The fix is to assume more. When proving $P(n)$, assume $P(m)$ for every $m < n$, not only for $n - 1$:`);
    md(r`
> [!theorem] Strong induction
> If, for every $n$, $P(m)$ for all $m < n$ implies $P(n)$, then $P(n)$ holds for every $n$.
`);
    md(r`There is no separate base case: for $n = 0$ the hypothesis is about no numbers at all, so $P(0)$ must be proved outright, and the same happens for any $n$ the argument cannot reduce.`);
    sec("Every number has a prime factor");
    md(r`
> [!example] Prime factors
> Every $n \ge 2$ has a prime factor. If $n$ is prime, it is its own. If not, $n = ab$ with $2 \le a < n$, and $a$ has a prime factor by the hypothesis for $a$, which divides $n$ too. The step uses the case $a$, which can be any number below $n$, not $n - 1$.
`);
    m("∀ n ∈ 2..60, ∃ p ∈ 2..n, prime(p) ∧ p ∣ n");
    sec("Postage stamps");
    md(r`
> [!try]
> With stamps of 3 and 5, which amounts can you make exactly, and which not? Find the largest one you cannot make before reading on.
`);
    m("∀ n ∈ 8..40, ∃ a ∈ 0..14, ∃ b ∈ 0..8, n = 3a + 5b");
    m("∃ a ∈ 0..3, ∃ b ∈ 0..2, 7 = 3a + 5b");
    md(r`7 cannot be made; every amount from 8 on can. Make 8, 9 and 10 directly, and any $n \ge 11$ from $n - 3$ plus one stamp of 3. The step reaches back three, to a case strong induction lets it use, so it needs three base cases.`);
    lean(r`theorem stamps (n : Nat) (h : 8 ≤ n) : ∃ a b, n = 3 * a + 5 * b := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    if h8 : n = 8 then exact ⟨1, 1, by omega⟩
    else if h9 : n = 9 then exact ⟨3, 0, by omega⟩
    else if h10 : n = 10 then exact ⟨0, 2, by omega⟩
    else
      obtain ⟨a, b, hab⟩ := ih (n - 3) (by omega) (by omega)
      exact ⟨a + 1, b, by omega⟩`);
    md(r`‹induction n using Nat.strongRecOn› gives ‹ih : ∀ m < n, 8 ≤ m → ∃ a b, …›: the statement for every smaller ‹m›.`);
    sec("Fibonacci numbers");
    lean(r`def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

#eval (List.range 12).map fib`);
    md(r`Each Fibonacci number uses the two before it, so a proof about them uses two earlier cases, and needs two base cases.`);
    lx(r`theorem fib_lt_two_pow (n : Nat) : fib n < 2 ^ n := by`, r`Prove $F_n < 2^n$ by strong induction.`, r`  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | k + 2 =>
      have h1 := ih k (by omega)
      have h2 := ih (k + 1) (by omega)
      rw [fib, Nat.pow_succ, Nat.pow_succ]
      rw [Nat.pow_succ] at h2
      omega`, [
      r`Start with ‹induction n using Nat.strongRecOn with | _ n ih => ›, then ‹match n with› for ‹0›, ‹1› and ‹k + 2›.`,
      r`For ‹k + 2›: ‹ih k (by omega)› and ‹ih (k + 1) (by omega)› are the two earlier cases.`,
      r`$F_k + F_{k+1} < 2^k + 2^{k+1} \le 2^{k+2}$. Rewrite the powers with ‹Nat.pow_succ› so ‹omega› sees ‹2 ^ k› as one number.`,
    ]);
    sec("Three forms of one principle");
    md(r`Strong induction assumes more, so it looks stronger. It is not:`);
    md(r`
> [!theorem] Weak induction, strong induction, well-ordering
> These are equivalent: each proves the others.
>
> - Strong induction gives weak: its hypothesis includes the case $n - 1$.
> - Weak gives strong: apply weak induction to $Q(n)$ = "$P(m)$ for every $m < n$".
> - Well-ordering (every non-empty set of naturals has a least element) gives strong induction: if $P$ failed somewhere, take the least $n$ where it fails; $P$ holds below $n$, so the step gives $P(n)$, a contradiction.
`);
    md(r`The last form is the one lesson 9 generalizes: induction works along any relation with no infinite descending chain.`);
    sec("Exercises");
    ex("∀ n ∈ 12..50, ∃ a ∈ 0..12, ∃ b ∈ 0..10, n = 4a + 5b", r`With stamps of 4 and 5, can every amount from 12 to 50 be made exactly? Answer ‹true› or ‹false›.`, [r`12, 13, 14 and 15 directly; then reach back by 4.`]);
    ex("∃ a ∈ 0..3, ∃ b ∈ 0..3, 11 = 4a + 5b", r`Can 11 be made from stamps of 4 and 5? Answer ‹true› or ‹false›.`, [r`Try $b = 0, 1, 2$.`]);
    md(r`
> [!try]
> The largest amount that cannot be made is 7 with stamps of 3 and 5, and 11 with stamps of 4 and 5. Guess the rule for stamps of $a$ and $b$ with no common factor, and test it on 3 and 7.
`);
    md(r`It is $ab - a - b$ (Sylvester, 1884): $15 - 8 = 7$, $20 - 9 = 11$, and $21 - 10 = 11$ for 3 and 7.`);
    md(r`
> [!summary]
> Strong induction lets the step use every smaller case, with as many base cases as the step reaches back. It proves nothing ordinary induction cannot, but it fits arguments that split $n$ into smaller pieces.
`);
    md(r`Natural numbers are built from $0$ by $+1$, and induction follows that construction. Lists and trees are built too, from smaller lists and trees. The next lesson gives them their own induction.`);
  });

  add("07-structural-induction.chalk", "Structural induction", "The same idea for anything defined by constructors: lists, trees, expressions, and a small simplifier proved sound.", ({ sec, md, lean, lx }) => {
    sec("Structural induction");
    md(r`
> [!goal]
> Prove properties of recursive data (lists, trees, expressions) by induction on how they are built, and prove a small program transformation correct.
`);
    md(r`Lesson 5 said Lean's induction on ‹Nat› is not an axiom: it comes from how ‹Nat› is built, from ‹zero› by ‹succ›. A base case for ‹zero›, a step for ‹succ›. Other types are built the same way. A list is either empty, ‹[]›, or an element in front of a shorter list, ‹x :: xs›.`);
    md(r`
> [!try]
> Guess the induction principle for lists: what must you prove to know $P$ holds for every list?
`);
    md(r`
> [!definition] Structural induction
> A type defined by constructors has an induction principle with a case per constructor, and a hypothesis for each recursive part. For lists: prove $P([\,])$, and $P(xs) \to P(x :: xs)$ for every $x$ and $xs$. Natural numbers are the special case ‹zero› and ‹succ n›.
`);
    sec("Lists");
    lean(r`def len {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => len xs + 1

theorem len_append {α : Type} (xs ys : List α) : len (xs ++ ys) = len xs + len ys := by
  induction xs with
  | nil => simp [len]
  | cons x xs ih => simp [len, ih]; omega`);
    md(r`Induction is on ‹xs›, the list that ‹++› recurses on: ‹(x :: xs) ++ ys = x :: (xs ++ ys)›, which is exactly where the hypothesis applies. Induction on ‹ys› would get stuck, since ‹++› does nothing with ‹ys› until ‹xs› runs out.`);
    sec("Trees");
    lean(r`inductive Tree where
  | leaf
  | node (l : Tree) (v : Nat) (r : Tree)

def Tree.mirror : Tree → Tree
  | .leaf => .leaf
  | .node l v r => .node r.mirror v l.mirror

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size`);
    md(r`
> [!try]
> A ‹node› is built from two smaller trees. How many induction hypotheses should its case get?
`);
    md(r`Two, one for each subtree: the recipe needs the property for both parts before it can build it for the whole.`);
    lx(r`theorem Tree.mirror_mirror (t : Tree) : t.mirror.mirror = t := by`, r`Mirroring twice gives back the tree.`, r`  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [Tree.mirror, ihl, ihr]`, [r`‹induction t with | leaf => … | node l v r ihl ihr => …›.`, r`In the ‹node› case, unfold ‹Tree.mirror› and use both hypotheses: ‹simp [Tree.mirror, ihl, ihr]›.`]);
    lx(r`theorem Tree.size_mirror (t : Tree) : t.mirror.size = t.size := by`, r`Mirroring keeps the size.`, r`  induction t with
  | leaf => rfl
  | node l v r ihl ihr => simp [Tree.mirror, Tree.size, ihl, ihr]; omega`, [r`As before, but ‹simp› leaves the sizes of the two sides in the other order: ‹omega› swaps them.`]);
    sec("A simplifier, proved sound");
    md(r`Expressions are trees too. Here is a tiny language of sums and products, what an expression means, and a simplifier that removes additions of zero:`);
    lean(r`inductive Ex where
  | num (n : Nat)
  | add (a b : Ex)
  | mul (a b : Ex)

def Ex.eval : Ex → Nat
  | .num n => n
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval

def Ex.simp : Ex → Ex
  | .add a b =>
    match a.simp, b.simp with
    | .num 0, b' => b'
    | a', .num 0 => a'
    | a', b' => .add a' b'
  | .mul a b => .mul a.simp b.simp
  | e => e

#eval (Ex.add (.num 0) (.mul (.num 3) (.add (.num 4) (.num 0)))).simp.eval`);
    md(r`
> [!note] Soundness is a fold
> A simplifier is **sound** when it never changes what an expression means. Checking examples cannot show that, for the reason lesson 4 gave; structural induction can: if simplifying the parts keeps their values, simplifying the whole does. ChalkMath's engine argues the same way: a rewrite rule proved to keep the value keeps it inside any larger term, by a structural induction, and the dot on a step says whether its rule has such a proof.
`);
    lx(r`theorem Ex.simp_sound (e : Ex) : e.simp.eval = e.eval := by`, r`Prove the simplifier sound: it keeps the value of every expression.`, r`  induction e with
  | num n => rfl
  | add a b iha ihb =>
    simp only [Ex.simp]
    split <;> simp_all [Ex.eval]
  | mul a b iha ihb => simp [Ex.simp, Ex.eval, iha, ihb]`, [
      r`Induction on ‹e›: three cases, and ‹add› and ‹mul› each get two hypotheses.`,
      r`In the ‹add› case, ‹simp only [Ex.simp]› exposes the ‹match›, and ‹split› gives one goal per branch.`,
      r`Each branch knows what ‹a.simp› and ‹b.simp› are; ‹simp_all [Ex.eval]› combines that with the hypotheses.`,
    ]);
    md(r`
> [!summary]
> Every inductive type comes with its own induction: a case per constructor and a hypothesis per recursive part. Lists, trees and syntax trees are proved about the same way as numbers, and "a transformation keeps the meaning" is a structural induction.
`);
    md(r`Every induction so far ran along a relation: "is one less than", "is less than", "is a part of". Which relations can induction run along? First, relations themselves, and what it means to close one up.`);
  });

  add("08-relations.chalk", "Relations", "When do two things count as the same? Properties with counterexamples, closures as what you are forced to add, equivalence classes, and a deduplication bug.", ({ sec, md, m, ex }) => {
    sec("Relations");
    md(r`
> [!goal]
> Decide the properties of a relation and point to the pairs that break them; compute closures; read an equivalence relation as a partition.
`);
    md(r`A service receives requests and drops duplicates. One day an action goes missing: a request was dropped as a duplicate when it was not one. Which requests should count as "the same"? The answer is a relation, and the bug, at the end of this lesson, is a fact about two relations.`);
    md(r`
> [!definition] Relation
> A **relation** on a set $S$ is a set of pairs $(x, y)$ of elements of $S$; write $x \mathrel{R} y$ when $(x, y)$ is one of them. Draw it as a graph: an arrow from $x$ to $y$ for each pair.
`);
    m("let R = rel({a, b, c}; a->b, b->c, b->b)");
    sec("Properties");
    md(r`"Is the same as" has three properties anyone would insist on: everything is the same as itself; if $x$ is the same as $y$, then $y$ is the same as $x$; and two things the same as a third are the same as each other. "Is at most" keeps the first and the third, and turns the second around: $x \le y$ and $y \le x$ together only when $x = y$.`);
    md(r`
> [!definition] Reflexive, symmetric, antisymmetric, transitive
> $R$ is **reflexive** when $x \mathrel{R} x$ for every $x$; **symmetric** when $x \mathrel{R} y$ gives $y \mathrel{R} x$; **antisymmetric** when $x \mathrel{R} y$ and $y \mathrel{R} x$ give $x = y$; **transitive** when $x \mathrel{R} y$ and $y \mathrel{R} z$ give $x \mathrel{R} z$.
`);
    md(r`Each is a $\forall$, so each falls to one counterexample: a failed check names the element or the pairs that break it, and the graph marks them.`);
    m("reflexive(R)", { work: true });
    m("symmetric(R)", { work: true });
    m("antisymmetric(R)");
    m("transitive(R)", { work: true });
    sec("Closures");
    md(r`
> [!try]
> $P$ below has $a \to b$, $b \to c$ and $c \to d$. If $P$ has to be transitive, which pairs are you forced to add? Is one round of adding enough?
`);
    m("let P = rel({a, b, c, d}; a->b, b->c, c->d)");
    md(r`Step through it: each round adds the pairs that the last round's pairs force. The added pairs are dashed.`);
    m("closure(P, transitive)", { step: 0 });
    md(r`One round is not enough: $(a, d)$ is forced only once $(a, c)$ is there. The rounds stop when nothing new is forced.`);
    md(r`
> [!definition] Closure
> The **transitive closure** of $R$ is the least transitive relation containing it: what you are forced to add, and nothing more. The reflexive and symmetric closures add the pairs $(x, x)$ and the reverse pairs.
`);
    md(r`
> [!theorem] The closure is the least
> Every pair a round adds lies in any transitive relation containing $R$, and the rounds stop only when the relation is transitive. So the result is transitive and inside every transitive relation containing $R$. Both facts are proved in Lean (the dot on each step).
`);
    sec("Equivalence relations and partitions");
    md(r`
> [!definition] Equivalence relation, class, partition
> An **equivalence relation** is reflexive, symmetric and transitive: it says when two elements count as the same. The **class** of $x$ is everything related to it, the classes **partition** the set (every element in exactly one), and the set of classes is the **quotient** $S/{\sim}$.
`);
    md(r`The commonest way to get one: give each element a label, and relate two elements when their labels are equal. That is the **kernel** of the labelling. It is an equivalence for free, because equality of labels is.`);
    m("let K = kernel({r1, r2, r3, r4}; r1->k1, r2->k1, r3->k2, r4->k2)");
    m("equivalence(K)");
    m("classes(K)", { work: true });
    md(r`A relation that is not an equivalence has a closure that is one: everything it is forced to identify.`);
    m("let E = closure(R, equivalence)");
    m("classes(E)");
    sec("Finer and coarser");
    md(r`
> [!definition] Refinement
> $A$ is **finer** than $K$ when every pair of $A$ is a pair of $K$: each class of $A$ lies inside a class of $K$. Then $K$ is **coarser**, and merges more.
`);
    md(r`
> [!example] Deduplicating by key
> Back to the service. Requests $r_1$ and $r_2$ carry key $k_1$ and the same action; $r_3$ and $r_4$ carry key $k_2$ but different actions. Deduplicating by key treats two requests as the same when their keys are equal: the relation $K$ above. What should count as the same is the same key *and* the same payload: the relation $A$.
`);
    m("let A = kernel({r1, r2, r3, r4}; r1->a, r2->a, r3->b, r4->c)");
    m("finer(A, K)", { work: true });
    m("finer(K, A)", { work: true });
    md(r`$K$ is strictly coarser: it merges $r_3$ and $r_4$, which $A$ keeps apart. Dropping $r_4$ as a duplicate of $r_3$ loses an action: the bug. Deduplication is safe exactly when the relation it uses is finer than "same request".`);
    sec("Exercises");
    md(r`Answer properties with ‹true› or ‹false›. Write a relation's pairs as ‹a->b, b->c› (in any order), and classes as ‹{a, b}, {c}›.`);
    m("let S = rel({1, 2, 3}; 1->2, 2->1, 2->3)");
    ex("symmetric(S)", r`Is $S$ symmetric?`, [r`Look for a pair whose reverse is missing.`]);
    ex("closure(S, transitive)", r`Write the transitive closure of $S$: all its pairs.`, [
      r`$1 \to 2 \to 1$ forces $(1, 1)$; $2 \to 1 \to 2$ forces $(2, 2)$; $1 \to 2 \to 3$ forces $(1, 3)$.`,
      r`Then check again: do the new pairs force any more?`,
    ]);
    m("let T = kernel({a, b, c, d, e}; a->x, b->y, c->x, d->y, e->z)");
    ex("classes(T)", r`Write the classes of $T$.`, [r`Group the elements by their label.`]);
    m("let U = kernel({a, b, c, d, e}; a->p, b->p, c->p, d->q, e->q)");
    ex("finer(T, U)", r`Is $T$ finer than $U$: does every class of $T$ lie inside a class of $U$?`, [r`Write out the classes of $U$, then look at the class of $T$ that contains $b$.`]);
    md(r`
> [!summary]
> A relation's properties are checked pair by pair, and a failure is a pair you can point at. A closure adds exactly what a property forces. An equivalence relation is a partition, and comparing two of them (finer, coarser) is how you find out which things get merged that should not be.
`);
    md(r`Induction ran along "one less than" and "is a part of", and both have a property the next lesson names: you cannot step down them forever. Which relations have it, and how do you prove that one does?`);
  });

  add("09-well-founded.chalk", "Well-founded relations and termination", "No infinite descent: why a loop stops, cycles as counterexamples, measures as proofs, and termination in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Well-founded relations and termination");
    md(r`
> [!goal]
> Recognize a relation with no infinite descent, prove it has none with a measure, and prove that recursive functions terminate.
`);
    md(r`Euclid's algorithm replaces $(a, b)$ by $(b, a \bmod b)$ until $b = 0$: $(48, 18)$, $(18, 12)$, $(12, 6)$, $(6, 0)$. Why does it stop for every input, not just this one? The second number goes down at every step, since $a \bmod b < b$, and a natural number cannot go down forever.`);
    md(r`
> [!definition] Well-founded
> Read $x \mathrel{R} y$ as "$x$ steps to $y$". $R$ is **well-founded** when there is no infinite chain of steps $x_0 \mathrel{R} x_1 \mathrel{R} x_2 \mathrel{R} \cdots$. On a finite set that means exactly: no cycle.
`);
    md(r`This is what made the induction lessons work. Induction is valid along any well-founded relation: if $P$ failed somewhere, the step would point to a smaller place where it fails, and to a smaller one from there, an infinite descent. $<$ on $\mathbb{N}$ is lesson 6's case, and "is a part of" lesson 7's.`);
    m("let R = rel({a, b, c, d}; a->b, b->c, a->c, c->d)");
    m("wellfounded(R)", { work: true });
    m("let C = rel({x, y, z}; x->y, y->z, z->x)");
    m("wellfounded(C)", { work: true });
    sec("Measures");
    md(r`On a big or infinite set you cannot follow every chain. Do what the Euclid argument did: find a number that goes down at every step.`);
    md(r`
> [!theorem] A measure proves termination
> If a function $m$ to the natural numbers goes down along every step ($x \mathrel{R} y$ gives $m(y) < m(x)$), $R$ is well-founded: an infinite chain of steps would be an infinite decreasing chain of natural numbers.
`);
    m("measure(R; a->3, b->2, c->1, d->0)", { work: true });
    m("measure(R; a->3, b->2, c->2, d->0)", { work: true });
    md(r`
> [!try]
> Find a measure for the cycle $C$: numbers for $x$, $y$ and $z$ that go down along all three steps.
`);
    m("measure(C; x->2, y->1, z->0)", { work: true });
    md(r`There is none: going round the cycle would come back to the same value, having gone down at every step. The measure has to land in the natural numbers, too. Into the integers, $0, -1, -2, \dots$ goes down forever, and so does $1, \frac12, \frac14, \dots$ in the rationals: a measure is only as good as the order it lands in.`);
    sec("Termination in Lean");
    md(r`Lean accepts a recursive definition only when it can see that it stops. Structural recursion (on a smaller part) it checks itself; otherwise it asks for a measure with ‹termination_by› and, if needed, a proof that each call decreases it with ‹decreasing_by›. Here is Euclid's algorithm with its measure:`);
    lean(r`def gcd' (a b : Nat) : Nat :=
  if _h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

#eval gcd' 48 18`);
    md(r`Some functions have no single number that goes down. Ackermann's function calls itself with $m$ smaller and $n$ anything, or with $m$ the same and $n$ smaller:`);
    md(r`
> [!definition] Lexicographic order
> Pairs are compared by their first components, and by the second only when the first are equal, as words are in a dictionary. It is well-founded when both orders are, even though the second component can grow without bound whenever the first goes down.
`);
    lean(r`def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

#eval ack 2 3`);
    md(r`In every call either $m$ goes down, or $m$ stays and $n$ goes down. No single number measures it, but the pair does.`);
    sec("Exercises");
    m("let G = rel({s, t, u, v}; s->t, t->u, u->s, u->v)");
    ex("wellfounded(G)", r`Is $G$ well-founded? Answer ‹true› or ‹false›.`, [r`Follow the arrows from $s$.`]);
    m("let H = rel({1, 2, 3, 4, 5}; 5->3, 3->1, 4->2, 5->4, 2->1)");
    ex("measure(H; 1->0, 2->1, 3->1, 4->2, 5->2)", r`Does the measure $1 \mapsto 0$, $2 \mapsto 1$, $3 \mapsto 1$, $4 \mapsto 2$, $5 \mapsto 2$ go down along every step of $H$? Answer ‹true› or ‹false›.`, [r`Check each arrow: the number at its head must be smaller than at its tail.`]);
    lx(r`theorem half_lt (n : Nat) (h : 0 < n) : n / 2 < n := by`, r`Halving a positive number makes it smaller: the measure argument for binary search.`, r`  omega`, [r`‹omega› knows about division by a numeral.`]);
    md(r`
> [!note] The engine's own termination proof
> ChalkMath's simplifier never runs on a step budget. Every rule in its pipeline decreases a well-founded ordering on terms: proved in Lean (‹pipelineOrdered›), or, for rules that hand the work to code the ordering cannot see into (commands, matrix arithmetic), checked on each output. It is the same argument as a measure, only the measure is an ordering on expression trees.
`);
    md(r`
> [!summary]
> Well-founded means no infinite descent; on a finite set, no cycle. A measure into the naturals proves it, a cycle refutes it, and Lean's ‹termination_by› is a measure written down. Every induction in this course ran along a well-founded relation.
`);
  });
}, { leanPrelude: true });

// ---------------------------------------------------------------------------------------------------
// Course 2. Lessons 1–4 are the chapters of notebooks/order-lattices.chalk (From Zero to Propagators,
// Part I), split at its section headings; each carries the earlier chapters' `let` cells it reads.
const book = JSON.parse(readFileSync(new URL("../../notebooks/order-lattices.chalk", import.meta.url), "utf8")).cells;
const at = (prefix) => book.findIndex((c) => c.type === "section" && c.src.startsWith(prefix));
const chapters = [[at("1 ·"), at("2 ·")], [at("2 ·"), at("3 ·")], [at("3 ·"), at("4 ·")], [at("4 ·"), at("Where Part II goes")]];
/** A notebook cell as a lesson's: its source and how it is shown, without saved outputs. */
const fresh = (c) => ({ src: c.src, ...(c.type ? { type: c.type } : {}), showWork: !!c.showWork, label: null,
  ...(c.stepwise !== undefined ? { stepwise: c.stepwise } : {}), ...(c.slider ? { slider: c.slider, mode: c.mode ?? "raw" } : {}) });
/** Lesson 11's reachability step on the subsets of {a, b, c, d}: S ↦ {a} ∪ S ∪ succ(S), edges a→b, b→c, d→a. */
const reachMap = "{}->{a}, {a}->{a,b}, {b}->{a,b,c}, {c}->{a,c}, {d}->{a,d}, {a,b}->{a,b,c}, {a,c}->{a,b,c}, {a,d}->{a,b,d}, {b,c}->{a,b,c}, {b,d}->{a,b,c,d}, {c,d}->{a,c,d}, {a,b,d}->{a,b,c,d}, {a,c,d}->{a,b,c,d}, {b,c,d}->{a,b,c,d}";
/** The same step from d: S ↦ {d} ∪ S ∪ succ(S). */
const reachFromD = "{}->{d}, {a}->{a,b,d}, {b}->{b,c,d}, {c}->{c,d}, {d}->{a,d}, {a,b}->{a,b,c,d}, {a,c}->{a,b,c,d}, {a,d}->{a,b,d}, {b,c}->{b,c,d}, {b,d}->{a,b,c,d}, {c,d}->{a,c,d}, {a,b,c}->{a,b,c,d}, {a,b,d}->{a,b,c,d}, {a,c,d}->{a,b,c,d}, {b,c,d}->{a,b,c,d}";
const letName = (src) => /^\s*let\s+([A-Za-z_][A-Za-z0-9_]*)\s*=/.exec(src)?.[1];
/** The `let` cells of chapters before `k` that chapter `k`'s math cells read (with what they read), in order. */
function carried(k) {
  const earlier = book.slice(0, chapters[k][0]).filter((c) => !c.type && letName(c.src));
  const defs = new Map(earlier.map((c) => [letName(c.src), c]));
  const need = new Set();
  const want = (src, bound) => {
    for (const id of src.match(/\b[A-Za-z_][A-Za-z0-9_]*\b/g) ?? []) {
      if (defs.has(id) && !bound.has(id) && !need.has(id)) { need.add(id); want(defs.get(id).src.replace(/^\s*let\s+\w+\s*=/, ""), bound); }
    }
  };
  const bound = new Set();
  for (const c of book.slice(...chapters[k])) {
    if (c.type) continue;
    want(c.src.replace(/^\s*let\s+\w+\s*=/, ""), bound);
    const n = letName(c.src); if (n) bound.add(n);
  }
  return earlier.filter((c) => need.has(letName(c.src)));
}
/** Chapter `k` as lesson cells: its heading, the goal, the lesson's own opening (`opening(L)` writes it: the
 *  question the chapter answers), the cells the earlier chapters left, then the chapter. */
function chapter(L, k, goal, opening = () => {}) {
  const cells = book.slice(...chapters[k]).map(fresh);
  L.cells.push(cells[0]);
  L.md(goal);
  opening(L);
  const prior = carried(k);
  if (prior.length) {
    L.md(r`From the earlier lessons, the names this one uses:`);
    for (const c of prior) L.cells.push(fresh(c));
  }
  L.cells.push(...cells.slice(1));
}

course("order-lattices", "Order and lattices",
  "From Zero to Propagators: partial orders, lattices and fixed points; semilattices as merges, access decisions and information flow; Galois connections; and propagator networks in Lean, ending with a Sudoku solver.",
  "Discrete mathematics", (add) => {

  /** The permissions on a file: the first picture of an order in which two things need not compare. */
  const perm = "let Perm = poset({none, read, write, rw}; none < read, none < write, read < rw, write < rw)";

  add("01-partial-orders.chalk", "Relations and partial orders", "What \"at most\" has to mean: partial orders on numbers, divisibility and sets, Hasse diagrams, and the definitions in Lean.", (L) => {
    chapter(L, 0, r`
> [!goal]
> Say exactly what "at most" must mean, recognise a partial order (divisibility, subsets, chains), read its Hasse diagram, and state the definition in Lean.
`, ({ md, m }) => {
      md(r`Some things line up: ages, prices, dates. Many things we still call "more" or "later" do not.

- Two people edit copies of a document offline. Each copy is later than the one they started from, but neither is later than the other.
- Permission to read and permission to write are each more than no permission and less than both, yet neither is more than the other.
- $4$ and $6$ both divide $12$, but neither divides the other.

Here are the permissions as an order. The engine draws it with "more" upwards, one edge for each step up:`);
      m(perm);
      m("le(Perm, read, write)", { work: true });
      md(r`
> [!try]
> What is the least a relation "$x$ is at most $y$" must satisfy to deserve the name? Make a list before reading on.

Three properties come up, and the chapter below names them. Everything is at most itself (**reflexive**). "At most" passes along: $x \le y$ and $y \le z$ give $x \le z$ (**transitive**). And if $x \le y$ and $y \le x$, then $x$ and $y$ are the same thing (**antisymmetric**), or else "at most" could not tell them apart. "Any two can be compared" is not on the list. Leaving it off is the point: it is what *partial* means.
`);
      md(r`
> [!note] Reading the cells
> Turn on **show work** (the ▸ beside a cell) to see how the engine decided an answer. The Lean cells are the book's definitions and proofs, checked by Lean 4 in your browser; with the cursor inside a proof, the **Lean goals** tab shows what is left to prove. The first time, Lean is a large download (about 140 MB, kept afterwards), so the Lean cells can take a minute while the engine's cells already answer.
`);
    });
    L.sec("Exercises");
    L.md(r`Answer ‹true› or ‹false›, or with an element or a set.`);
    L.ex("le(D, 4, 12)", r`In the divisors of 12, is $4 \le 12$?`, [r`$a \le b$ here means $a$ divides $b$.`]);
    L.ex("le(D, 4, 6)", r`In the divisors of 12, is $4 \le 6$?`, [r`Does 4 divide 6?`]);
    L.ex("le(P3, {a}, {a, b})", r`Among the subsets of $\{a, b, c\}$, is $\{a\} \le \{a, b\}$?`, [r`The order is inclusion.`]);
    L.md(r`Why antisymmetry? Ann and Bob are the same age and Cy is older. Here is "is no older than" as a relation, each arrow $x \to y$ read "$x$ is no older than $y$":`);
    L.m("let Age = rel({ann, bob, cy}; ann->ann, bob->bob, cy->cy, ann->bob, bob->ann, ann->cy, bob->cy)");
    L.ex("antisymmetric(Age)", r`Is ‹Age› antisymmetric?`, [
      r`Ann is no older than Bob, and Bob is no older than Ann. Are they the same person?`,
      r`‹Age› is reflexive and transitive but not antisymmetric: a *preorder*. It orders ages, not people; treat people of the same age as one element and it becomes a partial order.`,
    ]);
    L.md(r`
> [!summary]
> A partial order is reflexive, antisymmetric and transitive; not every two elements need be comparable. Divisibility, inclusion and $\le$ on numbers are the first examples, and a Hasse diagram draws one by its covers.

Without comparability two elements may have no larger one: neither read nor write is above the other. What takes the place of "the larger of the two" is the next lesson's question.
`);
  });

  add("02-special-elements.chalk", "Special elements and monotone maps", "What replaces \"the larger of two\": bounds, joins and meets, when they fail to exist, and maps that respect the order.", (L) => {
    chapter(L, 1, r`
> [!goal]
> Find what replaces "the larger of two" in a partial order, the join, see when it does not exist, and tell a monotone map from one that is not.
`, ({ md, m }) => {
      md(r`Any two numbers have a larger one, $\max(x, y)$. Read and write have none: neither is above the other. What is the best substitute?

> [!try]
> Before running the cell: what should "read combined with write" be, and what makes it *the* answer rather than just *an* answer?`);
      m(perm);
      m("join(Perm, read, write)", { work: true });
      md(r`It must be above both: an **upper bound**. Of the upper bounds it should be the least, so that it adds nothing neither side asked for: the **least upper bound**, or **join**, $\mathrm{read} \vee \mathrm{write} = \mathrm{rw}$. Merging what two people know works the same way: the least state of knowledge that contains both. The chapter makes this precise, and finds posets where no least upper bound exists, one of them in a published figure that claims otherwise.

It ends with the maps that respect an order, **monotone** maps: give one more, and it gives back more. They are the maps whose fixed points the later lessons compute.`);
    });
    L.sec("Exercises");
    L.ex("upper(E, {c, d})", r`List the upper bounds of $c$ and $d$ in $E$.`, [r`Everything above both $c$ and $d$.`]);
    L.ex("minimal(T)", r`List the minimal elements of $T$.`, [r`Nothing is strictly below a minimal element.`]);
    L.ex("join(D, 4, 6)", r`In the divisors of 12, what is $4 \vee 6$?`, [r`The least common multiple.`]);
    L.ex("monotone(D, k)", r`Is the map ‹k› monotone? Answer ‹true› or ‹false›.`, [r`‹k› sends 2 to 3 and fixes everything else. Look at $2 \le 4$.`]);
    L.md(r`
> [!summary]
> A maximum is above everything; a maximal element has nothing above it. The join of two elements is their least upper bound, when there is one. A monotone map keeps the order.

Every two divisors of 12 have a join and a meet; the vee's two upper elements have no join, and $c$ and $d$ in $E$ have none either. Posets in which every pair has both are lattices: next.
`);
  });

  add("03-lattices.chalk", "Lattices", "Posets where every pair has a join and a meet: duality, the standard examples, and distributivity.", (L) => {
    chapter(L, 2, r`
> [!goal]
> Decide whether a poset is a lattice, compute in the standard ones (Booleans, powersets, divisors), and see duality and the two lattices that are not distributive.
`, ({ md, m }) => {
      md(r`The join answers "the least thing that contains both", when there is one. A merge that sometimes has no answer is no use to a program, so ask for posets where every pair has a join, and also a **meet**: the greatest thing below both, what two states have in common.

> [!try]
> Predict, then check below: which of these is a lattice? The permissions diamond; the vee, $a < b$ and $a < c$; the divisors of 12.`);
      m(perm);
      m("lattice(Perm)", { work: true });
    });
    L.sec("Exercises");
    L.ex("lattice(V)", r`Is the "vee" $V$ a lattice?`, [r`Do $b$ and $c$ have a join?`]);
    L.ex("meet(D, 4, 6)", r`In the divisors of 12, what is $4 \wedge 6$?`, [r`The greatest common divisor.`]);
    L.ex("join(Dop, 4, 6)", r`In the dual of the divisors of 12, what is $4 \vee 6$?`, [r`In the dual, joins are the original meets.`]);
    L.md(r`
> [!summary]
> A lattice has every pairwise join and meet. Turning the order upside down swaps them (duality). Booleans, powersets and divisors are lattices; the vee is not, and M₃ and N₅ are lattices that fail the distributive law.

In a lattice any two elements can be merged. Next, a map applied again and again until nothing changes: when that stops, and where.
`);
  });

  add("04-fixed-points.chalk", "Complete lattices and fixed points", "Apply until nothing changes: complete lattices, the Knaster–Tarski theorem, and least fixed points by iteration.", (L) => {
    chapter(L, 3, r`
> [!goal]
> See why "apply until nothing changes" stops and what it finds: the least fixed point of a monotone map, by Knaster–Tarski in general and by iterating from the bottom on a finite lattice.
`, ({ md }) => {
      md(r`Many computations are a loop: apply a rule, then again, until nothing changes. Closing a set of facts under some rules, finding everything reachable from a start, solving constraints. Two questions decide whether such a loop is any good: does it stop, and does its answer depend on accidents such as where it started?

> [!try]
> Take the map on the divisors of 12 that sends $1 \mapsto 2$ and $3 \mapsto 6$ and fixes the rest (‹f› below). Start at $1$ and apply it until nothing changes; then start at $12$. Do you land in the same place? Which elements does it not move at all?`);
    });
    L.sec("Exercises");
    L.ex("lfp(D, f)", r`What is the least fixed point of ‹f›?`, [r`Start at $\bot = 1$ and apply ‹f› until nothing changes.`]);
    L.ex("gfp(D, f)", r`And the greatest?`, [r`Start at $\top = 12$.`]);
    L.ex("fixpoints(D, one)", r`List the fixed points of ‹one›, the map sending everything to 1.`, []);
    L.md(r`A new map: ‹tri› multiplies by 3 where the product is still a divisor of 12, and fixes the rest.`);
    L.m("let tri = map(D; 1 -> 3, 2 -> 6, 4 -> 12)");
    L.ex("lfp(D, tri)", r`Iterate by hand from $\bot$: what is the least fixed point of ‹tri›?`, [r`$1 \mapsto 3$, and then?`, r`‹tri› is monotone (check it with ‹monotone(D, tri)›), so where the chain stops is the least fixed point.`]);
    L.md(r`
> [!summary]
> On a complete lattice every monotone map has a least and a greatest fixed point (Knaster–Tarski). With a bottom and no infinite ascending chains, on any finite lattice for instance, the least one is reached by iterating from $\bot$. Monotonicity makes the chain climb: $\bot \le f(\bot)$, and $f^n(\bot) \le f^{n+1}(\bot)$ gives $f^{n+1}(\bot) \le f^{n+2}(\bot)$. Finite height means it can climb only finitely often. Where it stops is a fixed point, and below every other one.

So far a join was found by searching a picture. Next, turned around: the join as an operation, a way of merging two states, and the laws any such merge must obey.
`);
  });

  add("05-semilattices.chalk", "Semilattices: the laws of a merge", "Messages arrive in any order, grouped any way, twice: the three laws a merge needs, and the order every such merge hides.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Semilattices: the laws of a merge");
    md(r`
> [!goal]
> Derive the three laws a merge must obey from the ways messages travel, and recover an order from any operation that obeys them.
`);
    md(r`Two copies (**replicas**) of some data, say the highest score seen in a game, live on two machines. Now and then each sends its state to the other, which **merges** it into its own: $x \cdot y$. The network is unreliable in three ways:

1. messages arrive in any order;
2. a replica may merge a batch of messages before passing on the result;
3. a message may arrive twice.

We want two replicas that have received the same messages to hold the same value, however the network behaved.

> [!try]
> Before reading on, turn each of the three hazards into an equation the merge must satisfy.
`);
    sec("Three hazards, three laws");
    md(r`Any order: $x \cdot y = y \cdot x$, **commutative**. Any grouping: $(x \cdot y) \cdot z = x \cdot (y \cdot z)$, **associative**. Twice: $x \cdot x = x$, **idempotent**: merging what you already have changes nothing.

Each law is needed. Here are natural merges, written as tables (row $x$, column $y$ holds $x \cdot y$), each breaking one law. "Keep the newer one", $x \cdot y = y$, depends on which message arrived last:`);
    m("let K = op({a, b, c}; [a, b, c; a, b, c; a, b, c])");
    m("commutative(K)", { work: true });
    md(r`"Average, rounded down" depends on how the messages were batched:`);
    m("let AVG = op({0, 1, 2}; [0, 0, 1; 0, 1, 1; 1, 1, 2])");
    m("associative(AVG)", { work: true });
    md(r`"Add" (capped at 2, to stay in the set) counts a duplicated message twice:`);
    m("let ADD = op({0, 1, 2}; [0, 1, 2; 1, 2, 2; 2, 2, 2])");
    m("fold(ADD; 1)");
    m("fold(ADD; 1, 1)", { work: true });
    md(r`"Keep the larger", $\max$, survives all three:`);
    m("let M = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])");
    m("semilattice(M)", { work: true });
    md(r`
> [!definition] Semilattice
> A **semilattice** is a set with an operation that is **associative**, **commutative** and **idempotent**: an operation whose result does not depend on the order, the grouping or the repetition of what it combines.
`);
    md(r`Union on the subsets of $\{a, b\}$ is another; set elements are written as sets:`);
    m("let U = op({{}, {a}, {b}, {a,b}}; [{}, {a}, {b}, {a,b}; {a}, {a}, {a,b}, {a,b}; {b}, {a,b}, {b}, {a,b}; {a,b}, {a,b}, {a,b}, {a,b}])");
    m("semilattice(U)");
    m("identity(M)");
    md(r`An **identity**, an element that changes nothing, is the natural starting state of a replica that has heard nothing yet: $0$ for $\max$, $\varnothing$ for union.`);
    sec("The order hiding in a merge");
    md(r`$\max$ merges $0, 1, 2$, which are ordered $0 < 1 < 2$; union merges sets, which are ordered by $\subseteq$. In both, the merge is the join of the order.

> [!try]
> Given only the table of a semilattice, how would you get the order back? Ask when merging $x$ into $y$ tells $y$ nothing new.
`);
    md(r`
> [!theorem] A semilattice is a partial order
> Define $x \le y$ when $x \cdot y = y$. Idempotence makes it reflexive, commutativity antisymmetric, associativity transitive, and then $x \cdot y$ is the least upper bound of $x$ and $y$.
`);
    m("order(M)", { work: true });
    m("order(U)");
    md(r`The union table gives back the powerset's diamond. The engine's ‹order› is proved to produce a partial order whose join is the operation (‹semilattice_order›). Without the laws there is no order to find: averaging is refused, with the triple that breaks associativity.`);
    m("order(AVG)");
    md(r`So the laws a merge needs and the laws of a join are the same three. A safe merge *is* the join of an order, "knows at least as much as", and every merge moves a replica up it.`);
    sec("In Lean");
    md(r`The same definitions as a class, and the order it induces, proved a partial order:`);
    lean(r`class Semilattice (α : Type) where
  merge : α → α → α
  merge_comm  : ∀ (a b : α), merge a b = merge b a
  merge_assoc : ∀ (a b c : α), merge (merge a b) c = merge a (merge b c)
  merge_idem  : ∀ (a : α), merge a a = a

export Semilattice (merge merge_comm merge_assoc merge_idem)

/-- The order a semilattice induces: a is below b when merging a into b changes nothing. -/
def Semilattice.le {α : Type} [Semilattice α] (a b : α) : Prop := merge a b = b

theorem Semilattice.le_refl' {α : Type} [Semilattice α] (a : α) : Semilattice.le a a := merge_idem a

theorem Semilattice.le_antisymm' {α : Type} [Semilattice α] (a b : α)
    (h1 : Semilattice.le a b) (h2 : Semilattice.le b a) : a = b := by
  unfold Semilattice.le at h1 h2
  rw [← h2, merge_comm, h1]

theorem Semilattice.le_trans' {α : Type} [Semilattice α] (a b c : α)
    (h1 : Semilattice.le a b) (h2 : Semilattice.le b c) : Semilattice.le a c := by
  unfold Semilattice.le at *
  rw [← h2, ← merge_assoc, h1]

/-- So every semilattice is a partial order. -/
@[reducible] def Semilattice.toPartialOrder (α : Type) [Semilattice α] : PartialOrder α where
  le := Semilattice.le
  le_refl := Semilattice.le_refl'
  le_antisymm := Semilattice.le_antisymm'
  le_trans := Semilattice.le_trans'`);
    md(r`The merge of two elements is above both, and below anything above both: it is their join.`);
    lx(r`theorem Semilattice.le_merge_left {α : Type} [Semilattice α] (a b : α) : Semilattice.le a (merge a b) := by`, r`Prove that $a \le a \cdot b$.`, r`  unfold Semilattice.le
  rw [← merge_assoc, merge_idem]`, [r`‹unfold Semilattice.le› turns the goal into ‹merge a (merge a b) = merge a b›.`, r`Regroup with ‹merge_assoc› (right to left), then ‹merge_idem›.`]);
    lean(r`theorem Semilattice.le_merge_right {α : Type} [Semilattice α] (a b : α) : Semilattice.le b (merge a b) := by
  unfold Semilattice.le
  rw [merge_comm a b, ← merge_assoc, merge_idem]

theorem Semilattice.merge_le {α : Type} [Semilattice α] (a b c : α)
    (h1 : Semilattice.le a c) (h2 : Semilattice.le b c) : Semilattice.le (merge a b) c := by
  unfold Semilattice.le at *
  rw [merge_assoc, h2, h1]`);
    sec("Exercises");
    md(r`Answer ‹true› or ‹false›, or with an element.`);
    m("let W = op({0, 1, 2, 3}; [0, 1, 2, 3; 1, 1, 3, 3; 2, 3, 2, 3; 3, 3, 3, 3])");
    ex("semilattice(W)", r`Is $W$ a semilattice?`, [r`Check the diagonal first, then whether the table is symmetric.`]);
    ex("identity(W)", r`What is the identity of $W$?`, [r`The row that copies the header.`]);
    ex("join(order(W), 1, 2)", r`In the order $W$ gives, what is the join of $1$ and $2$? Read it off the table before computing it.`, [r`The join of the order is the merge: row 1, column 2.`]);
    ex("associative(K)", r`Is "keep the newer one" associative?`, [r`$(x \cdot y) \cdot z = z$ and $x \cdot (y \cdot z) = z$.`]);
    md(r`
> [!summary]
> A merge that ignores order, grouping and repetition is associative, commutative and idempotent: a semilattice. Every semilattice is an order, $x \le y$ exactly when $x \cdot y = y$, and its merge is the join. A table decides the three laws, and a failure is a triple or a pair you can point at.

$\max$ and union are merges of this kind. Next: the merges real systems use, for records of several fields and for "the last write wins", and whether they are joins too.
`);
  });

  add("06-merges.chalk", "A merge is a join", "Records merged field by field and last-writer-wins registers: merges that are joins, built and proved in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("A merge is a join");
    md(r`
> [!goal]
> Build merges that are joins for records and for timestamped values ("last writer wins"), and prove their laws once and for all in Lean.
`);
    md(r`Lesson 5 found the laws a merge needs, in $\max$ and in union. Real replicated state is richer. A user profile has a visit count and a "verified" flag: can it be merged field by field? A setting should hold the last value anyone wrote, but "keep the newer one" was not commutative. This lesson builds both merges and checks their laws.

First, what the laws buy. With $\max$, neither the order of the states nor their repetition makes a difference.

> [!try]
> Predict both folds before running them: the same states, shuffled, one of them sent twice.
`);
    m("let M = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])");
    m("fold(M; 2, 0, 1)", { work: true });
    m("fold(M; 1, 0, 2, 2, 0)", { work: true });
    md(r`Replicas that merge with a join therefore **converge**: two that have received the same states, in any order, grouped any way, any number of times, hold the same value.`);
    sec("Records merge field by field");
    md(r`A record of two fields can merge each field with that field's merge. Each law for pairs is the same law in each field, so it is a join again:`);
    md(r`
> [!theorem] Products of semilattices
> If $A$ and $B$ are semilattices, so is $A \times B$ with $(a, b) \cdot (a', b') = (a \cdot a', b \cdot b')$. Its order is the product order.
`);
    m("let C2 = chain(2)");
    m("let R2 = product(C2, C2)");
    m("join(R2, (0, 1), (1, 0))", { work: true });
    m("let JR = joinop(R2)");
    m("semilattice(JR)");
    md(r`Each replica had learnt one field; the merge keeps both, and nothing more: the least record that knows everything either knew.`);
    sec("In Lean");
    lean(r`instance : Semilattice Nat where
  merge := max
  merge_comm := Nat.max_comm
  merge_assoc := Nat.max_assoc
  merge_idem := Nat.max_self

instance : Semilattice Bool where
  merge := (· || ·)
  merge_comm := by decide
  merge_assoc := by decide
  merge_idem := by decide

/-- A record merges field by field: proved once, for any two field types. -/
instance {α β : Type} [Semilattice α] [Semilattice β] : Semilattice (α × β) where
  merge p q := (merge p.1 q.1, merge p.2 q.2)
  merge_comm p q := by rw [merge_comm p.1, merge_comm p.2]
  merge_assoc p q r := by simp only [merge_assoc]
  merge_idem p := by simp only [merge_idem]

#eval merge (3, true) (5, false)`);
    sec("Last writer wins");
    md(r`A register holds one value, and the last write should win. "Keep the newer one" failed because "newer" meant "arrived later", and messages arrive at two replicas in different orders. Put the time into the data instead: every write carries a timestamp, and the merge keeps the one with the later timestamp. Now both replicas compare the same numbers. One gap is left: two writes with the same timestamp.

> [!try]
> What should the merge do on a tie, so that it stays commutative?
`);
    md(r`
> [!definition] Last-writer-wins register
> A value with a timestamp; the merge keeps the later one, and on a tie the larger value, so that the merge is commutative even when two replicas write at the same time.
`);
    lean(r`/-- A last-writer-wins register: a timestamp and a value. -/
structure LWW where
  ts  : Nat
  val : Nat
  deriving Repr, DecidableEq

/-- a wins over b: a later timestamp, or the same one and a value at least as large. -/
def LWW.beats (a b : LWW) : Prop := b.ts < a.ts ∨ (b.ts = a.ts ∧ b.val ≤ a.val)
instance (a b : LWW) : Decidable (a.beats b) := inferInstanceAs (Decidable (_ ∨ _))

def LWW.merge (a b : LWW) : LWW := if a.beats b then a else b

theorem LWW.merge_comm (a b : LWW) : a.merge b = b.merge a := by
  rcases a with ⟨t1, v1⟩; rcases b with ⟨t2, v2⟩
  simp only [LWW.merge]
  by_cases h1 : (LWW.mk t1 v1).beats ⟨t2, v2⟩ <;> by_cases h2 : (LWW.mk t2 v2).beats ⟨t1, v1⟩ <;>
    simp only [h1, h2, ↓reduceIte, LWW.mk.injEq] <;> simp only [LWW.beats] at * <;> omega

theorem LWW.merge_assoc (a b c : LWW) : (a.merge b).merge c = a.merge (b.merge c) := by
  rcases a with ⟨t1, v1⟩; rcases b with ⟨t2, v2⟩; rcases c with ⟨t3, v3⟩
  simp only [LWW.merge]
  by_cases h12 : (LWW.mk t1 v1).beats ⟨t2, v2⟩ <;> by_cases h23 : (LWW.mk t2 v2).beats ⟨t3, v3⟩ <;>
    by_cases h13 : (LWW.mk t1 v1).beats ⟨t3, v3⟩ <;> simp only [h12, h23, h13, ↓reduceIte] <;>
    simp only [LWW.beats] at * <;> first | rfl | omega

theorem LWW.merge_idem (a : LWW) : a.merge a = a := by
  simp [LWW.merge, LWW.beats]

instance : Semilattice LWW where
  merge := LWW.merge
  merge_comm := LWW.merge_comm
  merge_assoc := LWW.merge_assoc
  merge_idem := LWW.merge_idem

#eval merge (LWW.mk 3 10) (LWW.mk 5 7)`);
    md(r`
> [!mistake]
> The natural tie-break, "keep the second on a tie", is "keep the newer one" again, for those writes: not commutative. Two replicas that each received the other's write last would keep different values forever. Any rule that picks the same winner whichever comes first will do; "the larger value" is one.
`);
    lx(r`theorem three_replicas {α : Type} [Semilattice α] (a b c : α) :
    merge (merge a b) c = merge (merge c a) b := by`, r`Three replicas merge their states in two different orders. Prove they agree.`, r`  rw [merge_assoc, merge_comm b c, ← merge_assoc, merge_comm a c]`, [
      r`Rewrite the left side into the right with ‹merge_assoc› and ‹merge_comm›.`,
      r`‹merge (merge a b) c = merge a (merge b c) = merge a (merge c b) = merge (merge a c) b›, and then swap ‹a› and ‹c›.`,
    ]);
    sec("Exercises");
    ex("fold(M; 0, 2, 1, 0)", r`Merge the states $0, 2, 1, 0$ with $\max$.`, []);
    ex("join(R2, (1, 0), (0, 0))", r`Merge the records $(1, 0)$ and $(0, 0)$ field by field. Write the pair as ‹(x, y)›.`, [r`Take the larger value in each field.`]);
    md(r`
> [!summary]
> A merge that is a join can be applied in any grouping, any order and any number of times: replicas that exchange states converge. Maxima, unions, last-writer-wins registers and records of them are all joins, and the product proof is written once for every record.

Every merge so far was a join. A lattice also has meets, "what two states have in common", and the two operations need not get along. Next: when they do, and what that buys.
`);
  });

  add("07-distributive.chalk", "Distributive and Boolean lattices", "Does meet distribute over join? M₃ and N₅ as the witnesses, unique complements, and the Boolean lattices of sets and squarefree divisors.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Distributive and Boolean lattices");
    md(r`
> [!goal]
> Decide whether meet distributes over join, with the witness when it does not, and see why distributivity is what makes complements ("not $x$") unique.
`);
    md(r`For sets, $\cap$ distributes over $\cup$: $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$, the way $\times$ distributes over $+$. Every lattice has a meet and a join. Does the meet always distribute over the join?

> [!try]
> M₃ below has a bottom, three incomparable atoms $a, b, c$, and a top. Compute both sides of $a \wedge (b \vee c) = (a \wedge b) \vee (a \wedge c)$ by hand before running the check.
`);
    m("let M3 = poset({bot, a, b, c, top}; bot < a, bot < b, bot < c, a < top, b < top, c < top)");
    m("distributive(M3)", { work: true });
    md(r`The left side is $a \wedge \top = a$, the right $\bot \vee \bot = \bot$. The pentagon N₅ fails too:`);
    m("let N5 = poset({bot, p, q, r, top}; bot < p, bot < q, q < r, p < top, r < top)");
    m("distributive(N5)", { work: true });
    md(r`
> [!definition] Distributive lattice
> A lattice is **distributive** when $x \wedge (y \vee z) = (x \wedge y) \vee (x \wedge z)$ for all $x, y, z$ (the dual law then follows).
`);
    md(r`
> [!theorem] Birkhoff
> A lattice is distributive exactly when it contains neither M₃ nor N₅ as a sublattice. They are the witnesses every failure contains.
`);
    m("let D = divisors(12)");
    m("distributive(D)");
    sec("Complements");
    md(r`Why care? Distributivity is what makes "not $x$" mean one thing.`);
    md(r`
> [!definition] Complement
> In a lattice with $\bot$ and $\top$, a **complement** of $x$ is a $y$ with $x \vee y = \top$ and $x \wedge y = \bot$.
`);
    m("complement(M3, a)", { work: true });
    md(r`In M₃, $a$ has two complements, so "not $a$" is ambiguous. In a distributive lattice that cannot happen. If $y$ and $y'$ are both complements of $x$, then
$$y = y \wedge (x \vee y') = (y \wedge x) \vee (y \wedge y') = \bot \vee (y \wedge y') = y \wedge y',$$
and in the same way $y' = y \wedge y'$, so $y = y'$. Distributivity was used once, in the middle step: it is exactly what the uniqueness needs. Among the divisors of 12, complements are unique, but some elements have none:`);
    m("complement(D, 4)");
    m("complement(D, 2)");
    md(r`$2$ has no complement: $\operatorname{lcm}(2, y) = 12$ forces $4 \mid y$ and $3 \mid y$, so $y = 12$, and then $\gcd(2, 12) = 2$, not $1$.`);
    sec("Boolean lattices");
    md(r`
> [!definition] Boolean lattice
> A **Boolean lattice** is distributive and complemented: every element has a complement, and only one. The subsets of a set are the model: complement is set complement.
`);
    m("let P = subsets({x, y, z})");
    m("boolean(P)");
    m("let D30 = divisors(30)");
    m("boolean(D30)");
    m("complement(D30, 6)");
    md(r`The divisors of 30 are the subsets of $\{2, 3, 5\}$ in disguise: a squarefree number is the set of its primes.`);
    sec("In Lean");
    lx(r`theorem bool_distrib (a b c : Bool) : (a && (b || c)) = ((a && b) || (a && c)) := by`, r`Prove that the Booleans are distributive.`, r`  cases a <;> cases b <;> cases c <;> rfl`, [r`There are eight cases: ‹cases a <;> cases b <;> cases c›, and each is ‹rfl›.`]);
    sec("Exercises");
    ex("complement(M3, b)", r`List the complements of $b$ in M₃.`, [r`Which elements join with $b$ to $\top$ and meet it at $\bot$?`]);
    ex("boolean(D)", r`Are the divisors of 12 a Boolean lattice?`, [r`Does every element have a complement?`]);
    ex("complement(D30, 10)", r`List the complements of 10 among the divisors of 30.`, [r`$10 = 2 \cdot 5$: which primes are missing?`]);
    ex("complement(N5, p)", r`Predict first: are complements unique in the pentagon N₅? Then list the complements of $p$.`, [r`Try each element $y$: is $p \vee y = \top$ and $p \wedge y = \bot$?`, r`N₅ is not distributive, so nothing forces a single answer.`]);
    md(r`
> [!summary]
> Distributivity can fail, and M₃ and N₅ are why. It is what makes complements unique. Boolean lattices are distributive with complements; the subsets of a set, and the divisors of a squarefree number, are the examples.

Next, a small lattice with a job: the answers an access rule can give, and the ways a policy combines them.
`);
  });

  add("08-access-decisions.chalk", "Access decisions", "Combining permit and deny: deny-overrides and permit-overrides are joins, first-applicable is not commutative.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Access decisions");
    md(r`
> [!goal]
> Combine permit and deny the way access-control policies do, see which combining rules are semilattices (so rule order cannot matter) and which are not, and prove that adding a rule never turns a deny into a permit.
`);
    md(r`A file server checks a request against three rules. One says **permit**, one says **deny**, and one does not apply (**na**). Should it grant the request? Should the answer change if an administrator reorders the rules?

There is no single right answer: it is a choice, called a *combining algorithm*. The standard ones (XACML's, here without its error values) are operations on $\{\mathrm{na}, \mathrm{permit}, \mathrm{deny}\}$, so they are tables with laws, and lesson 5 says what to look for: if the operation is a semilattice, the decision cannot depend on the order or grouping of the rules.`);
    sec("Deny overrides");
    md(r`A deny anywhere wins; otherwise a permit; otherwise not applicable.`);
    m("let DO = op({na, permit, deny}; [na, permit, deny; permit, permit, deny; deny, deny, deny])");
    m("semilattice(DO)", { work: true });
    m("order(DO)", { work: true });
    m("identity(DO)");
    md(r`It is the join of the chain $\mathrm{na} < \mathrm{permit} < \mathrm{deny}$: a rule's decision can only push the result up, and a policy with no applicable rule says na.

> [!try]
> The second fold lists the same rules in another order. Predict its answer before running it.
`);
    m("fold(DO; permit, na, deny, permit)", { work: true });
    m("fold(DO; deny, permit, permit, na)");
    sec("Permit overrides");
    md(r`The same with the roles swapped: the join of $\mathrm{na} < \mathrm{deny} < \mathrm{permit}$.`);
    m("let PO = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, permit, deny])");
    m("semilattice(PO)");
    m("order(PO)");
    sec("First applicable");
    md(r`The first rule that applies decides. Associative and idempotent, but not commutative:`);
    m("let FA = op({na, permit, deny}; [na, permit, deny; permit, permit, permit; deny, deny, deny])");
    m("commutative(FA)", { work: true });
    m("fold(FA; na, permit, deny)", { work: true });
    m("fold(FA; na, deny, permit)", { work: true });
    md(r`
> [!mistake]
> With first-applicable, reordering two rules can turn a permit into a deny. That is not a bug in the algorithm: the order of the rules is part of the policy, and a tool that sorts or merges rule lists must keep it. With deny-overrides no order is part of the policy.
`);
    sec("In Lean");
    lean(r`inductive Decision where
  | na | permit | deny
  deriving Repr, DecidableEq

def denyOverrides : Decision → Decision → Decision
  | .deny, _ | _, .deny => .deny
  | .permit, _ | _, .permit => .permit
  | .na, .na => .na

def firstApplicable : Decision → Decision → Decision
  | .na, d => d
  | d, _ => d

theorem denyOverrides_comm (a b : Decision) : denyOverrides a b = denyOverrides b a := by
  cases a <;> cases b <;> rfl
theorem denyOverrides_assoc (a b c : Decision) :
    denyOverrides (denyOverrides a b) c = denyOverrides a (denyOverrides b c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem denyOverrides_idem (a : Decision) : denyOverrides a a = a := by cases a <;> rfl

theorem firstApplicable_not_comm : ¬ ∀ a b, firstApplicable a b = firstApplicable b a := by
  intro h
  cases h .permit .deny

instance : Semilattice Decision where
  merge := denyOverrides
  merge_comm := denyOverrides_comm
  merge_assoc := denyOverrides_assoc
  merge_idem := denyOverrides_idem

/-- A policy's decision: its rules' decisions combined, starting from "not applicable". -/
def combine (ds : List Decision) : Decision := ds.foldl denyOverrides .na

#eval combine [.permit, .na, .deny, .permit]`);
    md(r`Under deny-overrides, adding a rule is monotone: it can only move the decision up the chain. In particular a deny stays a deny.`);
    lx(r`theorem deny_stays (ds : List Decision) (d : Decision) (h : combine ds = .deny) :
    combine (ds ++ [d]) = .deny := by`, r`Prove that adding a rule to a policy that denies keeps it denying.`, r`  simp only [combine, List.foldl_append, List.foldl_cons, List.foldl_nil] at *
  rw [h]
  cases d <;> rfl`, [
      r`Unfold ‹combine›: ‹List.foldl_append› splits the fold over ‹ds ++ [d]›.`,
      r`What is left is ‹denyOverrides (combine ds) d›; rewrite with ‹h›, then try each ‹d›.`,
    ]);
    sec("Exercises");
    ex("fold(DO; na, permit, na)", r`Under deny-overrides, what is the decision of rules that say na, permit, na?`, []);
    ex("fold(FA; permit, deny)", r`Under first-applicable, rules say permit then deny. What is the decision?`, []);
    ex("identity(PO)", r`Which decision is the identity of permit-overrides?`, [r`The one that never changes the result.`]);
    md(r`
> [!summary]
> Deny-overrides and permit-overrides are joins of a three-element chain, so a policy's decision under them does not depend on rule order. First-applicable is associative but not commutative: there the order of rules is part of the policy.

Here the lattice ordered the *answers* to a request. Next it orders the *data*: every value carries a security class, and information may only flow up.
`);
  });

  add("09-information-flow.chalk", "Information flow", "Denning's lattice of security classes: data may only flow up, and a computation's output gets the join of its inputs' classes.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Information flow");
    md(r`
> [!goal]
> Label data with security classes, find the class a computed value must get, and check that every flow of information in a program goes up the lattice; then prove the rule for combining inputs.
`);
    md(r`A payroll program reads salaries, which are secret and about HR, builds a report from them, and writes a summary to a folder the finance team reads. Is that a leak? To answer, every value needs a label saying how sensitive it is, and labels need an order, "at least as sensitive as".

A label here has two parts: a level, low or high, and the set of categories the data is about, from $\{\mathrm{fin}, \mathrm{hr}\}$. One label is below another when it is below in both parts, so the labels are the product of a chain and a powerset:`);
    m("let Lv = poset({low, high}; low < high)");
    m("let Cat = subsets({fin, hr})");
    m("let SC = product(Lv, Cat)");
    m("lattice(SC)");
    md(r`
> [!definition] Security classes (Denning)
> A **security class** is a level and a set of categories, ordered componentwise: level by level, categories by inclusion. Information may flow from class $a$ to class $b$ only when $a \le b$.
`);
    sec("Combining inputs");
    md(r`
> [!try]
> A value is computed from a $(\mathrm{low}, \{\mathrm{fin}\})$ input and a $(\mathrm{high}, \{\})$ input. Which classes could it safely get? Which one should it get?

It may reveal something about each input, so its class must be at least each of theirs: an upper bound. Every upper bound is safe; the least one keeps the value as widely usable as possible. So a computed value gets the join of its inputs' classes:`);
    m("join(SC, (low, {fin}), (high, {}))", { work: true });
    m("join(SC, (high, {hr}), (low, {fin}))");
    sec("Checking flows");
    md(r`A program's flows form a relation: $x \to y$ when information about $x$ reaches $y$. It is secure when every flow goes up. The payroll program:`);
    m("let Fl = rel({salary, report, audit}; salary->report, report->audit)");
    m("secure(SC, Fl; salary->(high, {hr}), report->(high, {hr, fin}), audit->(low, {fin}))", { work: true });
    md(r`The audit summary is labelled $(\mathrm{low}, \{\mathrm{fin}\})$, strictly below the report it reads: the flow goes down, and the graph marks it. Raising the audit's class fixes it:`);
    m("secure(SC, Fl; salary->(high, {hr}), report->(high, {hr, fin}), audit->(high, {hr, fin}))");
    sec("Decisions and data: two lattices compared");
    md(r`
> [!note] The last lesson and this one
> Both use a lattice to make "more restrictive" precise, but they order different things. In access decisions the lattice orders the *answers* to one request, and combining rules is a join: the policy's answer can only move up as rules are added. Here the lattice orders the *data*, every value carries a class, and the policy is a condition on every flow: a monotone labelling. One decides a request; the other constrains a computation.
`);
    sec("In Lean");
    lean(r`/-- A security class: high or not, and two categories, each present or not. -/
structure SecClass where
  high : Bool
  fin  : Bool
  hr   : Bool
  deriving Repr, DecidableEq

/-- a may flow to b: componentwise, false below true. -/
def SecClass.le (a b : SecClass) : Bool := (!a.high || b.high) && (!a.fin || b.fin) && (!a.hr || b.hr)
def SecClass.join (a b : SecClass) : SecClass := ⟨a.high || b.high, a.fin || b.fin, a.hr || b.hr⟩

/-- The join is the least upper bound: data may flow from the join exactly when it may flow from both. -/
theorem join_le_iff (a b c : SecClass) : (a.join b).le c = (a.le c && b.le c) := by
  cases a; cases b; cases c
  rename_i a1 a2 a3 b1 b2 b3 c1 c2 c3
  cases a1 <;> cases a2 <;> cases a3 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases c1 <;> cases c2 <;> cases c3 <;> rfl`);
    lx(r`theorem join_flow_left (a b c : SecClass) (h : (a.join b).le c = true) : a.le c = true := by`, r`If a computation's output may flow to $c$, so may its first input.`, r`  rw [join_le_iff] at h
  exact (Bool.and_eq_true _ _ |>.mp h).1`, [r`Rewrite ‹h› with ‹join_le_iff›.`, r`‹Bool.and_eq_true› splits a conjunction of Booleans.`]);
    sec("Exercises");
    ex("join(SC, (low, {fin}), (high, {hr}))", r`What class does a value computed from $(\mathrm{low}, \{\mathrm{fin}\})$ and $(\mathrm{high}, \{\mathrm{hr}\})$ data get? Write it as ‹(level, {categories})›.`, [r`Join componentwise: the higher level, the union of the categories.`]);
    ex("le(SC, (high, {}), (low, {fin}))", r`May information flow from $(\mathrm{high}, \{\})$ to $(\mathrm{low}, \{\mathrm{fin}\})$? Answer ‹true› or ‹false›.`, [r`Compare the levels.`]);
    md(r`
> [!summary]
> Security classes form a product lattice; data flows only upward, a computation's output gets the join of its inputs' classes, and a program is secure when its labelling is monotone along every flow.

Security classes are a lattice we designed. Often there are two orders already, a fine one and a coarse one, and the question is how to translate between them as faithfully as possible. Next: Galois connections.
`);
  });

  add("10-galois.chalk", "Galois connections and closure operators", "Best approximations between a fine order and a coarse one, the closure operators they make, and the concept lattice of a formal context.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Galois connections and closure operators");
    md(r`
> [!goal]
> Find the best approximation of an element of one order in another, recognise the pattern as a Galois connection, and see the closure operator it makes; then build the concept lattice of a small formal context.
`);
    md(r`A ruler is marked only at the even lengths $0, 2, 4, 6$, read as $0, 1, 2, 3$. A length $x$ from $0$ to $6$ has to be reported as one reading $y$, and the reading must never understate it: $x \le 2y$. Several readings are safe. The best is the least of them, $\lceil x/2 \rceil$.

> [!try]
> For which readings $y$ is $\lceil x/2 \rceil \le y$? Compare them with the safe readings.

They are the same: $\lceil x / 2 \rceil \le y$ exactly when $x \le 2y$. That one equivalence says everything about $\lceil x/2 \rceil$: it is safe (take $y = \lceil x/2 \rceil$), and it is below every safe reading.`);
    md(r`
> [!definition] Galois connection
> Monotone maps $f : P \to Q$ and $g : Q \to P$ form a **Galois connection** when $f(x) \le y \iff x \le g(y)$ for all $x$ and $y$. Then $f(x)$ is the best approximation of $x$ in $Q$ from above, as $g$ judges it: the least $y$ with $x \le g(y)$.
`);
    m("let C7 = chain(7)");
    m("let C4 = chain(4)");
    m("let half = map(C7, C4; 0->0, 1->1, 2->1, 3->2, 4->2, 5->3, 6->3)");
    m("let dbl = map(C4, C7; 0->0, 1->2, 2->4, 3->6)");
    m("galois(C7, C4, half, dbl)", { work: true });
    md(r`
> [!mistake]
> The first guess at "halve" is often to round down. It understates: a length of $1$ would read $0$. The check names that pair.
`);
    m("let flo = map(C7, C4; 0->0, 1->0, 2->1, 3->1, 4->2, 5->2, 6->3)");
    m("galois(C7, C4, flo, dbl)", { work: true });
    md(r`Rounding down has its own job: it is the best approximation from *below*. The largest reading that never overstates $x$ is $\lfloor x/2 \rfloor$, since $2y \le x \iff y \le \lfloor x/2 \rfloor$: doubling and rounding down form a Galois connection the other way round.`);
    m("galois(C4, C7, dbl, flo)");
    sec("Round trips are closures");
    md(r`Measure, then read back the length the reading stands for: $x \mapsto 2\lceil x/2 \rceil$, which rounds up to an even length. It never goes down, it is monotone, and doing it twice is doing it once.`);
    m("let even = map(C7; 1->2, 3->4, 5->6)");
    m("closureop(C7, even)", { work: true });
    m("fixpoints(C7, even)");
    md(r`
> [!definition] Closure operator
> A map $c$ on a poset is a **closure operator** when it is **extensive** ($x \le c(x)$), **monotone**, and **idempotent** ($c(c(x)) = c(x)$). Its fixed points are the **closed** elements.
`);
    md(r`For every Galois connection, $g \circ f$ is a closure operator on $P$. Here the closed elements are the even lengths, the ones the ruler states exactly. Closure operators also turn up on their own. On the divisors of 12, sending $3$ up to $6$ is one; sending $2$ down to $1$ is not, since a closure never goes down:`);
    m("let D = divisors(12)");
    m("let cl = map(D; 3->6)");
    m("closureop(D, cl)");
    m("let bad = map(D; 2->1)");
    m("closureop(D, bad)", { work: true });
    sec("Formal concept analysis");
    md(r`
> [!definition] Formal context, concept
> A **context** lists objects, attributes, and which object has which. A **concept** is a set of objects and a set of attributes that determine each other: exactly the objects having all those attributes, and exactly the attributes they all share. Ordered by their objects, the concepts form a complete lattice.
`);
    m("let A = context({duck, eagle, dog, bat}, {flies, mammal, bird}; duck->flies, duck->bird, eagle->flies, eagle->bird, dog->mammal, bat->flies, bat->mammal)");
    m("concepts(A)", { work: true });
    md(r`The two maps "the attributes these objects share" and "the objects having these attributes" form a Galois connection (one that reverses the order: more objects share fewer attributes), and the concepts are its closed pairs. The bat sits below both "flies" and "mammal": the lattice finds the category nobody named.`);
    sec("In Lean");
    lean(r`structure GaloisConnection {α β : Type} [PartialOrder α] [PartialOrder β] (f : α → β) (g : β → α) : Prop where
  gc : ∀ (a : α) (b : β), f a ≤ b ↔ a ≤ g b`);
    lx(r`theorem GaloisConnection.le_gf {α β : Type} [PartialOrder α] [PartialOrder β] {f : α → β} {g : β → α}
    (h : GaloisConnection f g) (a : α) : a ≤ g (f a) := by`, r`Prove that $g \circ f$ is extensive.`, r`  exact (h.gc a (f a)).mp (le_refl (f a))`, [r`Use the connection with $b = f(a)$.`, r`‹le_refl (f a)› proves ‹f a ≤ f a›.`]);
    lean(r`theorem GaloisConnection.fg_le {α β : Type} [PartialOrder α] [PartialOrder β] {f : α → β} {g : β → α}
    (h : GaloisConnection f g) (b : β) : f (g b) ≤ b :=
  (h.gc (g b) b).mpr (le_refl (g b))

theorem GaloisConnection.monotone_f {α β : Type} [PartialOrder α] [PartialOrder β] {f : α → β} {g : β → α}
    (h : GaloisConnection f g) : Monotone f where
  map_le a a' haa := (h.gc a (f a')).mpr (le_trans _ _ _ haa (h.le_gf a'))`);
    sec("Exercises");
    ex("galois(C4, C7, dbl, half)", r`Doubling is the lower partner of rounding down. Is it also the lower partner of rounding up: is ‹galois(C4, C7, dbl, half)› true? Answer ‹true› or ‹false›.`, [r`Try $x = 1$, $y = 1$: is $2 \cdot 1 \le 1$? Is $1 \le \lceil 1/2 \rceil$?`]);
    ex("fixpoints(D, cl)", r`List the closed elements of ‹cl›, the closure that sends $3$ to $6$.`, [r`Every element ‹cl› does not move.`]);
    md(r`
> [!summary]
> A Galois connection pairs each element with its best approximation in another order, $f(x) \le y \iff x \le g(y)$; composing the two maps gives a closure operator, which adds what is forced and then stops. Formal concept analysis is a Galois connection between objects and attributes, and its closed pairs are a lattice of concepts.

Computing a closure in practice means applying a step until it adds nothing. Next: that loop, and why it stops.
`);
  });

  add("11-fixed-points-in-practice.chalk", "Fixed points in practice", "Apply until nothing changes: reachability as a least fixed point, why start at the bottom, and why the iteration stops.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Fixed points in practice");
    md(r`
> [!goal]
> Recognise "apply until nothing changes" as computing a least fixed point, compute one on a lattice of sets, and see why it stops and why it finds exactly what is forced.
`);
    md(r`Which pages can a crawler reach from the home page? Which facts follow from a set of rules? Which variables might be unset at some line of a program? The algorithm is the same loop each time: start with what you know, apply the step, add what it gives, and stop when it gives nothing new. Lesson 4 said when such a loop stops and what it finds. Here it is at work.`);
    sec("Reachability");
    md(r`The nodes reachable from $a$ in the graph $a \to b \to c$, $d \to a$ are the least set $S$ with $a \in S$ and closed under successors: the least fixed point of $f(S) = \{a\} \cup S \cup \mathrm{succ}(S)$ on the subsets of $\{a, b, c, d\}$.`);
    m("let P4 = subsets({a, b, c, d})");
    m(`let reach = map(P4; ${reachMap})`);
    m("monotone(P4, reach)");
    md(r`
> [!try]
> Step through the iteration. Before each step, say which nodes the next set adds.
`);
    m("lfp(P4, reach)", { step: 0 });
    md(r`Each step adds one more layer of successors: $\varnothing$, $\{a\}$, $\{a, b\}$, $\{a, b, c\}$, and then nothing changes. $d$ is not reachable from $a$.`);
    sec("Why start at the bottom");
    md(r`The reachable set is a fixed point: the step adds nothing to it. It is not the only one.`);
    m("fixpoints(P4, reach)");
    m("gfp(P4, reach)", { work: true });
    md(r`$\{a, b, c, d\}$ is closed under successors too: no edge leads out of it. Iterating down from the top stops there at once, and the answer contains $d$, which is not reachable. The least fixed point contains only what is forced, and starting from $\bot$ is what finds it: every set in the chain from $\bot$ is below every fixed point, so the chain cannot overshoot.`);
    sec("Why it stops");
    md(r`
> [!theorem] The ascending chain condition
> If every increasing chain $x_0 \le x_1 \le \cdots$ in a lattice with a bottom is eventually constant (always true on a finite lattice), then iterating a monotone $f$ from $\bot$ reaches a fixed point after finitely many steps, and it is the least one.
`);
    md(r`On the subsets of an $n$-element set a strictly increasing chain has at most $n + 1$ sets, so the iteration takes at most $n$ steps that change anything. In Lean, every iterate is below every fixed point above the start:`);
    lx(r`theorem iter_le_of_fixed {α : Type} [PartialOrder α] {f : α → α} (hf : Monotone f) {a x : α}
    (ha : a ≤ x) (hx : f x = x) : ∀ n, iter f n a ≤ x := by`, r`Prove that every iterate of $f$ from $a$ stays below a fixed point $x$ above $a$.`, r`  intro n
  induction n with
  | zero => exact ha
  | succ n ih =>
    show f (iter f n a) ≤ x
    rw [← hx]
    exact hf.map_le _ _ ih`, [
      r`Induction on ‹n›. The base case is ‹ha›.`,
      r`For ‹n + 1›, the goal is ‹f (iter f n a) ≤ x›; rewrite ‹x› as ‹f x› and use monotonicity on the hypothesis.`,
    ]);
    sec("Exercises");
    m(`let R3 = map(P4; ${reachFromD})`);
    ex("lfp(P4, R3)", r`‹R3› is the reachability step from $d$. What can $d$ reach? Write the set, such as ‹{a, b}›.`, [r`Iterate from the empty set: $\{d\}$ first.`]);
    ex("fixpoints(P4, R3)", r`List every fixed point of ‹R3›, as a set of sets. Why is there only one this time?`, [r`A fixed point contains $d$ and is closed under successors.`, r`From $d$ every node is reachable, so the only such set is all of them: ‹{{a,b,c,d}}›.`]);
    md(r`
> [!summary]
> "Apply until nothing changes" computes a least fixed point when the step is monotone and starts from the bottom. On a finite lattice it always stops, and what it finds is the smallest solution: everything forced, nothing more. Starting from the top finds the greatest, which can contain things nothing forced.

That was one set and one step. Next: many cells, each holding part of an answer, and many small steps reading and writing them, in whatever order a scheduler picks.
`);
  });

  add("12-propagators.chalk", "The propagator model", "Cells that only gain information, in a lattice; propagators as monotone functions between them; why the answer does not depend on the schedule.", ({ sec, md, m, ex, lean, lx }) => {
    sec("The propagator model");
    md(r`
> [!goal]
> Model partial information as a lattice and computations as monotone propagators, and see why a network's answer does not depend on the order things run in, and why a propagator must never guess.
`);
    md(r`Three numbers are tied by $x + y = z$. One source says $x = 3$, another says $z = 10$. Three small computations can each fill in one number from the other two, and a scheduler runs them in whatever order it likes, perhaps in parallel, perhaps one of them twice. How do we make sure the answer does not depend on the schedule?

The idea of the propagator model: a place that holds a value, a **cell**, never forgets. It holds what is known so far, and new information is merged in, never written over. The simplest lattice of information about a number: nothing known, one of the values, or a contradiction.`);
    m("let F = poset({unknown, 1, 2, 3, conflict}; unknown < 1, unknown < 2, unknown < 3, 1 < conflict, 2 < conflict, 3 < conflict)");
    m("lattice(F)");
    m("join(F, unknown, 2)", { work: true });
    md(r`
> [!try]
> One computation writes $2$ to a cell and another writes $3$. Overwriting keeps whichever ran last. What does merging give, in each order?
`);
    m("join(F, 2, 3)", { work: true });
    m("join(F, 3, 2)");
    md(r`Either order gives ‹conflict›: the disagreement is reported, not decided by the schedule.`);
    md(r`
> [!definition] Cells and propagators
> A **cell** holds what is known so far about a value, an element of a lattice ordered by information. New information is **merged** in with the join, so a cell's content only rises. A **propagator** reads cells and writes its conclusions to another cell; a network runs propagators until nothing changes.
`);
    sec("Propagators are monotone");
    md(r`A propagator must say at least as much when it knows more. "Add one" is monotone; "guess 1 when nothing is known" is not, because learning that the value is 2 would make it take its answer back.`);
    m("let inc = map(F; 1->2, 2->3, 3->conflict)");
    m("monotone(F, inc)");
    m("let guess = map(F; unknown->1)");
    m("monotone(F, guess)", { work: true });
    md(r`
> [!theorem] Networks of monotone propagators converge
> Cells only rise under merges, and a monotone propagator's output only rises as its inputs rise. If every propagator keeps getting its turn, then on a lattice with no infinite ascending chains the network reaches a state that no propagator changes; that state is the least one, above the starting contents, that every propagator leaves alone, so it is the same whatever order the propagators ran in.
`);
    md(r`The argument is lesson 11's: every state the network passes through is below every state that all propagators leave alone, so whichever order it climbs in, it stops at the least of them. A guessing propagator breaks this. Run it before the real value $2$ arrives, and the cell becomes $1$ and then ‹conflict›; run it after, and it leaves the $2$ alone. The answer depends on the schedule, which is exactly what monotonicity rules out.`);
    sec("In Lean");
    lean(r`/-- What a cell knows: nothing yet, a value, or a contradiction. -/
inductive Flat (α : Type) where
  | unknown
  | known (a : α)
  | conflict
  deriving Repr, DecidableEq

def Flat.merge {α : Type} [DecidableEq α] : Flat α → Flat α → Flat α
  | .unknown, x => x
  | x, .unknown => x
  | .known a, .known b => if a = b then .known a else .conflict
  | _, _ => .conflict

instance {α : Type} [DecidableEq α] : Semilattice (Flat α) where
  merge := Flat.merge
  merge_comm a b := by
    cases a <;> cases b <;> simp only [Flat.merge]
    rename_i x y
    by_cases h : x = y
    · subst h; rfl
    · simp [h, Ne.symm h]
  merge_assoc a b c := by
    cases a <;> cases b <;> cases c <;> simp only [Flat.merge]
    all_goals first
      | rfl
      | (rename_i x y z
         by_cases h1 : x = y <;> by_cases h2 : y = z <;> simp_all)
      | (rename_i x y
         by_cases h1 : x = y <;> simp_all)
  merge_idem a := by cases a <;> simp [Flat.merge]

instance {α : Type} [ToString α] : ToString (Flat α) where
  toString
    | .unknown => "?"
    | .known a => toString a
    | .conflict => "conflict"

/-- The information order: unknown below everything, conflict above everything. -/
def Flat.below {α : Type} : Flat α → Flat α → Prop
  | .unknown, _ => True
  | _, .conflict => True
  | .known a, .known b => a = b
  | _, _ => False

/-- Addition, on what is known: a sum needs both summands. -/
def Flat.add : Flat Nat → Flat Nat → Flat Nat
  | .known a, .known b => .known (a + b)
  | .conflict, _ | _, .conflict => .conflict
  | _, _ => .unknown

#eval (merge (Flat.known 3) .unknown, merge (Flat.known 3) (Flat.known 4))`);
    lx(r`theorem Flat.add_mono (a a' b b' : Flat Nat) (ha : a.below a') (hb : b.below b') :
    (Flat.add a b).below (Flat.add a' b') := by`, r`Prove that addition is a monotone propagator: knowing more about the summands never makes it know less about the sum.`, r`  cases a <;> cases a' <;> cases b <;> cases b' <;> simp_all [Flat.add, Flat.below]`, [
      r`Case on all four arguments: ‹cases a <;> cases a' <;> cases b <;> cases b'›.`,
      r`Each case unfolds with ‹simp_all [Flat.add, Flat.below]›.`,
    ]);
    sec("Exercises");
    ex("join(F, 1, 1)", r`Merge the information "the value is 1" with itself.`, []);
    ex("monotone(F, guess)", r`Is guessing a monotone propagator? Answer ‹true› or ‹false›.`, [r`Compare what it says about ‹unknown› and about ‹2›.`]);
    md(r`
> [!summary]
> Partial information is a lattice; merging is the join; propagators are monotone maps. A network of them converges to the least state that every propagator leaves alone, whatever order they run in, and a propagator that guesses breaks that.

Next: such a network, running, in Lean.
`);
  });

  add("13-propagator-network.chalk", "A propagator network in Lean", "Mutable cells that only grow, a scheduler that runs to quiescence, and a constraint that runs in every direction.", ({ sec, md, lean, lx }) => {
    sec("A propagator network in Lean");
    md(r`
> [!goal]
> Build a running propagator network in Lean: cells as references that merge, propagators as small programs, and a loop that runs them until nothing changes.
`);
    md(r`Lesson 12 argued that a network of monotone propagators on a lattice without infinite ascending chains stops, and that its answer does not depend on the schedule. Here is one to run. It takes three pieces: a cell, a propagator, and a scheduler.

A cell is a mutable reference whose writes merge. Writing reports whether the content changed, which is how the scheduler knows when to stop.`);
    lean(r`/-- A cell: a mutable reference that only ever grows, by merging. -/
structure Cell (α : Type) where
  ref : IO.Ref α

def Cell.new {α : Type} (init : α) : IO (Cell α) := do
  return ⟨← IO.mkRef init⟩

def Cell.read {α : Type} (c : Cell α) : IO α := c.ref.get

/-- Merge new information into a cell, and say whether it changed. -/
def Cell.write {α : Type} [Semilattice α] [DecidableEq α] (c : Cell α) (v : α) : IO Bool := do
  let old ← c.ref.get
  let new := merge old v
  if new = old then return false
  c.ref.set new
  return true

/-- A propagator reads some cells and writes one; it says whether it changed anything. -/
abbrev Propagator := IO Bool

/-- Run every propagator until a whole round changes nothing; the number of rounds. -/
def runToFixpoint (ps : List Propagator) : IO Nat := do
  let mut rounds := 0
  let mut changed := true
  while changed do
    changed := false
    rounds := rounds + 1
    for p in ps do
      if ← p then changed := true
  return rounds`);
    sec("A constraint in every direction");
    md(r`$x + y = z$ is three propagators: one computes $z$ from $x$ and $y$, the others compute $x$ or $y$ from the rest. Whichever two values become known, the third follows.`);
    lean(r`/-- Subtraction, on what is known; a negative difference is a contradiction. -/
def Flat.sub : Flat Nat → Flat Nat → Flat Nat
  | .known t, .known a => if a ≤ t then .known (t - a) else .conflict
  | .conflict, _ | _, .conflict => .conflict
  | _, _ => .unknown

/-- x + y = z, in every direction it can be read. -/
def sumConstraint (x y z : Cell (Flat Nat)) : List Propagator :=
  [ do z.write (Flat.add (← x.read) (← y.read)),
    do y.write (Flat.sub (← z.read) (← x.read)),
    do x.write (Flat.sub (← z.read) (← y.read)) ]

def sumExample : IO Unit := do
  let x ← Cell.new (Flat.known 3)
  let y ← Cell.new (Flat.unknown : Flat Nat)
  let z ← Cell.new (Flat.known 10)
  let rounds ← runToFixpoint (sumConstraint x y z)
  IO.println s!"x = {← x.read}, y = {← y.read}, z = {← z.read}  ({rounds} rounds)"

#eval sumExample`);
    md(r`
> [!try]
> Edit the Lean above and predict before each run.
> - Reverse the list in ‹sumConstraint›. Does the answer change?
> - Start $z$ at ‹Flat.known 2› instead. The subtraction $2 - 3$ is impossible: where does the contradiction end up, and does the network still stop?
`);
    md(r`
> [!note] Why the lattice is load-bearing
> The loop stops because each write either changes nothing or moves a cell up the flat lattice, where no chain has more than three elements. It gives the same answer in any order because merges are joins and the propagators are monotone. Replace the merge with "overwrite" and both guarantees are gone: two propagators that disagree could overwrite each other forever, and which one wrote last would decide the answer.
`);
    sec("Exercises");
    lx(r`theorem Flat.below_merge (a b : Flat Nat) : a.below (merge a b) := by`, r`Prove that merging never loses information: a cell's old content is below its new one.`, r`  cases a <;> cases b <;> simp [merge, Flat.merge, Flat.below]
  rename_i x y
  by_cases h : x = y <;> simp [h]`, [
      r`Case on both arguments and unfold: ‹simp [merge, Flat.merge, Flat.below]›.`,
      r`One case is left, two known values: split on whether they are equal.`,
    ]);
    md(r`
> [!summary]
> A propagator network is cells that merge, propagators that read and write them, and a loop that runs until quiescence. Monotone propagators over a lattice of finite height make the loop stop, and make its answer independent of the order things run in.

The flat lattice knows a number exactly or not at all. Often what we know is a range, "between 1 and 5". Next: intervals.
`);
  });

  add("14-intervals.chalk", "The interval lattice", "Bounds on a number as partial information: intersection as the merge, interval arithmetic propagators, and what a contradiction does to termination.", ({ sec, md, m, ex, lean, lx }) => {
    sec("The interval lattice");
    md(r`
> [!goal]
> Represent partial knowledge of a number as an interval, merge intervals by intersecting them, propagate bounds through arithmetic, and see where termination needs care.
`);
    md(r`$x$ is between $1$ and $5$, $y$ between $2$ and $3$, and $x + y$ is between $0$ and $6$. What do you know about $x$?

> [!try]
> Work it out by hand before reading on.

Two steps do it. $x + y \ge 1 + 2 = 3$, so $x + y$ is between $3$ and $6$; then $x = (x + y) - y \le 6 - 2 = 4$. No number was ever known exactly, only bounds, and each step narrowed one. "The value is between 1 and 5" is partial information: more than "unknown", less than "it is 3". Two such facts about one number merge into their **intersection**, and an empty intersection is a contradiction. Ordered by information, smaller intervals are higher.`);
    md(r`On the integers $0$ to $2$ (write ‹i01› for $[0, 1]$):`);
    m("let I = poset({i02, i01, i12, i00, i11, i22, empty}; i02 < i01, i02 < i12, i01 < i00, i01 < i11, i12 < i11, i12 < i22, i00 < empty, i11 < empty, i22 < empty)");
    m("lattice(I)");
    m("join(I, i01, i12)", { work: true });
    m("join(I, i00, i22)", { work: true });
    md(r`The meet goes the other way: what two facts have in common, the smallest interval containing both.`);
    m("meet(I, i00, i22)");
    sec("In Lean");
    lean(r`/-- What is known about a number: it lies between lo and hi. -/
structure Ival where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

instance : ToString Ival := ⟨fun a => if a.hi < a.lo then "empty" else s!"[{a.lo}, {a.hi}]"⟩

/-- Merging two facts about one number: both hold, so it lies in the intersection. -/
def Ival.merge (a b : Ival) : Ival := ⟨max a.lo b.lo, min a.hi b.hi⟩

instance : Semilattice Ival where
  merge := Ival.merge
  merge_comm a b := by simp only [Ival.merge, Ival.mk.injEq]; omega
  merge_assoc a b c := by simp only [Ival.merge, Ival.mk.injEq]; omega
  merge_idem a := by simp only [Ival.merge]; cases a; simp only [Ival.mk.injEq]; omega

def Ival.add (a b : Ival) : Ival := ⟨a.lo + b.lo, a.hi + b.hi⟩
def Ival.sub (a b : Ival) : Ival := ⟨a.lo - b.hi, a.hi - b.lo⟩

/-- a says at least as much as b: it is inside it. -/
def Ival.within (a b : Ival) : Prop := b.lo ≤ a.lo ∧ a.hi ≤ b.hi`);
    md(r`The same three propagators as for $x + y = z$, now on intervals. Bounds flow in every direction until they stop narrowing:`);
    lean(r`def ivalSum (x y z : Cell Ival) : List Propagator :=
  [ do z.write (Ival.add (← x.read) (← y.read)),
    do y.write (Ival.sub (← z.read) (← x.read)),
    do x.write (Ival.sub (← z.read) (← y.read)) ]

def ivalExample : IO Unit := do
  let x ← Cell.new (⟨1, 5⟩ : Ival)
  let y ← Cell.new (⟨2, 3⟩ : Ival)
  let z ← Cell.new (⟨0, 6⟩ : Ival)
  let rounds ← runToFixpoint (ivalSum x y z)
  IO.println s!"x ∈ {← x.read}, y ∈ {← y.read}, z ∈ {← z.read}  ({rounds} rounds)"

#eval ivalExample`);
    md(r`The network repeats the reasoning above: $z$ narrows to $[3, 6]$, then $x$ to $[1, 4]$, and $y$ stays $[2, 3]$.`);
    lx(r`theorem Ival.add_mono (a a' b b' : Ival) (ha : a.within a') (hb : b.within b') :
    (Ival.add a b).within (Ival.add a' b') := by`, r`Prove that interval addition is monotone: narrower summands give a narrower sum.`, r`  simp only [Ival.within, Ival.add] at *
  omega`, [r`Unfold ‹Ival.within› and ‹Ival.add› everywhere with ‹simp only›; what is left is linear arithmetic.`]);
    sec("When a contradiction never settles");
    md(r`Lesson 13's loop stopped because the flat lattice has no long chains. ‹Ival› has infinitely many ways to be empty: ‹⟨5, 3⟩› and ‹⟨6, 3⟩› are different values that both mean "no number", and the second is above the first. Give the network a contradiction, $x = 5$ and $y = 5$ but $x + y = 0$, and watch $x$'s raw bounds round by round:`);
    lean(r`/-- x = 5 and y = 5, but x + y = 0: four rounds of the propagators, and x's bounds after each. -/
def ivalContradiction : IO Unit := do
  let x ← Cell.new (⟨5, 5⟩ : Ival)
  let y ← Cell.new (⟨5, 5⟩ : Ival)
  let z ← Cell.new (⟨0, 0⟩ : Ival)
  for round in [1, 2, 3, 4] do
    for p in ivalSum x y z do
      let _ ← p
    let v ← x.read
    IO.println s!"round {round}: x = ⟨{v.lo}, {v.hi}⟩, which is {v}"

#eval ivalContradiction`);
    md(r`
> [!mistake]
> Every round changes the cells, so ‹runToFixpoint› on this network would never return, although every cell has meant "empty" since the first round. The fix is to make all empty intervals one element, a single top, as ‹Flat› has a single ‹conflict›. Then a cell that starts with finite bounds can narrow only finitely often, and the loop stops. Termination comes from the lattice, so a lattice with infinite ascending chains needs this care, or the *widening* operators of static analysis, which jump ahead to a bound instead of creeping towards it.
`);
    sec("Exercises");
    ex("join(I, i02, i12)", r`Merge $[0, 2]$ with $[1, 2]$. Answer with the element's name.`, [r`Intersect them.`]);
    ex("join(I, i01, i22)", r`Merge $[0, 1]$ with $[2, 2]$.`, [r`Do they overlap?`]);
    md(r`
> [!summary]
> Intervals are partial information about numbers; merging is intersection, and an empty one is a contradiction. Interval arithmetic gives monotone propagators, so a network of them narrows every bound as far as the constraints force. When the constraints are consistent it stops; a contradiction stops only once every empty interval is the same element.

A Sudoku square is not a number to bound but a choice among a few digits, and what we know of it is the set of digits still possible. Next, and last: two capstones.
`);
  });

  add("15-capstones.chalk", "Capstones: Sudoku and type inference", "A Sudoku solver and a type checker, both as propagator networks over lattices of partial information.", ({ sec, md, lean, lx }) => {
    sec("Capstones: Sudoku and type inference");
    md(r`
> [!goal]
> Solve a Sudoku and infer the types of a small program with the same machinery: cells of partial information, merges that are joins, and propagators run to a fixed point.
`);
    md(r`What we know of a Sudoku square is the set of digits still possible. It only shrinks as we learn, two facts about one square merge by intersecting, and an empty set is a contradiction: one more lattice of partial information, ordered by reverse inclusion. The machinery of the last three lessons applies unchanged, and so does a type checker's.`);
    sec("Sudoku");
    md(r`A square whose set is down to one digit removes that digit from its **peers**, the squares sharing its row, column or box. Here is a 4×4 grid; candidates are bits, so intersection is bitwise and.`);
    lean(r`/-- The candidates for one Sudoku square, as bits: bit d - 1 set when d is still possible. -/
structure Cands where
  mask : Nat
  deriving Repr, DecidableEq, Inhabited

instance : Semilattice Cands where
  merge a b := ⟨a.mask &&& b.mask⟩
  merge_comm a b := by rw [Nat.and_comm]
  merge_assoc a b c := by simp only [Nat.and_assoc]
  merge_idem a := by simp only [Nat.and_self]

def Cands.digits (c : Cands) : List Nat :=
  (List.range 4).filterMap fun i => if c.mask &&& (1 <<< i) != 0 then some (i + 1) else none

/-- The squares sharing a row, a column or a 2×2 box with square i of a 4×4 grid. -/
def peers (i : Nat) : List Nat :=
  (List.range 16).filter fun j => j != i && (j / 4 == i / 4 || j % 4 == i % 4 || (j / 8 == i / 8 && j % 4 / 2 == i % 4 / 2))

/-- One round: every square whose digit is known removes it from its peers. -/
def eliminate (g : Array Cands) : Array Cands :=
  (List.range 16).foldl (fun g i =>
    match (g[i]!).digits with
    | [d] => (peers i).foldl (fun g j => g.set! j (merge g[j]! ⟨15 - (1 <<< (d - 1))⟩)) g
    | _ => g) g

/-- Rounds until nothing changes (at most n). -/
def solve (g : Array Cands) : Nat → Array Cands
  | 0 => g
  | n + 1 => let g' := eliminate g; if g' = g then g else solve g' n

def puzzle : List Nat := [1, 0, 0, 0,  0, 0, 3, 0,  0, 4, 0, 0,  0, 0, 0, 2]
def grid (p : List Nat) : Array Cands := (p.map fun d => if d == 0 then (⟨15⟩ : Cands) else ⟨1 <<< (d - 1)⟩).toArray

def showGrid (g : Array Cands) : String :=
  String.intercalate "\n" ((List.range 4).map fun r => String.intercalate " " ((List.range 4).map fun c =>
    match (g[r * 4 + c]!).digits with | [d] => toString d | _ => "."))

#eval IO.println (showGrid (solve (grid puzzle) 20))`);
    md(r`Four clues, and elimination alone fills all sixteen squares: every square that comes down to one digit narrows its peers in turn.

> [!try]
> Change ‹puzzle›: remove a clue and see which squares stay undecided (shown as ‹.›). Elimination alone does not solve every Sudoku; the book adds a second propagator ("the only place a digit can go in a unit") and, for hard ones, search.
`);
    lx(r`theorem every_square_has_seven_peers : (List.range 16).all (fun i => (peers i).length == 7) = true := by`, r`Check that every square of a 4×4 grid has seven peers: three in its row, three in its column, and one more in its box.`, r`  decide`, [r`The statement is a finite computation: ‹decide› runs it.`]);
    sec("Type inference by propagation");
    md(r`A type checker can work the same way: a cell per expression holding what is known of its type, in the flat lattice (unknown, a type, or a conflict), and a propagator per typing rule. For ‹e := if c then x + 1 else y›: a condition is a boolean, ‹+› takes and gives integers, and both branches have the type of the result.`);
    lean(r`inductive Ty where
  | int | bool
  deriving Repr, DecidableEq

instance : ToString Ty := ⟨fun | .int => "int" | .bool => "bool"⟩

/-- a and b have the same type: whatever is known of one is known of the other. -/
def sameType (a b : Cell (Flat Ty)) : List Propagator :=
  [ do a.write (← b.read), do b.write (← a.read) ]

def inferExample : IO Unit := do
  let c ← Cell.new (Flat.unknown : Flat Ty)
  let x ← Cell.new (Flat.unknown : Flat Ty)
  let y ← Cell.new (Flat.unknown : Flat Ty)
  let e ← Cell.new (Flat.unknown : Flat Ty)
  let plus1 ← Cell.new (Flat.unknown : Flat Ty)
  let ps : List Propagator :=
    [ do c.write (.known .bool),          -- a condition is a bool
      do x.write (.known .int),           -- x + 1 adds ints
      do plus1.write (.known .int) ] ++   -- and gives an int
    sameType plus1 e ++ sameType y e      -- the branches have the result's type
  let rounds ← runToFixpoint ps
  IO.println s!"c : {← c.read}, x : {← x.read}, y : {← y.read}, e : {← e.read}  ({rounds} rounds)"

#eval inferExample`);
    md(r`The type of ‹y› was never written down: it flowed from ‹x + 1› through ‹e›. A program that used ‹y› as a boolean too would drive its cell to ‹conflict›: a type error, found by the same fixed point.`);
    md(r`
> [!summary]
> Sudoku and type inference are both "partial information, merged and propagated to a fixed point". The lattice makes the merges order-independent and the loop terminate; the propagators carry the problem's rules. That is the whole of the propagator model, from the first lesson's partial orders to a working solver.

The same merges, sent between machines instead of between cells, are the subject of the course *CRDTs: replicated data that converges*.
`);
  });
}, { leanPrelude: true });

// ---------------------------------------------------------------------------------------------------
// Course 6. The Lean is the book's own (From Propagators to Replicas, adekau/lean4learning), ported to
// Lean 4.34 in notebooks/sources/Crdt.lean and split here at its chapter headings; the book's
// compiled solutions become the lessons' Lean exercises.
const crdtLines = readFileSync(new URL("../../notebooks/sources/Crdt.lean", import.meta.url), "utf8").split("\n");
/** The line where the chapter block headed `name` starts (its `/- ====` line). */
const crdtAt = (name) => {
  const i = crdtLines.findIndex((l, k) => l.startsWith("/- ====") && (crdtLines[k + 1] ?? "").trimStart().startsWith(name));
  if (i < 0) throw new Error(`Crdt.lean: no chapter headed ${name}`);
  return i;
};
/** Lines `from`–`to` as Lean cells, one per top-level comment block (the book's own sections). */
function crdtCells(from, to) {
  const cells = [];
  let cur = [];
  for (const l of crdtLines.slice(from, to)) {
    if (l.startsWith("/- ") && cur.some((x) => x.trim())) { cells.push(cur.join("\n").trim()); cur = []; }
    cur.push(l);
  }
  if (cur.some((x) => x.trim())) cells.push(cur.join("\n").trim());
  return cells;
}
const crdtChapters = ["Crdt.GCounter", "Crdt.PNCounter", "Crdt.SList", "Crdt.LWW", "Crdt.ORSet", "Crdt.Perm", "Crdt.Delivery", "Crdt.VV", "Crdt.OpBased", "Crdt.Capstone", "Crdt.Limits", "Crdt.Solutions"];
/** Lesson `k`'s Lean (0-based): the first lesson starts at the top of the file. */
const crdtLesson = (k) => crdtCells(k === 0 ? 0 : crdtAt(crdtChapters[k - 1]), crdtAt(crdtChapters[k]));
const crdtAudit = crdtCells(crdtLines.findIndex((l, k) => l.startsWith("/- ====") && (crdtLines[k + 1] ?? "").includes("Axiom audit")), crdtLines.length);
const OPEN = "open Order.PartialOrder Order.BoundedJoinSemilattice in\n";

course("crdt", "CRDTs: replicated data that converges",
  "From Propagators to Replicas: counters, sets and registers that replicas update without coordinating and merge as joins, each design the fix for the last one's bug; the main theorem that they converge; gossip, version vectors, op-based CRDTs, a replicated store, and the limits.",
  "Distributed systems", (add) => {

  add("01-replicas.chalk", "Replicas and the merge discipline", "Two replicas lose an update; the three laws a merge needs so that the network cannot make it lose one: states in a semilattice, merge as join.", ({ sec, md, m, ex, lean }) => {
    sec("Replicas and the merge discipline");
    md(r`
> [!goal]
> Watch two replicas lose an update, find the three laws a merge must obey so that the network cannot make it lose one, and name what obeys them: a state-based CRDT.
`);
    md(r`A like counter runs on two phones, ‹a› and ‹b›. Each phone keeps its own copy of the count (a **replica**), so that a tap registers at once, even offline, and the phones sync when they can. Both start at 0, each user taps once, and then the phones sync. Both should read 2.`);
    md(r`
> [!try]
> The obvious design: each replica stores a number; a tap reads it, adds one and stores the result; a sync passes the latest number across. Predict what each phone reads after the sync.
`);
    sec("A lost update");
    md(r`‹replicas(…)› runs a design on named replicas through a schedule, one event per line: ‹a: …› is a local update at ‹a›, and ‹a -> b› has ‹b› merge ‹a›'s state. It answers with each replica's reading and draws a **space-time diagram**: a lane per replica, an arrow per message. Here the design is ‹lww›, "keep the latest write", and each tap writes what its phone read plus one, so both write 1. Step through it:`);
    m(`replicas(lww; a, b
  a: write 1
  b: write 1
  a -> b
  b -> a
)`, { step: 0 });
    md(r`The phones agree, and they are wrong: two taps, and both read 1. Each tap wrote "0 plus one"; the sync kept one write and dropped the other. No message was lost and nothing crashed, yet an update vanished. This is the **lost update**, and each design in this course is the fix for the previous design's version of it.`);
    sec("Overwrite does not even agree");
    md(r`‹lww› at least drops the same write everywhere: it compares timestamps (lesson 5). Plain overwrite, "keep the incoming value", does not. As a table, row $x$, column $y$ is what a replica holding $x$ keeps on hearing $y$:`);
    m("let Ow = op({a, b}; [a, b; a, b])");
    m("commutative(Ow)", { work: true });
    md(r`A replica that hears $a$ and then $b$ ends at $b$; one that hears $b$ and then $a$ ends at $a$. The same messages in a different order leave the two in different states, for good:`);
    m("fold(Ow; a, b)");
    m("fold(Ow; b, a)");
    sec("What a merge must not care about");
    md(r`
> [!try]
> A real network delays messages, so they arrive in any **order**; replicas pass on what they have heard, so updates arrive already **grouped** into other replicas' states; and it retries, so a message can arrive **twice**. For each, what must a merge $\sqcup$ satisfy so that it cannot change the outcome?
`);
    md(r`One law each:
- order: $x \sqcup y = y \sqcup x$ (**commutative**);
- grouping: $(x \sqcup y) \sqcup z = x \sqcup (y \sqcup z)$ (**associative**);
- duplicates: $x \sqcup x = x$ (**idempotent**).

An operation with all three is a **semilattice**, and a semilattice is the same thing as a join: setting $x \sqsubseteq y$ when $x \sqcup y = y$ gives a partial order in which $x \sqcup y$ is the least upper bound. Overwrite breaks the first law. "Keep the larger" keeps all three, so any order, grouping or repetition of the same messages gives the same result:`);
    m("let Mx = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])");
    m("semilattice(Mx)", { work: true });
    m("fold(Mx; 2, 0, 1, 1)");
    m("fold(Mx; 1, 1, 0, 2)");
    md(r`A merge that is a join only ever moves up. So an update must move up too: an update that moved a state down would be undone by the first merge with a replica that had not heard of it, whose state is still above. Lesson 3 meets this as a bug.`);
    md(r`
> [!definition] State-based CRDT
> A **state-based CRDT** keeps each replica's state in a join-semilattice with a least element $\bot$ (the state before anything has happened), makes every update **inflationary** (it goes up: $s \sqsubseteq u(s)$), and merges by the join. A replica then holds not a value but everything it has heard about the value, and hearing the same things in any order, grouping or number of times gives the same state.
`);
    md(r`This is the propagator cell from *Order and lattices* read again: there a cell gathered partial information from propagators on one scheduler; here a replica gathers it from other replicas over an unreliable network. The algebra is the same.`);
    sec("A preview of the fix");
    md(r`"Keep the larger" on the count itself does not save the like counter: after their taps both phones hold 1, and $\max(1, 1) = 1$. Adding the counts would remember both taps, but addition is not idempotent: a sync delivered twice counts its taps twice. Yet here is the same schedule on the counter the next lesson builds:`);
    m(`replicas(gcounter; a, b
  a: inc
  b: inc
  a -> b
  b -> a
)`);
    md(r`Two taps, and both read 2.`);
    sec("In Lean");
    md(r`The book's Lean, chapter by chapter, runs in this course's lessons; each lesson sees the ones before it. First the merge discipline as classes (with notation $\sqcup$ for the join, $\bot$ for the bottom, $\sqsubseteq$ for "knows at least as much"), the laws every join obeys (the ACI toolkit: associative, commutative, idempotent), the propagator machinery re-read as replicas, and chapter 1's naive counter, where an overwriting sync loses an update and ends at 2 when the truth is 3.`);
    for (const c of crdtLesson(0)) lean(c);
    sec("Exercises");
    ex("commutative(Mx)", r`Is "keep the larger" commutative?`, []);
    ex("idempotent(Ow)", r`Overwrite breaks commutativity. Does it keep idempotence, $x \sqcup x = x$ for every $x$? Answer ‹true› or ‹false›.`, [r`A replica holding $x$ hears $x$ again. What does overwrite keep?`]);
    ex("fold(Ow; b, a, b, a)", r`Under overwrite, a replica hears $b$, $a$, $b$, $a$ in that order. What does it hold?`, [r`The last one heard wins.`]);
    md(r`
> [!summary]
> A merge that chooses between values (overwrite, the latest write) loses updates, or leaves replicas disagreeing. A merge that is commutative, associative and idempotent, that is a join, makes the order, grouping and repetition of messages irrelevant; with updates that only go up, that is a state-based CRDT. It leaves a question for the next lesson: the count cannot be a single number, so what state would let "the larger of two states" keep every tap?
`);
  });

  add("02-gcounter.chalk", "The G-Counter", "Counting without coordination: why one number cannot be merged, and the fix, one slot per replica merged by pointwise maximum.", ({ sec, md, m, ex, lean, lx }) => {
    sec("The G-Counter");
    md(r`
> [!goal]
> Find a state for a counter whose join keeps every increment exactly once, and see why one slot per replica is forced.
`);
    md(r`Lesson 1 left the like counter broken. Both merges of a single number fail:
- **max** forgets: two phones that each counted one tap hold 1 and 1, and $\max(1, 1) = 1$;
- **sum** double-counts: it is not idempotent, so a state delivered twice adds its taps twice.

Max has the right laws; the state is too poor. Two 1s could be the same tap heard twice or two different taps, and max has to assume the first.`);
    md(r`
> [!try]
> What could the state record so that the larger of two states never mixes up two different taps? Think about who made each tap.
`);
    sec("One slot per replica");
    md(r`Record the taps **per replica**. Every replica keeps a slot for every replica and only ever increments its own. Then each slot has a single writer, so of two values for slot $a$ the larger one already counts every tap the smaller one does: max, slot by slot, is exactly right. The value is the sum of the slots. For two replicas a state is a pair, and the states form a product of chains:`);
    m("let C4 = chain(4)");
    m("let G = product(C4, C4)");
    m("join(G, (2, 0), (1, 3))", { work: true });
    md(r`Replica $a$ has counted 2 taps and heard of none of $b$'s; replica $b$ has heard of 1 of $a$'s and counted 3 of its own. Merged: $(2, 3)$, value 5, every tap once. Merging an older state such as $(1, 0)$, or the same state again, changes nothing:`);
    m("join(G, (2, 3), (1, 0))");
    md(r`
> [!definition] G-Counter
> A **G-Counter** (grow-only counter) on replicas $1, \dots, R$ is a vector of $R$ naturals, all zero at the start. Replica $i$ increments only entry $i$; merge is the entrywise maximum; the value is the sum of the entries.
`);
    md(r`
> [!mistake]
> Why only its own slot? Let any replica bump any slot. From $(1, 0)$, replicas $a$ and $b$ each count a tap in slot $a$, and both hold $(2, 0)$. Their merge:
`);
    m("join(G, (2, 0), (2, 0))");
    md(r`Three taps, value 2: the lost update is back, because slot $a$ now has two writers.`);
    sec("The lost update, fixed");
    md(r`Lesson 1's schedule, on a G-Counter. The work shows each state as a map from replicas to their slots:`);
    m(`replicas(gcounter; a, b
  a: inc
  b: inc
  a -> b
  b -> a
)`, { work: true });
    md(r`Merges need not be symmetric or complete. Step through three replicas: ‹a› sends to ‹b›, and ‹b› to ‹c›.`);
    m(`replicas(gcounter; a, b, c
  a: inc
  b: inc
  b: inc
  a -> b
  b -> c
)`, { step: 0 });
    md(r`
> [!try]
> ‹b› and ‹c› read 3, but ‹a› has heard from no one and reads 1. Which single message makes all three agree?
`);
    m(`replicas(gcounter; a, b, c
  a: inc
  b: inc
  b: inc
  a -> b
  b -> c
  c -> a
)`);
    sec("In Lean");
    md(r`The chapter opens with the two failed merges as theorems, ‹max_undercounts› and ‹add_overcounts›, and then builds the G-Counter as a function from replicas to naturals.`);
    for (const c of crdtLesson(1)) lean(c);
    md(r`The executable G-Counter renders as a list; rendering a merge is zipping the renders with $\max$. The lemma behind it:`);
    lx(`theorem zipWith_map_map {α β : Type} (f : β → β → β) (g h : α → β) :
    ∀ (l : List α), List.zipWith f (l.map g) (l.map h) = l.map (fun i => f (g i) (h i)) := by`,
      r`Prove that zipping two maps of a list is mapping the combined function.`, `  intro l
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [ih]`, [r`Induction on the list.`, r`In the ‹cons› case, ‹simp only [List.map_cons, List.zipWith_cons_cons]› exposes the head, and the hypothesis handles the tail.`]);
    lean(`${OPEN}theorem toList_sup {R : Nat} (g h : GCounter R) :
    GCounter.toList (g ⊔ h)
      = List.zipWith Nat.max (GCounter.toList g) (GCounter.toList h) :=
  (zipWith_map_map Nat.max g h (List.finRange R)).symm

/-- A merge's value is at most the sum of the values... -/
theorem foldl_add_pair {ι : Type} (f g : ι → Nat) :
    ∀ (l : List ι) (a b : Nat),
      l.foldl (fun acc i => acc + (f i + g i)) (a + b)
        = l.foldl (fun acc i => acc + f i) a
            + l.foldl (fun acc i => acc + g i) b
  | [], _, _ => rfl
  | x :: t, a, b => by
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons,
          show a + b + (f x + g x) = (a + f x) + (b + g x) by omega]
      exact foldl_add_pair f g t (a + f x) (b + g x)

${OPEN}theorem value_sup_le {R : Nat} (g h : GCounter R) :
    GCounter.value (g ⊔ h) ≤ GCounter.value g + GCounter.value h := by
  have hle : ∀ i : Fin R, (g ⊔ h) i ≤ g i + h i := fun i =>
    Nat.max_le.mpr ⟨Nat.le_add_right _ _, Nat.le_add_left _ _⟩
  calc GCounter.value (g ⊔ h)
      ≤ (List.finRange R).foldl (fun acc i => acc + (g i + h i)) 0 :=
        GCounter.foldl_add_le hle _ (Nat.le_refl 0)
    _ = GCounter.value g + GCounter.value h := foldl_add_pair g h _ 0 0

/-- ... and strictly less as soon as the two have counted the same taps. -/
example :
    GCounter.value
        (GCounter.increment 0 (⊥ : GCounter 1) ⊔ GCounter.increment 0 ⊥)
      < GCounter.value (GCounter.increment 0 (⊥ : GCounter 1))
          + GCounter.value (GCounter.increment 0 (⊥ : GCounter 1)) := by
  decide`);
    sec("Exercises");
    ex("join(G, (3, 1), (2, 2))", r`Merge the G-Counter states $(3, 1)$ and $(2, 2)$. Write the pair as ‹(x, y)›.`, [r`Slot by slot, the maximum.`]);
    ex("join(G, (1, 3), (1, 2))", r`Replica $b$ holds $(1, 3)$. A delayed message arrives holding $(1, 2)$, an older state of $b$'s own. Merge it in.`, [r`Slot by slot, the maximum: an older state is below the current one.`]);
    md(r`
> [!summary]
> A single number cannot be merged: max cannot tell two taps from one tap heard twice, and sum counts repeats. One slot per replica, each with a single writer, makes max right: merge slot by slot, read the sum. Merging twice or merging stale states changes nothing, so the network may duplicate and reorder freely. But every update only adds: how do you count down when every update must go up?
`);
  });

  add("03-pncounter.chalk", "The PN-Counter", "Counting down without going down: the decrement a merge undoes, and the fix, two grow-only counters and a value that subtracts.", ({ sec, md, m, ex, lean }) => {
    sec("The PN-Counter");
    md(r`
> [!goal]
> Add decrements to the counter while every update still moves the state up.
`);
    md(r`The like button needs an unlike. The obvious decrement: a replica lowers its own slot.`);
    md(r`
> [!try]
> Replica $a$ has counted 2 taps, state $(2, 0)$, and $b$ has heard of them, so $b$ holds $(2, 0)$ too. Now $a$ decrements, to $(1, 0)$, and then $b$'s state arrives. Predict the merge.
`);
    m("let C4 = chain(4)");
    m("let G = product(C4, C4)");
    m("join(G, (1, 0), (2, 0))", { work: true });
    md(r`The decrement is undone. The join only goes up, the decrement went down, and $b$'s stale state, still above, wins: lesson 1's warning about updates that are not inflationary, now as a bug.`);
    sec("Count the decrements");
    md(r`The way out is the move every design in this course makes: if a merge loses information, put that information in the state. A decrement is not the removal of an increment but an event of its own, and events can be counted, in a G-Counter of their own. Keep two G-Counters, $P$ for increments and $N$ for decrements, and read the value as $P - N$. Every update raises one of them, so the state only goes up while the value may go down.`);
    md(r`
> [!definition] PN-Counter
> A **PN-Counter** is a pair of G-Counters $(P, N)$. Replica $i$ increments by raising its entry of $P$ and decrements by raising its entry of $N$; merge is the join of each half; the value is $\sum P - \sum N$.
`);
    md(r`For one replica a state is a pair $(p, n)$, ordered componentwise:`);
    m("let C3 = chain(3)");
    m("let PN = product(C3, C3)");
    m("le(PN, (1, 0), (1, 1))", { work: true });
    md(r`$(1, 0) \sqsubseteq (1, 1)$: a decrement moved the state up while the value went from 1 to 0.`);
    sec("The decrement survives");
    md(r`The schedule that undid the decrement, on a PN-Counter: $a$ counts two, $b$ hears of them, $a$ decrements, and $b$'s stale state reaches $a$. The state is a pair of G-Counters, increments and decrements:`);
    m(`replicas(pncounter; a, b
  a: inc
  a: inc
  a -> b
  a: dec
  b -> a
  a -> b
)`, { work: true });
    md(r`$b$'s state is no longer above $a$'s: $a$ has a decrement that $b$ lacks, and the merge keeps it. Both read 1.`);
    md(r`
> [!mistake]
> The value of a merge is not the larger value. An increment at $a$ (value 1) and a decrement at $b$ (value $-1$) merge to 0, not $\max(1, -1) = 1$:
`);
    m(`replicas(pncounter; a, b
  a: inc
  b: dec
  a -> b
  b -> a
)`);
    md(r`Only the state is merged; the value is read off it, and it is not monotone in the state.`);
    sec("In Lean");
    md(r`The chapter proves both halves of that: ‹decr_inflationary› (the state goes up) and ‹value_not_monotone› (the value need not), with ‹value_merge_ne_max› for the mistake above.`);
    for (const c of crdtLesson(2)) lean(c);
    md(r`A value that clamps at zero hides the negative truth: a seed for the last lesson.`);
    lean(`def clampedValue {R : Nat} (p : PNCounter R) : Nat :=
  (PNCounter.value p).toNat

example : clampedValue (PNCounter.decr 0 (⊥ : PNCounter 1)) = 0 := by decide
example : PNCounter.value (PNCounter.decr 0 (⊥ : PNCounter 1)) < 0 := by decide`);
    sec("Exercises");
    ex("le(PN, (2, 0), (1, 1))", r`For one replica, is the state $(2, 0)$ below $(1, 1)$? Answer ‹true› or ‹false›.`, [r`Compare componentwise.`]);
    ex("join(product(G, G), ((2, 0), (1, 0)), ((1, 1), (0, 1)))", r`Two replicas $a$, $b$; write a PN state as $(P, N)$, each half a pair of slots ($a$'s, $b$'s). Replica $a$ holds $((2, 0), (1, 0))$ and $b$ holds $((1, 1), (0, 1))$. Merge them. (The merged state reads $3 - 2 = 1$.)`, [r`$P$ and $N$ merge separately, each slot by the maximum.`]);
    md(r`
> [!summary]
> A decrement that lowers the state is undone by the next merge with a replica that has not heard of it. Counting decrements as events of their own keeps every update going up: the state is a pair of grow-only counters, and only the value, $P - N$, falls. Sets come next. Adding an element is easy; what is the decrement of a set?
`);
  });

  add("04-sets.chalk", "Sets that only grow", "G-Set and 2P-Set: union as the merge, the removal a merge brings back, tombstones, and the re-add they forbid.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Sets that only grow");
    md(r`
> [!goal]
> Replicate a set: adding merges by union for free; see why removing does not, and what it costs to make it work.
`);
    md(r`A shared shopping list. Adding is the easy half: replicas add items, and a merge takes the union. Union is a join (commutative, associative, idempotent), so a **G-Set** (grow-only set: states are sets, ordered by inclusion, merged by union) is a CRDT with no further thought:`);
    m("let S = subsets({x, y})");
    m("join(S, {x}, {y})");
    m("replicas(gset; a, b; a: add x; b: add y; a -> b; b -> a)");
    sec("Removal is the hard part");
    md(r`
> [!try]
> Both replicas hold $\{x\}$. Replica $a$ deletes $x$, leaving $\{\}$; then $b$'s state arrives. Predict the merge.
`);
    m("join(S, {}, {x})", { work: true });
    md(r`$x$ is back. Deleting moved the state down, and the join undid it: lesson 3's undone decrement, for sets. The fix is lesson 3's too: do not perform the removal, record it.`);
    sec("Tombstones: the 2P-Set");
    md(r`Keep a second grow-only set, the removed elements (**tombstones**). An element is in the set when it has been added and not removed. Both halves only grow, so a state is a pair in a product of semilattices:`);
    md(r`
> [!definition] 2P-Set
> A **2P-Set** (two-phase set) is a pair of G-Sets $(A, T)$, the added and the tombstoned elements. Adding $x$ puts it in $A$, removing it puts it in $T$, merge is union on each half, and the members are $A \setminus T$.
`);
    m("let TP = product(S, S)");
    m("join(TP, ({x}, {}), ({x}, {x}))", { work: true });
    m("join(TP, ({x}, {x}), ({x}, {}))");
    md(r`The removal survives the merge, in either order.`);
    sec("Removed for ever");
    md(r`
> [!try]
> $a$ adds $x$ and tells $b$; $b$ removes it; meanwhile $a$ adds $x$ again. After they exchange states, is $x$ in the set?
`);
    m(`replicas(twopset; a, b
  a: add x
  a -> b
  b: remove x
  a: add x
  b -> a
)`, { work: true });
    md(r`
> [!mistake]
> Both read $\{\}$: the re-add is lost, the lost update again. $a$'s second add puts $x$ in the added set, where it already is, so the merge cannot tell a re-add from the old add it has seen, and the tombstone outranks both. The next lessons tell adds apart, two ways: by time (last writer wins) and by a unique tag on each add (the OR-Set).
`);
    md(r`In the simulator a 2P-Set replica may remove only an element it has seen added, so a tombstone never comes before its add.`);
    sec("In Lean");
    md(r`To compute with finite sets (print them, decide equalities) the book represents them as **strictly sorted lists**: same members, same list, which is what antisymmetry needs. The chapter also proves the failed attempt wrong, ‹naiveRemove_resurrects›, and the 2P-Set's limit, ‹no_readd›.`);
    for (const c of crdtLesson(3)) lean(c);
    md(r`A sorted, duplicate-free sublist is no longer than the list it sits in; so a G-Set's size can only grow.`);
    lean(`${OPEN}theorem sorted_subset_length {α : Type} [TotalOrder α] :
    ∀ {l₁ l₂ : List α}, SList.Sorted l₁ → SList.Sorted l₂ →
      (∀ x ∈ l₁, x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _, _ => Nat.zero_le _
  | a :: _, [], _, _, h => absurd (h a List.mem_cons_self) (by intro hx; cases hx)
  | a :: t₁, b :: t₂, h₁, h₂, h => by
      have hab : b ≼ a := SList.sorted_head_le h₂ a (h a List.mem_cons_self)
      by_cases he : a = b
      · subst he
        apply Nat.succ_le_succ
        apply sorted_subset_length (SList.sorted_tail h₁) (SList.sorted_tail h₂)
        intro x hx
        have hax : a ≺ x := SList.sorted_head_lt h₁ x hx
        cases List.mem_cons.mp (h x (List.mem_cons_of_mem a hx)) with
        | inl hxa => exact absurd (hxa ▸ hax) (TotalOrder.lt_irrefl a)
        | inr hm => exact hm
      · have hba : b ≺ a := ⟨hab, fun hc => he hc.symm⟩
        have hsub : ∀ x ∈ a :: t₁, x ∈ t₂ := by
          intro x hx
          have hbx : b ≺ x :=
            TotalOrder.lt_of_lt_of_le hba (SList.sorted_head_le h₁ x hx)
          cases List.mem_cons.mp (h x hx) with
          | inl hxb => exact absurd (hxb ▸ hbx) (TotalOrder.lt_irrefl b)
          | inr hm => exact hm
        have hlen := sorted_subset_length h₁ (SList.sorted_tail h₂) hsub
        simp only [List.length_cons] at *
        omega`);
    lx(`theorem size_monotone {s t : GSet} (h : s ⊑ t) :
    SList.size s ≤ SList.size t := by`, r`Prove that a G-Set's size never shrinks under the information order.`, `  exact sorted_subset_length s.sorted t.sorted h`, [r`‹sorted_subset_length› does the work; a G-Set carries the proof that its list is sorted (‹s.sorted›).`]);
    sec("Exercises");
    ex("le(TP, ({x}, {}), ({x}, {x}))", r`Is removing $x$ an inflation: is the 2P-Set state $(\{x\}, \{\})$ below $(\{x\}, \{x\})$? Answer ‹true› or ‹false›.`, [r`Compare the halves separately, by inclusion.`]);
    ex("join(TP, ({x, y}, {}), ({x}, {x}))", r`Merge the 2P-Set states $(\{x, y\}, \{\})$ and $(\{x\}, \{x\})$. Write it as ‹({…}, {…})›.`, [r`Union the added sets and the removed sets separately.`]);
    md(r`
> [!summary]
> Union is a join, so grow-only sets replicate for free. Deleting goes down and is undone by the next merge, so a removal must be recorded as a tombstone, which only grows too. The 2P-Set pays for that with "removed once, removed for ever": it cannot tell a re-add from an old add. Telling them apart needs more in the state, and the first idea is a clock.
`);
  });

  add("05-lww.chalk", "Last writer wins", "Overwrite, done lawfully: timestamps in the state, ties broken by replica, and what the merge silently throws away.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Last writer wins");
    md(r`
> [!goal]
> Make "the latest write wins" a lawful merge by putting time in the state, and see what it silently discards.
`);
    md(r`Some values should be overwritten: a display name, a thermostat's set point. Lesson 1's overwrite did not even converge, because "latest" meant "heard last", which differs from replica to replica. And the 2P-Set could not re-add because its merge could not tell which came later, the remove or the add. Both need the merge to know which write came later, so put that in the state: each write carries a **timestamp**, and the merge keeps the write with the larger one.`);
    md(r`
> [!try]
> Two replicas write different values with the same timestamp. Which should the merge keep?
`);
    md(r`The naive answer, "on a tie, keep the incoming one", is overwrite again on tied writes, and it is not commutative:`);
    m("let Naive = op({w1, w2}; [w1, w2; w1, w2])");
    m("commutative(Naive)", { work: true });
    md(r`Break ties with something every replica agrees on: the writer's identity. Compare writes by (timestamp, replica), lexicographically. That is a total order, and the maximum in a total order is a join. On three writes, ‹w3a› (stamp 3 at $a$), ‹w3b› (stamp 3 at $b$) and ‹w5a› (stamp 5 at $a$):`);
    m("let Lex = op({w3a, w3b, w5a}; [w3a, w3b, w5a; w3b, w3b, w5a; w5a, w5a, w5a])");
    m("semilattice(Lex)");
    md(r`
> [!definition] LWW-Register
> A **last-writer-wins register** holds a value with its stamp (timestamp, replica), or nothing ($\bot$, never written). A write at time $t$ by replica $i$ joins in the stamped write; merge keeps the write with the lexicographically larger stamp.
`);
    sec("A register, run");
    md(r`‹write v @ t› gives the timestamp; without one, it is the event's number. Here $b$ writes after $a$ in the schedule, but with a smaller stamp:`);
    m(`replicas(lww; a, b
  a: write red @ 5
  b: write blue @ 3
  a -> b
  b -> a
)`, { work: true });
    md(r`Red wins: "last" means the largest stamp, not the latest moment, and the clocks of different machines disagree. On a tie the replica decides, the same way at every replica (here ‹b›, listed after ‹a›):`);
    m(`replicas(lww; a, b
  a: write red @ 3
  b: write blue @ 3
  a -> b
  b -> a
)`);
    sec("What it throws away");
    md(r`
> [!mistake]
> Lesson 1's lost update was an LWW register: two taps each wrote "0 plus one", and the merge kept one. LWW converges by choosing, and the loser of two concurrent writes is discarded without a trace. For a display name that is the intended meaning; for a counter it loses taps.
`);
    m(`replicas(lww; a, b
  a: write 1
  b: write 1
  a -> b
  b -> a
)`);
    md(r`The **LWW-Element-Set** puts one LWW register per element, holding "added" or "removed". It fixes the 2P-Set's re-add (a later add outranks an earlier remove), but by the clock: a remove can cancel an add its replica never saw, if its stamp happens to be larger.`);
    sec("In Lean");
    for (const c of crdtLesson(4)) lean(c);
    md(r`The book's naive merge keeps the left write on a tie. Three tied writes: swapping the order of the first merge changes the answer.`);
    lean(`example :
    LWW.naiveMerge (LWW.naiveMerge (3, 1) (3, 2)) (3, 3)
      ≠ LWW.naiveMerge (LWW.naiveMerge (3, 2) (3, 1)) (3, 3) := by decide`);
    lx(`${OPEN}theorem lww_merge_bot {R : Nat} (x : LWW.LWWReg R Nat) : ⊥ ⊔ x = x := by`, r`Prove that the never-written register is the identity of merge.`, `  exact Order.sup_bot_left x`, [r`Every bounded join-semilattice has $\bot \sqcup x = x$: look in the merge discipline's toolkit for ‹sup_bot_left›.`]);
    sec("Exercises");
    ex("associative(Naive)", r`Is the naive tie merge associative? Answer ‹true› or ‹false›.`, [r`$(x \cdot y) \cdot z$ and $x \cdot (y \cdot z)$ both give $z$.`]);
    ex("fold(Lex; w3a, w3b, w3a)", r`With ties broken by replica, a replica holding ‹w3a› hears ‹w3b›, then its own ‹w3a› again. What does it hold?`, [r`Same timestamp: the replica breaks the tie, and $b$ comes after $a$.`]);
    md(r`
> [!summary]
> Timestamps in the state turn overwrite into a join, provided ties are broken the same way everywhere; otherwise merging stops being commutative. The register converges, but one of two concurrent writes is silently discarded: converging is not the same as keeping what users did. What a set needs is a remove that cancels exactly the adds it has seen, with no clock involved.
`);
  });

  add("06-orset.chalk", "The OR-Set: add wins", "Observed-remove: tag every add, and let a remove delete only the tags it has seen, so re-adds work and a concurrent add survives.", ({ sec, md, m, ex, lean, lx }) => {
    sec("The OR-Set: add wins");
    md(r`
> [!goal]
> Build a set where a remove cancels exactly the adds its replica has seen, so that re-adds work and an add racing a remove wins.
`);
    md(r`The 2P-Set's tombstone on $x$ kills every later add of $x$; the LWW-Element-Set lets a clock decide, so a remove can kill an add its replica never saw. Both remove too much.`);
    md(r`
> [!try]
> When replica $b$ removes $x$, which adds of $x$ should that remove cancel? What would the state need so that the merge can tell?
`);
    md(r`The adds $b$ has seen, and no others: not future ones, not concurrent ones it has not heard of. To cancel "the adds I have seen" the merge must tell adds apart, so give each add a **unique tag**: the replica and its own count of adds, a pair no replica mints twice. A remove tombstones the tags of $x$ it has seen. $x$ is in the set while some tag of it is not tombstoned. A re-add mints a fresh tag, which no old tombstone covers.`);
    md(r`
> [!definition] OR-Set
> An **observed-remove set** keeps a set of tagged adds and a set of tombstoned tags, both grow-only. Adding $x$ at replica $i$ records $x$ with a fresh tag of $i$'s; removing $x$ tombstones every tag of $x$ the replica holds; merge is union on each part; $x$ is a member when it has a tag that is not tombstoned.
`);
    sec("The 2P-Set's failure, rerun");
    md(r`The schedule that lost the 2P-Set's re-add, with one more message so that both replicas hear everything:`);
    m(`replicas(twopset; a, b
  a: add x
  a -> b
  b: remove x
  a: add x
  b -> a
  a -> b
)`);
    md(r`The same schedule on an OR-Set. Each add makes a tag of its own (‹x@a1› is ‹a›'s first add); ‹b›'s remove tombstones ‹x@a1›, the only tag it has seen, and ‹x@a2› survives:`);
    m(`replicas(orset; a, b
  a: add x
  a -> b
  b: remove x
  a: add x
  b -> a
  a -> b
)`, { work: true });
    md(r`
> [!theorem] Add wins
> Replica $i$ adds $e$ to its state $s_A$; concurrently, a peer removes $e$ from its state $s_B$, which has not seen that add ($s_B$'s count for $i$ is at most $s_A$'s). If both states are well formed, then $e$ is a member of the merge of the two results. Well formed means an invariant every reachable state keeps: tombstones cover only recorded adds, and a replica's count for each replica is above every tag of that replica's it has recorded.
`);
    md(r`
> [!mistake]
> Tags must never be reused. Let the re-add recycle the old tag ‹x@a1›: then $b$'s earlier remove, which tombstoned ‹x@a1›, also kills the re-add (‹tag_reuse_bites› in the Lean below).
`);
    sec("In Lean");
    for (const c of crdtLesson(5)) lean(c);
    md(r`Tombstones are the price: they only ever accumulate.`);
    lx(`theorem orset_tombs_size_monotone {R : Nat} {s t : ORSet R} (h : s ⊑ t) :
    SList.size s.tombs ≤ SList.size t.tombs := by`, r`Prove that an OR-Set's tombstones never shrink.`, `  exact sorted_subset_length s.tombs.sorted t.tombs.sorted h.2.1`, [r`The order on OR-Set states compares the tombstone sets as its second component: ‹h.2.1›.`, r`Lesson 4's ‹sorted_subset_length› finishes it.`]);
    sec("Exercises");
    md(r`An OR-Set state for one element $x$, as a pair (tags added, tags tombstoned) over two tags: ‹t1›, an add both replicas saw, and ‹t2›, a later re-add.`);
    m("let T = subsets({t1, t2})");
    m("let OR = product(T, T)");
    ex("join(OR, ({t1, t2}, {}), ({t1}, {t1}))", r`Replica $a$ holds $(\{t1, t2\}, \{\})$. Replica $b$ removed $x$ having seen only ‹t1›: it holds $(\{t1\}, \{t1\})$. Merge them. Write it as ‹({…}, {…})›.`, [r`Union each half.`, r`‹t2› is added and not tombstoned, so $x$ is still in the set: add wins.`]);
    md(r`
> [!summary]
> A unique tag on every add makes removal precise: a remove deletes what it observed and nothing else. Re-adds work, a concurrent add survives a remove, and the cost is tombstones that never go away. Every run so far has ended with the replicas agreeing; the next lesson proves they always will.
`);
  });

  add("07-convergence.chalk", "Multisets, folds and the main theorem", "Why the three laws are exactly enough: drop one and a network breaks it; keep all three and the same updates give the same state, proved once for every CRDT.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Multisets, folds and the main theorem");
    md(r`
> [!goal]
> Prove, once for every design in this course, that replicas which have received the same updates are in the same state, and see that each of the three laws is needed.
`);
    md(r`Every run so far ended with the replicas agreeing, but a run is one schedule. Lesson 1 matched each law of a join to something the network does: commutativity to reordering, associativity to relaying, idempotence to duplication.`);
    md(r`
> [!try]
> Drop one law at a time. Which network behaviour can then make two replicas with the same updates disagree?
`);
    sec("Drop a law, break a network");
    md(r`Drop commutativity: overwrite. Two replicas hear the same two messages in different orders and disagree:`);
    m("let Ow = op({a, b}; [a, b; a, b])");
    m("fold(Ow; a, b)");
    m("fold(Ow; b, a)");
    md(r`Drop associativity: "keep the winner" of rock, paper, scissors. It is commutative and idempotent, but grouping matters:`);
    m("let RPS = op({r, p, s}; [r, p, r; p, p, s; r, s, s])");
    m("commutative(RPS)");
    m("associative(RPS)", { work: true });
    md(r`A replica that merged $r$ and $p$ and then hears $s$ holds $s$; one that holds $r$ and hears from a relay that had already merged $p$ and $s$ holds $r$. Drop idempotence: addition is commutative and associative, and one duplicated delivery counts twice (‹comm_assoc_not_enough› in the Lean below).`);
    sec("Keep all three");
    md(r`
> [!theorem] Strong eventual consistency
> In any join-semilattice, folding the join from $\bot$ over two delivery lists with the same members, in any order and with any number of repetitions, gives the same state.
`);
    md(r`On a small table, the same updates in different orders and multiplicities:`);
    m("let Mx = op({0, 1, 2, 3}; [0, 1, 2, 3; 1, 1, 2, 3; 2, 2, 2, 3; 3, 3, 3, 3])");
    m("fold(Mx; 1, 3, 2)");
    m("fold(Mx; 2, 2, 1, 3, 1)");
    md(r`The proof does not shuffle lists. Each fold is the least upper bound of the members of its list, and the two lists have the same members, so the folds are the least upper bound of the same set, and a least upper bound is unique (antisymmetry). Along the way the book makes "a list, up to order" a type, a **quotient**: lists modulo permutation are multisets, and the fold is defined on them because a permutation does not change it.`);
    sec("In Lean");
    for (const c of crdtLesson(6)) lean(c);
    md(r`Multiset union is well defined on the quotient because appending respects permutation, on either side:`);
    lean(`theorem perm_append_right {α : Type} (m : List α) {l₁ l₂ : List α}
    (h : Perm l₁ l₂) : Perm (l₁ ++ m) (l₂ ++ m) := by
  induction h with
  | nil => exact Perm.refl m
  | cons x _ ih => exact .cons x ih
  | swap x y l => exact .swap x y (l ++ m)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂`);
    lx(`theorem perm_append_left {α : Type} (m : List α) {l₁ l₂ : List α}
    (h : Perm l₁ l₂) : Perm (m ++ l₁) (m ++ l₂) := by`, r`Prove that prepending a list respects permutation.`, `  induction m with
  | nil => exact h
  | cons x t ih => exact .cons x ih`, [r`Induction on ‹m›, the list in front.`, r`‹Perm.cons x› extends a permutation by the same head.`]);
    lean(`def msetUnion {α : Type} : MSet α → MSet α → MSet α :=
  Quotient.lift₂ (fun l₁ l₂ => MSet.ofList (l₁ ++ l₂))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound
      (.trans (perm_append_right _ h₁) (perm_append_left _ h₂)))

example : msetUnion (MSet.ofList [1, 2]) (MSet.ofList [3])
    = MSet.ofList [1, 2, 3] := rfl`);
    sec("Exercises");
    ex("fold(Mx; 3, 0, 3, 1)", r`Under "keep the larger", a replica receives $3, 0, 3, 1$. What is its state?`, []);
    ex("fold(RPS; s, p, r)", r`Under the rock-paper-scissors merge, a replica receives $s$, $p$, $r$ in that order. What does it hold? (Above, $r$, $p$, $s$ gave $s$.)`, [r`$s \cdot p = s$ first.`]);
    md(r`
> [!summary]
> Each law of a join answers one thing the network does, and without any one of them some network makes replicas disagree. With all three, the main theorem holds for every state-based CRDT at once: the same set of updates, in any order and any number of times, gives the same state. Its hypothesis is "the same updates". The next lesson asks what a network must do to deliver that.
`);
  });

  add("08-delivery.chalk", "Delivery: gossip, duplication and reordering", "What the network may do to messages, why only loss matters, eventual delivery as the one requirement, and a gossip driver that provably stops.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Delivery: gossip, duplication and reordering");
    md(r`
> [!goal]
> Find the one thing a state-based CRDT needs from the network, prove that it gives convergence, and write a gossip driver whose termination Lean accepts.
`);
    md(r`The main theorem assumed that the replicas had received the same updates. A real network delays messages, delivers them out of order, delivers them twice, and loses them. Which of these can a join absorb?`);
    sec("Delayed and duplicated messages");
    md(r`‹m := a› puts a copy of ‹a›'s state in flight; ‹b <- m› delivers it, possibly later, possibly twice.`);
    md(r`
> [!try]
> Below, ‹m› leaves ‹a› after its first increment and reaches ‹b› only after ‹b› has heard ‹a›'s newer state, and then again. Predict whether the old message changes ‹b›.
`);
    m(`replicas(gcounter; a, b, c
  a: inc
  m := a
  a: inc
  a -> b
  b <- m
  b <- m
  c <- m
  b -> c
)`, { step: 0 });
    md(r`It changes nothing: an old state is below the newer one, so joining it in is a no-op, and a duplicate is idempotence at work. ‹c› gets the stale message first and catches up through ‹b›.`);
    sec("Lost messages");
    md(r`A message that never arrives is different:`);
    m(`replicas(gcounter; a, b
  a: inc
  m := a
  a: inc
)`);
    md(r`No merge can recover an update that never reached a replica. So the one requirement is **eventual delivery**: every update reaches every replica in the end, directly or relayed inside some other replica's state, after any delays and duplicates.`);
    sec("The network, twice over");
    md(r`The Lean builds the network two ways. As a **trace semantics**: a step relation on configurations (an update, a send, or the delivery of any message in flight, which stays in flight, so it can be delivered again or never), and the theorem that once every update has reached every replica, all replicas hold equal states. And as an **executable gossip driver**, run until no exchange teaches anyone anything new; Lean accepts its recursion because a measure, the number of updates still missing somewhere, strictly decreases with each exchange.`);
    sec("In Lean");
    for (const c of crdtLesson(7)) lean(c);
    md(r`Replicas never forget: what a replica has seen only grows along any execution.`);
    lx(`${OPEN}theorem seen_monotone {R : Nat} {σ : Type} [BoundedJoinSemilattice σ]
    {c₁ c₂ : Delivery.Config R σ} (h : Delivery.Reachable c₁ c₂)
    (r : Fin R) : ∀ x ∈ c₁.seen r, x ∈ c₂.seen r := by`, r`Prove that a replica's seen updates only grow along any execution.`, `  induction h with
  | refl => intro _ hx; exact hx
  | tail _ hs ih =>
      intro x hx
      have hx₂ := ih x hx
      cases hs with
      | update r' v =>
          show x ∈ (if r = r' then v :: _ else _)
          by_cases hr : r = r'
          · subst hr; simp; exact Or.inr hx₂
          · simp [hr]; exact hx₂
      | send r' r'' => exact hx₂
      | deliver r' p hp =>
          show x ∈ (if r = r' then p.2 ++ _ else _)
          by_cases hr : r = r'
          · subst hr; simp; exact Or.inr hx₂
          · simp [hr]; exact hx₂`, [
      r`Induction on the reachability derivation: ‹refl› and ‹tail›.`,
      r`In the ‹tail› case, case on the last step: an update or a delivery may add to some replica's list (‹by_cases› on whether it is ‹r›); a send changes nothing.`,
    ]);
    sec("Exercises");
    m("let C3 = chain(3)");
    m("let G = product(C3, C3)");
    ex("le(G, (1, 0), (2, 1))", r`A G-Counter replica holds $(2, 1)$ when a delayed message holding $(1, 0)$ arrives. Is the message's state below the replica's, so that delivering it changes nothing? Answer ‹true› or ‹false›.`, [r`Compare slot by slot.`]);
    md(r`
> [!summary]
> Delay, reordering and duplication cost a join nothing; only loss matters, so eventual delivery is the whole requirement, and under it every state-based CRDT converges. The gossip driver runs that argument as a program, and its termination is a theorem. One question has waited since lesson 5: LWW threw away one of two concurrent writes. How could a replica even tell that two writes were concurrent?
`);
  });

  add("09-version-vectors.chalk", "Version vectors and causality", "Time without clocks: record how much you have seen from each replica, which is the G-Counter again, and read concurrency as incomparability.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Version vectors and causality");
    md(r`
> [!goal]
> Tell "newer" from "concurrent" without clocks, by recording how many events of each replica have been seen.
`);
    md(r`LWW compared timestamps, so of two writes it always called one later, even when neither writer had seen the other's write. To do better a replica must answer a different question: had the writer of this state seen my write, or did we write without knowing of each other?`);
    md(r`
> [!try]
> What could a state carry to answer that? Think of what a G-Counter's slots record.
`);
    md(r`For each replica, how many of its events I have seen. That is a G-Counter's state read differently: a slot per replica, merged by the maximum, all zeroes at the start.`);
    md(r`
> [!definition] Version vector
> A **version vector** has one entry per replica: how many of that replica's events have been seen. Event $e$ **happened before** $f$ when $e$'s vector is strictly below $f$'s; $e$ and $f$ are **concurrent** when neither vector is below the other.
`);
    m("let C3 = chain(3)");
    m("let V = product(C3, C3)");
    m("le(V, (1, 0), (0, 1))", { work: true });
    m("le(V, (0, 1), (1, 0))");
    m("join(V, (1, 0), (0, 1))");
    md(r`A first event at replica 1 and a first event at replica 2 are concurrent: neither saw the other. Concurrency is not a failure to know the order; it is a fact about what each replica had seen. Their join, $(1, 1)$, is a history that includes both.`);
    sec("Clocks on a diagram");
    md(r`‹clocks› computes the vector of every event in a space-time diagram: each process as its events in order, each arrow a message from its sending to its receipt. Here ‹a1› sends to ‹b2›, and ‹b1› to ‹a3›:`);
    m("clocks({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)");
    md(r`‹a1› at $(1, 0)$ is below ‹b2› at $(1, 2)$: through the message, ‹a1› happened before ‹b2›. ‹a2› at $(2, 0)$ and ‹b2› at $(1, 2)$ are incomparable: concurrent. The happens-before order itself:`);
    m("let E = events({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)");
    m("concurrent(E, a2, b2)");
    md(r`With version vectors a register can keep both of two concurrent writes instead of dropping one (a multi-value register; this course does not build it), and a network can deliver **causally**: hold a message until it is the next event of its sender and everything it depends on has been seen.`);
    sec("In Lean");
    for (const c of crdtLesson(8)) lean(c);
    lx(`${OPEN}theorem vv_merge_lub {R : Nat} {v w u : VV R} (hv : v ⊑ u) (hw : w ⊑ u) :
    v ⊔ w ⊑ u := by`, r`Prove that the merged version vector is below any vector above both: it is the least upper bound of the two histories.`, `  exact sup_le v w u hv hw`, [r`It is the join's defining property, ‹sup_le›.`]);
    sec("Exercises");
    ex("le(V, (1, 1), (2, 1))", r`Is the version vector $(1, 1)$ below $(2, 1)$, so that its event happened before the other? Answer ‹true› or ‹false›.`, []);
    ex("join(V, (2, 0), (0, 1))", r`Merge the version vectors $(2, 0)$ and $(0, 1)$.`, [r`Pointwise maximum.`]);
    ex("concurrent(E, a3, b2)", r`In the diagram above, are ‹a3› and ‹b2› concurrent? Answer ‹true› or ‹false›.`, [r`Compare their clocks, $(3, 1)$ and $(1, 2)$.`]);
    md(r`
> [!summary]
> Version vectors are G-Counters that count events: their order is causality, their join merges histories, and incomparable vectors are concurrent events. Every design so far ships whole states. A state with a slot per replica grows with the system; why not ship just the operation?
`);
  });

  add("10-op-based.chalk", "Op-based CRDTs", "Shipping operations instead of states: what the join used to absorb becomes the network's job, commuting operations and exactly-once delivery.", ({ sec, md, m, lean, lx }) => {
    sec("Op-based CRDTs");
    md(r`
> [!goal]
> Ship operations instead of states, and find out what the network must then promise.
`);
    md(r`A G-Counter's state has a slot per replica. With thousands of replicas, every sync ships thousands of numbers to say "one more tap". Why not ship the operation itself, "increment slot 3"?`);
    md(r`
> [!try]
> Lesson 8's network delays, reorders, duplicates and loses messages. Which of these can a message saying "increment slot 3" survive, applied on arrival?
`);
    md(r`Reordering, yes: increments commute. Duplication, no: an increment applied twice counts twice, and there is no join to absorb the repeat. A state-based counter shrugs off the same duplicate:`);
    m(`replicas(gcounter; a, b
  a: inc
  m := a
  b <- m
  b <- m
)`);
    md(r`
> [!definition] Op-based CRDT
> In an **operation-based** CRDT a replica ships each operation it performs, and every replica applies every operation once. Concurrent operations must **commute**, so that the order of arrival does not matter, and the transport must deliver each operation **exactly once**.
`);
    md(r`
> [!mistake]
> Sets are worse. Add and remove of the same element do not commute, so an op-based set also needs causal delivery; and a duplicated old remove, delivered after a re-add, kills the re-add. The Lean below proves both (‹setops_not_comm›, ‹op_set_dup_kills_readd›), and the counter's double count (‹op_dup_overcounts›).
`);
    md(r`The burden moves from the algebra to the network, in exchange for small messages. The two readings agree where they meet: for operations that only go up, joining the states a replica would ship after each operation gives exactly the state that replaying its operations gives (‹foldJoin_statesAlong›).`);
    sec("In Lean");
    for (const c of crdtLesson(9)) lean(c);
    md(r`Increments commute, so the G-Counter is also an op-based CRDT:`);
    lx(`theorem increment_comm {R : Nat} (i j : Fin R) (g : GCounter R) :
    GCounter.increment i (GCounter.increment j g)
      = GCounter.increment j (GCounter.increment i g) := by`, r`Prove that increments commute, at any two slots (even the same one).`, `  exact (OpBased.opCounter R).comm i j g`, [r`The op-based counter above already carries this fact as its ‹comm› field.`]);
    md(r`The op-based PN-Counter: an operation is a signed increment, and everything commutes.`);
    lean(`${OPEN}def opPNCounter (R : Nat) : OpBased.OpCRDT (Bool × Fin R) (PNCounter R) where
  init := ⊥
  apply o p :=
    if o.1 then (GCounter.increment o.2 p.1, p.2)
    else (p.1, GCounter.increment o.2 p.2)
  comm o₁ o₂ s := by
    by_cases h₁ : o₁.1 <;> by_cases h₂ : o₂.1 <;> simp [h₁, h₂]
    · rw [increment_comm]
    · rw [increment_comm]`);
    md(r`
> [!summary]
> State-based CRDTs tolerate any network that eventually delivers; op-based CRDTs need commuting operations and exactly-once delivery, in exchange for small messages. For inflationary operations the Lean proves the two readings of a history agree. Every part is now built: can they be put together into one store without new proofs?
`);
  });

  add("11-capstone.chalk", "Capstone: a replicated store", "A collaborative shopping list from the course's parts: an OR-Set of items, each with a PN-Counter quantity, converging with no new proofs.", ({ sec, md, m, lean }) => {
    sec("Capstone: a replicated store");
    md(r`
> [!goal]
> Assemble a collaborative shopping list from the earlier designs, run it under a scrambled schedule, and see that its convergence needs no new proof.
`);
    md(r`Alice, Bob and Carol share a shopping list. Items come and go, and an item can be crossed off and put back; each item has a quantity that goes up and down.`);
    md(r`
> [!try]
> Which design from this course would you use for the items, and which for a quantity? Why not the others?
`);
    md(r`Items: an **OR-Set**. A G-Set cannot remove, a 2P-Set cannot re-add, and an LWW-Element-Set lets a clock cancel an add the remover never saw. Quantities: a **PN-Counter** per item. An LWW register would drop one of two concurrent changes, and a G-Counter cannot go down.`);
    sec("The list, run");
    md(r`Alice and Carol both add bread; Bob adds eggs, thinks better of it, and adds milk; then Alice crosses bread off, having seen only her own add. The messages arrive in no particular order, one of them twice:`);
    m(`replicas(orset; alice, bob, carol
  alice: add bread
  carol: add bread
  bob: add eggs
  bob: remove eggs
  bob: add milk
  alice: remove bread
  bob -> alice
  carol -> alice
  bob -> alice
  alice -> bob
  alice -> carol
)`, { work: true });
    md(r`Bread stays: Alice's remove tombstoned only her own tag, and Carol's concurrent add wins. Eggs are gone, milk is there, and all three agree. Bread's quantity, a PN-Counter, with Alice adding two and Carol one:`);
    m(`replicas(pncounter; alice, bob, carol
  alice: inc
  alice: inc
  carol: inc
  alice -> bob
  carol -> bob
  bob -> alice
  bob -> carol
)`);
    sec("Why no new proof");
    md(r`The store is a pair, an OR-Set and a map from items to PN-Counters. A product of semilattices is a semilattice (join each part), and so is a map into one (join pointwise). So the store is a state-based CRDT as it stands, and lesson 7's theorem applies to it unchanged: in the Lean, ‹sec_store› is one line. The Lean runs the whole store (items and quantities) under three schedules, orderly, reversed with duplicates, and chaotic with self-merges, and prints the same list for every replica: bread ×3, milk ×1, no eggs.`);
    sec("In Lean");
    for (const c of crdtLesson(10)) lean(c);
    md(r`
> [!summary]
> Composition is the payoff: a store built from verified parts, with lattice products and pointwise maps, inherits strong eventual consistency without a single new proof. Every replica agrees on the list. Is what they agree on always right?
`);
  });

  add("12-limits.chalk", "What CRDTs cannot do", "Agreement is not correctness: a balance that converges below zero, invariants that need coordination, and the axiom audit.", ({ sec, md, m, lean }) => {
    sec("What CRDTs cannot do");
    md(r`
> [!goal]
> Find the boundary of the promise: replicas that converge agree, but what they agree on can still be wrong, and some invariants cannot be kept without coordination.
`);
    md(r`A bank balance as a PN-Counter, with one rule: it must never go below zero. The balance is 1, and both replicas know it. Each receives a withdrawal of 1 and approves it, because locally the balance is 1.`);
    md(r`
> [!try]
> Predict the balance once the replicas have synced.
`);
    m(`replicas(pncounter; a, b
  a: inc
  a -> b
  a: dec
  b: dec
  a -> b
  b -> a
)`, { work: true });
    md(r`Both read $-1$. They have converged, and the rule is broken. No cleverer merge fixes it: in the Lean, ‹no_bank_merge› shows that no idempotent merge can honour both of two withdrawals of 80 from 100. Idempotence forces the merge of $20$ with $20$ to be $20$, while honouring both withdrawals needs $-60$. Each replica was right about its own state and neither could know about the other's withdrawal without asking it first.`);
    md(r`The same boundary showed up earlier. LWW converges by discarding one of two concurrent writes. Tombstones pile up for ever, and throwing one away safely needs to know that every replica has seen its remove: agreement about the state of everyone, which is coordination again.`);
    md(r`Invariants that span replicas (no overdraft, unique usernames, at most ten seats sold) need coordination somewhere: a lock, consensus, or an escrow that hands each replica a share it may spend alone. CRDTs are for the state that does not need it.`);
    sec("In Lean");
    for (const c of crdtLesson(11)) lean(c);
    md(r`
> [!note] The axiom audit
> The book closes by printing the axioms every headline theorem depends on. Nothing beyond propositional extensionality and quotient soundness: the whole chain, the main theorem included, is constructive.
`);
    for (const c of crdtAudit) lean(c);
    md(r`
> [!summary]
> CRDTs buy availability and convergence without coordination, and they cannot buy invariants that relate replicas. Knowing which state needs which is the design decision this course leaves you with.
`);
  });
}, { leanPrelude: true });

// ---------------------------------------------------------------------------------------------------
// Course 3. Systems are written over several lines (Shift+Enter in a cell), as a specification is.
const FENCE = "`".repeat(3);
/** Two threads add one to a shared ‹x›: each reads it into a copy (‹a›, ‹b›), then writes the copy plus one. */
const LOST = `let Inc = system(
  var x in 0..2
  var a in 0..2
  var b in 0..2
  var p in {read, write, done}
  var q in {read, write, done}
  init x = 0 ∧ a = 0 ∧ b = 0 ∧ p = read ∧ q = read
  action pread when p = read do a := x, p := write
  action pwrite when p = write do x := a + 1, p := done
  action qread when q = read do b := x, q := write
  action qwrite when q = write do x := b + 1, q := done
)`;
const COUNTER = `let C = system(
  var x in 0..3
  var y in 0..3
  init x = 0 ∧ y = 0
  action inc when x < 3 do x := x + 1
  action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1
)`;
const RACE = `let Race = system(
  var p in {idle, checked, crit}
  var q in {idle, checked, crit}
  var lock in bool
  init p = idle ∧ q = idle ∧ lock = false
  action pcheck when p = idle ∧ lock = false do p := checked
  action pset when p = checked do lock := true, p := crit
  action pexit when p = crit do p := idle, lock := false
  action qcheck when q = idle ∧ lock = false do q := checked
  action qset when q = checked do lock := true, q := crit
  action qexit when q = crit do q := idle, lock := false
)`;
const LOCKS = `let Fix = system(
  var p in {idle, crit}
  var q in {idle, crit}
  var lock in bool
  init p = idle ∧ q = idle ∧ lock = false
  action penter when p = idle ∧ lock = false do lock := true, p := crit
  action pexit when p = crit do p := idle, lock := false
  action qenter when q = idle ∧ lock = false do lock := true, q := crit
  action qexit when q = crit do q := idle, lock := false
)`;
/** Raise your flag, then wait until the other's is down. */
const FLAGS = `let Flags = system(
  var p in {idle, want, crit}
  var q in {idle, want, crit}
  var fp in bool
  var fq in bool
  init p = idle ∧ q = idle ∧ fp = false ∧ fq = false
  action pwant when p = idle do fp := true, p := want
  action penter when p = want ∧ fq = false do p := crit
  action pexit when p = crit do fp := false, p := idle
  action qwant when q = idle do fq := true, q := want
  action qenter when q = want ∧ fp = false do q := crit
  action qexit when q = crit do fq := false, q := idle
)`;
/** Peterson's algorithm: raise your flag, give the other the turn, and wait until its flag is down or the turn is yours.
 *  `f` prefixes every action (‹fair ›); `swap` writes the turn before the flag, the order that fails. */
const peterson = (name, f = "", swap = false) => `let ${name} = system(
  var p in {idle, flag, wait, crit}
  var q in {idle, flag, wait, crit}
  var fp in bool
  var fq in bool
  var turn in {P, Q}
  init p = idle ∧ q = idle ∧ fp = false ∧ fq = false ∧ turn = P
${swap ? `  ${f}action pyield when p = idle do turn := Q, p := flag
  ${f}action pflag when p = flag do fp := true, p := wait` : `  ${f}action pflag when p = idle do fp := true, p := flag
  ${f}action pyield when p = flag do turn := Q, p := wait`}
  ${f}action penter when p = wait ∧ (fq = false ∨ turn = P) do p := crit
  ${f}action pexit when p = crit do fp := false, p := idle
${swap ? `  ${f}action qyield when q = idle do turn := P, q := flag
  ${f}action qflag when q = flag do fq := true, q := wait` : `  ${f}action qflag when q = idle do fq := true, q := flag
  ${f}action qyield when q = flag do turn := P, q := wait`}
  ${f}action qenter when q = wait ∧ (fp = false ∨ turn = Q) do q := crit
  ${f}action qexit when q = crit do fq := false, q := idle
)`;
const waiter = (name, fairness) => `let ${name} = system(
  var p in {idle, crit}
  var q in {wait, crit}
  var lock in bool
  init p = idle ∧ q = wait ∧ lock = false
  action penter when p = idle ∧ lock = false do lock := true, p := crit
  action pexit when p = crit do p := idle, lock := false
  ${fairness}action qenter when q = wait ∧ lock = false do lock := true, q := crit
)`;
/** A client that tries a request at most twice over a network that loses requests and replies. With `dedup`, the
 *  server remembers that it has applied the request and only replies to a repeat. */
const client = (name, dedup) => `let ${name} = system(
  var tries in 0..2
  var req in bool
  var applied in 0..2
${dedup ? "  var seen in bool\n" : ""}  var reply in {none, flying, got}
  init tries = 0 ∧ req = false ∧ applied = 0${dedup ? " ∧ seen = false" : ""} ∧ reply = none
  action send when tries < 2 ∧ req = false ∧ reply ≠ got do tries := tries + 1, req := true
  action lose when req = true do req := false
${dedup ? `  action deliver when req = true ∧ seen = false do req := false, applied := applied + 1, seen := true, reply := flying
  action again when req = true ∧ seen = true do req := false, reply := flying` : `  action deliver when req = true do req := false, applied := applied + 1, reply := flying`}
  action loseReply when reply = flying do reply := none
  action gotReply when reply = flying do reply := got
)`;
const TWO = "let Two = system(var a in 0..2; var b in 0..2; init a = 0 ∧ b = 0; action ta when a < 2 do a := a + 1; action tb when b < 2 do b := b + 1)";
const SUM = "let Sum = system(var s in 0..4; init s = 0; action t when s < 4 do s := s + 1)";
const TS_LEAN = r`/-- A transition system on states σ: which states are initial, and which steps are allowed. -/
structure TS (σ : Type) where
  init : σ → Prop
  step : σ → σ → Prop

/-- The states a system can reach: an initial state, or a step from a reachable one. -/
inductive Reachable {σ : Type} (T : TS σ) : σ → Prop where
  | init {s : σ} : T.init s → Reachable T s
  | step {s t : σ} : Reachable T s → T.step s t → Reachable T t`;

/** Lesson 4's table of locks, one per key, made on demand: a job looks up the key's lock (`get`), making one if there
 *  is none (`new`), waits on it, works, and on the way out removes the entry (`done`: release and remove as one step).
 *  A lock is held when a job is inside with it; a new lock is the lowest name the other job does not hold. */
const keyedJob = (j, o) => `  action ${j}get when ${j} = idle ∧ tab ≠ 0 do l${j} := tab, ${j} := got
  action ${j}new when ${j} = idle ∧ tab = 0 ∧ l${o} ≠ 1 do tab := 1, l${j} := 1, ${j} := got
  action ${j}new2 when ${j} = idle ∧ tab = 0 ∧ l${o} = 1 do tab := 2, l${j} := 2, ${j} := got
  action ${j}wait when ${j} = got ∧ ¬(${o} = crit ∧ l${o} = l${j}) do ${j} := crit
  action ${j}done when ${j} = crit do tab := 0, l${j} := 0, ${j} := idle`;
const KEYED = `let Keyed = system(
  var p in {idle, got, crit}
  var q in {idle, got, crit}
  var lp in 0..2
  var lq in 0..2
  var tab in 0..2
  init p = idle ∧ q = idle ∧ lp = 0 ∧ lq = 0 ∧ tab = 0
${keyedJob("p", "q")}
${keyedJob("q", "p")}
)`;
/** The same table with a check after the take: a job that holds its lock looks at the table again and goes in only if
 *  the entry still names that lock (`ok`); otherwise it releases and starts over (`retry`). On the way out it removes
 *  the entry, then releases; with `swap`, it releases, then removes. A lock is held from the take to the release. */
const checkedJob = (j, o, swap) => `  action ${j}get when ${j} = idle ∧ tab ≠ 0 do l${j} := tab, ${j} := got
  action ${j}new when ${j} = idle ∧ tab = 0 ∧ l${o} ≠ 1 do tab := 1, l${j} := 1, ${j} := got
  action ${j}new2 when ${j} = idle ∧ tab = 0 ∧ l${o} = 1 do tab := 2, l${j} := 2, ${j} := got
  action ${j}wait when ${j} = got ∧ ¬((${o} = took ∨ ${o} = crit${swap ? "" : ` ∨ ${o} = out`}) ∧ l${o} = l${j}) do ${j} := took
  action ${j}ok when ${j} = took ∧ tab = l${j} do ${j} := crit
  action ${j}retry when ${j} = took ∧ tab ≠ l${j} do l${j} := 0, ${j} := idle
${swap ? `  action ${j}release when ${j} = crit do ${j} := out
  action ${j}remove when ${j} = out do tab := 0, l${j} := 0, ${j} := idle` : `  action ${j}remove when ${j} = crit do tab := 0, ${j} := out
  action ${j}release when ${j} = out do l${j} := 0, ${j} := idle`}`;
const checked = (name, swap = false) => `let ${name} = system(
  var p in {idle, got, took, crit, out}
  var q in {idle, got, took, crit, out}
  var lp in 0..2
  var lq in 0..2
  var tab in 0..2
  init p = idle ∧ q = idle ∧ lp = 0 ∧ lq = 0 ∧ tab = 0
${checkedJob("p", "q", swap)}
${checkedJob("q", "p", swap)}
)`;
/** The table with a count of the jobs using the entry, raised in the same step as the lookup; the last job out
 *  removes the entry. */
const countedJob = (j, o) => `  action ${j}get when ${j} = idle ∧ tab ≠ 0 do l${j} := tab, n := n + 1, ${j} := got
  action ${j}new when ${j} = idle ∧ tab = 0 ∧ l${o} ≠ 1 do tab := 1, l${j} := 1, n := 1, ${j} := got
  action ${j}new2 when ${j} = idle ∧ tab = 0 ∧ l${o} = 1 do tab := 2, l${j} := 2, n := 1, ${j} := got
  action ${j}wait when ${j} = got ∧ ¬(${o} = crit ∧ l${o} = l${j}) do ${j} := crit
  action ${j}leave when ${j} = crit ∧ n > 1 do n := n - 1, l${j} := 0, ${j} := idle
  action ${j}last when ${j} = crit ∧ n = 1 do n := 0, tab := 0, l${j} := 0, ${j} := idle`;
const COUNTED = `let Counted = system(
  var p in {idle, got, crit}
  var q in {idle, got, crit}
  var lp in 0..2
  var lq in 0..2
  var tab in 0..2
  var n in 0..2
  init p = idle ∧ q = idle ∧ lp = 0 ∧ lq = 0 ∧ tab = 0 ∧ n = 0
${countedJob("p", "q")}
${countedJob("q", "p")}
)`;

course("systems", "Transition systems, invariants and temporal logic",
  "A lost update as a path in a graph of states; invariants with counterexample traces and inductive proofs; a lock that fails and Peterson's that does not; one lock per key, and the gap between two atomic calls; safety and liveness under fairness; temporal logic as fixed points; happens-before, effectively-once delivery and refinement; rewriting systems, and retries under failure.",
  "Distributed systems", (add) => {

  add("01-state-machines.chalk", "State machines and executions", "Two threads that lose an update: a system as variables, an initial state and guarded actions, and its graph of reachable states as every interleaving at once.", ({ sec, md, m, ex, lean, lx }) => {
    sec("State machines and executions");
    md(r`
> [!goal]
> Find the order of steps in which two threads lose an update, by drawing every order at once.
`);
    md(r`Two threads each add one to a shared counter ‹x›, which starts at 0. Each does it as a processor does: read ‹x› into a copy of its own, then write back the copy plus one. When both have finished, ‹x› is 2.`);
    md(r`
> [!try]
> Is it? Each thread takes two steps, so there are six orders of the four steps. Before reading on, find one that leaves $x = 1$.
`);
    sec("A model");
    md(r`Write down only what the question needs: the shared ‹x›; each thread's copy, ‹a› for thread ‹p› and ‹b› for ‹q›; and where each thread is (‹read›, ‹write›, ‹done›). Each step is an **action**: a **guard**, when it may happen, and **updates**, what it changes, all at once. (In a cell, Shift+Enter starts a new line; Enter runs it.)`);
    m(LOST);
    md(r`Run ‹p› to the end, then ‹q›:`);
    m("trace(Inc; pread, pwrite, qread, qwrite)", { step: 0 });
    md(r`Now let both read before either writes:`);
    m("trace(Inc; pread, qread, pwrite, qwrite)", { step: 0 });
    md(r`Both copied 0 and both wrote 1: ‹q›'s write erased ‹p›'s. This is a **lost update**. Running the program a thousand times may never show it: the scheduler has to switch threads between a read and the write after it.`);
    md(r`A step whose guard fails cannot be taken: ‹q› cannot write before it has read.`);
    m("trace(Inc; qwrite)");
    sec("Every interleaving at once");
    md(r`Rather than try the six orders one at a time, draw every state the threads can be in and every step between them. The graph is drawn in rows: the initial state on top, each row one step further.`);
    m("states(Inc)");
    md(r`Each path down from the top is one order. The six orders share most of their states, so 13 states and 14 steps hold all of them. Three states end the graph: two with $x = 2$, one with $x = 1$. With a large graph we would not look; we would ask:`);
    m("reach(Inc, p = done ∧ q = done ∧ x = 1)", { step: 0 });
    md(r`The search goes breadth-first, row by row, so the first path it finds is a shortest one: here four steps, the second order we ran.`);
    md(r`
> [!definition] Transition system
> A **state** gives each variable a value. A **transition system** says which states are **initial** and which **steps** from one state to the next are allowed; actions describe the steps. An **execution** is a sequence of states, each a step from the one before. A state is **reachable** when some execution from an initial state gets there.
`);
    sec("In Lean");
    md(r`The same notions as definitions: a system is its initial predicate and its step relation, and reachability is the least set that contains the initial states and is closed under steps.`);
    lean(TS_LEAN);
    lean(r`/-- A counter that counts up to 3. -/
def counter : TS Nat where
  init s := s = 0
  step s t := s < 3 ∧ t = s + 1`);
    lx(`theorem counter_reaches_two : Reachable counter 2 := by`, r`Prove that the counter can reach 2: build the execution.`, `  exact .step (.step (.init rfl) ⟨by decide, rfl⟩) ⟨by decide, rfl⟩`, [
      r`Start from ‹.init rfl› (0 is initial), then take two ‹.step›s.`,
      r`Each step needs a proof of ‹s < 3 ∧ t = s + 1›: ‹⟨by decide, rfl⟩›.`,
    ]);
    sec("Exercises");
    md(r`Answer ‹true› or ‹false›.`);
    ex("reach(Inc, p = done ∧ q = done ∧ x = 0)", r`Can both threads finish and leave $x = 0$?`, [r`Every write writes a copy plus one.`]);
    md(r`Three threads, ‹p›, ‹q› and ‹r›, with copies ‹a›, ‹b› and ‹c›:`);
    m(`let Inc3 = system(
  var x in 0..3
  var a in 0..3
  var b in 0..3
  var c in 0..3
  var p in {read, write, done}
  var q in {read, write, done}
  var r in {read, write, done}
  init x = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0 ∧ p = read ∧ q = read ∧ r = read
  action pread when p = read do a := x, p := write
  action pwrite when p = write do x := a + 1, p := done
  action qread when q = read do b := x, q := write
  action qwrite when q = write do x := b + 1, q := done
  action rread when r = read do c := x, r := write
  action rwrite when r = write do x := c + 1, r := done
)`);
    ex("reach(Inc3, p = done ∧ q = done ∧ r = done ∧ x = 1)", r`Predict, then check: can all three finish with $x = 1$, two of the three increments lost?`, [r`One stale copy, written last, erases everything written since it was read.`], { hide: true });
    md(r`
> [!summary]
> A system is variables, initial states and guarded actions. Its graph of reachable states holds every interleaving of its steps at once, and a breadth-first search through it finds a shortest path to any state we ask for: here, the lost update.
`);
    md(r`$x = 2$ at the end is not guaranteed. What *is* guaranteed in every reachable state, and how can we know it when the graph is too large to draw? That is the next lesson.`);
  });

  add("02-invariants.chalk", "Invariants and induction", "What holds in every reachable state: refuted by a shortest trace, proved by one step of induction, and strengthened when that step fails.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Invariants and induction");
    md(r`
> [!goal]
> Check that a property holds in every reachable state, then prove it by looking at one step instead of every state.
`);
    md(r`Lesson 1's threads can lose an update, so "when both are done, $x = 2$" is false. Something weaker should survive: whichever thread writes last writes a copy plus one.`);
    md(r`
> [!try]
> Is "when both are done, $x \ge 1$" true in every reachable state?
`);
    m(LOST);
    m("invariant(Inc, p = done ∧ q = done → x = 2)", { step: 0 });
    m("invariant(Inc, p = done ∧ q = done → x ≥ 1)");
    md(r`‹invariant› turns ‹reach› around: it searches for a state that breaks the formula, and gives a shortest path there when there is one (the lost update again).`);
    md(r`
> [!definition] Invariant
> A state formula is an **invariant** when it holds in every reachable state. A **counterexample** is an execution from an initial state to a state where it fails.
`);
    sec("One step instead of every state");
    md(r`The search visited all 13 reachable states. A real program has billions, and a program whose counter can grow without bound has infinitely many. Ask instead what one step can do. If the formula holds at the start, and no step from a state where it holds can break it, then it holds after one step, so after two, so after any number: in every reachable state.`);
    md(r`
> [!theorem] Proof by induction
> If $I$ holds in every initial state, and every step from a state where $I$ holds leads to one where $I$ holds, then $I$ holds in every reachable state. Such an $I$ is **inductive**.
`);
    md(r`Checking that is local: take any state where $I$ holds, reachable or not, and try every action. Nothing needs to know which states are reachable. Two counters that step together:`);
    m(`let Pair = system(
  var x in 0..6
  var y in 0..6
  init x = 0 ∧ y = 0
  action step when x < 5 do x := x + 1, y := y + 1
)`);
    m("invariant(Pair, y ≤ 5)");
    md(r`
> [!try]
> $y \le 5$ holds in all 6 reachable states. Is it inductive?
`);
    m("inductive(Pair, y ≤ 5)", { work: true });
    md(r`No. The check found $x = 0, y = 5$: $y \le 5$ holds there, and a step makes $y = 6$. No execution reaches that state, but the check does not know that; that is the price of not searching. $y \le 5$ is true, yet too weak to carry itself through a step.`);
    md(r`
> [!mistake]
> The natural repair is to bound $x$ as well. It changes nothing: $x = 0, y = 5$ still satisfies $x \le 5 \land y \le 5$.
`);
    m("inductive(Pair, x ≤ 5 ∧ y ≤ 5)");
    md(r`What rules that state out is the reason $y \le 5$ is true at all: $y$ moves with $x$, and $x$ stops at 5. **Strengthen** the formula with that reason:`);
    m("inductive(Pair, x = y ∧ y ≤ 5)");
    md(r`A stronger formula is easier to prove, because the step may assume more. It is the same move as strengthening the hypothesis of an induction in a proof.`);
    sec("In Lean");
    md(r`The induction principle, proved once for every system:`);
    lx(`theorem invariant_of_inductive {σ : Type} (T : TS σ) (I : σ → Prop)
    (hinit : ∀ s, T.init s → I s) (hstep : ∀ s t, I s → T.step s t → I t) :
    ∀ s, Reachable T s → I s := by`, r`Prove the induction principle for invariants: by induction on reachability.`, `  intro s h
  induction h with
  | init hs => exact hinit _ hs
  | step _ hst ih => exact hstep _ _ ih hst`, [r`‹intro s h›, then ‹induction h› gives a case per constructor of ‹Reachable›.`, r`In the ‹step› case, the hypothesis says ‹I› holds before the step.`]);
    md(r`Applied to lesson 1's counter, whose states are all of ‹Nat›: the proof never asks which of them are reachable.`);
    lean(r`theorem counter_le_three : ∀ s, Reachable counter s → s ≤ 3 := by
  apply invariant_of_inductive
  · intro s hs; simp [counter] at hs; omega
  · intro s t _ hst; simp [counter] at hst; omega`);
    sec("Exercises");
    md(r`A pair where $y$ goes up twice as fast:`);
    m("let Dbl = system(var x in 0..6; var y in 0..12; init x = 0 ∧ y = 0; action step when x < 5 do x := x + 1, y := y + 2)");
    ex("invariant(Dbl, y ≤ 10)", r`Is $y \le 10$ an invariant of ‹Dbl›?`, []);
    ex("inductive(Dbl, y ≤ 10)", r`Is $y \le 10$ inductive?`, [r`Look for a state with $y \le 10$, not reachable, from which a step passes 10.`]);
    ex("inductive(Dbl, y = 2x ∧ x ≤ 5)", r`Strengthen it with what makes it true: is $y = 2x \land x \le 5$ inductive?`, [r`Initially $0 = 2 \cdot 0$; a step adds 1 to $x$ and 2 to $y$, and only when $x < 5$.`]);
    md(r`
> [!summary]
> An invariant holds in every reachable state, and a shortest trace refutes it. An inductive invariant is proved by one step from any state where it holds, reachable or not, so it needs no search. When that step fails at an unreachable state, strengthen the formula with the reason it is true.
`);
    md(r`Lesson 1's bug came from two threads inside the same read-then-write at once. Next: build a lock that lets one in at a time, and let the checker say whether it works.`);
  });

  add("03-mutual-exclusion.chalk", "Mutual exclusion", "A lock built from a check and a take, the race the checker finds, two fixes (an atomic step, and Peterson's flags and turn), and an inductive proof.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Mutual exclusion");
    md(r`
> [!goal]
> Build a lock that lets at most one thread into its critical section, find what is wrong with the first attempts from the checker's traces, and prove the fix.
`);
    md(r`The lost update needs both threads between a read and a write. Make that stretch a **critical section** that at most one thread may be in. The obvious lock: look at it, and if it is free, take it. Two threads, one lock:`);
    m(RACE);
    md(r`
> [!try]
> Can both threads get in? If so, in how few steps?
`);
    m("invariant(Race, ¬(p = crit ∧ q = crit))", { step: 0 });
    md(r`Both look while the lock is free, then both take it: **check, then act**, with a gap between. It is lesson 1's bug again, one level up: reading the lock and writing it are separate steps.`);
    sec("Closing the gap");
    md(r`Make the check and the take one action, as a compare-and-set instruction or a database's conditional write does:`);
    m(LOCKS);
    m("invariant(Fix, ¬(p = crit ∧ q = crit))");
    md(r`The checker has tried all 3 reachable states. For a proof, lesson 2's induction: is "not both inside" inductive?`);
    m("inductive(Fix, ¬(p = crit ∧ q = crit))", { work: true });
    md(r`Not by itself: from an unreachable state where ‹q› is inside without the lock, ‹p› can enter. What rules it out is why the lock works: whoever is inside holds the lock. Strengthened with that, it is inductive:`);
    m("inductive(Fix, (p = crit → lock = true) ∧ (q = crit → lock = true) ∧ ¬(p = crit ∧ q = crit))");
    sec("Without an atomic step");
    md(r`Can two threads exclude each other with nothing but ordinary reads and writes? Give each a flag. Raising it first, then looking, closes the gap: a thread only looks once its own flag is up.`);
    m(FLAGS);
    m("invariant(Flags, ¬(p = crit ∧ q = crit))");
    m("deadlock(Flags)", { step: 0 });
    md(r`Safe, but both can raise their flags and then wait for each other for ever: a **deadlock**. The trace says what is missing: a tie-breaker for when both want in. Add a shared ‹turn›. After raising its flag, each thread gives the turn to the other, and enters once the other's flag is down or the turn has come back to it. Whoever wrote ‹turn› last waits. This is **Peterson's algorithm**:`);
    m(peterson("Peterson"));
    m("invariant(Peterson, ¬(p = crit ∧ q = crit))");
    m("deadlock(Peterson)");
    sec("In TLA+");
    md(`The atomic lock in TLA+, for the TLC model checker:

${FENCE}
VARIABLES p, q, lock
Init == p = "idle" /\\ q = "idle" /\\ lock = FALSE
PEnter == p = "idle" /\\ lock = FALSE /\\ p' = "crit" /\\ lock' = TRUE /\\ UNCHANGED q
PExit  == p = "crit" /\\ p' = "idle" /\\ lock' = FALSE /\\ UNCHANGED q
QEnter == q = "idle" /\\ lock = FALSE /\\ q' = "crit" /\\ lock' = TRUE /\\ UNCHANGED p
QExit  == q = "crit" /\\ q' = "idle" /\\ lock' = FALSE /\\ UNCHANGED p
Next == PEnter \\/ PExit \\/ QEnter \\/ QExit
MutualExclusion == ~(p = "crit" /\\ q = "crit")
${FENCE}

The primed variables are the next state's; ‹UNCHANGED› says what an action leaves alone, which a system cell leaves implicit.`);
    sec("In Lean");
    md(r`The atomic lock again, and lesson 2's induction with the strengthened invariant:`);
    lean(r`/-- Two processes and a lock: each is in its critical section or not. -/
structure Mutex where
  p : Bool
  q : Bool
  lock : Bool
  deriving DecidableEq, Repr

def mutex : TS Mutex where
  init s := s = ⟨false, false, false⟩
  step s t :=
    (s.p = false ∧ s.lock = false ∧ t = { s with p := true, lock := true }) ∨
    (s.p = true ∧ t = { s with p := false, lock := false }) ∨
    (s.q = false ∧ s.lock = false ∧ t = { s with q := true, lock := true }) ∨
    (s.q = true ∧ t = { s with q := false, lock := false })

/-- The strengthened invariant: whoever is inside holds the lock, and not both are inside. -/
def MutexInv (s : Mutex) : Prop :=
  (s.p = true → s.lock = true) ∧ (s.q = true → s.lock = true) ∧ ¬(s.p = true ∧ s.q = true)`);
    lx(`theorem mutexInv_init : MutexInv ⟨false, false, false⟩ := by`, r`Prove that the strengthened invariant holds initially.`, `  simp [MutexInv]`, [r`Unfold ‹MutexInv›: every part is about ‹false = true›.`]);
    lean(r`theorem mutex_safe : ∀ s, Reachable mutex s → ¬(s.p = true ∧ s.q = true) := by
  intro s h
  have : MutexInv s := by
    apply invariant_of_inductive mutex MutexInv _ _ s h
    · intro s hs; simp [mutex] at hs; subst hs; exact mutexInv_init
    · intro s t hI hst
      obtain ⟨hp, hq, hpq⟩ := hI
      rcases s with ⟨p, q, l⟩
      simp only [mutex] at hst
      rcases hst with ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ <;>
        simp_all [MutexInv] <;> cases p <;> cases q <;> simp_all
  exact this.2.2`);
    sec("Exercises");
    md(r`Peterson's algorithm with its two writes the other way round: give away the turn first, then raise the flag.`);
    m(peterson("Swapped", "", true));
    ex("reach(Swapped, p = crit ∧ q = crit)", r`Can both threads be inside at once in ‹Swapped›? Answer ‹true› or ‹false›.`, [r`Let ‹p› give away the turn, then ‹q›: now the turn is ‹p›'s. Can ‹q› get in before ‹p›'s flag goes up?`], { hide: true });
    md(r`Strict alternation: one shared ‹turn›, and each thread hands it over on the way out.`);
    m(`let Turn = system(
  var p in {idle, crit}
  var q in {idle, crit}
  var turn in {P, Q}
  init p = idle ∧ q = idle ∧ turn = P
  action penter when p = idle ∧ turn = P do p := crit
  action pexit when p = crit do p := idle, turn := Q
  action qenter when q = idle ∧ turn = Q do q := crit
  action qexit when q = crit do q := idle, turn := P
)`);
    ex("invariant(Turn, ¬(p = crit ∧ q = crit))", r`Is ‹Turn› safe: never both inside?`, []);
    ex("deadlock(Turn)", r`Can ‹Turn› deadlock?`, []);
    md(r`
> [!summary]
> A lock that checks and then takes is a race, because the check and the take are separate steps; the checker finds the interleaving. One fix makes them one step, and an inductive invariant ("inside means holding the lock") proves it. Without an atomic step, flags alone deadlock, and Peterson's turn breaks the tie; the order of its two writes matters.
`);
    md(r`‹Turn› passes both checks, yet ‹p› cannot go in twice in a row: if ‹q› stops wanting in, ‹p› waits for ever. No state is bad; a good thing just never happens. Saying that needs a second kind of property, lesson 5's. Before that, the lock as programs keep it: one per key, in a table, with calls that each promise to be one step.`);
  });

  add("04-per-key-locks.chalk", "Linearizability and per-key locks", "One lock per key, made on demand: why a library call may be one step and two calls may not, the run in which two jobs hold two locks for one key, a fresh name as all a new lock is, and a fix proved by induction.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Linearizability and per-key locks");
    md(r`
> [!goal]
> Model a table with one lock per key, made on demand; say why each call on the table or on a lock is one step and the pair of them is not; find the run in which two jobs hold two different locks for one key; and fix it, with a proof.
`);
    md(r`A service runs jobs for many customers. Two jobs for the same customer must not overlap; jobs for different customers may. Lesson 3's lock, one for everything, would make every customer wait for every other. So keep a **table**: one lock per customer, made the first time a job for that customer arrives, and removed when the job is done, so that the table does not grow with every customer ever seen. A job for customer ‹key›:`);
    md(`${FENCE}
lock = table.getOrAdd(key, new Lock())    // the entry, made if there is none
lock.wait()                               // blocks until the lock is free
… the work for key …
lock.release()
table.remove(key)
${FENCE}

In .NET this is a ‹ConcurrentDictionary› of ‹SemaphoreSlim›s; in Go a ‹sync.Map› of mutexes. The shape is the same everywhere, and so is the bug.`);
    md(r`
> [!try]
> Each line is a call that the library promises is atomic. Is the sequence? Before reading on, find an order of two jobs' steps that puts both into the work at once.
`);
    sec("When is a call one step?");
    md(r`
> [!definition] Linearizability
> A call on a shared object is **linearizable** when it appears to take effect at one instant between its start and its return. An object is linearizable when every history of overlapping calls on it has the same effect as some sequence of those calls, one at a time, in an order that keeps each call before every call that started after it returned (Herlihy and Wing, 1990).
`);
    md(r`That is the licence for a model. A linearizable call is one action: its guard is when the instant can come (‹wait›'s instant comes when the lock is free), its updates are what the instant does. The real call runs many instructions, and the promise says that no one can tell. Lesson 3 used it without saying so: a compare-and-set is linearizable, and ‹Fix› made it one action. A table's ‹getOrAdd› and ‹remove›, a lock's ‹wait› and ‹release›: each comes with the promise.`);
    md(r`The promise ends at the call's return. Two calls in a row are two instants with a gap between them, and lesson 3's check-then-act lived in such a gap: two calls on the one lock. Here the calls are on two objects, the table and the lock, and the gap is between the table's answer and the lock's take.`);
    sec("A model");
    md(r`Two jobs, ‹p› and ‹q›, for one customer (jobs for different customers never meet at an entry, so one key is enough). Each job is ‹idle›, has ‹got› a lock from the table, or is inside (‹crit›). ‹lp› and ‹lq› name the lock each job got, 0 for none; ‹tab› names the lock the table's entry holds, 0 for no entry. A new lock is a name no one has: the lowest of 1 and 2 that the other job does not hold (‹pnew›, ‹pnew2›). A lock is held when a job is inside with it, so ‹wait› is enabled when the other job is not inside with the same name. The model makes ‹release› and ‹remove› one step, ‹done›: joining two calls can only hide interleavings, so a bug the joined model finds, the program has too.`);
    m(KEYED);
    md(r`‹p› makes the lock and goes in; ‹q› looks it up, waits for ‹p›, and goes in after. The lock did its job:`);
    m("trace(Keyed; pnew, qget, pwait, pdone, qwait, qdone)", { step: 0 });
    md(r`
> [!try]
> Now let ‹p› come back for another job for the same customer. Find a run in which both are inside.
`);
    m("invariant(Keyed, ¬(p = crit ∧ q = crit))", { step: 0 });
    md(r`‹p› makes lock 1 and goes in; ‹q› looks up lock 1 and waits on it. ‹p› finishes and removes the entry. ‹p›'s next job finds no entry, makes lock 2, and goes in. ‹q›'s wait on lock 1 succeeds: both inside. Each job holds a lock. They hold different locks. The table was there to give both jobs one name for "the lock for this key", and in the gap between ‹q›'s lookup and its take, that name went stale.`);
    md(r`What should have held, and does not:`);
    m("invariant(Keyed, (p = crit → lp = tab) ∧ (q = crit → lq = tab))", { step: 0 });
    md(r`Whoever is inside holds the lock the table names now. ‹q› is inside with lock 1 and the table names nothing: ‹p› removed the entry. From there, ‹p›'s next job makes lock 2. This is the property a per-key lock rests on: with it, two jobs inside hold the table's one name, and a lock has one holder.`);
    sec("Fresh names");
    md(r`‹new Lock()› gives a name no one else has, and that is all it gives: one lock is told from another only by being a different one. The model gives out 1 and 2 in turn, and two names are enough for two jobs, because a name nobody holds any more can be given out again: nothing can tell it from a new one. In the process calculi this is **restriction**, $\nu x$: a name known to no one else, with the rule that a name no one knows is as good as new. In those words, the bug is two jobs holding different names for what the table was to make one name, the lock for this key.`);
    sec("Checking after the take");
    md(r`The gap cannot be closed: the table and the lock are two objects, and no call takes from both at once. Lesson 3 closed its gap by making the check and the take one step. Here, keep the gap and check after the take instead: once a job holds its lock, it looks at the table again. If the entry still names its lock, it goes in; if not, someone removed the entry while it waited, so it releases and starts over. And on the way out it removes the entry first, then releases:`);
    md(`${FENCE}
loop:
  lock = table.getOrAdd(key, new Lock())
  lock.wait()
  if table.get(key) ≠ lock: lock.release(); continue
  … the work for key …
  table.remove(key)
  lock.release()
  break
${FENCE}

A job is ‹idle›, has ‹got› a lock, has taken it (‹took›), is inside (‹crit›), or is on the way ‹out› with the entry removed and the lock still held. A lock is held from the take to the release.`);
    m(checked("Checked"));
    m("invariant(Checked, ¬(p = crit ∧ q = crit))");
    md(r`For a proof, lesson 2's induction. "Inside means holding the table's lock" is not inductive by itself:`);
    m("inductive(Checked, (p = crit → lp = tab) ∧ (q = crit → lq = tab) ∧ ¬(p = crit ∧ q = crit))", { work: true });
    md(r`The counterexample starts from a state no run reaches: ‹q› inside with no lock at all (‹lq = 0›) and no entry in the table; then ‹p›'s new entry names a lock ‹q› does not hold. What rules such states out is why the check works: a job has a name exactly when it is not idle, and a lock has one holder, from the take to the release. With both, it is inductive:`);
    m("inductive(Checked, (p = crit → lp = tab) ∧ (q = crit → lq = tab) ∧ ¬((p = took ∨ p = crit ∨ p = out) ∧ (q = took ∨ q = crit ∨ q = out) ∧ lp = lq) ∧ (p = idle → lp = 0) ∧ (q = idle → lq = 0) ∧ (p ≠ idle → lp ≠ 0) ∧ (q ≠ idle → lq ≠ 0))");
    sec("In Lean");
    md(r`A fresh name, as a function: one more than the largest name in use. The lemma is the whole of what "fresh" means.`);
    lean(r`/-- A name no lock in use has: one more than the largest. -/
def freshName (used : List Nat) : Nat := used.foldr max 0 + 1

/-- Every name in use is at most the largest. -/
theorem le_foldr_max (used : List Nat) : ∀ x ∈ used, x ≤ used.foldr max 0 := by
  intro x hx
  induction used with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldr]
    rcases List.mem_cons.mp hx with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)`);
    lx(`theorem freshName_not_mem (used : List Nat) : freshName used ∉ used := by`, r`Prove that the fresh name is not in use.`, `  intro h
  have := le_foldr_max used _ h
  simp only [freshName] at this
  omega`, [
      r`Suppose it is in use (‹intro h›): then by ‹le_foldr_max› it is at most the largest name.`,
      r`Unfold ‹freshName› in that fact (‹simp only [freshName] at this›); ‹omega› finishes.`,
    ]);
    sec("Exercises");
    md(r`The same check, with the two calls on the way out the other way round: release, then remove.`);
    m(checked("Swapped", true));
    ex("invariant(Swapped, ¬(p = crit ∧ q = crit))", r`Is ‹Swapped› safe: never both inside? Answer ‹true› or ‹false›.`, [r`After ‹p› releases, ‹q› can take lock 1 and pass its check: the entry is still there.`, r`Then ‹p› removes the entry, and ‹p›'s next job makes lock 2.`], { hide: true });
    ex("reach(Keyed, p = crit ∧ tab = 0)", r`In ‹Keyed›, can a job be inside while the table has no entry for the key? Answer ‹true› or ‹false›.`, [r`Let ‹q› look up ‹p›'s lock, go in and finish before ‹p› takes it.`], { hide: true });
    md(r`A different fix counts the jobs using the entry. The lookup raises the count in the same step, and the last job out removes the entry. The table has to offer that: an update of the entry, lock and count together, as one call.`);
    m(COUNTED);
    ex("invariant(Counted, ¬(p = crit ∧ q = crit))", r`Is ‹Counted› safe: never both inside?`, []);
    ex("reach(Counted, tab = 2)", r`Does ‹Counted› ever make a second lock? Answer ‹true› or ‹false›.`, [r`The entry goes only when the count is 0, so no job holds the old name, and the lowest free name is 1 again.`], { hide: true });
    md(r`
> [!summary]
> A linearizable call takes effect at one instant, so a model may make it one action; the promise ends at the call's return. The gap between two calls, on the table and on the lock, is where a per-key lock fails: the entry is removed and made again between a lookup and a take, and two jobs hold two locks for one key. A new lock is only a fresh name. Checking the table again after the take, and removing before releasing, fixes it; an inductive invariant proves it.
`);
    md(r`‹Checked› never lets two in. But a job can take its lock, find the entry gone, and start over, and nothing says it will not find it gone every time, while the other job goes round and round. No state is bad; a good thing just never happens. Saying that needs a second kind of property, the next lesson's.`);
  });

  add("05-safety-liveness.chalk", "Safety and liveness", "Nothing bad happens; something good eventually does. Finite counterexamples and infinite ones, deadlocks and lassos, and the fairness a scheduler must promise.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Safety and liveness");
    md(r`
> [!goal]
> Tell "nothing bad happens" from "something good eventually happens" by the shape of their counterexamples, and see which promise from the scheduler makes "eventually" true.
`);
    md(r`A lock that never lets anyone in is perfectly safe: no state ever has both threads inside. Lesson 3's flags came close to that. So mutual exclusion is not all we want; we also want each thread that is waiting to get in, eventually.`);
    md(r`The two claims fail differently. "Never both inside" fails at a moment: show the trace up to the bad state, and it is refuted, whatever comes after. "Eventually gets in" fails at no moment: after any trace that can go on, the thread might still get in later. A counterexample has to be a whole run that never gets there: one that stops, or one that goes on for ever.`);
    md(r`
> [!definition] Safety and liveness
> A **safety** property says nothing bad ever happens; a finite trace refutes it (invariants are safety properties). A **liveness** property says something good eventually happens; no trace that can still go on refutes it, only a complete run that never gets there: one that stops in a **deadlock**, where no action is enabled, or, on a finite system, a **lasso**, a path into a loop that repeats for ever.
`);
    md(r`Lesson 3's flags gave a run of the first kind: both flags up, both threads waiting, no action enabled. Runs of the second kind need a closer look.`);
    sec("Runs that loop, and fairness");
    md(r`Here nothing stops. Thread ‹q› waits to enter; thread ‹p› has work of its own, and alternates between working and resting.`);
    m(`let Spin = system(
  var p in {idle, busy}
  var q in {wait, crit}
  init p = idle ∧ q = wait
  action pwork when p = idle do p := busy
  action prest when p = busy do p := idle
  action qenter when q = wait do q := crit
)`);
    md(r`
> [!try]
> Does ‹q› always get in eventually?
`);
    m("eventually(Spin, q = crit)", { step: 0 });
    md(r`No: the lasso runs ‹p› for ever and never ‹q›, though ‹qenter› is enabled all along. That is not a bug in the threads; it is a scheduler that never runs ‹q›. Liveness in a concurrent system rests on a promise from the scheduler: a **fairness** assumption. **Weak fairness** for an action: if it stays enabled, it is eventually taken. A system marks such an action ‹fair›:`);
    m(`let Spin2 = system(
  var p in {idle, busy}
  var q in {wait, crit}
  init p = idle ∧ q = wait
  action pwork when p = idle do p := busy
  action prest when p = busy do p := idle
  fair action qenter when q = wait do q := crit
)`);
    m("eventually(Spin2, q = crit)");
    md(r`Weak fairness is not always enough. Put the lock back: ‹p› takes and releases it over and over, and ‹q› needs it free.`);
    m(waiter("W", "fair "));
    m("eventually(W, q = crit)", { step: 0 });
    md(r`On this lasso ‹qenter› is enabled only while ‹p› is out, never continuously, so weak fairness owes ‹q› nothing. **Strong fairness**: if an action is enabled again and again, it is eventually taken.`);
    m(waiter("S", "strong fair "));
    m("eventually(S, q = crit)");
    md(r`Peterson's algorithm needs only the weak promise, for every step. If ‹p› comes round again while ‹q› waits, its next move hands ‹q› the turn; from then on ‹q›'s way in stays open, and ‹p›'s is shut, until ‹q› has been through.`);
    m(peterson("Peterson", "fair "));
    m("eventually(Peterson, q = crit)");
    sec("In Lean");
    md(r`Termination is liveness too: every run reaches a final state. Its proof is a measure, a natural number that every step lowers, because such a number cannot go down for ever.`);
    lx(`theorem no_infinite_descent (f : Nat → Nat) (h : ∀ n, f (n + 1) < f n) : False := by`, r`Prove that no sequence of natural numbers decreases forever.`, `  have key : ∀ n, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => have := h k; omega
  have := key (f 0 + 1)
  omega`, [
      r`Show first that $f(n) + n \le f(0)$ for every $n$, by induction.`,
      r`Then take $n = f(0) + 1$: impossible.`,
    ]);
    sec("Exercises");
    md(r`Two workers each need two forks, and take them in opposite orders: ‹a› takes fork 1 first, ‹b› fork 2.`);
    m(`let Forks = system(
  var a in {idle, one, both}
  var b in {idle, one, both}
  var f1 in bool
  var f2 in bool
  init a = idle ∧ b = idle ∧ f1 = false ∧ f2 = false
  action a1 when a = idle ∧ f1 = false do a := one, f1 := true
  action a2 when a = one ∧ f2 = false do a := both, f2 := true
  action arel when a = both do a := idle, f1 := false, f2 := false
  action b1 when b = idle ∧ f2 = false do b := one, f2 := true
  action b2 when b = one ∧ f1 = false do b := both, f1 := true
  action brel when b = both do b := idle, f1 := false, f2 := false
)`);
    ex("deadlock(Forks)", r`Predict, then check: can ‹Forks› deadlock? Answer ‹true› or ‹false›.`, [r`Let each worker take its first fork.`, r`The usual cure is to take forks in one global order: with both taking fork 1 first, whoever holds it can always get fork 2.`], { hide: true });
    ex("eventually(Peterson, p = crit)", r`With every step weakly fair, does ‹p› always get into ‹Peterson›'s critical section eventually?`, [r`The algorithm is symmetric.`]);
    md(r`
> [!summary]
> Safety fails on a finite trace; liveness only on a complete run, one that stops (a deadlock) or one that loops (a lasso). Whether "eventually" holds depends on what the scheduler promises: weak fairness protects an action that stays enabled, strong fairness one that is enabled again and again.
`);
    md(r`Invariants, deadlocks, "eventually": three commands for three kinds of claim. The next lesson gives them one language, and one way to compute them all.`);
  });

  add("06-temporal-logic.chalk", "Temporal logic as fixed points", "Words for always and eventually, on some path and on every path; each one computed by repeating a step until nothing changes: least and greatest fixed points.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Temporal logic as fixed points");
    md(r`
> [!goal]
> Say "always", "eventually", "on some path" and "on every path" in one language, and compute each one by working backwards until nothing changes.
`);
    md(r`Two letters say where we look and two say when: **E**, on some path, and **A**, on every path; **F**, eventually (at some future state), and **G**, always (at every one); **X** is the next state. So $\mathsf{EF}\,\varphi$: some path reaches $\varphi$; $\mathsf{AG}\,\varphi$: $\varphi$ holds at every state of every path, an invariant; $\mathsf{AF}\,\varphi$: every path reaches $\varphi$; $\mathsf{EG}\,\varphi$: some path keeps $\varphi$ for ever. This is **CTL**.`);
    md(r`A system with two counters: ‹inc› counts ‹x› up to 3, and ‹move› moves one unit from ‹x› to ‹y›.`);
    m(COUNTER);
    md(r`
> [!try]
> How would you compute the set of states from which $y = 3$ can be reached? Start with the states where it holds.
`);
    md(r`Those states are in. So is every state with a step into them, and every state with a step into *those*, and so on, until a round adds nothing. Step through the rounds:`);
    m("ctl(C, EF y = 3)", { step: 0 });
    md(r`Each round applies one map to the set found so far: $Z \mapsto \varphi \cup \mathsf{EX}\,Z$, the goal together with the states that have a step into $Z$. The round that changes nothing has found a **fixed point**: $Z = \varphi \cup \mathsf{EX}\,Z$.`);
    sec("Why the least fixed point");
    md(r`That equation has more than one solution. Take three states: ‹a› steps to itself and to ‹b›, ‹b› steps back to ‹a›, and ‹c› has no steps in or out. Ask for $\mathsf{EF}\,c$: the map is $Z \mapsto \{c\} \cup \mathsf{EX}\,Z$, here on all eight sets of states.`);
    m("let P3 = subsets({a, b, c})");
    m("let f = map(P3; {}->{c}, {a}->{a,b,c}, {b}->{a,c}, {c}->{c}, {a,b}->{a,b,c}, {a,c}->{a,b,c}, {b,c}->{a,c}, {a,b,c}->{a,b,c})");
    m("fixpoints(P3, f)");
    md(r`$\{a, b, c\}$ is a fixed point too, and it claims that ‹a› can reach ‹c›, which is false. ‹a› and ‹b› hold each other up: each "can reach ‹c›" because the other can. The least solution holds only what is built up from the goal, one real step at a time, and Kleene iteration from $\varnothing$ finds it.`);
    m("lfp(P3, f)", { step: 0 });
    m("gfp(P3, f)");
    md(r`"Always" goes the other way. Start from the states where $\varphi$ holds, and remove those with a step out of the set, until nothing changes: the **greatest** fixed point of $Z \mapsto \varphi \cap \mathsf{AX}\,Z$. Staying for ever is assumed until a step refutes it. In ‹C›, $x + y \le 3$ holds in 10 states, and the set shrinks round by round to nothing:`);
    m("ctl(C, AG x + y ≤ 3)", { work: true });
    md(r`
> [!theorem] As fixed points
> On the lattice of sets of states, ordered by inclusion: $\mathsf{EF}\,\varphi$ is the least $Z$ with $Z = \varphi \cup \mathsf{EX}\,Z$, and $\mathsf{AG}\,\varphi$ the greatest $Z$ with $Z = \varphi \cap \mathsf{AX}\,Z$; likewise $\mathsf{AF}$ is a least fixed point and $\mathsf{EG}$ a greatest. The maps are monotone, so by Knaster–Tarski the fixed points exist, and on a finite lattice Kleene iteration reaches them: from $\varnothing$ for the least, from all states for the greatest.
`);
    m("ctl(C, AF y = 3)");
    md(r`This is *Order and lattices*' fixed-point lesson applied: the lattice is the powerset of the states, and the monotone map is a predicate transformer. Model checking a finite system is computing these fixed points.`);
    sec("In Lean");
    lean(r`/-- EX P: some step leads to a state where P holds. -/
def EX {σ : Type} (T : TS σ) (P : σ → Prop) (s : σ) : Prop := ∃ t, T.step s t ∧ P t

/-- The k-th approximation of EF P from below: P within k steps. -/
def EFk {σ : Type} (T : TS σ) (P : σ → Prop) : Nat → σ → Prop
  | 0 => fun s => P s
  | k + 1 => fun s => P s ∨ EX T (EFk T P k) s`);
    lx(`theorem EX_mono {σ : Type} (T : TS σ) (P Q : σ → Prop) (h : ∀ s, P s → Q s) :
    ∀ s, EX T P s → EX T Q s := by`, r`Prove that ‹EX› is monotone: the property the fixed-point argument needs.`, `  intro s ⟨t, hst, hp⟩
  exact ⟨t, hst, h t hp⟩`, [r`Take the witness step apart with ‹intro s ⟨t, hst, hp⟩›, and put it back with ‹h›.`]);
    lean(r`/-- The approximations only grow: the Kleene chain is increasing. -/
theorem EFk_mono {σ : Type} (T : TS σ) (P : σ → Prop) : ∀ k s, EFk T P k s → EFk T P (k + 1) s := by
  intro k
  induction k with
  | zero => intro s h; exact Or.inl h
  | succ k ih =>
    intro s h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (EX_mono T _ _ ih s h)`);
    sec("Exercises");
    ex("ctl(C, EF x = 3 ∧ y = 3)", r`Does $\mathsf{EF}(x = 3 \land y = 3)$ hold initially in ‹C›?`, []);
    ex("ctl(C, EG y < 3)", r`Does $\mathsf{EG}\,(y < 3)$ hold: is there a path that keeps $y < 3$ for ever?`, [r`"For ever" needs an infinite path. Does ‹C› have a cycle, and where does every path end?`]);
    ex("ctl(C, AF x = 3)", r`Does $\mathsf{AF}\,(x = 3)$ hold: does every path reach $x = 3$?`, [r`Can a path keep $x < 3$ all the way to its end?`]);
    md(r`
> [!summary]
> Temporal operators are fixed points of maps on sets of states: "eventually" a least one, built up from the goal, "always" a greatest one, whittled down from everything. Model checking a finite system is computing them by Kleene iteration.
`);
    md(r`All of this assumed one global state, and one step at a time. Machines that talk over a network share neither a state nor a clock. Which of their events came first? That is the next lesson.`);
  });

  add("07-happens-before.chalk", "Happens-before", "Without a shared clock, ask which event could have caused which: a partial order, a single counter that cannot capture it, and vector clocks that can.", ({ sec, md, m, ex, lean, lx, sc }) => {
    sec("Happens-before");
    md(r`
> [!goal]
> Order the events of machines that only talk by messages by what could have influenced what, and compute that order with vector clocks.
`);
    md(r`Machine ‹a› logs a debit at 10:00:02 by its clock; machine ‹b› logs a credit at 10:00:01 by its own. Which came first? Clocks drift, so the timestamps do not say. The question that matters is a different one: could the debit have caused the credit?`);
    sc(r`
clock t from 0 to 1
view 0, 5, -0.6, 1.6
noaxes
LA = segment(0.6 + i, 4.6 + i) faint
LB = segment(0.6, 4.6) faint
NA = label(0.3 + i, "a")
NB = label(0.3, "b")
A1 = point(1 + i) color 1
A2 = point(2.2 + i) color 1
A3 = point(4 + i) color 1
B1 = point(1.6) color 2
B2 = point(3.2) color 2
LA1 = label(A1, "a_1")
LA2 = label(A2, "a_2")
LA3 = label(A3, "a_3")
LB1 = label(B1, "b_1")
LB2 = label(B2, "b_2")
M1 = arrow(1 + i, 3.2) color 3
M2 = arrow(1.6, 4 + i) color 3
S = point(1 + i + t*(2.2 - i)) thick color 3
> show LA, LB, NA, NB | Two machines, $a$ and $b$; time runs to the right.
> show A1, A2, A3, LA1, LA2, LA3, B1, B2, LB1, LB2 | Their events, each machine's in its own order.
> show M1, M2 | Two messages: $a_1$ sends one that $b_2$ receives, and $b_1$ one that $a_3$ receives.
> show S; play t to 1 in 2s | Information moves only forward along a machine's line, or along a message. What $a_1$ knew can reach $b_2$: $a_1$ could have caused $b_2$.
> wait 1s | $a_2$ happens earlier than $b_2$, but no path leads from $a_2$ to $b_2$: nothing $a_2$ did can have reached $b_2$, and nothing of $b_2$ can have reached $a_2$.
`);
    md(r`
> [!definition] Happens-before (Lamport)
> Event $e$ **happens before** $f$ when $e$ comes earlier on the same machine, or $e$ sends a message that $f$ receives, or a chain of these leads from $e$ to $f$. Events neither of which happens before the other are **concurrent**. Happens-before is a partial order.
`);
    m("let E = events({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)");
    m("le(E, a1, b2)", { work: true });
    m("concurrent(E, a2, b2)");
    md(r`
> [!mistake]
> Messages cannot travel back in time: a pattern where an event would happen before itself is not a computation.
`);
    m("events({a1, a2}, {b1, b2}; a2->b1, b2->a1)");
    sec("Computing it locally");
    md(r`No machine sees the whole diagram. Can each event carry a tag, computed from what its machine has seen, such that comparing two tags says whether one event happens before the other?`);
    md(r`The first idea is one number per event, Lamport's clock: count up by one at each event, and on receiving a message, first catch up with the number it carries. If $e$ happens before $f$, $e$'s number is smaller. Here $a_1, a_2, a_3$ get $1, 2, 3$ and $b_1, b_2$ get $1, 2$. But the converse fails: $b_1$'s 1 is below $a_2$'s 2, and yet`);
    m("le(E, b1, a2)");
    md(r`One number cannot record *whose* events it has heard of. So keep a number per machine: for each machine, how many of its events this event has heard of.`);
    md(r`
> [!definition] Vector clock
> Each event gets a vector with an entry per machine: how many of that machine's events happen before it or are it. For two different events, $e$ happens before $f$ exactly when $e$'s vector is $\le$ $f$'s in every entry.
`);
    m("clocks({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)");
    md(r`$a_2 = (2, 0)$ and $b_2 = (1, 2)$: neither is below the other, so they are concurrent. A machine computes its clocks with no global clock: count its own entry up at each event, attach the vector to every message, and on receipt take the entrywise maximum with the message's.`);
    sec("In Lean");
    lean(r`/-- A vector clock, one entry per process. -/
abbrev VC := List Nat

def VC.le (a b : VC) : Prop := a.length = b.length ∧ ∀ i (h₁ : i < a.length) (h₂ : i < b.length), a[i] ≤ b[i]

def VC.merge (a b : VC) : VC := List.zipWith max a b

#eval VC.merge [2, 0, 1] [1, 3, 1]`);
    lx(`theorem VC.le_merge_left (a b : VC) (h : a.length = b.length) : VC.le a (VC.merge a b) := by`, r`Prove that merging clocks on receipt never goes back: the receiver's old clock is below the merge.`, `  refine ⟨by simp [VC.merge, h], ?_⟩
  intro i h₁ h₂
  simp [VC.merge]
  omega`, [r`Two parts: the lengths agree, and each entry is below.`, r`‹simp [VC.merge]› turns an entry of the merge into a ‹max›; ‹omega› finishes.`]);
    sec("Exercises");
    ex("concurrent(E, a1, b1)", r`Are ‹a1› and ‹b1› concurrent?`, []);
    ex("le(E, b1, a3)", r`Does ‹b1› happen before ‹a3›?`, []);
    ex("le(E, a2, b2)", r`$a_2$'s vector is $(2, 0)$ and $b_2$'s is $(1, 2)$. Does ‹a2› happen before ‹b2›?`, [r`Compare the vectors entry by entry.`]);
    md(r`
> [!summary]
> Without a shared clock, "earlier" is the wrong question; "could have influenced" is the right one, and it is a partial order. A single counter respects it but cannot detect concurrency; a vector of counters, one per machine, computes it exactly and locally.
`);
    md(r`Messages carry the influence. Networks lose messages, so senders send again, and then a message can arrive twice. What does that do to the receiver? That is the next lesson.`);
  });

  add("08-effectively-once.chalk", "Effectively-once delivery", "A client that retries because it cannot tell a lost request from a lost reply; the duplicate that follows; and the idempotent handler that makes the effect happen once.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Effectively-once delivery");
    md(r`
> [!goal]
> See why retrying a request applies it twice, and make the effect happen once anyway.
`);
    md(r`A client asks a server to add 5 to a balance, and hears nothing back. Either the request was lost, and the server did nothing, or the reply was lost, and the server has already added 5. The client cannot tell which. Sending again is the only way to be sure the request gets through.`);
    md(r`A model: the client tries at most twice; the network may lose the request or the reply; the server adds one to ‹applied› for each request it receives.`);
    m(client("Retry", false));
    md(r`
> [!try]
> Can the request be applied twice? Does a message have to be lost for that?
`);
    m("invariant(Retry, applied ≤ 1)", { step: 0 });
    md(r`No message was lost. The server applied the request, and while the reply was still on its way the client stopped waiting and sent again; the server applied that too. A lost reply does the same, one step later. Retries turn "at most once" into **at least once**: the client can make sure a request is applied, but not that it is applied only once. **Exactly-once delivery** is not something a network can promise.`);
    sec("Making a duplicate harmless");
    md(r`What can be promised is an effect that happens once. Make applying a request twice the same as applying it once: the handler is **idempotent**. Here the server remembers that it has applied the request (in practice, its id), and answers a repeat without applying it:`);
    m(client("Dedup", true));
    m("invariant(Dedup, applied ≤ 1)");
    md(r`The same invariant, now true. **Effectively once** is at-least-once delivery plus an idempotent handler. Idempotence is a property of the handler, not of the network, so it can be proved once, about the handler alone.`);
    md(r`With a cap of two tries, both can be lost, and the client gives up:`);
    m("reach(Dedup, tries = 2 ∧ req = false ∧ reply = none ∧ applied = 0)", { step: 0 });
    md(r`Without the cap the client retries for ever, and whether it eventually gets a reply is a liveness question. It holds when the network promises that a message sent again and again is eventually delivered: strong fairness, from lesson 5, on the steps that deliver.`);
    m(`let Forever = system(
  var req in bool
  var applied in 0..2
  var seen in bool
  var reply in {none, flying, got}
  init req = false ∧ applied = 0 ∧ seen = false ∧ reply = none
  action send when req = false ∧ reply ≠ got do req := true
  action lose when req = true do req := false
  strong fair action deliver when req = true ∧ seen = false do req := false, applied := applied + 1, seen := true, reply := flying
  strong fair action again when req = true ∧ seen = true do req := false, reply := flying
  action loseReply when reply = flying do reply := none
  strong fair action gotReply when reply = flying do reply := got
)`);
    m("eventually(Forever, reply = got)");
    sec("In Lean");
    lean(r`/-- A handler that adds to a balance: a duplicate is applied twice. -/
def credit (balance : Nat) (amount : Nat) : Nat := balance + amount

example : credit (credit 0 5) 5 ≠ credit 0 5 := by decide

/-- A handler that records a message id in a set. -/
def record (seen : List Nat) (m : Nat) : List Nat := if m ∈ seen then seen else m :: seen`);
    lx(`theorem record_idempotent (seen : List Nat) (m : Nat) : record (record seen m) m = record seen m := by`, r`Prove that recording a message twice is recording it once.`, `  unfold record
  by_cases h : m ∈ seen <;> simp [h]`, [r`Unfold ‹record› and split on whether ‹m› was already seen.`]);
    sec("Exercises");
    md(r`Some requests are idempotent without any memory. "Set ‹x› to 1" in place of "add 1 to ‹x›":`);
    m(`let Put = system(
  var tries in 0..2
  var req in bool
  var x in 0..2
  var reply in {none, flying, got}
  init tries = 0 ∧ req = false ∧ x = 0 ∧ reply = none
  action send when tries < 2 ∧ req = false ∧ reply ≠ got do tries := tries + 1, req := true
  action lose when req = true do req := false
  action deliver when req = true do req := false, x := 1, reply := flying
  action loseReply when reply = flying do reply := none
  action gotReply when reply = flying do reply := got
)`);
    ex("invariant(Put, x ≤ 1)", r`Retries and all, does $x \le 1$ hold in every reachable state of ‹Put›? Answer ‹true› or ‹false›.`, [r`Applying ‹x := 1› twice leaves ‹x = 1›.`], { hide: true });
    ex("invariant(Retry, applied ≤ 1)", r`Does the counting handler, ‹Retry›, apply the request at most once?`, []);
    md(r`
> [!summary]
> A client that hears nothing cannot tell a lost request from a lost reply, so it retries, and retries duplicate. Effectively-once processing is at-least-once delivery plus an idempotent handler, and idempotence is a one-line theorem about the handler, not a property of the network.
`);
    md(r`‹Dedup› keeps "applied at most once" through every loss and retry. Is that all it does, or does it behave, step by step, like a server that applies each request exactly when asked? The next lesson makes "behaves like" precise.`);
  });

  add("09-refinement.chalk", "Refinement", "An implementation's steps are the specification's steps or invisible ones: checking that one system implements another, and an operation-rewriting optimization proved sound.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Refinement");
    md(r`
> [!goal]
> Check that a detailed system does only what an abstract one allows, by mapping its states and matching its steps.
`);
    md(r`A specification of lesson 8's server says only this: the request goes from not applied to applied, once. (‹applied› has room for a 2 that the specification never reaches, so that an implementation that goes there can be compared with it.)`);
    m("let Once = system(var applied in 0..2; init applied = 0; action apply when applied = 0 do applied := 1)");
    m(client("Dedup", true));
    md(r`
> [!try]
> ‹Dedup› has six actions and ‹Once› one. In what sense could ‹Dedup› behave like ‹Once›?
`);
    md(r`Look at ‹Dedup› only through ‹applied›. ‹deliver› takes it from 0 to 1, a step of ‹Once›. Every other action (sending, losing, replying) leaves it alone: through this window, nothing happens. Such a step is a **stutter**, and allowing it is what lets an implementation have moving parts the specification never mentions.`);
    m("refines(Dedup, Once; applied := applied)");
    m(client("Retry", false));
    m("refines(Retry, Once; applied := applied)", { step: 0 });
    md(r`‹Retry›'s second delivery takes ‹applied› from 1 to 2: through the window, it does something ‹Once› never does.`);
    md(r`
> [!definition] Refinement
> A concrete system $C$ **refines** an abstract system $A$ under a mapping from $C$'s states to $A$'s when every initial state maps to an initial state, and every step of $C$ maps to a step of $A$ or to no change at all (a stutter). Then every behaviour of $C$, seen through the mapping, is a behaviour of $A$, so every safety property proved of $A$ holds of $C$ seen the same way.
`);
    md(r`The mapping can combine variables. Two counters, seen through their sum:`);
    m(TWO);
    m(SUM);
    m("refines(Two, Sum; s := a + b)", { work: true });
    md(r`An implementation that bumps both at once takes a step the specification does not have:`);
    m("let Jump = system(var a in 0..2; var b in 0..2; init a = 0 ∧ b = 0; action both when a < 2 ∧ b < 2 do a := a + 1, b := b + 1)");
    m("refines(Jump, Sum; s := a + b)", { step: 0 });
    sec("Normalizing operations, soundly");
    md(r`A client queues operations on a key (create, update, delete) and sends them in a batch. An optimizer folds adjacent operations into one: $\mathsf{update}\,a;\ \mathsf{update}\,b$ becomes $\mathsf{update}\,b$. The batch must still do the same to the store: the same idea as refinement, for a rewriting. Every fold must leave the store's final state the same, from every starting state.`);
    lean(r`/-- An operation on one key of a store: create (overwriting), update (only if present), delete. -/
inductive Op where
  | create (v : Nat)
  | update (v : Nat)
  | delete
  deriving DecidableEq, Repr

def Op.apply : Option Nat → Op → Option Nat
  | _, .create v => some v
  | some _, .update v => some v
  | none, .update _ => none
  | _, .delete => none

def run (s : Option Nat) (ops : List Op) : Option Nat := ops.foldl Op.apply s

/-- Two operations as one, when one does the work of both. -/
def combine : Op → Op → Option Op
  | .create _, .update b => some (.create b)
  | .update _, .update b => some (.update b)
  | _, .create b => some (.create b)
  | _, .delete => some .delete
  | _, _ => none`);
    lx(`theorem combine_sound (a b c : Op) (h : combine a b = some c) (s : Option Nat) :
    Op.apply (Op.apply s a) b = Op.apply s c := by`, r`Prove each combination sound: applying the two is applying the one, from any state.`, `  cases a <;> cases b <;> simp [combine] at h <;> subst h <;> cases s <;> rfl`, [r`Case on both operations; the impossible combinations fall away with ‹simp [combine] at h›.`, r`What is left: substitute ‹c› and try both starting states.`]);
    md(r`One fold at a time is sound; so is folding a whole batch, by induction on it:`);
    lean(r`/-- Normalize a batch: fold each operation into the next one where they combine. -/
def normalize : List Op → List Op
  | [] => []
  | a :: rest =>
    match normalize rest with
    | b :: tl => match combine a b with
      | some c => c :: tl
      | none => a :: b :: tl
    | [] => [a]

theorem normalize_sound : ∀ (ops : List Op) (s : Option Nat), run s (normalize ops) = run s ops := by
  intro ops
  induction ops with
  | nil => intro s; rfl
  | cons a rest ih =>
    intro s
    simp only [normalize, run, List.foldl_cons]
    split
    · rename_i b tl heq
      split
      · rename_i c hc
        have := ih (Op.apply s a)
        rw [heq] at this
        simp only [run, List.foldl_cons] at this ⊢
        rw [← this, ← combine_sound a b c hc s]
      · have := ih (Op.apply s a)
        rw [heq] at this
        simp only [run, List.foldl_cons] at this ⊢
        exact this
    · rename_i heq
      have := ih (Op.apply s a)
      rw [heq] at this
      simp only [run, List.foldl_cons, List.foldl_nil] at this ⊢
      exact this

#eval normalize [.create 1, .update 2, .update 3, .delete, .create 4]`);
    md(r`
> [!mistake]
> "Create then delete cancels out" looks like a fine fold, and it is wrong: if the key already existed, the pair deletes it, and the empty batch would not. Lean finds the starting state:
`);
    lean(r`example : run (some 7) [.create 1, .delete] ≠ run (some 7) [] := by decide`);
    sec("Exercises");
    ex("refines(Two, Sum; s := a)", r`Look at ‹Two› through ‹a› alone: ‹s := a›. Does it still refine ‹Sum›?`, [r`What does ‹tb› look like through ‹a›?`]);
    ex("refines(Jump, Sum; s := a + b)", r`Does ‹Jump› refine ‹Sum› under the sum mapping?`, []);
    md(r`
> [!summary]
> Refinement checks that an implementation only does what the specification allows, with its internal steps as stutters. A rewriting of operations is sound in the same sense: same effect from every state, which a structural induction proves once for every batch.
`);
    md(r`‹normalize› folds a batch in one fixed order, from the right. An optimizer that may fold anywhere, in any order: does it always stop, and does the order change the answer? That is the next lesson.`);
  });

  add("10-rewriting.chalk", "Rewriting systems", "Lesson 9's folds as rules on terms: rewriting to a normal form, termination by a measure, and confluence by critical pairs.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Rewriting systems");
    md(r`
> [!goal]
> Write an optimization as rewrite rules, show that rewriting always stops, and check that the order the rules fire in cannot change the answer.
`);
    md(r`Lesson 9's ‹normalize› folded a batch from the right. Written as rules instead, a fold may fire anywhere in the batch, in any order. That is more freedom, and two questions: does it always stop, and does every order give the same batch?`);
    md(r`
> [!definition] Term, rule, normal form
> A **term** is a variable or a symbol applied to terms: ‹then(create(1), done)›. A **rule** $l \to r$ rewrites any instance of $l$, anywhere in a term, to the same instance of $r$. A **normal form** is a term no rule applies to.
`);
    md(r`A batch is a term: ‹then(op, rest)› puts an operation before the rest, and ‹done› is the empty batch. The combinations are four rules. The variables are ‹u›, ‹v›, ‹w›, ‹x›, ‹y› and ‹z›; anything else is a symbol or a constant.`);
    m("let N = rules(\n  cu: then(create(x), then(update(y), z)) -> then(create(y), z)\n  uu: then(update(x), then(update(y), z)) -> then(update(y), z)\n  xc: then(u, then(create(y), z)) -> then(create(y), z)\n  xd: then(u, then(delete, z)) -> then(delete, z)\n)");
    m("rewrite(N, then(create(1), then(update(2), then(update(3), then(delete, then(create(4), done))))))", { step: 0 });
    md(r`Each step names its rule and marks where it applied: the leftmost-outermost redex, the first instance of a left side from the root. The answer is the batch ‹normalize› gave in lesson 9, ‹[create 4]›.`);
    sec("Termination");
    md(r`
> [!try]
> Why must rewriting with ‹N› stop, whatever the term and whatever order the rules fire in?
`);
    md(r`Every rule drops an operation, so the size (the number of symbols) goes down at each step, and a natural number cannot go down for ever: lesson 5's measure.`);
    m("terminates(N)", { work: true });
    md(r`Size is not always the right measure. Addition on numerals ‹0›, ‹s(0)›, ‹s(s(0))›, …:`);
    m("let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))");
    m("terminates(A)", { work: true });
    md(r`The second rule keeps the size: it only moves an ‹s› outward. What does go down is how much work is left inside ‹add›. Weigh ‹add›'s first argument double, an **interpretation** of the symbols as functions on numbers, and every step lowers it:`);
    m("terminates(A; add(x, y) = 2x + y, s(x) = x + 1)", { work: true });
    md(r`
> [!theorem] The check is sound
> With coefficients of at least one, a rule whose left side has a larger constant and no smaller coefficient is worth more for every value of the variables, and so is every term around an instance of it. Every step lowers a natural number, so no term rewrites for ever. The engine's ‹RewritingProofs› proves this, and the converse for a single rule: one that fails is worth no more on the right for some values.
`);
    sec("Confluence and critical pairs");
    md(r`
> [!definition] Confluent
> A system is **confluent** when any two ways of rewriting a term can be brought back together. A terminating, confluent system gives every term exactly one normal form: the optimizer's answer does not depend on which rule it tries first.
`);
    md(r`Two rules can only disagree where their left sides overlap. Each overlap gives a **critical pair**: the two results. If every pair rewrites to a common term (it is **joinable**), the system is locally confluent, and with termination, confluent (Newman's lemma). So finitely many overlaps decide a question about every term.`);
    m("critical(N)", { work: true });
    md(r`
> [!mistake]
> Add lesson 9's tempting fold, "create then delete cancels out":
`);
    m("let M = rules(\n  cu: then(create(x), then(update(y), z)) -> then(create(y), z)\n  uu: then(update(x), then(update(y), z)) -> then(update(y), z)\n  xc: then(u, then(create(y), z)) -> then(create(y), z)\n  xd: then(u, then(delete, z)) -> then(delete, z)\n  cd: then(create(x), then(delete, z)) -> z\n)");
    m("critical(M)", { work: true });
    md(r`The pair $(\mathsf{then}(\mathsf{delete}, z),\ z)$ does not join: the same batch normalizes to "delete" or to nothing depending on which rule fires first. Lesson 9's Lean found the store state where the two differ (the key already existed). Here the rules themselves show that something is wrong, before any semantics.`);
    sec("Normalization never lengthens a batch");
    md(r`Back in Lean, with lesson 9's ‹normalize›: it never makes a batch longer. (Its termination Lean checks by itself: the recursion is structural.)`);
    lx(`theorem normalize_length : ∀ ops : List Op, (normalize ops).length ≤ ops.length := by`, r`Prove it by induction on the batch.`, `  intro ops
  induction ops with
  | nil => simp [normalize]
  | cons a rest ih =>
    simp only [normalize]
    split
    · rename_i b tl heq
      rw [heq] at ih
      split <;> simp at ih ⊢ <;> omega
    · simp`, [r`‹induction ops›, then ‹simp only [normalize]› and ‹split› on what ‹normalize rest› gave.`, r`In the case ‹b :: tl›, rewrite ‹ih› with the equation ‹split› names, then ‹split› again on ‹combine a b›; ‹omega› finishes the arithmetic.`]);
    sec("Exercises");
    ex("rewrite(N, then(update(1), then(update(2), then(update(3), done))))", r`Normalize ‹then(update(1), then(update(2), then(update(3), done)))› with ‹N›. Write the term.`, [r`‹uu› keeps the second update.`]);
    ex("rewrite(N, then(create(1), then(delete, then(update(2), done))))", r`And ‹then(create(1), then(delete, then(update(2), done)))›?`, [r`No rule folds an update into a delete before it: an update on a missing key does nothing, but the rules keep it.`]);
    ex("terminates(A; add(x, y) = x + y + 1, s(x) = x + 1)", r`Would a plainer weight do: does ‹A› pass with ‹add(x, y) = x + y + 1› and ‹s(x) = x + 1›? Answer ‹true› or ‹false›.`, [r`Work out both sides of the second rule: ‹add(s(x), y)› and ‹s(add(x, y))›.`], { hide: true });
    ex("rewrite(A, add(s(s(0)), s(s(0))))", r`What is ‹add(s(s(0)), s(s(0)))›, rewritten with ‹A›?`, []);
    md(r`
> [!summary]
> Rewrite rules are an optimization written as equations directed left to right. A measure every rule lowers shows termination; joinable critical pairs show local confluence; together they give each term one normal form. A pair that does not join points at a rule to fix, or one to add (Knuth–Bendix completion).
`);
    md(r`A measure says a loop of rewriting stops. Lesson 8's retry loop stops for a blunter reason: a cap on the tries. What does the cap cost, in failures and in load? The last lesson counts.`);
  });

  add("11-retries.chalk", "Retries and backoff", "Retrying a call that fails at random: the chance that every attempt fails, the expected number of attempts, and the load and wait that backoff trades.", ({ sec, md, m, ex }) => {
    sec("Retries and backoff");
    md(r`
> [!goal]
> Work out how often a capped retry loop gives up, how many calls it makes on average, and how long backoff makes it wait.
`);
    md(r`Lesson 8's client tried twice and could still give up. More tries make giving up rarer, and cost calls. How much rarer, and how many calls?`);
    md(r`Say each attempt fails with probability $q$, independently of the others, and the client tries at most $n$ times. Take $q = 1/10$:`);
    m("let q = 1/10");
    md(r`
> [!try]
> What is the chance that three attempts all fail? That five do not all fail?
`);
    md(r`Independent failures multiply: all $n$ fail with probability $q^n$.`);
    m("q^3");
    m("1 - q^5");
    md(r`The same number comes from the other side. The first success is at attempt $k$ with probability $q^{k-1}(1 - q)$: $k - 1$ failures, then a success. Adding these up for $k = 1, \dots, 5$ gives the chance of some success:`);
    m("sum((1 - q)*q^(k - 1), k, 1, 5)", { work: true });
    md(r`That they agree is the geometric sum. With a symbol for $q$, multiplying by $1 - r$ telescopes:`);
    m("expand((1 - r)*sum(r^k, k, 0, 4))", { work: true });
    sec("Expected attempts");
    md(r`
> [!definition] Expected value
> The **expected** number of attempts is the sum of each count times its probability: $k$ attempts when the first success is at $k < n$, and $n$ when the first $n - 1$ fail.
`);
    m("sum(k*(1 - q)*q^(k - 1), k, 1, 4) + 5*q^4", { work: true });
    md(r`
> [!try]
> There is a shorter way. When does the client make an attempt $k + 1$ at all?
`);
    md(r`Exactly when the first $k$ attempts failed, which has probability $q^k$. Each attempt counts one when it happens, so the expected count is the sum of those chances:`);
    m("sum(q^k, k, 0, 4)");
    md(r`
> [!mistake]
> Retries look free when failures are rare: $1.1111$ calls per request. But failures are rarely independent. When a server is overloaded most calls fail, and the retries are more load on the server that is already failing:
`);
    m("sum((9/10)^k, k, 0, 4)");
    md(r`At $q = 9/10$ every request costs about four calls ($4.0951$): retries multiply the load just when the server can take the least. Hence retry budgets, which cap retries at a fraction of the traffic, and backoff.`);
    md(r`The expected attempts as a function of the failure rate:`);
    m("manipulate(sum(p^k, k, 0, 4), p, 0, 1)");
    sec("Exponential backoff");
    md(r`
> [!definition] Exponential backoff
> Wait $d$ before the second attempt, $2d$ before the third, $4d$ before the fourth: the wait before attempt $k + 2$ is $2^k d$. Real clients also cap it and add **jitter**, a random part, so that clients that failed together do not retry together.
`);
    md(r`With $d = 100$ ms and five attempts, the longest the client waits in all:`);
    m("sum(100*2^k, k, 0, 3)");
    md(r`On average far less: the wait before attempt $k + 2$ only happens when the first $k + 1$ attempts failed.`);
    m("sum(100*2^k*q^(k + 1), k, 0, 3)", { work: true });
    md(r`
> [!note]
> Retries repeat requests. A request that the server applied but whose reply was lost is sent again: lesson 8's idempotent handler is what makes retrying safe.
`);
    sec("Exercises");
    ex("(1/5)^3", r`A call fails with probability $1/5$. What is the chance that three attempts all fail?`, [r`Independent attempts: multiply.`]);
    ex("1 - (1/2)^4", r`With $q = 1/2$ and four attempts, what is the chance that the call succeeds?`, [r`One minus the chance that all four fail.`]);
    ex("sum((1/2)^k, k, 0, 3)", r`With $q = 1/2$ and at most four attempts, how many attempts does a request cost on average?`, [r`Sum $q^k$ for $k$ from $0$ to $n - 1$.`]);
    ex("sum(50*2^k, k, 0, 4)", r`Backoff starts at $50$ ms and doubles, with six attempts. How long does the client wait in all, at most?`, [r`Five waits: $50, 100, 200, 400, 800$.`]);
    md(r`
> [!summary]
> Independent attempts multiply: all $n$ fail with probability $q^n$, and the expected attempts are $\sum_{k<n} q^k$. Under overload $q$ is near one and retries multiply the load; backoff spaces them out, and costs little on average when failures are rare. Retrying is only safe with an idempotent handler.
`);
  });
}, { leanPrelude: true });

// ---------------------------------------------------------------------------------------------------
course("calculus", "Calculus: derivatives and integrals",
  "The slope at a point, found by zooming in; the power, product and chain rules read off pictures; the circle behind cos, sin and e^(it), and the hyperbola behind cosh and sinh; tangent lines and bending; then antiderivatives the engine checks by differentiating, and area as slope run backwards.",
  "Calculus I–II", (add) => {

  add("01-rules.chalk", "The rules of differentiation", "The slope at a point, as what secants settle on; the power rule from a growing square, the product rule from a growing rectangle.", ({ sec, md, m, ex, sc }) => {
    sec("The rules of differentiation");
    md(r`
> [!goal]
> Say what the slope of a curve at one point means, and see where the power and product rules come from, well enough to rebuild them.
`);
    md(r`A slope is rise over run, between two points. On a straight line any two points give the same answer; on the graph of $y = x^2$ they do not, since it curves. Yet a speedometer shows one speed at one instant, and a curve looks steeper at some points than at others. What can "the slope at a point" mean, when a slope needs two points?`);
    sec("Zoom in");
    md(r`Magnify the graph of $y = x^2$ around the point $(1, 1)$, held in the middle of the picture. The axes and the graph paper are magnified with it:`);
    sc(r`
clock s from 0 to ln(40)
let z = exp(s)
view -1, 1, -2.2, 2.2
noaxes
U = grid([z, 0; 0, z]) faint color 2
F = grid([z/10, 0; 0, z/10]) faint color 2
H = grid([z/100, 0; 0, z/100]) faint color 2
X = line(-z*i, 1 - z*i) color 6
Y = line(-z, -z + i) color 6
G = graph(z*((1 + x/z)^2 - 1), x, -5, 5) thick color 1
T = graph(2*x, x, -5, 5) dashed color 6
P = point(0) color 1
> show U, F, X, Y, G, P | The curve $y = x^2$ and its axes, on graph paper ruled in units and tenths. The point $(1, 1)$ is in the middle.
> play s to ln(10) in 4s | Zoom in $10$ times, paper and all. The axes run off, the tenths spread out to where the units were, and the bend straightens out.
> show H; play s to ln(40) in 3s | On to $40$ times, with hundredths now in sight. The curve is all but straight.
> show T | What is left looks like a line, of slope $2$: the slope of $x^2$ at $1$.
`);
    md(r`Close up, a smooth curve looks straight, and a straight line has a slope. That slope is the slope at the point. To compute it without a microscope, take two points of the graph and let them close in.`);
    sec("From secant to tangent");
    md(r`The line through two points of the graph, $(x, f(x))$ and $(x + h, f(x + h))$, is a **secant**, and its slope is $\dfrac{f(x + h) - f(x)}{h}$. Take $f(x) = x^2$ at $x = 1$, and leave $h$ a letter: ‹m› is the secant's slope in terms of $h$, ‹L› the secant, and ‹T› the line the zoom showed, through $(1, 1)$ with slope $2$ (‹diff›, below, computes it).`);
    m("let f = x^2");
    m("let m = (subst(f, x, 1 + h) - subst(f, x, 1)) / h");
    m("let L = subst(f, x, 1) + m*(x - 1)");
    m("let T = subst(f, x, 1) + subst(diff(f, x), x, 1)*(x - 1)");
    md(r`‹manipulate(e, h, from, to)› shows ‹e› with a slider for $h$ and a ‹▶ Play› button, like Mathematica's ‹Manipulate›, and ‹column(…)› puts several things under the one slider, like its ‹Column›: here the picture, then the calculation of ‹m›, ‹L› and ‹T› at the same $h$. $h$ runs from $2$ down to $0.05$.`);
    m("manipulate(column(plot([f, L, T], x, -0.5, 3), m, L, T), h, 2, 0.05)");
    md(r`
> [!try]
> Before you press ‹▶ Play›: what number will ‹m› close in on? Then play it. As $h$ shrinks toward $0$ the second point slides down the curve toward $(1, 1)$, and the secant ‹L› turns onto the tangent ‹T›. Under the picture, ‹m› is worked out at each $h$: $\dfrac{(1 + h)^2 - 1}{h}$ with $h$ put in, closing in on $2$, the slope the zoom showed.
`);
    md(r`The slope is never computed *at* $h = 0$, where the fraction is $\frac00$: it is the number the secant slopes settle on. That number gets a name.`);
    md(r`
> [!definition] Derivative
> The derivative of $f$ at $x$ is $f'(x) = \lim_{h \to 0} \dfrac{f(x + h) - f(x)}{h}$: the number the secant slopes settle on, the slope of the line the graph looks like when you zoom in.
`);
    md(r`‹diff(f, x)› is the derivative of $f$ with respect to $x$. The engine takes no limits: it applies rules, one at a time, and each rule is a step you can read, with a dot that says whether the rule is proved in Lean. The rest of this lesson finds where two of those rules come from.`);
    sec("Why the derivative of x² is 2x");
    md(r`Do the limit once, at any $x$. The secant slope of $x^2$ between $x$ and $x + h$, multiplied out:`);
    m("expand(((x + h)^2 - x^2)/h)", { work: true });
    md(r`It is $2x + h$. (Cancelling $h$ assumes $h \neq 0$, and the step says so: at $h = 0$ the fraction means nothing.) As $h$ shrinks, $2x + h$ settles on $2x$. A picture says why. Read $x^2$ as the area of a square of side $x$, and lengthen the side by a little, $dx$:`);
    sc(r`
clock d from 0 to 0.5
noaxes
view -0.3, 2.3, -0.3, 2.3
S = poly(0, 1.5, 1.5 + 1.5*i, 1.5*i) color 2
LX = label(0.75 - 0.15*i, "x") color 2
R = poly(1.5, 1.5 + d, 1.5 + d + 1.5*i, 1.5 + 1.5*i) color 1
T = poly(1.5*i, 1.5 + 1.5*i, 1.5 + (1.5 + d)*i, (1.5 + d)*i) color 1
C = poly(1.5 + 1.5*i, 1.5 + d + 1.5*i, 1.5 + d + (1.5 + d)*i, 1.5 + (1.5 + d)*i) color 3
LR = label(1.5 + d + 0.75*i, "x\,dx") color 1
LT = label(0.75 + (1.5 + d)*i, "x\,dx") color 1
LC = label(1.5 + d + (1.5 + d)*i, "dx^2") color 3
> show S, LX | A square of side $x$: its area is $x^2$.
> show R, T, C, LR, LT, LC; play d to 0.5 in 2s | Lengthen the side by $dx$. The new area is two strips, $x\,dx$ each, and a corner, $dx^2$.
> play d to 0.04 in 4s | Make $dx$ small. The strips thin in proportion to $dx$; the corner, $dx$ times $dx$, vanishes much faster.
`);
    md(r`The area grows by $2x\,dx + dx^2$. Divided by $dx$, that is $2x + dx$: the secant slope above, with $h$ called $dx$. As $dx$ shrinks the corner stops counting, and what is left is the two strips: $d(x^2) = 2x\,dx$. The $2$ in $2x$ is there because the square grows on two sides.`);
    md(r`
> [!try]
> Now a cube of side $x$, volume $x^3$. Lengthen every edge by $dx$, keeping one corner fixed. Some of the new volume is thin slabs of area $x^2$ and thickness $dx$: how many? The rest (rods along the edges, a small cube at the far corner) is a multiple of $dx^2$ or $dx^3$, and vanishes faster. Predict the derivative of $x^3$, then answer the exercise.
`);
    ex("diff(x^3, x)", r`Invent it: from the cube, what is the derivative of $x^3$?`, [
      r`The slabs are on the three faces that do not touch the fixed corner.`,
      r`Three slabs of $x^2\,dx$: divide the new volume by $dx$ and let $dx$ shrink.`,
    ]);
    md(r`Multiplied out, the cube's growth is exactly those pieces: three slabs, three rods and a small cube.`);
    m("expand((x + h)^3 - x^3)");
    md(r`The same count works in any number of dimensions, and so does the algebra: $(x + h)^n = x^n + n x^{n-1} h + (\text{terms with } h^2)$.`);
    sec("Powers, sums and constants");
    md(r`
> [!theorem] Power, sum and constant-multiple rules
> $\dfrac{d}{dx} x^n = n x^{n-1}$ for a whole number $n$ (and, for $x > 0$, for any real $n$); $\quad (f + g)' = f' + g'$: nudge a sum and each part adds its own change; $\quad (c f)' = c f'$: stretch a graph upward and every slope stretches with it; and a constant has derivative $0$.
`);
    m("diff(x^5, x)", { work: true });
    md(r`A polynomial takes all four. Step through it: before each ‹▸ Next step›, say which rule comes next.`);
    m("diff(3x^4 - 2x + 7, x)", { step: 0 });
    ex("diff(x^4 - 5x^2 + 2, x)", r`Differentiate $x^4 - 5x^2 + 2$.`, [
      r`Differentiate term by term: the sum rule.`,
      r`Each term: $\frac{d}{dx}\, a x^n = a n x^{n-1}$, and the constant $2$ has derivative $0$.`,
    ]);
    sec("Products");
    md(r`Now a product $f g$. The natural guess is the product of the derivatives, $f' g'$. Test it where the answer is known: $x^2 \cdot x^3 = x^5$, whose derivative is $5x^4$. The guess gives:`);
    m("diff(x^2, x) * diff(x^3, x)");
    md(r`
> [!mistake]
> $6x^3$ is not $5x^4$; it is not even the right power. The derivative of a product is **not** the product of the derivatives.
`);
    md(r`Go back to areas. Read $f g$ as a rectangle with sides $f$ and $g$, and nudge $x$: $f$ grows by $df$, $g$ by $dg$.`);
    sc(r`
clock d from 0 to 0.5
noaxes
view -0.4, 3, -0.4, 2.1
B = poly(0, 2, 2 + 1.2*i, 1.2*i) color 2
LF = label(1 - 0.2*i, "f") color 2
LG = label(-0.2 + 0.6*i, "g") color 2
R = poly(2, 2 + d, 2 + d + 1.2*i, 2 + 1.2*i) color 1
LR = label(2 + d + 0.6*i, "g\,df") color 1
T = poly(1.2*i, 2 + 1.2*i, 2 + (1.2 + 0.6*d)*i, (1.2 + 0.6*d)*i) color 4
LT = label(1 + (1.2 + 0.6*d)*i, "f\,dg") color 4
C = poly(2 + 1.2*i, 2 + d + 1.2*i, 2 + d + (1.2 + 0.6*d)*i, 2 + (1.2 + 0.6*d)*i) color 3
LC = label(2 + d + (1.2 + 0.6*d)*i, "df\,dg") color 3
> show B, LF, LG | A rectangle with sides $f$ and $g$: its area is the product $fg$.
> show R, LR, T, LT, C, LC; play d to 0.5 in 2s | Nudge $x$: $f$ grows by $df$ and $g$ by $dg$. The new area is a strip $g\,df$, a strip $f\,dg$ and a corner $df\,dg$.
> play d to 0.05 in 4s | Make the nudge small. The strips shrink in proportion to it; the corner, a product of two small changes, vanishes faster.
`);
    md(r`
> [!theorem] Product rule
> $d(fg) = g\,df + f\,dg + df\,dg$, and the corner vanishes faster than the nudge: $(fg)' = f'g + fg'$. The guess $f'g'$ is what survives in the corner alone, $df\,dg = f'g'\,dx^2$: the one piece that does not count.
`);
    md(r`On $x^2 \cdot x^3$: $2x \cdot x^3 + x^2 \cdot 3x^2 = 5x^4$, as it should be. Step through a product whose factors do not merge:`);
    m("diff(x^2 * sin(x), x)", { step: 0 });
    ex("diff(x^3 * cos(x), x)", r`Differentiate $x^3 \cos x$.`, [
      r`It is a product: $f = x^3$ and $g = \cos x$.`,
      r`$f' = 3x^2$ and $g' = -\sin x$; now $f'g + fg'$.`,
    ]);
    ex("diff(exp(x) * cos(x), x)", r`Differentiate $e^x \cos x$. (Type $e^x$ as ‹exp(x)›.)`, [
      r`$(e^x)' = e^x$: the exponential is its own derivative.`,
      r`Any correct form is accepted: $e^x \cos x - e^x \sin x$ and $e^x(\cos x - \sin x)$ reduce to the same normal form.`,
    ]);
    md(r`
> [!summary]
> Zoom in on a smooth curve and it looks like a line: the derivative is that line's slope, the number the secant slopes settle on. The power rule is the strips of a growing square (the slabs of a growing cube), the product rule the strips of a growing rectangle; in both the corner vanishes. These rules reach $x^2$ and $\sin x$, but not $\sin(x^2)$, a function inside another: that is the next lesson.
`);
  });

  add("02-chain-rule.chalk", "The chain rule", "Functions of functions: follow a nudge through the inner function and then the outer one, and see why the inner derivative comes out in front.", ({ sec, md, m, ex, sc }) => {
    sec("The chain rule");
    md(r`
> [!goal]
> Differentiate a function of a function, such as $\sin(x^2)$, and see why the derivative of the inside comes out in front.
`);
    md(r`The rules so far handle $x^2$ and $\sin x$, but not $\sin(x^2)$: the sine of something that is itself changing. The natural guess is to differentiate the outside and leave the inside alone, giving $\cos(x^2)$. Plot the true derivative against the guess:`);
    m("plot([diff(sin(x^2), x), cos(x^2)], x, 0, 3)");
    md(r`
> [!mistake]
> The guess $\cos(x^2)$ is wrong: the true derivative is $2x\cos(x^2)$, the guess times $2x$, so they agree only at $x = \frac12$ and where both are $0$. $2x$ is the derivative of the inside. Why should it multiply?
`);
    sec("Follow a nudge");
    md(r`Follow a small nudge through each function in turn, on three number lines: $x$ on top, $x^2$ in the middle, $\sin x^2$ at the bottom.`);
    sc(r`
clock a from 1 to 1.5
noaxes
view -1.4, 3.3, -0.5, 2.5
X = segment(-1.2 + 2*i, 3.2 + 2*i) faint color 6
G = segment(-1.2 + i, 3.2 + i) faint color 6
F = segment(-1.2, 3.2) faint color 6
LX = label(-1.3 + 2*i, "x") color 6
LG = label(-1.3 + i, "x^2") color 6
LF = label(-1.3 + 0*i, "\sin x^2") color 6
DX = arrow(a + 2*i, a + 0.2 + 2*i) thick color 1
DG = arrow(a^2 + i, (a + 0.2)^2 + i) thick color 2
DF = arrow(sin(a^2), sin((a + 0.2)^2)) thick color 3
M1 = segment(a + 2*i, a^2 + i) dashed color 6
M2 = segment(a^2 + i, sin(a^2)) dashed color 6
> show DX | A nudge to $x$.
> show M1, DG | Squaring turns it into a nudge to $x^2$, about $2x$ times as long: the inner derivative.
> show M2, DF | The sine scales that nudge by $\cos(x^2)$: the outer derivative, taken where the inside is.
> play a to 1.5 in 6s | Move $x$ from $1$ to $1.5$. The middle nudge grows, about $2x$ times the top one; the bottom one is the middle one times $\cos(x^2)$, which falls to $0$ at $x^2 = \pi/2$ and then turns the nudge round.
`);
    md(r`A nudge $dx$ moves $x^2$ by about $2x\,dx$. That nudge, $dg = 2x\,dx$, moves $\sin g$ by about $\cos(g)\,dg$, with $g = x^2$. Altogether $d(\sin x^2) \approx \cos(x^2) \cdot 2x \cdot dx$. The guess forgot that the inside moves at its own rate, $2x$ times as fast as $x$.`);
    md(r`
> [!theorem] Chain rule
> $\dfrac{d}{dx} f(g(x)) = f'(g(x))\, g'(x)$, where $g$ is differentiable at $x$ and $f$ at $g(x)$: the outer derivative, taken at the inner function, times the inner derivative. In nudges: $dg = g'(x)\,dx$ and $df = f'(g)\,dg$.
`);
    m("diff(sin(x^2), x)", { step: 0 });
    md(r`
> [!try]
> Predict the derivative of $e^{3x}$ before you open the work: what is the inside, and how fast does it move?
`);
    m("diff(exp(3x), x)", { work: true });
    sec("The inner derivative comes out in front");
    md(r`
> [!try]
> Drag ‹a›. In $\sin(ax)$ the inside runs $a$ times as fast as $x$, so the wave goes by $a$ times as fast: the derivative $a\cos(ax)$ has the inner derivative $a$ in front, its curve is $a$ times taller, and the slopes are $a$ times steeper.
`);
    m("let a = 2", { slider: [1, 6, 1] });
    m("diff(sin(a*x), x)");
    m("plot([sin(a*x), diff(sin(a*x), x)], x, 0, 6.28)");
    sec("Chains inside chains");
    md(r`A power of a sum is a chain too: the outer function is $u^5$, the inner $2x + 1$.`);
    m("diff((2x + 1)^5, x)", { step: 0 });
    md(r`Three layers make three factors, one per layer, each taken at what is inside it:`);
    m("diff(exp(sin(x^2)), x)", { work: true });
    ex("diff(cos(x^3), x)", r`Differentiate $\cos(x^3)$.`, [
      r`The outer function is $\cos u$, the inner $u = x^3$.`,
      r`$(\cos u)' = -\sin u$ and $(x^3)' = 3x^2$.`,
    ]);
    ex("diff(exp(x^2), x)", r`Differentiate $e^{x^2}$. (Type it as ‹exp(x^2)›.)`, [
      r`The outer function is $e^u$, whose derivative is itself.`,
    ]);
    ex("diff((x^2 + 1)^3, x)", r`Differentiate $(x^2 + 1)^3$.`, [
      r`The outer function is $u^3$, the inner $u = x^2 + 1$.`,
      r`Factored or multiplied out, either form is right: the check compares normal forms.`,
    ]);
    ex("diff(ln(x), x)", r`Invent it: for $x > 0$, $e^{\ln x} = x$. Differentiate both sides, using the chain rule on the left (the inside is $\ln x$), and solve for the derivative of $\ln x$.`, [
      r`The left side's derivative is $e^{\ln x} \cdot (\ln x)'$, which is $x \cdot (\ln x)'$.`,
      r`The right side's derivative is $1$.`,
    ]);
    md(r`
> [!summary]
> Follow a nudge: the inside stretches it by $g'(x)$, then the outside by $f'(g)$. The derivative of the inside comes out in front because the inside moves at its own rate. One chain is worth a lesson of its own: $e^{it}$, where the inside is multiplied by $i$. What does a point do whose velocity is its position times $i$?
`);
  });
  add("03-circles.chalk", "Circles, exponentials and rotation", "Why e^(it) walks round the unit circle: cosine and sine as shadows, multiplying by i as a quarter turn, Euler's formula, angles that add, and arctan as an angle.", ({ sec, md, m, ex, sc }) => {
    sec("Circles, exponentials and rotation");
    md(r`
> [!goal]
> See why $e^{it}$ walks round the unit circle, and read the derivatives of $\cos$ and $\sin$, Euler's formula and the angle-sum formulas off that one picture.
`);
    md(r`This lesson works in the complex plane: the number $a + bi$ is the point $(a, b)$, and ‹i› is typed as it is. A cell that mentions ‹i› is read over $\mathbb{C}$, and its steps are judged by the rules' proofs there.`);
    sec("A point going round the circle");
    md(r`
> [!definition] Cosine and sine
> Walk a distance $t$ round the unit circle, counterclockwise from $1$. Where you stand is $\cos t + i \sin t$: the **cosine** is your shadow on the horizontal axis, the **sine** your shadow on the vertical one.
`);
    sc(r`
clock t from 0 to 2pi
C = curve(exp(i*s), s, 0, 2pi) faint color 6
P = point(exp(i*t)) thick color 1
W = trace(P) color 1
R = arrow(0, P) color 1
L = label(P, "\cos t + i \sin t") color 1
X = point(cos(t)) color 2
DX = segment(P, X) dashed color 2
Y = point(i*sin(t)) color 3
DY = segment(P, Y) dashed color 3
> show C | The unit circle: every point at distance $1$ from $0$.
> show P, R, L, W; play t to 0.7 in 2s | Walk a distance $t$ round it, counterclockwise from $1$. Where you stand is $\cos t + i \sin t$.
> show X, DX, Y, DY | The **cosine** is your shadow on the horizontal axis (blue), the **sine** your shadow on the vertical one (green).
> play t to pi/2 in 2s | A quarter of the way round, at $t = \pi/2$, the sine is at its peak and the cosine is $0$.
> play t to 2pi in 5s | Once round: each shadow swings between $-1$ and $1$, the sine a quarter turn behind the cosine.
`);
    md(r`Unrolled against the distance walked, the two shadows are the familiar waves:`);
    sc(r`
clock t from 0.01 to 2pi
view 0, 6.3, -1.25, 1.25
Cw = graph(cos(x), x, 0, t) color 2
Sw = graph(sin(x), x, 0, t) color 3
Q = point(t + i*cos(t)) color 2
P = point(t + i*sin(t)) color 3
> show Cw, Q, Sw, P; play t to 2pi in 6s | The cosine starts at $1$, the sine at $0$; each is the other shifted by a quarter turn, $\pi/2$.
`);
    md(r`
> [!try]
> The same walk as a calculation you can stop anywhere: drag ‹T›, and the arc, the radius and the drop to the axis are worked out at that $T$.
`);
    m("manipulate(plot([cos(2*pi*t/T) + i*sin(2*pi*t/T), cos(t) + i*sin(t), (t/T)*(cos(T) + i*sin(T)), cos(T) + i*(t/T)*sin(T)], t, 0, T), T, 0.05, 6.28)");
    sec("Multiplying by i is a quarter turn");
    md(r`$i \cdot (a + bi) = -b + ai$: the point $(a, b)$ goes to $(-b, a)$, the same distance from $0$ and a quarter turn further round.`);
    m("i*(3 + 4i)", { work: true });
    m("plot([t*(3 + 4i), t*i*(3 + 4i)], t, 0, 1)");
    m("abs(3 + 4i) - abs(i*(3 + 4i))");
    sec("A rate that turns");
    md(r`$e^x$ is the function whose rate of change is itself. Ask the same of a point moving in the plane, but with a quarter turn: a point $z(t)$ whose velocity is always $i\,z(t)$. The velocity is the position turned a quarter, so it is always at right angles to the radius: the point never moves toward $0$ or away from it, only round it. Starting from $1$, at speed $1$, it walks the unit circle. That point is $e^{it}$:`);
    sc(r`
clock t from 0 to 2pi
C = curve(exp(i*s), s, 0, 2pi) faint color 6
P = point(exp(i*t)) thick color 1
R = arrow(0, P) color 1
LP = label(P, "e^{it}") color 1
V = arrow(P, (1 + i)*exp(i*t)) color 4
LV = label((1 + i)*exp(i*t), "i\,e^{it}") color 4
E = eq(diff(exp(i*t), t))
> show C, P, R, LP | The point $e^{it}$, and its radius.
> show E; work E | Its velocity, by the chain rule: $i\,e^{it}$.
> show V, LV | Multiplying by $i$ turns a quarter, so the velocity is the radius turned a quarter: always at right angles to it.
> play t to 2pi in 6s | Never along the radius, always across it: the point neither nears $0$ nor leaves it. It goes round.
`);
    m("diff(exp(i*t), t)", { work: true });
    md(r`
> [!theorem] Euler's formula
> $e^{it} = \cos t + i \sin t$: the exponential with a turning rate is the walk round the circle. ‹exptotrig› applies it.
`);
    m("exptotrig(exp(i*pi/3))", { work: true });
    m("exp(i*pi) + 1", { work: true });
    md(r`Write both sides of $\frac{d}{dt} e^{it} = i\,e^{it}$ with Euler's formula. The left is $\cos' t + i \sin' t$; the right is the position turned a quarter. Their real and imaginary parts are the derivatives of cosine and sine, read off the picture:`);
    m("expand(exptotrig(diff(exp(i*t), t)))");
    sec("Compound growth, turned");
    md(r`$e = \lim_{n \to \infty} (1 + 1/n)^n$: grow by a fraction $1/n$, $n$ times over.`);
    m("let n = 4", { slider: [1, 64, 1] });
    m("N((1 + 1/n)^n)");
    md(r`
> [!try]
> Now grow by $i\pi/n$ instead, $n$ times: each step multiplies by $1 + i\pi/n$, a small turn and a slight stretch. The path below runs from $1$ through the powers $(1 + i\pi/n)^k$. Drag ‹n› up: the stretch fades, the path settles onto the circle, and it ends at $e^{i\pi} = -1$.
`);
    sc(r`
clock n from 1 to 40
C = curve(exp(i*s), s, 0, pi) faint color 6
M = point(-1) color 4
LM = label(M, "-1") color 4
S = curve((1 + i*pi/n)^(n*s/pi), s, 0, pi) color 1
E = point((1 + i*pi/n)^n) thick color 1
> show C, M, LM | Half way round the circle: the walk $e^{i\pi}$ takes, from $1$ to $-1$.
> show S, E | One step of $1 + i\pi$ overshoots: a turn, but a stretch too.
> play n to 40 in 7s | Split it into $n$ steps of $1 + i\pi/n$. As $n$ grows the stretch fades, the path settles onto the circle, and it ends at $e^{i\pi} = -1$.
`);
    md(r`The same path with a slider of your own, through the powers $(1 + i\pi/n)^k$:`);
    m("plot([cos(t) + i*sin(t), (1 + i*pi/n)^(n*t/pi)], t, 0, pi)");
    m("N((1 + i*pi/n)^n)");
    sec("Angles add when you multiply");
    sc(r`
clock b from 0.01 to 2
C = curve(exp(i*s), s, 0, 2pi) faint color 6
AA = curve(0.3*exp(i*s), s, 0, 0.6) color 2
A = arrow(0, exp(0.6*i)) color 2
LA = label(exp(0.6*i), "e^{ia}") color 2
BB = curve(0.45*exp(i*s), s, 0, b) color 3
B = arrow(0, exp(i*b)) color 3
LB = label(exp(i*b), "e^{ib}") color 3
PP = curve(0.6*exp(i*s), s, 0, 0.6 + b) color 1
P = arrow(0, exp(i*(0.6 + b))) thick color 1
LP = label(exp(i*(0.6 + b)), "e^{ia} e^{ib}") color 1
> show C, AA, A, LA | A turn by $a$: the point $e^{ia}$.
> show BB, B, LB | A turn by $b$.
> show PP, P, LP | Their product is the turn by $a$ followed by the turn by $b$: angle $a + b$.
> play b to 2 in 5s | As $b$ grows the product turns with it, always $a$ ahead. Multiplying points on the circle adds their angles.
`);
    md(r`$e^{ia}\,e^{ib} = e^{i(a + b)}$: turning by $a$ and then by $b$ is turning by $a + b$. Expand both sides with Euler's formula and compare real parts and imaginary parts.`);
    m("expand(exptotrig(exp(i*a))*exptotrig(exp(i*b)))");
    m("expand(exptotrig(exp(i*(a + b))))");
    md(r`
> [!theorem] Angle sums
> $\cos(a + b) = \cos a \cos b - \sin a \sin b$ and $\sin(a + b) = \sin a \cos b + \cos a \sin b$: the real and imaginary parts of one product of turns.
`);
    sec("The angle of a point");
    md(r`‹abs(z)› is the distance from $0$ and ‹arg(z)› the angle from the positive real axis, so $z = |z|\,e^{i \arg z}$. For a point $1 + iy$, to the right of $0$, the angle is $\arctan y$.`);
    m("let z = 1 + i");
    m("abs(z)");
    m("N(arg(z))");
    m("N(arctan(1))");
    md(r`So ‹arctan› measures an angle, and its derivative $\dfrac{1}{1 + y^2}$ is how fast the angle grows as the point climbs the vertical line through $1$. Adding those small turns from $y = 0$ to $y = 1$ gives the angle to $1 + i$, an eighth of a turn, $\pi/4$; four of them make $\pi$.`);
    sc(r`
clock y from 0.01 to 1
view -0.3, 1.5, -0.25, 1.15
C = curve(exp(i*s), s, 0, pi/2) faint color 6
K = segment(1, 1 + i) faint color 6
AR = curve(0.35*exp(i*s), s, 0, arctan(y)) thick color 2
LA = label(0.36*exp(i*arctan(y)/2), "\arctan y") color 2
R = arrow(0, P) color 1
P = point(1 + i*y) thick color 1
LP = label(P, "1 + iy") color 1
> show C, K, R, P, LP | A point climbing the vertical line through $1$: the point $1 + iy$.
> show AR, LA | Its angle from the real axis is $\arctan y$.
> play y to 1 in 6s | The angle grows fast at first and slower as the point climbs, at the rate $\frac{1}{1 + y^2}$. At $y = 1$ it is an eighth of a turn, $\pi/4$.
`);
    m("integrate(1/(1 + y^2), y)", { work: true });
    m("N(4*integrate(1/(1 + y^2), y, 0, 1))");
    sec("Circles riding on circles");
    md(r`A sum of terms $c_k e^{ikt}$ is circles riding on circles, each turning $k$ times per lap, with radius $|c_k|$. ‹epicycles› draws them; enough of them trace any closed curve you can draw, as closely as you like, which is what the *Llamas* notebook does.`);
    m("epicycles(exp(i*t) + exp(3*i*t)/3, t)");
    ex("i*(1 + 2i)", r`Turn $1 + 2i$ a quarter turn counterclockwise about $0$.`, [
      r`Multiply by $i$, and use $i^2 = -1$.`,
    ], { hide: true });
    ex("exptotrig(exp(i*pi/2))", r`Where is $e^{i\pi/2}$? Give it as a complex number.`, [
      r`A walk of $\pi/2$ round the unit circle is a quarter turn from $1$.`,
    ], { hide: true });
    ex("diff(exp(3*i*t), t)", r`Differentiate $e^{3it}$ with respect to $t$.`, [
      r`The chain rule: the inner derivative is $3i$.`,
    ]);
    ex("expand((cos(t) + i*sin(t))^2)", r`Square $\cos t + i \sin t$ and multiply it out, in terms of $\cos t$ and $\sin t$. (Its real part is $\cos 2t$: why?)`, [
      r`$(a + bi)^2 = a^2 - b^2 + 2abi$.`,
      r`Squaring $e^{it}$ doubles the angle, so the square is $e^{2it} = \cos 2t + i \sin 2t$.`,
    ]);
    md(r`
> [!summary]
> Multiplying by $i$ turns a quarter, so a rate of $i$ times the position goes round a circle: $e^{it} = \cos t + i\sin t$. The derivatives of $\cos$ and $\sin$, the angle-sum formulas and $\arctan$ as an angle all come from that walk. Now flip one sign: $x^2 - y^2 = 1$ is a hyperbola. What walks it the way $(\cos t, \sin t)$ walks the circle, and what does $t$ measure there, where it cannot be an angle?
`);
  });

  // the sectors of the circle and the hyperbola, as polygons through points of the arc
  const arc = (pt, n = 12) => Array.from({ length: n + 1 }, (_, k) => pt(`${k}*t/${n}`)).join(", ");
  add("04-hyperbolic.chalk", "Hyperbolic functions: the other circle", "cosh and sinh found by factoring the hyperbola as the circle factors over ℂ: the even and odd parts of e^x, the area that t measures on both curves, and derivatives with no minus sign.", ({ sec, md, m, ex, sc }) => {
    sec("Hyperbolic functions: the other circle");
    md(r`
> [!goal]
> Find the functions that walk the hyperbola $x^2 - y^2 = 1$ as $\cos$ and $\sin$ walk the circle, and read their derivatives off that picture.
`);
    md(r`The circle $x^2 + y^2 = 1$ is walked by $(\cos t, \sin t)$. Flip one sign and $x^2 - y^2 = 1$ is a hyperbola. What walks that?`);
    sec("Factor the hyperbola");
    md(r`Look again at how the circle was walked. Over $\mathbb{C}$ its equation factors, $x^2 + y^2 = (x + iy)(x - iy)$, and the point $x + iy = e^{it}$ makes the other factor $x - iy = e^{-it}$, so the product is $1$. The hyperbola's equation factors with no $i$ at all: $x^2 - y^2 = (x + y)(x - y)$.`);
    md(r`
> [!try]
> Invent it: copy the circle's move without the $i$, and set $x + y = e^t$. What must $x - y$ be for the product to be $1$? Solve the two equations for $x$ and $y$ before reading on.
`);
    md(r`$x - y = e^{-t}$; adding and subtracting the two equations gives $x = \frac{e^t + e^{-t}}{2}$ and $y = \frac{e^t - e^{-t}}{2}$. Any positive number in place of $e^t$ would give a point of the right branch. $e^t$ is the circle's choice with the $i$ taken out, and the rest of the lesson shows what it buys: $t$ measures the same thing on both curves, and the derivatives come out as simply as $\cos' = -\sin$.`);
    md(r`
> [!definition] Hyperbolic cosine and sine
> $\cosh x = \dfrac{e^x + e^{-x}}{2}$, the average of $e^x$ and its mirror image $e^{-x}$; and $\sinh x = \dfrac{e^x - e^{-x}}{2}$, half their difference.
`);
    md(r`The engine reads ‹cosh›, ‹sinh› and ‹tanh› as these definitions in ‹exp›, so its answers come back in exponentials: everything about them is something about $e^x$.`);
    sec("Even and odd parts of e^x");
    sc(r`
clock t from -1.39 to 1.4
view -2, 2, -2.2, 4.6
Ep = graph(exp(x), x, -1.5, 1.5) faint color 1
Em = graph(exp(-x), x, -1.5, 1.5) faint color 2
A = point(t + i*exp(t)) color 1
B = point(t + i*exp(-t)) color 2
AB = segment(A, B) dashed color 6
Mc = point(t + i*cosh(t)) thick color 3
Cg = graph(cosh(x), x, -1.4, t) thick color 3
Cf = graph(cosh(x), x, -1.4, 1.4) thick color 3
D = segment(Mc, A) thick color 4
Ms = point(t + i*sinh(t)) thick color 4
Sf = graph(sinh(x), x, -1.4, 1.4) thick color 4
> show Ep, Em | $e^x$ (orange) grows to the right; its mirror image $e^{-x}$ (blue) grows to the left.
> show A, B, AB, Mc, Cg; play t to 1.4 in 5s | At every $x$, take the point halfway between them: their average, $\cosh x$ (green). It is symmetric, an **even** function, lowest at $\cosh 0 = 1$.
> hide Cg; show Cf, D | From the average up to $e^x$ is half their difference: $\sinh x$ (pink). So $e^x = \cosh x + \sinh x$.
> show Ms, Sf | Drawn on its own, $\sinh x$ is **odd**: through $0$, and turned half a turn about it.
> play t to -1.39 in 5s | Walk back. At every $x$, $e^x = \cosh x + \sinh x$ and $e^{-x} = \cosh x - \sinh x$: an even part and an odd part, the way every function splits.
`);
    m("cosh(x)");
    m("expand(cosh(x) + sinh(x))", { work: true });
    m("expand(cosh(x) - sinh(x))");
    m("cosh(-x) - cosh(x)");
    sec("The hyperbola");
    md(r`$(\cos t, \sin t)$ stays on the circle because $\cos^2 t + \sin^2 t = 1$. The hyperbolic pair was built to satisfy the same equation with one sign changed; multiplied out, the definitions confirm it:`);
    m("expand(cosh(x)^2 - sinh(x)^2)");
    md(r`
> [!theorem] The unit hyperbola
> $\cosh^2 t - \sinh^2 t = 1$: the point $(\cosh t, \sinh t)$ lies on the hyperbola $x^2 - y^2 = 1$, on its right branch, since $\cosh t > 0$.
`);
    sc(r`
clock t from 0 to 1.4
view -1.7, 2.7, -1.5, 2.45
C = curve(exp(i*s), s, 0, 2pi) faint color 6
H = curve(cosh(s) + i*sinh(s), s, -1.5, 1.5) color 3
Q = point(exp(i*t)) thick color 1
RQ = segment(0, Q) color 1
P = point(cosh(t) + i*sinh(t)) thick color 3
R = segment(0, P) color 3
X = point(cosh(t)) color 2
DX = segment(P, X) dashed color 2
Y = point(i*sinh(t)) color 4
DY = segment(P, Y) dashed color 4
V = value(cosh(t)^2 - sinh(t)^2, "\cosh^2 t - \sinh^2 t = ")
SC = poly(0, ${arc((u) => `exp(i*${u})`)}) color 1
SH = poly(0, ${arc((u) => `cosh(${u}) + i*sinh(${u})`)}) color 3
Ar = value(t/2, "\text{each shaded area} = ")
> show C, Q, RQ | The unit circle, $x^2 + y^2 = 1$, and $(\cos t, \sin t)$ on it.
> show H, P, R | The unit hyperbola, $x^2 - y^2 = 1$, and $(\cosh t, \sinh t)$ on it: the same recipe with one sign flipped.
> show X, DX, Y, DY, V; play t to 1.4 in 4s | The shadows of the green point are $\cosh t$ (blue) and $\sinh t$ (pink). The point runs out along the hyperbola, and $\cosh^2 t - \sinh^2 t$ never leaves $1$.
> hide X, DX, Y, DY, V; play t to 0 in 2s | So what is $t$? On the circle it is an angle. On the hyperbola it is not: the green segment's angle never reaches $45°$, however large $t$ grows.
> show SC, SH, Ar; play t to 1.4 in 5s | But on both, $t$ measures an **area**: the sector swept out from $1$ has area $\frac{t}{2}$, on the circle and on the hyperbola alike. The hyperbola's sector is long and thin; its area grows at exactly the circle's rate.
`);
    md(r`Why $\frac t2$? A point $(x(s), y(s))$ moving from $s = 0$ to $t$ sweeps a sector of area $\frac12 \int_0^t (x y' - y x')\,ds$. For the hyperbola the integrand is $\cosh^2 s - \sinh^2 s$:`);
    m("expand(cosh(s)*diff(sinh(s), s) - sinh(s)*diff(cosh(s), s))");
    m("integrate(1, s, 0, t)/2");
    md(r`For the circle it is $\cos^2 s + \sin^2 s$, which is $1$ too, the circle's own equation (the engine leaves it written that way):`);
    m("expand(cos(s)*diff(sin(s), s) - sin(s)*diff(cos(s), s))");
    sec("Derivatives with no minus sign");
    md(r`The circle's point $e^{it}$ has velocity $i e^{it}$: the radius turned a quarter, so $\cos' = -\sin$ and $\sin' = \cos$. Differentiate the hyperbola's point instead.`);
    md(r`
> [!try]
> Predict first: differentiate $\frac{e^x + e^{-x}}{2}$ term by term. Which function comes out, and with what sign? The cells check your answer by subtracting it.
`);
    m("diff(cosh(x), x) - sinh(x)", { work: true });
    m("diff(sinh(x), x) - cosh(x)");
    sc(r`
clock t from -1.2 to 0.6
view -1.4, 2.8, -1.8, 2.4
H = curve(cosh(s) + i*sinh(s), s, -1.7, 1.7) faint color 3
K = line(0, 1 + i) dashed color 6
P = point(cosh(t) + i*sinh(t)) thick color 3
R = arrow(0, P) color 3
M = arrow(0, sinh(t) + i*cosh(t)) dashed color 4
Vel = arrow(P, cosh(t) + sinh(t) + i*(sinh(t) + cosh(t))) thick color 4
> show H, P, R | The point $(\cosh t, \sinh t)$ and its position arrow.
> show Vel; play t to 0.6 in 4s | Its velocity (pink) is $(\sinh t, \cosh t)$. The circle's velocity is its radius turned a quarter; this one is at right angles to the radius only at the vertex, $t = 0$.
> show K, M | It is the position with $x$ and $y$ swapped: its mirror image in the line $y = x$ (dashed, from $0$). Reflecting has no minus sign, and neither do $\cosh' = \sinh$ and $\sinh' = \cosh$.
> play t to -0.9 in 4s | The velocity's tip runs along that line: it is at $(\cosh t + \sinh t)(1, 1) = e^t (1, 1)$.
`);
    sec("The circle, turned by i");
    md(r`
> [!intuition] cos is cosh at an imaginary argument
> Put $it$ into the definition: $\cosh(it) = \frac{e^{it} + e^{-it}}{2}$, and Euler's formula turns that into $\cos t$; likewise $\sinh(it) = i \sin t$. Put $x = \cos t$ and $y = i \sin t$ into the hyperbola's $x^2 - y^2 = 1$ and it becomes the circle's $\cos^2 t + \sin^2 t = 1$: the circle is the hyperbola with $y$ made imaginary.
`);
    m("exptotrig(cosh(i*t))", { work: true });
    m("expand(exptotrig(sinh(i*t)))");
    md(r`A chain hanging between two posts takes the shape of $\cosh$, stretched to $a \cosh(x/a)$ for some $a$: the **catenary**. Near the bottom $\cosh x$ is almost the parabola $1 + \frac{x^2}{2}$, and then it climbs away from it, exponentially:`);
    m("plot([cosh(x), 1 + x^2/2], x, -3, 3)");
    ex("diff(cosh(3x), x)", r`Differentiate $\cosh(3x)$.`, [r`$\cosh' = \sinh$, with no minus sign.`, r`The chain rule: times the inner derivative, $3$.`]);
    ex("sinh(x)", r`Invent it: $\sin$ is the function with $f'' = -f$, $f(0) = 0$ and $f'(0) = 1$. Which function has $f'' = f$, $f(0) = 0$ and $f'(0) = 1$?`, [
      r`Take the minus sign away: look among $\cosh$ and $\sinh$, whose derivatives have none.`,
      r`$\sinh 0 = 0$ and $\sinh' 0 = \cosh 0 = 1$.`,
    ], { hide: true });
    ex("cosh(0)", r`What is $\cosh 0$, the $x$-coordinate of the point $t = 0$ on the hyperbola?`, [r`$e^0 = 1$.`], { hide: true });
    ex("expand(cosh(2x) - (cosh(x)^2 + sinh(x)^2))", r`Check the double-angle formula $\cosh 2x = \cosh^2 x + \sinh^2 x$: what is the difference of the two sides?`, [r`Write everything in $e^{x}$ and expand.`], { hide: true });
    md(r`
> [!summary]
> Factor $x^2 - y^2$ as the circle's equation factors over $\mathbb{C}$, and $\cosh$ and $\sinh$ fall out: the even and odd parts of $e^x$. The point $(\cosh t, \sinh t)$ walks the hyperbola $x^2 - y^2 = 1$ as $(\cos t, \sin t)$ walks the circle, with $t$ twice the area swept on both; its velocity is its mirror image, so $\cosh' = \sinh$ and $\sinh' = \cosh$; and $\cosh(it) = \cos t$, $\sinh(it) = i \sin t$. Next, back on the real line: how well does a tangent line stand in for its curve, and what does the derivative of the derivative say about the curve's shape?
`);
  });

  add("05-tangent-lines.chalk", "Tangent lines and the second derivative", "The tangent line as the best straight stand-in for a curve, estimates from it, and the second derivative as how fast the curve bends away.", ({ sec, md, m, ex, sc }) => {
    sec("Tangent lines and the second derivative");
    md(r`
> [!goal]
> Use the tangent line as a stand-in for a curve near a point, see why it is the best straight line there, and read the curve's bending from the second derivative.
`);
    md(r`Back on the real line, with one curve and one point. Without a calculator: what is $\sqrt{4.1}$? You know $\sqrt 4 = 2$, and $4.1$ is close to $4$. Zoomed in near $4$, the graph of $\sqrt x$ looks like a line (lesson 1), so follow the line instead of the curve.`);
    md(r`
> [!try]
> The slope of $\sqrt x = x^{1/2}$ at $4$ is $\frac12 \cdot 4^{-1/2} = \frac14$. Moving $0.1$ to the right, a line of that slope rises $0.1 \cdot \frac14$. Estimate $\sqrt{4.1}$ before the next cells do.
`);
    m("subst(diff(sqrt(x), x), x, 4)", { work: true });
    m("2 + subst(diff(sqrt(x), x), x, 4)*(4.1 - 4)");
    m("N(sqrt(4.1))");
    md(r`The estimate $2.025$ is off by less than $0.0002$. The line it used, through the point with the curve's slope there, is the tangent line.`);
    md(r`
> [!definition] Tangent line
> The tangent line to $y = f(x)$ at $x = a$ is $y = f(a) + f'(a)\,(x - a)$: the line through $(a, f(a))$ with the curve's slope there.
`);
    sec("The tangent line");
    m("let f = x^3 - 3x");
    m("diff(f, x)");
    m("let a = 2", { slider: [-2, 2, 1] });
    m("let s = subst(diff(f, x), x, a)");
    m("let t = subst(f, x, a) + s*(x - a)");
    m("plot([f, t], x, -2.5, 2.5)");
    md(r`
> [!try]
> Drag ‹a›. At which points is the tangent flat? Predict first. There $f'(a) = 3a^2 - 3 = 0$, so $a = \pm 1$: the top of the hump and the bottom of the dip.
`);
    sec("Why this line and not another");
    md(r`Many lines pass through $(2, f(2)) = (2, 2)$. What makes the tangent, $y = 2 + 9(x - 2)$, the best? Measure the gap between curve and line a distance $h$ from the point:`);
    m("expand(subst(f - (2 + 9*(x - 2)), x, 2 + h))");
    md(r`The gap is $6h^2 + h^3$: no term in $h$ alone. Halve $h$ and the gap falls to about a quarter. Tilt the line, to slope $8$ say, and the gap gets an $h$ term:`);
    m("expand(subst(f - (2 + 8*(x - 2)), x, 2 + h))");
    md(r`For small $h$ the $h$ term is far larger than the others, so this gap shrinks only in proportion to $h$. Any slope but $9$ leaves an $h$ term, $(9 - \text{slope})\,h$; only the tangent's gap shrinks faster than $h$. That is the sense in which it is the best straight-line approximation near the point, and why the estimate of $\sqrt{4.1}$ was so close.`);
    sec("How the slope changes");
    md(r`The $6h^2$ is the curve bending away from its tangent. Bending is the slope changing, so watch the slope: roll the tangent along the curve.`);
    sc(r`
clock a from -1.7 to 1.7
view -2.4, 2.4, -3, 3
G = graph(x^3 - 3*x, x, -2.3, 2.3) color 2
P = point(a + i*(a^3 - 3*a)) thick color 1
T = segment(a + i*(a^3 - 3*a) - 0.7*(1 + i*(3*a^2 - 3)), a + i*(a^3 - 3*a) + 0.7*(1 + i*(3*a^2 - 3))) thick color 1
> show G, P, T | The curve $y = x^3 - 3x$ and its tangent line at a point.
> play a to 0 in 5s | Roll the point to the right. The tangent turns clockwise: its slope falls, from about $5.7$ to $-3$. The curve bends down, and the tangent lies above it.
> play a to 1.7 in 5s | At $x = 0$, where the bending switches, the tangent crosses the curve. Past it the tangent turns back the other way: the slope rises again. The curve bends up, and the tangent lies below it.
`);
    md(r`How fast the slope changes is the derivative of the derivative, the **second derivative** $f''$. ‹diff(f, x, 2)› differentiates twice. Before you open the work: the slope falls left of $0$ and rises right of it, so what sign should $f''$ have on each side?`);
    m("diff(f, x, 2)", { work: true });
    md(r`
> [!definition] Second derivative, bending
> $f''$ is the derivative of $f'$: the rate at which the slope changes. Where $f'' > 0$ the slope rises and the curve bends up, lying above its tangents; where $f'' < 0$ it bends down, below them.
`);
    md(r`Here $f''(x) = 6x$: the curve bends down for $x < 0$, around the hump, and up for $x > 0$, around the dip. And at $x = 2$, $f''(2) = 12$, half of which is the $6$ in the gap $6h^2$: the second derivative says how fast the curve leaves its tangent.`);
    ex("subst(diff(x^2, x), x, 3)", r`What is the slope of $y = x^2$ at $x = 3$?`, [
      r`The slope is the derivative, $2x$, at $x = 3$.`,
    ], { hide: true });
    ex("3 + subst(diff(sqrt(x), x), x, 9)*(9.6 - 9)", r`Estimate $\sqrt{9.6}$ with the tangent line of $\sqrt x$ at $x = 9$. Give it as a decimal.`, [
      r`$\sqrt 9 = 3$, and the slope there is $\frac{1}{2\sqrt 9} = \frac16$.`,
      r`Follow the tangent $0.6$ to the right: $3 + 0.6 \cdot \frac16$.`,
    ], { hide: true });
    ex("diff(x^4, x, 2)", r`Find the second derivative of $x^4$.`, [
      r`Differentiate twice: $x^4 \to 4x^3 \to \dots$`,
    ]);
    ex("subst(diff(f, x, 2), x, 1)", r`For the $f$ above, what is $f''(1)$?`, [
      r`$f''(x) = 6x$ (the cell above shows it).`,
    ], { hide: true });
    ex("diff(sin(x), x, 2)", r`Find the second derivative of $\sin x$. Predict first: on an arch where $\sin x > 0$, which way does the wave bend, so what sign has $f''$ there?`, [
      r`The arches above the axis bend down, so $f'' < 0$ where $\sin x > 0$.`,
      r`$(\sin x)' = \cos x$ and $(\cos x)' = -\sin x$.`,
    ]);
    md(r`
> [!summary]
> Near a point a smooth curve is nearly its tangent line, $y = f(a) + f'(a)(x - a)$: the only line whose gap shrinks faster than the distance. The second derivative is how fast the slope changes: the curve bends up where $f'' > 0$ and down where $f'' < 0$. So far: given a function, find its rate of change. Next, the other way round: given the rate, find the function.
`);
  });

  add("06-antiderivatives.chalk", "Antiderivatives, checked", "Differentiation run backwards: guess a function with the given derivative, then check it by differentiating, as the engine does; substitution and parts as the chain and product rules undone.", ({ sec, md, m, ex }) => {
    sec("Antiderivatives, checked");
    md(r`
> [!goal]
> Run differentiation backwards: given a rate, find a function that has it, and check the answer by differentiating it.
`);
    md(r`Which function has derivative $x^3$? There is no formula to apply yet, only the rules for going forwards. So guess, and check.`);
    md(r`
> [!try]
> The power rule lowers a power by one, so a guess is $x^4$. Differentiate it: how far off is it, and how do you fix it?
`);
    m("diff(x^4, x)");
    m("diff(x^4/4, x)");
    md(r`$x^4$ gives four times too much; $\frac{x^4}{4}$ is right. That is the whole method: guess, differentiate, fix the guess.`);
    md(r`
> [!definition] Antiderivative
> $F$ is an antiderivative of $f$ when $F' = f$. Adding a constant changes no slope, so $\frac{x^4}{4} + 1$ works too; on an interval any two antiderivatives differ by a constant, since a function with derivative $0$ there is constant. The engine gives one and leaves out the $+\,C$.
`);
    sec("Guess and check, by the engine");
    md(r`‹integrate(f, x)› works the same way. A few textbook rules make the guess; then, whatever made it, the engine differentiates the guess and answers only if the integrand comes back. Open the work: the guess, ‹Power rule for integrals›, then ‹Check by differentiating›.`);
    m("integrate(x^3, x)", { work: true });
    m("integrate(3x^2 + 2x + 1, x)");
    md(r`Most of the guessing rules (powers, sums, constant factors, the table of $\sin$, $\cos$, $e^x$) are proved in Lean as well. The two below, substitution and integration by parts, are not: their steps are marked **checked** (a hollow dot), and for them the check by differentiating is the proof.`);
    sec("Substitution: the chain rule backwards");
    md(r`Which function has derivative $2x\cos(x^2)$? You have seen this shape before: lesson 2 made it as the derivative of $\sin(x^2)$, the outer derivative $\cos(x^2)$ times the inner derivative $2x$.`);
    md(r`
> [!try]
> Predict the engine's answer, then open its work and find the inner function it chose.
`);
    m("integrate(2x*cos(x^2), x)", { work: true });
    md(r`
> [!theorem] Substitution
> $\int f(g(x))\, g'(x)\, dx = F(g(x))$ where $F' = f$: the chain rule, read backwards. The sign to look for is an inner function with its derivative standing beside it.
`);
    md(r`Without the inner derivative there is nothing to undo. $e^{x^2}$ has an antiderivative (the area under it, next lesson), but none that can be written with powers, $e^x$, $\ln$ and the trigonometric functions, so every guess fails, and the engine says so:`);
    m("integrate(exp(x^2), x)");
    sec("By parts: the product rule backwards");
    md(r`Which function has derivative $x e^x$? Guess $x e^x$ itself, and differentiate:`);
    m("diff(x*exp(x), x)");
    md(r`The product rule gives the wanted $x e^x$, plus an extra $e^x$. Take the extra away: subtract a function whose derivative is $e^x$, which is $e^x$ itself.`);
    m("diff(x*exp(x) - exp(x), x)");
    md(r`
> [!theorem] Integration by parts
> $\int u\, dv = uv - \int v\, du$: the product rule, read backwards. Above, $u = x$ and $dv = e^x\,dx$: $uv = x e^x$ was the first guess, and $\int v\,du = \int e^x\,dx$ the extra taken away.
`);
    m("integrate(x*exp(x), x)", { work: true });
    md(r`
> [!mistake]
> An antiderivative is not unique: $x^4$ and $x^4 + 1$ both have derivative $4x^3$. The exercises compare answers exactly, so give them **without** the $+\,C$.
`);
    ex("integrate(4x^3, x)", r`Find an antiderivative of $4x^3$.`, [r`Which power has derivative $4x^3$?`]);
    ex("integrate(cos(3x), x)", r`Find an antiderivative of $\cos 3x$: guess, differentiate, fix.`, [
      r`$\sin 3x$ is close: its derivative is $3\cos 3x$.`,
      r`Divide by the inner derivative $3$.`,
    ]);
    ex("integrate(2x*exp(x^2), x)", r`Find an antiderivative of $2x\,e^{x^2}$.`, [r`Substitute $u = x^2$: then $du = 2x\,dx$.`]);
    ex("integrate(x*cos(x), x)", r`Find an antiderivative of $x \cos x$.`, [
      r`Guess $x \sin x$ and differentiate it: what extra term appears?`,
      r`By parts, with $u = x$ and $dv = \cos x\,dx$: $uv - \int v\,du = x \sin x - \int \sin x\,dx$.`,
    ]);
    md(r`
> [!summary]
> Integration is guessing; differentiation is checking. Substitution undoes the chain rule and parts undoes the product rule, and some functions, like $e^{x^2}$, have no antiderivative built from the usual functions. Why run differentiation backwards at all? Because of area: the next lesson.
`);
  });

  add("07-definite-integrals.chalk", "Area and the fundamental theorem", "The area under a curve from rectangles, then exactly: the area so far grows at the rate of the curve's height, so it is an antiderivative.", ({ sec, md, m, ex, sc }) => {
    // the right Riemann rectangles of x^2 on [0, 1] with n strips, filled: a scene's script lines
    const rects = (n, tag, color) => {
      const lines = [], names = [];
      for (let k = 1; k <= n; k++) {
        const h = `${k * k}/${n * n}*i`;
        lines.push(`${tag}${k} = poly(${k - 1}/${n}, ${k}/${n}, ${k}/${n} + ${h}, ${k - 1}/${n} + ${h}) color ${color}`);
        names.push(`${tag}${k}`);
      }
      return { lines: lines.join("\n"), names: names.join(", ") };
    };
    // the region under x^2 from 0 to `to`, as a polygon through points of the curve
    // the j-th arch of the sine wave, from j*pi to (j + 1)*pi, as a polygon through points of the curve
    const arch = (j, n = 16) => Array.from({ length: n + 1 }, (_, k) => `pi*${j * n + k}/${n} + i*sin(pi*${j * n + k}/${n})`).join(", ");
    const under = (to, n = 16) => `poly(0, ${Array.from({ length: n }, (_, k) => `${k + 1}*${to}/${n} + i*(${k + 1}*${to}/${n})^2`).join(", ")}, ${to})`;
    const r5 = rects(5, "A", 1), r10 = rects(10, "B", 4), r20 = rects(20, "C", 5);
    sec("Area and the fundamental theorem");
    md(r`
> [!goal]
> Find the area under a curve: first approximately, with rectangles, then exactly, from an antiderivative, and see why an antiderivative gives it.
`);
    md(r`What is the area under $y = x^2$ from $0$ to $1$? Geometry has formulas for rectangles and triangles, not for a curved edge. It is less than $\frac12$, the triangle under the diagonal $y = x$, since the curve stays below the diagonal. Guess a number before reading on.`);
    sec("Rectangles");
    md(r`Rectangles we can add. Cut the region into strips, and replace each strip by a rectangle as tall as the curve at the strip's right edge:`);
    sc(`
clock t from 0 to 1
view -0.1, 1.15, -0.1, 1.1
F = graph(x^2, x, 0, 1) thick color 2
U = ${under(1)} color 2
${r5.lines}
${r10.lines}
${r20.lines}
> show F, U | The curve $y = x^2$ from $0$ to $1$, and the area under it: the number we want.
> show ${r5.names} | Five strips of width $\\frac15$; the $k$-th rectangle is $(k/5)^2$ tall. Each one pokes above the curve, so together they are too big.
> hide ${r5.names}; show ${r10.names} | Ten strips: the slivers above the curve are thinner, and the total is closer.
> hide ${r10.names}; show ${r20.names} | Twenty: the slivers thin again. Each doubling of the strips about halves what pokes out.
`);
    md(r`Five rectangles of width $\frac15$ and heights $\left(\frac15\right)^2, \left(\frac25\right)^2, \dots, \left(\frac55\right)^2$. ‹sum(f, k, a, b)› adds $f$ for $k = a, a + 1, \dots, b$:`);
    m("sum(k^2, k, 1, 5)", { work: true });
    m("sum((k/5)^2 / 5, k, 1, 5)");
    md(r`$\frac{11}{25} = 0.44$: too big, as the picture said. More strips poke out less.`);
    md(r`
> [!definition] Right Riemann sum, definite integral
> Cut $[0, 1]$ into $n$ strips of width $\frac1n$ and stand a rectangle of height $f(\frac kn)$ on the $k$-th: the area of the rectangles is $\displaystyle\sum_{k=1}^{n} f\!\left(\tfrac kn\right) \tfrac1n$. For a continuous $f$ these sums approach a single number as $n$ grows: the **definite integral** $\int_0^1 f(x)\,dx$, the area under the curve. On $[a, b]$ it is the same, with strips of width $\frac{b - a}{n}$.
`);
    m("let n = 10", { slider: [1, 60, 1] });
    m("let R = sum((k/n)^2 / n, k, 1, n)");
    m("N(R)");
    md(r`
> [!try]
> Drag ‹n›. The sum is an exact fraction for every $n$, and its decimal falls toward a number from above: the rectangles stand above the curve. Which number? Even at $n = 60$ it is still $0.34\ldots$, so the sums alone are slow to say.
`);
    sec("The area so far");
    md(r`For the exact value, change the question: not the area up to $1$, but the area up to any $x$. Call it $A(x)$, the area so far. How fast does it grow as $x$ moves?`);
    sc(r`
clock X from 0.6 to 1.5
view -0.1, 1.6, -0.15, 2.4
F = graph(x^2, x, 0, 1.5) color 2
LF = label(0.6 + 1.6*i, "f(x) = x^2") color 2
U = ${under("X")} color 2
A = graph(x^3/3, x, 0, X) thick color 1
P = point(X + i*X^3/3) color 1
LA = label(P, "A(x)") color 1
S = poly(X, X + 0.1, X + 0.1 + i*X^2, X + i*X^2) color 3
> show F, LF, U | The curve $y = x^2$, and the region under it from $0$ to $x$.
> show A, P, LA; play X to 1.5 in 5s | Move $x$ and plot the area so far, $A(x)$, as it grows.
> show S; play X to 1 in 3s | Push $x$ on by $dx$: the area gains a thin strip, of height $f(x)$ and width $dx$. So $dA \approx f(x)\,dx$: the slope of $A$ is $f$.
`);
    md(r`Push $x$ on by $dx$ and $A$ grows by a strip of height $f(x)$ and width $dx$, area about $f(x)\,dx$ (the sliver between the strip's top and the curve is smaller still, of the order of $dx^2$). So $dA \approx f(x)\,dx$: the slope of the area so far is the height of the curve, $A' = f$. The area so far is an antiderivative, and lesson 6 finds those.`);
    md(r`For $f = x^2$: $A(x) = \frac{x^3}{3} + C$, and $A(0) = 0$, since there is no area yet, so $C = 0$ and the area up to $1$ is $\frac13$. Any antiderivative $F$ gives the same difference $F(1) - F(0)$: the $C$ cancels.`);
    md(r`
> [!theorem] Fundamental theorem of calculus
> If $f$ is continuous on $[a, b]$ and $F' = f$ there, then $\displaystyle\int_a^b f(x)\,dx = F(b) - F(a)$.
`);
    md(r`‹integrate(f, x, a, b)› finds a checked antiderivative, then evaluates it at the bounds. Step through it:`);
    m("integrate(x^2, x, 0, 1)", { step: 0 });
    md(r`$\frac13 = 0.333\ldots$: the number the Riemann sums were falling toward.`);
    sec("Signed area");
    md(r`One arch of the sine wave, from $0$ to $\pi$, has area exactly $2$:`);
    m("integrate(sin(x), x, 0, pi)");
    md(r`
> [!mistake]
> Twice the interval is not twice the area. From $0$ to $2\pi$ the second arch lies below the axis, where $f < 0$: the strips $f(x)\,dx$ count as negative, and the two arches cancel. A definite integral is a *signed* area.
`);
    sc(r`
view -0.3, 6.6, -1.3, 1.3
G = graph(sin(x), x, 0, 2pi) thick color 2
P = poly(${arch(0)}) color 1
N = poly(${arch(1)}) color 4
LP = label(pi/2 + 0.4*i, "+2") color 1
LN = label(3*pi/2 - 0.5*i, "-2") color 4
> show G, P, LP | From $0$ to $\pi$ the arch is above the axis: its strips $f(x)\,dx$ are positive, and it counts $+2$.
> show N, LN | From $\pi$ to $2\pi$ it is below: its strips are negative, and it counts $-2$. Together, $0$.
`);
    m("integrate(sin(x), x, 0, 2pi)");
    ex("integrate(x, x, 0, 2)", r`Evaluate $\displaystyle\int_0^2 x\,dx$. (Check it against the triangle it is the area of.)`, [r`An antiderivative is $\frac{x^2}{2}$; evaluate at $2$ and at $0$.`]);
    ex("integrate(x^2, x, 1, 3)", r`Evaluate $\displaystyle\int_1^3 x^2\,dx$.`, [r`$F(x) = \frac{x^3}{3}$; the answer is $F(3) - F(1)$.`]);
    ex("integrate(x^3, x, 0, 1)", r`Invent it: what is the area under $y = x^3$ from $0$ to $1$? Find the area-so-far function first.`, [
      r`$A' = x^3$ and $A(0) = 0$.`,
      r`$A(x) = \frac{x^4}{4}$; the area is $A(1)$.`,
    ], { hide: true });
    ex("sum(2k - 1, k, 1, 6)", r`Add the first six odd numbers, $1 + 3 + 5 + \dots + 11$.`, [
      r`Try $1$, then $1 + 3$, then $1 + 3 + 5$: what do the totals have in common?`,
      r`Lesson 1's growing square: from side $k - 1$ to side $k$ it gains two strips and a corner, $2(k - 1) + 1 = 2k - 1$ unit squares.`,
    ], { hide: true });
    md(r`
> [!summary]
> Area is the number rectangle sums approach. The area so far grows at the rate of the curve's height, so it is an antiderivative, and the area from $a$ to $b$ is $F(b) - F(a)$, signed. Slope and area undo each other: that is the fundamental theorem, and the two halves of this course are one subject.
`);
  });
});

// ---------------------------------------------------------------------------------------------------
course("linear-algebra", "Linear algebra: vectors, matrices and systems",
  "Vectors as arrows and as lists, matrices as moves of the plane, solving systems by elimination with verified row operations, the determinant as the factor by which area scales, and change of basis and eigenvectors.",
  "Linear algebra", (add) => {

  add("01-vectors.chalk", "Vectors: arrows, lists and the dot product", "Adding arrows tip to tail, stretching them, reaching every point with two of them, length, and the dot product as a shadow.", ({ sec, md, m, ex, sc }) => {
    sec("Vectors: arrows, lists and the dot product");
    md(r`
> [!goal]
> Add and stretch vectors, as arrows and as lists; reach any point by combining two of them; and see why multiplying entries and adding measures how far two vectors point the same way.
`);
    md(r`Walk 3 steps east and 1 north, then 1 east and 2 north. Where are you? Each walk is an arrow, a **vector**: a length and a direction, wherever it starts. So the question is how to add two arrows.`);
    sc(r`
clock t from 0 to 1
view -0.5, 5, -0.5, 3.6
U = arrow(0, [3, 1]) thick color 3
LU = label([3, 1], "u") color 3
V = arrow(0, [1, 2]) thick color 4
LV = label([1, 2], "v") color 4
W = arrow(t*[3, 1], t*[3, 1] + [1, 2]) color 4
S = arrow(0, [4, 3]) thick color 1
LS = label([4, 3], "u + v") color 1
> show U, LU, V, LV | Two walks: $u$, three east and one north, and $v$, one east and two north.
> show W; play t to 1 in 2s | Do one, then the other: slide $v$, without turning it, until it starts where $u$ ends.
> show S, LS | The sum $u + v$ is where you end up, tip to tail: $(4, 3)$. The east steps add, $3 + 1$, and the north steps add, $1 + 2$.
`);
    md(r`So an arrow from $0$ is recorded by where its tip lands, a list of numbers in brackets, ‹[3, 1]›, and adding arrows tip to tail is adding lists entry by entry. Arrow or list, it is one object seen two ways: the arrow to think with, the list to compute with.`);
    m("[3, 1] + [1, 2]", { work: true });
    md(r`Three entries make an arrow in space; any number of entries make a list that no picture shows, but the arithmetic is the same.`);
    m("[1, 2, 3] + [4, -1, 2]");
    sec("Stretching");
    md(r`Doubling an arrow should double its length and keep its direction: two copies, tip to tail. As lists, $u + u$ doubles every entry. Any number $c$ works the same way, and a negative one turns the arrow round:`);
    sc(r`
clock c from -1.5 to 2
view -5, 7, -2, 3
U = arrow(0, [3, 1]) faint color 3
P = point(c*[3, 1]) color 1
C = arrow(0, P) thick color 1
LC = label(P, "c\,u") color 1
K = value(c, "c = ")
> show U; play c to 1 in 0.6s | The arrow $u = (3, 1)$.
> show C, P, LC, K | $c\,u$ with $c = 1$: $u$ itself.
> play c to 2 in 2s | $c = 2$: twice as long, the same direction.
> play c to 0.5 in 2s | $c = \frac12$: half as long.
> play c to -1.5 in 3s | Through $c = 0$ and out the other side: a negative $c$ points the arrow backwards.
`);
    m("2*[3, 1]");
    m("-[3, 1]");
    sec("Combining two arrows");
    md(r`Stretch $u$ by $a$ and $v$ by $b$, then add: $a\,u + b\,v$ is a **linear combination** of $u$ and $v$. Which points can you reach this way? Drag ‹a› and ‹b›: the path walks $a\,u$ from $0$, then $b\,v$, and the small circle is the point $(5, 5)$.`);
    m("let a = 1", { slider: [-4, 4, 0.5] });
    m("let b = 1", { slider: [-4, 4, 0.5] });
    m("plot([t*a*(3 + i), a*(3 + i) + t*b*(1 + 2i), 5 + 5i + 0.15*exp(2*pi*i*t)], t, 0, 1)");
    m("a*[3, 1] + b*[1, 2]");
    md(r`
> [!try]
> Reach the circle. Then try $(1, 7)$, or a point of your own.
`);
    md(r`Every point can be reached, and a picture says why:`);
    sc(r`
clock t from 0 to 1
view -3, 7, -1.5, 6
let M = [3, 1 + 5*t; 1, 2]
G0 = grid([1, 0; 0, 1]) faint color 6
G = grid(M) color 2
U = arrow(0, [3, 1]) thick color 3
LU = label([3, 1], "u") color 3
V = arrow(0, M*[0; 1]) thick color 4
LV = label(M*[0; 1], "v") color 4
P = point([5, 5]) color 1
W1 = arrow(0, [3, 1]) color 1
W2 = arrow([3, 1], [5, 5]) color 1
> show U, LU, V, LV | $u = (3, 1)$ and $v = (1, 2)$, on the square grid of whole steps east and north.
> show G | Their stretched copies, $a\,u + b\,v$ for whole numbers $a$ and $b$, lay a slanted grid over the whole plane, as whole steps east and north lay the square one. Every point lies in some cell of it, and fractions of $u$ and $v$ reach inside the cell.
> show P, W1, W2 | The circle's point $(5, 5)$ is a corner: $1\,u + 2\,v$.
> hide P, W1, W2; play t to 1 in 4s | Now swing $v$ round to $(6, 2) = 2u$. The cells flatten, and at the end every combination lies on the line through $u$: no point off it can be reached.
`);
    md(r`So two arrows reach every point exactly when they do not lie along one line through $0$. Finding $a$ and $b$ for a given point means solving two equations at once, which is lesson 3.`);
    sec("Length");
    md(r`How long is $(3, 4)$? It is the long side of a right triangle with legs $3$ and $4$, so by Pythagoras it is $\sqrt{3^2 + 4^2} = 5$. In space, Pythagoras twice gives $\sqrt{v_1^2 + v_2^2 + v_3^2}$. ‹norm› computes it.`);
    m("norm([3, 4])", { work: true });
    m("norm([1, 2, 3])");
    sec("How far does one arrow point along another?");
    md(r`How much do two arrows agree in direction? Make it a length. Take a direction, given by a unit arrow $\hat u$ (length $1$), and shine a light at right angles to its line: any arrow $v$ casts a **shadow** on the line.`);
    sc(r`
clock w from 0 to 2pi
view -2.6, 2.6, -2.2, 2.2
let u = [cos(0.5), sin(0.5)]
let v = [2*cos(w + 0.5), 2*sin(w + 0.5)]
K = line(0, u) faint color 6
U = arrow(0, u) thick color 5
LU = label(u, "\hat u") color 5
V = arrow(0, v) color 4
LV = label(v, "v") color 4
S = arrow(0, 2*cos(w)*u) thick color 1
D = segment(v, 2*cos(w)*u) dashed color 1
H = value(2*cos(w), "\text{shadow} = ")
> show K, U, LU | A direction: the unit arrow $\hat u$ and its line.
> show V, LV, S, D, H | An arrow $v$ of length $2$, and its shadow on the line: how far $v$ goes in the direction $\hat u$. Along $\hat u$, the shadow is all of $v$.
> play w to pi/2 in 3s | As $v$ turns away from $\hat u$ the shadow shrinks; at a right angle it is $0$.
> play w to pi in 3s | Past a right angle the shadow points backwards: count its length as negative, down to $-2$.
> play w to 2pi in 4s | All the way round.
`);
    md(r`For the direction $\hat{\imath} = (1, 0)$, east, the shadow of $(v_1, v_2)$ is just its first entry, $v_1$. For a slanted direction $\hat u = (u_1, u_2)$, two facts do all the work.`);
    md(r`First, shadows respect the arithmetic above: arrows tip to tail cast shadows tip to tail, and a stretched arrow casts a stretched shadow. Since $v = v_1 \hat{\imath} + v_2 \hat{\jmath}$, where $\hat{\jmath} = (0, 1)$, the shadow of $v$ is $v_1$ times the shadow of $\hat{\imath}$ plus $v_2$ times the shadow of $\hat{\jmath}$. Second, a symmetry:`);
    sc(r`
view -0.3, 1.45, -0.3, 1
let u = [cos(0.6), sin(0.6)]
K = line(0, u) faint color 6
F = line(0, [cos(0.3), sin(0.3)]) dashed color 6
I = arrow(0, [1, 0]) color 3
LI = label([1, 0], "\hat{\imath}") color 3
U = arrow(0, u) color 5
LU = label(u, "\hat u") color 5
SU = segment(u, [cos(0.6), 0]) dashed color 5
HU = arrow(0, [cos(0.6), 0]) thick color 5
SI = segment([1, 0], cos(0.6)*u) dashed color 3
HI = arrow(0, cos(0.6)*u) thick color 3
> show K, I, LI, U, LU | Two unit arrows: $\hat{\imath}$, and the direction $\hat u = (u_1, u_2)$.
> show SU, HU | The shadow of $\hat u$ on $\hat{\imath}$'s line is its first entry, $u_1$.
> show F, SI, HI | The shadow of $\hat{\imath}$ on $\hat u$'s line. Fold the picture along the dashed line, halfway between the two arrows: $\hat{\imath}$ and $\hat u$ swap places, and so do their lines and the two shadows. So this one is $u_1$ long too.
`);
    md(r`So the shadow of $\hat{\imath}$ on the direction $\hat u$ is $u_1$, and likewise the shadow of $\hat{\jmath}$ is $u_2$. Put together, the shadow of $v$ is $u_1 v_1 + u_2 v_2$: multiply the entries and add.`);
    md(r`
> [!definition] Dot product
> $u \cdot v = u_1 v_1 + u_2 v_2 + \cdots$, over all the entries. For a unit arrow $\hat u$, $\hat u \cdot v$ is the signed length of $v$'s shadow on $\hat u$'s line. Stretching $u$ stretches the product, so for any $u \ne 0$, $u \cdot v = \lVert u \rVert$ times that shadow; and $v \cdot v = \lVert v \rVert^2$.
`);
    m("dot([3, 4], [1, 0])");
    md(r`
> [!try]
> $(1, 2)$ and $(2, -1)$ are at right angles. Predict their dot product before stepping through it.
`);
    m("dot([1, 2], [2, -1])", { step: 0 });
    md(r`
> [!theorem] Angle
> For nonzero $u$ and $v$ at an angle $\theta$, the shadow of $v$ on $u$'s line is $\lVert v \rVert \cos\theta$ (the shadow scene's readout, $2\cos\theta$, was $\hat u \cdot v$), so $u \cdot v = \lVert u \rVert\, \lVert v \rVert \cos\theta$. The sign tells the angle apart: $u \cdot v$ is positive when $\theta$ is less than a right angle, $0$ exactly when $u$ and $v$ are perpendicular, and negative when $\theta$ is more.
`);
    md(r`Turned round, it measures angles: $\cos\theta = \dfrac{u \cdot v}{\lVert u \rVert\, \lVert v \rVert}$. For $u = (3, 1)$ and $v = (1, 2)$ it gives $\pi/4$, an eighth of a turn:`);
    m("N(arccos(dot([3, 1], [1, 2])/(norm([3, 1])*norm([1, 2]))))");
    m("N(pi/4)");
    md(r`
> [!mistake]
> The natural first guess multiplies entry by entry and stops there. That is ‹.*›, and it gives a vector, not a number: for the perpendicular pair above, $(2, -2)$, which says nothing about the angle by itself and changes if the axes are turned. The adding is what makes it a shadow: $2 + (-2) = 0$.
`);
    m("[1, 2] .* [2, -1]");
    ex("dot([1, 2, 3], [4, 5, 6])", r`Compute $(1, 2, 3) \cdot (4, 5, 6)$.`, [r`Multiply entry by entry and add: $1 \cdot 4 + 2 \cdot 5 + 3 \cdot 6$.`]);
    ex("norm([6, 8])", r`How long is the vector $(6, 8)$?`, [r`It is $(3, 4)$ stretched by $2$.`, r`$\sqrt{6^2 + 8^2}$.`], { hide: true });
    ex("dot([1, 3], [2, -1])", r`Is the angle between $(1, 3)$ and $(2, -1)$ more or less than a right angle? Compute their dot product: its sign answers it.`, [r`$1 \cdot 2 + 3 \cdot (-1)$.`, r`Negative means more than a right angle.`]);
    ex("dot([2, 3], [3, -2])", r`Compute $(2, 3) \cdot (3, -2)$. What does the answer say about the two vectors?`, [r`Zero means perpendicular.`]);
    ex("[-1, 4]", r`Find $a$ and $b$ with $a\,(3, 1) + b\,(1, 2) = (1, 7)$, with the sliders above or by hand. Answer with the two numbers as a list, $a$ first.`, [
      r`Compare entries: $3a + b = 1$ and $a + 2b = 7$.`,
      r`The first gives $b = 1 - 3a$; put that into the second.`,
    ], { hide: true });
    md(r`
> [!summary]
> A vector is an arrow and a list at once: arrows add tip to tail, lists add entry by entry, and the two are the same. Two arrows in different directions, stretched and added, reach every point of the plane. The dot product, multiply the entries and add, is the shadow of one arrow on the other's line, times the other's length: zero exactly when they are perpendicular.
>
> Every vector is a combination of the two unit arrows: $(x, y) = x\,\hat{\imath} + y\,\hat{\jmath}$. So what happens to every vector at once if you move $\hat{\imath}$ and $\hat{\jmath}$? That is lesson 2.
`);
  });

  add("02-matrices.chalk", "Matrices as moves of the plane", "A matrix records where the two unit arrows land; from that, where it sends any vector, and multiplying matrices as one move after another, in an order that matters.", ({ sec, md, m, ex, sc }) => {
    sec("Matrices as moves of the plane");
    md(r`
> [!goal]
> Read a matrix as a move of the plane, work out from its columns where it sends any vector, and multiply matrices as one move after another.
`);
    md(r`Move the whole plane: stretch it, turn it, slant it, but keep the grid lines straight, parallel and evenly spaced, and keep $0$ where it is. Such a move is called **linear**. How much do you need to write down to know where every point goes?`);
    sc(r`
clock t from 0 to 1
view -3.2, 3.8, -1.2, 3.8
let A = [2, -1; 1, 1]
let M = (1 - t)*[1, 0; 0, 1] + t*A
G0 = grid([1, 0; 0, 1]) faint color 6
G = grid(M) color 2
I = arrow(0, M*[1; 0]) thick color 3
LI = label(M*[1; 0], "\hat{\imath}") color 3
J = arrow(0, M*[0; 1]) thick color 4
LJ = label(M*[0; 1], "\hat{\jmath}") color 4
D1 = segment(M*[1; 0], M*[1; 1]) dashed color 4
D2 = segment(M*[1; 1], M*[1; 2]) dashed color 4
V = arrow(0, M*[1; 2]) color 1
LV = label(M*[1; 2], "v") color 1
> show D1, D2, V, LV | The grid, the unit arrows $\hat{\imath} = (1, 0)$ (green) and $\hat{\jmath} = (0, 1)$ (pink), and $v = (1, 2) = \hat{\imath} + 2\hat{\jmath}$: one step along $\hat{\imath}$, two along $\hat{\jmath}$.
> play t to 1 in 4s | Move the plane. The grid lines stay straight, parallel and evenly spaced, and $0$ stays put. $\hat{\imath}$ lands on $(2, 1)$ and $\hat{\jmath}$ on $(-1, 1)$.
> wait 1s | And $v$ is still one step along the new $\hat{\imath}$ and two along the new $\hat{\jmath}$: it lands on $(2, 1) + 2\,(-1, 1) = (0, 3)$.
`);
    md(r`Two arrows' worth. Every vector is $x\,\hat{\imath} + y\,\hat{\jmath}$, and a linear move keeps that recipe, so wherever $\hat{\imath}$ and $\hat{\jmath}$ land, $(x, y)$ lands on $x$ times the first landing spot plus $y$ times the second.`);
    md(r`So write down the two landing spots, side by side as columns: that table is a **matrix**. Rows are separated by ‹;›, so the columns read downwards: here $\hat{\imath}$ lands on $(2, 1)$ and $\hat{\jmath}$ on $(-1, 1)$.`);
    m("let A = [2, -1; 1, 1]");
    md(r`
> [!try]
> Before the next cell: where does $A$ send $(1, 2)$, written as a column ‹[1; 2]›? Use only the columns.
`);
    m("A*[1; 2]", { work: true });
    md(r`The same for any input $(x, y)$: $x$ times the first column plus $y$ times the second. That is the whole rule for a matrix times a vector, with nothing to memorise:`);
    m("x*[2; 1] + y*[-1; 1]");
    m("A*[x; y]");
    md(r`
> [!definition] Matrix times vector
> $\begin{pmatrix} a & b \\ c & d \end{pmatrix} \begin{pmatrix} x \\ y \end{pmatrix} = x \begin{pmatrix} a \\ c \end{pmatrix} + y \begin{pmatrix} b \\ d \end{pmatrix} = \begin{pmatrix} ax + by \\ cx + dy \end{pmatrix}$. Each entry of the answer is a row of the matrix dotted with the vector.
`);
    m("[a, b; c, d]*[x; y]");
    sec("Moves, read off their columns");
    md(r`To write down a move, ask where $\hat{\imath}$ and $\hat{\jmath}$ go. A quarter turn counterclockwise sends $\hat{\imath}$ to $(0, 1)$ and $\hat{\jmath}$ to $(-1, 0)$. A shear slides each point sideways by its height: $\hat{\imath}$ stays, and $\hat{\jmath}$ slides to $(1, 1)$.`);
    m("let R = [0, -1; 1, 0]");
    m("let S = [1, 1; 0, 1]");
    m("R*[3; 1]");
    m("S*[3; 1]");
    sec("One move after another");
    md(r`Shear, then turn. Where do $\hat{\imath}$ and $\hat{\jmath}$ end up?`);
    sc(r`
clock t from 0 to 2
view -2.8, 2.8, -0.8, 2.6
let S = [1, 1; 0, 1]
let Sh = (1 - t)*[1, 0; 0, 1] + t*S
let Tn = [cos(pi*(t - 1)/2), -sin(pi*(t - 1)/2); sin(pi*(t - 1)/2), cos(pi*(t - 1)/2)]*S
G0 = grid([1, 0; 0, 1]) faint color 6
G1 = grid(Sh) color 2
Q1 = poly(0, Sh*[1; 0], Sh*[1; 1], Sh*[0; 1]) color 1
I1 = arrow(0, Sh*[1; 0]) thick color 3
J1 = arrow(0, Sh*[0; 1]) thick color 4
G2 = grid(Tn) color 2
Q2 = poly(0, Tn*[1; 0], Tn*[1; 1], Tn*[0; 1]) color 1
I2 = arrow(0, Tn*[1; 0]) thick color 3
J2 = arrow(0, Tn*[0; 1]) thick color 4
> show G1, Q1, I1, J1 | The unit square on $\hat{\imath}$ (green) and $\hat{\jmath}$ (pink).
> play t to 1 in 2s | First the shear $S$: $\hat{\imath}$ stays put, $\hat{\jmath}$ slides over to $(1, 1)$.
> hide G1, Q1, I1, J1; show G2, Q2, I2, J2 | Then the quarter turn $R$, applied to wherever things are now.
> play t to 2 in 2s | $\hat{\imath}$ ends at $(0, 1)$ and $\hat{\jmath}$ at $(-1, 1)$: the columns of the combined move.
`);
    md(r`Each column of the combined move is $R$ applied to a column of $S$: the shear sent $\hat{\jmath}$ to $(1, 1)$, $S$'s second column, and the turn took it on from there. That is how matrices multiply. The combined move is written $RS$, with $S$ on the right, because it acts on a vector as $R(Sv)$: as in $f(g(x))$, the one written nearer the vector happens first.`);
    m("R*S", { work: true });
    m("R*(S*[3; 1])");
    m("(R*S)*[3; 1]");
    md(r`
> [!definition] Matrix product
> Column $j$ of $AB$ is $A$ times column $j$ of $B$: $AB$ is the move "$B$, then $A$". So its entry in row $i$, column $j$ is row $i$ of $A$ dotted with column $j$ of $B$, which is the quick way to compute it.
`);
    sec("The order matters");
    md(r`
> [!try]
> Now turn first, then shear. Predict where $\hat{\imath}$ lands before the scene plays: the turn sends it to $(0, 1)$, and then the shear slides it sideways by its height.
`);
    sc(r`
clock t from 0 to 2
view -2.8, 2.8, -0.8, 2.6
let R = [0, -1; 1, 0]
let S = [1, 1; 0, 1]
let Tn = [cos(pi*t/2), -sin(pi*t/2); sin(pi*t/2), cos(pi*t/2)]
let Sh = ((2 - t)*[1, 0; 0, 1] + (t - 1)*S)*R
G0 = grid([1, 0; 0, 1]) faint color 6
G1 = grid(Tn) color 2
Q1 = poly(0, Tn*[1; 0], Tn*[1; 1], Tn*[0; 1]) color 1
I1 = arrow(0, Tn*[1; 0]) thick color 3
J1 = arrow(0, Tn*[0; 1]) thick color 4
G2 = grid(Sh) color 2
Q2 = poly(0, Sh*[1; 0], Sh*[1; 1], Sh*[0; 1]) color 1
I2 = arrow(0, Sh*[1; 0]) thick color 3
J2 = arrow(0, Sh*[0; 1]) thick color 4
F = poly(0, [0, 1], [-1, 2], [-1, 1]) faint color 6
FI = arrow(0, [0, 1]) faint color 3
FJ = arrow(0, [-1, 1]) faint color 4
> show G1, Q1, I1, J1 | The same square; this time the turn comes first.
> play t to 1 in 2s | The quarter turn $R$: $\hat{\imath}$ goes to $(0, 1)$, $\hat{\jmath}$ to $(-1, 0)$.
> hide G1, Q1, I1, J1; show G2, Q2, I2, J2 | Then the shear $S$, which slides each point sideways by its height.
> play t to 2 in 2s | $\hat{\imath}$, at height $1$, slides to $(1, 1)$; $\hat{\jmath}$, at height $0$, stays at $(-1, 0)$.
> show F, FI, FJ | Faint: where shear-then-turn left the square. A different move.
`);
    md(r`
> [!mistake]
> With numbers the order of a product never matters, so the natural guess is $SR = RS$. The pictures already disagree, and so does the engine:
`);
    m("S*R");
    md(r`Some pairs do commute (two turns, for instance), but in general $AB \neq BA$.`);
    ex("[2, -1; 1, 1]*[3; -1]", r`Where does $A = \begin{pmatrix} 2 & -1 \\ 1 & 1 \end{pmatrix}$ send $(3, -1)$? Work it out from the columns, then type it as a column, ‹[p; q]›.`, [
      r`$3$ times the first column minus the second: $3\,(2, 1) - (-1, 1)$.`,
    ]);
    ex("[0, 1; 1, 0]", r`Invent it: write the matrix of the mirror in the line $y = x$, which swaps $\hat{\imath}$ and $\hat{\jmath}$.`, [
      r`Where does $\hat{\imath}$ land? That is the first column.`,
    ], { hide: true });
    ex("[0, -1; 1, 0]*[0, -1; 1, 0]", r`A quarter turn done twice is a half turn. Write its matrix from where $\hat{\imath}$ and $\hat{\jmath}$ land, then check that it is $RR$.`, [
      r`A half turn sends $\hat{\imath}$ to $(-1, 0)$.`,
    ], { hide: true });
    ex("[1, 2; 3, 4]*[0, 1; 1, 0]", r`Multiply. The right-hand matrix swaps $\hat{\imath}$ and $\hat{\jmath}$, and it happens first: predict what that does to the columns of the left-hand one.`, [
      r`Column $1$ of the product is $\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$ times $(0, 1)$: its second column.`,
      r`The answer is a matrix: type it as ‹[p, q; r, s]›.`,
    ]);
    md(r`
> [!summary]
> A matrix is a linear move of the plane, written down as where $\hat{\imath}$ and $\hat{\jmath}$ land, its columns. It sends $(x, y)$ to $x$ times the first column plus $y$ times the second. The product $AB$ is "$B$, then $A$", its columns $A$ times the columns of $B$, and the order matters.
>
> Lesson 2 ran the move forwards. Lesson 3 runs it backwards: given where a vector landed, which vector was it?
`);
  });

  add("03-systems.chalk", "Solving systems by elimination", "Which input lands on a given output: elimination on the augmented matrix, row operations proved to keep the solutions, and the matrices that squash the plane, with no solution or infinitely many.", ({ sec, md, m, ex, sc }) => {
    sec("Solving systems by elimination");
    md(r`
> [!goal]
> Find which input a matrix sends to a given output by elimination on the augmented matrix, and see when there is one answer, none, or infinitely many.
`);
    md(r`Lesson 2 ran a matrix forwards. Now run one backwards: $\begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix}$ sends some $(x, y)$ to $(5, 6)$. Which?`);
    md(r`The matrix sends $(x, y)$ to $x$ times its first column plus $y$ times its second. So the question is which combination of the columns makes $(5, 6)$; entry by entry, it is two equations, $x + 2y = 5$ and $3x + 4y = 6$.`);
    m("[1, 2; 3, 4]*[x; y]");
    sec("Elimination");
    md(r`By hand you would eliminate: take $3$ times the first equation from the second, so that $x$ drops out of it; solve that for $y$; put it back. Only the numbers matter, so write the system as one table, the **augmented matrix**: one row per equation, the right-hand sides in the last column, ‹[1, 2, 5; 3, 4, 6]›.`);
    md(r`
> [!try]
> Each step below is a move on the equations: swap two, scale one by a nonzero number, or add a multiple of one to another. Before stepping, predict the first move and what the second row becomes.
`);
    m("rref([1, 2, 5; 3, 4, 6])", { step: 0 });
    md(r`The result is in **reduced row echelon form**: each variable stands alone in its own row. The first row says $x = -4$, the second $y = \frac92$. Run it forwards to check:`);
    m("[1, 2; 3, 4]*[-4; 9/2]");
    md(r`Why do the moves never lose the answer, or make up a new one? Draw the equations. The points $(x, y)$ with $x + 2y = 5$ form a line, and so do those with $3x + 4y = 6$; the solution is where the two lines cross.`);
    sc(r`
clock t from 0 to 2
view -7.5, 3.5, -0.8, 6.8
let a2 = 3 - 3*t
let b2 = 4 - 6*t
let c2 = 6 - 15*t
let b1 = 4 - 2*t
let c1 = 14 - 9*t
L1 = line([1, 2], [-1, 3]) thick color 3
L2 = line(c2/(a2^2 + b2^2)*[a2, b2], c2/(a2^2 + b2^2)*[a2, b2] + [-b2, a2]) thick color 4
L2b = line([0, 4.5], [1, 4.5]) thick color 4
L1m = line(c1/(1 + b1^2)*[1, b1], c1/(1 + b1^2)*[1, b1] + [-b1, 1]) thick color 3
X = point([-4, 4.5]) thick color 1
LX = label([-4, 4.5], "(-4, \tfrac92)") color 1
> show L1, L2, X, LX | The two equations as lines: $x + 2y = 5$ (green) and $3x + 4y = 6$ (pink). The solution is where they cross.
> play t to 1 in 3s | Take $3$ times the first row from the second, a little at a time. Part way, the row is $3x + 4y - s\,(x + 2y) = 6 - 5s$, true wherever both equations are: the pink line turns about the crossing, and ends level, $-2y = -9$.
> hide L2; show L2b | Scale the second row by $-\frac12$: $y = \frac92$. The same line, written more simply.
> hide L1; show L1m; play t to 2 in 3s | Take twice the second row from the first. Now the green line turns, about the same point, until it stands upright: $x = -4$.
> | Reduced, each line names one coordinate, and the crossing never moved: $x = -4$, $y = \frac92$.
`);
    md(r`So no move loses the solution: a combination of the equations holds wherever both do, and its line goes through the crossing. Nor does a move make up a new one, because each move can be undone, and undoing it would lose that new solution.`);
    md(r`
> [!theorem] Row operations keep the solutions
> Swapping two rows, scaling a row by a nonzero number and adding a multiple of one row to another do not change the set of solutions. Each move can be undone by another (swap back, scale by the reciprocal, subtract the multiple again), so no solution is gained and none is lost. For rational entries each of the three is proved in Lean, as is elimination as a whole and the claim that its result is in reduced row echelon form: the green dots on the steps.
`);
    md(r`Scaling by $0$ is the one move left out, because it cannot be undone: it turns an equation into $0 = 0$ and forgets it.`);
    sec("Three equations");
    md(r`Three unknowns, three equations, the same moves: $2x + y - z = 8$, $-3x - y + 2z = -11$, $-2x + y + 2z = -3$.`);
    m("rref([2, 1, -1, 8; -3, -1, 2, -11; -2, 1, 2, -3])", { work: true });
    md(r`So $x = 2$, $y = 3$, $z = -1$. Forwards again, all three equations at once:`);
    m("[2, 1, -1; -3, -1, 2; -2, 1, 2]*[2; 3; -1]");
    sec("When it fails");
    md(r`Not every matrix can be run backwards. $\begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix}$ sends $\hat{\imath}$ to $(1, 2)$ and $\hat{\jmath}$ to $(2, 4)$, in the same direction. Watch the plane:`);
    sc(r`
clock t from 0 to 1
view -3, 6, -2, 8
let M = (1 - t)*[1, 0; 0, 1] + t*[1, 2; 2, 4]
G0 = grid([1, 0; 0, 1]) faint color 6
G = grid(M) color 2
Q = poly(0, M*[1; 0], M*[1; 1], M*[0; 1]) color 5
K = line(0, [1, 2]) dashed color 6
I = arrow(0, M*[1; 0]) thick color 3
J = arrow(0, M*[0; 1]) thick color 4
P1 = point(M*[3; 0]) color 1
P2 = point(M*[1; 1]) color 1
P3 = point(M*[-1; 2]) color 1
T = point([3, 7]) thick color 6
LT = label([3, 7], "(3, 7)") color 6
> wait 1s | The grid, the unit square on $\hat{\imath}$ (green) and $\hat{\jmath}$ (pink), and three points: $(3, 0)$, $(1, 1)$ and $(-1, 2)$.
> show K; play t to 1 in 4s | Apply the matrix: $\hat{\imath}$ goes to $(1, 2)$, $\hat{\jmath}$ to $(2, 4)$, and the whole plane is squashed onto the line $y = 2x$, the square to a segment of it. All three points land on $(3, 6)$.
> show T, LT | Nothing lands on $(3, 7)$, off the line.
`);
    md(r`Every output lies on one line. A target on it, such as $(3, 6)$, is hit by a whole line of inputs; a target off it, such as $(3, 7)$, by none. Elimination finds both:`);
    m("rref([1, 2, 3; 2, 4, 6])", { work: true });
    md(r`A row of zeros: the second equation was twice the first, and only $x + 2y = 3$ is left, a whole line of solutions.`);
    m("rref([1, 2, 3; 2, 4, 7])", { work: true });
    md(r`The last row says $0x + 0y = 1$: no solution.`);
    ex("rref([1, 1, 3; 1, -1, 1])", r`Solve $x + y = 3,\ x - y = 1$ by reducing the augmented matrix. Give the reduced matrix.`, [
      r`The augmented matrix is ‹[1, 1, 3; 1, -1, 1]›.`,
      r`Subtract the first row from the second, giving $0, -2, -2$; scale that by $-\frac12$; then subtract it from the first row.`,
    ], { hide: true });
    ex("rref([2, 4, 6; 1, 3, 4])", r`Reduce the augmented matrix of $2x + 4y = 6,\ x + 3y = 4$.`, [
      r`Scale the first row by $\frac12$ first.`,
    ], { hide: true });
    ex("rref([3, 1, 5; 1, 2, 5])", r`Lesson 1 asked for $a$ and $b$ with $a\,(3, 1) + b\,(1, 2) = (5, 5)$, found by dragging. Find them by elimination: give the reduced augmented matrix.`, [
      r`The columns are $(3, 1)$, $(1, 2)$ and the target $(5, 5)$: ‹[3, 1, 5; 1, 2, 5]›.`,
    ], { hide: true });
    ex("rref([1, -1, 2; -2, 2, 1])", r`Reduce the augmented matrix of $x - y = 2,\ -2x + 2y = 1$. How many solutions are there?`, [
      r`Add twice the first row to the second.`,
      r`A row $0, 0, c$ with $c \neq 0$ says $0 = c$.`,
    ], { hide: true });
    md(r`
> [!summary]
> Solving $A\,x = b$ asks which input $A$ sends to $b$. Elimination answers it with three moves on the augmented matrix, each of which can be undone and so keeps the solutions, until each variable stands alone. A matrix that squashes the plane onto a line cannot be run backwards: a target on the line has infinitely many inputs, one off it has none.
>
> How can you tell from the matrix alone, before solving anything, whether it squashes the plane? Lesson 4 measures what it does to area.
`);
  });

  add("04-determinants.chalk", "Determinants: how a matrix scales area", "The determinant as the factor by which a matrix scales area, ad − bc from a picture, its sign as a flip, zero as squashing with no inverse, and why determinants multiply.", ({ sec, md, m, ex, sc }) => {
    sec("Determinants: how a matrix scales area");
    md(r`
> [!goal]
> Find the factor by which a matrix scales area, get $ad - bc$ from a picture, and read a flip and the lack of an inverse off its sign and its zeros.
`);
    md(r`Lesson 3's $\begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix}$ squashed the plane onto a line, and could not be run backwards. How could you tell that from the four entries alone? Watch what a matrix does to area.`);
    sc(r`
clock t from 0 to 1
view -1.5, 5.8, -1.2, 5.4
let M = (1 - t)*[1, 0; 0, 1] + t*[3, 1; 1, 2]
G0 = grid([1, 0; 0, 1]) faint color 6
G = grid(M) color 2
Q = poly(0, M*[1; 0], M*[1; 1], M*[0; 1]) color 1
N = poly(M*[0; 1], M*[1; 1], M*[1; 2], M*[0; 2]) color 5
I = arrow(0, M*[1; 0]) thick color 3
J = arrow(0, M*[0; 1]) thick color 4
A = value(det(M), "\text{area} = ")
T1 = poly(0, [3, 0], [3, 1]) faint color 3
T2 = poly([4, 3], [1, 3], [1, 2]) faint color 3
T3 = poly([3, 1], [4, 1], [4, 3]) faint color 4
T4 = poly([1, 2], [0, 2], 0) faint color 4
S1 = poly([3, 0], [4, 0], [4, 1], [3, 1]) faint color 6
S2 = poly([0, 2], [1, 2], [1, 3], [0, 3]) faint color 6
> show N; wait 1s | The grid, and the unit square on $\hat{\imath}$ (green) and $\hat{\jmath}$ (pink): area $1$, like the square above it.
> show A; play t to 1 in 4s | Apply $\begin{pmatrix} 3 & 1 \\ 1 & 2 \end{pmatrix}$: $\hat{\imath}$ lands on $(3, 1)$, $\hat{\jmath}$ on $(1, 2)$, and the square on the parallelogram they span. The square above it, and every other grid square, becomes a copy of it.
> hide N; show T1, T2, T3, T4, S1, S2 | Why $5$: box it in. The box is $3 + 1$ by $1 + 2$. Outside the parallelogram are two triangles of area $\frac32$ (green), two of area $1$ (pink) and two unit squares: $12 - 3 - 2 - 2 = 5$.
`);
    md(r`Because the grid lines stay parallel and evenly spaced, every grid square becomes the same parallelogram, so every area (fill a shape with small squares) is scaled by one factor: the area of the parallelogram the columns span. That factor is the **determinant**. For columns $(a, c)$ and $(b, d)$ with positive entries, as in the picture, the box is $a + b$ by $c + d$, and what lies outside is two triangles of area $\frac12 ac$, two of area $\frac12 bd$, and two rectangles $b$ by $c$:`);
    m("expand((a + b)*(c + d) - a*c - b*d - 2*b*c)");
    md(r`
> [!definition] Determinant of a $2 \times 2$ matrix
> $\det \begin{pmatrix} a & b \\ c & d \end{pmatrix} = ad - bc$: the factor by which the matrix scales area, with a sign that is the next section's subject.
`);
    m("det([a, b; c, d])");
    m("let A = [3, 1; 1, 2]");
    m("det(A)", { step: 0 });
    md(r`
> [!try]
> Predict before computing. Stretching by $a$ across and by $d$ upwards should scale area by $ad$. A shear slides each square into a parallelogram with the same base and height, so it should not change area at all.
`);
    m("det([a, 0; 0, d])");
    m("det([1, k; 0, 1])");
    sec("The sign: flipping the plane over");
    md(r`$ad - bc$ can be negative, and an area cannot. Swap the columns of $\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$: $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ sends $\hat{\imath}$ to $(0, 1)$ and $\hat{\jmath}$ to $(1, 0)$, a mirror in the line $y = x$.`);
    m("det([0, 1; 1, 0])");
    sc(r`
clock t from 0 to 1
view -0.8, 1.8, -0.5, 1.5
let M = [1 - t, t; t, 1 - t]
G0 = grid([1, 0; 0, 1]) faint color 6
G = grid(M) color 2
Q = poly(0, M*[1; 0], M*[1; 1], M*[0; 1]) color 1
I = arrow(0, M*[1; 0]) thick color 3
LI = label(M*[1; 0], "\hat{\imath}") color 3
J = arrow(0, M*[0; 1]) thick color 4
LJ = label(M*[0; 1], "\hat{\jmath}") color 4
D = value(det(M), "\det = ")
> wait 1s | The unit square: $\hat{\jmath}$ is a quarter turn counterclockwise from $\hat{\imath}$.
> play t to 0.5 in 2.5s | Slide $\hat{\imath}$ toward $(0, 1)$ and $\hat{\jmath}$ toward $(1, 0)$. Halfway they meet, the square is flat, and the determinant is $0$.
> play t to 1 in 2.5s | They pass each other, and the square opens out again, the same size but mirrored: now $\hat{\jmath}$ is clockwise from $\hat{\imath}$, and the determinant is $-1$.
`);
    md(r`The size of the area is unchanged; the negative sign records that the plane has been turned over. Halfway the matrix is $\begin{pmatrix} \frac12 & \frac12 \\ \frac12 & \frac12 \end{pmatrix}$, both columns on the line $y = x$. Along the way the determinant the scene read off is a straight run from $1$ to $-1$:`);
    m("expand(det([1 - t, t; t, 1 - t]))");
    md(r`That is no accident of this path: the determinant changes continuously as the entries do, so any continuous way of turning the plane into its mirror image passes through a moment with no area.`);
    sec("Zero: squashed flat");
    md(r`Back to the opening question. A determinant of $0$ means the unit square goes to something with no area: the columns lie on one line, and the plane is squashed onto it (or onto $0$), as in lesson 3's picture.`);
    m("det([1, 2; 2, 4])");
    md(r`Squashing cannot be undone: many inputs land on each output, as lesson 3 found. When the determinant is not $0$ nothing is squashed, every target has exactly one input, and the move can be undone. Undoing $A$ means finding the inputs that $A$ sends to $\hat{\imath}$ and to $\hat{\jmath}$: those are the columns of the **inverse**. Elimination finds both at once, with both targets in the augmented matrix:`);
    m("rref([3, 1, 1, 0; 1, 2, 0, 1])");
    md(r`The right half is the inverse; $A$ times it gives back $\hat{\imath}$ and $\hat{\jmath}$. Every entry has $5 = \det A$ underneath: dividing by the determinant is part of undoing a matrix, and a determinant of $0$ cannot be divided by.`);
    m("A*[2/5, -1/5; -1/5, 3/5]");
    md(r`
> [!theorem] Invertibility
> A square matrix has an inverse exactly when its determinant is not zero.
`);
    sec("One move after another");
    md(r`Do $B$, then $A$. $B$ scales every area by $\det B$, then $A$ scales the result by $\det A$, so together they scale it by the product:`);
    md(r`
> [!theorem] Determinant of a product
> $\det(AB) = \det A \cdot \det B$.
`);
    m("let B = [1, -1; 1, 1]");
    m("det(B)");
    m("det(A*B)");
    md(r`
> [!mistake]
> Area scales multiply; they do not add. The tempting $\det(A + B) = \det A + \det B$ is false: here it would be $5 + 2 = 7$.
`);
    m("det(A + B)");
    sec("Three dimensions");
    md(r`A $3 \times 3$ matrix moves space, sending the three unit arrows to its three columns, and its determinant is the factor by which it scales volume: the signed volume of the slanted box the columns span. ‹det› expands it along the first row. A determinant of $0$ means space is squashed onto a plane, a line or a point.`);
    m("det([2, 1, 0; 1, 3, 1; 0, 1, 2])");
    ex("det([2, 1; 5, 3])", r`By what factor does $\begin{pmatrix} 2 & 1 \\ 5 & 3 \end{pmatrix}$ scale area?`, [r`$ad - bc$ with $a = 2,\ b = 1,\ c = 5,\ d = 3$.`]);
    ex("det([3, 6; 1, 2])", r`Compute the determinant. Is the matrix invertible?`, [r`Is one column a multiple of the other?`]);
    ex("det(2*[1, 2; 3, 4])", r`Invent it: $\det \begin{pmatrix} 1 & 2 \\ 3 & 4 \end{pmatrix} = -2$. Predict the determinant of twice that matrix, $\begin{pmatrix} 2 & 4 \\ 6 & 8 \end{pmatrix}$, before computing it.`, [
      r`Doubling every entry doubles both columns: both sides of the parallelogram.`,
      r`Not $2 \cdot (-2)$.`,
    ], { hide: true });
    ex("det([1, 0, 0; 0, 2, 0; 0, 0, 3])", r`By what factor does $\begin{pmatrix} 1 & 0 & 0 \\ 0 & 2 & 0 \\ 0 & 0 & 3 \end{pmatrix}$ scale volume?`, [r`It stretches the unit cube into a box, $1$ by $2$ by $3$.`]);
    md(r`
> [!summary]
> The determinant is the factor by which a matrix scales area (volume, in space): the area of the parallelogram its columns span, $ad - bc$ for a $2 \times 2$ matrix. A negative sign means the plane is flipped over; $0$ means it is squashed flat, which is exactly when there is no inverse. One move after another multiplies the factors.
>
> A diagonal matrix such as $\begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$ is the easiest kind to understand: it stretches along the axes, by $3$ and by $1$, and its determinant is $3 \cdot 1$. Most matrices are not diagonal. But perhaps that is only because $\hat{\imath}$ and $\hat{\jmath}$ are the wrong arrows to describe them with: are there directions a matrix only stretches? Lesson 5.
`);
  });

  add("05-change-of-basis.chalk", "Change of basis and eigenvectors", "Describing the plane with arrows of your own choosing, the matrix that translates between descriptions, and the arrows a matrix only stretches, in which it is a diagonal matrix.", ({ sec, md, m, ex, sc }) => {
    sec("Change of basis and eigenvectors");
    md(r`
> [!goal]
> Describe vectors with two arrows of your own choosing, translate between that description and ours, and find the arrows a matrix only stretches.
`);
    md(r`Lesson 4 ended on a hope. $A = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ sends $\hat{\imath}$ to $(2, 1)$ and $\hat{\jmath}$ to $(1, 2)$: it turns both and stretches both, and its columns say little more. Seen through other arrows, might it be as simple as a diagonal matrix? That is two questions. How do you describe the plane with arrows other than $\hat{\imath}$ and $\hat{\jmath}$? And which arrows suit $A$?`);
    sec("Coordinates in another basis");
    md(r`Lesson 1 found that two arrows not on one line reach every point: their stretched copies lay a slanted grid over the plane. So any such pair can stand in for $\hat{\imath}$ and $\hat{\jmath}$. Take $b_1 = (2, 1)$ and $b_2 = (-1, 1)$, and walk two steps along $b_1$ and one along $b_2$. Where do you end up, in our terms?`);
    sc(r`
clock t from 0 to 1
view -3.6, 5.6, -1.2, 4.2
let P = [2, -1; 1, 1]
let M = (1 - t)*[1, 0; 0, 1] + t*P
G0 = grid([1, 0; 0, 1]) faint color 6
G = grid(M) color 2
B1 = arrow(0, M*[1; 0]) thick color 3
LB1 = label(M*[1; 0], "b_1") color 3
B2 = arrow(0, M*[0; 1]) thick color 4
LB2 = label(M*[0; 1], "b_2") color 4
V = point(M*[2; 1]) thick color 1
LV = label(M*[2; 1], "v") color 1
W1 = arrow(0, 2*P*[1; 0]) color 3
W2 = arrow(2*P*[1; 0], P*[2; 1]) color 4
> show G0, B1, LB1, B2, LB2, V, LV | Our grid, and the point $(2, 1)$ on it: two steps along $\hat{\imath}$ and one along $\hat{\jmath}$. The two arrows are about to become $b_1$ and $b_2$.
> show G; play t to 1 in 4s | Carry the grid along with $P = \begin{pmatrix} 2 & -1 \\ 1 & 1 \end{pmatrix}$, whose columns are $b_1$ and $b_2$. The arrows land on $b_1$ and $b_2$, the grid becomes theirs, and the point keeps its place on it: it lands at $v = 2b_1 + b_2 = (3, 3)$.
> show W1, W2 | Two steps along $b_1$ and one along $b_2$: described with $b_1$ and $b_2$, $v$ is $(2, 1)$; described with $\hat{\imath}$ and $\hat{\jmath}$, it is $(3, 3)$.
`);
    md(r`Each vector has exactly one such description. Two different pairs for one vector would subtract to a combination of $b_1$ and $b_2$ that is $0$ without both numbers being $0$, and then $b_1$ and $b_2$ would lie on one line.`);
    md(r`
> [!definition] Basis and coordinates
> Two vectors $b_1, b_2$ of the plane that do not lie on one line are a **basis**: every vector is $v = c_1 b_1 + c_2 b_2$ for exactly one pair $(c_1, c_2)$, its **coordinates** in that basis. $\hat{\imath}$ and $\hat{\jmath}$ are one basis among many.
`);
    md(r`Their coordinates into ours is what the scene did, with $P$, the matrix whose columns are $b_1$ and $b_2$. Lesson 2 says why: $P$ sends $(c_1, c_2)$ to $c_1$ times its first column plus $c_2$ times its second, which is $c_1 b_1 + c_2 b_2$.`);
    m("let P = [2, -1; 1, 1]");
    m("P*[2; 1]");
    md(r`Ours into theirs is the same question run backwards, which is lesson 3's: which input does $P$ send to $v$?`);
    md(r`
> [!try]
> Before the next cell: which augmented matrix gives the coordinates of $(3, 3)$, and what should its last column come out as?
`);
    m("rref([2, -1, 3; 1, 1, 3])", { work: true });
    md(r`The last column is the coordinates, $(2, 1)$: elimination undid $P$.`);
    md(r`
> [!theorem] Finding coordinates is solving a system
> The coordinates $c$ of $v$ in the basis are the solution of $Pc = v$: elimination on $P$ with $v$ beside it. Since $b_1$ and $b_2$ are not on one line, $\det P \neq 0$ (lesson 4), and there is exactly one solution.
`);
    sec("Arrows a matrix only stretches");
    md(r`Now the second question: which arrows suit $A$? The best would be arrows that $A$ does not turn at all, only stretches. Along such an arrow, $A$ acts like a plain number.`);
    md(r`
> [!try]
> $A$ sends $(1, 0)$ to its first column, $(2, 1)$: off the line through $(1, 0)$. Before the scene, work out where it sends $(1, 1)$. Is that on the line through $(1, 1)$?
`);
    sc(r`
clock t from 0 to 1
view -3.6, 4.6, -1.4, 3.9
let A = [2, 1; 1, 2]
let M = (1 - t)*[1, 0; 0, 1] + t*A
G0 = grid([1, 0; 0, 1]) faint color 6
G = grid(M) color 2
K1 = line(0, [1, 1]) dashed color 3
K2 = line(0, [1, -1]) dashed color 4
U = arrow(0, M*[1; 1]) thick color 3
LU = label(M*[1; 1], "u") color 3
W = arrow(0, M*[-0.5; 0.5]) thick color 4
LW = label(M*[-0.5; 0.5], "w") color 4
X = arrow(0, M*[1; 0]) thick color 1
KX = line(0, [1, 0]) dashed color 1
> show G0, U, LU, W, LW, X, KX | Three vectors, each on a line through $0$: $u = (1, 1)$, $w = (-\frac12, \frac12)$, and $(1, 0)$ in orange.
> show G; play t to 1 in 4s | Apply $A$. The orange vector $(1, 0)$ is turned off its line, to $(2, 1)$.
> show K1, K2 | But $u$ stays on its line, stretched three times to $(3, 3)$, and $w$ stays exactly where it was: stretched by $1$.
`);
    md(r`Arrows like $u$ and $w$ are what we were looking for, and they have a name.`);
    md(r`
> [!definition] Eigenvector and eigenvalue
> A nonzero vector $v$ is an **eigenvector** of $A$ when $A$ only stretches it: $Av = \lambda v$ for a number $\lambda$, its **eigenvalue**. The line through $v$ is then carried onto itself. In the scene, $u$ has eigenvalue $3$ and $w$ has eigenvalue $1$.
`);
    m("let A = [2, 1; 1, 2]");
    m("A*[1; 1]");
    m("A*[-1; 1]");
    md(r`$u$ and $w$ were found by looking at a picture. How would you find them for a matrix you cannot picture?`);
    md(r`
> [!try]
> Invent it. $Av = \lambda v$ says $(A - \lambda I)v = 0$, where $I = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}$: the matrix $A - \lambda I$ sends a nonzero vector to $0$. What does lesson 4 say about such a matrix, and what equation does that give for $\lambda$?
`);
    md(r`
> [!theorem] The characteristic polynomial
> If $A - \lambda I$ sends a nonzero $v$ to $0$, where it also sends $0$, it squashes the plane and cannot be undone, so $\det(A - \lambda I) = 0$. That is an equation in $\lambda$ alone: the eigenvalues are the roots of the polynomial $\det(A - \lambda I)$.
`);
    md(r`For $A$, writing $x$ for $\lambda$: $(2 - x)^2 - 1 = x^2 - 4x + 3 = (x - 1)(x - 3)$, with roots $1$ and $3$, the two stretches in the scene.`);
    m("expand(det(A - x*[1, 0; 0, 1]))");
    m("subst(det(A - x*[1, 0; 0, 1]), x, 3)");
    m("subst(det(A - x*[1, 0; 0, 1]), x, 1)");
    md(r`Each eigenvalue then gives its eigenvectors: the inputs that $A - \lambda I$ sends to $0$, found by elimination again. For $\lambda = 3$, $A - 3I = \begin{pmatrix} -1 & 1 \\ 1 & -1 \end{pmatrix}$, with $0$ as the target:`);
    m("rref([-1, 1, 0; 1, -1, 0])", { work: true });
    md(r`A row of zeros, and $x - y = 0$: a whole line of solutions, the line through $u = (1, 1)$.`);
    sec("The matrix in its own basis");
    md(r`Back to the opening question. Describe the plane with the eigenvectors, $b_1 = (1, 1)$ and $b_2 = (-1, 1)$, and ask, as lesson 2 did, where $A$ sends the two arrows. Multiplying by the matrix whose columns they are does both at once:`);
    m("A*[1, -1; 1, 1]");
    md(r`
> [!try]
> The columns are $3b_1$ and $b_2$. Written in the new basis, what are their coordinates? So what matrix is $A$, described with $b_1$ and $b_2$?
`);
    md(r`
> [!intuition] In its own basis a matrix is simple
> In the basis of its eigenvectors, $A$ sends $b_1$ to $3b_1$, coordinates $(3, 0)$, and $b_2$ to itself, $(0, 1)$: described with them, $A$ is the diagonal matrix $\begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$, a stretch by $3$ along $u$'s line and none along $w$'s. That is what the scene showed and what the columns $(2, 1)$ and $(1, 2)$ hid; even $\det A = 3$ is the product of the two stretches. Choosing the basis well is most of understanding a matrix.
`);
    ex("rref([1, 1, 3; 1, -1, 1])", r`Find the coordinates of $v = (3, 1)$ in the basis $b_1 = (1, 1)$, $b_2 = (1, -1)$: reduce the augmented matrix, and give the reduced matrix.`, [
      r`The augmented matrix has $b_1$ and $b_2$ as columns, then $v$: ‹[1, 1, 3; 1, -1, 1]›.`,
      r`The coordinates are the last column of the reduced matrix.`,
    ]);
    ex("[2, 1; 1, 2]*[1; -1]", r`Apply $A = \begin{pmatrix} 2 & 1 \\ 1 & 2 \end{pmatrix}$ to $(1, -1)$, as a column. Then compare: is $(1, -1)$ an eigenvector, and with which eigenvalue?`, [r`Compare the answer with $(1, -1)$ itself.`]);
    ex("[3, 0; 0, 1]*[2; 5]", r`Described with its eigenvectors, $A$ is $\begin{pmatrix} 3 & 0 \\ 0 & 1 \end{pmatrix}$. The vector with coordinates $(2, 5)$ in that basis: what are the coordinates of where $A$ sends it? Answer as a column.`, [r`A diagonal matrix scales each coordinate by its own entry.`], { hide: true });
    ex("expand(det([0, -1; 1, 0] - x*[1, 0; 0, 1]))", r`Invent it: the quarter turn $R = \begin{pmatrix} 0 & -1 \\ 1 & 0 \end{pmatrix}$ of lesson 2 turns every arrow, so it should have no eigenvectors. Give $\det(R - xI)$, expanded, and see why it has no real roots.`, [
      r`$R - xI = \begin{pmatrix} -x & -1 \\ 1 & -x \end{pmatrix}$.`,
      r`Its determinant is $(-x)(-x) - (-1) \cdot 1$.`,
    ], { hide: true });
    md(r`
> [!summary]
> Any two arrows not on one line are a basis, and give every vector coordinates. The matrix $P$ whose columns they are turns those coordinates into ours, and elimination turns ours into them. An eigenvector is an arrow a matrix only stretches, by its eigenvalue, a root of $\det(A - \lambda I)$. Described with a basis of eigenvectors, the matrix is diagonal: a stretch along each. Not every matrix has one: a quarter turn turns every arrow.
`);
  });
});

// ---------------------------------------------------------------------------------------------------
// λ-calculus I and II. The Lean of each course is one development, grown lesson by lesson (a Lean
// prelude): an interpreter for the untyped calculus, then a typed calculus, a typed language and its
// safety proof. After "A Programmer's Guide to Lambda Calculus", whose Lean the first course follows.
course("lambda", "λ-calculus I: computing with functions",
  "What if functions were the only thing? Terms, free and bound variables, substitution without capture, β-reduction and normal forms, evaluation strategies, de Bruijn indices, Church encodings and recursion by fixed points; an interpreter built in Lean alongside.",
  "Logic and computation", (add) => {

  add("01-terms.chalk", "Terms and notation", "A language with nothing but functions: variables, functions and applications, how they are written, and a first β-step.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Terms and notation");
    md(r`
> [!goal]
> Read and write λ-terms, and take a first step of computation with them.
`);
    md(r`What if functions were the only thing? No numbers, no booleans, no loops, no data: only functions, which take a function and give back a function. It sounds too little to compute anything with. This course shows it is enough: by lesson 7 these functions count, add and choose, and by lesson 8 they loop. First, what would such programs look like?`);
    sec("Functions without names");
    md(r`Start from a function you know, $f(x) = x + 1$. The name $f$ is not needed to say what it does: write $x \mapsto x + 1$, or in Church's notation $\lambda x.\, x + 1$. Now take away $+$ and $1$, since there are only functions. Three things are left to write:`);
    md(r`
> [!definition] λ-terms
> A **term** is one of three things: a **variable** $x$; a **function** (an abstraction) $\lambda x.\, M$, which takes $x$ and gives $M$; or an **application** $M\ N$, the function $M$ applied to the argument $N$, written side by side with no brackets round the argument. Nothing else: everything else will be built from these three.
`);
    md(r`Type λ as ‹\lam› then space, or a backslash: ‹\x. x› is $\lambda x.\, x$.`);
    sec("Two arguments, and the parentheses");
    md(r`
> [!try]
> Every function here takes one argument. How would you write a function of two, such as $(x, y) \mapsto x$?
`);
    md(r`Take $x$ and give back a function that takes $y$: $\lambda x.\, \lambda y.\, x$. Giving it $a$ and then $b$ is $((\lambda x.\, \lambda y.\, x)\ a)\ b$. Functions returning functions are everywhere, so three conventions keep the parentheses down:

- application groups to the left: $f\ a\ b$ is $(f\ a)\ b$, the arguments taken one at a time;
- a λ's body reaches as far right as it can: $\lambda x.\, f\ x$ is $\lambda x.\, (f\ x)$, not $(\lambda x.\, f)\ x$;
- $\lambda x\ y.\, M$ is short for $\lambda x.\, \lambda y.\, M$.

A cell with only a term prints it back with as few parentheses as these rules allow (the reading beside the first is a preview of lesson 7):`);
    m("(λx. (λy. (x y)))");
    m("λx y z. x z (y z)");
    sec("A first β-step");
    md(r`With nothing but functions, the only thing that can happen is a function meeting its argument. What should $(\lambda x.\, M)\ N$ become? What $f(3)$ becomes for $f(x) = x + 1$: the body, with the argument put in for the parameter.`);
    md(r`
> [!definition] β-reduction
> A **redex** is a function applied to an argument, $(\lambda x.\, M)\ N$. It **reduces** to $M[x := N]$: the body with $N$ put in for every $x$. One such step is a **β-step**.
`);
    m("(λx. x) y", { work: true });
    md(r`
> [!try]
> $\lambda x.\, \lambda y.\, x$ takes two arguments. Which one does it give back? Predict $(\lambda x.\, \lambda y.\, x)\ a\ b$, then step through it.
`);
    m("(λx. λy. x) a b", { step: 0 });
    md(r`Application groups left, so here the identity is applied to $\lambda y.\, y$ first, and the result to $z$:`);
    m("(λx. x) (λy. y) z", { step: 0 });
    md(r`A redex can sit inside a function body; the engine reduces it there too (which redex goes first is lesson 5's question):`);
    m("λx. (λy. y) x", { work: true });
    sec("In Lean");
    md(r`This course builds an interpreter for the λ-calculus in Lean, a piece per lesson; each lesson's Lean sees the Lean of the lessons before it. First the terms: an inductive type with one constructor per kind of term.`);
    lean(r`/-- λ-terms with named variables: a variable, a function λx. body, an application f a. -/
inductive Term where
  | var : String → Term
  | lam : String → Term → Term
  | app : Term → Term → Term
  deriving Repr, DecidableEq, Inhabited

namespace Term

/-- Fully parenthesized, so the structure is plain. -/
def pretty : Term → String
  | var x => x
  | lam x b => s!"(λ{x}. {b.pretty})"
  | app f a => s!"({f.pretty} {a.pretty})"

def I : Term := lam "x" (var "x")
def K : Term := lam "x" (lam "y" (var "x"))
def ω : Term := lam "x" (app (var "x") (var "x"))

#eval (app K I).pretty

/-- The number of nodes: variables, λs and applications. -/
def size : Term → Nat
  | var _ => 1
  | lam _ b => 1 + b.size
  | app f a => 1 + f.size + a.size

end Term
open Term

example : K.size = 3 := rfl`);
    lx(`theorem size_pos (t : Term) : 0 < t.size := by`, r`Every term has at least one node. Prove it.`, `  cases t <;> simp [Term.size] <;> omega`, [
      r`Split into the three kinds of term with ‹cases t›.`,
      r`‹simp [Term.size]› unfolds the size; ‹omega› finishes the arithmetic. Combine them with ‹<;>›.`,
    ]);
    sec("Exercises");
    md(r`Reduce until no redex is left, and write the result. Answers are compared up to the names of bound variables, so $\lambda a.\, a$ is as good as $\lambda x.\, x$; an answer that still has a redex in it is sent back.`);
    ex("(λx. λy. y) a b", r`Reduce $(\lambda x.\, \lambda y.\, y)\ a\ b$.`, [r`Application groups left: first $(\lambda x.\, \lambda y.\, y)\ a$, which throws $a$ away.`]);
    ex("(λf. f a) (λx. x)", r`Reduce $(\lambda f.\, f\ a)\ (\lambda x.\, x)$.`, [r`Put $\lambda x.\, x$ for $f$, then reduce again.`]);
    ex("(λx. x x) (λy. y)", r`Reduce $(\lambda x.\, x\ x)\ (\lambda y.\, y)$.`, [r`$x$ is replaced by $\lambda y.\, y$ twice: $(\lambda y.\, y)\ (\lambda y.\, y)$.`]);
    ex("λf. λx. f (f x)", r`Write a function that takes $f$ and then $x$, and applies $f$ to $x$ twice.`, [
      r`Two parameters: $\lambda f.\, \lambda x.\, \ldots$`,
      r`Applying $f$ twice is $f\ (f\ x)$.`,
    ], { hide: true });
    md(r`
> [!summary]
> Terms are variables, functions and applications. A function of two arguments is a function returning a function, so application groups left; a λ reaches right. Computation is the β-step: a function applied to an argument becomes its body, with the argument put in.

In $\lambda x.\, x\ y$, the $x$ is the function's own. Where does $y$ come from? Lesson 2 sorts the variables a function owns from those it does not.
`);
  });

  add("02-free-bound.chalk", "Free and bound variables", "Placeholders and outside values: which variables a λ binds, which are free, and why the names of bound ones do not matter.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Free and bound variables");
    md(r`
> [!goal]
> Tell the variables a λ owns from the ones it does not, and see when renaming one is harmless.
`);
    md(r`What does $\lambda x.\, x\ y$ do? Given $a$ it gives $a\ y$. The $x$ is a placeholder for the argument. The $y$ is something else: a value from outside the function, which this term does not fix. Mathematics has the same two roles: in $\sum_{i=1}^{n} i\,k$ and $\int_0^1 x\,t\ dx$, the $i$ and the $x$ are placeholders, and $n$, $k$ and $t$ come from outside.`);
    md(r`
> [!try]
> $\sum_{j=1}^{n} j\,k$ means the same as $\sum_{i=1}^{n} i\,k$; renaming $k$ changes the meaning. In $\lambda x.\, x\ y$, which of $x$ and $y$ could you rename without changing what the function does?
`);
    sec("Bound and free");
    md(r`The answer is $x$: the λ owns it, and renaming it together with the λ changes nothing. The $y$ belongs to whoever supplies it.`);
    md(r`
> [!definition] Free and bound
> In $\lambda x.\, M$ the λ **binds** $x$: every $x$ in $M$ (not under another $\lambda x$) refers to it. An occurrence of a variable is **bound** when some λ above it has its name, and **free** otherwise. The free variables:
> $$FV(x) = \{x\}, \quad FV(\lambda x.\, M) = FV(M) \setminus \{x\}, \quad FV(M\ N) = FV(M) \cup FV(N).$$
> A term with no free variables is **closed**, a **combinator**.
`);
    md(r`Each clause says one thing: a variable alone is free; a λ takes its own variable out; an application has the free variables of both sides. The command ‹fv:› computes them and names the bound ones:`);
    m("fv: λx. x y", { work: true });
    md(r`The same name can be free in one place and bound in another. Here $x$ is bound on the left and free on the right, and $y$ the other way round, so both are listed as free and as bound:`);
    m("fv: (λx. x y) (λy. x y)");
    m("fv: λf. λx. f (f x)");
    sec("Renaming placeholders");
    md(r`So $\lambda x.\, x$ and $\lambda y.\, y$ are the same function: both give back what they get. Renaming a bound variable, everywhere it is bound, changes nothing. Now try it on $\lambda x.\, y$, the function that ignores its argument and gives $y$. Rename $x$ to $y$ and you get $\lambda y.\, y$, the identity: the new name caught the free $y$.`);
    md(r`
> [!definition] α-equivalence
> Renaming a bound variable, together with every occurrence it binds, to a name not free in its body gives the same function. Terms that differ only so are **α-equivalent**, and are treated as equal: $\lambda x.\, x$ and $\lambda y.\, y$ are, $\lambda x.\, y$ and $\lambda y.\, y$ are not.
`);
    md(r`‹alpha: s, t› decides it, by comparing the terms with their bound names removed (lesson 6 shows how):`);
    m("alpha: λx. λy. x y, λa. λb. a b", { work: true });
    m("alpha: λx. y, λy. y");
    md(r`Keep the failure in mind: lesson 3 meets it again, in the middle of a β-step.`);
    sec("In Lean");
    md(r`Free variables follow the definition clause by clause.`);
    lean(r`/-- The free variables: FV(x) = {x}, FV(λx. b) = FV(b) \ {x}, FV(f a) = FV(f) ∪ FV(a). -/
def freeVars : Term → List String
  | var x => [x]
  | lam x b => (freeVars b).filter (· != x)
  | app f a => freeVars f ++ freeVars a

#eval freeVars (lam "x" (app (var "x") (var "y")))
#eval freeVars K

/-- A term is closed (a combinator) when it has no free variables. -/
def closed (t : Term) : Bool := (freeVars t).isEmpty

example : closed K = true := by decide
example : closed (lam "x" (var "y")) = false := by decide`);
    lx(`theorem freeVars_lam_self (x : String) (b : Term) : x ∉ freeVars (lam x b) := by`, r`A λ binds its own variable: $x$ is never free in $\lambda x.\, b$.`, `  simp [freeVars]`, [
      r`Unfold ‹freeVars›: what does ‹filter (· != x)› leave out?`,
      r`‹simp [freeVars]› does it.`,
    ]);
    sec("Exercises");
    md(r`Answer ‹fv› questions with a set, like ‹{a, b}› (‹{}› for none), and ‹alpha› questions with ‹true› or ‹false›.`);
    ex("fv: λx. x y (λy. y z)", r`Which variables are free in $\lambda x.\, x\ y\ (\lambda y.\, y\ z)$?`, [r`The $y$ inside $\lambda y$ is bound there; the first $y$ is not under it.`]);
    ex("fv: (λx. λy. x) y", r`Which variables are free in $(\lambda x.\, \lambda y.\, x)\ y$?`, [r`The last $y$ is the argument, outside both λs.`]);
    ex("alpha: λx. λy. y x, λy. λx. x y", r`Are $\lambda x.\, \lambda y.\, y\ x$ and $\lambda y.\, \lambda x.\, x\ y$ α-equivalent?`, [r`Both take two arguments and apply the second to the first.`]);
    ex("alpha: λx. x y, λy. y y", r`Are $\lambda x.\, x\ y$ and $\lambda y.\, y\ y$ α-equivalent?`, [r`Renaming $x$ to $y$ would capture the free $y$.`]);
    md(r`
> [!summary]
> A λ binds its variable in its body; every other variable is free, a value from outside. Bound names can be changed at will, as long as no free variable gets captured. That is α-equivalence, and terms are equal up to it.

A β-step puts an argument into a body. What if the argument has a free $y$ and the body has a $\lambda y$? Lesson 3.
`);
  });

  add("03-substitution.chalk", "Substitution and capture", "The obvious substitution, two ways it goes wrong, and the renaming that fixes it.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Substitution and capture");
    md(r`
> [!goal]
> Find the rule for $M[x := N]$, the substitution a β-step does, by repairing the obvious rule where it fails.
`);
    md(r`A β-step turns $(\lambda x.\, M)\ N$ into "$M$ with $N$ put in for $x$". Writing that out looks like a formality: replace every $x$ in $M$ by $N$. It is not, and seeing why is the whole lesson.`);
    sec("Two ways the obvious rule fails");
    md(r`First failure: $((\lambda x.\, x)\ x)[x := y]$. Replacing every $x$ gives $(\lambda y.\, y)\ y$. But the $x$ in $\lambda x.\, x$ belongs to its own λ (lesson 2); only the last $x$ is free, so the answer is $(\lambda x.\, x)\ y$. Repair: replace only **free** occurrences, and stop at a λ that binds $x$ again. ‹subst: M, x := N› does it:`);
    m("subst: x y, x := λz. z", { work: true });
    m("subst: λx. x y, x := z", { work: true });
    md(r`Second failure, subtler. $\lambda y.\, x$ ignores its argument and gives $x$. Put $y$ in for $x$ with the repaired rule: $(\lambda y.\, x)[x := y] = \lambda y.\, y$, the identity.`);
    md(r`
> [!try]
> Predict both before running them. $(\lambda x.\, \lambda y.\, x)\ y\ a$ gives $y$ and then $a$ to a function that keeps its first argument. $(\lambda y.\, y)\ a$ is where the step $(\lambda y.\, x)[x := y] = \lambda y.\, y$ would lead.
`);
    m("(λx. λy. x) y a");
    m("(λy. y) a");
    md(r`The function keeps its first argument, $y$; the naive step led to $a$. The $y$ put in was free, a value from outside, but it landed under a $\lambda y$ and now means the parameter: it has been **captured**.`);
    md(r`
> [!try]
> How would you repair it? Lesson 2 has the tool.
`);
    md(r`The name of a bound variable does not matter, so move it out of the way first. $\lambda y.\, x$ is the same function as $\lambda y'.\, x$, and $(\lambda y'.\, x)[x := y] = \lambda y'.\, y$: a function that ignores its argument and gives $y$, as it should. The new name must be **fresh**: free neither in what is put in nor in the body.`);
    md(r`
> [!definition] Substitution
> $M[x := N]$ replaces the free occurrences of $x$ in $M$ by $N$:
> - $x[x := N] = N$, and $y[x := N] = y$ for another variable $y$;
> - $(M_1\ M_2)[x := N] = M_1[x := N]\ M_2[x := N]$;
> - $(\lambda x.\, M)[x := N] = \lambda x.\, M$: here $x$ is bound, so there is nothing to replace (the first repair);
> - $(\lambda y.\, M)[x := N] = \lambda y.\, M[x := N]$ when $y$ is not free in $N$;
> - otherwise rename $y$ first, to a fresh $z$: $\lambda z.\, M[y := z][x := N]$ (the second).
`);
    md(r`The engine does the renaming as its own step:`);
    m("subst: λy. x y, x := y", { work: true });
    m("subst: λy. λx. x y z, z := x y", { work: true });
    md(r`A β-step is a substitution, so it renames too:`);
    m("(λx. λy. x y) y", { work: true });
    sec("In Lean");
    md(r`The obvious substitution first, with the first repair. It captures:`);
    lean(r`/-- Substitution as it first comes to mind: put s for every free x, stopping under a binder named x. -/
def substNaive (x : String) (s : Term) : Term → Term
  | var y => if y = x then s else var y
  | lam y b => if y = x then lam y b else lam y (substNaive x s b)
  | app f a => app (substNaive x s f) (substNaive x s a)

-- (λy. x)[x := y] should ignore its argument and return the free y
#eval (substNaive "x" (var "y") (lam "y" (var "x"))).pretty`);
    lx(`theorem substNaive_self (x : String) (t : Term) : substNaive x (var x) t = t := by`, r`Substituting a variable for itself changes nothing. Prove it by induction on the term.`, `  induction t with
  | var y => by_cases h : y = x <;> simp [substNaive, h]
  | lam y b ih => by_cases h : y = x <;> simp [substNaive, h, ih]
  | app f a ihf iha => simp [substNaive, ihf, iha]`, [
      r`‹induction t with› gives a case per constructor, with induction hypotheses for the subterms.`,
      r`In the ‹var› and ‹lam› cases, split on ‹y = x› with ‹by_cases h : y = x›, then ‹simp [substNaive, h]› (add ‹ih› where there is one).`,
    ]);
    md(r`The real one renames. Renaming $y$ to $z$ is done with the naive substitution, so $z$ must avoid every name in the body, bound ones too: a $\lambda z$ inside would capture it. And its recursive call is on a renamed body, which is not a subterm, so Lean cannot see on its own that it stops: we say why (renaming keeps the size) and Lean checks it.`);
    lean(r`/-- A name not in avoid: x, x', x'', … (avoid is finite, so one of the first length + 1 is free). -/
def fresh (avoid : List String) (x : String) : String :=
  go x avoid.length
where
  go (c : String) : Nat → String
    | 0 => c
    | n + 1 => if c ∈ avoid then go (c ++ "'") n else c

/-- Every name in a term, bound or free. -/
def allVars : Term → List String
  | var x => [x]
  | lam x b => x :: allVars b
  | app f a => allVars f ++ allVars a

/-- Rename the variable y to z. -/
def rename (y z : String) (b : Term) : Term := substNaive y (var z) b

/-- Renaming keeps the size: the measure capture-avoiding substitution recurses on. -/
theorem size_rename (y z : String) (t : Term) : (rename y z t).size = t.size := by
  induction t with
  | var w => by_cases h : w = y <;> simp [rename, substNaive, h, Term.size]
  | lam w b ih => by_cases h : w = y <;> simp_all [rename, substNaive, Term.size]
  | app f a ihf iha => simp_all [rename, substNaive, Term.size]

/-- Capture-avoiding substitution t[x := s]. -/
def subst (x : String) (s : Term) : Term → Term
  | var y => if y = x then s else var y
  | app f a => app (subst x s f) (subst x s a)
  | lam y b =>
    if y = x then lam y b
    else if y ∈ freeVars s then
      let z := fresh (freeVars s ++ allVars b ++ [x]) y
      lam z (subst x s (rename y z b))
    else lam y (subst x s b)
termination_by t => t.size
decreasing_by all_goals simp_wf <;> simp [size_rename, Term.size] <;> omega

#eval (subst "x" (var "y") (lam "y" (var "x"))).pretty
-- the body binds y', so the fresh name is y''
#eval (subst "x" (var "y") (lam "y" (lam "y'" (app (var "x") (var "y"))))).pretty`);
    sec("Exercises");
    md(r`A ‹subst› answer is compared with the result up to the names of bound variables, and is not reduced: write the term the substitution gives.`);
    ex("subst: x (λx. x y), x := y", r`Compute $(x\ (\lambda x.\, x\ y))[x := y]$.`, [r`Only the first $x$ is free; the λ binds the others.`]);
    ex("subst: λz. x z, x := z", r`Compute $(\lambda z.\, x\ z)[x := z]$.`, [r`The binder $z$ would capture the $z$ put in: rename it first.`]);
    ex("subst: λy. x, x := λw. w", r`Compute $(\lambda y.\, x)[x := \lambda w.\, w]$.`, [r`$\lambda w.\, w$ has no free variables, so nothing can be captured.`]);
    ex("(λx. λy. y x) y", r`Reduce $(\lambda x.\, \lambda y.\, y\ x)\ y$ to normal form, with the renaming you invented.`, [r`The $y$ passed in is free; the $\lambda y$ would capture it. Rename the binder, say to $z$, first.`]);
    md(r`
> [!summary]
> Substitution replaces free occurrences only, and renames a binder that would capture a free variable of what is put in. Both rules come from the obvious rule failing, and together they are the whole of β-reduction's work.

With substitution settled, β-steps can be chained. Does the chain always end, and does it matter which redex goes first? Lesson 4.
`);
  });

  add("04-beta.chalk", "β-reduction and normal forms", "Chaining β-steps: where it stops, terms that never stop, why the order of steps cannot change the answer, and η.", ({ sec, md, m, ex, lean, lx }) => {
    sec("β-reduction and normal forms");
    md(r`
> [!goal]
> Reduce terms to normal form, meet terms that have none, and see why the order of the steps can decide whether you finish but never where.
`);
    md(r`Keep taking β-steps, and three questions come up at once. Does it stop? If it stops, is the end the same whichever redex you pick each time? And can the choice decide whether it stops at all?`);
    sec("Where it stops");
    md(r`
> [!definition] Normal form
> A term with no redex is in **normal form**: it cannot take a step, and it is the term's answer. A term **has** a normal form when some sequence of β-steps reaches one.
`);
    m("(λx. λy. y x) a (λz. z)", { step: 0 });
    md(r`‹S›, ‹K› and ‹I› are library combinators, unfolded in one δ-step: $S = \lambda x\ y\ z.\, x\ z\ (y\ z)$, $K = \lambda x\ y.\, x$, $I = \lambda x.\, x$. $S\ K\ K$ turns out to be the identity:`);
    m("S K K a", { work: true });
    sec("Terms that never stop");
    md(r`A β-step uses up a λ, but it also copies the argument once for each use of the parameter. So look for a term that, applied to itself, makes a copy of itself.`);
    md(r`
> [!try]
> $\omega = \lambda x.\, x\ x$ applies its argument to itself. What is $\omega\ \omega$ after one step?
`);
    md(r`The library calls $\omega$ ‹omega›. A step count after the strategy's name shows that many steps instead of refusing:`);
    m("normal 2: omega omega", { work: true });
    md(r`$\Omega = \omega\ \omega$ steps to itself, for ever. The engine gives up:`);
    m("omega omega");
    md(r`Triple instead of double, and the term grows as it goes, until the engine stops it:`);
    m("(λx. x x x) (λx. x x x)");
    sec("Does the order matter?");
    md(r`$(\lambda x.\, \lambda y.\, y)\ \Omega$ has two redexes: the whole term, and $\Omega$ inside it. Reduce $\Omega$ and you are back where you started, for ever. Reduce the outer one and $\Omega$ is thrown away, since $x$ is not used:`);
    m("normal: (λx. λy. y) (omega omega)", { work: true });
    md(r`So the order can decide **whether** you reach a normal form. Can it decide **which**? Take a term where both paths finish: $(\lambda x.\, x\ x)\ ((\lambda y.\, y)\ z)$. Outer redex first copies the inner redex and reduces it twice; inner first (‹applicative:›, lesson 5) reduces it once and copies the result.`);
    md(r`
> [!try]
> Predict both answers, and which path is shorter.
`);
    m("normal: (λx. x x) ((λy. y) z)", { work: true });
    m("applicative: (λx. x x) ((λy. y) z)", { work: true });
    md(r`Three steps one way, two the other, and the same end. That is no accident:`);
    md(r`
> [!theorem] Church–Rosser
> If $M$ reduces to $N_1$ and to $N_2$ (each in any number of steps), then $N_1$ and $N_2$ both reduce to some common $P$. So a term has **at most one** normal form, up to α: the order of the steps can change whether you get there, never where.
`);
    md(r`That is why a λ-term has a meaning, and why an exercise can compare normal forms.`);
    sec("η");
    md(r`$\lambda x.\, f\ x$ and $f$ are different terms, both in normal form. Yet applied to any $a$, both give $f\ a$. Should they count as equal?`);
    md(r`
> [!definition] η-reduction
> $\lambda x.\, f\ x$ reduces to $f$ when $x$ is not free in $f$. Adding this rule says that a function is determined by what it does (**extensionality**).
`);
    m("eta: λx. λy. f x y", { work: true });
    m("eta: λx. x x");
    md(r`$\lambda x.\, x\ x$ is not an η-redex: $x$ is free in the function part, so dropping the λ would change what $x$ means.`);
    sec("In Lean");
    md(r`A step contracts the leftmost-outermost redex; evaluation takes steps on fuel, because some terms never stop.`);
    lean(r`/-- One normal-order step: contract the leftmost-outermost redex, if there is one. -/
def betaStep : Term → Option Term
  | app (lam x b) a => some (subst x a b)
  | app f a =>
    match betaStep f with
    | some f' => some (app f' a)
    | none => (betaStep a).map (app f ·)
  | lam x b => (betaStep b).map (lam x ·)
  | var _ => none

/-- Take up to fuel steps. -/
def eval : Nat → Term → Term
  | 0, t => t
  | n + 1, t =>
    match betaStep t with
    | none => t
    | some t' => eval n t'

#eval (eval 10 (app (app K (var "a")) (var "b"))).pretty
#eval (eval 3 (app ω ω)).pretty`);
    lx(`theorem eval_normal (t : Term) (h : betaStep t = none) : ∀ n, eval n t = t := by`, r`A normal form stays put: evaluating it, with any fuel, gives it back.`, `  intro n
  cases n <;> simp [eval, h]`, [r`Introduce ‹n› and split ‹cases n›: no fuel, or some.`, r`‹simp [eval, h]› settles both.`]);
    sec("Exercises");
    ex("(λx. λy. x) y", r`Reduce $(\lambda x.\, \lambda y.\, x)\ y$ to normal form. (The trap: $\lambda y.\, y$ is wrong.)`, [r`Rename the inner binder first, say to $z$: $\lambda z.\, y$.`], { hide: true });
    ex("(λf. λx. f (f x)) (λy. y y)", r`Reduce $(\lambda f.\, \lambda x.\, f\ (f\ x))\ (\lambda y.\, y\ y)$ to normal form.`, [r`After the first step: $\lambda x.\, (\lambda y.\, y\ y)\ ((\lambda y.\, y\ y)\ x)$. Normal order then reduces the outer redex.`]);
    ex("(λx. λy. x) (λz. z) (omega omega)", r`$(\lambda x.\, \lambda y.\, x)\ (\lambda z.\, z)\ \Omega$ has a normal form. Choose your redexes well and find it.`, [r`Never touch $\Omega$: the function throws its second argument away.`]);
    ex("eta: λx. (λy. g y) x", r`Reduce $\lambda x.\, (\lambda y.\, g\ y)\ x$ with β and η.`, [r`$\lambda y.\, g\ y$ is an η-redex.`]);
    md(r`
> [!summary]
> A normal form is a term with no redex. Some terms have none, and some reach one only along the right path. By Church–Rosser a term has at most one normal form, so the order of steps decides whether you get there, never where. η adds extensionality: $\lambda x.\, f\ x$ is $f$.

If the order can decide whether we finish, which order should an interpreter use? Lesson 5.
`);
  });

  add("05-strategies.chalk", "Evaluation strategies", "Which redex first: normal order, call by name, call by value, applicative order, and a term where the choice decides whether you finish.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Evaluation strategies");
    md(r`
> [!goal]
> Compare the classic answers to "which redex first?": what each finds, where each stops, and what each costs.
`);
    md(r`An interpreter has to pick a redex by a fixed rule. Two rules come to mind, and every programming language picks one: evaluate the argument before the call, as $f(g(x))$ does in most languages; or hand the argument over as it is, and evaluate it only where it is used.`);
    md(r`
> [!try]
> $K = \lambda x.\, \lambda y.\, x$ throws its second argument away. Under each rule, what happens to $K\ I\ \Omega$?
`);
    sec("A term where the choice decides");
    md(r`Hand arguments over as they are, and $\Omega$ is never touched:`);
    m("normal: K I (omega omega)", { work: true });
    m("cbn: K I (omega omega)");
    md(r`Evaluate arguments first, and you never get past it. A step count shows how it goes round:`);
    m("cbv 4: K I (omega omega)", { work: true });
    m("applicative: K I (omega omega)");
    md(r`Normal order is the safe choice, always:`);
    md(r`
> [!theorem] Standardization
> If a term has a normal form, normal order reaches it.
`);
    md(r`The four classic strategies are the two rules, each with and without reducing inside a function body:`);
    md(r`
> [!definition] Strategies
> - **Normal order** (‹normal:›): the leftmost-outermost redex, also under λ, to the normal form.
> - **Call by name** (‹cbn:›): the leftmost-outermost redex, never under a λ, the argument passed unevaluated. It stops at a **weak head normal form**: a λ, or a variable applied to arguments.
> - **Call by value** (‹cbv:›): the function, then the argument, are reduced to **values** (a λ or a variable) before the call; never under a λ.
> - **Applicative order** (‹applicative:›): the leftmost-innermost redex, under λ too: call by value that goes all the way.
`);
    sec("Where they stop");
    md(r`Call by name and call by value do not look inside a λ: a function is already a result, and its body runs when it is called.`);
    m("cbn: λx. (λy. y) x");
    m("cbv: (λx. x) (λy. (λz. z) y)");
    sec("What they cost");
    md(r`
> [!try]
> In $(\lambda x.\, x\ x)\ ((\lambda y.\, y)\ z)$ the argument is used twice. Call by name copies it unevaluated; call by value evaluates it first. Predict where each stops.
`);
    m("cbn: (λx. x x) ((λy. y) z)", { work: true });
    m("cbv: (λx. x x) ((λy. y) z)", { work: true });
    md(r`Call by value did the argument's step once, first. Call by name copied the unevaluated argument, and stopped at $z\ ((\lambda y.\, y)\ z)$, a weak head normal form; normal order goes on into the copies and does the same step twice (lesson 4). Most languages call by value; Haskell calls by **need**: call by name that remembers an argument once it is evaluated, so it is done at most once, and never if unused.`);
    sec("In Lean");
    lean(r`/-- Call by value treats variables and λs as values. -/
def isValue : Term → Bool
  | app _ _ => false
  | _ => true

/-- One call-by-value step: the function, then the argument, become values before the call; never under a λ. -/
def cbvStep : Term → Option Term
  | app (lam x b) a =>
    if isValue a then some (subst x a b)
    else (cbvStep a).map (app (lam x b) ·)
  | app f a =>
    match cbvStep f with
    | some f' => some (app f' a)
    | none => (cbvStep a).map (app f ·)
  | _ => none

/-- Take up to fuel steps with any strategy. -/
def run (step : Term → Option Term) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => match step t with
    | none => t
    | some t' => run step n t'

def KIΩ : Term := app (app K I) (app ω ω)
#eval (run betaStep 10 KIΩ).pretty   -- normal order: I
#eval (run cbvStep 10 KIΩ).pretty    -- call by value: still evaluating Ω`);
    lx(`theorem cbvStep_lam (x : String) (b : Term) : cbvStep (lam x b) = none := by`, r`Call by value does not reduce under a λ: a function takes no step.`, `  simp [cbvStep]`, [r`Unfold ‹cbvStep›: which clause does ‹lam x b› match?`]);
    sec("Exercises");
    md(r`Write the term the strategy stops at; it is compared up to bound names, not reduced further.`);
    ex("cbv: (λx. λy. y) ((λz. z) w)", r`Reduce $(\lambda x.\, \lambda y.\, y)\ ((\lambda z.\, z)\ w)$ by value.`, [r`The argument is reduced first, to $w$; then the call.`]);
    ex("cbn: (λx. λy. x) ((λz. z) w)", r`Reduce $(\lambda x.\, \lambda y.\, x)\ ((\lambda z.\, z)\ w)$ by name. Is the argument ever evaluated?`, [r`The argument goes in unevaluated, under $\lambda y$, where call by name does not look.`]);
    ex("cbn: (λx. x x) ((λy. y) z)", r`Reduce $(\lambda x.\, x\ x)\ ((\lambda y.\, y)\ z)$ by name. Where does it stop?`, [r`The argument goes in unevaluated, twice. Then the head is reduced, and only the head.`]);
    ex("cbn: λx. (λy. y) x", r`Reduce $\lambda x.\, (\lambda y.\, y)\ x$ by name.`, [r`Call by name does not reduce under a λ.`]);
    md(r`
> [!summary]
> A strategy answers "which redex first?". Normal order finds every normal form there is. Call by name and call by value stop at functions; call by value evaluates arguments first, once, and can loop on an argument nobody needs.

Every strategy here renames bound variables to substitute, and lesson 2 had to compare terms up to renaming. Names are a nuisance: can we do without them? Lesson 6.
`);
  });

  add("06-de-bruijn.chalk", "De Bruijn indices", "Terms without bound names: point at a variable's binder by counting λs, and α-equivalence becomes equality.", ({ sec, md, m, ex, lean, lx }) => {
    sec("De Bruijn indices");
    md(r`
> [!goal]
> Write terms without bound names, so that α-equivalent terms are literally equal.
`);
    md(r`Names have cost us twice: substitution must rename to avoid capture (lesson 3), and $\lambda x.\, \lambda y.\, x$ and $\lambda a.\, \lambda b.\, a$ are one function with two spellings (lesson 2). Could every function have just one?`);
    md(r`
> [!try]
> What does a bound variable tell you? Only which λ it belongs to. How could you say that without a name?
`);
    sec("Counting instead of naming");
    md(r`Point at the binder by counting: replace each bound variable by how many λs it must step out past to reach its binder, $0$ for the nearest. The λs no longer need names. In $\lambda x.\, \lambda y.\, x$, the $x$ steps out past $\lambda y$ to reach $\lambda x$: one. So the term is $\lambda.\, \lambda.\, 1$, and so is $\lambda a.\, \lambda b.\, a$.`);
    md(r`
> [!definition] De Bruijn indices
> Replace each bound variable by the number of λs between it and its binder: $0$ for the nearest. The λs lose their names. A free variable keeps its name.
`);
    m("db: λx. λy. x", { work: true });
    md(r`
> [!try]
> Work out $\lambda f.\, \lambda x.\, f\ (f\ x)$ and $\lambda x.\, \lambda y.\, x\ (\lambda z.\, z\ y)$ before running them.
`);
    m("db: λf. λx. f (f x)");
    m("db: λx. λy. x (λz. z y)");
    md(r`An index counts from where the variable stands, so it is not a label: the same variable gets different numbers at different depths, and different variables can share one.`);
    m("db: λx. x (λy. x)");
    m("db: λx. x (λy. y)");
    sec("α-equivalence is equality");
    md(r`Two terms are α-equivalent exactly when their de Bruijn forms are equal: there are no bound names left to differ. That is how ‹alpha:› decides.`);
    m("alpha: λx. λy. x (λz. z y), λa. λb. a (λc. c b)", { work: true });
    md(r`The View menu's de Bruijn indices shows every λ-cell's result, and every step, this way.`);
    sec("The price: shifting");
    md(r`Without names nothing can be captured, so substitution never renames. It has its own bookkeeping instead. In $\lambda z.\, (\lambda x.\, \lambda y.\, x)\ z$ the β-step gives $\lambda z.\, \lambda y.\, z$. Watch the $z$:`);
    m("db: λz. (λx. λy. x) z");
    m("db: λz. λy. z");
    md(r`As an argument it was $0$; put under $\lambda y$ it is $1$, one more λ away from its binder. A term moved under a λ must have its free indices raised: **shifting**.`);
    sec("In Lean");
    md(r`An interpreter on de Bruijn terms needs no renaming and no fresh names; it shifts instead.`);
    lean(r`/-- De Bruijn terms: a bound variable is the number of λs between it and its binder. -/
inductive DB where
  | bvar : Nat → DB
  | free : String → DB
  | lam : DB → DB
  | app : DB → DB → DB
  deriving Repr, DecidableEq

/-- Translate, keeping the binders in scope innermost first. -/
def toDB (ctx : List String) : Term → DB
  | var x => match ctx.idxOf? x with
    | some i => .bvar i
    | none => .free x
  | lam x b => .lam (toDB (x :: ctx) b)
  | app f a => .app (toDB ctx f) (toDB ctx a)

/-- α-equivalence: the same term up to the names of bound variables. -/
def alphaEq (s t : Term) : Bool := toDB [] s == toDB [] t

#eval toDB [] K
example : alphaEq (lam "x" (var "x")) (lam "y" (var "y")) = true := by decide
example : alphaEq (lam "x" (var "y")) (lam "y" (var "y")) = false := by decide

/-- Shift the free indices (those ≥ c) by d. -/
def DB.shift (d : Nat) (c : Nat) : DB → DB
  | bvar n => if n ≥ c then bvar (n + d) else bvar n
  | free x => free x
  | lam b => lam (shift d (c + 1) b)
  | app f a => app (shift d c f) (shift d c a)

example : (DB.lam (.bvar 1)).shift 1 0 = .lam (.bvar 2) := by decide`);
    lx(`theorem DB.shift_zero (c : Nat) (t : DB) : t.shift 0 c = t := by`, r`Shifting by zero changes nothing. Prove it by induction; the cutoff ‹c› changes under a λ, so generalize it.`, `  induction t generalizing c with
  | bvar n => simp [DB.shift]
  | free x => rfl
  | lam b ih => simp [DB.shift, ih]
  | app f a ihf iha => simp [DB.shift, ihf, iha]`, [
      r`‹induction t generalizing c with› lets the hypothesis for the body hold at ‹c + 1›.`,
      r`Each case is ‹simp [DB.shift]›, with the induction hypotheses where there are some; ‹free› is ‹rfl›.`,
    ]);
    sec("Exercises");
    md(r`Answer with ‹true› or ‹false›; write both terms with indices first.`);
    ex("alpha: λx. λy. y (λz. x), λa. λb. b (λb. a)", r`Are $\lambda x.\, \lambda y.\, y\ (\lambda z.\, x)$ and $\lambda a.\, \lambda b.\, b\ (\lambda b.\, a)$ α-equivalent?`, [r`The inner $x$ and $a$ each step out past two λs: both are $\lambda.\, \lambda.\, 0\ (\lambda.\, 2)$.`]);
    ex("alpha: λx. λy. x, λy. λx. x", r`Are $\lambda x.\, \lambda y.\, x$ and $\lambda y.\, \lambda x.\, x$ α-equivalent?`, [r`In indices: $\lambda.\, \lambda.\, 1$ and $\lambda.\, \lambda.\, 0$.`]);
    ex("alpha: λx. x (λy. x), λa. a (λa. a)", r`Are $\lambda x.\, x\ (\lambda y.\, x)$ and $\lambda a.\, a\ (\lambda a.\, a)$ α-equivalent?`, [r`In the second, the inner $a$ belongs to the inner λ.`]);
    md(r`
> [!summary]
> De Bruijn indices point at a binder by counting the λs in between. Bound names disappear, so α-equivalent terms are equal, and substitution shifts indices instead of renaming.

Back to lesson 1's question: with only functions, where are the numbers? Lesson 7.
`);
  });

  add("07-church.chalk", "Church encodings", "A thing is what you can do with it: booleans that choose, numerals that iterate, pairs, the predecessor puzzle, and lists.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Church encodings");
    md(r`
> [!goal]
> Build booleans, numbers and pairs out of functions, by asking what each one is for.
`);
    md(r`Lesson 1 promised that functions are enough, yet there is no $\mathsf{true}$ here and no $3$. To build them, ask what you **do** with a thing, and let the thing be that doing: a thing is what you can do with it.`);
    sec("Booleans choose");
    md(r`What do you do with a boolean? Choose: "if $b$ then $x$ else $y$". So let the boolean be the chooser: $b\ x\ y$ should be $x$ when $b$ is true, and $y$ when it is false.`);
    md(r`
> [!try]
> Write $\mathsf{true}$ and $\mathsf{false}$: each takes two arguments.
`);
    md(r`
> [!definition] Church booleans
> $\mathsf{true} = \lambda t.\, \lambda f.\, t$ keeps the first, and $\mathsf{false} = \lambda t.\, \lambda f.\, f$ the second. Then $\mathsf{if}\ b\ x\ y$ is just $b\ x\ y$, and $\mathsf{not}\ b = b\ \mathsf{false}\ \mathsf{true}$.
`);
    md(r`The library has ‹true›, ‹false›, ‹if›, ‹not›, ‹and›, ‹or›. Names are unfolded in one δ-step; the result is read back when it is a boolean or a numeral.`);
    m("if true a b", { work: true });
    md(r`$\mathsf{and}\ p\ q$ is "if $p$ then $q$ else false"; the library writes the "false" as $p$, which is false in that branch: $\lambda p.\, \lambda q.\, p\ q\ p$.`);
    m("and true false");
    md(r`A definition, ‹name := term›, is there for the cells after it. Exclusive or: if $p$, the opposite of $q$, else $q$:`);
    m("xor := λp. λq. p (not q) q");
    m("xor true false");
    m("xor true true");
    md(r`$\mathsf{false}$ and $0$ (below) are the same term, $\lambda t.\, \lambda f.\, f$: the reading names it as the numeral.`);
    sec("Numerals iterate");
    md(r`What do you do with a natural number $n$? Do something $n$ times. So let $n$ be that: given $f$ and $x$, it applies $f$ to $x$, $n$ times.`);
    md(r`
> [!definition] Church numerals
> $n$ is the function that applies $f$ to $x$ $n$ times: $0 = \lambda f.\, \lambda x.\, x$, $1 = \lambda f.\, \lambda x.\, f\ x$, $2 = \lambda f.\, \lambda x.\, f\ (f\ x)$, and so on. In a λ-term a digit is its numeral.
`);
    m("λf. λx. f (f (f x))");
    md(r`
> [!try]
> Write $\mathsf{succ}$: given $n$, apply $f$ once more than $n$ does. Then $\mathsf{add}\ m\ n$: apply $f$ $n$ times, then $m$ more.
`);
    md(r`$n\ f\ x$ is $f$ applied $n$ times, so $\mathsf{succ} = \lambda n.\, \lambda f.\, \lambda x.\, f\ (n\ f\ x)$, and $\mathsf{add} = \lambda m.\, \lambda n.\, \lambda f.\, \lambda x.\, m\ f\ (n\ f\ x)$: start from $n\ f\ x$ and apply $f$ $m$ more times. ($\lambda n.\, \lambda f.\, \lambda x.\, n\ f\ (f\ x)$, one extra $f$ first instead of last, is a successor just as good.) These are the library's:`);
    m("succ 2", { work: true });
    m("add 2 3");
    md(r`Multiplying is iterating an iteration: $\mathsf{mul}\ m\ n = \lambda f.\, m\ (n\ f)$ does "$f$, $n$ times" $m$ times. And $\mathsf{pow}\ m\ n = n\ m$: $n$ copies of "do it $m$ times", composed.`);
    m("mul 2 3");
    m("pow 2 3");
    md(r`So a function that applies its argument twice is the numeral 2, and applying it to itself applies four times:`);
    m("twice := λf. λx. f (f x)");
    m("twice twice succ 0");
    sec("The predecessor: a puzzle");
    md(r`Subtracting one looks easy and is not. A numeral can apply $f$; it can never undo it. Church himself at first doubted it could be done; his student Kleene found how.`);
    md(r`
> [!try]
> How do you get $n - 1$ from something that can only go forward $n$ times? A hint: go forward, but carry where you were one step ago.
`);
    md(r`Carrying two numbers needs a pair, and a pair is what you do with it: hand both to a selector.`);
    md(r`
> [!definition] Pairs
> $\mathsf{pair}\ a\ b = \lambda s.\, s\ a\ b$ holds $a$ and $b$ until a selector comes: $\mathsf{fst}\ p = p\ \mathsf{true}$ and $\mathsf{snd}\ p = p\ \mathsf{false}$.
`);
    m("fst (pair a b)", { work: true });
    md(r`Kleene's trick: start at $(0, 0)$ and step $(a, b) \mapsto (b, b + 1)$, so $(0, 0) \to (0, 1) \to (1, 2) \to (2, 3) \to \cdots$. The first place lags one behind the second, so after $n \geq 1$ steps it holds $n - 1$; with no steps it holds $0$, which is as close as the naturals get to $0 - 1$.`);
    m("pred := λn. fst (n (λp. pair (snd p) (succ (snd p))) (pair 0 0))");
    m("pred 3");
    md(r`Subtraction is then a predecessor iterated: $\mathsf{sub}\ m\ n$ applies $\mathsf{pred}$ to $m$, $n$ times. And $\mathsf{iszero}\ n = n\ (\lambda y.\, \mathsf{false})\ \mathsf{true}$: one application of "make it false" is enough to spoil $\mathsf{true}$.`);
    m("sub := λm. λn. n pred m");
    m("sub 3 1");
    m("iszero (pred 1)");
    sec("Lists fold");
    md(r`What do you do with a list? Walk it: combine each head with the result for the rest, and say what to give for the empty list. So a list is its own fold.`);
    md(r`
> [!definition] Church lists
> Given what to do with a head and the rest ($c$) and what to give for the empty list ($n$), a list does it: $\mathsf{nil} = \lambda c.\, \lambda n.\, n$ and $\mathsf{cons}\ h\ t = \lambda c.\, \lambda n.\, c\ h\ (t\ c\ n)$, so $[1, 2]$ is $\lambda c.\, \lambda n.\, c\ 1\ (c\ 2\ n)$.
`);
    m("nil := λc. λn. n");
    m("cons := λh. λt. λc. λn. c h (t c n)");
    md(r`($\mathsf{nil}$ is $\lambda c.\, \lambda n.\, n$ again: the same term as $0$ and $\mathsf{false}$.) Folding with $\mathsf{add}$ from $0$ sums a list, and counting the heads gives its length:`);
    m("cons 1 (cons 2 nil) add 0");
    m("length := λl. l (λh. λr. succ r) 0");
    m("length (cons a (cons b (cons c nil)))");
    sec("In Lean");
    md(r`Lean is typed, so a Church numeral is used at one type at a time; inside that type it is iteration.`);
    lean(r`/-- The Church numeral n at one type: apply f to x, n times. -/
def church {α : Type} : Nat → (α → α) → α → α
  | 0, _, x => x
  | n + 1, f, x => f (church n f x)

#eval church 3 (· + 1) 0
#eval church 3 (· ++ "!") "hi"`);
    lx(`theorem church_add {α : Type} (f : α → α) (x : α) : ∀ m n, church (m + n) f x = church m f (church n f x) := by`, r`Adding numerals is composing: $m + n$ applications are $n$ and then $m$ more. Prove it by induction on $m$.`, `  intro m n
  induction m with
  | zero => simp [church]
  | succ k ih => rw [Nat.succ_add]; simp [church, ih]`, [
      r`‹intro m n›, then ‹induction m with›.`,
      r`In the successor case ‹(k + 1) + n› is not syntactically ‹(k + n) + 1›: rewrite with ‹Nat.succ_add› first, then ‹simp [church, ih]›.`,
    ]);
    sec("Exercises");
    md(r`Answer with a numeral or a boolean by name, or with the λ-term. A cell that starts with a digit is read as arithmetic, so the last two questions name their strategy, ‹normal:›.`);
    ex("pred 2", r`Reduce $\mathsf{pred}\ 2$.`, [r`Two steps of the pair counter: $(0, 0) \to (0, 1) \to (1, 2)$.`]);
    ex("or false (not false)", r`Reduce $\mathsf{or}\ \mathsf{false}\ (\mathsf{not}\ \mathsf{false})$.`, [r`$\mathsf{not}\ \mathsf{false}$ is $\mathsf{true}$.`]);
    ex("snd (pair 1 (succ 1))", r`Reduce $\mathsf{snd}\ (\mathsf{pair}\ 1\ (\mathsf{succ}\ 1))$.`, []);
    ex("cons 1 (cons 1 (cons 1 nil)) add 0", r`Sum the list $[1, 1, 1]$: reduce $\mathsf{cons}\ 1\ (\mathsf{cons}\ 1\ (\mathsf{cons}\ 1\ \mathsf{nil}))\ \mathsf{add}\ 0$.`, [r`The list puts $\mathsf{add}$ between its elements and $0$ at the end: $1 + (1 + (1 + 0))$.`]);
    ex("normal: 3 not true", r`A numeral is a loop. Reduce $3\ \mathsf{not}\ \mathsf{true}$.`, [r`It applies $\mathsf{not}$ to $\mathsf{true}$ three times.`]);
    ex("normal: 2 (add 3) 0", r`Reduce $2\ (\mathsf{add}\ 3)\ 0$. Which operation on 2 and 3 have you invented?`, [r`It applies "add 3" to 0, twice.`]);
    md(r`
> [!summary]
> A thing is what you can do with it: booleans choose, numerals iterate, pairs wait for a selector, lists are their own folds. Arithmetic is iteration of iterations, and the predecessor is a counter carried in a pair.

Every loop here is a numeral, which knows in advance how many times to run. A loop that runs until it is done needs a function that calls itself. With no names, how can a function refer to itself? Lesson 8.
`);
  });

  add("08-recursion.chalk", "Recursion and fixed points", "How a function can call itself without a name: self-application, the Y combinator derived from ω, factorial, and Z for call by value.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Recursion and fixed points");
    md(r`
> [!goal]
> Write a recursive function without naming it: find the trick that lets a function call itself, and the combinator that packages it.
`);
    md(r`The factorial is "if $n = 0$ then $1$ else $n \cdot \mathsf{fact}\ (n - 1)$". The definition mentions $\mathsf{fact}$, and a λ-term has no names to mention: ‹name := term› is shorthand, unfolded before reduction. How can a function refer to itself without a name?`);
    md(r`The factorial needs lesson 7's predecessor (each lesson starts with only the library):`);
    m("pred := λn. fst (n (λp. pair (snd p) (succ (snd p))) (pair 0 0))");
    md(r`
> [!mistake]
> The natural first try is to write the name anyway. Inside its own definition ‹fact› is not yet defined, so it is a free variable: $\mathsf{fact}\ 0$ works, because it never recurses, and $\mathsf{fact}\ 1$ gets stuck on the free ‹fact›.
`);
    m("fact := λn. if (iszero n) 1 (mul n (fact (pred n)))");
    m("fact 0");
    m("fact 1");
    sec("A term that copies itself");
    md(r`One term from lesson 4 does refer to itself, in a way: $\omega = \lambda x.\, x\ x$, applied to itself, hands itself its own copy.`);
    m("normal 2: omega omega", { work: true });
    md(r`That is the trick. A function cannot name itself, but it can be **given** itself, as an argument. Add a parameter $\mathit{self}$, write $\mathit{self}\ \mathit{self}$ where the function would call itself, and start it off as $\omega$ does, by applying it to itself:`);
    m("G := λself. λn. if (iszero n) 1 (mul n (self self (pred n)))");
    m("G G 3");
    md(r`$G\ G\ 3$ becomes "if $3 = 0$ then $1$ else $3 \cdot (G\ G\ (\mathsf{pred}\ 3))$": the copy of $G$ it was given is passed on, with a copy of itself.`);
    sec("Packaging the trick: Y");
    md(r`Writing $\mathit{self}\ \mathit{self}$ in every recursive function is a nuisance. We would rather write the honest step, $F = \lambda \mathit{self}.\, \lambda n.\, \ldots\ \mathit{self}\ (n - 1)$, and have something tie the knot. We want a term $X$ with $F\ X = X$: then $X$ is the factorial, since putting it in for $\mathit{self}$ gives it back. $X$ is a **fixed point** of $F$.`);
    md(r`
> [!try]
> $\omega\ \omega$ steps to itself. Slip an $F$ into $\omega$ so that each copy is passed through $F$: what does $(\lambda x.\, F\ (x\ x))\ (\lambda x.\, F\ (x\ x))$ step to?
`);
    md(r`It steps to $F\ ((\lambda x.\, F\ (x\ x))\ (\lambda x.\, F\ (x\ x)))$: $F$ applied to the term we started from. A fixed point of $F$. Abstract over $F$:`);
    md(r`
> [!definition] The Y combinator
> $Y = \lambda f.\, (\lambda x.\, f\ (x\ x))\ (\lambda x.\, f\ (x\ x))$ satisfies $Y\ g = g\ (Y\ g)$ for every $g$: $Y\ g$ is a fixed point of $g$. The equation is up to β: the two sides reduce to a common term, not one to the other.
`);
    m("normal 2: Y g", { step: 0 });
    md(r`The last line is also what $g\ (Y\ g)$ reduces to, in one step. Each unfolding hands $g$ another copy of the self-application, as many as it asks for.`);
    sec("Factorial");
    md(r`$Y\ F$ has no normal form (it unfolds for ever), so the engine keeps the definition as written; applied to a number, $F$'s test stops the unfolding. Defining ‹fact› again replaces the stuck one:`);
    m("fact := Y (λself. λn. if (iszero n) 1 (mul n (self (pred n))))");
    m("fact 2");
    m("fact 3", { work: true });
    md(r`That took 1030 β-steps, and $\mathsf{fact}\ 4$ takes 6732: numerals in unary, a predecessor that counts up from $0$ every time, and arguments copied unevaluated and computed again. The work shows the first steps and the last, and says how many it leaves out. This is why real languages build numbers in.`);
    sec("Under call by value");
    md(r`
> [!try]
> $Y\ g$ reduces to $g\ (A\ A)$ with $A = \lambda x.\, g\ (x\ x)$. Call by value evaluates an argument before the call. What happens to $A\ A$?
`);
    md(r`$A\ A$ steps to $g\ (A\ A)$, whose argument is $A\ A$ again: call by value never finishes evaluating $g$'s argument, so $g$ is never called.`);
    m("cbv 3: Y g", { work: true });
    md(r`The repair is to make the self-application a value, which waits until it is called: wrap it in a λ, $\lambda v.\, x\ x\ v$ (an η-expansion, lesson 4).`);
    md(r`
> [!definition] The Z combinator
> $Z = \lambda f.\, (\lambda x.\, f\ (\lambda v.\, x\ x\ v))\ (\lambda x.\, f\ (\lambda v.\, x\ x\ v))$. $Z\ g$ reduces to $g$ applied to a λ that wraps the self-application: a value, so call by value stops there, and the copy unfolds only when $g$ calls it.
`);
    m("Z := λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))");
    m("cbv: Z g");
    md(r`
> [!theorem] Turing completeness
> With booleans, numerals, pairs and a fixed-point combinator, every computable function on the numbers can be written as a λ-term (Kleene; Turing showed λ-definable and Turing-computable coincide). Which terms have a normal form is then undecidable, which is why the engine reduces on a budget.
`);
    sec("In Lean");
    md(r`Lean has no Y: self-application has no type (λ-calculus II shows why), and a recursive Lean definition must be shown to terminate, as a recursion on a smaller number is. Yet the factorial is still a fixed point of its defining step.`);
    lean(r`def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

#eval fact 5

/-- The step that defines the factorial, with the recursive call abstracted. -/
def F (self : Nat → Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * self n

theorem fact_fixed : ∀ n, F fact n = fact n := by
  intro n; cases n <;> rfl`);
    lx(`theorem fact_pos : ∀ n, 0 < fact n := by`, r`The factorial is never zero. Prove it by induction.`, `  intro n
  induction n with
  | zero => decide
  | succ k ih => simp [fact, ih]`, [r`‹induction n with›: ‹fact 0 = 1›, and ‹(k + 1) * fact k› is positive when ‹fact k› is.`, r`‹simp [fact, ih]› knows a product of positives is positive.`]);
    sec("Exercises");
    ex("normal 1: Y g", r`Take one step of $Y\ g$ in normal order. What is the term?`, [r`Put $g$ for $f$ in $Y$'s body.`]);
    ex("fact 1", r`Reduce $\mathsf{fact}\ 1$.`, [r`$1 \cdot \mathsf{fact}\ 0 = 1$.`]);
    ex("Y (λself. λn. if (iszero n) 0 (add n (self (pred n)))) 3", r`Change the factorial so that it sums instead: $0$ at $0$, and $n$ plus the sum up to $n - 1$ otherwise. Write it with $Y$ in a cell of your own. What does it give for $3$?`, [
      r`Replace ‹1› by ‹0› and ‹mul› by ‹add› in the step given to ‹Y›.`,
      r`$3 + 2 + 1 + 0$.`,
    ], { hide: true });
    md(r`
> [!summary]
> A function cannot name itself, but it can be given itself: self-application, as in $\omega$. $Y$ packages the trick: $Y\ g = g\ (Y\ g)$, a fixed point. Call by value needs $Z$, which delays the self-application. With fixed points the λ-calculus computes everything a computer can, and so whether a term stops is undecidable.

λ-calculus II adds types, and finds that they rule out $\omega$, $\Omega$ and $Y$: every simply typed term has a normal form.
`);
  });
}, { leanPrelude: true });

course("lambda-types", "λ-calculus II: types and proofs",
  "The simply typed λ-calculus: typing rules and derivation trees, type inference by unification, what types rule out, propositions as types, type safety, polymorphism and dependent types, with the theory proved in Lean.",
  "Logic and computation", (add) => {

  add("01-simple-types.chalk", "Simple types", "What goes wrong without types, what a type has to record to prevent it, and the three typing rules that follow.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Simple types");
    md(r`
> [!goal]
> Find what a label on a term has to say to rule out nonsense before anything runs, and type terms by the three rules that follow.
`);
    md(r`The untyped calculus refuses nothing. Hand $\mathsf{if}$ a numeral where it expects a boolean:`);
    m("if 2 a b");
    md(r`No complaint: $2$ is a function like everything else, so it takes $a$ and $b$ and gives $a\ (a\ b)$, which means nothing. Some terms never answer at all. $\Omega = (\lambda x.\, x\ x)\ (\lambda x.\, x\ x)$ steps to itself:`);
    m("normal 3: omega omega");
    md(r`It is back where it started after each step. The engine gives up after 10,000 steps; nothing in the term warned that it would never stop.`);
    md(r`
> [!try]
> Without running anything, what would you need to know about $f$ and $a$ to be sure that $f\ a$ makes sense?
`);
    sec("Types");
    md(r`Two things: that $f$ is a function, and that $a$ is the kind of thing $f$ expects. So label each term with what it is: data of some kind ($\mathsf{Nat}$, $\mathsf{Bool}$, or just $A$, $B$), or a function from one kind to another, written $A \to B$. Such a label is a **type**. A label must be checked, not trusted, so each binder states the type of what it binds: $\lambda x{:}A.\, M$ takes an $A$.`);
    md(r`
> [!definition] Simple types
> A **type** is a **base type** ($A$, $B$, $\mathsf{Nat}$, …) or an **arrow** $A \to B$, the type of functions from $A$ to $B$. The arrow groups to the right: $A \to B \to C$ is $A \to (B \to C)$, a function returning a function. A binder carries its type: $\lambda x{:}A.\, M$.
`);
    md(r`Type ‹->› for → and write the type after a colon: ‹type: \x:A. x›. The identity on $A$ takes an $A$ and gives it back:`);
    m("type: λx:A. x");
    sec("The rules");
    md(r`A term is built in one of three ways, and each way needs a rule saying what its type is.
- A **variable** has the type its binder gave it.
- A **function** $\lambda x{:}A.\, M$: assume $x : A$ and find the type $B$ of the body. The function turns $A$s into $B$s, so it has type $A \to B$.
- An **application** $M\ N$ answers the question above: $M$ must have an arrow type $A \to B$, and $N$ must have type $A$, exactly. Then $M\ N$ has type $B$.

Free names get their types from a **context**, written before ‹⊢› (or ‹|-›). With $\mathsf{Bool}$ and $\mathsf{Nat}$ kept apart, the nonsense from the start fails the third rule:`);
    m("type: if : Bool → A → A → A, two : Nat, a : A, b : A ⊢ if two a b");
    md(r`and the version that makes sense goes through:`);
    m("type: if : Bool → A → A → A, yes : Bool, a : A, b : A ⊢ if yes a b");
    md(r`
> [!mistake] Asking only for a function
> A looser application rule, "$M$ is some function", lets ‹if two a b› through: $\mathsf{if}$ is a function. The argument's type has to be the one the function expects, or the label says nothing. (Encoded as pure λ-terms, Church's $2$ and $\mathsf{if}$ are just functions, and the inference of lesson 3 accepts ‹if 2 a b›: it is base types such as $\mathsf{Nat}$ and $\mathsf{Bool}$ that tell numbers from booleans.)
`);
    md(r`
> [!definition] Typing rules
> A **context** $\Gamma$ lists the types of the variables in scope; a **judgment** $\Gamma \vdash M : T$ says $M$ has type $T$ there.
> - **Var**: if $x : T$ is in $\Gamma$, then $\Gamma \vdash x : T$.
> - **→I** (abstraction): if $\Gamma, x : A \vdash M : B$, then $\Gamma \vdash \lambda x{:}A.\, M : A \to B$.
> - **→E** (application): if $\Gamma \vdash M : A \to B$ and $\Gamma \vdash N : A$, then $\Gamma \vdash M\ N : B$.
`);
    sec("Derivations");
    md(r`Typing $\lambda f{:}A \to B.\, \lambda x{:}A.\, f\ x$ uses all three rules: Var for $f$ and for $x$, →E for $f\ x$, then →I for each binder. Stacked with each rule's premises above its conclusion, they form a tree, the **derivation**: axioms (Var) at the top, the judgment about the whole term at the bottom. ‹type:› draws it and lists its steps from the top down.`);
    md(r`
> [!try]
> Work out the type yourself, then step through the derivation.
`);
    m("type: λf:A→B. λx:A. f x", { step: 0 });
    sec("In Lean");
    md(r`The typing relation, as an inductive proposition with one constructor per rule; a derivation is a proof built from them.`);
    lean(r`/-- Simple types: base types and arrows. -/
inductive Ty where
  | base : String → Ty
  | arrow : Ty → Ty → Ty
  deriving Repr, DecidableEq

infixr:30 " ⇒ " => Ty.arrow

/-- Terms whose binders carry their types: λx:A. b. -/
inductive Tm where
  | var : String → Tm
  | lam : String → Ty → Tm → Tm
  | app : Tm → Tm → Tm
  deriving Repr, DecidableEq

/-- A context, innermost binding first. -/
abbrev Ctx := List (String × Ty)

/-- The typing relation, one constructor per rule. -/
inductive HasType : Ctx → Tm → Ty → Prop where
  | var {Γ x T} : Γ.lookup x = some T → HasType Γ (.var x) T
  | abs {Γ x A b B} : HasType ((x, A) :: Γ) b B → HasType Γ (.lam x A b) (A ⇒ B)
  | app {Γ f a A B} : HasType Γ f (A ⇒ B) → HasType Γ a A → HasType Γ (.app f a) B

def A : Ty := .base "A"
def B : Ty := .base "B"

/-- λx:A. x : A → A, as a derivation: →I over Var. -/
example : HasType [] (.lam "x" A (.var "x")) (A ⇒ A) := .abs (.var rfl)`);
    lx(`theorem K_typed : HasType [] (.lam "x" A (.lam "y" B (.var "x"))) (A ⇒ B ⇒ A) := by`, r`Build the derivation of $\vdash \lambda x{:}A.\, \lambda y{:}B.\, x : A \to B \to A$.`, `  exact .abs (.abs (.var rfl))`, [
      r`Two →I, then Var: ‹.abs (.abs (.var _))›.`,
      r`Var needs ‹x› to have type ‹A› in the context ‹[("y", B), ("x", A)]›; ‹rfl› computes the lookup.`,
    ]);
    sec("Exercises");
    md(r`Answer with a type, writing ‹->› for →: ‹(A -> B) -> A -> B›.`);
    ex("type: λx:A. λy:B. x", r`What type does $\lambda x{:}A.\, \lambda y{:}B.\, x$ have?`, [r`Two arguments, $A$ then $B$; it returns the first.`]);
    ex("type: λf:A→A. λx:A. f (f x)", r`What type does $\lambda f{:}A \to A.\, \lambda x{:}A.\, f\ (f\ x)$ have?`, [r`$f\ x : A$, so $f\ (f\ x) : A$ too.`]);
    ex("type: f : A → B ⊢ λx:A. f x", r`In the context $f : A \to B$, what type does $\lambda x{:}A.\, f\ x$ have?`, [r`The context's $f$ is not a binder of the term: only $x$ adds an arrow.`]);
    ex("type: λf:(A→B)→C. λg:A→B. f g", r`A function can take a function as its argument. What type does $\lambda f{:}(A \to B) \to C.\, \lambda g{:}A \to B.\, f\ g$ have?`, [r`$f\ g : C$. Put the binders' types in front, in parentheses where a type is itself an arrow.`]);
    md(r`
> [!summary]
> Untyped terms can compute nonsense, or never stop. A type labels a term as data of a base type or as a function $A \to B$, and binders state their types. Three rules, one per way of building a term, give a term its type: Var reads the context, →I types a function by its body, →E types an application when the argument has exactly the type the function expects. A derivation is the tree of rules used.
`);
    md(r`$\Omega$ is built from $\lambda x.\, x\ x$. What type could that $x$ have? The next lesson tries, and reads what the checker says when a term has no type.`);
  });

  add("02-derivations.chalk", "Typing derivations", "Why Ω's half has no type, where a derivation gets stuck, shadowing, one type per term, and the checker proved sound.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Typing derivations");
    md(r`
> [!goal]
> Say exactly where a term with no type gets stuck, read derivations in a context, and see why a term has only one type.
`);
    md(r`$\Omega$'s half, $\lambda x.\, x\ x$, applies $x$ to $x$, so $x$ must be a function. Try to give it a type.`);
    md(r`
> [!try]
> What goes wrong with $x : A$? With $x : A \to A$? Predict each message.
`);
    m("type: λx:A. x x");
    m("type: λx:A→A. x x");
    md(r`A base type cannot be applied. An arrow can, but $x : A \to A$ wants an $A$ and is handed itself. Whatever type $T$ you pick, $x\ x$ needs $T = T \to B$ for some $B$: $T$ would be a proper part of itself, and no type is. So $\lambda x.\, x\ x$ has no type, and $\Omega$ has none either. Lesson 4 returns to what that buys.`);
    sec("Reading a derivation");
    md(r`A derivation is a certificate: each step can be checked on its own, against its premises. The checker builds it bottom-up: to type $\lambda x{:}A.\, M$ it adds $x : A$ to the context and types $M$; to type $M\ N$ it types both and checks that they fit. The tree is read the other way, from the axioms down. Long contexts are named $\Gamma_1, \Gamma_2, \ldots$ under the tree.`);
    m("type: λf:A→B. λg:B→C. λx:A. g (f x)", { work: true });
    sec("Where a derivation gets stuck");
    md(r`Each rule has a condition, and a term without a type is one where some condition fails: Var, when a name has no type; →E, when the function is not a function (as with $x\ x$ at $x : A$), or when its argument has the wrong type.`);
    md(r`
> [!try]
> Which condition fails in each of these?
`);
    m("type: λf:A→B. λx:B. f x");
    m("type: λx:A. y");
    sec("Shadowing");
    md(r`
> [!mistake] The outer x
> A natural guess for $\lambda x{:}A.\, \lambda x{:}B.\, x$ is $A \to B \to A$, reading the last $x$ as the first binder's. But the inner binder hides the outer one: the context remembers only the nearest $x$.
`);
    m("type: λx:A. λx:B. x");
    md(r`It has to be so, or the type would disagree with what the term does: given two arguments, it returns the second.`);
    m("normal: (λx. λx. x) a b");
    sec("One type");
    md(r`At no node of a derivation is there a choice: the term's shape picks the rule, and the binder's type extends the context. So a term has at most one type in a context; the Lean below proves it. Take the binder's type away and the choice is back: $\lambda x.\, x$ could be $A \to A$, or $B \to B$, or $(A \to B) \to A \to B$, and the checker will not guess:`);
    m("type: λx. x");
    sec("In Lean");
    md(r`The checker, as a function, and the proof that it is right: whatever type it returns, the term has that type by the rules. The engine's ‹type:› is the same checker, with the same theorem (‹check_sound›), which is why its steps are marked verified.`);
    lean(r`/-- The checker: the type, if the term has one. -/
def typeOf (Γ : Ctx) : Tm → Option Ty
  | .var x => Γ.lookup x
  | .lam x A b => (typeOf ((x, A) :: Γ) b).map (A ⇒ ·)
  | .app f a =>
    match typeOf Γ f, typeOf Γ a with
    | some (.arrow A B), some A' => if A = A' then some B else none
    | _, _ => none

#eval typeOf [] (.lam "x" A (.var "x"))
#eval typeOf [] (.lam "x" A (.app (.var "x") (.var "x")))

/-- What the checker says is so. -/
theorem typeOf_sound : ∀ (t : Tm) (Γ : Ctx) (T : Ty), typeOf Γ t = some T → HasType Γ t T := by
  intro t
  induction t with
  | var x => intro Γ T h; exact .var h
  | lam x A b ih =>
    intro Γ T h
    simp only [typeOf, Option.map_eq_some_iff] at h
    obtain ⟨B, hb, rfl⟩ := h
    exact .abs (ih _ _ hb)
  | app f a ihf iha =>
    intro Γ T h
    simp only [typeOf] at h
    split at h
    · rename_i A B A' hf ha
      split at h
      · rename_i hA; subst hA; cases h; exact .app (ihf _ _ hf) (iha _ _ ha)
      · cases h
    · cases h`);
    lx(`theorem HasType.unique {Γ : Ctx} {t : Tm} {T U : Ty} (h₁ : HasType Γ t T) (h₂ : HasType Γ t U) : T = U := by`, r`A term has at most one type in a context. Prove it by induction on the first derivation.`, `  induction h₁ generalizing U with
  | var h => cases h₂ with | var h' => rw [h] at h'; exact Option.some.inj h'
  | abs _ ih => cases h₂ with | abs h' => rw [ih h']
  | app _ _ ihf _ => cases h₂ with | app hf' _ => cases ihf hf'; rfl`, [
      r`‹induction h₁ generalizing U with›, and in each case ‹cases h₂›: the second derivation must end with the same rule.`,
      r`Var: both lookups give ‹some _›, so the types are equal (‹Option.some.inj›). →I: the bodies' types agree by the hypothesis. →E: the functions' types ‹A ⇒ T› and ‹A' ⇒ U› agree, so ‹T = U›.`,
    ]);
    sec("Exercises");
    ex("type: f : A → B, g : B → C ⊢ λx:A. g (f x)", r`In the context $f : A \to B,\ g : B \to C$, what type does $\lambda x{:}A.\, g\ (f\ x)$ have?`, [r`$f\ x : B$, then $g$ takes it to $C$.`]);
    ex("type: λx:A→B→C. λy:A→B. λz:A. x z (y z)", r`What type does $\lambda x{:}A \to B \to C.\, \lambda y{:}A \to B.\, \lambda z{:}A.\, x\ z\ (y\ z)$ have? (It is $S$.)`, [r`The body has type $C$; put the three binders' types in front.`]);
    ex("type: y : A ⊢ λx:A→B. x y", r`In the context $y : A$, the term $\lambda x{:}T.\, x\ y$ should give back a $B$. Choose $T$, and give the type of the whole term.`, [r`$x$ is applied to $y : A$ and must return a $B$.`, r`So $T = A \to B$, and the term has type $T \to B$.`], { hide: true });
    md(r`
> [!summary]
> A derivation is a certificate, checked rule by rule. A term has no type when a rule's condition fails: a variable with no type, a non-function applied, an argument of the wrong type; $\lambda x.\, x\ x$ fails for every choice of type. An inner binder hides an outer one. The checker is sound, and a term has at most one type in a context.
`);
    md(r`Every binder so far carried its type, and without them the checker refuses. Must every type be written, or can it be worked out from how a term uses its variables?`);
  });

  add("03-inference.chalk", "Type inference", "Types without annotations: unknown types as variables, the equations a term imposes, unification and the occurs check.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Type inference");
    md(r`
> [!goal]
> Find the most general type of a term whose binders have no types, by solving the equations its applications impose.
`);
    md(r`Without a type on its binder, $\lambda x.\, x$ has the type $A \to A$, and $B \to B$, and $(A \to B) \to A \to B$: no single answer, until we ask for the best one.`);
    md(r`
> [!try]
> Find a type for $\lambda f.\, \lambda x.\, f\ x$ by hand. What were you forced to decide, and what could you leave open?
`);
    sec("Unknowns and equations");
    md(r`Treat the unknown types like unknowns in algebra. Say $f : \tau_1$ and $x : \tau_2$, and call the type of $f\ x$ $\tau_3$. Only the application forces anything: $f\ x$ types when $f$ is a function from $x$'s type to the result's, $\tau_1 = \tau_2 \to \tau_3$. Put that in, and the term has type $(\tau_2 \to \tau_3) \to \tau_2 \to \tau_3$. Nothing constrains $\tau_2$ and $\tau_3$, so they stay variables, $\alpha$ and $\beta$:`);
    m("infer: λf. λx. f x", { work: true });
    md(r`Equations can meet. In $\lambda f.\, \lambda x.\, f\ (f\ x)$, $f$ is applied twice, and each application gives an equation for $f$'s type.`);
    md(r`
> [!try]
> Predict the type: what does applying $f$ to its own result force?
`);
    m("infer: λf. λx. f (f x)", { step: 0 });
    md(r`Two arrows are equal only when their arguments are equal and their results are, so $\tau_2 \to \tau_3 = \tau_3 \to \tau_4$ splits into $\tau_2 = \tau_3$ and $\tau_3 = \tau_4$: $f$ must return the type it takes. The answer, $(\alpha \to \alpha) \to \alpha \to \alpha$, is the type of the Church numeral $2$.`);
    md(r`
> [!definition] Inference
> 1. Give each binder without a type, and each application's result, a **type variable** $\tau_1, \tau_2, \ldots$.
> 2. Each application $M\ N$ gives an equation: $M$'s type $= N$'s type $\to$ the result's.
> 3. Solve the equations one at a time (**unification**): an equation $\tau = T$ puts $T$ for $\tau$ everywhere; two arrows are equal when their arguments and their results are.
> 4. The variables left are named $\alpha, \beta, \ldots$: any types put for them give a type of the term.
`);
    md(r`$S$, three binders and three applications, goes the same way:`);
    m("infer: S");
    sec("The most general type");
    md(r`The variables left over are a promise: any types put for them give a type of the term. $K$ comes out as $\alpha \to \beta \to \alpha$,`);
    m("infer: K");
    md(r`so $A \to B \to A$ and $(A \to A) \to B \to A \to A$ are types of $K$ too: instances of it. Unification never commits to more than the equations force, so the type it finds is the **principal type**: every type of the term is an instance of it (Hindley, 1969). One answer covers them all.`);
    sec("The occurs check");
    md(r`Lesson 2 showed that $\lambda x.\, x\ x$ has no type by trying guesses. Inference finds it in one equation: $x : \tau_1$ applied to itself gives $\tau_1 = \tau_1 \to \tau_2$.`);
    m("infer: λx. x x");
    md(r`
> [!mistake] Just substitute
> Putting $\tau_1 \to \tau_2$ for $\tau_1$ never ends: $\tau_1 = (\tau_1 \to \tau_2) \to \tau_2 = ((\tau_1 \to \tau_2) \to \tau_2) \to \tau_2 = \cdots$. A variable cannot be solved by a type that contains it, so unification checks for that (the **occurs check**) and gives up. Allowing the infinite type instead would give $\Omega$ a type.
`);
    sec("Some types given");
    md(r`Types given and types found mix: annotated binders keep their types, and the rest is inferred around them. A free variable gets a type variable too, and the answer says what it had to be.`);
    m("infer: λf:A→B. λx. f x");
    m("infer: f x");
    md(r`Every inferred type is checked: the term, annotated with it, goes through the type checker of lesson 1, and the tree shown is that check.`);
    sec("In Lean");
    md(r`Lean infers too, by the same kind of unification: give it some types and it finds the rest.`);
    lean(r`#check fun (f : Nat → Bool) x => f x
#check fun (x : Nat) (_ : String) => x`);
    lx(`theorem typing_by_inference : ∃ T, HasType [] (.lam "f" (A ⇒ B) (.lam "x" A (.app (.var "f") (.var "x")))) T := by`, r`Show that $\lambda f{:}A \to B.\, \lambda x{:}A.\, f\ x$ has a type, without writing it: let Lean infer it from the derivation.`, `  exact ⟨_, .abs (.abs (.app (.var rfl) (.var rfl)))⟩`, [
      r`‹exact ⟨_, derivation⟩›: the underscore is solved by unification with the derivation's conclusion.`,
      r`The derivation is →I, →I, then →E over two Vars.`,
    ]);
    sec("Exercises");
    md(r`Answer with letters for the type variables, like ‹a -> b -> a›; any names will do, as long as the shape matches.`);
    ex("infer: λx. λy. y", r`Infer the type of $\lambda x.\, \lambda y.\, y$.`, [r`Two arguments of unrelated types; it returns the second.`]);
    ex("infer: λf. λg. λx. g (f x)", r`Infer the type of composition, $\lambda f.\, \lambda g.\, \lambda x.\, g\ (f\ x)$.`, [r`$x : \alpha$, $f : \alpha \to \beta$, $g : \beta \to \gamma$.`]);
    ex("infer: λx. λf. f x", r`Infer the type of $\lambda x.\, \lambda f.\, f\ x$.`, [r`$f$ is applied to $x$.`]);
    ex("infer: λx. λy. x (y x)", r`Infer the type of $\lambda x.\, \lambda y.\, x\ (y\ x)$, by writing its two equations and solving them.`, [r`Say $x : \tau_1$, $y : \tau_2$. Then $y\ x$ gives $\tau_2 = \tau_1 \to \tau_3$, and $x\ (y\ x)$ gives $\tau_1 = \tau_3 \to \tau_4$.`, r`Put the second into the first: $y : (\tau_3 \to \tau_4) \to \tau_3$.`]);
    md(r`
> [!summary]
> Inference gives each unknown type a variable, turns each application into an equation, and solves the equations by unification. The occurs check rejects a type that would contain itself. The answer is the principal type: every other type of the term is an instance of it.
`);
    md(r`$\lambda x.\, x\ x$ has no simple type, so neither do $\Omega$ and $Y$, the terms that loop. Are they the only terms types rule out, and can a typed term ever run for ever?`);
  });

  add("04-normalization.chalk", "What types rule out", "Ω and Y fail to type, every typed term stops, and what that costs.", ({ sec, md, m, ex, lean, lx }) => {
    sec("What types rule out");
    md(r`
> [!goal]
> See $\Omega$ and $Y$ fail to type, see why every typed term reaches a normal form, and what that guarantee costs.
`);
    md(r`Lesson 1 opened with $\Omega$ looping. $Y$, which gives the untyped calculus its recursion, unfolds for as long as you let it:`);
    m("normal 4: Y f");
    md(r`
> [!try]
> Both are built on self-application. What will inference say about each?
`);
    m("infer: omega");
    m("infer: Y");
    md(r`The occurs check both times: inside $Y$, $\lambda x.\, f\ (x\ x)$ has the same $x\ x$.`);
    sec("Every typed term stops");
    md(r`Is that luck, or can no typed term loop? Watch what a β-step does to types. A redex $(\lambda x{:}A.\, M)\ N$ uses up a function of type $A \to B$. A redex the step creates is headed by a function of type $A$ or $B$: smaller than $A \to B$. New work appears only at smaller types, and types cannot shrink for ever. That is not yet a proof, since a step can also copy redexes already inside $N$; Tait's method turns the idea into one.`);
    md(r`
> [!theorem] Strong normalization
> In the simply typed λ-calculus every reduction sequence of a typed term is finite: every typed term has a normal form, and every strategy reaches it (Tait, 1967).
`);
    md(r`So a typed term never loops. It can still take a long time: the theorem says reduction ends, not that it ends soon, and a short typed term can have an enormous normal form.`);
    sec("The price");
    md(r`Every typed term stops, so no fixed-point combinator has a type, and the simply typed calculus has no unbounded recursion: it is not Turing complete. Typed languages add recursion back as a primitive (‹fix›, ‹let rec›), and give up termination with it.`);
    md(r`Types also refuse some terms that would run fine. Give the identity to a function that uses its argument on an $a$ and on a $b$:`);
    m("normal: (λf. pair (f a) (f b)) (λx. x)");
    m("infer: a : A, b : B ⊢ (λf. pair (f a) (f b)) (λx. x)");
    md(r`It reduces to the pair of $a$ and $b$, but a simply typed $f$ has one type, and the identity is needed at $A \to A$ and at $B \to B$. An identity written once for every type is lesson 7's polymorphism.`);
    sec("Typed numerals");
    md(r`Much of Church's arithmetic survives. A numeral has type $(\alpha \to \alpha) \to \alpha \to \alpha$, and multiplication is typed:`);
    m("infer: 3");
    m("infer: mul");
    md(r`‹mul›'s principal type is more general than numerals need: put $A \to A$ for each of $\alpha, \beta, \gamma$ and it becomes $N \to N \to N$, where $N = (A \to A) \to A \to A$ is the type of numerals at $A$.`);
    md(r`Not all of it survives. Church's $\mathsf{and} = \lambda p.\, \lambda q.\, p\ q\ p$ passes $p$ to itself:`);
    m("infer: and");
    md(r`
> [!try]
> When $p$ is false, $p\ q\ p$ returns $p$, which is false. So what could stand in place of the last $p$? Predict whether the result has a type.
`);
    m("infer: λp. λq. p q false");
    md(r`The same truth table, no self-application, and a type.`);
    sec("In Lean");
    md(r`A small typed language: numbers, booleans, addition, a test for zero and ‹if›. Its evaluator is structurally recursive, so Lean accepts it as total: it always stops. With no functions in the language, termination is that easy; for λ-terms it is the theorem above. A program can still be stuck: ‹1 + true› has no value, and the type checker refuses it before it runs.`);
    lean(r`inductive Expr where
  | num : Nat → Expr
  | tt : Expr
  | ff : Expr
  | add : Expr → Expr → Expr
  | isZero : Expr → Expr
  | ite : Expr → Expr → Expr → Expr

inductive T where
  | nat | bool
  deriving DecidableEq, Repr

def typeOfE : Expr → Option T
  | .num _ => some .nat
  | .tt | .ff => some .bool
  | .add a b => match typeOfE a, typeOfE b with
    | some .nat, some .nat => some .nat
    | _, _ => none
  | .isZero a => match typeOfE a with
    | some .nat => some .bool
    | _ => none
  | .ite c t e => match typeOfE c, typeOfE t, typeOfE e with
    | some .bool, some A, some B => if A = B then some A else none
    | _, _, _ => none

inductive Val where
  | num : Nat → Val
  | bool : Bool → Val
  deriving DecidableEq, Repr

/-- Evaluation; none is a program stuck on a type error. -/
def evalE : Expr → Option Val
  | .num n => some (.num n)
  | .tt => some (.bool true)
  | .ff => some (.bool false)
  | .add a b => match evalE a, evalE b with
    | some (.num m), some (.num n) => some (.num (m + n))
    | _, _ => none
  | .isZero a => match evalE a with
    | some (.num n) => some (.bool (n == 0))
    | _ => none
  | .ite c t e => match evalE c with
    | some (.bool true) => evalE t
    | some (.bool false) => evalE e
    | _ => none

#eval evalE (.ite (.isZero (.num 0)) (.num 1) (.num 2))
#eval evalE (.add (.num 1) .tt)`);
    lx(`theorem rejects : typeOfE (.add (.num 1) .tt) = none := by`, r`The type checker refuses ‹1 + true›, the program that gets stuck.`, `  rfl`, [r`Both sides compute: ‹rfl›.`]);
    sec("Exercises");
    ex("infer: λx. λy. x y y", r`Infer the type of $\lambda x.\, \lambda y.\, x\ y\ y$.`, [r`$x$ takes $y$ twice.`]);
    ex("infer: λf. f (λx. x)", r`Infer the type of $\lambda f.\, f\ (\lambda x.\, x)$.`, [r`$f$ is given the identity, of type $\alpha \to \alpha$.`]);
    ex("infer: λp. λq. p true q", r`Church's $\mathsf{or} = \lambda p.\, \lambda q.\, p\ p\ q$ passes $p$ to itself too, and has no simple type. When $p$ is true, the $p$ it passes is true. Repair it the same way as ‹and›, and infer the type of the result.`, [r`Replace the middle $p$ by $\mathsf{true}$: $\lambda p.\, \lambda q.\, p\ \mathsf{true}\ q$.`, r`$\mathsf{true} : \alpha \to \beta \to \alpha$, and $p$ takes it and then $q$.`], { hide: true });
    md(r`
> [!summary]
> Self-application has no simple type, so neither $\Omega$ nor $Y$ does. Every typed term reaches a normal form (strong normalization): a β-step makes new work only at smaller types. The price: no unbounded recursion, and some harmless terms refused, since a simply typed function uses its argument at one type.
`);
    md(r`Look again at the arrow rules. From $B$, assuming $A$, conclude $A \to B$; from $A \to B$ and $A$, conclude $B$. Read $\to$ as "implies", and these are the rules for implication in logic. The next lesson asks whether that is a coincidence.`);
  });

  add("05-curry-howard.chalk", "Propositions as types", "The typing rules turn out to be the rules of logic: a type is a proposition, a term a proof of it, β-reduction simplifies proofs, and Peirce's law, true by truth table, has no term.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Propositions as types");
    md(r`
> [!goal]
> Read a type as a proposition and a term as its proof, prove implications by writing functions, and find a tautology that no function proves.
`);
    md(r`Lesson 4 ended on a resemblance: read $\to$ as "implies", and the arrow rules look like the rules for implication. Test it on the types already found.`);
    md(r`
> [!try]
> $K = \lambda x.\, \lambda y.\, x$ has type $A \to B \to A$. Read $A$ and $B$ as statements and $\to$ as "implies": is it true whatever $A$ and $B$ are?
`);
    m("taut(p → q → p)");
    md(r`A tautology. So is $S$'s type, $(A \to B \to C) \to (A \to B) \to A \to C$:`);
    m("taut((p → q → r) → (p → q) → p → r)");
    md(r`
> [!try]
> Is every type a tautology? Look for a closed term of type $A \to B$, and ask the truth table about $p \to q$.
`);
    m("taut(p → q)");
    md(r`Not a tautology, and no term either. A function of type $A \to B$ has to produce a $B$, and inside $\lambda x{:}A.\, \ldots$ the only thing at hand is $x : A$. Anything else is a variable with no type:`);
    m("type: λx:A. y");
    sec("Proofs as programs");
    md(r`Put the typing rules next to natural deduction's rules for implication, and look only at the types:
- **Var**: $x : A$ in the context gives $A$. In logic: use an assumption.
- **→I**: if $M : B$ with $x : A$ added, then $\lambda x{:}A.\, M : A \to B$. In logic: assume $A$, prove $B$, and conclude $A \to B$, discharging the assumption.
- **→E**: $M : A \to B$ and $N : A$ give $M\ N : B$. In logic: modus ponens.

They are the same rules. A term records which rule was used where, so a term is a proof, written compactly, and its type is what it proves.`);
    md(r`
> [!theorem] Curry–Howard
> Read base types as propositions and $A \to B$ as "$A$ implies $B$". A closed term of type $T$ is a proof of $T$ in intuitionistic propositional logic (its part with only $\to$), and every such proof is a term: Var is using an assumption, →I is proving an implication by assuming its premise, →E is modus ponens. (Curry saw it for combinators in the 1930s, Howard for λ-terms in 1969.)
`);
    md(r`A derivation tree is then a proof tree. Here is composition's; read only the types, and it proves that implication is transitive: from $A \to B$ and $B \to C$, conclude $A \to C$.`);
    m("type: λf:A→B. λg:B→C. λx:A. g (f x)", { work: true });
    md(r`Curry's version: the types of $K$ and $S$ are exactly the two axioms of Hilbert's logic of implication, and application is modus ponens, its one rule.`);
    sec("Simplifying a proof");
    md(r`What does β-reduction do to a proof? A redex $(\lambda x{:}A.\, M)\ N$ proves $A \to B$ by →I only to use it at once by →E: a detour. The step puts the proof $N$ of $A$ wherever $M$ used the assumption $x$, and leaves a direct proof of the same conclusion.`);
    m("type: a : A ⊢ (λx:A. λy:B. x) a");
    m("normal: (λx:A. λy:B. x) a");
    md(r`Both prove $B \to A$ from $a : A$; the second (printed without its binder's type) with no detour. Read as logic, lesson 4's theorem says that every proof simplifies to one with no detours (Prawitz, 1965). That gives a short proof that the logic is consistent. A closed term with no redex is a λ (anything else has a variable at its head, and a closed term has no free one), so its type is an arrow. A base type $A$ has no closed term in normal form, hence none at all: not everything is provable.`);
    sec("A tautology with no proof");
    md(r`Each rule keeps truth, row by row of a truth table, so every type with a term is a tautology. The converse is the real question. Take **Peirce's law**, $((A \to B) \to A) \to A$:`);
    m("taut(((p → q) → p) → p)");
    md(r`
> [!try]
> Find a term of type $((A \to B) \to A) \to A$.
`);
    md(r`Given $h : (A \to B) \to A$, the only way to an $A$ is through $h$, and $h$ wants a function from $A$ to $B$. The obvious one to hand it returns what it is given:`);
    m("type: λh:(A→B)→A. h (λa:A. a)");
    md(r`That turns an $A$ into an $A$, not a $B$, and nothing in sight makes a $B$. No term does better: every term has a normal form, so it is enough to search the normal ones, and a short search finds none of this type. Peirce's law is true by truth table and has no proof here.`);
    md(r`The truth table assumes that $A$ is true or false, one or the other, even when nobody can say which. A proof that is a program has to actually produce its $A$. Logic that asks for that is **intuitionistic**, and the simply typed terms prove exactly its implications. Classical logic adds the excluded middle, $A \lor \lnot A$, which no program proves: in the Lean below it comes from Lean's axiom of choice.`);
    sec("Negation");
    md(r`Simple types have only arrows, but negation fits. Let $F$ be a proposition with no proof, falsity, and read $\lnot A$ as $A \to F$: a way of turning a proof of $A$ into the impossible. (Lean defines ‹¬P› as ‹P → False›.) Then $A \to \lnot\lnot A$ is $A \to (A \to F) \to F$, and has a term:`);
    m("type: λa:A. λk:A→F. k a");
    md(r`The converse, $\lnot\lnot A \to A$, is again a tautology with no term: a $k : (A \to F) \to F$ only ever gives an $F$.`);
    sec("In Lean");
    md(r`In Lean propositions are types and proofs are terms, literally: a tactic proof builds a term, and ‹fun› writes one directly. ‹P ∧ Q› is a type of pairs, and a proof of ‹P ∨ Q› is one of the two, tagged with which.`);
    lean(r`theorem K_prop (P Q : Prop) : P → Q → P := fun p _ => p
theorem S_prop (P Q R : Prop) : (P → Q → R) → (P → Q) → P → R := fun f g p => f p (g p)

/-- Peirce's law needs the excluded middle. -/
theorem peirce (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  cases Classical.em P with
  | inl p => exact p
  | inr np => exact h (fun p => absurd p np)`);
    lx(`theorem imp_trans (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by`, r`Prove that implication is transitive. The proof is the composition function.`, `  intro f g p
  exact g (f p)`, [r`‹intro f g p› names the assumptions.`, r`Apply ‹f› to ‹p›, then ‹g› to that.`]);
    lx(`theorem and_swap (P Q : Prop) : P ∧ Q → Q ∧ P := by`, r`Prove that ∧ commutes. A proof of ‹P ∧ Q› is a pair.`, `  intro ⟨p, q⟩
  exact ⟨q, p⟩`, [r`‹intro ⟨p, q⟩› takes the pair apart.`, r`Build the swapped pair with ‹⟨q, p⟩›.`]);
    sec("Exercises");
    ex("type: λf:A→B→C. λb:B. λa:A. f a b", r`What does $\lambda f{:}A \to B \to C.\, \lambda b{:}B.\, \lambda a{:}A.\, f\ a\ b$ prove? Give its type.`, [r`It swaps the order of two assumptions.`]);
    ex("infer: λf. λk. λa. k (f a)", r`Prove contraposition, $(A \to B) \to \lnot B \to \lnot A$, that is $(A \to B) \to (B \to F) \to A \to F$: write a term without types, in a cell of your own, taking its three arguments in that order, and give the type ‹infer:› finds for it.`, [
      r`Given $a : A$, $f$ makes a $B$, and $k$ turns a $B$ into $F$.`,
      r`It is composition again: $\lambda f.\, \lambda k.\, \lambda a.\, k\ (f\ a)$.`,
    ], { hide: true });
    ex("taut(¬¬p → p)", r`Is $\lnot\lnot A \to A$ a tautology? Answer ‹⊤› or ‹⊥›.`, []);
    md(r`
> [!summary]
> The typing rules are natural deduction's rules for implication: a type is a proposition and a closed term a proof of it; Var is an assumption, →I assuming, →E modus ponens, and a β-step removes a detour from a proof. Every type with a term is a tautology, but not every tautology has a term: Peirce's law and $\lnot\lnot A \to A$ need classical logic's excluded middle, which no program proves.
`);
    md(r`A proof is a program, and lesson 1 promised that a typed program cannot compute nonsense. What exactly does a type promise about a program while it runs?`);
  });

  add("06-safety.chalk", "Type safety", "A program stuck with no rule to apply, the two promises a type must make about every step (progress and preservation), a looser rule that breaks one, and safety proved in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Type safety");
    md(r`
> [!goal]
> Find what "a typed program cannot go wrong" has to mean, step by step, and prove it for a small language.
`);
    md(r`In the pure λ-calculus everything is a function, so nonsense still computes: lesson 1's ‹if 2 a b› gave $a\ (a\ b)$. Real languages have data that is not a function, numbers and booleans, and there a program can reach a point where nothing applies. Let free names stand for such data, $\mathsf{tt}$ a boolean and $n$ a number:`);
    m("cbv: (λf. f n) tt");
    md(r`Call by value stops at $\mathsf{tt}\ n$. It is not a value (a value is a λ or a name on its own), and no step applies, since $\mathsf{tt}$ is not a function. The program is **stuck**: not finished, and unable to go on. A machine would crash here, or carry on with garbage. The type checker refuses it before it runs:`);
    m("type: tt : Bool, n : Nat ⊢ (λf:Nat→Nat. f n) tt");
    md(r`
> [!try]
> The checker looks at a program once, before it runs; running takes many steps. What must be true of a single step for that one check to protect them all?
`);
    sec("Two promises");
    md(r`Two things. A typed term that is not yet a value must be able to take a step, so it is not stuck now. And the term after the step must still be typed, at the same type, so that the first promise applies to it as well. Watch the second over two steps. The term has type $B$:`);
    m("type: f : A → B, x : A ⊢ (λg:A→B. λy:A. g y) f x");
    m("normal: (λg:A→B. λy:A. g y) f x", { work: true });
    md(r`
> [!try]
> What type does the middle term, $(\lambda y{:}A.\, f\ y)\ x$, have? And the last, $f\ x$?
`);
    m("type: f : A → B, x : A ⊢ (λy:A. f y) x");
    m("type: f : A → B, x : A ⊢ f x");
    md(r`$B$ each time. (Reduction drops the binders' types, so the engine prints $\lambda y.\, f\ y$: they say which terms are allowed, not how they compute.) Every step keeps the type, and at every step being typed means not being stuck, so the chain never breaks.`);
    md(r`
> [!theorem] Type safety
> - **Progress**: a closed, typed term is a value or can take a step.
> - **Preservation**: if $\Gamma \vdash M : T$ and $M$ takes a step to $M'$, then $\Gamma \vdash M' : T$.
>
> Together, by induction on the number of steps: a closed typed term never reaches a stuck term. Milner's slogan (1978) is "well-typed programs cannot go wrong"; the two halves are Wright and Felleisen's way of proving it (1994).
`);
    sec("Why both");
    md(r`Each promise can fail without the other. Take lesson 4's small language, with numbers, booleans, ‹+›, a test for zero and ‹if›, and a natural shortcut in the rule for ‹if›.`);
    md(r`
> [!mistake] An ‹if› typed by its first branch
> "‹if c then t else e› has the type of ‹t›" is simpler than asking the two branches to agree, and it lets ‹if false then 1 else true› through as a number. That term is not stuck: it steps, to ‹true›, which is a boolean. Preservation fails, and with it the chain: a typed program can now get stuck (an exercise below builds one).
`);
    md(r`Lesson 4's checker asks the branches to agree (‹if A = B›). Here is the loose one, in Lean: it calls the program a number, and the program evaluates to a boolean.`);
    lean(r`/-- A looser checker: an if has the type of its first branch, whatever the second's. -/
def typeOfLoose : Expr → Option T
  | .num _ => some .nat
  | .tt | .ff => some .bool
  | .add a b => match typeOfLoose a, typeOfLoose b with
    | some .nat, some .nat => some .nat
    | _, _ => none
  | .isZero a => match typeOfLoose a with
    | some .nat => some .bool
    | _ => none
  | .ite c t _ => match typeOfLoose c with
    | some .bool => typeOfLoose t
    | _ => none

#eval typeOfLoose (.ite .ff (.num 1) .tt)
#eval evalE (.ite .ff (.num 1) .tt)`);
    md(r`
> [!try]
> Which rule would you loosen to break progress instead, so that a typed term is stuck at once?
`);
    md(r`Let ‹isZero› accept anything. ‹isZero true› is then a boolean, and no rule evaluates it. It takes no step, so preservation, a promise about steps, is kept; progress is the half that fails.`);
    sec("Small steps and big steps");
    md(r`
> [!definition] Operational semantics
> A **small-step** semantics says what one step does, $M \to M'$: the β-steps of every cell so far. A **big-step** semantics says what a whole program evaluates to, $M \Downarrow v$, in one judgment, by recursion on the program. Progress and preservation are about small steps. The Lean evaluator of lesson 4 is big-step, so its safety theorem says it in one go: a typed program evaluates, and to a value of its type.
`);
    sec("Safety in Lean");
    md(r`For lesson 4's language, with its strict rule for ‹if›, safety is one theorem: a program with a type evaluates to a value of that type. It never gets stuck, and it never comes back with the wrong kind of value.`);
    lean(r`/-- A value's type: a number is a nat, a boolean a bool. -/
def Val.ty : Val → T
  | .num _ => .nat
  | .bool _ => .bool

theorem safety : ∀ (e : Expr) (τ : T), typeOfE e = some τ → ∃ v, evalE e = some v ∧ v.ty = τ := by
  intro e
  induction e with
  | num n => intro τ h; cases h; exact ⟨.num n, rfl, rfl⟩
  | tt => intro τ h; cases h; exact ⟨.bool true, rfl, rfl⟩
  | ff => intro τ h; cases h; exact ⟨.bool false, rfl, rfl⟩
  | add a b iha ihb =>
    intro τ h
    simp only [typeOfE] at h
    split at h
    · rename_i ha hb
      cases h
      obtain ⟨va, ea, ta⟩ := iha _ ha
      obtain ⟨vb, eb, tb⟩ := ihb _ hb
      cases va <;> cases vb <;> simp_all [Val.ty, evalE]
    · cases h
  | isZero a iha =>
    intro τ h
    simp only [typeOfE] at h
    split at h
    · rename_i ha
      cases h
      obtain ⟨va, ea, ta⟩ := iha _ ha
      cases va <;> simp_all [Val.ty, evalE]
    · cases h
  | ite c t e ihc iht ihe =>
    intro τ h
    simp only [typeOfE] at h
    split at h
    · rename_i A B hc ht he
      split at h
      · rename_i hAB
        cases h; subst hAB
        obtain ⟨vc, ec, tc⟩ := ihc _ hc
        cases vc with
        | num _ => simp [Val.ty] at tc
        | bool b =>
          cases b
          · obtain ⟨v, ev, tv⟩ := ihe _ he; exact ⟨v, by simp [evalE, ec, ev], tv⟩
          · obtain ⟨v, ev, tv⟩ := iht _ ht; exact ⟨v, by simp [evalE, ec, ev], tv⟩
      · cases h
    · cases h`);
    md(r`The proof leans on the strict rule exactly once: in the ‹ite› case, ‹subst hAB› makes the two branches' types one, so whichever branch runs has the promised type. For the loose checker the theorem is false, and this is the case that breaks.`);
    lx(`theorem typed_add_evaluates (a b : Expr) (ha : typeOfE a = some .nat) (hb : typeOfE b = some .nat) :
    ∃ n, evalE (.add a b) = some (.num n) := by`, r`Use safety: adding two typed numbers gives a number.`, `  obtain ⟨va, ea, ta⟩ := safety a _ ha
  obtain ⟨vb, eb, tb⟩ := safety b _ hb
  cases va <;> cases vb <;> simp_all [Val.ty, evalE]`, [
      r`‹safety a _ ha› gives a value of ‹a› and that its type is ‹nat›; the same for ‹b›.`,
      r`Split both values with ‹cases›: a boolean contradicts its type, two numbers add. ‹simp_all [Val.ty, evalE]›.`,
    ]);
    lx(`theorem loose_gets_stuck : ∃ e, typeOfLoose e = some .nat ∧ evalE e = none := by`, r`Find a program that the loose checker calls a number and that gets stuck: evaluation gives ‹none›.`, `  exact ⟨.add (.ite .ff (.num 1) .tt) (.num 1), rfl, rfl⟩`, [
      r`‹if false then 1 else true› is a number to the loose checker and evaluates to a boolean. Use it where a number is needed.`,
      r`‹exact ⟨.add (.ite .ff (.num 1) .tt) (.num 1), rfl, rfl⟩›: both sides compute.`,
    ]);
    md(r`
> [!note] What safety does not promise
> Safety is only as strong as the types. Haskell's ‹head› has type ‹[a] -> a›, and at the empty list it has no ‹a› to give, so it raises an error. An error the language defines is not a stuck term, so safety holds, and the program still fails. Lesson 8 finds types that rule the empty list out.
`);
    sec("Exercises");
    md(r`Check preservation on one more step.`);
    ex("type: f : A → B, x : A ⊢ (λg:A→B. g x) f", r`What type does $(\lambda g{:}A \to B.\, g\ x)\ f$ have, in the context $f : A \to B,\ x : A$?`, [r`The function returns $g\ x : B$.`]);
    ex("normal: (λg:A→B. g x) f", r`Reduce $(\lambda g{:}A \to B.\, g\ x)\ f$. By preservation, the result has the same type.`, [r`One β-step.`]);
    md(r`
> [!summary]
> Without types a program can get stuck: not a value, and no rule applies. The checker runs once, so a type has to promise something about every step: progress (a typed term is a value or takes a step) and preservation (a step keeps the type). Loosen a rule and one of them fails: an ‹if› typed by one branch breaks preservation, an ‹isZero› that takes anything breaks progress. Together they are type safety, proved in Lean, in its big-step form, for lesson 4's language.
`);
    md(r`Safety has lesson 4's price: $(\lambda f.\, \mathsf{pair}\ (f\ a)\ (f\ b))\ (\lambda x.\, x)$ would never get stuck, and is refused, because $f$ can have only one type. Can one term have many?`);
  });

  add("07-polymorphism.chalk", "Polymorphism", "The identity written once for every type: why a defined name can be used at many types and an argument cannot, System F, and Church numerals at every type.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Polymorphism");
    md(r`
> [!goal]
> Use one term at many types: find why a defined name can be and an argument cannot, and the quantifier that lets an argument be too.
`);
    md(r`Lesson 4 refused a harmless term: the identity, handed to a function that uses it on an $a : A$ and on a $b : B$.`);
    m("infer: a : A, b : B ⊢ (λf. pair (f a) (f b)) id");
    md(r`
> [!try]
> Now use ‹id› in both places directly. Will this have a type?
`);
    m("infer: a : A, b : B ⊢ pair (id a) (id b)", { work: true });
    md(r`It does. ‹id› is a name, and names are unfolded before inference (the first step of the work), so each use is a copy of $\lambda x.\, x$ with a type variable of its own: one becomes $A \to A$, the other $B \to B$. In the refused term the identity is the value of one variable, $f$, and a variable has one type.`);
    sec("Type schemes");
    md(r`So a name deserves a type that each use can instantiate as it likes. Its inferred type already reads that way:`);
    m("infer: id");
    md(r`$\alpha$ may be anything, and each use may choose. Written out, the type is a **scheme**, $\forall \alpha.\, \alpha \to \alpha$: for every $\alpha$, a function from $\alpha$ to $\alpha$. $K$, with scheme $\forall \alpha\, \beta.\, \alpha \to \beta \to \alpha$, can be used at two types the same way:`);
    m("infer: a : A, b : B ⊢ pair (K a b) (K b a)");
    md(r`ML and Haskell build this into ‹let›: in ‹let id = λx. x in …›, ‹id› gets the scheme $\forall \alpha.\, \alpha \to \alpha$ and each use takes its own instance, as each unfolded copy did. This is **Hindley–Milner** typing: inference stays decidable and still finds principal types, as in lesson 3. A λ-bound variable still has one type.`);
    sec("Quantifiers inside types");
    md(r`Lesson 4's term needs more than schemes. Its function, $\lambda f.\, \mathsf{pair}\ (f\ a)\ (f\ b)$, wants an argument that works at every type, so its type would begin $(\forall \alpha.\, \alpha \to \alpha) \to \cdots$: a $\forall$ to the left of an arrow. A scheme can only put $\forall$ in front of a whole type. The fix is to make $\forall$ a type like any other, and types something a term can take and be given.`);
    md(r`
> [!definition] System F (Girard, 1972; Reynolds, 1974)
> Types may quantify over types: $\forall \alpha.\, T$. A term may take a type as an argument, $\Lambda \alpha.\, M$, and be given one, $M\ [T]$, which puts $T$ for $\alpha$. The polymorphic identity is $\mathit{id} = \Lambda \alpha.\, \lambda x{:}\alpha.\, x : \forall \alpha.\, \alpha \to \alpha$, and $\mathit{id}\ [A] : A \to A$.
`);
    md(r`Lesson 4's term becomes $(\lambda f{:}\forall \alpha.\, \alpha \to \alpha.\, \langle f\ [A]\ a,\ f\ [B]\ b \rangle)\ \mathit{id}$, of type $A \times B$: $f$ is given $A$ in one place and $B$ in the other. Lean's ‹∀ α : Type› is System F's quantifier, and a type is an argument like any other:`);
    lean(r`/-- The polymorphic identity: given a type, the identity on it. -/
def polyId : ∀ α : Type, α → α := fun _ x => x

/-- Lesson 4's term: a function whose argument must work at every type. -/
def onBoth (f : ∀ α : Type, α → α) : Nat × String := (f Nat 1, f String "b")

#eval onBoth polyId`);
    sec("Numerals at every type");
    md(r`Church numerals hit the same wall. A numeral iterates, $2\ f\ a = f\ (f\ a)$, at any type. Used twice by name, it types; passed in as an argument, it does not:`);
    m("infer: f : A → A, a : A, g : B → B, b : B ⊢ pair (2 f a) (2 g b)");
    m("infer: f : A → A, a : A, g : B → B, b : B ⊢ λn. pair (n f a) (n g b)");
    md(r`In System F a numeral has one type that covers every use, $\mathsf{Nat} = \forall \alpha.\, (\alpha \to \alpha) \to \alpha \to \alpha$, and a function that takes a numeral can use it at any type it likes. In Lean, used at ‹Nat› to read it and at ‹String› for fun:`);
    lean(r`/-- Church numerals in System F: a numeral works at every type. -/
def CNat := ∀ α : Type, (α → α) → α → α

def czero : CNat := fun _ _ x => x
def csucc (n : CNat) : CNat := fun α f x => f (n α f x)
def cadd (m n : CNat) : CNat := fun α f x => m α f (n α f x)
def cmul (m n : CNat) : CNat := fun α f => m α (n α f)
def two : CNat := csucc (csucc czero)
def three : CNat := csucc two

/-- Read a numeral by using it at Nat. -/
def CNat.toNat (n : CNat) : Nat := n Nat (· + 1) 0

#eval (cadd two three).toNat
-- the same numeral, used at String
#eval three String (· ++ "!") "go"`);
    md(r`System F keeps lesson 4's guarantee: every term still has a normal form (Girard, 1972), although even self-application now has a type, $\lambda x{:}\forall \alpha.\, \alpha \to \alpha.\, x\ [\forall \alpha.\, \alpha \to \alpha]\ x$. What it gives up is inference: whether a term without annotations has a System F type is undecidable (Wells, 1994). So ML stops at Hindley–Milner, and Haskell goes beyond it only where the programmer writes the types.`);
    lx(`theorem six : (cmul two three).toNat = 6 := by`, r`Check that $2 \cdot 3 = 6$ with System F numerals.`, `  rfl`, [r`Everything computes: ‹rfl›.`]);
    lx(`theorem cpow_exists : ∃ p : CNat → CNat → CNat, (p two three).toNat = 8 := by`, r`Invent exponentiation: find ‹p› with ‹p two three› equal to $2^3 = 8$. ‹cmul› used ‹m› at the type ‹α›; use ‹n› at the type ‹α → α›, to iterate ‹m α›.`, `  exact ⟨fun m n α => n (α → α) (m α), rfl⟩`, [
      r`‹m α : (α → α) → α → α› turns $f$ into $f$ applied $m$ times. Do that $n$ times, and $f$ is applied $m^n$ times.`,
      r`‹exact ⟨fun m n α => n (α → α) (m α), rfl⟩›.`,
    ]);
    sec("Exercises");
    md(r`Answer with letters for type variables.`);
    ex("infer: λf. λg. λx. f (g x)", r`Infer the most general type of $\lambda f.\, \lambda g.\, \lambda x.\, f\ (g\ x)$.`, [r`$g$ first, then $f$.`]);
    ex("infer: pair", r`Infer the type of $\mathsf{pair} = \lambda a.\, \lambda b.\, \lambda s.\, s\ a\ b$.`, [r`$s$ takes $a$ and $b$ and returns anything.`]);
    ex("infer: a : A ⊢ id id a", r`In $\mathsf{id}\ \mathsf{id}\ a$, with $a : A$, the two copies of $\mathsf{id}$ are used at different types. Infer the type of the whole term.`, [r`The second $\mathsf{id}$ is used at $A \to A$, the first at $(A \to A) \to A \to A$.`]);
    md(r`
> [!summary]
> A defined name can be used at many types: each use is a copy, with its own instance of the name's scheme $\forall \alpha.\, \ldots$; ML's and Haskell's ‹let› work the same way (Hindley–Milner). A λ-bound variable has one type, so a function cannot ask for an argument that works at every type, until System F makes $\forall$ part of types and lets terms take types as arguments. Church numerals then have one type, $\forall \alpha.\, (\alpha \to \alpha) \to \alpha \to \alpha$, usable at any type; decidable inference is the price.
`);
    md(r`In System F a term can depend on a type. Can a type depend on a term: a list type that knows the list's length, so that a type can say "never the head of an empty list"?`);
  });

  add("08-dependent-types.chalk", "Dependent types", "Types that mention values: a head that cannot be given an empty list, Π-types as ∀, and Lean checking a proof by checking a type.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Dependent types");
    md(r`
> [!goal]
> Write a type that mentions a value, use it to rule out the head of an empty list, and see Lean check a proof by checking a type.
`);
    md(r`Lesson 6 left a hole in safety: a ‹head› of type ‹List α → α› promises an ‹α› for every list, the empty one too.`);
    md(r`
> [!try]
> How would you write a ‹head› that never fails? What would its type have to know?
`);
    md(r`At the empty list there is nothing to return, and ‹α› may have no values at all. Either the result admits failure (‹Option α›), or the argument's type rules the empty list out. Lean's own ‹List.head› does the second:`);
    lean(r`#check @List.head
#eval [1, 2, 3].head (List.cons_ne_nil _ _)`);
    md(r`After the list ‹as› comes a second argument, of type ‹as ≠ []›: a proof that this list is not empty. That type mentions ‹as›, a value given earlier. A type that mentions a value is **dependent**.`);
    sec("Length in the type");
    md(r`Another way: put the length in the list's type. ‹Vec α n› is the type of lists of length ‹n›: ‹nil› has length $0$, and ‹cons› adds one. ‹head› asks for a ‹Vec α (n + 1)› and needs no case for ‹nil› at all, since ‹nil›'s type, ‹Vec α 0›, is never ‹Vec α (n + 1)›.`);
    lean(r`/-- Vectors: lists whose length is in their type. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

namespace Vec

/-- The head of a nonempty vector: there is no case for nil, because the type rules it out. -/
def head : Vec α (n + 1) → α
  | cons x _ => x

def toList : Vec α n → List α
  | nil => []
  | cons x xs => x :: xs.toList

/-- n copies of x: the result's type depends on the number given. -/
def replicate : (n : Nat) → α → Vec α n
  | 0, _ => nil
  | n + 1, x => cons x (replicate n x)

def append : Vec α n → Vec α m → Vec α (m + n)
  | nil, ys => ys
  | cons x xs, ys => cons x (append xs ys)

end Vec

#eval (Vec.cons 1 (Vec.cons 2 Vec.nil)).head
#eval (Vec.append (Vec.cons 1 (Vec.cons 2 Vec.nil)) (Vec.cons 3 Vec.nil)).toList
#check Vec.replicate 3 'a'`);
    md(r`
> [!try]
> What will Lean say to the head of ‹nil›?
`);
    lean(r`#check_failure (Vec.nil : Vec Nat 0).head`);
    md(r`A type error, found before anything runs: ‹0› is not ‹n + 1› for any ‹n›. The head of an empty vector is not a failure at run time; it is not a program at all.`);
    sec("Π-types");
    md(r`Look at ‹replicate›'s type, ‹(n : Nat) → α → Vec α n›. The type of the result depends on the value of the argument: ‹replicate 3 'a'› is a ‹Vec Char 3›.`);
    md(r`
> [!definition] Π-types
> A **dependent function type** $(x : A) \to B(x)$, also written $\Pi x{:}A.\, B(x)$, is the type of functions that take an $a : A$ to a value of type $B(a)$. When $B$ does not mention $x$, it is the arrow $A \to B$. Its rules are →I and →E grown up: $\lambda x{:}A.\, M$ has type $(x : A) \to B(x)$ when $M : B(x)$ with $x : A$ added; and if $f : (x : A) \to B(x)$ and $a : A$, then $f\ a : B(a)$, with $a$ put for $x$ in the type.
`);
    md(r`Curry–Howard comes along. Read $B(x)$ as a statement about $x$: a function taking each $x : A$ to a proof of $B(x)$ is a proof of $\forall x : A,\ B(x)$. Lean writes ‹∀ x : A, B x› and ‹(x : A) → B x› for the same type, and a proof by induction on ‹n› is such a function, built by recursion on ‹n›.`);
    sec("Type checking runs programs");
    md(r`Look at ‹append›'s type: lengths ‹n› and ‹m› give ‹m + n›. In the ‹cons› case, ‹xs› has some length ‹k› and the result, ‹cons x (append xs ys)›, has length ‹(m + k) + 1›; the type promised ‹m + (k + 1)›. The checker sees that they agree by computing: ‹+› is defined by recursion on its second argument, so ‹m + (k + 1)› reduces to ‹(m + k) + 1›. Write the type with ‹n + m› and the two sides no longer reduce to one, and Lean asks for a proof.`);
    md(r`
> [!theorem] Type checking is proof checking
> A Lean theorem is a type and its proof a term. Lean's kernel checks a proof by type checking the term, with lesson 1's rules grown to Π-types and inductive types, and with computation inside types: two types that compute to the same thing are the same type. That is why ‹rfl›, the proof that a thing equals itself, proves ‹2 + 2 = 4›.
`);
    lean(r`theorem two_plus_two : 2 + 2 = 4 := rfl`);
    lx(`theorem Vec.toList_length : ∀ (v : Vec α n), v.toList.length = n := by`, r`The list of a vector of length $n$ has length $n$: the type was telling the truth.`, `  intro v
  induction v with
  | nil => rfl
  | cons x xs ih => simp [Vec.toList, ih]`, [r`‹induction v with›: ‹nil› is ‹rfl›.`, r`For ‹cons›, unfold ‹toList› and use the hypothesis: ‹simp [Vec.toList, ih]›.`]);
    lx(`theorem Vec.eq_nil (v : Vec α 0) : v = .nil := by`, r`A vector of length $0$ can only be ‹nil›: the reason ‹head› needs no ‹nil› case, seen from the other side. Prove it.`, `  cases v
  rfl`, [r`‹cases v› leaves one case: ‹cons› would need ‹0 = k + 1›, and Lean sees that it cannot be.`, r`What is left is ‹nil = nil›: ‹rfl›.`]);
    sec("The map");
    md(r`
> [!definition] The λ-cube
> Simple types let terms depend on terms: functions. Lesson 7 let terms depend on types (System F), and this lesson types depend on terms (dependent types). The third step, types that depend on types (type operators, such as ‹List›, which takes a type to a type), gives $F_\omega$. All three together are the **calculus of constructions** (Coquand and Huet, 1988); Lean's type theory adds inductive types, such as ‹Vec›, and a hierarchy of universes.
`);
    sec("Exercises");
    ex("infer: λx. λy. λz. x z (y z)", r`The course in one cell: infer the type of $S$ without annotations. Read as a proposition, it is lesson 5's second Hilbert axiom.`, [r`It is $(A \to B \to C) \to (A \to B) \to A \to C$, with variables.`]);
    md(r`
> [!summary]
> A dependent type mentions a value: ‹as ≠ []›, ‹Vec α n›. With the length in the type, the head of an empty list is a type error, not a failure at run time. Π-types $(x : A) \to B(x)$ generalize the arrow and, read as propositions, are $\forall$: Curry–Howard reaches the quantifiers. Lean checks a proof this way: the proof is a term, and checking it is lesson 1's three rules, grown to Π-types and inductive types, with computation inside types.
`);
  });
}, { leanPrelude: true });

// ---------------------------------------------------------------------------------------------------
const manifest = {
  projects: [
    ...courses.map((c) => ({ id: c.id, title: c.title, blurb: c.blurb, kind: "course", level: c.level, path: `courses/${c.id}`,
      ...(c.leanPrelude ? { leanPrelude: true } : {}),
      lessons: c.lessons.map((l) => ({ file: l.file, title: l.title, blurb: l.blurb })) })),
    { id: "explorations", title: "Explorations", kind: "collection", path: "",
      blurb: "Notebooks that show what ChalkMath does: a tour, Fourier series drawing a llama, and order theory with its proofs in Lean.",
      lessons: [
        { file: "welcome.chalk", title: "Welcome to ChalkMath", blurb: "A short tour: running cells, reading the steps, and one example from each area." },
        { file: "llamas.chalk", title: "Drawing llamas with circles", blurb: "Fourier series from inner products to epicycles, ending with a llama drawn by spinning circles." },
        { file: "order-lattices.chalk", title: "Order and lattices", blurb: "Part I of From Zero to Propagators: partial orders, joins and meets, monotone maps and fixed points, with the proofs in Lean cells." },
      ] },
  ],
};
for (const c of courses) {
  const dir = new URL(`../../notebooks/courses/${c.id}/`, import.meta.url);
  mkdirSync(dir, { recursive: true });
  for (const l of c.lessons) {
    writeFileSync(new URL(l.file, dir), JSON.stringify({ chalk: 1, name: l.file, cells: l.cells, scenes: [] }, null, 2) + "\n");
  }
  console.log(`notebooks/courses/${c.id}: ${c.lessons.length} lessons, ${c.lessons.reduce((n, l) => n + l.cells.filter((x) => x.type === "exercise").length, 0)} exercises`);
}
writeFileSync(new URL("../../notebooks/courses.json", import.meta.url), JSON.stringify(manifest, null, 2) + "\n");
console.log(`notebooks/courses.json: ${manifest.projects.length} projects`);
