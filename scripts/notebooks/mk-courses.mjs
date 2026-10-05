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
course("logic", "Logic and proof technique",
  "Propositions and truth tables, normal forms, proofs as Lean tactics, quantifiers, three kinds of induction, relations and well-founded termination: the toolkit every later course uses.",
  "Discrete mathematics", (add) => {

  add("01-truth-tables.chalk", "Propositions and truth tables", "Connectives, truth tables, tautologies, and satisfying assignments as witnesses.", ({ sec, md, m, ex }) => {
    sec("Propositions and truth tables");
    md(r`
> [!goal]
> Read a formula of propositional logic, build its truth table, and decide whether it is always true, sometimes true, or never true, with a row that shows it.
`);
    md(r`
> [!definition] Proposition, connective
> A **proposition** is a statement that is either true or false. Variables $p, q, r$ stand for propositions, and the **connectives** build bigger ones: $\lnot p$ (not), $p \land q$ (and), $p \lor q$ (or), $p \to q$ (if … then), $p \leftrightarrow q$ (if and only if). $\top$ is true and $\bot$ is false.
`);
    md(r`Type the glyphs, or their ASCII spellings: ‹!p›, ‹p && q›, ‹p || q›, ‹p -> q›, ‹p <-> q›, ‹true›, ‹false›. A cell with a connective in it is a logic cell.`);
    m("p && q -> p");
    sec("Truth tables");
    md(r`
> [!definition] Truth table
> A formula's **truth table** lists every assignment of true and false to its variables, one row each, with the formula's value. $n$ variables make $2^n$ rows.
`);
    m("truthtable(p ∧ q)");
    m("truthtable(p ∨ q)");
    md(r`
> [!definition] Implication
> $p \to q$ is false in exactly one row: $p$ true and $q$ false. When $p$ is false the implication holds whatever $q$ is ("vacuously"): a promise "if it rains, I bring an umbrella" is not broken on a dry day.
`);
    m("truthtable(p → q)");
    sec("Tautologies and counterexamples");
    md(r`
> [!definition] Tautology, satisfiable, contradiction
> A formula is a **tautology** when every row is true, **satisfiable** when some row is, and a **contradiction** when none is. A row where it is false is a **counterexample**; a row where it is true is a **witness**.
`);
    md(r`‹taut› decides by the table. When the answer is ⊥ the step names the row that falsifies it.`);
    m("taut((p → q) ∨ (q → p))", { work: true });
    m("taut(p → q)", { work: true });
    m("truthtable((p → q) ∧ (q → r) → (p → r))");
    md(r`‹sat› gives a satisfying assignment, as a map from each variable to its value, or ⊥ when there is none; ‹falsify› gives a counterexample the same way.`);
    m("sat((p ∨ q) ∧ ¬p)", { work: true });
    m("sat(p ∧ ¬p)");
    m("falsify(p ∧ q → r)");
    sec("The converse and the contrapositive");
    md(r`
> [!mistake]
> $p \to q$ does not say $q \to p$ (the **converse**). "If $n$ is divisible by 4 then $n$ is even" is true; "if $n$ is even then $n$ is divisible by 4" is not. ‹equiv› decides whether two formulas have the same table, and names a row where they differ:
`);
    m("equiv(p → q, q → p)", { work: true });
    md(r`The **contrapositive** $\lnot q \to \lnot p$ is equivalent, which is why a proof "suppose not $q$ … then not $p$" proves $p \to q$.`);
    m("equiv(p → q, ¬q → ¬p)");
    sec("Exercises");
    md(r`Answer ‹true› or ‹false› (or ⊤, ⊥) for ‹taut› and ‹equiv›. For ‹sat› and ‹falsify›, give an assignment, as a map such as ‹{p ↦ true, q ↦ false}› or as a conjunction of literals such as ‹p ∧ ¬q›; any assignment that works is right.`);
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
> A propositional formula is decided by its truth table: true in every row (a tautology), in some row (satisfiable, with a witness), or in none (a contradiction). A counterexample is a single row, and one is enough.
`);
  });

  add("02-normal-forms.chalk", "Equivalence and normal forms", "The laws of logic as rewrites: negation normal form, CNF and DNF, one law a step.", ({ sec, md, m, ex }) => {
    sec("Equivalence and normal forms");
    md(r`
> [!goal]
> Rewrite a formula into negation normal form, conjunctive normal form and disjunctive normal form, naming the law used at each step, and check an answer by its truth table.
`);
    md(r`
> [!definition] Logical equivalence
> $\varphi \equiv \psi$ when $\varphi$ and $\psi$ have the same value under every assignment: the same truth table. Replacing a subformula by an equivalent one does not change the value of the whole.
`);
    md(r`
> [!theorem] The laws used below
> $p \to q \equiv \lnot p \lor q$, $\quad p \leftrightarrow q \equiv (p \to q) \land (q \to p)$, $\quad \lnot\lnot p \equiv p$,
>
> De Morgan: $\lnot(p \land q) \equiv \lnot p \lor \lnot q$ and $\lnot(p \lor q) \equiv \lnot p \land \lnot q$,
>
> distribution: $p \lor (q \land r) \equiv (p \lor q) \land (p \lor r)$ and $p \land (q \lor r) \equiv (p \land q) \lor (p \land r)$.
`);
    md(r`Each is proved in Lean over the booleans, and the engine's normal forms are proved to keep the value of the formula (the dot next to each step).`);
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
> $\lnot(p \land q)$ is **not** $\lnot p \land \lnot q$: De Morgan's law swaps $\land$ for $\lor$. The engine finds the row where they differ:
`);
    m("equiv(¬(p ∧ q), ¬p ∧ ¬q)", { work: true });
    sec("Conjunctive and disjunctive normal form");
    md(r`
> [!definition] CNF and DNF
> A **literal** is a variable or its negation. A **clause** is an $\lor$ of literals and a **term** an $\land$ of them. A formula is in **conjunctive normal form** when it is an $\land$ of clauses, and in **disjunctive normal form** when it is an $\lor$ of terms.
`);
    md(r`From NNF, distribute $\lor$ over $\land$ for CNF (or $\land$ over $\lor$ for DNF). A clause that contains both $p$ and $\lnot p$ is always true and drops out; so does a term with both, which is always false.`);
    m("cnf(p ∨ (q ∧ r))", { work: true });
    m("cnf(p ↔ q)", { step: 0 });
    m("dnf(p ↔ q)", { step: 0 });
    md(r`
> [!note] Why CNF
> A CNF is a list of constraints that must all hold, each satisfied by any one of its literals. SAT solvers, which decide satisfiability for formulas with millions of variables, take their input in CNF.
`);
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
    md(r`
> [!summary]
> The laws of logic are rewrites that keep the truth table. NNF pushes negations onto the variables; CNF and DNF then distribute. Any formula has all three forms, and the truth table decides whether a proposed one is right.
`);
  });

  add("03-natural-deduction.chalk", "Proofs as Lean tactics", "Natural deduction in Lean: introduce and use each connective, and see proofs as programs.", ({ sec, md, lean, lx }) => {
    sec("Proofs as Lean tactics");
    md(r`
> [!goal]
> Prove propositional statements in Lean with the rules of natural deduction, written as tactics: ‹intro›, ‹exact›, ‹constructor›, ‹cases›, ‹left› and ‹right›.
`);
    md(r`A truth table checks a formula by trying every row. A **proof** derives it by rules, each a small, obviously valid step, and it works where a table cannot: for statements about infinitely many numbers, or with variables that are not just true or false. Lean checks every step.`);
    md(r`
> [!definition] Introduction and elimination
> Each connective has rules that **introduce** it (how to prove it) and rules that **eliminate** it (how to use it):
>
> - $p \to q$: to prove it, assume $p$ and prove $q$ (‹intro›); to use it, apply it to a proof of $p$.
> - $p \land q$: prove both (‹constructor›, or ‹⟨hp, hq⟩›); from it, take either (‹h.1›, ‹h.2›).
> - $p \lor q$: prove one (‹left›, ‹right›); to use it, prove the goal in both cases (‹cases›).
> - $\lnot p$ is $p \to \bot$: to prove it, assume $p$ and reach a contradiction.
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
> The term ‹fun hp => h (Or.inl hp)› above is a program: a function taking a proof of $p$ to a proof of $\bot$. In Lean a proof of $p \to q$ *is* a function from proofs of $p$ to proofs of $q$, and a proof of $p \land q$ is a pair. Propositions are types and proofs are their values; checking a proof is type checking. The λ-calculus courses come back to this.
`);
    lean(r`example (p q : Prop) : p ∧ q → q ∧ p := fun ⟨hp, hq⟩ => ⟨hq, hp⟩`);
    md(r`
> [!mistake]
> Every tautology has a truth table, but not every tautology has a proof by these rules alone. $\lnot\lnot p \to p$ is a tautology, yet the rules above only give $p$ from evidence for $p$. It needs one more principle, the excluded middle (‹Classical.em p : p ∨ ¬p›), or proof by contradiction:
`);
    lean(r`theorem dne (p : Prop) : ¬¬p → p := by
  intro h
  exact Classical.byContradiction h`);
    md(r`
> [!summary]
> Natural deduction gives each connective rules to introduce and to eliminate it, and Lean's tactics are those rules. A proof of an implication is a function; a proof of a conjunction is a pair.
`);
  });

  add("04-quantifiers.chalk", "Predicates and quantifiers", "∀ and ∃ over finite sets, with the element that decides them; quantifiers in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Predicates and quantifiers");
    md(r`
> [!goal]
> Read and decide statements with $\forall$ and $\exists$ over a finite set, find the counterexample or the witness, negate them, and prove simple ones in Lean.
`);
    md(r`
> [!definition] Quantifiers
> $\forall n \in S,\ \varphi(n)$ says $\varphi$ holds for every $n$ in $S$; $\exists n \in S,\ \varphi(n)$ says it holds for at least one. A $\forall$ is refuted by one **counterexample**; an $\exists$ is proved by one **witness**.
`);
    md(r`Over a finite set the engine checks every element in order, and names the one that decided. Type ‹forall n in 1..10, …› or the glyphs; the body can compare numbers and use ‹prime›, ‹even›, ‹odd› and ‹∣› (divides).`);
    m("∀ n ∈ 1..10, n^2 ≥ n", { work: true });
    m("∀ n ∈ 1..10, n^2 ≥ 2n", { work: true });
    m("∃ n ∈ {4, 6, 9, 11}, prime(n)", { work: true });
    sec("Checking is not proving");
    md(r`
> [!mistake]
> A statement about every natural number is not proved by checking some of them. Euler noticed that $n^2 + n + 41$ is prime for $n = 1, 2, 3, \dots$, a long way:
`);
    m("∀ n ∈ 1..39, prime(n^2 + n + 41)");
    m("∀ n ∈ 1..40, prime(n^2 + n + 41)", { work: true });
    md(r`At $n = 40$ it is $41^2$. Checking finds counterexamples; only a proof covers all $n$. The induction lessons are about those proofs.`);
    sec("Negation and order");
    md(r`
> [!theorem] Negating a quantifier
> $\lnot \forall n,\ \varphi(n) \equiv \exists n,\ \lnot\varphi(n)$ and $\lnot \exists n,\ \varphi(n) \equiv \forall n,\ \lnot\varphi(n)$: "not every" is "some not".
`);
    m("¬(∀ n ∈ 1..10, n^2 ≥ 2n)");
    m("∃ n ∈ 1..10, ¬(n^2 ≥ 2n)", { work: true });
    md(r`
> [!mistake]
> The order of quantifiers matters. "Every $n$ has some $m$ different from it" is true; "some $m$ is different from every $n$" is false, since $m$ would have to differ from itself.
`);
    m("∀ n ∈ 1..6, ∃ m ∈ 1..6, m ≠ n");
    m("∃ m ∈ 1..6, ∀ n ∈ 1..6, m ≠ n");
    sec("Exercises");
    md(r`Answer ‹true› or ‹false›.`);
    ex("∀ n ∈ 1..20, prime(n) → odd(n)", r`Is every prime between 1 and 20 odd?`, [r`One prime is even.`]);
    ex("∃ n ∈ 3..30, n^2 = 2^n", r`Is there an $n$ between 3 and 30 with $n^2 = 2^n$?`, [r`Try small powers of 2.`]);
    ex("∀ n ∈ 1..12, 3 ∣ n^3 - n", r`Does 3 divide $n^3 - n$ for every $n$ from 1 to 12?`, [r`Factor it: $n^3 - n = (n-1)\,n\,(n+1)$. What is true of three consecutive numbers?`]);
    ex("∀ n ∈ 1..10, n^2 ≤ 2^n", r`Is $n^2 \le 2^n$ for every $n$ from 1 to 10?`, [r`Compute both sides for $n = 3$.`]);
    sec("Quantifiers in Lean");
    md(r`In Lean, a proof of $\exists n, P(n)$ is a pair: the witness and a proof that it works. A proof of $\forall n, P(n)$ is a function taking any $n$ to a proof of $P(n)$.`);
    lean(r`example : ∃ n : Nat, n * n = 16 := ⟨4, rfl⟩

example : ∀ n : Nat, n + 0 = n := fun _ => rfl`);
    lx(r`theorem exists_sq_36 : ∃ n : Nat, n * n = 36 := by`, r`Give a witness.`, r`  exact ⟨6, rfl⟩`, [r`‹exact ⟨w, rfl⟩›, with the right ‹w›.`]);
    lx(r`theorem forall_and_left (α : Type) (P Q : α → Prop) : (∀ x, P x ∧ Q x) → ∀ x, P x := by`, r`If every $x$ has both properties, every $x$ has the first.`, r`  intro h x
  exact (h x).1`, [r`‹intro h x›, then ‹h x› is a proof of ‹P x ∧ Q x›.`]);
    lx(r`theorem not_exists_forall (α : Type) (P : α → Prop) : (¬ ∃ x, P x) → ∀ x, ¬ P x := by`, r`Prove one half of negating $\exists$: if no $x$ has $P$, every $x$ lacks it.`, r`  intro h x hx
  exact h ⟨x, hx⟩`, [r`‹¬ P x› is ‹P x → False›: introduce the proof ‹hx› too.`, r`Then ‹⟨x, hx⟩› proves the ‹∃› that ‹h› denies.`]);
    md(r`
> [!summary]
> A $\forall$ falls to one counterexample and an $\exists$ stands on one witness. Over a finite set both can be checked; over all numbers they must be proved. Negation swaps them, and their order changes the meaning.
`);
  });

  add("05-induction.chalk", "Induction on the natural numbers", "Weak induction: check a formula for small n, then prove it for all n in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Induction on the natural numbers");
    md(r`
> [!goal]
> Prove statements about every natural number by induction: a base case and a step from $n$ to $n + 1$.
`);
    md(r`Is $1 + 2 + \cdots + n = \dfrac{n(n+1)}{2}$? Drag ‹n› and compare.`);
    m("let n = 5", { slider: [1, 30, 1] });
    m("sum(k, k, 1, n)");
    m("n(n+1)/2");
    md(r`And for every $n$ up to 20 at once:`);
    m("∀ n ∈ 1..20, sum(k, k, 1, n) = n(n+1)/2");
    md(r`Twenty cases are evidence, not a proof (Euler's polynomial worked for 39). Induction proves all of them.`);
    sec("The principle");
    md(r`
> [!theorem] Induction
> If $P(0)$ holds, and $P(n)$ implies $P(n + 1)$ for every $n$, then $P(n)$ holds for every natural number $n$.
`);
    md(r`
> [!note] Why it works
> $P(0)$ gives $P(1)$, which gives $P(2)$, and so on: every $n$ is reached from $0$ by finitely many steps of $+1$. In Lean this is not an axiom but the way ‹Nat› is defined: a natural number is ‹zero› or ‹succ n›, and the ‹induction› tactic is the recursion that follows that definition.
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
    md(r`The ‹succ› case has the **induction hypothesis** ‹ih : 2 * sumTo k = k * (k + 1)› and must prove the formula for ‹k + 1›. Unfolding ‹sumTo› once and using ‹ih› leaves arithmetic, which ‹grind› finishes.`);
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
    grind`, [r`‹induction n with›, then a case for ‹zero› and one for ‹succ k ih›.`, r`In the ‹succ› case, ‹simp only [oddSum, ih]› leaves ‹k * k + (2 * k + 1) = (k + 1) * (k + 1)›.`]);
    lx(r`theorem lt_two_pow' (n : Nat) : n + 1 ≤ 2 ^ n := by`, r`Prove $n + 1 \le 2^n$ for every $n$.`, r`  induction n with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega`, [r`The step: from $k + 1 \le 2^k$, show $k + 2 \le 2^k \cdot 2$.`, r`‹rw [Nat.pow_succ]› turns ‹2 ^ (k + 1)› into ‹2 ^ k * 2›; then ‹omega› treats ‹2 ^ k› as a number.`]);
    md(r`
> [!summary]
> Induction proves $P(n)$ for all $n$ from a base case and a step. Checking cases finds mistakes; the step is the proof. In Lean, ‹induction› splits the goal into those two cases and hands the step its hypothesis.
`);
  });

  add("06-strong-induction.chalk", "Strong induction", "Course-of-values arguments: using every smaller case, and how strong induction, weak induction and well-ordering relate.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Strong induction");
    md(r`
> [!goal]
> Prove statements whose step needs not just the case before but any smaller case, and see why that is no stronger than ordinary induction.
`);
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
    md(r`With stamps of 3 and 5, which amounts can you make exactly?`);
    m("∀ n ∈ 8..40, ∃ a ∈ 0..14, ∃ b ∈ 0..8, n = 3a + 5b");
    m("∃ a ∈ 0..3, ∃ b ∈ 0..2, 7 = 3a + 5b");
    md(r`Every amount from 8 on: 8, 9 and 10 directly, and any $n \ge 11$ from $n - 3$ plus one stamp of 3. The step reaches back three, so it needs three base cases.`);
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
    md(r`Each Fibonacci number uses the two before it, so a proof about them uses two earlier cases.`);
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
    md(r`
> [!theorem] Weak induction, strong induction, well-ordering
> These are equivalent: each proves the others.
>
> - Strong induction gives weak: its hypothesis includes the case $n - 1$.
> - Weak gives strong: apply weak induction to $Q(n)$ = "$P(m)$ for every $m < n$".
> - Well-ordering (every non-empty set of naturals has a least element) gives strong induction: if $P$ failed somewhere, take the least $n$ where it fails; $P$ holds below $n$, so the step gives $P(n)$, a contradiction.
`);
    md(r`The last form is the one lesson 9 generalizes: induction works on any relation with no infinite descending chains.`);
    ex("∀ n ∈ 12..50, ∃ a ∈ 0..12, ∃ b ∈ 0..10, n = 4a + 5b", r`With stamps of 4 and 5, can every amount from 12 to 50 be made exactly? Answer ‹true› or ‹false›.`, [r`12, 13, 14 and 15 directly; then reach back by 4.`]);
    ex("∃ a ∈ 0..3, ∃ b ∈ 0..3, 11 = 4a + 5b", r`Can 11 be made from stamps of 4 and 5?`, [r`Try $b = 0, 1, 2$.`]);
    md(r`
> [!summary]
> Strong induction lets the step use every smaller case, with as many base cases as the step reaches back. It proves nothing ordinary induction cannot, but it fits arguments that split $n$ into smaller pieces.
`);
  });

  add("07-structural-induction.chalk", "Structural induction", "Induction on lists, trees and expressions, and a small simplifier proved sound.", ({ sec, md, lean, lx }) => {
    sec("Structural induction");
    md(r`
> [!goal]
> Prove properties of recursive data (lists, trees, expressions) by induction on their structure, and prove a small program transformation correct.
`);
    md(r`
> [!definition] Structural induction
> A type defined by constructors (a list is ‹[]› or ‹x :: xs›) has an induction principle with a case per constructor, and a hypothesis for each recursive part. To prove $P$ for every list: prove $P([\,])$, and $P(xs) \to P(x :: xs)$.
`);
    md(r`Natural numbers are the special case ‹zero› or ‹succ n›: the last two lessons were structural induction on ‹Nat›.`);
    sec("Lists");
    lean(r`def len {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => len xs + 1

theorem len_append {α : Type} (xs ys : List α) : len (xs ++ ys) = len xs + len ys := by
  induction xs with
  | nil => simp [len]
  | cons x xs ih => simp [len, ih]; omega`);
    md(r`Induction is on ‹xs›, the list that ‹++› recurses on: ‹(x :: xs) ++ ys = x :: (xs ++ ys)›, which is exactly where the hypothesis applies.`);
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
    md(r`A ‹node› has two recursive parts, so its case has two hypotheses, one for each subtree.`);
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
> A simplifier is **sound** when it never changes what an expression means. ChalkMath's own engine is proved sound this way: each rewrite rule keeps the value, and a structural induction carries that through the whole term. Here is the same argument in miniature.
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
  });

  add("08-relations.chalk", "Relations", "Properties with counterexamples, closures step by step, equivalence classes and partitions, and a deduplication bug.", ({ sec, md, m, ex }) => {
    sec("Relations");
    md(r`
> [!goal]
> Decide the properties of a relation, with the pairs that break them; compute closures; and read an equivalence relation as a partition.
`);
    md(r`
> [!definition] Relation
> A **relation** on a set $S$ is a set of pairs $(x, y)$ of elements of $S$; write $x \mathrel{R} y$ when $(x, y)$ is one of them. Draw it as a graph: an arrow from $x$ to $y$ for each pair.
`);
    m("let R = rel({a, b, c}; a->b, b->c, b->b)");
    sec("Properties");
    md(r`
> [!definition] Reflexive, symmetric, antisymmetric, transitive
> $R$ is **reflexive** when $x \mathrel{R} x$ for every $x$; **symmetric** when $x \mathrel{R} y$ gives $y \mathrel{R} x$; **antisymmetric** when $x \mathrel{R} y$ and $y \mathrel{R} x$ give $x = y$; **transitive** when $x \mathrel{R} y$ and $y \mathrel{R} z$ give $x \mathrel{R} z$.
`);
    md(r`Each check shows the pairs that break the property in red.`);
    m("reflexive(R)", { work: true });
    m("symmetric(R)", { work: true });
    m("antisymmetric(R)");
    m("transitive(R)", { work: true });
    sec("Closures");
    md(r`
> [!definition] Closure
> The **transitive closure** of $R$ is the least transitive relation containing it: add every pair forced by two that chain, and repeat until nothing new is forced. The reflexive and symmetric closures add $(x, x)$ and the reverse pairs.
`);
    md(r`Step through it: each round adds the pairs that the last round's pairs force. The added pairs are dashed.`);
    m("let P = rel({a, b, c, d}; a->b, b->c, c->d)");
    m("closure(P, transitive)", { step: 0 });
    md(r`
> [!theorem] The closure is the least
> Every pair a round adds lies in any transitive relation containing $R$, and the rounds stop only when the relation is transitive. So the result is transitive and inside every transitive relation containing $R$. Both facts are proved in Lean (the dot on each step).
`);
    sec("Equivalence relations and partitions");
    md(r`
> [!definition] Equivalence relation, class, partition
> An **equivalence relation** is reflexive, symmetric and transitive: it says when two elements count as the same. The **class** of $x$ is everything related to it, the classes **partition** the set (every element in exactly one), and the set of classes is the **quotient** $S/{\sim}$.
`);
    md(r`The commonest way to get one: give each element a label, and relate two elements when their labels are equal. That is the **kernel** of the labelling.`);
    m("let K = kernel({r1, r2, r3, r4}; r1->k1, r2->k1, r3->k2, r4->k2)");
    m("equivalence(K)");
    m("classes(K)", { work: true });
    md(r`A relation that is not an equivalence has a closure that is one:`);
    m("let E = closure(R, equivalence)");
    m("classes(E)");
    sec("Finer and coarser");
    md(r`
> [!definition] Refinement
> $A$ is **finer** than $K$ when every pair of $A$ is a pair of $K$: each class of $A$ lies inside a class of $K$. Then $K$ is **coarser**, and merges more.
`);
    md(r`
> [!example] Deduplicating by key
> A service receives requests $r_1, \dots, r_4$ and drops duplicates. Requests $r_1$ and $r_2$ carry key $k_1$ and the same action; $r_3$ and $r_4$ carry key $k_2$ but different actions. Deduplicating by key treats two requests as the same when their keys are equal (the relation $K$ above). What should count as the same is the same key *and* the same payload: the relation $A$.
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
> A relation's properties are checked pair by pair, and a failure is a pair you can point at. Closures add exactly what a property forces. An equivalence relation is a partition, and comparing two of them (finer, coarser) is how you find out which things get merged that should not be.
`);
  });

  add("09-well-founded.chalk", "Well-founded relations and termination", "No infinite descent: cycles as counterexamples, measures as proofs, and termination in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Well-founded relations and termination");
    md(r`
> [!goal]
> Recognize a well-founded relation, prove one with a measure, and prove that recursive functions terminate.
`);
    md(r`
> [!definition] Well-founded
> Read $x \mathrel{R} y$ as "$x$ steps to $y$". $R$ is **well-founded** when there is no infinite chain of steps $x_0 \mathrel{R} x_1 \mathrel{R} x_2 \mathrel{R} \cdots$. On a finite set that means exactly: no cycle.
`);
    md(r`This is the setting of the last two lessons: induction is valid along any well-founded relation, because a counterexample could be followed down forever otherwise. $<$ on $\mathbb{N}$ is the familiar case.`);
    m("let R = rel({a, b, c, d}; a->b, b->c, a->c, c->d)");
    m("wellfounded(R)", { work: true });
    m("let C = rel({x, y, z}; x->y, y->z, z->x)");
    m("wellfounded(C)", { work: true });
    sec("Measures");
    md(r`
> [!theorem] A measure proves termination
> If a function $m$ to the natural numbers goes down along every step ($x \mathrel{R} y$ gives $m(y) < m(x)$), $R$ is well-founded: an infinite chain of steps would be an infinite decreasing chain of natural numbers.
`);
    m("measure(R; a->3, b->2, c->1, d->0)", { work: true });
    m("measure(R; a->3, b->2, c->2, d->0)", { work: true });
    md(r`A cycle can have no measure: going round it would return to the same value having gone down.`);
    sec("Termination in Lean");
    md(r`Lean accepts a recursive definition only when it can see that it stops. Structural recursion (on a smaller part) it checks itself; otherwise it asks for a measure with ‹termination_by› and, if needed, a proof that each call decreases it with ‹decreasing_by›.`);
    lean(r`def gcd' (a b : Nat) : Nat :=
  if _h : b = 0 then a else gcd' b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

#eval gcd' 48 18`);
    md(r`
> [!definition] Lexicographic order
> Pairs are compared by their first components, and by the second only when the first are equal. It is well-founded when both orders are, even though the second component can grow without bound whenever the first goes down.
`);
    lean(r`def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack m 1
  | m + 1, n + 1 => ack m (ack (m + 1) n)
termination_by m n => (m, n)

#eval ack 2 3`);
    md(r`Ackermann's function: in every call either $m$ goes down, or $m$ stays and $n$ goes down. No single number measures it, but the pair does.`);
    sec("Exercises");
    m("let G = rel({s, t, u, v}; s->t, t->u, u->s, u->v)");
    ex("wellfounded(G)", r`Is $G$ well-founded? Answer ‹true› or ‹false›.`, [r`Follow the arrows from $s$.`]);
    m("let H = rel({1, 2, 3, 4, 5}; 5->3, 3->1, 4->2, 5->4, 2->1)");
    ex("measure(H; 1->0, 2->1, 3->1, 4->2, 5->2)", r`Does the measure $1 \mapsto 0$, $2 \mapsto 1$, $3 \mapsto 1$, $4 \mapsto 2$, $5 \mapsto 2$ go down along every step of $H$?`, [r`Check each arrow: the number at its head must be smaller than at its tail.`]);
    lx(r`theorem half_lt (n : Nat) (h : 0 < n) : n / 2 < n := by`, r`Halving a positive number makes it smaller: the measure argument for binary search.`, r`  omega`, [r`‹omega› knows about division by a numeral.`]);
    md(r`
> [!note] The engine's own termination proof
> ChalkMath's simplifier never runs on a step budget. Every rule in its pipeline comes with a proof that it decreases a well-founded ordering on terms (‹pipelineOrdered› in the engine's Lean), the same argument as a measure, only the measure is an ordering on expression trees.
`);
    md(r`
> [!summary]
> Well-founded means no infinite descent; on a finite set, no cycle. A measure into the naturals proves it, a cycle refutes it, and Lean's ‹termination_by› is a measure written down.
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
/** Chapter `k` as lesson cells: its heading, the goal, the cells the earlier chapters left, then the chapter. */
function chapter(L, k, goal, opening = []) {
  const cells = book.slice(...chapters[k]).map(fresh);
  L.cells.push(cells[0]);
  L.md(goal);
  for (const c of opening) L.cells.push(fresh(c));
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

  add("01-partial-orders.chalk", "Relations and partial orders", "Partial orders on numbers, divisibility and sets, Hasse diagrams, and the definitions in Lean.", (L) => {
    chapter(L, 0, r`
> [!goal]
> Recognize a partial order, compute in one (divisibility, subsets, chains), read its Hasse diagram, and state the definitions in Lean.
`, [book[1]]);
    L.sec("Exercises");
    L.md(r`Answer ‹true› or ‹false›, or with an element or a set.`);
    L.ex("le(D, 4, 12)", r`In the divisors of 12, is $4 \le 12$?`, [r`$a \le b$ here means $a$ divides $b$.`]);
    L.ex("le(D, 4, 6)", r`In the divisors of 12, is $4 \le 6$?`, [r`Does 4 divide 6?`]);
    L.ex("le(P3, {a}, {a, b})", r`Among the subsets of $\{a, b, c\}$, is $\{a\} \le \{a, b\}$?`, [r`The order is inclusion.`]);
    L.md(r`
> [!summary]
> A partial order is reflexive, antisymmetric and transitive; not every two elements need be comparable. Divisibility, inclusion and $\le$ on numbers are the first examples, and a Hasse diagram draws one by its covers.
`);
  });

  add("02-special-elements.chalk", "Special elements and monotone maps", "Least, greatest, maximal and minimal elements, bounds, joins and meets, and monotone maps.", (L) => {
    chapter(L, 1, r`
> [!goal]
> Find the extremal elements and bounds of a poset, compute joins and meets (and see when they do not exist), and decide whether a map is monotone.
`);
    L.sec("Exercises");
    L.ex("upper(E, {c, d})", r`List the upper bounds of $c$ and $d$ in $E$.`, [r`Everything above both $c$ and $d$.`]);
    L.ex("minimal(T)", r`List the minimal elements of $T$.`, [r`Nothing is strictly below a minimal element.`]);
    L.ex("join(D, 4, 6)", r`In the divisors of 12, what is $4 \vee 6$?`, [r`The least common multiple.`]);
    L.ex("monotone(D, k)", r`Is the map ‹k› monotone? Answer ‹true› or ‹false›.`, [r`‹k› sends 2 to 3 and fixes everything else. Look at $2 \le 4$.`]);
    L.md(r`
> [!summary]
> A maximum is above everything; a maximal element has nothing above it. The join of two elements is their least upper bound, when there is one. A monotone map keeps the order, and those are the maps whose fixed points the next lessons find.
`);
  });

  add("03-lattices.chalk", "Lattices", "Posets where every pair has a join and a meet: duality, the standard examples, and distributivity.", (L) => {
    chapter(L, 2, r`
> [!goal]
> Decide whether a poset is a lattice, compute in the standard ones (Booleans, powersets, divisors), and see duality and the two lattices that are not distributive.
`);
    L.sec("Exercises");
    L.ex("lattice(V)", r`Is the "vee" $V$ a lattice?`, [r`Do $b$ and $c$ have a join?`]);
    L.ex("meet(D, 4, 6)", r`In the divisors of 12, what is $4 \wedge 6$?`, [r`The greatest common divisor.`]);
    L.ex("join(Dop, 4, 6)", r`In the dual of the divisors of 12, what is $4 \vee 6$?`, [r`In the dual, joins are the original meets.`]);
    L.md(r`
> [!summary]
> A lattice has every pairwise join and meet. Turning the order upside down swaps them (duality). Booleans, powersets and divisors are lattices; the vee is not, and M₃ and N₅ are lattices that fail the distributive law.
`);
  });

  add("04-fixed-points.chalk", "Complete lattices and fixed points", "Complete lattices, the Knaster–Tarski theorem, and least fixed points by iteration.", (L) => {
    chapter(L, 3, r`
> [!goal]
> State and prove the Knaster–Tarski theorem, and compute least and greatest fixed points of monotone maps on finite lattices by iterating from the bottom and the top.
`);
    L.sec("Exercises");
    L.ex("lfp(D, f)", r`What is the least fixed point of ‹f›?`, [r`Start at $\bot = 1$ and apply ‹f› until nothing changes.`]);
    L.ex("gfp(D, f)", r`And the greatest?`, [r`Start at $\top = 12$.`]);
    L.ex("fixpoints(D, one)", r`List the fixed points of ‹one›, the map sending everything to 1.`, []);
    L.md(r`
> [!summary]
> On a complete lattice every monotone map has a least and a greatest fixed point. On a finite one they are reached by iterating from $\bot$ and from $\top$: the Kleene chain, every element of which is below every fixed point.
`);
  });

  add("05-semilattices.chalk", "Semilattices as algebras", "Join as an operation with laws: associative, commutative, idempotent, and the order it gives back.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Semilattices as algebras");
    md(r`
> [!goal]
> Read a join as an operation, check its three laws on a table (with the elements that break them when they fail), and recover the order from the operation.
`);
    md(r`The join of a lattice is an operation $x \vee y$ on its elements, and it obeys laws whatever the lattice. Turned around, any operation with those laws defines an order.`);
    md(r`
> [!definition] Semilattice
> A **semilattice** is a set with an operation $\cdot$ that is **associative** ($(x \cdot y) \cdot z = x \cdot (y \cdot z)$), **commutative** ($x \cdot y = y \cdot x$) and **idempotent** ($x \cdot x = x$).
`);
    sec("Operations as tables");
    md(r`An operation on a finite set is its table: row $x$, column $y$ holds $x \cdot y$. Here is $\max$ on $\{0, 1, 2\}$.`);
    m("let M = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])");
    m("semilattice(M)", { work: true });
    m("identity(M)");
    md(r`Union on the subsets of $\{a, b\}$ is another; set elements are written as sets:`);
    m("let U = op({{}, {a}, {b}, {a,b}}; [{}, {a}, {b}, {a,b}; {a}, {a}, {a,b}, {a,b}; {b}, {a,b}, {b}, {a,b}; {a,b}, {a,b}, {a,b}, {a,b}])");
    m("semilattice(U)");
    sec("The order an operation gives");
    md(r`
> [!theorem] A semilattice is a partial order
> Define $x \le y$ when $x \cdot y = y$. Idempotence makes it reflexive, commutativity antisymmetric, associativity transitive, and then $x \cdot y$ is the least upper bound of $x$ and $y$.
`);
    m("order(M)", { work: true });
    m("order(U)");
    md(r`The union table gives back the powerset's diamond. The engine's ‹order› is proved to produce a partial order whose join is the operation (‹semilattice_order›).`);
    sec("When a law fails");
    md(r`Rock, paper, scissors: $x \cdot y$ is the winner of $x$ against $y$. Commutative and idempotent, but not associative, so there is no order behind it. The table marks the four entries the two sides of the law read.`);
    m("let RPS = op({r, p, s}; [r, p, r; p, p, s; r, s, s])");
    m("commutative(RPS)");
    m("associative(RPS)", { work: true });
    m("order(RPS)");
    md(r`"Keep the newer one", $x \cdot y = y$, is associative and idempotent but not commutative: the result depends on the order the values arrive in.`);
    m("let K = op({a, b, c}; [a, b, c; a, b, c; a, b, c])");
    m("commutative(K)", { work: true });
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
    ex("associative(K)", r`Is "keep the newer one" associative?`, [r`$(x \cdot y) \cdot z = z$ and $x \cdot (y \cdot z) = z$.`]);
    md(r`
> [!summary]
> A semilattice is an associative, commutative, idempotent operation, and it is the same thing as an order with joins: $x \le y$ exactly when $x \cdot y = y$. A table decides the three laws, and a failure is a triple or a pair you can point at.
`);
  });

  add("06-merges.chalk", "A merge is a join", "Max, union, last-writer-wins and records merged field by field: why replicas that merge this way agree.", ({ sec, md, m, ex, lean, lx }) => {
    sec("A merge is a join");
    md(r`
> [!goal]
> See why a merge that is a join can be applied in any order and any number of times with the same result, build merges for numbers, flags, timestamped values and records, and prove their laws in Lean.
`);
    md(r`Two copies of some data (replicas) change independently and later exchange states. Each **merges** the other's state into its own. They end up equal, whatever order the messages arrive in and however often they are repeated, exactly when the merge is associative, commutative and idempotent: a join.`);
    sec("Order and repetition do not matter");
    m("let M = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])");
    m("fold(M; 2, 0, 1)", { work: true });
    m("fold(M; 1, 0, 2, 2, 0)", { work: true });
    md(r`Associativity lets the merges be grouped any way, commutativity lets them arrive in any order, and idempotence lets a message be delivered twice.`);
    sec("Records merge field by field");
    md(r`
> [!theorem] Products of semilattices
> If $A$ and $B$ are semilattices, so is $A \times B$ with $(a, b) \cdot (a', b') = (a \cdot a', b \cdot b')$. Its order is the product order.
`);
    m("let C2 = chain(2)");
    m("let R2 = product(C2, C2)");
    m("join(R2, (0, 1), (1, 0))", { work: true });
    m("let JR = joinop(R2)");
    m("semilattice(JR)");
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
> Without the tie-break ("keep the second on a tie") the merge is not commutative: two replicas that each received the other's write last would keep different values forever.
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
`);
  });

  add("07-distributive.chalk", "Distributive and Boolean lattices", "M₃ and N₅ as the witnesses, complements, and the Boolean lattices of sets and squarefree divisors.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Distributive and Boolean lattices");
    md(r`
> [!goal]
> Decide distributivity with a witness triple when it fails, find complements, and recognize Boolean lattices.
`);
    md(r`
> [!definition] Distributive lattice
> A lattice is **distributive** when $x \wedge (y \vee z) = (x \wedge y) \vee (x \wedge z)$ for all $x, y, z$ (the dual law then follows).
`);
    m("let M3 = poset({bot, a, b, c, top}; bot < a, bot < b, bot < c, a < top, b < top, c < top)");
    m("distributive(M3)", { work: true });
    m("let N5 = poset({bot, p, q, r, top}; bot < p, bot < q, q < r, p < top, r < top)");
    m("distributive(N5)", { work: true });
    md(r`
> [!theorem] Birkhoff
> A lattice is distributive exactly when it contains neither M₃ nor N₅ as a sublattice. They are the witnesses every failure contains.
`);
    m("let D = divisors(12)");
    m("distributive(D)");
    sec("Complements");
    md(r`
> [!definition] Complement
> In a lattice with $\bot$ and $\top$, a **complement** of $x$ is a $y$ with $x \vee y = \top$ and $x \wedge y = \bot$. In a distributive lattice an element has at most one.
`);
    m("complement(M3, a)", { work: true });
    m("complement(D, 4)");
    m("complement(D, 2)");
    md(r`$2$ has no complement among the divisors of 12: any $y$ with $\operatorname{lcm}(2, y) = 12$ is a multiple of 4 or of 3 times 4, and then $\gcd(2, y) = 2$.`);
    sec("Boolean lattices");
    md(r`
> [!definition] Boolean lattice
> A **Boolean lattice** is distributive and complemented. The subsets of a set are the model: complement is set complement.
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
    md(r`
> [!summary]
> Distributivity can fail, and M₃ and N₅ are why. Boolean lattices are distributive with complements; the subsets of a set, and the divisors of a squarefree number, are the examples.
`);
  });

  add("08-access-decisions.chalk", "Access decisions", "Combining permit and deny: deny-overrides and permit-overrides are joins, first-applicable is not commutative.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Access decisions");
    md(r`
> [!goal]
> Model the combining algorithms of an access-control policy as operations, see which are semilattices (so rule order cannot matter) and which are not, and prove that adding a rule never turns a deny into a permit.
`);
    md(r`An access policy has many rules. For a given request each rule says **permit**, **deny**, or **not applicable** (na), and a *combining algorithm* turns their answers into one. The standard ones (XACML's) are operations on $\{\mathrm{na}, \mathrm{permit}, \mathrm{deny}\}$, so they are tables with laws.`);
    sec("Deny overrides");
    md(r`A deny anywhere wins; otherwise a permit; otherwise not applicable.`);
    m("let DO = op({na, permit, deny}; [na, permit, deny; permit, permit, deny; deny, deny, deny])");
    m("semilattice(DO)", { work: true });
    m("order(DO)", { work: true });
    m("identity(DO)");
    md(r`It is the join of the chain $\mathrm{na} < \mathrm{permit} < \mathrm{deny}$: a rule's decision can only push the result up. Because it is a semilattice, the decision for a list of rules does not depend on their order or grouping:`);
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
`);
  });

  add("09-information-flow.chalk", "Information flow", "Denning's lattice of security classes: data may only flow up, and a computation's output gets the join of its inputs' classes.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Information flow");
    md(r`
> [!goal]
> Build a lattice of security classes as a product, label data with classes, and check that every flow of information goes up the lattice; then prove the rule for combining inputs.
`);
    md(r`
> [!definition] Security classes (Denning)
> A **security class** is a level and a set of categories: $(\mathrm{high}, \{\mathrm{fin}\})$ is high-level data about finance. Classes are ordered componentwise, level by level and categories by inclusion, so they form a product lattice. Information may flow from class $a$ to class $b$ only when $a \le b$.
`);
    m("let Lv = poset({low, high}; low < high)");
    m("let Cat = subsets({fin, hr})");
    m("let SC = product(Lv, Cat)");
    m("lattice(SC)");
    sec("Combining inputs");
    md(r`A value computed from two inputs may reveal both, so its class must be at least each of theirs: at least their join.`);
    m("join(SC, (low, {fin}), (high, {}))", { work: true });
    m("join(SC, (high, {hr}), (low, {fin}))");
    sec("Checking flows");
    md(r`A program's flows form a relation: $x \to y$ when information about $x$ reaches $y$. It is secure when every flow goes up. A report built from salaries and then summarized for an audit:`);
    m("let Fl = rel({salary, report, audit}; salary->report, report->audit)");
    m("secure(SC, Fl; salary->(high, {hr}), report->(high, {hr, fin}), audit->(low, {fin}))", { work: true });
    md(r`The audit summary is labelled $(\mathrm{low}, \{\mathrm{fin}\})$, below the report it reads: the flow goes down, and the graph marks it. Raising the audit's class fixes it:`);
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
`);
  });

  add("10-galois.chalk", "Closure operators and Galois connections", "Closure operators, Galois connections between two orders, and the concept lattice of a formal context.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Closure operators and Galois connections");
    md(r`
> [!goal]
> Recognize closure operators and Galois connections, see how one gives the other, and build the concept lattice of a small formal context.
`);
    md(r`
> [!definition] Closure operator
> A map $c$ on a poset is a **closure operator** when it is **extensive** ($x \le c(x)$), **monotone**, and **idempotent** ($c(c(x)) = c(x)$). Its fixed points are the **closed** elements.
`);
    m("let D = divisors(12)");
    m("let cl = map(D; 3->6)");
    m("closureop(D, cl)", { work: true });
    m("fixpoints(D, cl)");
    m("let bad = map(D; 2->1)");
    m("closureop(D, bad)", { work: true });
    sec("Galois connections");
    md(r`
> [!definition] Galois connection
> Monotone maps $f : P \to Q$ and $g : Q \to P$ form a **Galois connection** when $f(x) \le y \iff x \le g(y)$ for all $x$ and $y$. Then $g \circ f$ is a closure operator on $P$.
`);
    md(r`Halving and doubling: $\lceil x / 2 \rceil \le y$ exactly when $x \le 2y$.`);
    m("let C7 = chain(7)");
    m("let C4 = chain(4)");
    m("let half = map(C7, C4; 0->0, 1->1, 2->1, 3->2, 4->2, 5->3, 6->3)");
    m("let dbl = map(C4, C7; 0->0, 1->2, 2->4, 3->6)");
    m("galois(C7, C4, half, dbl)", { work: true });
    m("let same = map(C4, C7; 0->0, 1->1, 2->2, 3->3)");
    m("galois(C7, C4, half, same)", { work: true });
    sec("Formal concept analysis");
    md(r`
> [!definition] Formal context, concept
> A **context** lists objects, attributes, and which object has which. A **concept** is a set of objects and a set of attributes that determine each other: exactly the objects having all those attributes, and exactly the attributes they all share. Ordered by their objects, the concepts form a complete lattice.
`);
    m("let A = context({duck, eagle, dog, bat}, {flies, mammal, bird}; duck->flies, duck->bird, eagle->flies, eagle->bird, dog->mammal, bat->flies, bat->mammal)");
    m("concepts(A)", { work: true });
    md(r`The two maps "the attributes these objects share" and "the objects having these attributes" form a Galois connection (reversing the order), and the concepts are its closed pairs. The bat sits below both "flies" and "mammal": the lattice finds the category nobody named.`);
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
    ex("closureop(D, bad)", r`Is ‹bad› a closure operator? Answer ‹true› or ‹false›.`, [r`Is $2 \le$ ‹bad›$(2)$?`]);
    ex("galois(C7, C4, half, dbl)", r`Do halving (rounded up) and doubling form a Galois connection?`, []);
    md(r`
> [!summary]
> A closure operator adds what a property forces and stops; a Galois connection is a pair of maps that are "adjoint", and composing them gives a closure. Formal concept analysis is a Galois connection between objects and attributes, and its closed pairs are a lattice of concepts.
`);
  });

  add("11-fixed-points-in-practice.chalk", "Fixed points in practice", "Apply until nothing changes: reachability as a least fixed point, and why the iteration stops.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Fixed points in practice");
    md(r`
> [!goal]
> Recognize "apply until nothing changes" as computing a least fixed point, compute one on a lattice of sets, and see why it stops.
`);
    md(r`Many algorithms keep applying a step until it has no effect: closing a set under rules, propagating facts, computing what can be reached. When the step is monotone and starts from the bottom, the result is the **least** fixed point (Kleene), and it is the smallest set closed under the step.`);
    sec("Reachability");
    md(r`The nodes reachable from $a$ in the graph $a \to b \to c$, $d \to a$ are the least set $S$ with $a \in S$ and closed under successors: the least fixed point of $f(S) = \{a\} \cup S \cup \mathrm{succ}(S)$ on the subsets of $\{a, b, c, d\}$.`);
    m("let P4 = subsets({a, b, c, d})");
    m(`let reach = map(P4; ${reachMap})`);
    m("monotone(P4, reach)");
    m("lfp(P4, reach)", { step: 0 });
    md(r`Each step adds one more layer of successors: $\varnothing$, $\{a\}$, $\{a, b\}$, $\{a, b, c\}$, and then nothing changes. $d$ is not reachable from $a$.`);
    sec("Why it stops");
    md(r`
> [!theorem] The ascending chain condition
> If every increasing chain $x_0 \le x_1 \le \cdots$ in a lattice is eventually constant (always true on a finite lattice), then iterating a monotone $f$ from $\bot$ reaches a fixed point after finitely many steps, and it is the least one.
`);
    md(r`On the subsets of an $n$-element set a chain has at most $n + 1$ distinct elements, so the iteration takes at most $n$ steps. In Lean, every iterate is below every fixed point above the start:`);
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
    md(r`
> [!summary]
> "Apply until nothing changes" computes a least fixed point when the step is monotone and starts from the bottom. On a finite lattice it always stops, and what it finds is the smallest solution: everything forced, nothing more.
`);
  });

  add("12-propagators.chalk", "The propagator model", "Cells that only gain information, in a lattice; propagators as monotone functions between them.", ({ sec, md, m, ex, lean, lx }) => {
    sec("The propagator model");
    md(r`
> [!goal]
> Model partial information as a lattice, merges as joins, and computations as monotone propagators; see why a propagator must never guess.
`);
    md(r`
> [!definition] Cells and propagators
> A **cell** holds what is known so far about a value, an element of a lattice ordered by information. New information is **merged** in with the join, so a cell's content only rises. A **propagator** reads cells and writes its conclusions to another cell; a network runs propagators until nothing changes.
`);
    md(r`The simplest information lattice for a number: nothing known, one of the values, or a contradiction.`);
    m("let F = poset({unknown, 1, 2, 3, conflict}; unknown < 1, unknown < 2, unknown < 3, 1 < conflict, 2 < conflict, 3 < conflict)");
    m("lattice(F)");
    m("join(F, unknown, 2)", { work: true });
    m("join(F, 2, 3)", { work: true });
    sec("Propagators are monotone");
    md(r`A propagator must give at least as much output when it knows more. "Add one" is monotone; "guess 1 when nothing is known" is not, because learning the value is 2 would make it take back its answer.`);
    m("let inc = map(F; 1->2, 2->3, 3->conflict)");
    m("monotone(F, inc)");
    m("let guess = map(F; unknown->1)");
    m("monotone(F, guess)", { work: true });
    md(r`
> [!theorem] Networks of monotone propagators converge
> Each propagator's output only rises as its inputs rise, and cells only rise under merges, so the cells' contents form an ascending chain. On a lattice with no infinite ascending chains the network reaches a fixed point, the least one, whatever order the propagators run in.
`);
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
> Partial information is a lattice; merging is the join; propagators are monotone maps. A network of them converges to the least fixed point, whatever order they run in, and a propagator that guesses breaks that.
`);
  });

  add("13-propagator-network.chalk", "A propagator network in Lean", "Mutable cells that only grow, a scheduler that runs to quiescence, and a constraint that runs in every direction.", ({ sec, md, lean, lx }) => {
    sec("A propagator network in Lean");
    md(r`
> [!goal]
> Build a running propagator network in Lean: cells as references that merge, propagators as small programs, and a loop that runs them until nothing changes.
`);
    md(r`A cell is a mutable reference whose writes merge. Writing reports whether the content changed, which is how the scheduler knows when to stop.`);
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
> Edit ‹sumExample›: start $z$ at ‹Flat.known 2› instead. The subtraction $2 - 3$ is impossible, $y$ becomes a contradiction, and the network still stops.
`);
    md(r`
> [!note] Why the lattice is load-bearing
> The loop stops because each write either changes nothing or moves a cell up a lattice with no infinite ascending chains, and it gives the same answer in any order because merges are joins. Replace the merge with "overwrite" and both guarantees are gone.
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
> A propagator network is cells that merge, propagators that read and write them, and a loop that runs until quiescence. Monotone propagators over a lattice make the loop stop, and make its answer independent of the order things run in.
`);
  });

  add("14-intervals.chalk", "The interval lattice", "Bounds on a number as partial information: intersection as the merge, and interval arithmetic propagators.", ({ sec, md, m, ex, lean, lx }) => {
    sec("The interval lattice");
    md(r`
> [!goal]
> Represent partial knowledge of a number as an interval, merge intervals by intersecting them, and propagate bounds through arithmetic.
`);
    md(r`"The value is between 1 and 5" is partial information, more than "unknown" and less than "it is 3". Two such facts merge into their **intersection**; an empty intersection is a contradiction. Ordered by information, smaller intervals are higher.`);
    md(r`On the integers $0$ to $2$ (write ‹i01› for $[0, 1]$):`);
    m("let I = poset({i02, i01, i12, i00, i11, i22, empty}; i02 < i01, i02 < i12, i01 < i00, i01 < i11, i12 < i11, i12 < i22, i00 < empty, i11 < empty, i22 < empty)");
    m("lattice(I)");
    m("join(I, i01, i12)", { work: true });
    m("join(I, i00, i22)", { work: true });
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
    md(r`From $x \in [1, 5]$, $y \in [2, 3]$ and $x + y \in [0, 6]$: $z \ge 3$, so $z \in [3, 6]$, and $x = z - y \le 4$, so $x \in [1, 4]$.`);
    lx(r`theorem Ival.add_mono (a a' b b' : Ival) (ha : a.within a') (hb : b.within b') :
    (Ival.add a b).within (Ival.add a' b') := by`, r`Prove that interval addition is monotone: narrower summands give a narrower sum.`, r`  simp only [Ival.within, Ival.add] at *
  omega`, [r`Unfold ‹Ival.within› and ‹Ival.add› everywhere with ‹simp only›; what is left is linear arithmetic.`]);
    sec("Exercises");
    ex("join(I, i02, i12)", r`Merge $[0, 2]$ with $[1, 2]$. Answer with the element's name.`, [r`Intersect them.`]);
    ex("join(I, i01, i22)", r`Merge $[0, 1]$ with $[2, 2]$.`, [r`Do they overlap?`]);
    md(r`
> [!summary]
> Intervals are partial information about numbers; merging is intersection, and an empty one is a contradiction. Interval arithmetic gives monotone propagators, so a network of them narrows every bound as far as the constraints force, and stops.
`);
  });

  add("15-capstones.chalk", "Capstones: Sudoku and type inference", "A Sudoku solver and a type checker, both as propagator networks over lattices of partial information.", ({ sec, md, lean, lx }) => {
    sec("Capstones: Sudoku and type inference");
    md(r`
> [!goal]
> Solve a Sudoku and infer the types of a small program with the same machinery: cells of partial information, merges that are joins, and propagators run to a fixed point.
`);
    sec("Sudoku");
    md(r`Each square holds the set of digits still possible: a lattice ordered by reverse inclusion, where merging intersects. A square whose set is down to one digit removes that digit from its **peers**, the squares sharing its row, column or box. Here is a 4×4 grid; candidates are bits, so intersection is bitwise and.`);
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
    md(r`
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
const COUNTER = `let C = system(
  var x in 0..3
  var y in 0..3
  init x = 0 ∧ y = 0
  action inc when x < 3 do x := x + 1
  action move when x > 0 ∧ y < 3 do x := x - 1, y := y + 1
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
const waiter = (name, fairness) => `let ${name} = system(
  var p in {idle, crit}
  var q in {wait, crit}
  var lock in bool
  init p = idle ∧ q = wait ∧ lock = false
  action penter when p = idle ∧ lock = false do lock := true, p := crit
  action pexit when p = crit do p := idle, lock := false
  ${fairness}action qenter when q = wait ∧ lock = false do lock := true, q := crit
)`;
const TS_LEAN = r`/-- A transition system on states σ: which states are initial, and which steps are allowed. -/
structure TS (σ : Type) where
  init : σ → Prop
  step : σ → σ → Prop

/-- The states a system can reach: an initial state, or a step from a reachable one. -/
inductive Reachable {σ : Type} (T : TS σ) : σ → Prop where
  | init {s : σ} : T.init s → Reachable T s
  | step {s t : σ} : Reachable T s → T.step s t → Reachable T t`;

course("systems", "Transition systems, invariants and temporal logic",
  "State machines and their reachable states; invariants with counterexample traces and inductive proofs; mutual exclusion, safety and liveness under fairness; temporal logic as fixed points; happens-before, effectively-once delivery, and refinement; rewriting systems, and retries under failure.",
  "Distributed systems", (add) => {

  add("01-state-machines.chalk", "State machines and executions", "Variables, an initial condition and guarded actions; executions as traces; the graph of reachable states.", ({ sec, md, m, ex, lean, lx }) => {
    sec("State machines and executions");
    md(r`
> [!goal]
> Describe a system by its variables, its initial states and its actions; run it step by step; and draw every state it can reach.
`);
    md(r`
> [!definition] Transition system
> A **state** gives each variable a value. A **transition system** says which states are **initial** and which **steps** from a state to the next are allowed. An **action** is a kind of step: a **guard** (when it may happen) and **updates** (what it changes, all at once). An **execution** is a sequence of states, each a step from the one before; a state is **reachable** when some execution from an initial state gets there.
`);
    md(r`A system cell lists its parts on separate lines (in a cell, Shift+Enter starts a new line and Enter runs it). A traffic light:`);
    m(`let Light = system(
  var c in {red, green, yellow}
  init c = red
  action go when c = red do c := green
  action slow when c = green do c := yellow
  action stop when c = yellow do c := red
)`);
    m("trace(Light; go, slow, stop, go)", { step: 0 });
    md(r`An action whose guard fails cannot be taken; asking for it is an error that says which condition failed.`);
    m("trace(Light; slow)");
    sec("The reachable states");
    md(r`Two variables: ‹inc› counts up, ‹move› moves one unit from ‹x› to ‹y›. The graph is drawn in rows, the initial state on top and each row one step further.`);
    m(COUNTER);
    m("states(C)");
    m("reach(C, y = 3)", { step: 0 });
    md(r`A shortest way to $y = 3$ takes six steps: the search is breadth-first, so the first trace it finds is a shortest one.`);
    sec("In Lean");
    md(r`The same notions as definitions: a system is its initial predicate and its step relation, and reachability is the least set closed under steps.`);
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
    md(r`Answer with a number, ‹true› or ‹false›, or a state written as ‹x = 1 ∧ y = 2›.`);
    ex("states(Light)", r`How many states can the traffic light reach?`, []);
    ex("trace(C; inc, move, inc)", r`Run ‹inc›, ‹move›, ‹inc› from the initial state of ‹C›. Which state do you reach?`, [r`Updates in one action happen together: ‹move› takes one from ‹x› and gives it to ‹y›.`]);
    ex("reach(C, x = 3 ∧ y = 3)", r`Can ‹C› reach $x = 3, y = 3$?`, [r`Count up to 3, move three times, count up again.`]);
    md(r`
> [!summary]
> A transition system is states, initial states and steps; actions describe steps by guards and updates. Its reachable states form a graph, and an execution is a path in it from an initial state.
`);
  });

  add("02-invariants.chalk", "Invariants and induction", "Properties of every reachable state: refuted by a shortest trace, proved by induction, and strengthened when induction fails.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Invariants and induction");
    md(r`
> [!goal]
> Decide whether a property holds in every reachable state, read the shortest counterexample when it does not, and prove it by induction, strengthening it when the induction fails.
`);
    md(r`
> [!definition] Invariant
> A state formula is an **invariant** when it holds in every reachable state. A counterexample is an execution from an initial state to a state where it fails.
`);
    m(COUNTER);
    m("invariant(C, x + y ≤ 3)", { step: 0 });
    m("invariant(C, y ≤ 3)");
    sec("Inductive invariants");
    md(r`
> [!theorem] Proof by induction
> If $I$ holds in every initial state, and every step from a state where $I$ holds leads to one where $I$ holds, then $I$ holds in every reachable state. Such an $I$ is **inductive**.
`);
    md(r`Inductiveness is checked over *every* state, reachable or not, so it needs no search, and it is a proof. But an invariant need not be inductive. Two counters stepping together:`);
    m(`let Pair = system(
  var x in 0..6
  var y in 0..6
  init x = 0 ∧ y = 0
  action step when x < 5 do x := x + 1, y := y + 1
)`);
    m("invariant(Pair, y ≤ 5)");
    m("inductive(Pair, y ≤ 5)", { work: true });
    md(r`The counterexample to induction is a state that no execution reaches ($y = 5$ with $x < 5$): $y \le 5$ is true but too weak to prove itself. **Strengthen** it with what makes it true, that $x$ and $y$ move together:`);
    m("inductive(Pair, x = y ∧ y ≤ 5)");
    sec("In Lean");
    lx(`theorem invariant_of_inductive {σ : Type} (T : TS σ) (I : σ → Prop)
    (hinit : ∀ s, T.init s → I s) (hstep : ∀ s t, I s → T.step s t → I t) :
    ∀ s, Reachable T s → I s := by`, r`Prove the induction principle for invariants: by induction on reachability.`, `  intro s h
  induction h with
  | init hs => exact hinit _ hs
  | step _ hst ih => exact hstep _ _ ih hst`, [r`‹intro s h›, then ‹induction h› gives a case per constructor of ‹Reachable›.`, r`In the ‹step› case, the hypothesis says ‹I› holds before the step.`]);
    lean(r`theorem counter_le_three : ∀ s, Reachable counter s → s ≤ 3 := by
  apply invariant_of_inductive
  · intro s hs; simp [counter] at hs; omega
  · intro s t _ hst; simp [counter] at hst; omega`);
    sec("Exercises");
    ex("inductive(Pair, y ≤ 5)", r`Is $y \le 5$ inductive for ‹Pair›?`, []);
    ex("inductive(Pair, x = y ∧ x ≤ 5)", r`Is $x = y \land x \le 5$ inductive?`, [r`Initially both are 0; the only step adds one to each, and only when $x < 5$.`]);
    ex("invariant(C, x ≤ 3)", r`Is $x \le 3$ an invariant of ‹C›?`, []);
    md(r`
> [!summary]
> An invariant holds in every reachable state; a shortest trace refutes it. An inductive invariant proves itself in one step, over all states; when induction fails at an unreachable state, strengthen the invariant with the fact that rules that state out.
`);
  });

  add("03-mutual-exclusion.chalk", "Mutual exclusion", "A check-then-act race as a stepped trace, the fix, its inductive proof, and the same model in TLA+.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Mutual exclusion");
    md(r`
> [!goal]
> Find a race by model checking, fix it, prove the fix by an inductive invariant, and see the model in TLA+.
`);
    md(r`A service must run at most one job per customer at a time. Each worker checks that no job is running, then starts one: **check, then act**. Two workers, one lock:`);
    m(`let Race = system(
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
)`);
    md(r`Step through the counterexample: both workers check while the lock is free, then both take it.`);
    m("invariant(Race, ¬(p = crit ∧ q = crit))", { step: 0 });
    sec("The fix");
    md(r`Make the check and the taking one action, as a compare-and-set or a database's conditional write does:`);
    m(LOCKS);
    m("invariant(Fix, ¬(p = crit ∧ q = crit))");
    md(r`The model checker has tried every reachable state. A proof covers every state at once: the property is not inductive by itself (from an unreachable state where one is inside without the lock, the other can enter), but it is once strengthened with "whoever is inside holds the lock":`);
    m("inductive(Fix, ¬(p = crit ∧ q = crit))", { work: true });
    m("inductive(Fix, (p = crit → lock = true) ∧ (q = crit → lock = true) ∧ ¬(p = crit ∧ q = crit))");
    sec("In TLA+");
    md(`The same model in TLA+, for the TLC model checker:

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

The primed variables are the next state's; ‹UNCHANGED› says what an action leaves alone, which here is implicit.`);
    sec("In Lean");
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
    ex("reach(Fix, p = crit ∧ q = crit)", r`Can both workers be inside at once in ‹Fix›?`, []);
    ex("reach(Race, p = crit ∧ q = crit)", r`And in ‹Race›?`, []);
    md(r`
> [!summary]
> Check-then-act is a race whenever the check and the act are separate steps: the model checker finds the interleaving and shows it step by step. The fix makes them one step, and an inductive invariant (strengthened with "inside means holding the lock") proves it for every state.
`);
  });

  add("04-safety-liveness.chalk", "Safety and liveness", "Nothing bad happens; something good eventually does. Deadlocks, lassos, and weak and strong fairness.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Safety and liveness");
    md(r`
> [!goal]
> Tell safety properties from liveness properties, find deadlocks, and decide "eventually" under fairness, reading a lasso when it fails.
`);
    md(r`
> [!definition] Safety and liveness
> A **safety** property says nothing bad ever happens; it is refuted by a finite trace (invariants are safety properties). A **liveness** property says something good eventually happens; it is refuted by an infinite execution, which on a finite system is a **lasso**: a path to a loop that repeats forever.
`);
    sec("Deadlock");
    md(r`Two workers each need two forks, and take them in opposite orders:`);
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
    m("deadlock(Forks)", { step: 0 });
    sec("Fairness");
    md(r`Will a waiting worker ever get in? Not if the scheduler never lets it. A **fair** action is one the scheduler may not starve: **weakly fair** if it stays enabled it is taken; **strongly fair** if it is enabled again and again it is taken.`);
    m(waiter("W", "fair "));
    m("eventually(W, q = crit)", { step: 0 });
    md(r`Under weak fairness ‹q› can starve: ‹p› keeps taking the lock, so ‹qenter› is enabled only now and then, never continuously. Strong fairness rules that out:`);
    m(waiter("S", "strong fair "));
    m("eventually(S, q = crit)");
    sec("In Lean");
    md(r`Termination is liveness too, and its proof is a measure: a natural number that every step decreases cannot decrease forever.`);
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
    ex("deadlock(Forks)", r`Can the two workers deadlock?`, []);
    ex("eventually(W, q = crit)", r`Under weak fairness, does ‹q› always get in eventually?`, [r`Is ‹qenter› ever continuously enabled while ‹p› keeps cycling?`]);
    md(r`
> [!summary]
> Safety fails on a finite trace, liveness on an infinite one: a lasso. Deadlocks are reachable states with nothing to do. Whether "eventually" holds depends on fairness: weak fairness only protects actions that stay enabled, strong fairness those that are enabled again and again.
`);
  });

  add("05-temporal-logic.chalk", "Temporal logic as fixed points", "EF, AF, EG and AG on the lattice of state sets: least and greatest fixed points, computed by Kleene iteration.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Temporal logic as fixed points");
    md(r`
> [!goal]
> Read CTL formulas, and compute them as least and greatest fixed points on the lattice of sets of states, one Kleene round at a time.
`);
    md(r`
> [!definition] CTL
> **E** means "on some path" and **A** "on every path"; **F** means "eventually" and **G** "always"; **X** means "next". So $\mathsf{EF}\,\varphi$: some path reaches $\varphi$; $\mathsf{AG}\,\varphi$: $\varphi$ holds forever on every path; $\mathsf{AF}\,\varphi$: every path reaches $\varphi$; $\mathsf{EG}\,\varphi$: some path keeps $\varphi$ forever.
`);
    md(r`
> [!theorem] As fixed points
> On the lattice of sets of states, ordered by inclusion:
> $\mathsf{EF}\,\varphi$ is the least $Z$ with $Z = \varphi \cup \mathsf{EX}\,Z$, and $\mathsf{AG}\,\varphi$ the greatest $Z$ with $Z = \varphi \cap \mathsf{AX}\,Z$. Both maps are monotone, so by Knaster–Tarski the fixed points exist, and on a finite lattice Kleene iteration reaches them: from $\varnothing$ for the least, from all states for the greatest.
`);
    m(COUNTER);
    md(r`Step through the rounds: each adds the states one step further back from $y = 3$.`);
    m("ctl(C, EF y = 3)", { step: 0 });
    m("ctl(C, AG x + y ≤ 3)", { work: true });
    m("ctl(C, AF y = 3)");
    md(r`This is *Order and lattices*' fixed-point lesson applied: the lattice is the powerset of the states, and the monotone map is a predicate transformer.`);
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
    ex("ctl(C, EF x = 3 ∧ y = 3)", r`Does $\mathsf{EF}(x = 3 \land y = 3)$ hold initially?`, []);
    ex("ctl(C, AG y ≤ 3)", r`Does $\mathsf{AG}\,(y \le 3)$ hold?`, []);
    md(r`
> [!summary]
> Temporal operators are fixed points of predicate transformers on sets of states: "eventually" a least one, "always" a greatest. Model checking a finite system is computing them by Kleene iteration.
`);
  });

  add("06-happens-before.chalk", "Happens-before", "Events of several processes as a partial order, vector clocks that compute it, and concurrency as incomparability.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Happens-before");
    md(r`
> [!goal]
> Order the events of a distributed computation by what could have influenced what, compute that order with vector clocks, and recognize concurrent events.
`);
    md(r`
> [!definition] Happens-before (Lamport)
> Event $e$ **happens before** $f$ when $e$ comes earlier on the same process, or $e$ sends a message that $f$ receives, or a chain of these leads from $e$ to $f$. Events neither of which happens before the other are **concurrent**. Happens-before is a partial order.
`);
    md(r`Two processes; ‹a1› sends a message received at ‹b2›, and ‹b1› one received at ‹a3›:`);
    m("let E = events({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)");
    m("le(E, a1, b2)", { work: true });
    m("concurrent(E, a2, b2)");
    sec("Vector clocks");
    md(r`
> [!definition] Vector clock
> Each event gets a vector with an entry per process: how many of that process's events happen before it or are it. Then $e$ happens before $f$ exactly when $e$'s vector is below $f$'s in every entry.
`);
    m("clocks({a1, a2, a3}, {b1, b2}; a1->b2, b1->a3)");
    md(r`$a_2 = (2, 0)$ and $b_2 = (1, 2)$: neither is below the other, so they are concurrent. A process computes its clocks without a global clock: tick its own entry at each event, attach the vector to messages, and on receipt take the entrywise maximum.`);
    md(r`
> [!mistake]
> Messages cannot travel back in time: a pattern where an event would happen before itself is not a computation.
`);
    m("events({a1, a2}, {b1, b2}; a2->b1, b2->a1)");
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
    md(r`
> [!summary]
> Happens-before is the partial order of possible influence; vector clocks compute it locally, and two events are concurrent exactly when their clocks are incomparable.
`);
  });

  add("07-effectively-once.chalk", "Effectively-once delivery", "A channel that duplicates; a handler that is idempotent keeps the effect exactly once, one that is not double-applies.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Effectively-once delivery");
    md(r`
> [!goal]
> Model a channel that may deliver a message twice, and see that an idempotent handler gives each message its effect exactly once while a non-idempotent one does not.
`);
    md(r`A network that guarantees delivery retries, and retries duplicate. **Exactly-once delivery** is not something a network can promise; **effectively once** is: deliver at least once, and make applying a message twice the same as applying it once.`);
    m(`let Dup = system(
  var sent in 0..1
  var copies in 0..2
  var applied in 0..3
  init sent = 0 ∧ copies = 0 ∧ applied = 0
  action send when sent = 0 do sent := 1, copies := 1
  action duplicate when copies = 1 ∧ applied = 0 do copies := 2
  action deliver when copies > 0 do copies := copies - 1, applied := applied + 1
)`);
    m("invariant(Dup, applied ≤ sent)", { step: 0 });
    md(r`The handler adds each delivery to a count, so a duplicate doubles the effect. An idempotent handler records that the message was seen:`);
    m(`let Idem = system(
  var sent in 0..1
  var copies in 0..2
  var seen in bool
  init sent = 0 ∧ copies = 0 ∧ seen = false
  action send when sent = 0 do sent := 1, copies := 1
  action duplicate when copies = 1 do copies := 2
  action deliver when copies > 0 do copies := copies - 1, seen := true
)`);
    m("invariant(Idem, seen = true → sent = 1)");
    m("eventually(Idem, seen = true)");
    md(r`Here every run delivers, because delivering is all the system can do once the message is sent. In a real system other work competes for the same machine, and it is fairness that guarantees delivery: a liveness question for the channel, separate from the handler's safety.`);
    sec("In Lean");
    lean(r`/-- A handler that adds to a balance: a duplicate is applied twice. -/
def credit (balance : Nat) (amount : Nat) : Nat := balance + amount

example : credit (credit 0 5) 5 ≠ credit 0 5 := by decide

/-- A handler that records a message id in a set. -/
def record (seen : List Nat) (m : Nat) : List Nat := if m ∈ seen then seen else m :: seen`);
    lx(`theorem record_idempotent (seen : List Nat) (m : Nat) : record (record seen m) m = record seen m := by`, r`Prove that recording a message twice is recording it once.`, `  unfold record
  by_cases h : m ∈ seen <;> simp [h]`, [r`Unfold ‹record› and split on whether ‹m› was already seen.`]);
    sec("Exercises");
    ex("invariant(Dup, applied ≤ sent)", r`Does the counting handler apply each message at most once?`, []);
    ex("invariant(Idem, seen = true → sent = 1)", r`Is the idempotent handler's effect always backed by a sent message?`, []);
    md(r`
> [!summary]
> Retrying networks duplicate. Effectively-once processing is at-least-once delivery plus an idempotent handler, and idempotence is a one-line theorem about the handler, not a property of the network.
`);
  });

  add("08-refinement.chalk", "Refinement", "An implementation's steps are the specification's steps or stutters; and a normalization of operations proved sound.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Refinement");
    md(r`
> [!goal]
> Check that a detailed system implements an abstract one by mapping its states and matching its steps, and prove an operation-rewriting optimization sound against the semantics it preserves.
`);
    md(r`
> [!definition] Refinement
> A concrete system $C$ **refines** an abstract system $A$ under a mapping from $C$'s states to $A$'s when every initial state maps to an initial state, and every step of $C$ maps to a step of $A$ or to no change at all (a **stutter**). Then every behavior of $C$, seen through the mapping, is a behavior of $A$: properties proved of $A$ hold of $C$.
`);
    md(r`Two counters, abstracted to their sum:`);
    m("let Two = system(var a in 0..2; var b in 0..2; init a = 0 ∧ b = 0; action ta when a < 2 do a := a + 1; action tb when b < 2 do b := b + 1)");
    m("let Sum = system(var s in 0..4; init s = 0; action t when s < 4 do s := s + 1)");
    m("refines(Two, Sum; s := a + b)", { work: true });
    md(r`An implementation that bumps both at once takes a step the specification does not have:`);
    m("let Jump = system(var a in 0..2; var b in 0..2; init a = 0 ∧ b = 0; action both when a < 2 ∧ b < 2 do a := a + 1, b := b + 1)");
    m("refines(Jump, Sum; s := a + b)", { step: 0 });
    sec("Normalizing operations, soundly");
    md(r`A client queues operations on a key (create, update, delete) and sends them in a batch. An optimizer folds adjacent operations into one: $\mathsf{update}\,a;\ \mathsf{update}\,b$ becomes $\mathsf{update}\,b$. It must not change what the batch does to the store. That is refinement again, for a rewriting: every rewrite must leave the store's final state the same, from every starting state.`);
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
> "Create then delete cancels out" looks like a fine rewrite, and it is wrong: if the key already existed, the pair deletes it, and the empty batch would not. Lean finds the starting state:
`);
    lean(r`example : run (some 7) [.create 1, .delete] ≠ run (some 7) [] := by decide`);
    sec("Exercises");
    ex("refines(Jump, Sum; s := a + b)", r`Does ‹Jump› refine ‹Sum› under the sum mapping?`, []);
    ex("refines(Two, Sum; s := a + b)", r`Does ‹Two›?`, []);
    md(r`
> [!summary]
> Refinement checks that an implementation only does what the specification allows, up to stuttering. A rewriting of operations is sound when it refines the same way: same effect from every state, which a structural induction proves once for every batch.
`);
  });

  add("09-rewriting.chalk", "Rewriting systems", "The normalization of lesson 8 as rules on terms: rewriting to a normal form, termination by a measure, and confluence by critical pairs.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Rewriting systems");
    md(r`
> [!goal]
> Write an optimization as rewrite rules, show that rewriting always stops, and check that the order the rules are applied in cannot change the answer.
`);
    md(r`
> [!definition] Term, rule, normal form
> A **term** is a variable or a symbol applied to terms: ‹then(create(1), done)›. A **rule** $l \to r$ rewrites any instance of $l$, anywhere in a term, to the same instance of $r$. A **normal form** is a term no rule applies to.
`);
    md(r`Lesson 8's batch of operations is a term: ‹then(op, rest)› puts an operation before the rest, and ‹done› is the empty batch. Its combinations are four rules. The variables are ‹u›, ‹v›, ‹w›, ‹x›, ‹y› and ‹z›; anything else is a symbol or a constant.`);
    m("let N = rules(\n  cu: then(create(x), then(update(y), z)) -> then(create(y), z)\n  uu: then(update(x), then(update(y), z)) -> then(update(y), z)\n  xc: then(u, then(create(y), z)) -> then(create(y), z)\n  xd: then(u, then(delete, z)) -> then(delete, z)\n)");
    m("rewrite(N, then(create(1), then(update(2), then(update(3), then(delete, then(create(4), done))))))", { step: 0 });
    md(r`Each step names its rule and marks where in the term it applied: the leftmost-outermost redex, the first instance of a left side from the root.`);
    sec("Termination");
    md(r`
> [!definition] Terminating
> A system **terminates** when no term can be rewritten for ever. One way to show it: give every term a natural number that every step lowers. A natural number cannot go down for ever.
`);
    md(r`Here every rule drops an operation, so the size (the number of symbols) goes down:`);
    m("terminates(N)", { work: true });
    md(r`The size is not always enough. Addition on numerals ‹0›, ‹s(0)›, ‹s(s(0))›, … keeps the size in its second rule, but an **interpretation** that weighs ‹add›'s first argument double shows that it goes down:`);
    m("let A = rules(add(0, y) -> y; add(s(x), y) -> s(add(x, y)))");
    m("terminates(A)", { work: true });
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
    md(r`Two rules can only disagree where their left sides overlap. Each overlap gives a **critical pair**: the two results. If every pair rewrites to a common term (it is **joinable**), the system is locally confluent, and with termination, confluent (Newman's lemma).`);
    m("critical(N)", { work: true });
    md(r`
> [!mistake]
> Add lesson 8's tempting rule, "create then delete cancels out":
`);
    m("let M = rules(\n  cu: then(create(x), then(update(y), z)) -> then(create(y), z)\n  uu: then(update(x), then(update(y), z)) -> then(update(y), z)\n  xc: then(u, then(create(y), z)) -> then(create(y), z)\n  xd: then(u, then(delete, z)) -> then(delete, z)\n  cd: then(create(x), then(delete, z)) -> z\n)");
    m("critical(M)", { work: true });
    md(r`The pair $(\mathsf{then}(\mathsf{delete}, z),\ z)$ does not join: the same batch normalizes to "delete" or to nothing depending on which rule fires first. Lesson 8's Lean found the store state where the two differ (the key already existed). Here the rules themselves show that something is wrong, before any semantics.`);
    sec("Normalization never lengthens a batch");
    md(r`Back in Lean, with lesson 8's ‹normalize›: it never makes a batch longer. (Its termination Lean checks itself: the recursion is structural.)`);
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
    ex("terminates(A)", r`Does addition terminate by size alone?`, [r`Compare the sizes of ‹add(s(x), y)› and ‹s(add(x, y))›.`]);
    ex("rewrite(A, add(s(s(0)), s(s(0))))", r`What is ‹add(s(s(0)), s(s(0)))›, rewritten with ‹A›?`, []);
    md(r`
> [!summary]
> Rewrite rules are an optimization written as equations directed left to right. A measure every rule lowers shows termination; joinable critical pairs show local confluence; together they give each term one normal form. A pair that does not join points at a rule to fix, or one to add (Knuth–Bendix completion).
`);
  });

  add("10-retries.chalk", "Retries and backoff", "Retrying a call that fails at random: the chance that every attempt fails, the expected number of attempts, and the load and wait that backoff trades.", ({ sec, md, m, ex }) => {
    sec("Retries and backoff");
    md(r`
> [!goal]
> Compute the chance that a retried call fails, the attempts it costs on average, and the time exponential backoff waits, as finite sums.
`);
    md(r`A call fails with probability $q$, each attempt independently of the others, and the client tries at most $n$ times. Take $q = 1/10$:`);
    m("let q = 1/10");
    md(r`
> [!definition] Independent attempts
> The attempts all fail with probability $q \cdot q \cdots q = q^n$. The first success comes at attempt $k$ with probability $q^{k-1}(1 - q)$: $k - 1$ failures, then a success.
`);
    m("q^3");
    m("1 - q^5");
    md(r`Adding up the chance of succeeding first at each attempt gives the same number, as it must:`);
    m("sum((1 - q)*q^(k - 1), k, 1, 5)", { work: true });
    md(r`That is the geometric sum. With a symbol for $q$, multiplying by $1 - r$ telescopes:`);
    m("expand((1 - r)*sum(r^k, k, 0, 4))", { work: true });
    sec("Expected attempts");
    md(r`
> [!definition] Expected value
> The **expected** number of attempts is the sum of each count times its probability: $k$ attempts when the first success is at $k < n$, and $n$ when the first $n - 1$ fail.
`);
    m("sum(k*(1 - q)*q^(k - 1), k, 1, 4) + 5*q^4", { work: true });
    md(r`A shorter way: there is an attempt $k + 1$ exactly when the first $k$ failed, with probability $q^k$. Summing those chances counts the attempts:`);
    m("sum(q^k, k, 0, 4)");
    md(r`
> [!mistake]
> Retries look free when failures are rare: $1.1111$ calls per request. But failures are rarely independent. When a server is overloaded, most calls fail, and the retries are more load on the server that is already failing:
`);
    m("sum((9/10)^k, k, 0, 4)");
    md(r`At $q = 9/10$ every request costs four calls: the retries quadruple the load just when the server can take the least. Hence retry budgets, which cap retries at a fraction of the traffic, and backoff.`);
    sec("Exponential backoff");
    md(r`
> [!definition] Exponential backoff
> Wait $d$ before the second attempt, $2d$ before the third, $4d$ before the fourth: the wait before attempt $k + 2$ is $2^k d$. Real clients also cap it and add **jitter**, a random part, so that clients that failed together do not retry together.
`);
    md(r`With $d = 100$ ms and five attempts, the longest the client waits in all:`);
    m("sum(100*2^k, k, 0, 3)");
    md(r`On average far less: the wait before attempt $k + 2$ only happens when the first $k + 1$ attempts failed.`);
    m("sum(100*2^k*q^(k + 1), k, 0, 3)", { work: true });
    md(r`The expected attempts as a function of the failure rate, with a slider:`);
    m("manipulate(sum(p^k, k, 0, 4), p, 0, 1)");
    md(r`
> [!note]
> Retries repeat requests. A request that the server applied but whose reply was lost is sent again: lesson 7's idempotent handler is what makes retrying safe.
`);
    sec("Exercises");
    ex("(1/5)^3", r`A call fails with probability $1/5$. What is the chance that three attempts all fail?`, [r`Independent attempts: multiply.`]);
    ex("1 - (1/2)^4", r`With $q = 1/2$ and four attempts, what is the chance that the call succeeds?`, [r`One minus the chance that all four fail.`]);
    ex("sum((1/2)^k, k, 0, 3)", r`With $q = 1/2$ and at most four attempts, how many attempts does a request cost on average?`, [r`Sum $q^k$ for $k$ from $0$ to $n - 1$.`]);
    ex("sum(50*2^k, k, 0, 4)", r`Backoff starts at $50$ ms and doubles, with six attempts. How long does the client wait in all, at most?`, [r`Five waits: $50, 100, 200, 400, 800$.`]);
    md(r`
> [!summary]
> Independent attempts multiply: $q^n$ fail, and the expected attempts are $\sum_{k<n} q^k$. Under overload $q$ is near one and retries multiply the load; backoff spaces them out, and on average costs little when failures are rare.
`);
  });
}, { leanPrelude: true });

// ---------------------------------------------------------------------------------------------------
course("calculus", "Calculus: derivatives and integrals",
  "The slope at a point, found by zooming in; the power, product and chain rules read off pictures; the circle behind cos, sin and e^(it); tangent lines and bending; then antiderivatives the engine checks by differentiating, and area as slope run backwards.",
  "Calculus I–II", (add) => {

  add("01-rules.chalk", "The rules of differentiation", "The slope at a point, as what secants settle on; the power rule from a growing square, the product rule from a growing rectangle.", ({ sec, md, m, ex, sc }) => {
    sec("The rules of differentiation");
    md(r`
> [!goal]
> Say what the slope of a curve at one point means, and see where the power and product rules come from, well enough to rebuild them.
`);
    md(r`A slope is rise over run, between two points. On a straight line any two points give the same answer; on the graph of $y = x^2$ they do not, since it curves. Yet a speedometer shows one speed at one instant, and a curve looks steeper at some points than at others. What can "the slope at a point" mean, when a slope needs two points?`);
    sec("Zoom in");
    md(r`Magnify the graph of $y = x^2$ around the point $(1, 1)$, which stays where the axes cross:`);
    sc(r`
clock z from 1 to 40
view -1, 1, -2.2, 2.2
T = graph(2*x, x, -1, 1) dashed color 6
G = graph(z*((1 + x/z)^2 - 1), x, -1, 1) thick color 1
P = point(0) color 1
> show G, P | The curve $y = x^2$ near the point $(1, 1)$, placed where the axes cross.
> play z to 40 in 6s | Zoom in, up to $40$ times. The bend straightens out.
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
S1 = segment(0, 1.5) color 2
S2 = segment(1.5, 1.5 + 1.5*i) color 2
S3 = segment(1.5 + 1.5*i, 1.5*i) color 2
S4 = segment(1.5*i, 0) color 2
LX = label(0.75 - 0.15*i, "x") color 2
R1 = segment(1.5, 1.5 + d) color 1
R2 = segment(1.5 + d, 1.5 + d + 1.5*i) color 1
R3 = segment(1.5 + 1.5*i, 1.5 + d + 1.5*i) color 1
T1 = segment(1.5*i, (1.5 + d)*i) color 1
T2 = segment((1.5 + d)*i, 1.5 + (1.5 + d)*i) color 1
T3 = segment(1.5 + 1.5*i, 1.5 + (1.5 + d)*i) color 1
C1 = segment(1.5 + d + 1.5*i, 1.5 + d + (1.5 + d)*i) color 3
C2 = segment(1.5 + (1.5 + d)*i, 1.5 + d + (1.5 + d)*i) color 3
LR = label(1.5 + d + 0.75*i, "x\,dx") color 1
LT = label(0.75 + (1.5 + d)*i, "x\,dx") color 1
LC = label(1.5 + d + (1.5 + d)*i, "dx^2") color 3
> show S1, S2, S3, S4, LX | A square of side $x$: its area is $x^2$.
> show R1, R2, R3, T1, T2, T3, C1, C2, LR, LT, LC; play d to 0.5 in 2s | Lengthen the side by $dx$. The new area is two strips, $x\,dx$ each, and a corner, $dx^2$.
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
B1 = segment(0, 2) color 2
B2 = segment(2, 2 + 1.2*i) color 2
B3 = segment(2 + 1.2*i, 1.2*i) color 2
B4 = segment(1.2*i, 0) color 2
LF = label(1 - 0.2*i, "f") color 2
LG = label(-0.2 + 0.6*i, "g") color 2
R1 = segment(2, 2 + d) color 1
R2 = segment(2 + d, 2 + d + 1.2*i) color 1
R3 = segment(2 + 1.2*i, 2 + d + 1.2*i) color 1
LR = label(2 + d + 0.6*i, "g\,df") color 1
T1 = segment(1.2*i, (1.2 + 0.6*d)*i) color 4
T2 = segment((1.2 + 0.6*d)*i, 2 + (1.2 + 0.6*d)*i) color 4
T3 = segment(2 + 1.2*i, 2 + (1.2 + 0.6*d)*i) color 4
LT = label(1 + (1.2 + 0.6*d)*i, "f\,dg") color 4
C1 = segment(2 + d + 1.2*i, 2 + d + (1.2 + 0.6*d)*i) color 3
C2 = segment(2 + (1.2 + 0.6*d)*i, 2 + d + (1.2 + 0.6*d)*i) color 3
LC = label(2 + d + (1.2 + 0.6*d)*i, "df\,dg") color 3
> show B1, B2, B3, B4, LF, LG | A rectangle with sides $f$ and $g$: its area is the product $fg$.
> show R1, R2, R3, LR, T1, T2, T3, LT, C1, C2, LC; play d to 0.5 in 2s | Nudge $x$: $f$ grows by $df$ and $g$ by $dg$. The new area is a strip $g\,df$, a strip $f\,dg$ and a corner $df\,dg$.
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
> Multiplying by $i$ turns a quarter, so a rate of $i$ times the position goes round a circle: $e^{it} = \cos t + i\sin t$. The derivatives of $\cos$ and $\sin$, the angle-sum formulas and $\arctan$ as an angle all come from that walk. Next, back on the real line: the tangent line as a stand-in for a curve, and what the derivative of the derivative says about its shape.
`);
  });

  add("04-tangent-lines.chalk", "Tangent lines and the second derivative", "The tangent line as the best straight stand-in for a curve, estimates from it, and the second derivative as how fast the curve bends away.", ({ sec, md, m, ex, sc }) => {
    sec("Tangent lines and the second derivative");
    md(r`
> [!goal]
> Use the tangent line as a stand-in for a curve near a point, see why it is the best straight line there, and read the curve's bending from the second derivative.
`);
    md(r`Without a calculator: what is $\sqrt{4.1}$? You know $\sqrt 4 = 2$, and $4.1$ is close to $4$. Zoomed in near $4$, the graph of $\sqrt x$ looks like a line (lesson 1), so follow the line instead of the curve.`);
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

  add("05-antiderivatives.chalk", "Antiderivatives, checked", "Differentiation run backwards: guess a function with the given derivative, then check it by differentiating, as the engine does; substitution and parts as the chain and product rules undone.", ({ sec, md, m, ex }) => {
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

  add("06-definite-integrals.chalk", "Area and the fundamental theorem", "The area under a curve from rectangles, then exactly: the area so far grows at the rate of the curve's height, so it is an antiderivative.", ({ sec, md, m, ex, sc }) => {
    // the right Riemann rectangles of x^2 on [0, 1] with n strips, as segments: a scene's script lines
    const rects = (n, tag, color) => {
      const lines = [], names = [];
      const seg = (name, a, b) => { lines.push(`${name} = segment(${a}, ${b}) color ${color}`); names.push(name); };
      for (let j = 0; j <= n; j++) seg(`${tag}v${j}`, `${j}/${n}`, `${j}/${n} + ${Math.min(j + 1, n) ** 2}/${n * n}*i`);
      for (let k = 1; k <= n; k++) seg(`${tag}t${k}`, `${k - 1}/${n} + ${k * k}/${n * n}*i`, `${k}/${n} + ${k * k}/${n * n}*i`);
      return { lines: lines.join("\n"), names: names.join(", ") };
    };
    const r5 = rects(5, "A", 1), r10 = rects(10, "B", 4);
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
${r5.lines}
${r10.lines}
> show F | The curve $y = x^2$ from $0$ to $1$.
> show ${r5.names} | Five strips of width $\\frac15$; the $k$-th rectangle is $(k/5)^2$ tall. Each one pokes above the curve, so together they are too big.
> hide ${r5.names}; show ${r10.names} | Ten strips: the parts above the curve are thinner, and the total is closer.
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
E = segment(X, X + i*X^2) color 2
A = graph(x^3/3, x, 0, X) thick color 1
P = point(X + i*X^3/3) color 1
LA = label(P, "A(x)") color 1
S1 = segment(X + 0.1, X + 0.1 + i*X^2) color 3
S2 = segment(X + i*X^2, X + 0.1 + i*X^2) color 3
> show F, LF, E | The curve $y = x^2$, and the region under it from $0$ to $x$.
> show A, P, LA; play X to 1.5 in 5s | Move $x$ and plot the area so far, $A(x)$, as it grows.
> show S1, S2; play X to 1 in 3s | Push $x$ on by $dx$: the area gains a thin strip, of height $f(x)$ and width $dx$. So $dA \approx f(x)\,dx$: the slope of $A$ is $f$.
`);
    md(r`Push $x$ on by $dx$ and $A$ grows by a strip of height $f(x)$ and width $dx$, area about $f(x)\,dx$ (the sliver between the strip's top and the curve is smaller still, of the order of $dx^2$). So $dA \approx f(x)\,dx$: the slope of the area so far is the height of the curve, $A' = f$. The area so far is an antiderivative, and lesson 5 finds those.`);
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
  "Vectors and the dot product, matrix arithmetic, solving systems by row reduction with verified row operations, and determinants.",
  "Linear algebra", (add) => {

  add("01-vectors.chalk", "Vectors and the dot product", "Adding and scaling vectors, lengths, and the dot product that measures angles.", ({ sec, md, m, ex }) => {
    sec("Vectors and the dot product");
    md(r`
> [!goal]
> Add and scale vectors, find lengths, and use the dot product to tell when two vectors are perpendicular.
`);
    md(r`A vector is a list of numbers in brackets, ‹[1, 2, 3]›. Vectors add and scale entry by entry.`);
    m("let u = [1, 2, 3]");
    m("let v = [4, -1, 2]");
    m("u + v", { work: true });
    m("2u");
    sec("The dot product");
    md(r`
> [!definition] Dot product and length
> $u \cdot v = \sum_i u_i v_i$, and the length of $v$ is $\lVert v \rVert = \sqrt{v \cdot v}$.
`);
    m("dot(u, v)", { step: 0 });
    m("norm([3, 4])", { work: true });
    m("norm(u)");
    md(r`
> [!theorem] Angle
> $u \cdot v = \lVert u \rVert\, \lVert v \rVert \cos\theta$, where $\theta$ is the angle between them. So $u \cdot v = 0$ exactly when $u$ and $v$ are perpendicular.
`);
    m("dot([1, 2], [2, -1])");
    ex("dot([1, 2, 3], [4, 5, 6])", r`Compute $(1, 2, 3) \cdot (4, 5, 6)$.`, [r`Multiply entry by entry and add: $1 \cdot 4 + 2 \cdot 5 + 3 \cdot 6$.`]);
    ex("norm([6, 8])", r`How long is the vector $(6, 8)$?`, [r`$\sqrt{6^2 + 8^2}$.`], { hide: true });
    ex("dot([2, 3], [3, -2])", r`Compute $(2, 3) \cdot (3, -2)$. What does the answer say about the two vectors?`, [r`Zero means perpendicular.`]);
    md(r`
> [!summary]
> Vectors add and scale entrywise; the dot product turns two vectors into a number that is zero exactly when they are perpendicular.
`);
  });

  add("02-matrices.chalk", "Matrices", "Matrix arithmetic, the product that is not commutative, the transpose, and a matrix acting on a vector.", ({ sec, md, m, ex }) => {
    sec("Matrices");
    md(r`
> [!goal]
> Multiply matrices, see that the order matters, transpose, and apply a matrix to a vector.
`);
    md(r`Rows are separated by ‹;›: ‹[1, 2; 3, 4]› is the $2 \times 2$ matrix with first row $1, 2$.`);
    m("let A = [1, 2; 3, 4]");
    m("let B = [0, 1; 1, 0]");
    md(r`
> [!definition] Matrix product
> The entry in row $i$, column $j$ of $AB$ is the dot product of row $i$ of $A$ with column $j$ of $B$.
`);
    m("A*B", { work: true });
    md(r`
> [!mistake]
> Matrix multiplication is not commutative: $AB$ and $BA$ are different matrices. Here $B$ swaps: on the right of $A$ it swaps $A$'s columns, on the left its rows.
`);
    m("B*A");
    m("transpose(A)", { work: true });
    sec("A matrix acting on a vector");
    md(r`A column vector is a matrix with one column, ‹[1; 1]›. $A$ sends it to the sum of $A$'s columns.`);
    m("A*[1; 1]");
    ex("[1, 2; 3, 4]*[0, 1; 1, 0]", r`Multiply.`, [r`Row $i$ of the first times column $j$ of the second.`, r`The answer is a matrix: type it as ‹[a, b; c, d]›.`]);
    ex("[2, 0; 1, 3]*[1; 2]", r`Apply the matrix to the vector.`, [r`The first entry is $2 \cdot 1 + 0 \cdot 2$.`, r`The answer is a column: ‹[a; b]›.`]);
    ex("transpose([1, 2, 3; 4, 5, 6])", r`Transpose the $2 \times 3$ matrix.`, [r`Rows become columns: the answer is $3 \times 2$.`]);
    md(r`
> [!summary]
> A matrix product is a table of dot products, and its order matters; a matrix times a vector is a combination of the matrix's columns.
`);
  });

  add("03-systems.chalk", "Solving systems by row reduction", "An augmented matrix, the three row operations (each proved to keep the solutions), and reading the answer off the reduced form.", ({ sec, md, m, ex }) => {
    sec("Solving systems by row reduction");
    md(r`
> [!goal]
> Solve a system of linear equations by reducing its augmented matrix, and read each row operation.
`);
    md(r`The system $x + 2y = 5,\ 3x + 4y = 6$ is the augmented matrix ‹[1, 2, 5; 3, 4, 6]›: one row per equation, the right-hand sides in the last column.`);
    md(r`
> [!theorem] Row operations keep the solutions
> Swapping two rows, scaling a row by a nonzero number, and adding a multiple of one row to another do not change the solution set. Each of the three is proved in Lean (the green dots), and so is the claim that the result is in reduced row echelon form.
`);
    m("rref([1, 2, 5; 3, 4, 6])", { work: true });
    md(r`Read it off: the first row says $x = -4$, the second $y = \frac92$.`);
    sec("Three equations");
    m("rref([2, 1, -1, 8; -3, -1, 2, -11; -2, 1, 2, -3])", { work: true });
    md(r`
> [!try]
> Check the solution $x = 2,\ y = 3,\ z = -1$: put it into the first equation, $2x + y - z$.
`);
    m("subst(subst(subst(2x + y - z, x, 2), y, 3), z, -1)");
    ex("rref([1, 1, 3; 1, -1, 1])", r`Solve $x + y = 3,\ x - y = 1$ by reducing the augmented matrix. Give the reduced matrix.`, [
      r`The augmented matrix is ‹[1, 1, 3; 1, -1, 1]›.`,
      r`Subtract the first row from the second, then scale.`,
    ], { hide: true });
    ex("rref([2, 4, 6; 1, 3, 4])", r`Reduce the augmented matrix of $2x + 4y = 6,\ x + 3y = 4$.`, [
      r`Scale the first row by $\frac12$ first.`,
    ], { hide: true });
    md(r`
> [!summary]
> Row reduction is elimination written on the matrix: three operations, none of which changes the solutions, until each variable stands alone in its row.
`);
  });

  add("04-determinants.chalk", "Determinants", "The determinant of 2×2 and 3×3 matrices, the product rule, and what a zero determinant means.", ({ sec, md, m, ex }) => {
    sec("Determinants");
    md(r`
> [!goal]
> Compute determinants, see that the determinant of a product is the product of determinants, and recognise a matrix with no inverse.
`);
    md(r`
> [!definition] Determinant of a $2 \times 2$ matrix
> $\det \begin{pmatrix} a & b \\ c & d \end{pmatrix} = ad - bc$: the signed area of the parallelogram the columns span.
`);
    m("let A = [1, 2; 3, 4]");
    m("det(A)", { step: 0 });
    m("det([2, 1, 0; 1, 3, 1; 0, 1, 2])");
    sec("Products");
    md(r`
> [!theorem] Determinant of a product
> $\det(AB) = \det A \cdot \det B$.
`);
    m("let B = [0, 1; 1, 0]");
    m("det(A*B)");
    m("det(A)*det(B)");
    sec("When the determinant is zero");
    md(r`
> [!theorem] Invertibility
> A square matrix has an inverse exactly when its determinant is not zero. A zero determinant means the columns lie on one line (or plane): the area they span is flat.
`);
    m("det([1, 2; 2, 4])");
    m("rref([1, 2; 2, 4])", { work: true });
    md(r`The reduced form has a row of zeros: the second column is twice the first.`);
    ex("det([2, 1; 5, 3])", r`Compute the determinant.`, [r`$ad - bc$ with $a = 2,\ b = 1,\ c = 5,\ d = 3$.`]);
    ex("det([3, 6; 1, 2])", r`Compute the determinant. Is the matrix invertible?`, [r`Is one column a multiple of the other?`]);
    ex("det([1, 0, 0; 0, 2, 0; 0, 0, 3])", r`Compute the determinant of this diagonal matrix.`, [r`For a diagonal matrix it is the product of the diagonal.`]);
    md(r`
> [!summary]
> The determinant is a single number that measures how a matrix scales area; it multiplies across products, and it is zero exactly when the matrix cannot be undone.
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

  add("05-curry-howard.chalk", "Propositions as types", "A type is a proposition, a term of it a proof: the Curry–Howard correspondence.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Propositions as types");
    md(r`
> [!goal]
> Read a type as a proposition and a term as its proof; prove implications by writing functions, and see where classical logic needs more.
`);
    md(r`
> [!theorem] Curry–Howard
> Read $A \to B$ as "$A$ implies $B$". Then a closed term of type $T$ is a proof of $T$ in intuitionistic propositional logic, and the typing rules are the rules of proof:
> - Var is using an assumption;
> - →I is proving $A \to B$ by assuming $A$ and proving $B$;
> - →E is modus ponens: from $A \to B$ and $A$, conclude $B$.
>
> β-reduction simplifies a proof that introduces an implication only to eliminate it at once.
`);
    md(r`$K$ proves $A \to B \to A$: from $A$, anything implies $A$. $S$ proves $(A \to B \to C) \to (A \to B) \to A \to C$. Composition proves that implication is transitive:`);
    m("type: λf:A→B. λg:B→C. λx:A. g (f x)", { work: true });
    md(r`Each of these is a tautology, as the logic world confirms:`);
    m("taut((p → q) → (q → r) → p → r)");
    sec("Where classical logic differs");
    md(r`**Peirce's law**, $((A \to B) \to A) \to A$, is a tautology:`);
    m("taut(((p → q) → p) → p)");
    md(r`but no λ-term has that type: it is not provable intuitionistically. Classical logic adds the excluded middle, $A \lor \lnot A$, as an axiom, a proof with no program inside.`);
    sec("In Lean");
    md(r`In Lean propositions are types and proofs are terms, literally. A proof by tactics builds a term; ‹fun› writes one directly.`);
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
    ex("taut((p → q) → (¬q → ¬p))", r`Is contraposition a tautology? Answer ‹⊤› or ‹⊥›.`, []);
    md(r`
> [!summary]
> Types are propositions and terms are proofs: →I is assuming, →E is modus ponens, β simplifies proofs. The simply typed calculus proves exactly the intuitionistic implications; Peirce's law needs classical logic.
`);
  });

  add("06-safety.chalk", "Type safety", "Well-typed programs do not go wrong: progress and preservation, and a safety proof in Lean.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Type safety");
    md(r`
> [!goal]
> State type safety, see preservation at work, and prove safety for a small typed language.
`);
    md(r`
> [!theorem] Type safety (Milner: "well-typed programs cannot go wrong")
> - **Preservation**: if $\Gamma \vdash M : T$ and $M$ takes a step to $M'$, then $\Gamma \vdash M' : T$.
> - **Progress**: a closed, typed term is a value or can take a step.
>
> Together: a typed program never gets stuck on a type error.
`);
    md(r`Preservation, on one step. The redex has type $A$:`);
    m("type: x:A ⊢ (λy:A. y) x", { work: true });
    m("normal: (λy:A. y) x");
    m("type: x:A ⊢ x");
    md(r`and so does what it reduces to. (Reduction erases the binders' types: they say which terms are allowed, not how they compute.)`);
    sec("Small steps and big steps");
    md(r`
> [!definition] Operational semantics
> A **small-step** semantics says what one step does, $M 	o M'$: the β-steps of every cell so far. A **big-step** semantics says what a whole program evaluates to, $M \Downarrow v$, in one judgment, by recursion on the program. Progress and preservation are about small steps; the Lean evaluator below is big-step, so its safety theorem says it in one go: a typed program evaluates, and to a value of its type.
`);
    sec("Safety in Lean");
    md(r`For the typed language of lesson 4, safety is one theorem: a program with a type evaluates to a value of that type. It never gets stuck, and it never comes back with the wrong kind of value.`);
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
    lx(`theorem typed_add_evaluates (a b : Expr) (ha : typeOfE a = some .nat) (hb : typeOfE b = some .nat) :
    ∃ n, evalE (.add a b) = some (.num n) := by`, r`Use safety: adding two typed numbers gives a number.`, `  obtain ⟨va, ea, ta⟩ := safety a _ ha
  obtain ⟨vb, eb, tb⟩ := safety b _ hb
  cases va <;> cases vb <;> simp_all [Val.ty, evalE]`, [
      r`‹safety a _ ha› gives a value of ‹a› and that its type is ‹nat›; the same for ‹b›.`,
      r`Split both values with ‹cases›: a boolean contradicts its type, two numbers add. ‹simp_all [Val.ty, evalE]›.`,
    ]);
    sec("Exercises");
    ex("type: f : A → B, x : A ⊢ (λg:A→B. g x) f", r`What type does $(\lambda g{:}A \to B.\, g\ x)\ f$ have, in the context $f : A \to B,\ x : A$?`, [r`The function returns $g\ x : B$.`]);
    ex("normal: (λg:A→B. g x) f", r`Reduce $(\lambda g{:}A \to B.\, g\ x)\ f$. By preservation, the result has the same type.`, [r`One β-step.`]);
    md(r`
> [!summary]
> Preservation keeps a term's type as it reduces, and progress says a typed term is never stuck. Together they are type safety: well-typed programs do not go wrong.
`);
  });

  add("07-polymorphism.chalk", "Polymorphism", "One term at many types: type schemes, System F, and Church numerals that work at every type.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Polymorphism");
    md(r`
> [!goal]
> Read an inferred type as a scheme for all its instances, and use System F's explicit polymorphism to type what simple types cannot.
`);
    md(r`The identity has type $\alpha \to \alpha$ for every $\alpha$: the type variables of an inferred type are implicitly **for all**. That is a type **scheme**, $\forall \alpha.\, \alpha \to \alpha$.`);
    m("infer: λx. x");
    m("infer: λf. λx. f (f x)");
    md(r`In the simply typed calculus, though, one occurrence of a variable has one type. Church's $\mathsf{and}$ uses its argument at two types, and fails:`);
    m("infer: and");
    sec("System F");
    md(r`
> [!definition] System F (Girard, Reynolds)
> Types may quantify over types: $\forall \alpha.\, T$. Terms may take a type as an argument, $\Lambda \alpha.\, M$, and be given one, $M\ [T]$. The polymorphic identity is $\Lambda \alpha.\, \lambda x{:}\alpha.\, x : \forall \alpha.\, \alpha \to \alpha$, and $\mathit{id}\ [\mathsf{Nat}] : \mathsf{Nat} \to \mathsf{Nat}$.
`);
    md(r`In System F a Church numeral has the one type $\forall \alpha.\, (\alpha \to \alpha) \to \alpha \to \alpha$, and can be used at many. Even self-application has a type: $\lambda x{:}\forall \alpha.\, \alpha \to \alpha.\, x\ [\forall \alpha.\, \alpha \to \alpha]\ x$. System F still normalizes, but inference for it is undecidable (Wells, 1994), so ML and Haskell allow polymorphism only at ‹let› (Hindley–Milner), where inference stays decidable.`);
    sec("In Lean");
    md(r`Lean's ‹∀ α : Type› is System F's quantifier. A Church numeral is a polymorphic function, used at ‹Nat› to read it and at ‹String› for fun.`);
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
#eval three String (· ++ "!") "go"

/-- The polymorphic identity has one type for every type. -/
def polyId : ∀ α : Type, α → α := fun _ x => x`);
    lx(`theorem six : (cmul two three).toNat = 6 := by`, r`Check that $2 \cdot 3 = 6$ with System F numerals.`, `  rfl`, [r`Everything computes: ‹rfl›.`]);
    sec("Exercises");
    md(r`Answer with letters for type variables.`);
    ex("infer: λf. λg. λx. f (g x)", r`Infer the most general type of $\lambda f.\, \lambda g.\, \lambda x.\, f\ (g\ x)$.`, [r`$g$ first, then $f$.`]);
    ex("infer: pair", r`Infer the type of $\mathsf{pair} = \lambda a.\, \lambda b.\, \lambda s.\, s\ a\ b$.`, [r`$s$ takes $a$ and $b$ and returns anything.`]);
    md(r`
> [!summary]
> An inferred type is a scheme, true at every instance. System F makes the quantifier explicit and types more terms (Church $\mathsf{and}$, self-application), at the cost of decidable inference.
`);
  });

  add("08-dependent-types.chalk", "Dependent types", "Types that depend on values; Lean's type theory; type checking is proof checking.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Dependent types");
    md(r`
> [!goal]
> Use a type that depends on a value, and see that Lean's type checker, checking a proof, is the same idea as the first lesson's three rules.
`);
    md(r`
> [!definition] The λ-cube
> Starting from simple types, let terms depend on types (polymorphism: System F), types depend on types (type operators: $F_\omega$), and types depend on **terms** (dependent types). All three together is the **calculus of constructions**; Lean's type theory extends it with inductive types and universes.
`);
    md(r`
> [!definition] Π-types
> A dependent function $(x : A) \to B(x)$ returns a value whose **type** depends on the argument. When $B$ does not mention $x$ it is the arrow $A \to B$. Read as a proposition it is $\forall x : A,\ B(x)$: Curry–Howard extends to quantifiers.
`);
    sec("In Lean");
    md(r`Vectors carry their length in their type, so taking the head of an empty one is not an error at run time: it is a type error, and needs no case at all.`);
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

def append : Vec α n → Vec α m → Vec α (m + n)
  | nil, ys => ys
  | cons x xs, ys => cons x (append xs ys)

end Vec

#eval (Vec.cons 1 (Vec.cons 2 Vec.nil)).head
#eval (Vec.append (Vec.cons 1 (Vec.cons 2 Vec.nil)) (Vec.cons 3 Vec.nil)).toList`);
    lx(`theorem Vec.toList_length : ∀ (v : Vec α n), v.toList.length = n := by`, r`The list of a vector of length $n$ has length $n$: the type was telling the truth.`, `  intro v
  induction v with
  | nil => rfl
  | cons x xs ih => simp [Vec.toList, ih]`, [r`‹induction v with›: ‹nil› is ‹rfl›.`, r`For ‹cons›, unfold ‹toList› and use the hypothesis: ‹simp [Vec.toList, ih]›.`]);
    md(r`
> [!theorem] Type checking is proof checking
> A Lean proof is a term, and checking the proof is type checking the term: the kernel applies rules like Var, →I and →E (generalized to Π-types and inductive types). ‹rfl : 2 + 2 = 4› type checks because both sides reduce to the same normal form.
`);
    lean(r`theorem two_plus_two : 2 + 2 = 4 := rfl`);
    sec("Exercises");
    md(r`A last review in the simply typed calculus.`);
    ex("type: λf:A→A. λg:A→A. λx:A. f (g x)", r`What type does $\lambda f{:}A \to A.\, \lambda g{:}A \to A.\, \lambda x{:}A.\, f\ (g\ x)$ have?`, []);
    ex("infer: λx. λy. λz. x z (y z)", r`Infer the type of $S$ without annotations.`, [r`It is the type of the axiom $(A \to B \to C) \to (A \to B) \to A \to C$, with variables.`]);
    md(r`
> [!summary]
> Dependent types let types mention values: a vector's length, a proposition's quantified variable. Lean's type theory has them, and its kernel checks proofs by checking types, as the three rules of the first lesson do.
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
