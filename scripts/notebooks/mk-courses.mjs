// node scripts/notebooks/mk-courses.mjs
// Generates the courses: notebooks/courses/<course>/<nn-lesson>.chalk and notebooks/courses.json, the
// list of projects the Courses tab shows (the courses, then the example notebooks as a collection).
// A lesson is short: a goal, worked examples to step through, a slider where a picture moves, and
// exercises the engine checks by normal form. Every cell is checked against the engine by
// `drive.mjs --check` (notebooks/golden/), so a lesson cannot quietly stop working.
// Inline code is written ‹like this› (template literals cannot hold backticks).
import { writeFileSync, mkdirSync } from "node:fs";

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
    md(r`‹sat› gives a satisfying assignment, written as a conjunction of literals, or ⊥ when there is none; ‹falsify› gives a counterexample.`);
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
    md(r`Answer ‹true› or ‹false› (or ⊤, ⊥) for ‹taut› and ‹equiv›. For ‹sat› and ‹falsify›, give an assignment as a conjunction of literals, such as ‹p ∧ ¬q›; any assignment that works is right.`);
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
    ex("sat((a ↔ ¬b) ∧ (b ↔ (a ↔ b)))", r`Who is a knight and who is a knave? Answer with an assignment to $a$ and $b$, such as ‹a ∧ ¬b›.`, [
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
course("calculus", "Calculus: derivatives and integrals",
  "The rules of differentiation, the chain rule and tangent lines; then antiderivatives the engine checks by differentiating, definite integrals and Riemann sums.",
  "Calculus I–II", (add) => {

  add("01-rules.chalk", "The rules of differentiation", "Powers, sums, constant multiples and products: four rules, every step named.", ({ sec, md, m, ex }) => {
    sec("The rules of differentiation");
    md(r`
> [!goal]
> Differentiate polynomials and products with four rules, and read every step the engine takes.

‹diff(f, x)› is the derivative of $f$ with respect to $x$. The engine does not look the answer up: it applies one rule at a time, and each rule is a step you can read, with a dot that says whether the rule is proved in Lean.
`);
    md(r`
> [!definition] Derivative
> The derivative of $f$ at $x$ is $f'(x) = \lim_{h \to 0} \dfrac{f(x + h) - f(x)}{h}$, the slope of the graph there. The rules below are consequences of this definition, so they can be applied without taking a limit each time.
`);
    sec("Powers, sums and constants");
    md(r`
> [!theorem] Power, sum and constant-multiple rules
> $\dfrac{d}{dx} x^n = n x^{n-1}$, $\quad (f + g)' = f' + g'$, $\quad (c f)' = c f'$, and a constant has derivative $0$.
`);
    m("diff(x^5, x)", { work: true });
    md(r`A polynomial takes all four. Step through it: before each ‹▸ Next step›, say which rule comes next.`);
    m("diff(3x^4 - 2x + 7, x)", { step: 0 });
    ex("diff(x^4 - 5x^2 + 2, x)", r`Differentiate $x^4 - 5x^2 + 2$.`, [
      r`Differentiate term by term: the sum rule.`,
      r`Each term: $\frac{d}{dx}\, a x^n = a n x^{n-1}$, and the constant $2$ has derivative $0$.`,
    ]);
    sec("Products");
    md(r`
> [!theorem] Product rule
> $(fg)' = f'g + fg'$: differentiate one factor at a time and add.
`);
    m("diff(x^2 * sin(x), x)", { step: 0 });
    md(r`
> [!mistake]
> The derivative of a product is **not** the product of the derivatives. Here is $f' \cdot g'$ for the same $f = x^2$ and $g = \sin x$, which is not the answer above:
`);
    m("diff(x^2, x) * diff(sin(x), x)");
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
> Four rules differentiate every polynomial and every product of functions you know: power, sum, constant multiple, product. The next lesson adds the fifth, for functions inside functions.
`);
  });

  add("02-chain-rule.chalk", "The chain rule", "Functions of functions: the outer derivative times the inner one, with a slider to watch the inner factor.", ({ sec, md, m, ex }) => {
    sec("The chain rule");
    md(r`
> [!goal]
> Differentiate a function of a function, such as $\sin(x^2)$ or $e^{3x}$, and see where the inner derivative goes.
`);
    md(r`
> [!theorem] Chain rule
> $\dfrac{d}{dx} f(g(x)) = f'(g(x))\, g'(x)$: the outer derivative, evaluated at the inner function, times the inner derivative.
`);
    m("diff(sin(x^2), x)", { step: 0 });
    m("diff(exp(3x), x)", { work: true });
    sec("The inner derivative comes out in front");
    md(r`
> [!try]
> Drag ‹a›. The derivative of $\sin(ax)$ is $a\cos(ax)$: the inner derivative $a$ is a factor in front, so the derivative's curve is $a$ times taller and the slopes are $a$ times steeper.
`);
    m("let a = 2", { slider: [1, 6, 1] });
    m("diff(sin(a*x), x)");
    m("plot([sin(a*x), diff(sin(a*x), x)], x, 0, 6.28)");
    sec("Chains inside chains");
    md(r`A power of a sum is a chain too: the outer function is $u^5$, the inner $2x + 1$.`);
    m("diff((2x + 1)^5, x)", { step: 0 });
    m("diff(ln(x^2 + 1), x)", { work: true });
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
    md(r`
> [!summary]
> Peel the function from the outside in: differentiate the outer layer, keep the inside as it is, and multiply by the derivative of the inside.
`);
  });

  add("03-tangent-lines.chalk", "Higher derivatives and tangent lines", "Derivatives of derivatives, slopes at a point, and the tangent line that follows a slider.", ({ sec, md, m, ex }) => {
    sec("Higher derivatives and tangent lines");
    md(r`
> [!goal]
> Take second derivatives, find the slope of a curve at a point, and draw the tangent line there.
`);
    m("let f = x^3 - 3x");
    m("diff(f, x)");
    md(r`‹diff(f, x, 2)› differentiates twice: the second derivative, which measures how the slope itself changes.`);
    m("diff(f, x, 2)", { work: true });
    sec("Slope at a point");
    md(r`The slope at one point is the derivative with a number put in for $x$: ‹subst(e, x, v)› substitutes.`);
    m("subst(diff(f, x), x, 2)", { work: true });
    sec("The tangent line");
    md(r`
> [!definition] Tangent line
> The tangent line to $y = f(x)$ at $x = a$ is $y = f(a) + f'(a)\,(x - a)$: the line through the point with the curve's slope there.
`);
    m("let a = 2", { slider: [-2, 2, 1] });
    m("let s = subst(diff(f, x), x, a)");
    m("let t = subst(f, x, a) + s*(x - a)");
    m("plot([f, t], x, -2.5, 2.5)");
    md(r`
> [!try]
> Drag ‹a›. At which points is the tangent flat? There $f'(a) = 3a^2 - 3 = 0$, so $a = \pm 1$: the top of the hump and the bottom of the dip.
`);
    ex("subst(diff(x^2, x), x, 3)", r`What is the slope of $y = x^2$ at $x = 3$?`, [
      r`The slope is the derivative, $2x$, at $x = 3$.`,
    ], { hide: true });
    ex("diff(x^4, x, 2)", r`Find the second derivative of $x^4$.`, [
      r`Differentiate twice: $x^4 \to 4x^3 \to \dots$`,
    ]);
    ex("subst(diff(f, x, 2), x, 1)", r`For the $f$ above, what is $f''(1)$?`, [
      r`$f''(x) = 6x$ (the cell above shows it).`,
    ], { hide: true });
    md(r`
> [!summary]
> The derivative at a point is a number, the slope there; the tangent line is the straight line with that slope through the point. Where the slope is zero the curve turns.
`);
  });

  add("04-antiderivatives.chalk", "Antiderivatives, checked", "Integration as the search for a function whose derivative you know, accepted only after the engine differentiates it back.", ({ sec, md, m, ex }) => {
    sec("Antiderivatives, checked");
    md(r`
> [!goal]
> Find antiderivatives, including by substitution and by parts, and see why every answer the engine gives is checked.
`);
    md(r`
> [!definition] Antiderivative
> $F$ is an antiderivative of $f$ when $F' = f$. Any two differ by a constant, so the engine gives one and leaves out the $+\,C$.
`);
    md(r`‹integrate(f, x)› searches for an antiderivative with a few textbook rules. The search proves nothing, so its steps are marked **checked** (a hollow dot): the answer is accepted only when the engine differentiates it and gets $f$ back. Open the work to see the guess and the check.`);
    m("integrate(x^3, x)", { work: true });
    m("integrate(3x^2 + 2x + 1, x)");
    sec("Substitution");
    md(r`
> [!theorem] Substitution
> $\int f(g(x))\, g'(x)\, dx = F(g(x))$ where $F' = f$: the chain rule, read backwards.
`);
    m("integrate(2x*cos(x^2), x)", { work: true });
    sec("By parts");
    md(r`
> [!theorem] Integration by parts
> $\int u\, dv = uv - \int v\, du$: the product rule, read backwards.
`);
    m("integrate(x*exp(x), x)", { work: true });
    md(r`Check it yourself: differentiate the answer, and the integrand comes back.`);
    m("diff(x*exp(x) - exp(x), x)");
    md(r`
> [!mistake]
> An antiderivative is not unique: $x^4$ and $x^4 + 1$ both have derivative $4x^3$. The exercises compare answers exactly, so give them **without** the $+\,C$.
`);
    ex("integrate(4x^3, x)", r`Find an antiderivative of $4x^3$.`, [r`Which power has derivative $4x^3$?`]);
    ex("integrate(cos(3x), x)", r`Find an antiderivative of $\cos 3x$.`, [
      r`$\sin 3x$ is close: its derivative is $3\cos 3x$.`,
      r`Divide by the inner derivative $3$.`,
    ]);
    ex("integrate(2x*exp(x^2), x)", r`Find an antiderivative of $2x\,e^{x^2}$.`, [r`Substitute $u = x^2$: then $du = 2x\,dx$.`]);
    ex("integrate(x*cos(x), x)", r`Find an antiderivative of $x \cos x$.`, [
      r`By parts, with $u = x$ and $dv = \cos x\,dx$.`,
      r`$uv - \int v\,du = x \sin x - \int \sin x\,dx$.`,
    ]);
    md(r`
> [!summary]
> Integration is guessing; differentiation is checking. Substitution undoes the chain rule and parts undoes the product rule.
`);
  });

  add("05-definite-integrals.chalk", "Definite integrals and sums", "The fundamental theorem of calculus, finite sums, and Riemann sums that close in on the area as a slider adds rectangles.", ({ sec, md, m, ex }) => {
    sec("Definite integrals and sums");
    md(r`
> [!goal]
> Evaluate definite integrals with the fundamental theorem, compute finite sums, and watch Riemann sums approach an integral.
`);
    md(r`
> [!theorem] Fundamental theorem of calculus
> If $F' = f$ on $[a, b]$, then $\displaystyle\int_a^b f(x)\,dx = F(b) - F(a)$.
`);
    md(r`‹integrate(f, x, a, b)› finds a checked antiderivative, then evaluates it at the bounds. Step through it.`);
    m("integrate(x^2, x, 0, 1)", { step: 0 });
    m("integrate(sin(x), x, 0, pi)");
    sec("Sums");
    md(r`‹sum(f, k, a, b)› adds $f$ for $k = a, a + 1, \dots, b$.`);
    m("sum(k, k, 1, 10)");
    m("sum(k^2, k, 1, 5)", { work: true });
    sec("Riemann sums");
    md(r`
> [!definition] Right Riemann sum
> Cut $[0, 1]$ into $n$ strips of width $\frac1n$ and stand a rectangle of height $f(\frac kn)$ on the $k$-th: the area of the rectangles is $\displaystyle\sum_{k=1}^{n} f\!\left(\tfrac kn\right) \tfrac1n$.
`);
    m("let n = 10", { slider: [1, 60, 1] });
    m("let R = sum((k/n)^2 / n, k, 1, n)");
    m("N(R)");
    md(r`
> [!try]
> Drag ‹n›. The sum is an exact fraction for every $n$, and its decimal closes in on $\int_0^1 x^2\,dx = \frac13 \approx 0.333$ from above: the rectangles stand above the curve.
`);
    ex("integrate(x, x, 0, 2)", r`Evaluate $\displaystyle\int_0^2 x\,dx$.`, [r`An antiderivative is $\frac{x^2}{2}$; evaluate at $2$ and at $0$.`]);
    ex("integrate(x^2, x, 1, 3)", r`Evaluate $\displaystyle\int_1^3 x^2\,dx$.`, [r`$F(x) = \frac{x^3}{3}$; the answer is $F(3) - F(1)$.`]);
    ex("sum(2k - 1, k, 1, 6)", r`Add the first six odd numbers, $1 + 3 + 5 + \dots + 11$.`, [
      r`Try $1$, then $1 + 3$, then $1 + 3 + 5$: what do the totals have in common?`,
    ], { hide: true });
    md(r`
> [!summary]
> A definite integral is a difference of antiderivative values, and the limit of Riemann sums: the same number reached two ways.
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
course("lambda", "λ-calculus: computing by reduction",
  "Terms, β-reduction in normal order and why substitution must avoid capture; then numbers, arithmetic and booleans built from functions alone.",
  "Logic and computation", (add) => {

  add("01-beta-reduction.chalk", "β-reduction", "Applying a function by substituting its argument, one redex at a time, and the renaming that keeps substitution honest.", ({ sec, md, m, ex }) => {
    sec("β-reduction");
    md(r`
> [!goal]
> Reduce λ-terms to normal form by β-reduction, and see why substitution must rename bound variables.
`);
    md(r`
> [!definition] Terms and β-reduction
> A term is a variable $x$, a function $\lambda x.\, M$, or an application $M\ N$. A **redex** is a function applied to an argument, $(\lambda x.\, M)\ N$, and β-reduction replaces it by $M[x := N]$: the body with the argument put in for the parameter.
`);
    md(r`Type λ as ‹\lam› then space (or a backslash). The engine reduces in **normal order**: always the leftmost, outermost redex first.`);
    m("(λx. x) y", { work: true });
    m("(λx. x x) (λy. y)", { step: 0 });
    m("(λx. λy. x) a b", { work: true });
    sec("Normal forms");
    md(r`
> [!definition] Normal form
> A term with no redex left is in **normal form**. Two terms are equal as programs when they reduce to the same normal form, up to the names of bound variables ($\lambda x.\, x$ and $\lambda y.\, y$ are the same function).
`);
    md(r`The exercises use exactly this: your answer and the question are both reduced, and compared by their normal forms. So any name for a bound variable is right.`);
    ex("(λx. λy. y x) a (λz. z)", r`Reduce to normal form.`, [r`The first redex puts $a$ for $x$: $(\lambda y.\, y\ a)\ (\lambda z.\, z)$.`]);
    ex("(λx. x x) (λy. y)", r`Reduce to normal form. Any name for the bound variable will do.`, [r`$x$ is replaced by $\lambda y.\, y$ twice: $(\lambda y.\, y)(\lambda y.\, y)$.`]);
    sec("Capture");
    md(r`
> [!mistake]
> Substituting blindly can **capture** a variable. In $(\lambda x.\, \lambda y.\, x)\ y$, putting $y$ for $x$ naively gives $\lambda y.\, y$, the identity, but the $y$ that was passed in is free, not the parameter. The engine renames the binder first (an α-step) and gets $\lambda y'.\, y$, the function that ignores its argument and returns $y$.
`);
    m("(λx. λy. x) y", { work: true });
    ex("(λx. λy. x) y", r`Reduce $(\lambda x.\, \lambda y.\, x)\ y$ to normal form. (The trap: $\lambda y.\, y$ is wrong.)`, [
      r`Rename the inner binder first, say to $z$: $\lambda x.\, \lambda z.\, x$.`,
    ], { hide: true });
    md(r`
> [!summary]
> Computation in the λ-calculus is substitution: find the leftmost outermost redex, put the argument in for the parameter, renaming binders that would capture, and repeat until nothing is left to reduce.
`);
  });

  add("02-church-numerals.chalk", "Church numerals and booleans", "Numbers as repeated application, arithmetic as composition, and booleans as choice.", ({ sec, md, m, ex }) => {
    sec("Church numerals and booleans");
    md(r`
> [!goal]
> Represent numbers and truth values as functions, and compute with them by reduction alone.
`);
    md(r`
> [!definition] Church numerals
> The number $n$ is the function that applies $f$ to $x$ $n$ times: $0 = \lambda f.\, \lambda x.\, x$, $1 = \lambda f.\, \lambda x.\, f\ x$, $2 = \lambda f.\, \lambda x.\, f\,(f\ x)$, and so on.
`);
    md(r`The engine knows the numerals and a small library (‹succ›, ‹add›, ‹mul›, ‹pow›, ‹true›, ‹false›, ‹not›, ‹and›, ‹or›, ‹if›, ‹iszero›, ‹pair›, ‹fst›, ‹snd›). It unfolds the names first, in one δ-step, then reduces, and reads a numeral back when the result is one.`);
    m("succ 2", { step: 0 });
    m("add 2 3", { work: true });
    m("mul 2 3");
    sec("Your own definitions");
    md(r`‹name := term› defines a term for the rest of the notebook.`);
    m("twice := λf. λx. f (f x)");
    m("twice twice g z", { work: true });
    sec("Booleans");
    md(r`
> [!definition] Church booleans
> $\mathsf{true} = \lambda t.\, \lambda f.\, t$ and $\mathsf{false} = \lambda t.\, \lambda f.\, f$: a boolean chooses one of two things. Then $\mathsf{if}\ b\ x\ y$ is just $b\ x\ y$.
`);
    m("and true false");
    m("if true a b");
    ex("succ 1", r`Reduce $\mathsf{succ}\ 1$. Write the numeral out as a λ-term (or by its name).`, [r`$\mathsf{succ}$ adds one more application of $f$.`]);
    ex("mul 2 2", r`Reduce $\mathsf{mul}\ 2\ 2$ to a numeral.`, [r`$2 \cdot 2 = 4$: four applications of $f$.`]);
    ex("not true", r`Reduce $\mathsf{not}\ \mathsf{true}$.`, [r`The answer is a boolean: which one chooses its second argument?`]);
    md(r`
> [!summary]
> With nothing but functions and substitution you get numbers, arithmetic and logic: the λ-calculus computes everything a computer can.
`);
  });
});

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
