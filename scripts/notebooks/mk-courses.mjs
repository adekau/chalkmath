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
  "From Propagators to Replicas: counters, sets and registers that replicas update without coordinating and merge as joins; the main theorem that they converge; gossip, version vectors, op-based CRDTs, a replicated store, and the limits.",
  "Distributed systems", (add) => {

  add("01-replicas.chalk", "Replicas and the merge discipline", "Why merging copies is hard, and the one discipline that makes it easy: states in a semilattice, merge as join.", ({ sec, md, m, ex, lean }) => {
    sec("Replicas and the merge discipline");
    md(r`
> [!goal]
> See how replicas that accept updates locally diverge, why "overwrite" and other casual merges lose updates, and state the discipline every design in this course obeys: the state is a bounded join-semilattice, updates go up, and merge is the join.
`);
    md(r`Several machines keep a copy (a **replica**) of the same logical value, accept updates locally without waiting for each other, and reconcile later over a network that delays, drops, duplicates and reorders. Accepting updates locally is easy. Merging afterwards, so that every replica ends with the same state and that state reflects every update, is the hard part.`);
    sec("Overwrite is not a merge");
    md(r`"Keep the incoming value" depends on who hears from whom last. As an operation it is not commutative, so two replicas that exchange states end up swapped rather than equal:`);
    m("let Ow = op({a, b}; [a, b; a, b])");
    m("commutative(Ow)", { work: true });
    m("fold(Ow; a, b)");
    m("fold(Ow; b, a)");
    md(r`"Keep the larger" is a join. Any order of exchanges, any grouping, any duplicates, the same result:`);
    m("let Mx = op({0, 1, 2}; [0, 1, 2; 1, 1, 2; 2, 2, 2])");
    m("semilattice(Mx)");
    m("fold(Mx; 2, 0, 1, 1)");
    md(r`
> [!definition] The merge discipline
> A **state-based CRDT** keeps its state in a bounded join-semilattice, makes every update **inflationary** (the new state is above the old), and merges by the **join**. Then a replica stores not a value but everything it has heard about the value, and hearing the same things in any order gives the same state.
`);
    md(r`This is the propagator cell from *Order and lattices*, read again: there a cell gathered partial information from propagators on one scheduler; here a replica gathers it from other replicas over an unreliable network. The algebra is the same.`);
    sec("Replicas in the notebook");
    md(r`‹replicas(…)› runs a CRDT on named replicas through a schedule of events, one per line: ‹a: inc› updates replica ‹a›, and ‹a -> b› has ‹b› merge ‹a›'s state. It answers with each replica's reading and whether they have converged, and draws a **space-time diagram**: a lane per replica, an arrow per message. Step through it: the diagram grows event by event.`);
    m(`replicas(gcounter; a, b, c
  a: inc
  b: inc
  b: inc
  a -> b
  b -> c
)`, { step: 0 });
    md(r`Replica ‹a› has not heard from anyone, so the replicas have not converged. One more message does it:`);
    m(`replicas(gcounter; a, b, c
  a: inc
  b: inc
  b: inc
  a -> b
  b -> c
  c -> a
)`);
    sec("In Lean");
    md(r`The book's Lean, chapter by chapter, runs in this course's lessons; each lesson sees the ones before it. First the merge discipline as classes (with notation $\sqcup$ for the join, $\bot$ for the bottom, $\sqsubseteq$ for "knows at least as much"), the laws every join obeys (the ACI toolkit), the propagator machinery re-read as replicas, and the chapter 1 demonstrations of naive merges going wrong.`);
    for (const c of crdtLesson(0)) lean(c);
    sec("Exercises");
    ex("commutative(Mx)", r`Is "keep the larger" commutative?`, []);
    ex("fold(Ow; b, a, b, a)", r`Under overwrite, a replica hears $b$, $a$, $b$, $a$ in that order. What does it hold?`, [r`The last one heard wins.`]);
    md(r`
> [!summary]
> Replicas that accept updates locally must reconcile, and reconciliation must remember rather than choose. Keeping states in a semilattice and merging by the join makes the order, grouping and repetition of messages irrelevant.
`);
  });

  add("02-gcounter.chalk", "The G-Counter", "Counting without coordination: one slot per replica, merged by pointwise maximum.", ({ sec, md, m, ex, lean, lx }) => {
    sec("The G-Counter");
    md(r`
> [!goal]
> Build a grow-only counter that replicas increment independently and merge without losing or double-counting, and see why one slot per replica is forced.
`);
    md(r`A like button: taps land on the nearest replica, replicas exchange states when they can, and everyone should eventually see the same total. A single shared number cannot be merged (max loses taps, sum double-counts repeats). The **G-Counter** keeps one slot per replica, each replica only increments its own slot, merge takes the maximum slot by slot, and the value is the sum of the slots.`);
    md(r`Two replicas' slots form a product of chains, and merge is its join:`);
    m("let C4 = chain(4)");
    m("let G = product(C4, C4)");
    m("join(G, (2, 0), (1, 3))", { work: true });
    md(r`Replica 1 has counted 2 taps and replica 2 has counted 3: merged, $(2, 3)$, total 5. Merging the same states again changes nothing; merging an older state ($(1, 0)$) changes nothing either.`);
    m("join(G, (2, 3), (1, 0))");
    sec("A G-Counter, run");
    md(r`Each replica counts its own increments in its own slot; a merge takes the larger count, slot by slot. The work shows each state as a map from replicas to their slots.`);
    m(`replicas(gcounter; a, b
  a: inc
  a: inc
  b: inc
  a -> b
  b -> a
)`, { work: true });
    sec("In Lean");
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
    md(r`
> [!summary]
> A G-Counter gives each replica its own slot; increments touch only one's own slot, merge is the pointwise maximum, and the value is the sum. Merging twice or merging stale states changes nothing, so the network may duplicate and reorder freely.
`);
  });

  add("03-pncounter.chalk", "The PN-Counter", "Counting down without going down: two grow-only counters, and a query that subtracts.", ({ sec, md, m, ex, lean }) => {
    sec("The PN-Counter");
    md(r`
> [!goal]
> Support decrements while keeping every update inflationary, by separating the state (which only grows) from the query (which may go down).
`);
    md(r`A decrement makes the number smaller, but the discipline requires updates to go up. The way out: a decrement is not the removal of an increment but a new event in its own right. Keep two G-Counters, $P$ for increments and $N$ for decrements, and let the **query** compute $P - N$. The state never goes down; the report does.`);
    md(r`For one replica the state is a pair $(p, n)$, ordered componentwise:`);
    m("let C3 = chain(3)");
    m("let PN = product(C3, C3)");
    m("le(PN, (1, 0), (1, 1))", { work: true });
    md(r`$(1, 0) \sqsubseteq (1, 1)$: a decrement moved the state up, while the value went from 1 to 0. Information grows even when the number shrinks.`);
    sec("A PN-Counter, run");
    md(r`The state is a pair of G-Counters, increments and decrements; the reading subtracts.`);
    m(`replicas(pncounter; a, b
  a: inc
  a: inc
  b: dec
  a -> b
  b -> a
)`, { work: true });
    sec("In Lean");
    for (const c of crdtLesson(2)) lean(c);
    md(r`A query that clamps at zero hides the negative truth: a seed for the last lesson.`);
    lean(`def clampedValue {R : Nat} (p : PNCounter R) : Nat :=
  (PNCounter.value p).toNat

example : clampedValue (PNCounter.decr 0 (⊥ : PNCounter 1)) = 0 := by decide
example : PNCounter.value (PNCounter.decr 0 (⊥ : PNCounter 1)) < 0 := by decide`);
    sec("Exercises");
    ex("le(PN, (2, 0), (1, 1))", r`Is the state $(2, 0)$ below $(1, 1)$? Answer ‹true› or ‹false›.`, [r`Compare componentwise.`]);
    md(r`
> [!summary]
> Split state from query: the state is a pair of grow-only counters and only rises; the query $P - N$ may fall. The value is not monotone in the state, and that is fine, because only the state is merged.
`);
  });

  add("04-sets.chalk", "Sets that only grow", "G-Set and 2P-Set: union as the merge, finite sets as sorted lists, and the removal that cannot be undone.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Sets that only grow");
    md(r`
> [!goal]
> Replicate sets: a grow-only set merged by union, and a two-phase set that supports removal with a second grow-only set of tombstones, at the price of never re-adding.
`);
    md(r`A **G-Set** is the powerset lattice: states are finite sets, the order is inclusion, the merge is union. To compute with finite sets (print them, decide equalities) the book represents them as **strictly sorted lists**: same members, same list, which is what antisymmetry needs.`);
    m("let S = subsets({x, y})");
    m("join(S, {x}, {y})");
    sec("Removal: the 2P-Set");
    md(r`Removing from a G-Set would make the state go down. A **2P-Set** keeps two G-Sets, the added and the removed (tombstones); an element is in the set when it is added and not removed. Both halves only grow, so the pair is a product semilattice:`);
    m("let TP = product(S, S)");
    m("join(TP, ({x}, {}), ({x}, {x}))", { work: true });
    m("join(TP, ({x}, {x}), ({x}, {}))");
    md(r`
> [!mistake]
> A removed element can never come back: its tombstone outranks every later add, because the merge cannot tell a re-add from an old add it has already seen. The next lessons fix this two ways: with timestamps (last writer wins) and with unique tags (the OR-Set).
`);
    sec("Sets, run");
    md(r`A G-Set merges by union. A 2P-Set keeps a second set of removed elements, also merged by union, and reads the added minus the removed: so a removal is for ever, and adding again does nothing.`);
    m("replicas(gset; a, b; a: add x; b: add y; a -> b; b -> a)");
    m(`replicas(twopset; a, b
  a: add x
  a -> b
  b: remove x
  a: add x
  b -> a
)`, { work: true });
    sec("In Lean");
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
    ex("join(TP, ({x, y}, {}), ({x}, {x}))", r`Merge the 2P-Set states $(\{x, y\}, \{\})$ and $(\{x\}, \{x\})$. Write it as ‹({…}, {…})›.`, [r`Union the added sets and the removed sets separately.`]);
    md(r`
> [!summary]
> Union is a join, so grow-only sets replicate for free. Removal needs tombstones, which only grow too; the 2P-Set pays for that with "removed once, removed forever".
`);
  });

  add("05-lww.chalk", "Last writer wins", "Overwrite, done lawfully: timestamps in the state, ties broken by replica, and the LWW-Element-Set.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Last writer wins");
    md(r`
> [!goal]
> Recover overwrite semantics as a join, by putting time in the state; see why ties must be broken and what convergence still costs.
`);
    md(r`A display name, a thermostat set point: here the *last* write should win. The move is the one every design in this course makes: if the merge needs information, put it in the state. Each write carries a stamp, and merge keeps the write with the larger stamp, breaking ties by replica identity. That is a join on a lexicographic order.`);
    md(r`Done naively ("on a tie, keep the incoming one"), the merge is not commutative:`);
    m("let Naive = op({w1, w2}; [w1, w2; w1, w2])");
    m("commutative(Naive)", { work: true });
    sec("A register, run");
    md(r`An LWW-Register keeps the write with the latest timestamp, ties broken by replica. ‹write v @ t› gives the timestamp; without one, it is the event's number. The write that wins need not be the one made last in real time:`);
    m(`replicas(lww; a, b
  a: write red @ 5
  b: write blue @ 3
  a -> b
  b -> a
)`, { work: true });
    sec("In Lean");
    for (const c of crdtLesson(4)) lean(c);
    md(r`Three replicas with tied naive timestamps: grouping one merge differently changes the answer.`);
    lean(`example :
    LWW.naiveMerge (LWW.naiveMerge (3, 1) (3, 2)) (3, 3)
      ≠ LWW.naiveMerge (LWW.naiveMerge (3, 2) (3, 1)) (3, 3) := by decide`);
    lx(`${OPEN}theorem lww_merge_bot {R : Nat} (x : LWW.LWWReg R Nat) : ⊥ ⊔ x = x := by`, r`Prove that the never-written register is the identity of merge.`, `  exact Order.sup_bot_left x`, [r`Every bounded join-semilattice has $\bot \sqcup x = x$: look in the merge discipline's toolkit for ‹sup_bot_left›.`]);
    sec("Exercises");
    ex("associative(Naive)", r`Is the naive merge associative? Answer ‹true› or ‹false›.`, [r`$(x \cdot y) \cdot z$ and $x \cdot (y \cdot z)$ both give $z$.`]);
    md(r`
> [!summary]
> Timestamps in the state turn overwrite into a join. Ties must be broken deterministically, or merging stops being commutative. The register converges, but one of two concurrent writes is silently discarded: convergence is not the same as keeping what users meant.
`);
  });

  add("06-orset.chalk", "The OR-Set: add wins", "Observed-remove: a remove deletes only the adds it has seen, so a concurrent add survives.", ({ sec, md, m, lean, lx }) => {
    sec("The OR-Set: add wins");
    md(r`
> [!goal]
> Build a set where removal only cancels the additions the remover observed, so that when an add and a remove race the add wins, and follow the book's proof of that slogan.
`);
    md(r`The G-Set never forgets, the 2P-Set forgets once and forever, and the LWW-Element-Set lets a clock decide, so a remove can cancel an add its issuer never saw. The **observed-remove set** tags every add with a unique identifier; a remove tombstones the tags it has seen. An element is present when some tag of it is not tombstoned. A concurrent add carries a tag the remove never saw, so it survives: **add wins**.`);
    md(r`
> [!theorem] Add wins
> If an add of $e$ is concurrent with a remove of $e$, then after both are merged $e$ is in the set. The proof (the longest in the book) runs on an invariant of reachable states, not on the algebra alone.
`);
    sec("Add wins, run");
    md(r`Each add makes a tag of its own (‹x@a1› is ‹a›'s first add); a remove removes the tags of that element its replica has seen. Here ‹b› removes ‹x› while ‹a› adds it again: the new tag was not seen, so it survives.`);
    m(`replicas(orset; a, b
  a: add x
  a -> b
  b: remove x
  a: add x
  b -> a
  a -> b
)`, { work: true });
    sec("In Lean");
    for (const c of crdtLesson(5)) lean(c);
    md(r`Tombstones are the price: they only ever accumulate.`);
    lx(`theorem orset_tombs_size_monotone {R : Nat} {s t : ORSet R} (h : s ⊑ t) :
    SList.size s.tombs ≤ SList.size t.tombs := by`, r`Prove that an OR-Set's tombstones never shrink.`, `  exact sorted_subset_length s.tombs.sorted t.tombs.sorted h.2.1`, [r`The order on OR-Set states compares the tombstone sets as its second component: ‹h.2.1›.`, r`Lesson 4's ‹sorted_subset_length› finishes it.`]);
    md(r`
> [!summary]
> Unique tags make removal precise: a remove deletes what it observed and nothing else. Add wins, re-adds work, and the cost is tombstones that never go away.
`);
  });

  add("07-convergence.chalk", "Multisets, folds and the main theorem", "Quotient types for 'the same updates, in any order', and strong eventual consistency proved once for every CRDT.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Multisets, folds and the main theorem");
    md(r`
> [!goal]
> State and prove the main theorem: replicas that have received the same updates, in any order and with any repetitions, are in the same state. Along the way, learn quotient types.
`);
    md(r`Each earlier lesson ended with replicas agreeing after scrambled deliveries; none proved they must. A replica receives a *sequence* of updates, but what should matter is the *collection* of them, order and repetition being noise. The honest type for that is a **quotient**: lists modulo permutation are multisets.`);
    md(r`
> [!theorem] Strong eventual consistency
> For any state-based CRDT, folding the join over two delivery sequences with the same members gives the same state. Order does not matter (commutativity and associativity), and repeats do not matter (idempotence).
`);
    md(r`On a small table, any order and any repetition of the same updates:`);
    m("let Mx = op({0, 1, 2, 3}; [0, 1, 2, 3; 1, 1, 2, 3; 2, 2, 2, 3; 3, 3, 3, 3])");
    m("fold(Mx; 1, 3, 2)");
    m("fold(Mx; 2, 2, 1, 3, 1)");
    sec("In Lean");
    for (const c of crdtLesson(6)) lean(c);
    md(r`Multiset union is well-defined on the quotient because appending respects permutation, on either side:`);
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
    ex("fold(Mx; 3, 0, 3, 1)", r`A replica receives $3, 0, 3, 1$. What is its state?`, []);
    md(r`
> [!summary]
> The main theorem is proved once: for any CRDT whose merge is a join, the same multiset of updates gives the same state. Quotient types make "same updates, any order" a type, and the fold over it well-defined.
`);
  });

  add("08-delivery.chalk", "Delivery: gossip, duplication and reordering", "A trace semantics for an at-least-once network, eventual delivery implies convergence, and a gossip driver that provably stops.", ({ sec, md, m, lean, lx }) => {
    sec("Delivery: gossip, duplication and reordering");
    md(r`
> [!goal]
> Model the network: every execution an adversarial at-least-once network could produce, as a relation; prove that eventual delivery gives convergence; and write a gossip driver whose termination Lean accepts.
`);
    md(r`The main theorem assumed replicas had received the same set of updates. Where do those sets come from? This lesson builds the network twice: as an inductive **trace semantics** (a step relation: update, send, deliver, with messages duplicated and reordered at will), and as an **executable gossip driver** run to quiescence, whose termination is proved by well-founded recursion.`);
    sec("Delayed and duplicated messages, run");
    md(r`‹m := a› puts a copy of ‹a›'s state in flight; ‹b <- m› delivers it, possibly later, possibly twice. An old message delivered after newer ones, or twice, changes nothing more, because the merge is a join:`);
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
    md(r`
> [!summary]
> An at-least-once network is a relation on configurations; eventual delivery is a property of executions; and under it, every state-based CRDT converges. The gossip driver runs that argument as a program, and its termination is a theorem.
`);
  });

  add("09-version-vectors.chalk", "Version vectors and causality", "Time without clocks: the G-Counter again, read as a causal history, and concurrency as incomparability.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Version vectors and causality");
    md(r`
> [!goal]
> Track causality without clocks: a version vector records how many events of each replica have been seen; happened-before is its order, and concurrency is incomparability.
`);
    md(r`A **version vector** has one entry per replica: how many of that replica's events have been seen. Its merge is the pointwise maximum and its bottom is all zeroes: it is exactly the G-Counter, read differently. Event $e$ **happened before** $f$ when $e$'s vector is below $f$'s; two events are **concurrent** when neither vector is below the other.`);
    m("let C3 = chain(3)");
    m("let V = product(C3, C3)");
    m("le(V, (1, 0), (0, 1))", { work: true });
    m("le(V, (0, 1), (1, 0))");
    m("join(V, (1, 0), (0, 1))");
    md(r`A tick at replica 1 and a tick at replica 2 are concurrent: neither saw the other. Concurrency is not a failure to know the order; it is a fact about what each replica had seen.`);
    sec("In Lean");
    for (const c of crdtLesson(8)) lean(c);
    lx(`${OPEN}theorem vv_merge_lub {R : Nat} {v w u : VV R} (hv : v ⊑ u) (hw : w ⊑ u) :
    v ⊔ w ⊑ u := by`, r`Prove that the merged version vector is below any vector above both: it is the least upper bound of the two histories.`, `  exact sup_le v w u hv hw`, [r`It is the join's defining property, ‹sup_le›.`]);
    sec("Exercises");
    ex("le(V, (1, 1), (2, 1))", r`Did the event with vector $(1, 1)$ happen before the one with $(2, 1)$? Answer ‹true› or ‹false›.`, []);
    ex("join(V, (2, 0), (0, 1))", r`Merge the version vectors $(2, 0)$ and $(0, 1)$.`, [r`Pointwise maximum.`]);
    md(r`
> [!summary]
> Version vectors are G-Counters that count events; their order is causality, their join is merging histories, and incomparable vectors are concurrent events. Causal delivery waits until a message is the next event of its sender and everything it depends on has been seen.
`);
  });

  add("10-op-based.chalk", "Op-based CRDTs", "Shipping operations instead of states: commutativity moves from the merge to the operations, and duplication becomes the network's problem.", ({ sec, md, lean, lx }) => {
    sec("Op-based CRDTs");
    md(r`
> [!goal]
> Compare the two traditions: state-based replicas ship states and join them; operation-based replicas ship operations and apply them. See what each asks of the network, and how one simulates the other.
`);
    md(r`In an **op-based** CRDT a replica ships the operation it performed ("increment slot 3", "add element 7"), and every receiver applies it. Messages are small, but there is no join to hide behind: if operations arrive out of order they must **commute**, and if one arrives twice it is applied twice, so the transport must deliver **exactly once**. The burden moves from the algebra to the network.`);
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
> State-based CRDTs tolerate any network that eventually delivers; op-based CRDTs need commuting operations and exactly-once delivery, in exchange for small messages. Each can simulate the other.
`);
  });

  add("11-capstone.chalk", "Capstone: a replicated store", "A collaborative shopping list from the course's parts: an OR-Set of items, each with a PN-Counter quantity, converging with no new proofs.", ({ sec, md, lean }) => {
    sec("Capstone: a replicated store");
    md(r`
> [!goal]
> Assemble a collaborative shopping list from the earlier designs, run three replicas under an adversarial schedule, and see that its convergence needs no new proof.
`);
    md(r`The list is an OR-Set of items (adds must win, re-adds must work), and each item has a quantity that goes up and down, a PN-Counter, one per item: a pointwise function lattice. Products and function spaces of semilattices are semilattices, so the store is one, and the main theorem applies to it as it is. Alice, Bob and Carol edit concurrently; their messages are reordered and duplicated; they agree.`);
    sec("In Lean");
    for (const c of crdtLesson(10)) lean(c);
    md(r`
> [!summary]
> Composition is the payoff: a store built from verified parts, with lattice products and function spaces, inherits strong eventual consistency without a single new proof.
`);
  });

  add("12-limits.chalk", "What CRDTs cannot do", "Agreement is not correctness: invariants that need coordination, and the axiom audit.", ({ sec, md, lean }) => {
    sec("What CRDTs cannot do");
    md(r`
> [!goal]
> Walk the boundary of the promise: strong eventual consistency says replicas agree, not that what they agree on is right; some invariants cannot be kept without coordination.
`);
    md(r`A last-writer-wins register converges while discarding one of two concurrent writes. A bank balance that must never go negative cannot be a CRDT: two replicas can each approve a withdrawal that is fine locally, and no merge can make both right. Invariants that span replicas need coordination (a lock, consensus, an escrow of rights) somewhere; CRDTs are for the state that does not.`);
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
    sec("From secant to tangent");
    md(r`The fraction in the definition is the slope of a **secant**: the line through two points of the graph, $(x, f(x))$ and $(x + h, f(x + h))$. Take $f(x) = x^2$ at $x = 1$, and leave $h$ a letter: ‹m› is the secant's slope in terms of $h$, ‹L› the secant, and ‹T› the tangent, the line through $(1, 1)$ with slope $f'(1)$.`);
    m("let f = x^2");
    m("let m = (subst(f, x, 1 + h) - subst(f, x, 1)) / h");
    m("let L = subst(f, x, 1) + m*(x - 1)");
    m("let T = subst(f, x, 1) + subst(diff(f, x), x, 1)*(x - 1)");
    md(r`‹manipulate(e, h, from, to)› shows ‹e› with a slider for $h$ and a ‹▶ Play› button, like Mathematica's ‹Manipulate›, and ‹column(…)› puts several things under the one slider, like its ‹Column›: here the picture, then the calculation of ‹m›, ‹L› and ‹T› at the same $h$. $h$ runs from $2$ down to $0.05$.`);
    m("manipulate(column(plot([f, L, T], x, -0.5, 3), m, L, T), h, 2, 0.05)");
    md(r`
> [!try]
> Press ‹▶ Play›. As $h$ shrinks toward $0$ the second point slides down the curve toward $(1, 1)$, and the secant ‹L› turns onto the tangent ‹T›. Under the picture, ‹m› is worked out at each $h$: rise over run, $\dfrac{(1 + h)^2 - 1}{h}$ with $h$ put in, closing in on $f'(1) = 2$. Drag the slider to stop anywhere and read the calculation there.
`);
    md(r`The slope is never computed *at* $h = 0$, where the fraction is $\frac00$: the derivative is the number the slopes approach.`);
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
// λ-calculus I and II. The Lean of each course is one development, grown lesson by lesson (a Lean
// prelude): an interpreter for the untyped calculus, then a typed calculus, a typed language and its
// safety proof. After "A Programmer's Guide to Lambda Calculus", whose Lean the first course follows.
course("lambda", "λ-calculus I: computing with functions",
  "Terms, free and bound variables, substitution without capture, β-reduction and normal forms, evaluation strategies, de Bruijn indices, Church encodings and recursion by fixed points; an interpreter built in Lean alongside.",
  "Logic and computation", (add) => {

  add("01-terms.chalk", "Terms and notation", "Variables, functions and applications; how terms are written and read; a first β-step.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Terms and notation");
    md(r`
> [!goal]
> Read and write λ-terms: know where a function's body ends, how applications group, and what a term means as a tree.
`);
    md(r`
> [!definition] λ-terms
> A **term** is one of three things: a **variable** $x$; a **function** (an abstraction) $\lambda x.\, M$, which takes $x$ and gives $M$; or an **application** $M\ N$, the function $M$ applied to the argument $N$. Nothing else: no numbers, no booleans, no names for functions. Everything else will be built from these three.
`);
    md(r`Type λ as ‹\lam› then space, or a backslash: ‹\x. x› is $\lambda x.\, x$. Three conventions keep the parentheses down:

- application groups to the left: $f\ a\ b$ is $(f\ a)\ b$;
- a λ's body reaches as far right as it can: $\lambda x.\, f\ x$ is $\lambda x.\, (f\ x)$, not $(\lambda x.\, f)\ x$;
- $\lambda x\ y.\, M$ is short for $\lambda x.\, \lambda y.\, M$, a function returning a function.

A cell with only a term prints it back with as few parentheses as these rules allow.`);
    m("λx y z. x z (y z)");
    m("(λx. (λy. (x y)))");
    sec("A first β-step");
    md(r`
> [!definition] β-reduction
> A **redex** is a function applied to an argument, $(\lambda x.\, M)\ N$. It **reduces** to $M[x := N]$: the body with $N$ put in for every $x$. One such step is a **β-step**.
`);
    m("(λx. x) y", { work: true });
    md(r`Application groups left, so the identity is applied to $\lambda y.\, y$ first, and the result to $z$:`);
    m("(λx. x) (λy. y) z", { step: 0 });
    md(r`A redex can sit inside a function body; normal order (the engine's default, lesson 5) reduces it there too:`);
    m("λx. (λy. y) x", { work: true });
    sec("In Lean");
    md(r`This course builds an interpreter for the λ-calculus in Lean, a piece per lesson; each lesson's Lean sees the lessons' before it. First the terms: an inductive type with one constructor per kind of term.`);
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
    md(r`Reduce each term to the end. An answer is compared after reducing it too, so any name for a bound variable is right.`);
    ex("(λx. λy. x) a b", r`Reduce $(\lambda x.\, \lambda y.\, x)\ a\ b$.`, [r`Application groups left: first $(\lambda x.\, \lambda y.\, x)\ a$.`]);
    ex("(λf. f a) (λx. x)", r`Reduce $(\lambda f.\, f\ a)\ (\lambda x.\, x)$.`, [r`Put $\lambda x.\, x$ for $f$, then reduce again.`]);
    ex("(λx. x x) (λy. y)", r`Reduce $(\lambda x.\, x\ x)\ (\lambda y.\, y)$.`, [r`$x$ is replaced by $\lambda y.\, y$ twice: $(\lambda y.\, y)\ (\lambda y.\, y)$.`]);
    md(r`
> [!summary]
> Terms are variables, functions and applications. Application groups left and a λ reaches right. Computation is the β-step: a function applied to an argument becomes its body, with the argument put in.
`);
  });

  add("02-free-bound.chalk", "Free and bound variables", "Which variables a λ binds, which are free, and why the names of bound ones do not matter.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Free and bound variables");
    md(r`
> [!goal]
> Tell bound variables from free ones, compute the free variables of a term, and decide when two terms are the same up to renaming.
`);
    md(r`
> [!definition] Free and bound
> In $\lambda x.\, M$ the λ **binds** $x$: every $x$ in $M$ (not under another $\lambda x$) refers to it. An occurrence of a variable is **bound** when some λ above it has its name, and **free** otherwise. The free variables:
> $$FV(x) = \{x\}, \quad FV(\lambda x.\, M) = FV(M) \setminus \{x\}, \quad FV(M\ N) = FV(M) \cup FV(N).$$
> A term with no free variables is **closed**, a **combinator**.
`);
    md(r`The command ‹fv:› computes them and names the bound ones:`);
    m("fv: λx. x y", { work: true });
    md(r`The same name can be free in one place and bound in another. Here the first $x$ is bound by its λ, and the second is outside it:`);
    m("fv: (λx. x y) (λy. x y)");
    m("fv: λf. λx. f (f x)");
    sec("α-equivalence");
    md(r`
> [!definition] α-equivalence
> Renaming a bound variable, together with every occurrence it binds, gives the same function: $\lambda x.\, x$ and $\lambda y.\, y$ are both the identity. Terms that differ only so are **α-equivalent**, and are treated as equal. The new name must not be one that is free in the body, or it would be captured: $\lambda x.\, y$ (the constant function giving $y$) is not $\lambda y.\, y$.
`);
    md(r`‹alpha: s, t› decides it, by comparing the terms with their bound names removed (lesson 6 shows how):`);
    m("alpha: λx. λy. x y, λa. λb. a b", { work: true });
    m("alpha: λx. y, λy. y");
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
> A λ binds its variable in its body; everything else is free. Bound names can be changed at will, as long as no free variable gets captured. That is α-equivalence, and terms are equal up to it.
`);
  });

  add("03-substitution.chalk", "Substitution and capture", "Putting a term in for a variable, without capturing its free variables.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Substitution and capture");
    md(r`
> [!goal]
> Compute $M[x := N]$, renaming bound variables where the substitution would otherwise capture a free variable of $N$.
`);
    md(r`
> [!definition] Substitution
> $M[x := N]$ replaces the free occurrences of $x$ in $M$ by $N$:
> - $x[x := N] = N$, and $y[x := N] = y$ for another variable $y$;
> - $(M_1\ M_2)[x := N] = M_1[x := N]\ M_2[x := N]$;
> - $(\lambda x.\, M)[x := N] = \lambda x.\, M$: here $x$ is bound, so there is nothing to replace;
> - $(\lambda y.\, M)[x := N] = \lambda y.\, M[x := N]$ when $y$ is not free in $N$;
> - otherwise rename $y$ first, to a fresh $z$: $\lambda z.\, M[y := z][x := N]$.
`);
    md(r`‹subst: M, x := N› does it, the renaming as its own step:`);
    m("subst: x y, x := λz. z", { work: true });
    m("subst: λx. x y, x := z", { work: true });
    sec("Capture");
    md(r`
> [!mistake] Capture
> Substituting blindly into $\lambda y.\, x$ for $x := y$ gives $\lambda y.\, y$: the identity. But $\lambda y.\, x$ ignores its argument, and so should the result, returning the free $y$. The $y$ that was put in has been **captured** by the λ. The fifth rule renames the binder first: $\lambda y'.\, y$.
`);
    m("subst: λy. x y, x := y", { work: true });
    m("subst: λy. λx. x y z, z := x y", { work: true });
    md(r`A β-step is a substitution, so it renames too:`);
    m("(λx. λy. x y) y", { work: true });
    sec("In Lean");
    md(r`The naive substitution first, to see it capture:`);
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
    md(r`The real one renames. Its recursive call is on a renamed body, which is not a subterm, so Lean cannot see on its own that it stops: we say why (renaming keeps the size) and Lean checks it.`);
    lean(r`/-- A name not in avoid: x, x', x'', … (avoid is finite, so one of the first length + 1 is free). -/
def fresh (avoid : List String) (x : String) : String :=
  go x avoid.length
where
  go (c : String) : Nat → String
    | 0 => c
    | n + 1 => if c ∈ avoid then go (c ++ "'") n else c

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
      let z := fresh (freeVars s ++ freeVars b ++ [x]) y
      lam z (subst x s (rename y z b))
    else lam y (subst x s b)
termination_by t => t.size
decreasing_by all_goals simp_wf <;> simp [size_rename, Term.size] <;> omega

#eval (subst "x" (var "y") (lam "y" (var "x"))).pretty`);
    sec("Exercises");
    md(r`An answer is compared with the result up to the names of bound variables, and is not reduced: write the term the substitution gives.`);
    ex("subst: (λx. x) x, x := y", r`Compute $((\lambda x.\, x)\ x)[x := y]$.`, [r`Only the free $x$ changes; the one under $\lambda x$ is bound.`]);
    ex("subst: λz. x z, x := z", r`Compute $(\lambda z.\, x\ z)[x := z]$.`, [r`The binder $z$ would capture the $z$ put in: rename it first.`]);
    ex("subst: λy. x, x := λw. w", r`Compute $(\lambda y.\, x)[x := \lambda w.\, w]$.`, [r`$\lambda w.\, w$ has no free variables, so nothing can be captured.`]);
    md(r`
> [!summary]
> Substitution replaces free occurrences only, and renames a binder that would capture a free variable of what is put in. It is the whole of β-reduction's work.
`);
  });

  add("04-beta.chalk", "β-reduction and normal forms", "Reducing to normal form; terms that never stop; why the normal form is unique; η.", ({ sec, md, m, ex, lean, lx }) => {
    sec("β-reduction and normal forms");
    md(r`
> [!goal]
> Reduce a term to normal form, recognise terms that have none, and know why the normal form, when there is one, does not depend on the order of the steps.
`);
    md(r`
> [!definition] Normal form
> A term with no redex is in **normal form**. A term **has** a normal form when some sequence of β-steps reaches one.
`);
    m("(λx. λy. y x) a (λz. z)", { step: 0 });
    m("S K K a", { work: true });
    sec("Terms that never stop");
    md(r`$\Omega = (\lambda x.\, x\ x)\ (\lambda x.\, x\ x)$ reduces to itself, for ever. The library calls $\lambda x.\, x\ x$ ‹omega›. A step count after the strategy's name shows the first few steps instead of refusing:`);
    m("normal 2: omega omega", { work: true });
    m("omega omega");
    md(r`Some terms grow as they go, and the engine stops them once they are too big:`);
    m("(λx. x x x) (λx. x x x)");
    md(r`And some have a normal form even though a careless order of steps would never find it: $K\ I\ \Omega$ throws $\Omega$ away.`);
    m("normal: (λx. λy. y) (omega omega)", { work: true });
    sec("Confluence");
    md(r`
> [!theorem] Church–Rosser
> If $M$ reduces to $N_1$ and to $N_2$, then $N_1$ and $N_2$ both reduce to some common $P$. So a term has **at most one** normal form, up to α: the order of the steps can change whether you get there, never where.
`);
    md(r`That is why a λ-term has a meaning, and why an exercise can compare normal forms.`);
    sec("η");
    md(r`
> [!definition] η-reduction
> $\lambda x.\, f\ x$ reduces to $f$ when $x$ is not free in $f$: both give $f\ a$ for every $a$. Adding this rule says that a function is determined by what it does (**extensionality**).
`);
    m("eta: λx. λy. f x y", { work: true });
    m("eta: λx. x x");
    md(r`$\lambda x.\, x\ x$ is not an η-redex: $x$ is free in the function part.`);
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
    ex("eta: λx. (λy. g y) x", r`Reduce $\lambda x.\, (\lambda y.\, g\ y)\ x$ with β and η.`, [r`$\lambda y.\, g\ y$ is an η-redex.`]);
    md(r`
> [!summary]
> A normal form is a term with no redex. Some terms have none, and some have one only along the right path. By Church–Rosser, a term has at most one normal form. η adds extensionality: $\lambda x.\, f\ x$ is $f$.
`);
  });

  add("05-strategies.chalk", "Evaluation strategies", "Which redex next: normal order, call by name, call by value, applicative order.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Evaluation strategies");
    md(r`
> [!goal]
> Reduce a term under each of the four classic strategies, and say what each finds, what it misses, and what it costs.
`);
    md(r`
> [!definition] Strategies
> - **Normal order** (‹normal:›): the leftmost-outermost redex, also under λ, to the normal form.
> - **Call by name** (‹cbn:›): the leftmost-outermost redex, never under a λ, the argument passed unevaluated. It stops at a **weak head normal form**: a λ, or a variable applied to arguments.
> - **Call by value** (‹cbv:›): the function, then the argument, are reduced to **values** (a λ or a variable) before the call; never under a λ.
> - **Applicative order** (‹applicative:›): the leftmost-innermost redex, under λ too: call by value that goes all the way.
`);
    sec("Which terminate");
    md(r`$K\ I\ \Omega$ ignores $\Omega$. The strategies that pass arguments unevaluated never touch it:`);
    m("normal: K I (omega omega)", { work: true });
    m("cbn: K I (omega omega)");
    md(r`The ones that evaluate arguments first never finish. A step count shows how they go round:`);
    m("cbv 4: K I (omega omega)", { work: true });
    m("applicative: K I (omega omega)");
    md(r`
> [!theorem] Standardization
> If a term has a normal form, normal order reaches it.
`);
    sec("What they stop at");
    md(r`Call by name and call by value do not look inside a λ: a function is already a result.`);
    m("cbn: λx. (λy. y) x");
    m("cbv: (λx. x) (λy. (λz. z) y)");
    sec("What they cost");
    md(r`Call by name copies an unevaluated argument, and may evaluate the copy twice; call by value evaluates it once, first:`);
    m("cbn: (λx. x x) ((λy. y) z)", { work: true });
    m("cbv: (λx. x x) ((λy. y) z)", { work: true });
    md(r`Call by name never even reached the redex in the argument: $z\ ((\lambda y.\, y)\ z)$ is a weak head normal form. Normal order goes on to $z\ z$. Most languages call by value; Haskell calls by **need**, call by name that remembers an argument once evaluated.`);
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
    ex("cbn: (λx. x x) ((λy. y) z)", r`Reduce $(\lambda x.\, x\ x)\ ((\lambda y.\, y)\ z)$ by name. Where does it stop?`, [r`The argument goes in unevaluated, twice. Then the head is reduced, and only the head.`]);
    ex("cbn: λx. (λy. y) x", r`Reduce $\lambda x.\, (\lambda y.\, y)\ x$ by name.`, [r`Call by name does not reduce under a λ.`]);
    md(r`
> [!summary]
> Normal order finds every normal form there is. Call by name and call by value stop at functions; call by value evaluates arguments first, once, and can loop on an argument nobody needs.
`);
  });

  add("06-de-bruijn.chalk", "De Bruijn indices", "Terms without bound names: indices count the λs, and α-equivalence becomes equality.", ({ sec, md, m, ex, lean, lx }) => {
    sec("De Bruijn indices");
    md(r`
> [!goal]
> Write a term with de Bruijn indices, and use them to decide α-equivalence.
`);
    md(r`
> [!definition] De Bruijn indices
> Replace each bound variable by the number of λs between it and its binder: $0$ for the nearest. The λs lose their names. $\lambda x.\, \lambda y.\, x$ becomes $\lambda.\, \lambda.\, 1$. A free variable keeps its name.
`);
    m("db: λx. λy. x", { work: true });
    m("db: λf. λx. f (f x)");
    m("db: λx. λy. x (λz. z y)");
    md(r`The same variable can have different indices in different places: in the last term $y$ is $0$ under one λ and $1$ under two.`);
    sec("α-equivalence is equality");
    md(r`Two terms are α-equivalent exactly when their de Bruijn forms are equal: there are no bound names left to differ. That is how ‹alpha:› decides.`);
    m("alpha: λx. λy. x (λz. z y), λa. λb. a (λc. c b)", { work: true });
    md(r`The View menu's de Bruijn indices shows every λ-cell's result, and every step, this way.`);
    sec("In Lean");
    md(r`An interpreter on de Bruijn terms needs no renaming at all; the price is **shifting**: a term moved under a λ has its free indices raised by one.`);
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
    ex("alpha: λx. λy. y (λz. x), λa. λb. b (λb. a)", r`Are $\lambda x.\, \lambda y.\, y\ (\lambda z.\, x)$ and $\lambda a.\, \lambda b.\, b\ (\lambda b.\, a)$ α-equivalent?`, [r`Write both with indices: the inner $x$ and $a$ are two λs up.`]);
    ex("alpha: λx. λy. x, λy. λx. x", r`Are $\lambda x.\, \lambda y.\, x$ and $\lambda y.\, \lambda x.\, x$ α-equivalent?`, [r`In indices: $\lambda.\, \lambda.\, 1$ and $\lambda.\, \lambda.\, 0$.`]);
    md(r`
> [!summary]
> De Bruijn indices count binders instead of naming them. Bound names disappear, so α-equivalent terms are equal, and substitution needs shifting instead of renaming.
`);
  });

  add("07-church.chalk", "Church encodings", "Booleans, numbers, arithmetic, pairs and lists, built from functions alone.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Church encodings");
    md(r`
> [!goal]
> Represent booleans, natural numbers, pairs and lists as functions, compute with them by reduction, and write new operations.
`);
    sec("Booleans");
    md(r`
> [!definition] Church booleans
> $\mathsf{true} = \lambda t.\, \lambda f.\, t$ and $\mathsf{false} = \lambda t.\, \lambda f.\, f$: a boolean chooses one of two things. Then $\mathsf{if}\ b\ x\ y$ is just $b\ x\ y$, and $\mathsf{not}\ b = b\ \mathsf{false}\ \mathsf{true}$.
`);
    md(r`The library has ‹true›, ‹false›, ‹if›, ‹not›, ‹and›, ‹or›. Names are unfolded in one δ-step; the result is read back when it is a boolean or a numeral.`);
    m("if true a b", { work: true });
    m("and true false");
    md(r`A definition, ‹name := term›, is there for the cells after it:`);
    m("xor := λp. λq. p (not q) q");
    m("xor true false");
    m("xor true true");
    md(r`$\mathsf{false}$ and $0$ are the same term, $\lambda t.\, \lambda f.\, f$: the reading names it as the numeral.`);
    sec("Numbers");
    md(r`
> [!definition] Church numerals
> $n$ is the function that applies $f$ to $x$ $n$ times: $0 = \lambda f.\, \lambda x.\, x$, $1 = \lambda f.\, \lambda x.\, f\ x$, $2 = \lambda f.\, \lambda x.\, f\ (f\ x)$. Then $\mathsf{succ}\ n$ applies $f$ once more, $\mathsf{add}\ m\ n$ applies it $n$ times and then $m$ times, and $\mathsf{mul}\ m\ n$ applies "$f$ $n$ times" $m$ times.
`);
    m("succ 2", { work: true });
    m("add 2 3");
    m("mul 2 3");
    m("pow 2 3");
    md(r`A function that applies its argument twice is the numeral 2, and applying it to itself applies four times:`);
    m("twice := λf. λx. f (f x)");
    m("twice twice succ 0");
    sec("Pairs, and the predecessor");
    md(r`
> [!definition] Pairs
> $\mathsf{pair}\ a\ b = \lambda s.\, s\ a\ b$ holds $a$ and $b$ until a selector comes: $\mathsf{fst}\ p = p\ \mathsf{true}$ and $\mathsf{snd}\ p = p\ \mathsf{false}$.
`);
    m("fst (pair a b)", { work: true });
    md(r`Subtracting one is hard: a numeral can only apply $f$, never undo it. Kleene's trick counts up with pairs, $(0, 0) \to (0, 1) \to (1, 2) \to \cdots$, keeping the previous number in the first place. After $n$ steps the first place holds $n - 1$.`);
    m("pred := λn. fst (n (λp. pair (snd p) (succ (snd p))) (pair 0 0))");
    m("pred 3");
    m("sub := λm. λn. n pred m");
    m("sub 3 1");
    m("iszero (pred 1)");
    sec("Lists");
    md(r`
> [!definition] Church lists
> A list is its own fold: given what to do with a head and the rest ($c$) and what to give for the empty list ($n$), it does it. $\mathsf{nil} = \lambda c.\, \lambda n.\, n$ and $\mathsf{cons}\ h\ t = \lambda c.\, \lambda n.\, c\ h\ (t\ c\ n)$, so $[1, 2]$ is $\lambda c.\, \lambda n.\, c\ 1\ (c\ 2\ n)$.
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
    ex("pred 2", r`Reduce $\mathsf{pred}\ 2$. Answer with a numeral, or the λ-term.`, [r`Two steps of the pair counter: $(0, 0) \to (0, 1) \to (1, 2)$.`]);
    ex("pow 2 2", r`Reduce $\mathsf{pow}\ 2\ 2$.`, [r`$2^2$.`]);
    ex("or false (not false)", r`Reduce $\mathsf{or}\ \mathsf{false}\ (\mathsf{not}\ \mathsf{false})$. Answer ‹true› or ‹false›.`, [r`$\mathsf{not}\ \mathsf{false}$ is $\mathsf{true}$.`]);
    ex("snd (pair 1 (succ 1))", r`Reduce $\mathsf{snd}\ (\mathsf{pair}\ 1\ (\mathsf{succ}\ 1))$.`, []);
    ex("cons 1 (cons 1 (cons 1 nil)) add 0", r`Sum the list $[1, 1, 1]$: reduce $\mathsf{cons}\ 1\ (\mathsf{cons}\ 1\ (\mathsf{cons}\ 1\ \mathsf{nil}))\ \mathsf{add}\ 0$.`, [r`The list puts $\mathsf{add}$ between its elements and $0$ at the end: $1 + (1 + (1 + 0))$.`]);
    md(r`
> [!summary]
> With functions alone: booleans choose, numerals iterate, pairs wait for a selector, lists are their own folds. Arithmetic is composition of iterations, and the predecessor is a counter carried in a pair.
`);
  });

  add("08-recursion.chalk", "Recursion and fixed points", "No names, yet recursion: fixed-point combinators, factorial, and Y under call by value.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Recursion and fixed points");
    md(r`
> [!goal]
> Write a recursive function without naming it, using a fixed-point combinator, and see why call by value needs a different one.
`);
    md(r`A recursive definition, $\mathsf{fact} = \lambda n.\, \mathsf{if}\ (n = 0)\ 1\ (n \cdot \mathsf{fact}\ (n - 1))$, mentions itself, and λ-terms cannot. Abstract the self-reference instead: $F = \lambda \mathit{self}.\, \lambda n.\, \ldots\ \mathit{self}\ (n-1)$. A factorial is a **fixed point** of $F$: a $g$ with $F\ g = g$.`);
    md(r`
> [!definition] The Y combinator
> $Y = \lambda f.\, (\lambda x.\, f\ (x\ x))\ (\lambda x.\, f\ (x\ x))$ satisfies $Y\ g = g\ (Y\ g)$ for every $g$: $Y\ g$ is a fixed point of $g$.
`);
    m("normal 2: Y g", { work: true });
    md(r`Each unfolding hands $g$ another copy of $Y\ g$, as many as it asks for.`);
    sec("Factorial");
    md(r`$Y\ F$ has no normal form (it unfolds for ever), so the definition is kept as written; applied to a number, $F$'s test stops the unfolding.`);
    m("pred := λn. fst (n (λp. pair (snd p) (succ (snd p))) (pair 0 0))");
    m("fact := Y (λself. λn. if (iszero n) 1 (mul n (self (pred n))))");
    m("fact 2");
    m("fact 3", { work: true });
    md(r`That took 1525 β-steps, and $\mathsf{fact}\ 4$ takes over ten thousand: numerals in unary, a predecessor that counts up from $0$ every time, and arguments copied unevaluated and computed again. The work shows the first steps and the last, and says how many it leaves out. This is why real languages build numbers in.`);
    sec("Under call by value");
    md(r`Call by value evaluates $Y\ g$'s argument $(\lambda x.\, g\ (x\ x))\ (\lambda x.\, g\ (x\ x))$ before calling $g$, and that unfolds again first, for ever:`);
    m("cbv 3: Y g", { work: true });
    md(r`
> [!definition] The Z combinator
> $Z = \lambda f.\, (\lambda x.\, f\ (\lambda v.\, x\ x\ v))\ (\lambda x.\, f\ (\lambda v.\, x\ x\ v))$ wraps the self-application in a λ (an η-expansion), so it is a value and waits until it is called.
`);
    m("Z := λf. (λx. f (λv. x x v)) (λx. f (λv. x x v))");
    m("cbv: Z g");
    md(r`
> [!theorem] Turing completeness
> With booleans, numerals, pairs and a fixed-point combinator, every computable function on the numbers can be written as a λ-term (Kleene; Turing showed λ-definable and Turing-computable coincide). Which terms have a normal form is then undecidable, which is why the engine reduces on a budget.
`);
    sec("In Lean");
    md(r`Lean has no Y: every function must be shown to terminate, and a recursion on a smaller number does. Yet the factorial is still a fixed point of its defining step.`);
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
    md(r`
> [!summary]
> Recursion without names is a fixed point: $Y\ g = g\ (Y\ g)$. Call by value needs $Z$, which delays the self-application. With fixed points the λ-calculus computes everything a computer can, and so whether a term stops is undecidable.
`);
  });
}, { leanPrelude: true });

course("lambda-types", "λ-calculus II: types and proofs",
  "The simply typed λ-calculus: typing rules and derivation trees, type inference by unification, what types rule out, propositions as types, type safety, polymorphism and dependent types, with the theory proved in Lean.",
  "Logic and computation", (add) => {

  add("01-simple-types.chalk", "Simple types", "Types for terms: base types and arrows, annotated binders, and the three typing rules.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Simple types");
    md(r`
> [!goal]
> Give a type to a λ-term with typed binders, by the three rules of the simply typed λ-calculus, and read its derivation tree.
`);
    md(r`In the untyped calculus anything can be applied to anything: $\mathsf{true}\ 1\ 0$ reduces happily, and $\Omega$ runs for ever. Types sort terms by what they can be given and what they give back, and refuse the rest before anything runs.`);
    md(r`
> [!definition] Simple types
> A **type** is a **base type** ($A$, $B$, $\mathsf{Nat}$, …) or an **arrow** $A \to B$, the type of functions from $A$ to $B$. The arrow groups to the right: $A \to B \to C$ is $A \to (B \to C)$, a function returning a function. A binder carries its type: $\lambda x{:}A.\, M$.
`);
    md(r`Type ‹->› for → and write the type after a colon: ‹type: \x:A. x›.`);
    m("type: λx:A. x");
    sec("The rules");
    md(r`
> [!definition] Typing rules
> A **context** $\Gamma$ lists the types of the variables in scope; a **judgment** $\Gamma \vdash M : T$ says $M$ has type $T$ there.
> - **Var**: if $x : T$ is in $\Gamma$, then $\Gamma \vdash x : T$.
> - **→I** (abstraction): if $\Gamma, x : A \vdash M : B$, then $\Gamma \vdash \lambda x{:}A.\, M : A \to B$.
> - **→E** (application): if $\Gamma \vdash M : A \to B$ and $\Gamma \vdash N : A$, then $\Gamma \vdash M\ N : B$.
`);
    md(r`Every typed term has a **derivation**: a tree of rules, the judgment at the bottom, axioms (Var) at the top. ‹type:› draws it, and lists its steps from the top down.`);
    m("type: λf:A→B. λx:A. f x", { work: true });
    md(r`Free variables get their types from a context written before ‹⊢› (or ‹|-›):`);
    m("type: f : A → B, x : A ⊢ f x");
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
    ex("type: f : A → B ⊢ λx:A. f x", r`In the context $f : A \to B$, what type does $\lambda x{:}A.\, f\ x$ have?`, []);
    md(r`
> [!summary]
> Types are base types and arrows. Three rules type every term that has a type: Var reads the context, →I types a function by its body, →E types an application when the argument fits. A derivation is the tree of rules used.
`);
  });

  add("02-derivations.chalk", "Typing derivations", "Contexts and judgments, why a term fails to type, and the checker proved sound.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Typing derivations");
    md(r`
> [!goal]
> Build and read derivations in a context, say exactly why an ill-typed term fails, and know that a term's type is unique.
`);
    md(r`The checker works bottom-up: to type $\lambda x{:}A.\, M$ it adds $x : A$ to the context and types $M$; to type $M\ N$ it types both and checks that they fit. The tree is read the other way, from the axioms down. Long contexts are named $\Gamma_1, \Gamma_2, \ldots$ under the tree.`);
    m("type: λf:A→B. λg:B→C. λx:A. g (f x)", { work: true });
    sec("Why a term has no type");
    md(r`Three things can go wrong, and each has its message:`);
    m("type: λx:A. x x");
    m("type: λf:A→B. λx:B. f x");
    m("type: λx:A. y");
    md(r`An inner binder hides an outer one of the same name, and the context remembers only the nearest:`);
    m("type: λx:A. λx:B. x");
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
    md(r`
> [!summary]
> A derivation types a term from its parts in a context. A term fails when a variable has no type, an argument has the wrong type, or a non-function is applied. The checker is sound, and types are unique.
`);
  });

  add("03-inference.chalk", "Type inference", "Types without annotations: type variables, equations, unification and the occurs check.", ({ sec, md, m, ex, lean, lx }) => {
    sec("Type inference");
    md(r`
> [!goal]
> Find the most general type of a term whose binders have no types, by setting up equations between types and solving them.
`);
    md(r`
> [!definition] Inference
> 1. Give each binder without a type, and each application's result, a **type variable** $\tau_1, \tau_2, \ldots$.
> 2. Each application $M\ N$ gives an equation: $M$'s type $= N$'s type $\to$ the result's.
> 3. Solve the equations one at a time (**unification**): an equation $\tau = T$ puts $T$ for $\tau$ everywhere; two arrows are equal when their arguments and their results are.
> 4. The variables left are named $\alpha, \beta, \ldots$: any types put for them give a type of the term.
`);
    m("infer: λf. λx. f x", { work: true });
    m("infer: S", { work: true });
    md(r`The result is the **principal type**: every other type of the term is an instance of it (Hindley). $K$ has type $A \to B \to A$, and also $(A \to A) \to B \to A \to A$:`);
    m("infer: K");
    sec("The occurs check");
    md(r`
> [!mistake] Self-application
> In $\lambda x.\, x\ x$, $x$ is applied to itself, so its type would satisfy $\tau = \tau \to \sigma$: a type containing itself. Unification refuses (the **occurs check**), and the term has no simple type.
`);
    m("infer: λx. x x");
    md(r`Types given and types found mix: annotated binders keep their types, and the rest is inferred around them.`);
    m("infer: λf:A→B. λx. f x");
    m("infer: f x");
    md(r`Every inferred type is checked: the term, annotated with it, goes through the type checker, and the tree shown is that check.`);
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
    md(r`
> [!summary]
> Inference gives unknown types variables, turns each application into an equation, and solves the equations by unification. The occurs check rejects a type that would contain itself. The answer is the most general type, and every other type is an instance of it.
`);
  });

  add("04-normalization.chalk", "What types rule out", "No Ω, no Y: typed terms always stop. The cost, and a typed language that cannot loop.", ({ sec, md, m, ex, lean, lx }) => {
    sec("What types rule out");
    md(r`
> [!goal]
> See which untyped terms have no simple type, know the theorem that every typed term has a normal form, and what that costs.
`);
    md(r`$\Omega$ and $Y$ are built on self-application, and the occurs check refuses both:`);
    m("infer: omega");
    m("infer: Y");
    md(r`
> [!theorem] Strong normalization
> In the simply typed λ-calculus every reduction sequence of a typed term is finite: every typed term has a normal form, and every strategy reaches it (Tait, 1967).
`);
    md(r`So the engine's step budget is never needed for a typed term. The price: no fixed-point combinator, so no unbounded recursion. The simply typed λ-calculus is not Turing complete, and real typed languages add recursion back as a primitive (‹fix›, ‹let rec›).`);
    sec("Typed numerals");
    md(r`A Church numeral has type $(\alpha \to \alpha) \to \alpha \to \alpha$, and arithmetic is typed at those types:`);
    m("infer: 3");
    m("infer: mul");
    md(r`Not everything survives. Church's $\mathsf{and} = \lambda p.\, \lambda q.\, p\ q\ p$ passes $p$ to itself, at a second type:`);
    m("infer: and");
    md(r`A simple type cannot be used at two types. Polymorphism (lesson 7) can.`);
    sec("In Lean");
    md(r`A small typed language: numbers, booleans, addition, a test for zero and ‹if›. Its evaluator is structurally recursive, so Lean accepts it as total: it always stops, the strong normalization of this language. A program can still be stuck: ‹1 + true› has no value.`);
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
    md(r`
> [!summary]
> Self-application has no simple type, so neither $\Omega$ nor $Y$ does. Every typed term has a normal form; the cost is that the simply typed calculus cannot express unbounded recursion.
`);
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
