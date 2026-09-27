// node scripts/notebooks/mk-order-lattices.mjs
// Generates notebooks/order-lattices.chalk: Part I of "From Zero to Propagators" (lean4learning)
// as a ChalkMath notebook, the Lean computation interludes replaced by live poset cells.
// Inline code is written ‹like this› (template literals cannot hold backticks).
import { writeFileSync } from "node:fs";

const cells = [];
const sec = (title) => cells.push({ src: title, type: "section", showWork: false, label: null });
const md = (text) => cells.push({ src: text.replace(/‹|›/g, "`").replace(/^~~~/gm, "```").trim(), type: "markdown", showWork: false, label: null });
const m = (src, showWork = false) => cells.push({ src, showWork, label: null });
const r = String.raw;

// ───────────────────────────── Preface ─────────────────────────────
sec("From Zero to Propagators — Part I: Order and Lattices");
md(r`
> *“The concept of an ordering is one of the most basic in all of mathematics, and yet we rarely pause to examine what it actually requires.”*

This notebook is the first part of *From Zero to Propagators*, a book that builds up from binary relations to lattices and fixed points and then uses them to write verified propagator networks in Lean 4. Part I — relations, partial orders, special elements, monotone maps, lattices, and the Knaster–Tarski fixed-point theorem — is *finite* mathematics, and the ChalkMath engine has a small world for exactly that. So where the book stops to run a Lean ‹#eval›, this notebook runs a cell, and where the book draws a Hasse diagram by hand, the engine draws it from the order.

**How to read it.** A cell whose head is one of the order-world commands is evaluated by the engine's finite-poset world rather than as an algebraic expression:

- ‹let P = poset({a,b,c}; a<b, a<c)› — a poset from a generating relation; the engine takes the reflexive-transitive closure and *checks* reflexivity, antisymmetry and transitivity. ‹divisors(n)›, ‹subsets({…})› and ‹chain(n)› are the three families the book uses most.
- ‹hasse(P)› draws the covers; ‹le(P, a, b)› decides $a \le b$ by exhibiting a chain of covers.
- ‹upper(P, {a,b})›, ‹lower›, ‹join› (or ‹sup›), ‹meet› (or ‹inf›), ‹top›, ‹bottom›, ‹maximal›, ‹minimal›, ‹lattice›.
- ‹let f = map(P; a->b, c->d)› — a map given as a table (elements not listed are fixed); ‹monotone(P, f)›, ‹fixpoints(P, f)›, ‹lfp(P, f)›, ‹gfp(P, f)›.

Turn on **show work** for a cell (the ▸ beside it) to see the derivation: which elements are the upper bounds, why the least of them is the join, the Kleene chain climbing to a fixed point. Every rule these cells use is in the verified column of the ledger — ‹PosetProofs.lean› proves the decisions correct (‹checkPartialOrder_none›, ‹covers_spec›, ‹sup_spec›, ‹iter_le_fixed›).

Where the book proves a theorem in Lean, the proof is kept here as a code block: the engine decides facts about *particular* finite posets; the Lean proofs are about *all* of them.
`);

// ───────────────────────────── Chapter 1 ─────────────────────────────
sec("1 · Relations and Partial Orders");
md(r`
Before we can study lattices or build propagator networks, we need a precise vocabulary for talking about *order*: what it means for one thing to be “at most” another, how such a concept can be captured in a type, and which algebraic laws make it useful.

## Binary relations

**Definition (binary relation).** A *binary relation* on a set $A$ is a subset $R \subseteq A \times A$. We write $a \mathrel{R} b$ for $(a, b) \in R$.

Lean 4 encodes a relation as a function returning ‹Prop›:

~~~lean
def Rel (α : Type) : Type := α → α → Prop
~~~

Using ‹Prop› rather than ‹Bool› is crucial: proofs are computationally irrelevant, and we can state facts like “this relation is a partial order” as types.

**Common relations.** $\le$ on $\mathbb{N}$; divisibility $m \mid n \iff \exists k,\ n = mk$; subset inclusion on $\mathcal{P}(S)$; equality; the *discrete* relation $a \mathrel{R} b \iff a = b$; the *trivial* relation that relates everything to everything.

## Properties of relations

Four properties will occupy us throughout.

$$\begin{aligned}
\text{Reflexive} &\iff \forall a,\; a \mathrel{R} a \\
\text{Symmetric} &\iff \forall a\, b,\; a \mathrel{R} b \to b \mathrel{R} a \\
\text{Antisymmetric} &\iff \forall a\, b,\; a \mathrel{R} b \to b \mathrel{R} a \to a = b \\
\text{Transitive} &\iff \forall a\, b\, c,\; a \mathrel{R} b \to b \mathrel{R} c \to a \mathrel{R} c
\end{aligned}$$

> **Symmetry vs antisymmetry.** These are not negations of each other. A relation can be both (equality), neither (“$a$ is a parent of $b$”), or only one. Antisymmetry says: if you can go *both* ways, the elements must be equal.

## Partial orders

**Definition.** A *partial order* on $A$ is a relation $\le$ that is reflexive, antisymmetric and transitive. The pair $(A, \le)$ is a *partially ordered set*, or *poset*.

The word *partial* means not every two elements need be comparable: there may be $a, b$ with neither $a \le b$ nor $b \le a$. In Lean the definition is a typeclass:

~~~lean
class PartialOrder (α : Type) where
  le          : α → α → Prop
  le_refl     : ∀ (a : α), le a a
  le_antisymm : ∀ (a b : α), le a b → le b a → a = b
  le_trans    : ∀ (a b c : α), le a b → le b c → le a c
~~~

The engine's ‹poset› takes a finite set and a *generating* relation, closes it under reflexivity and transitivity, and then checks all three laws — so the order below contains $a \le c$ although only $a < b$ and $b < c$ were written:
`);
m("let C = poset({a, b, c}; a < b, b < c)", true);
m("le(C, a, c)", true);
md(r`
The check is not decoration. Give it a relation that is not antisymmetric and the *error is the answer*, with the witness:
`);
m("poset({a, b}; a < b, b < a)");
md(r`
## The natural numbers

The natural numbers with the usual $\le$ are the first instance; Lean's core library already has ‹Nat.le_refl›, ‹Nat.le_antisymm›, ‹Nat.le_trans›, so the instance just reuses them. A finite initial segment is ‹chain(n)›: the elements $0 < 1 < \cdots < n-1$, every pair comparable, which is what *total* order looks like as a Hasse diagram — a single line.
`);
m("let N5 = chain(5)");
md(r`
## Divisibility

Divisibility is a partial order on $\mathbb{N}$: $n \le m$ means $n \mid m$, i.e. $\exists k,\ m = n k$. It is a genuinely different order from $\le$: $3 \mid 12$ but $4 \nmid 6$.

In the book this is where the first real proof lives. Reflexivity has the explicit witness $k = 1$; transitivity composes witnesses, $b = ak$ and $c = bj$ give $c = a(kj)$; but antisymmetry — if $a \mid b$ and $b \mid a$ then $a = b$ — needs three lemmas: that only $0$ is divisible by $0$, that $kj = 1$ in $\mathbb{N}$ forces $k = 1$, and cancellation of $a > 0$. The mathematical core is the middle one:

~~~lean
theorem mul_eq_one_left {k j : Nat} (h : k * j = 1) : k = 1 := by
  match k with
  | 0     => simp [Nat.zero_mul] at h          -- 0 * j = 0 ≠ 1
  | 1     => rfl
  | k + 2 =>                                    -- (k+2) * j ≥ 2 ≠ 1
    exfalso
    have hj : j ≥ 1 := by
      cases j with
      | zero   => simp [Nat.mul_zero] at h
      | succ j => exact Nat.succ_le_succ (Nat.zero_le j)
    have hbig : (k + 2) * j ≥ 2 :=
      calc (k + 2) * j ≥ (k + 2) * 1 := Nat.mul_le_mul_left (k + 2) hj
        _ = k + 2 := Nat.mul_one (k + 2)
        _ ≥ 2 := Nat.le_add_left 2 k
    omega
~~~

Everything else is bookkeeping. When reading an unfamiliar proof it is always worth asking where the actual mathematical content is; here it is entirely in that one lemma.

For a *finite* set of naturals the engine simply decides the order. ‹divisors(12)› is the divisors of $12$ under $\mid$, and the engine draws its Hasse diagram:
`);
m("let D = divisors(12)", true);
m("le(D, 3, 12)", true);
m("le(D, 4, 6)", true);
md(r`
## Sets

Sets, represented as predicates $\alpha \to \mathsf{Prop}$, are ordered by inclusion $s \subseteq t \iff \forall a,\ s\,a \to t\,a$. This is the first non-trivial Lean proof in the book: antisymmetry needs *function extensionality* and *propositional extensionality* to turn $s\,a \leftrightarrow t\,a$ for all $a$ into $s = t$.

~~~lean
instance {α : Type} : PartialOrder (Set α) where
  le          := Set.subset
  le_refl     := fun s a ha => ha
  le_antisymm := fun s t h1 h2 => funext (fun a => propext ⟨h1 a, h2 a⟩)
  le_trans    := fun s t u h1 h2 a ha => h2 a (h1 a ha)
~~~

The finite version is ‹subsets({…})›: all subsets of a finite set under $\subseteq$. The book's first Hasse diagram is $\mathcal{P}(\{a, b, c\})$:
`);
m("let P3 = subsets({a, b, c})");
m("le(P3, {a}, {a, b, c})", true);
md(r`
## Hasse diagrams

Posets are best understood visually. A *Hasse diagram* draws elements as nodes and *covers* as upward edges: $a$ is covered by $b$, written $a \lessdot b$, if $a < b$ and there is no $c$ with $a < c < b$. Reflexive loops and transitive edges are left out — they can be recovered.

The engine's diagrams above are exactly this. ‹hasse(D)› lists the covers it drew; the rule ‹order.covers› is proved to produce exactly the pairs $x < y$ with nothing strictly between (‹covers_spec›).
`);
m("hasse(D)", true);
md(r`
That is the book's ‹printHasse› output — $1 \to 2$, $1 \to 3$, $2 \to 4$, $2 \to 6$, $3 \to 6$, $4 \to 12$, $6 \to 12$ — computed from the order rather than written down.

## Computation interlude: running the divisibility order

The book's interlude defines ‹D12›, ‹dvd12›, ‹upperBounds›, ‹sup12›, ‹lowerBounds›, ‹inf12› as Lean functions and evaluates them. Here they are the engine's own commands. The upper bounds of $\{4, 6\}$ in $D$ are the common multiples in the set; the *least* of them is the join — which for divisibility is the lcm:
`);
m("upper(D, {4, 6})");
m("sup(D, 4, 6)", true);
m("sup(D, 2, 3)", true);
md(r`
Dually, the lower bounds are the common divisors and the greatest of them — the meet — is the gcd:
`);
m("lower(D, {4, 6})");
m("inf(D, 4, 6)", true);
m("inf(D, 3, 4)", true);

md(r`
## Exercises

**1.1 Reflexivity and symmetry.** Show that a relation that is both symmetric and antisymmetric must be a subset of equality: $a \mathrel{R} b \to a = b$.

~~~lean
theorem symm_antisymm_eq {α : Type} (r : Rel α)
    (hs : Symmetric r) (ha : Antisymm r) :
    ∀ a b : α, r a b → a = b := by
  intro a b h
  exact ha a b h (hs a b h)
~~~

This one is about *all* relations, so it is a Lean theorem and not a cell.

**1.2 Divisibility on a small set.** For divisibility on $\{1, 2, 3, 4, 6, 12\}$: (a) draw its Hasse diagram — that is $D$ above; (b) which pairs are incomparable? Ask the engine. An element is incomparable with another when ‹le› fails in both directions:
`);
m("le(D, 2, 3)");
m("le(D, 3, 2)");
m("le(D, 3, 4)");
m("le(D, 4, 6)", true);
m("le(D, 6, 4)");
md(r`
So the incomparable pairs are $\{2, 3\}$, $\{3, 4\}$, $\{4, 6\}$ — and $\{4,6\}$'s derivation shows the engine looked for a chain of covers from $4$ to $6$ and found none.

**1.3 Product order.** Given posets $(A, \le_A)$ and $(B, \le_B)$, the *product order* on $A \times B$ is $(a_1, b_1) \le (a_2, b_2) \iff a_1 \le_A a_2 \wedge b_1 \le_B b_2$. The Lean instance proves each law component-wise. The engine has no product constructor (yet), but a small product can be written out: $\mathbf{2} \times \mathbf{2}$, with $x_{ij}$ standing for the pair $(i, j)$ —
`);
m("let Sq = poset({x00, x01, x10, x11}; x00 < x01, x00 < x10, x01 < x11, x10 < x11)");
m("le(Sq, x01, x10)");
md(r`
— which is the same diagram as $\mathcal{P}(\{x, y\})$: the product of two two-element chains *is* the powerset of a two-element set (each coordinate says whether one element is in).

**1.4 Reverse order.** If $(A, \le)$ is a partial order, so is $(A, \ge)$ — the *dual* or *opposite* order, the Hasse diagram turned upside down. Sudoku domains in Chapter 8 use this. Reversing every generating pair of $D$:
`);
m("let Dop = poset({1, 2, 3, 4, 6, 12}; 12 < 4, 12 < 6, 4 < 2, 6 < 2, 6 < 3, 2 < 1, 3 < 1)");
m("le(Dop, 12, 1)", true);

// ───────────────────────────── Chapter 2 ─────────────────────────────
sec("2 · Special Elements and Monotone Maps");
md(r`
In a poset, certain elements play privileged roles (least, greatest, bounds), and certain functions are especially well-behaved (monotone maps). This chapter equips us with the vocabulary for both.

## Extremal elements

**Definition.** Let $(P, \le)$ be a poset and $S \subseteq P$.

- $m \in S$ is the *minimum* of $S$ if $\forall s \in S,\ m \le s$; the *maximum* if $\forall s \in S,\ s \le m$.
- $m \in S$ is *minimal* in $S$ if there is no $s \in S$ with $s < m$; *maximal* if there is no $s$ with $m < s$.

A minimum, if it exists, is unique (by antisymmetry) — we call it $\bot$, and a unique maximum $\top$. A minimal element need not be unique. The distinction is subtle but important: a *minimum* beats every other element; a *minimal* element merely has nothing strictly below it.

The book's figure has two posets side by side. On the left, $a$ is the minimum (and the only minimal element):
`);
m("let A = poset({a, b, c, d}; a < b, a < c, b < d, c < d)");
m("minimal(A)");
m("bottom(A)");
md(r`
On the right, $p$ and $q$ are both minimal — nothing is below either — but there is no minimum, because $p \not\le q$ and $q \not\le p$. The engine's refusal says exactly this:
`);
m("let T = poset({p, q, r, s, t}; p < r, p < s, q < s, r < t, s < t)");
m("minimal(T)");
m("bottom(T)");
md(r`
~~~lean
class Bot (α : Type) where bot : α
class Top (α : Type) where top : α

class BoundedPartialOrder (α : Type) extends PartialOrder α, Bot α, Top α where
  bot_le : ∀ (a : α), (⊥ : α) ≤ a
  le_top : ∀ (a : α), a ≤ (⊤ : α)
~~~

**Bounded orders.** $(\mathcal{P}(S), \subseteq)$ has $\bot = \varnothing$ and $\top = S$; $(\{0, 1\}, \le)$ has $\bot = 0$, $\top = 1$; $(\mathbb{N}, \le)$ has $\bot = 0$ and no $\top$. The divisors of $12$ have both ($1$ divides everything, everything divides $12$):
`);
m("bottom(P3)");
m("top(P3)");
m("bottom(D)");
m("top(D)");
md(r`
The book's example is divisibility on *all* of $\{1, \ldots, 12\}$, not just the divisors of $12$ — and that poset has $\bot = 1$ but no single $\top$. Writing out the generating pairs (a prime's multiples suffice; the closure does the rest):
`);
m("let D12 = poset({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12}; 1 < 2, 1 < 3, 1 < 5, 1 < 7, 1 < 11, 2 < 4, 2 < 6, 2 < 10, 3 < 6, 3 < 9, 4 < 8, 4 < 12, 5 < 10, 6 < 12)");
m("maximal(D12)");
m("top(D12)");
md(r`
## Upper and lower bounds

**Definition.** Let $S \subseteq P$.

- $u \in P$ is an *upper bound* of $S$ if $\forall s \in S,\ s \le u$; $l$ is a *lower bound* if $\forall s \in S,\ l \le s$.
- The *supremum* (least upper bound) $\sup S$ is the smallest upper bound, when it exists; the *infimum* (greatest lower bound) $\inf S$ the largest lower bound.

The book illustrates these on a seven-element poset with $S = \{c, d\}$: the upper bounds of $S$ are $e$, $f$, $g$ and the lower bounds are $a$, $b$.
`);
m("let E = poset({a, b, c, d, e, f, g}; a < b, a < c, b < c, b < d, c < e, d < e, c < f, d < f, e < g, f < g)");
m("upper(E, {c, d})");
m("lower(E, {c, d})");
m("inf(E, c, d)", true);
md(r`
The infimum is $b$: of the lower bounds $\{a, b\}$, $b$ is the greatest. Now the supremum. The book's caption argues: “$e$ and $f$ are incomparable, so $\sup S = g$.” Ask the engine:
`);
m("sup(E, c, d)");
md(r`
It refuses — and it is right. A least upper bound must be an upper bound that is *below every other upper bound*. $g$ is an upper bound, but $g \not\le e$ and $g \not\le f$; and neither $e$ nor $f$ is below the other. The upper bounds $\{e, f, g\}$ have no least element, so $\sup\{c, d\}$ does not exist in $E$. (This is the same shape as the no-minimum poset $T$ above, sitting on top of $S$.) The figure's caption is wrong, and a decided order catches what a hand-drawn one lets through — the point of a verified notebook in one cell.

**Theorem (uniqueness of sup/inf).** If $\sup S$ exists it is unique; likewise $\inf S$.

*Proof.* If $u$ and $v$ are both least upper bounds, then $v \le u$ because $u$ is an upper bound and $v$ is least; symmetrically $u \le v$; antisymmetry gives $u = v$. $\square$

~~~lean
structure IsSupOf {α : Type} [PartialOrder α] (a b sup : α) : Prop where
  ge_a  : a ≤ sup
  ge_b  : b ≤ sup
  least : ∀ (u : α), a ≤ u → b ≤ u → sup ≤ u

theorem sup_unique {α : Type} [PartialOrder α] {a b s t : α}
    (hs : IsSupOf a b s) (ht : IsSupOf a b t) : s = t := by
  apply PartialOrder.le_antisymm
  · exact hs.least t ht.ge_a ht.ge_b
  · exact ht.least s hs.ge_a hs.ge_b
~~~

The engine's ‹join› is this specification made executable: the rule ‹order.least› picks the upper bound below every other, and ‹sup_spec› proves that is what it picked (and ‹sup_none› that when it finds nothing, nothing exists).

## Monotone maps

**Definition.** A function $f : (P, \le_P) \to (Q, \le_Q)$ between posets is *monotone* (order-preserving) if $\forall a, b,\ a \le_P b \to f(a) \le_Q f(b)$.

Monotone maps are the morphisms of the category of posets, and they will be central to propagators: every propagator is a monotone function on a lattice.

~~~lean
structure Monotone {α β : Type} [PartialOrder α] [PartialOrder β] (f : α → β) : Prop where
  map_le : ∀ (a b : α), a ≤ b → f a ≤ f b

theorem Monotone.comp {f : α → β} {g : β → γ} (hf : Monotone f) (hg : Monotone g) :
    Monotone (g ∘ f) where
  map_le := fun a b h => hg.map_le _ _ (hf.map_le _ _ h)
~~~

The engine's maps are maps from a poset *to itself*, given as a table; elements not listed are fixed. The book's ‹double12› sends $n$ to $2n$ when that is still a divisor of $12$ and leaves it alone otherwise. Monotone: if $a \mid b$ then $2a \mid 2b$.
`);
m("let dbl = map(D; 1 -> 2, 2 -> 4, 3 -> 6, 6 -> 12)");
m("monotone(D, dbl)", true);
md(r`
The book's picture of a *non*-monotone map is a pair $x \le y$ with $g(x) > g(y)$ — the order violated. The check reports the first violating pair it finds, so the counterexample is the derivation:
`);
m("let k = map(D; 2 -> 3)");
m("monotone(D, k)", true);
md(r`
**Monotone functions.** $n \mapsto n + 5$ on $(\mathbb{N}, \le)$; $S \mapsto S \cup \{x\}$ and $S \mapsto S \cap T$ on $(\mathcal{P}(A), \subseteq)$; every constant function; the identity. Two of these on $D$:
`);
m("let one = map(D; 2 -> 1, 3 -> 1, 4 -> 1, 6 -> 1, 12 -> 1)");
m("monotone(D, one)");
m("let idD = map(D; 1 -> 1)");
m("monotone(D, idD)");
md(r`
## Computation interlude: running monotone maps

The book decides monotonicity by checking all pairs of ‹D12› — the engine's ‹monotone› is that check, over the pairs of the order, with the failing pair reported. Its most instructive example is the “complement” $n \mapsto 12/n$, which *reverses* the order (it is antitone), and whose composite with itself is the identity:
`);
m("let comp = map(D; 1 -> 12, 2 -> 6, 3 -> 4, 4 -> 3, 6 -> 2, 12 -> 1)");
m("monotone(D, comp)", true);
md(r`
**Fixed points.** A fixed point of $f$ is an $x$ with $f(x) = x$. ‹fixpoints› lists them all — every element for the identity, only $1$ for the constant, none for the complement:
`);
m("fixpoints(D, idD)");
m("fixpoints(D, one)");
m("fixpoints(D, comp)");
md(r`
**Iterating a monotone map.** If $f$ is monotone and $a \le f(a)$, the chain $a, f(a), f^2(a), \ldots$ is ascending; on a finite poset it must stop. ‹lfp› iterates from $\bot$ and shows the chain:
`);
m("lfp(D, dbl)", true);
md(r`
Each application moves strictly upward in the divisibility order until it reaches a fixed point — the ascending chain theorem, watched. The book's comment claims ‹iterToFixpoint double12 1› is ‹[1, 2, 4, 12]›; the engine stops at $4$, and it is right: $2 \cdot 4 = 8$ is not a divisor of $12$, so ‹double12› leaves $4$ where it is, and $4$ is the fixed point the chain reaches. ($12$ is a fixed point too — the *greatest* one, as Chapter 4 will show — but the chain from $\bot$ never gets there.)

## Exercises

**2.1 Antitone composition.** Show that the composite of two *antitone* maps ($a \le b \to f(b) \le f(a)$) is monotone. Example: ‹comp› above is antitone, and ‹comp ∘ comp› is the identity, which is monotone. In general $a \le b \Rightarrow f(b) \le f(a) \Rightarrow g(f(a)) \le g(f(b))$: the two reversals cancel.

**2.2 Fixed points.** Show that if $f$ is monotone and $a \le f(a)$, the chain $a \le f(a) \le f^2(a) \le \cdots$ is indeed a chain. Induction: $f^n(a) \le f^{n+1}(a)$ gives $f^{n+1}(a) \le f^{n+2}(a)$ by monotonicity — each step of the ‹lfp› derivation above is one instance.

**2.3 The identity is monotone.** For any poset. The cell ‹monotone(D, idD)› above checks the instance; the Lean proof is one line, ‹⟨fun a b h => h⟩›.
`);

// ───────────────────────────── Chapter 3 ─────────────────────────────
sec("3 · Lattices");
md(r`
A poset in which every pair of elements has both a supremum and an infimum is a *lattice*. This apparently modest requirement yields a rich algebraic structure that shows up in logic, topology, computer science, and — in Part II — concurrency and constraint solving.

## Meet and join

**Definition.** A *lattice* is a poset $(L, \le)$ in which every two elements $a, b$ have a *meet* (greatest lower bound) $a \sqcap b$ and a *join* (least upper bound) $a \sqcup b$.

The smallest picture of it is the diamond: $a \sqcap b$ below both $a$ and $b$, $a \sqcup b$ above both.
`);
m("let L4 = poset({m, a, b, j}; m < a, m < b, a < j, b < j)");
m("meet(L4, a, b)", true);
m("join(L4, a, b)", true);
m("lattice(L4)", true);
md(r`
Meet and join satisfy laws that can be taken as an equivalent *algebraic* definition of a lattice:

$$\begin{aligned}
a \sqcap b &= b \sqcap a, & a \sqcup b &= b \sqcup a & &\text{(commutativity)} \\
(a \sqcap b) \sqcap c &= a \sqcap (b \sqcap c), & (a \sqcup b) \sqcup c &= a \sqcup (b \sqcup c) & &\text{(associativity)} \\
a \sqcap a &= a, & a \sqcup a &= a & &\text{(idempotence)} \\
a \sqcap (a \sqcup b) &= a, & a \sqcup (a \sqcap b) &= a & &\text{(absorption)}
\end{aligned}$$

and the order can be recovered from either operation: $a \le b \iff a \sqcap b = a \iff a \sqcup b = b$.

~~~lean
class Lattice (α : Type) extends PartialOrder α where
  inf : α → α → α    -- meet  (⊓)
  sup : α → α → α    -- join  (⊔)
  inf_le_left  : ∀ (a b : α), inf a b ≤ a
  inf_le_right : ∀ (a b : α), inf a b ≤ b
  le_inf : ∀ (a b c : α), a ≤ b → a ≤ c → a ≤ inf b c
  sup_le_left  : ∀ (a b : α), a ≤ sup a b
  sup_le_right : ∀ (a b : α), b ≤ sup a b
  le_sup : ∀ (a b c : α), a ≤ c → b ≤ c → sup a b ≤ c
~~~

Commutativity and idempotence follow from the axioms alone; the book derives them by ‹le_antisymm› against ‹le_inf›. For instance:

~~~lean
theorem inf_comm (a b : α) : a ⊓ b = b ⊓ a := by
  apply le_antisymm
  · apply le_inf
    · exact inf_le_right a b
    · exact inf_le_left a b
  · apply le_inf
    · exact inf_le_right b a
    · exact inf_le_left b a
~~~

Those are theorems about every lattice. On a particular one the engine just computes both sides. Commutativity, idempotence and absorption in $D$ — the last as two cells, since the order world has no nesting: $4 \sqcap 6 = 2$, and then $4 \sqcup 2 = 4$:
`);
m("meet(D, 4, 6)");
m("meet(D, 6, 4)");
m("meet(D, 6, 6)");
m("join(D, 4, 2)");
md(r`
And the order recovered from the meet: $2 \le 6$ because $2 \sqcap 6 = 2$.
`);
m("meet(D, 2, 6)");
m("le(D, 2, 6)", true);
md(r`
## The duality principle

Every lattice has a *dual*: swap $\sqcap \leftrightarrow \sqcup$ and $\le \leftrightarrow \ge$. Any theorem proved in a lattice has a dual theorem for free.

**Theorem (duality principle).** If $\varphi$ is a theorem about lattices, so is the statement obtained by replacing every $\sqcap$ with $\sqcup$, $\sqcup$ with $\sqcap$, $\le$ with $\ge$, $\bot$ with $\top$ and $\top$ with $\bot$.

In Lean the dual is a wrapper type whose ‹LE› flips the original's, and whose lattice instance swaps ‹inf› and ‹sup›:

~~~lean
structure Dual (α : Type) where
  val : α

instance {α : Type} [LE α] : LE (Dual α) where
  le a b := LE.le (α := α) b.val a.val

instance {α : Type} [Lattice α] : Lattice (Dual α) where
  inf := fun a b => ⟨Lattice.sup (α := α) a.val b.val⟩
  sup := fun a b => ⟨Lattice.inf (α := α) a.val b.val⟩
  inf_le_left  := fun a b => Lattice.sup_le_left  (α := α) a.val b.val
  inf_le_right := fun a b => Lattice.sup_le_right (α := α) a.val b.val
  sup_le_left  := fun a b => Lattice.inf_le_left  (α := α) a.val b.val
  sup_le_right := fun a b => Lattice.inf_le_right (α := α) a.val b.val
  le_inf := fun a b c h1 h2 => Lattice.le_sup (α := α) b.val c.val a.val h1 h2
  le_sup := fun a b c h1 h2 => Lattice.le_inf (α := α) c.val a.val b.val h1 h2
~~~

Turning the Hasse diagram upside down exchanges every meet with every join. ‹Dop› from Exercise 1.4 is $D$ upside down, and its meet of $4$ and $6$ is $D$'s join:
`);
m("meet(Dop, 4, 6)", true);
m("join(Dop, 4, 6)");
m("bottom(Dop)");
md(r`
## Important lattice examples

**The two-element lattice $\mathbf{2}$.** ‹Bool› with ‹false < true›; meet is ‹&&›, join is ‹||›, and every axiom is ‹by decide› because the type is finite and the statements decidable. The engine's version is decided the same way:
`);
m("let B = poset({false, true}; false < true)");
m("join(B, false, true)");
m("meet(B, false, true)");
m("lattice(B)", true);
md(r`
**The powerset lattice.** Sets under inclusion, with meet $\cap$ and join $\cup$; the Lean instance's proof obligations are the introduction and elimination rules for $\wedge$ and $\vee$. In $\mathcal{P}(\{x, y\})$, $\{x\}$ and $\{y\}$ are incomparable, their join is the whole set and their meet is empty:
`);
m("let P2 = subsets({x, y})");
m("join(P2, {x}, {y})", true);
m("meet(P2, {x}, {y})", true);
m("lattice(P3)", true);
md(r`
**The divisibility lattice.** On the divisors of a fixed $n$, meet is $\gcd$ and join is $\mathrm{lcm}$ — the Lean instance is a list of core lemmas, ‹Nat.gcd_dvd_left›, ‹Nat.dvd_gcd›, ‹Nat.lcm_dvd›, and so on. The book's figure annotates the diagram of $D$ with $4 \sqcap 6 = \gcd(4, 6) = 2$, $4 \sqcup 6 = \mathrm{lcm}(4, 6) = 12$, $3 \sqcap 4 = 1$, $3 \sqcup 4 = 12$. Every incomparable pair still has a gcd and an lcm in the set, confirming this is a lattice:
`);
m("join(D, 4, 6)");
m("meet(D, 3, 4)");
m("join(D, 3, 4)");
m("lattice(D)", true);
md(r`
**Not every poset is a lattice.** The smallest failure is the “vee”: $a$ below both $b$ and $c$, which have no join because nothing is above both. ‹lattice› names the pair that fails:
`);
m("let V = poset({a, b, c}; a < b, a < c)");
m("lattice(V)", true);
m("lattice(E)", true);
md(r`
— and $E$, the poset from §2.2, fails at exactly the pair the book's caption got wrong.

## Distributive lattices

**Definition.** A lattice is *distributive* if $a \sqcap (b \sqcup c) = (a \sqcap b) \sqcup (a \sqcap c)$ (equivalently, the dual law holds too).

The powerset lattice and Boolean lattices are distributive. The two smallest non-distributive lattices are $\mathbf{M}_3$ — three mutually incomparable middle elements — and the pentagon $\mathbf{N}_5$; a classical theorem says a lattice is distributive if and only if it contains neither as a sublattice.

$\mathbf{M}_3$ is a lattice:
`);
m("let M3 = poset({bot, a, b, c, top}; bot < a, bot < b, bot < c, a < top, b < top, c < top)");
m("lattice(M3)", true);
md(r`
but the distributive law fails at $a \sqcap (b \sqcup c)$. The left side is $a \sqcap \top = a$; the right side is $\bot \sqcup \bot = \bot$; and $a \ne \bot$:
`);
m("join(M3, b, c)");
m("meet(M3, a, top)");
m("meet(M3, a, b)");
m("meet(M3, a, c)");
m("join(M3, bot, bot)");
md(r`
In $\mathbf{N}_5$ — $\bot < p < \top$ and $\bot < q < r < \top$ — take $r \sqcap (p \sqcup q)$: the left side is $r \sqcap \top = r$, the right side $(r \sqcap p) \sqcup (r \sqcap q) = \bot \sqcup q = q$, and $r \ne q$:
`);
m("let N5 = poset({bot, p, q, r, top}; bot < p, bot < q, q < r, p < top, r < top)");
m("lattice(N5)");
m("join(N5, p, q)");
m("meet(N5, r, top)");
m("meet(N5, r, p)");
m("meet(N5, r, q)");
m("join(N5, bot, q)");
md(r`
## Exercises

**3.1 Lattice of intervals.** Define ‹Interval› as pairs $[l, h]$ with $l \le h$, ordered by $[l_1, h_1] \le [l_2, h_2] \iff l_2 \le l_1 \wedge h_1 \le h_2$ — “containment by a smaller interval”, the *precision* or *information* order. Prove it is a partial order; what are meet and join? (Meet is the smallest interval containing both — the convex hull; join is the intersection, when it is non-empty. Chapter 7 makes this the interval lattice of the propagators.)

**3.2 Absorption.** In any lattice, $a \sqcap (a \sqcup b) = a$. The instance in $D$ with $a = 4$, $b = 6$: $4 \sqcup 6 = 12$ and $4 \sqcap 12 = 4$.
`);
m("join(D, 4, 6)");
m("meet(D, 4, 12)");
md(r`
**3.3 Characterising the order.** $a \le b \iff a \sqcup b = b$, from the lattice axioms alone:

~~~lean
theorem le_iff_sup_eq {α : Type} [Lattice α] (a b : α) : a ≤ b ↔ a ⊔ b = b := by
  constructor
  · intro h
    apply PartialOrder.le_antisymm
    · exact Lattice.le_sup a b b h (PartialOrder.le_refl b)
    · exact Lattice.sup_le_right a b
  · intro h
    have : b = a ⊔ b := h.symm
    rw [this]
    exact Lattice.sup_le_left a b
~~~

Checked at one instance — $2 \le 6$ in $D$, and $2 \sqcup 6 = 6$:
`);
m("join(D, 2, 6)");
md(r`
**3.4 The product lattice.** Given lattices $\alpha$ and $\beta$, the component-wise order on $\alpha \times \beta$ is a lattice with component-wise meet and join; each of the eight axioms reduces to the corresponding axiom in one component. ‹Sq› from Exercise 1.3 is $\mathbf{2} \times \mathbf{2}$, and its join of $(0,1)$ and $(1,0)$ is $(1, 1)$ — the join in each coordinate:
`);
m("lattice(Sq)");
m("join(Sq, x01, x10)", true);

// ───────────────────────────── Chapter 4 ─────────────────────────────
sec("4 · Complete Lattices and the Fixed-Point Theorem");
md(r`
Lattices let us take meets and joins of *pairs* of elements. A *complete* lattice extends this to arbitrary (possibly infinite) subsets, and that extra power buys one of the most useful theorems in theoretical computer science: the Knaster–Tarski fixed-point theorem.

## Complete lattices

**Definition.** A lattice $(L, \le)$ is *complete* if every subset $S \subseteq L$ has a supremum $\bigvee S$ and an infimum $\bigwedge S$ in $L$.

> In particular the empty set has a supremum, which is $\bot$, and an infimum, which is $\top$ — so every complete lattice is bounded. Taking $S = L$ gives $\bigvee L = \top$ and $\bigwedge L = \bot$.

~~~lean
abbrev Pred (α : Type) := α → Prop

class CompleteLattice (α : Type) extends Lattice α where
  sSup : Pred α → α    -- supremum of a set  (⨆)
  sInf : Pred α → α    -- infimum of a set   (⨅)
  le_sSup : ∀ (s : Pred α) (a : α), s a → a ≤ sSup s
  sSup_le : ∀ (s : Pred α) (u : α), (∀ a, s a → a ≤ u) → sSup s ≤ u
  sInf_le : ∀ (s : Pred α) (a : α), s a → sInf s ≤ a
  le_sInf : ∀ (s : Pred α) (l : α), (∀ a, s a → l ≤ a) → l ≤ sInf s
~~~

The powerset lattice is the canonical example: $\bigvee \mathcal{F} = \bigcup \mathcal{F}$ and $\bigwedge \mathcal{F} = \bigcap \mathcal{F}$. And *every finite lattice is complete*: the supremum of a finite set is the join of its elements one at a time, so every lattice in this notebook is a complete lattice. ‹upper› and ‹lower› take any set; the least upper bound of $\{2, 3, 4\}$ in $D$ is the least of its upper bounds, and the upper bounds of the *empty* set are everything, whose least element is $\bot$:
`);
m("upper(D, {2, 3, 4})");
m("lower(D, {4, 6, 12})");
m("upper(D, {})");
md(r`
## Why fixed points matter

A *fixed point* of $f : L \to L$ is an element $x$ with $f(x) = x$ — where an iterative process *stabilises*.

- **Propagator networks.** Cell values stop changing when the propagators reach a fixed point of “apply all propagators once”. That stable state is the least fixed point: the most conservative set of conclusions forced by the constraints, nothing more.
- **Dataflow analysis.** A compiler iterates a flow function until it stabilises; the result is its least fixed point.
- **Denotational semantics.** The meaning of a recursive program is the least fixed point of a semantic functional.
- **Regular expressions.** The set matched by $a^*$ is the least fixed point of $S \mapsto \{\varepsilon\} \cup a \cdot S$.

## The Knaster–Tarski fixed-point theorem

**Theorem (Knaster–Tarski, 1955).** Let $(L, \le)$ be a complete lattice and $f : L \to L$ monotone. Then $f$ has a *least fixed point* $\mu f = \bigwedge \{x \mid f(x) \le x\}$ and a *greatest fixed point* $\nu f = \bigvee \{x \mid x \le f(x)\}$.

*Proof.* Let $P = \{x \mid f(x) \le x\}$, the *pre-fixed points*, and $m = \bigwedge P$.

*Step 1: $f(m) \le m$.* For every $x \in P$, $m \le x$, so $f(m) \le f(x) \le x$ by monotonicity. Hence $f(m)$ is a lower bound of $P$, so $f(m) \le m$.

*Step 2: $m \le f(m)$.* Applying $f$ to Step 1 gives $f(f(m)) \le f(m)$, so $f(m) \in P$; since $m$ is the infimum of $P$, $m \le f(m)$.

So $f(m) = m$. Any fixed point $x^*$ has $f(x^*) = x^* \le x^*$, so $x^* \in P$ and $m \le x^*$: $m$ is the *least* fixed point. $\square$

~~~lean
theorem knaster_tarski {α : Type} [CompleteLattice α] (f : α → α) (hf : Monotone f) :
    ∃ (lfp : α), f lfp = lfp ∧ ∀ (x : α), f x = x → lfp ≤ x := by
  let P : Pred α := fun x => f x ≤ x
  let m := sInf P
  have step1 : f m ≤ m := by
    apply le_sInf
    intro x hx
    exact le_trans (hf.map_le m x (sInf_le P x hx)) hx
  have step2 : m ≤ f m := by
    apply sInf_le
    exact hf.map_le _ _ step1
  have fixed : f m = m := le_antisymm step1 step2
  refine ⟨m, fixed, ?_⟩
  intro x hx
  apply sInf_le
  show f x ≤ x
  exact le_of_eq hx
~~~

On a finite lattice the least fixed point can be *reached*: start at $\bot$ and apply $f$ until nothing changes. This is the ascending *Kleene chain* $\bot \le f(\bot) \le f^2(\bot) \le \cdots$, and the engine's ‹lfp› is exactly that iteration, each step shown. Take a monotone map on $D$ with several fixed points:
`);
m("let f = map(D; 1 -> 2, 3 -> 6)");
m("monotone(D, f)");
m("fixpoints(D, f)");
m("lfp(D, f)", true);
m("gfp(D, f)", true);
md(r`
The fixed points are $\{2, 4, 6, 12\}$; the chain from $\bot = 1$ stops at $2$, the least of them, and the chain from $\top = 12$ stops at $12$, the greatest. The rule ‹order.iterate› carries the theorem's content: ‹iter_le_fixed› proves every element of the chain from $\bot$ is below every fixed point, so wherever the chain stops is the least one.

The theorem needs monotonicity, and so does the iteration: without it the chain need not climb, and need not stop at a fixed point at all. ‹lfp› refuses a non-monotone map rather than iterate it — the complement ‹comp› from Chapter 2 flips $1 \mapsto 12 \mapsto 1$ forever:
`);
m("lfp(D, comp)");
md(r`
## Chains and convergence

Chains are the lattice-theoretic version of sequences in calculus, and understanding them is essential to understanding why iterative computations terminate.

**Definition.** A *chain* in a poset is a subset in which every pair is comparable. An *ascending chain* is a chain written as a sequence $a_0 \le a_1 \le a_2 \le \cdots$.

The parallel with calculus is direct:

$$\begin{array}{ll}
\textbf{Calculus} & \textbf{Lattice theory} \\ \hline
\text{sequence } a_0 \le a_1 \le a_2 \le \cdots & \text{ascending chain} \\
\text{limit } \lim_{n\to\infty} a_n & \text{supremum } \bigsqcup_n a_n \\
\text{convergence} & \text{chain stabilising} \\
\text{completeness of } \mathbb{R} & \text{completeness of the lattice} \\
\text{Cauchy sequence} & \text{ascending chain condition}
\end{array}$$

Just as the completeness of $\mathbb{R}$ guarantees every bounded ascending sequence a limit, the completeness of a lattice guarantees every chain a supremum. Without it the supremum might not exist in your structure — exactly as $\sqrt 2$ does not exist in $\mathbb{Q}$ although rational sequences converge to it.

**The ascending chain condition.** A poset satisfies the ACC if every strictly ascending chain $a_0 < a_1 < \cdots$ is finite. Then the Kleene chain must stabilise at some $f^n(\bot) = f^{n+1}(\bot)$: a fixed point in finitely many iterations. Every finite poset satisfies the ACC trivially — a strictly ascending chain in ‹chain(5)› has at most five elements — which is why every ‹lfp› cell in this notebook terminates. ‹FlatNat› in Part II satisfies it too (its chains are $\bot < \mathrm{known}(n)$, length two); the interval lattice does *not* — $[0,10] < [0,9] < [0,8] < \cdots$ — which is why interval propagators need a widening operator.

**$\bot$ is the starting point, not the limit.** The supremum of the Kleene chain is not $\bot$; $\bot$ is its *minimum*. For the sequence $0, \tfrac12, \tfrac34, \tfrac78, \ldots$ the minimum is $0$ and the limit is $1$. The chain in ‹lfp(D, dbl)› starts at $1$ and ends at $4$:
`);
m("lfp(D, dbl)", true);
md(r`
## Exercises

**4.1 Greatest fixed point.** Using the Knaster–Tarski proof as a template, prove the existence of $\nu f = \bigvee \{x \mid x \le f(x)\}$. Dualise every step: post-fixed points, $\bigvee$ for $\bigwedge$, ‹le_sSup› for ‹sInf_le›. ‹gfp› is the dual iteration, from $\top$ down:
`);
m("gfp(D, dbl)", true);
m("gfp(D, one)", true);
md(r`
**4.2 Ascending Kleene chain.** Prove in Lean that each element of $\bot, f(\bot), f^2(\bot), \ldots$ is $\le$ the next. Induction on $n$: $\bot \le f(\bot)$ since $\bot$ is least, and $f^n(\bot) \le f^{n+1}(\bot)$ gives $f^{n+1}(\bot) \le f^{n+2}(\bot)$ by ‹hf.map_le›. Each ‹order.iterate› step in the derivations above is one instance of the induction step — and ‹le› confirms any of them:
`);
m("le(D, 2, 4)", true);

// ───────────────────────────── Coda ─────────────────────────────
sec("Where Part II goes");
md(r`
The rest of the book leaves finite mathematics for programs: propagator *cells* that accumulate partial information (Chapter 5), a scheduler and network in Lean 4 with monotonicity proofs for ‹addProp› and ‹subProp› (Chapter 6), the interval lattice of Exercise 3.1 (Chapter 7), and two capstones — a Sudoku solver whose domains are the *dual* powerset of Exercise 1.4, and type inference by propagation on a type lattice. The load-bearing facts in all of them are the ones checked here: the order is a partial order, the propagators are monotone, and the network's quiescent state is the least fixed point of Knaster–Tarski, reached along the Kleene chain because the lattices satisfy the ascending chain condition.

**What the engine checked.** Every order-world cell above runs on rules in the ledger's verified column: ‹order.closure› (the three laws, ‹checkPartialOrder_none›), ‹order.covers› (‹covers_spec›), ‹order.upper-bounds› / ‹order.least› (‹sup_spec›, ‹sup_none›) and their duals, ‹order.lattice›, ‹order.cover› for ‹le›, ‹order.monotone› (‹monotone_of_none›), and ‹order.iterate› / ‹order.fixed› (‹iter_le_fixed›). The Lean theorems quoted in code blocks are the book's; they are about all posets and lattices, and are checked by Lean in the ‹lean4learning› repository rather than by this engine.

**What the engine does not have yet**, found by writing this notebook: a product-poset constructor and a dual (Exercises 1.3, 1.4 are written out by hand); maps between *different* posets and maps whose table uses set literals, so $S \mapsto S \cup \{x\}$ on a powerset cannot be typed; nested order expressions such as ‹meet(D, 4, join(D, 4, 6))›; a ‹distributive(P)› check; and an $n$-ary ‹sup› / ‹inf› of a set, which ‹upper› and ‹lower› only approximate.
`);

const nb = { chalk: 1, name: "order-lattices.chalk", cells, scenes: [] };
writeFileSync(new URL("../../notebooks/order-lattices.chalk", import.meta.url), JSON.stringify(nb, null, 2) + "\n");
const n = (t) => cells.filter((c) => (c.type ?? "math") === t).length;
console.log(`${cells.length} cells: ${n("math")} math, ${n("markdown")} markdown, ${n("section")} sections`);
