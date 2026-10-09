/**
 * @chalkmath/protocol — the contract between a notebook frontend and a math engine.
 *
 * Design rules (see ARCHITECTURE.md §2; rule 5: new capabilities are optional fields, never changes):
 *  1. Everything crossing the boundary is plain JSON. No classes, no functions, no BigInt.
 *  2. Transport is abstract. A Transport moves JSON-RPC 2.0 messages; it does not know what they mean.
 *  3. Expressions are trees with *paths* (child-index lists). Paths are the provenance key that
 *     lets the frontend map "the thing I selected" back to "the step that produced it".
 *  4. The engine is stateful per *session* (a notebook), stateless across sessions.
 */

// ---------------------------------------------------------------------------
// Wire expression representation (JSON-safe)
// ---------------------------------------------------------------------------

/** Exact rational as decimal strings so BigInt survives JSON. "3" / "1" for integers. */
export interface WireRational { num: string; den: string }

export type WireExpr =
  | { k: "num"; v: WireRational }
  | { k: "var"; name: string }
  | { k: "add"; args: WireExpr[] }
  | { k: "mul"; args: WireExpr[] }
  | { k: "pow"; base: WireExpr; exp: WireExpr }
  | { k: "fn"; name: string; args: WireExpr[] }
  | { k: "matrix"; rows: WireExpr[][] };

/** A path from the root of an expression to a subterm: child indices. [] is the root. */
export type Path = number[];

// ---------------------------------------------------------------------------
// Derivations — the "show work" data model
// ---------------------------------------------------------------------------

/** One rewrite. `path` locates where in `before` the rule fired; `after` is the whole term after. */
export interface Step {
  /** Machine name, e.g. "diff.product", "simp.collect-like-terms", "la.row-swap". */
  rule: string;
  /** Human explanation of *why* this step is valid, for show-work mode. Markdown + $latex$. */
  explanation: string;
  path: Path;
  before: WireExpr;
  after: WireExpr;
  /** `before`, rendered: what the step started from — not always the previous step's `after`, since the
   *  pipeline canonicalizes (flattens, reorders) silently between recorded steps. */
  beforeRendered?: Rendered;
  /** `after`, rendered (no path annotations). Optional; used by the notebook's Manim Studio to animate steps. */
  afterRendered?: Rendered;
  /** λ-cells: the same term after the step, with de Bruijn indices. */
  afterDeBruijn?: Rendered;
  /** Nested derivation (e.g. simplification that ran inside a differentiation step). */
  sub?: Derivation;
}

export interface Derivation {
  input: WireExpr;
  steps: Step[];
  output: WireExpr;
  /** `input`, rendered (with path annotations when requested): what the first step rewrote. */
  inputRendered?: Rendered;
}

/** A step without its terms: what an `outline` reply carries (see `EvaluateParams.outline`). */
export interface StepOutline {
  rule: string;
  explanation: string;
  path: Path;
  /** The term prints the same before and after the step (a one-factor product unwrapped), and the
   *  step has no nested work: a frontend folds it. Absent means false. */
  quiet?: boolean;
  sub?: Outline;
}

/** A derivation without its terms: rules, explanations and paths, in step order. Its size is what
 *  the steps say, not what the terms weigh; `engine.steps` sends the derivation itself. */
export interface Outline { steps: StepOutline[] }

// ---------------------------------------------------------------------------
// Rendering
// ---------------------------------------------------------------------------

export interface Rendered {
  text: string;
  /** LaTeX. If `paths` was requested, subterms are wrapped in \htmlData{path=0.1.2}{...}. */
  latex: string;
}

// ---------------------------------------------------------------------------
// Requests / responses (the RPC surface). Keep this small; grow it deliberately.
// ---------------------------------------------------------------------------

/** Proof status of one rewrite rule, as reported by the engine. */
export interface RuleStatus {
  rule: string;
  /** "verified": unconditional soundness theorem. "conditional": theorem with a side condition,
   *  whose necessity is itself proved. "checked": a guess whose result a later step verifies (the
   *  integration finder, checked by differentiation). "unverified": no theorem yet. Rules the
   *  engine omits are unverified. */
  status: "verified" | "conditional" | "checked" | "unverified";
  note: string;
  /** The rule's status over ℂ, when it has a theorem there (`proofs/Proofs/Cx.lean`). A cell whose
   *  input or output mentions `i` is read in the complex semantics and shows this instead; a rule
   *  without it is unverified in such a cell. Optional (rule 5). */
  complex?: { status: "verified" | "conditional" | "checked" | "unverified"; note: string };
}

export interface EngineCapabilities {
  engine: string;              // "engine-ts" | "engine-lean" | ...
  version: string;
  verified: boolean;           // true iff the implementation has machine-checked proofs
  features: string[];          // "simplify", "diff", "linalg", "integrate", ...
  /** Per-rule proof status, so a frontend can mark derivation steps. Optional; absent means unknown. */
  ruleStatus?: RuleStatus[];
  /** M5: how the engine knows evaluation terminates. */
  termination?: { status: 'proven' | 'fuel'; theorem?: string; summary: string };
}

export interface EvaluateParams {
  sessionId: string;
  cellId: string;
  source: string;
  /** Include the derivation. Off by default — derivations can be large. */
  showWork?: boolean;
  /** Emit \htmlData path annotations in LaTeX so the UI can map selections to subterms. */
  paths?: boolean;
  /** With `showWork`: reply with the derivation's `outline` instead of the derivation. Every step
   *  carries the whole term before and after it, so the derivation of a big term (a table's worth of
   *  numbers) is large where its outline is not; `engine.steps` sends the derivation when the work
   *  is opened. Optional (rule 5). */
  outline?: boolean;
}

/**
 * A declarative picture the frontend may draw (ARCHITECTURE.md §5). The engine never renders;
 * it describes. `kind` is namespaced by the math module that produced it (e.g. "linalg.heatmap",
 * "group.cayley-table", "plot.samples"); `data` is that kind's own JSON schema.
 */
export interface VisualSpec { kind: string; title?: string; data: unknown }
/** `logic.truthtable` (a `truthtable(φ)` cell): the variables, the formula, and one row per
 *  assignment — the variables' values in order, then the formula's. */
export interface TruthTableData { vars: string[]; formula: Rendered; rows: boolean[][] }
/** `relation.digraph` (a relation cell): the elements, the pairs as arrows, and the arrows to mark —
 *  `bad`, those that show a property failing (a pair whose reverse is missing, two that chain without
 *  their composite, …), and `added`, those a closure added. */
export interface DigraphData {
  nodes: string[]; edges: [string, string][]; bad: [string, string][]; added: [string, string][];
  /** Each node's layer (a state's distance from an initial one), for a layered drawing. Optional. */
  layers?: number[];
  /** Each arrow's label, in the order of `edges` (a state graph's: the actions that take it). Optional. */
  labels?: string[];
  /** Where each step of the cell's derivation is on the graph, in step order: the transition it takes,
   *  or the state it is at; `null` for a step that is not on it. Optional (a state graph's). */
  steps?: ({ edge?: [string, string]; node?: string } | null)[];
}
/** `algebra.optable` (an operation cell, or a law checked on one): the set, the table row by row
 *  (`rows[i][j]` is `elems[i] · elems[j]`), and the cells to mark, as `[row element, column element]`. */
export interface OpTableData { elems: string[]; rows: string[][]; marks: [string, string][] }
/** `context.table` (a formal context): objects, attributes, and which object has which. */
export interface ContextTableData { objects: string[]; attributes: string[]; has: boolean[][] }
/** `typing.tree` (a typing derivation): each node a judgment `Γ ⊢ t : T`, the rule that concludes it,
 *  and the derivations of its premises (none for Var). Long contexts are named in the judgments' LaTeX
 *  (Γ₁, Γ₂, …), and `legend` says what each name stands for; a node's `text` writes its context out. */
export interface TypingNode { rule: string; latex: string; text: string; premises: TypingNode[] }
export interface TypingTreeData { root: TypingNode; legend?: { latex: string; text: string }[] }
/** `replicas.spacetime` (a replica simulation): a lane per replica, the events in order (each with its
 *  lane, a label, and the replica's state after it), the messages as arrows from one event to another,
 *  and, per step of the derivation, the events it made. */
export interface SpacetimeData {
  lanes: string[]; events: { lane: string; label: string; state: string }[]; messages: [number, number][];
  steps: number[][];
}
export type KnownVisual =
  | { kind: "logic.truthtable"; title?: string; data: TruthTableData }
  | { kind: "relation.digraph"; title?: string; data: DigraphData }
  | { kind: "algebra.optable"; title?: string; data: OpTableData }
  | { kind: "context.table"; title?: string; data: ContextTableData }
  | { kind: "typing.tree"; title?: string; data: TypingTreeData }
  | { kind: "replicas.spacetime"; title?: string; data: SpacetimeData };

export interface EvaluateResult {
  ok: true;
  value: WireExpr;
  rendered: Rendered;
  derivation?: Derivation;
  /** With `showWork` and `outline`: the derivation's steps without their terms, in place of `derivation`. */
  outline?: Outline;
  /** Names bound by this cell (e.g. `let f = x^2`). */
  bound?: string[];
  /** With `bound`: the parameters when the binding defined a function (`let f(x, y) = e`). */
  params?: string[];
  /** What to draw for this result, beside the value: `KnownVisual` lists the kinds the engine sends. Optional (rule 5). */
  visuals?: VisualSpec[];
  /** The parsed input, rendered by the engine (the frontend owns no printer). Sent with `showWork`.
   *  For the other worlds' cells (order, systems, a logic command) it is the input as written, its
   *  pieces read by their grammars and its separators unlabelled, not the value the derivation
   *  starts from; explain on `{ kind: "input" }` addresses that reading. */
  inputRendered?: Rendered;
  /** The evaluation's number in the session — Mathematica's `In[n]`/`Out[n]` — which `%`, `%%`
   *  and `%n` in later cells refer to. Every evaluation takes one, error or not. Optional (rule 5). */
  label?: number;
  /** Which semantics the cell is read in: "complex" when the input or output mentions `i`,
   *  otherwise "real". Decides which of a rule's statuses applies. Optional (rule 5). */
  semantics?: "real" | "complex";
  /** Things about the input worth a word under the answer, such as a variable named `e` (not
   *  Euler's number `ℯ`). Optional (rule 5). */
  warnings?: string[];
}

export interface EvaluateError {
  ok: false;
  error: { code: string; message: string; span?: { start: number; end: number } };
  /** The evaluation's number (see `EvaluateResult.label`); a failed evaluation still takes one. */
  label?: number;
}

export interface ExplainParams {
  sessionId: string;
  cellId: string;
  /** Path into the chosen term of the cell (the output unless `term` says otherwise). */
  path: Path;
  /** Which term the path is into: the output (default), the input, or the term after step `index`. Optional. */
  term?: { kind: "output" } | { kind: "input" } | { kind: "step"; index: number };
}

/** How a step relates to the selected subterm (M6 origin tracking). */
export interface StepRelation {
  /** Index into the cell's derivation steps. */
  index: number;
  /** `created`: the rule built this node. `copied`: it moved or duplicated it. `contains`: it fired below it. */
  relation: "created" | "copied" | "contains";
}

export interface ExplainResult {
  /** The subterm at `path` and the steps that produced it, traced backwards through the derivation. */
  subterm: WireExpr;
  rendered: Rendered;
  steps: Step[];
  /** Same steps with how each one relates, in derivation order. Optional (M6). */
  trace?: StepRelation[];
}

/** `plot(f, x, from, to[, n])` or `plot([f, g, …], x, from, to[, n])`: the engine simplifies the
 *  function (or the list, entrywise) under the session, records the cell like any other (so
 *  `engine.explain` works on it), and samples each curve on a uniform grid. Drawing is the
 *  frontend's; a sample is `null` where the curve has no finite value. Optional method (rule 5). */
/** `quiet`: a scene's sample, not an evaluation — the session is left as it was, no `In[n]` is
 *  taken and `%` is untouched. Optional (rule 5). */
export interface PlotParams { sessionId: string; cellId: string; source: string; showWork?: boolean; paths?: boolean; outline?: boolean; quiet?: boolean }
/** One curve: its normalized term (rendered) and its samples. A `parametric` curve is complex-valued
 *  and its samples are `[re, im]` — a point in the plane rather than `[t, y]`. */
export interface PlotSeries { rendered: Rendered; points: [number, number | null][]; parametric?: boolean }
/** `epicycles(f, t)` / `dft(points)`: one rotating circle — frequency `k`, coefficient `c_k` as a
 *  number (and as the exact term when the sum was symbolic). */
export interface Epicycle { k: number; re: number; im: number; rendered?: Rendered }
export interface PlotResult {
  ok: true; kind: "plot";
  value: WireExpr; rendered: Rendered;
  var: string; from: number; to: number;
  series: PlotSeries[];
  /** Non-empty for `epicycles` and `dft`: the circles, in frequency order. */
  terms?: Epicycle[];
  derivation?: Derivation; outline?: Outline; inputRendered?: Rendered; label?: number;
}

/** `manipulate(e, p, from, to[, frames])`, Mathematica's `Manipulate`: the body `e` evaluated as a
 *  cell would be, once for each of `frames` values of `p` evenly spaced from `from` to `to` (either
 *  way round; the first is where the slider starts). Each frame carries `p`'s value (as a number to
 *  place it and as the engine prints it), the body's normal form there, and, when the body is a
 *  `plot`, that frame's samples. The cell's value, rendering and work are the first frame's.
 *  Optional method (rule 5). */
export interface ManipulateFrame {
  value: number; valueRendered: Rendered; rendered: Rendered;
  plot?: ManipulatePlot;
  /** A body that is not a plot: its calculation at this value, from the body with `p` put in to the
   *  value, each step's whole term (one that prints like the one before left out). Absent when the
   *  value is all there is. */
  work?: Rendered[];
  /** A `column(e₁, e₂, …)` body (Mathematica's `Column`): each part, evaluated as its own cell. */
  parts?: ManipulatePart[];
}
export interface ManipulatePlot { var: string; from: number; to: number; series: PlotSeries[]; terms?: Epicycle[] }
/** One part of a column: its value, the session name it was written as (`m`), and its samples when
 *  it is a plot or its calculation otherwise. */
export interface ManipulatePart { rendered: Rendered; label?: string; plot?: ManipulatePlot; work?: Rendered[] }
export interface ManipulateResult {
  ok: true; kind: "manipulate";
  value: WireExpr; rendered: Rendered;
  param: string;
  frames: ManipulateFrame[];
  derivation?: Derivation; outline?: Outline; inputRendered?: Rendered; label?: number;
}

/** M-λ: a λ-cell's reply carries the de Bruijn view of the result and of every step
 *  (`Step.afterDeBruijn`), and a reading when the normal form is a Church numeral or boolean. */
export interface HasseData { nodes: { name: string; height: number }[]; covers: [string, string][] }
/** The other worlds' extras on an evaluate reply. λ-cells (`kind: "lambda"`): the de Bruijn view of
 *  the result and of every step (`Step.afterDeBruijn`), and a reading when the normal form is a
 *  Church numeral or boolean, or when it says why reduction stopped. Order cells (`kind: "poset"`,
 *  relations included): what to draw (elements with their height, the covers = Hasse edges); a
 *  relation's graph comes as a `relation.digraph` visual. Logic cells (`kind: "logic"`): for
 *  `truthtable` a `logic.truthtable` visual; a counterexample, witness or distinguishing row is in
 *  the work, and `sat`/`falsify` answer with the assignment itself. Systems cells (`kind: "system"`):
 *  the state graph as a `relation.digraph` visual (a counterexample's transitions marked), and a
 *  trace as the derivation, a step per action. `summary` is a note beside the answer, sent only when
 *  it says something neither the answer nor the work does (a system's reachable states, a rewriting
 *  system's rule names, `critical`'s verdict). */
export interface WorldExtras {
  kind?: "lambda" | "poset" | "logic" | "system";
  renderedDeBruijn?: Rendered; reading?: string;
  hasse?: HasseData; summary?: string;
}

/** The derivation of the cell's last evaluation in the session, with its terms: what an `outline`
 *  reply left out. A cell the session has not evaluated is an error. Optional method (rule 5). */
export interface StepsParams { sessionId: string; cellId: string; paths?: boolean }
export interface StepsResult { derivation: Derivation; inputRendered: Rendered }

/** An exercise: `source` is the question (an expression or a λ-term), whose value is the expected
 *  answer and whose derivation is the worked solution; `answer`, when sent, is compared with it. Both
 *  are reduced to a normal form and the two forms compared, as two λ-terms are β-equivalent when they
 *  reduce to the same normal form: expressions in the canonical form the integration check uses
 *  (distributed, `cos² = 1 − sin²`, `(eᵘ)ᵏ = eᵏᵘ`, then simplified), λ-terms up to α. An answer that
 *  calls a function the question uses for its work (other than the elementary functions) is refused,
 *  and a λ answer must already be a normal form. The question is recorded as `cellId` (so
 *  `engine.steps` and `engine.explain` work on the solution) but nothing is bound and no label is
 *  taken: `%` is untouched. Optional method (rule 5). */
export interface CheckParams {
  sessionId: string; cellId: string; source: string;
  answer?: string;
  showWork?: boolean; paths?: boolean; outline?: boolean;
}
export interface CheckResult {
  ok: true; kind: "exercise" | "lambda";
  /** The expected answer, and the normal form answers are compared against. */
  rendered: Rendered; normalForm: Rendered;
  /** The question, as the engine reads it. */
  inputRendered: Rendered;
  derivation?: Derivation; outline?: Outline;
  /** With `answer`: its value and normal form, or why it could not be compared. */
  answer?: { ok: true; rendered: Rendered; normalForm: Rendered } | EvaluateError;
  /** With `answer`: whether its normal form is the expected one. "Not equivalent" means "not shown
   *  equivalent": the canonical form decides the identities it applies, not every identity. */
  equivalent?: boolean;
}

export interface Methods {
  "engine.capabilities": { params: Record<string, never>; result: EngineCapabilities };
  "engine.evaluate":     { params: EvaluateParams; result: (EvaluateResult & WorldExtras) | EvaluateError };
  "engine.explain":      { params: ExplainParams; result: ExplainResult };
  "engine.steps":        { params: StepsParams; result: StepsResult };
  "engine.resetSession": { params: { sessionId: string }; result: { ok: true } };
  "engine.plot":         { params: PlotParams; result: PlotResult | EvaluateError };
  "engine.manipulate":   { params: PlotParams; result: ManipulateResult | EvaluateError };
  "engine.check":        { params: CheckParams; result: CheckResult | EvaluateError };
}
export type MethodName = keyof Methods;

// ---------------------------------------------------------------------------
// JSON-RPC 2.0 envelope + transport abstraction
// ---------------------------------------------------------------------------

export interface RpcRequest<M extends MethodName = MethodName> {
  jsonrpc: "2.0"; id: number | string; method: M; params: Methods[M]["params"];
}
export interface RpcSuccess<M extends MethodName = MethodName> {
  jsonrpc: "2.0"; id: number | string; result: Methods[M]["result"];
}
export interface RpcFailure {
  jsonrpc: "2.0"; id: number | string | null; error: { code: number; message: string; data?: unknown };
}
export type RpcResponse = RpcSuccess | RpcFailure;

/**
 * A Transport moves opaque JSON strings. Implementations: postMessage (web worker),
 * fetch (HTTP), WebSocket, stdio (child process running the Lean engine).
 */
export interface Transport {
  send(msg: string): void;
  onMessage(handler: (msg: string) => void): void;
  /** The far end is gone (a worker that failed to load or crashed): every pending call fails with
   *  this error rather than waiting forever. Optional; a transport without it never reports one. */
  onError?(handler: (e: Error) => void): void;
  close?(): void;
}

/** The thing a frontend holds. Built from a Transport by `createClient`. */
export interface EngineClient {
  call<M extends MethodName>(method: M, params: Methods[M]["params"]): Promise<Methods[M]["result"]>;
  close(): void;
  /** Called when the transport reports the engine gone (see `Transport.onError`). Optional. */
  onError?(handler: (e: Error) => void): void;
}

/** The thing an engine implements. Hosted over a Transport by `serve`. */
export interface EngineHandler {
  handle<M extends MethodName>(method: M, params: Methods[M]["params"]): Promise<Methods[M]["result"]>;
}

/** An error reply from the engine, with its JSON-RPC code (`-32601` for a method this engine does
 *  not have, which an old frontend against a new engine, or the reverse, can tell from a failure). The
 *  message keeps the `code: message` form the hosts and the notebook show. */
export class RpcError extends Error {
  constructor(public readonly code: number, message: string, public readonly data?: unknown) {
    super(`${code}: ${message}`);
    this.name = "RpcError";
  }
  /** The message without the code in front, for a host that forwards the error with its code. */
  get detail(): string { return this.message.replace(/^-?\d+: /, ""); }
}

export function createClient(t: Transport): EngineClient {
  let nextId = 1;
  const pending = new Map<number | string, { resolve: (v: unknown) => void; reject: (e: Error) => void }>();
  const failAll = (e: Error) => { for (const p of pending.values()) p.reject(e); pending.clear(); };
  // the engines answer in order, so a reply that names no call is the oldest call's
  const failOldest = (e: Error) => {
    const oldest = pending.keys().next();
    if (oldest.done) return;
    const p = pending.get(oldest.value)!;
    pending.delete(oldest.value);
    p.reject(e);
  };
  const listeners: ((e: Error) => void)[] = [];
  t.onError?.((e) => { failAll(e); for (const l of listeners) l(e); });
  t.onMessage((raw) => {
    let msg: RpcResponse | null = null;
    try { msg = JSON.parse(raw) as RpcResponse; } catch { /* not JSON: answered below */ }
    if (!msg || typeof msg !== "object") {
      // a reply that is not JSON-RPC fails the oldest call instead of throwing in the transport's
      // listener (which kills a Node host) and leaving it pending
      failOldest(new Error(`the engine sent a reply that is not JSON-RPC: ${raw.slice(0, 80)}`));
      return;
    }
    if (msg.id === null || msg.id === undefined) {
      // an error with no id says the request could not be read (a body the host refused, a parse
      // error): it is the oldest call's answer, not a notification to drop
      if ("error" in msg && msg.error) failOldest(new RpcError(msg.error.code, msg.error.message, msg.error.data));
      return;
    }
    const p = pending.get(msg.id);
    if (!p) return;
    pending.delete(msg.id);
    if ("error" in msg) p.reject(new RpcError(msg.error.code, msg.error.message, msg.error.data));
    else p.resolve(msg.result);
  });
  return {
    call(method, params) {
      const id = nextId++;
      const req: RpcRequest = { jsonrpc: "2.0", id, method, params };
      return new Promise((resolve, reject) => {
        pending.set(id, { resolve: resolve as (v: unknown) => void, reject });
        // a send that throws (a closed socket, a worker gone) fails this call now, and does not
        // leave an entry that would take the next reply meant for another call
        try { t.send(JSON.stringify(req)); }
        catch (e) { pending.delete(id); reject(e instanceof Error ? e : new Error(String(e))); }
      });
    },
    // closing abandons what is in flight: those calls fail now instead of never settling
    close() { t.close?.(); failAll(new Error("the engine connection was closed")); },
    onError(handler) { listeners.push(handler); },
  };
}

/** The error object a host answers with: an engine's own error keeps its code and data, anything
 *  else is `-32000` with the message. */
export function rpcErrorOf(e: unknown): RpcFailure["error"] {
  if (e instanceof RpcError) return { code: e.code, message: e.detail, ...(e.data !== undefined ? { data: e.data } : {}) };
  return { code: -32000, message: e instanceof Error ? e.message : String(e) };
}

export function serve(t: Transport, engine: EngineHandler): void {
  t.onMessage(async (raw) => {
    let req: RpcRequest;
    try { req = JSON.parse(raw) as RpcRequest; }
    catch { t.send(JSON.stringify({ jsonrpc: "2.0", id: null, error: { code: -32700, message: "Parse error" } })); return; }
    if (!req || typeof req !== "object" || typeof req.method !== "string") {
      t.send(JSON.stringify({ jsonrpc: "2.0", id: null, error: { code: -32600, message: "Invalid Request" } })); return;
    }
    try {
      const result = await engine.handle(req.method, req.params as never);
      t.send(JSON.stringify({ jsonrpc: "2.0", id: req.id, result }));
    } catch (e) {
      t.send(JSON.stringify({ jsonrpc: "2.0", id: req.id, error: rpcErrorOf(e) }));
    }
  });
}
