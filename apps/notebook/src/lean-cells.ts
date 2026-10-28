/**
 * Lean cells: the notebook's side of @chalkmath/lean-editor (packages/lean-editor).
 *
 * One Lean document per notebook: the notebook's Lean cells, in order, are that document's cells, so a
 * definition in one is in scope in the next. Each cell shows an editor (the VS Code editor with the Lean 4
 * extension) and, as its output, the messages Lean reports on its lines; the infoview — goals at the
 * cursor — sits in the panel. Lean checks as you type: there is no Run.
 *
 * Nothing is loaded until a notebook has a Lean cell: the editor (dist/lean/lean-editor.js) and Lean's
 * server (a web worker running Lean compiled to wasm, with its library) are large, and the server is
 * threaded, so the page must be cross-origin isolated. A static host cannot send the headers that asks
 * for, so a service worker (coi-sw.js) adds them; it is registered the first time Lean is wanted, and
 * the page reloads once.
 */
import type { LeanNotebook, LeanMessage, CellView, LeanOptions } from "@chalkmath/lean-editor/types";
import { versioned } from "./version.js";

export type { LeanMessage };
declare const __LEAN_BUILT__: boolean;
const PREF = "chalkmath.lean";

/** `held`: not started, because the page stopped the last time Lean started in it (see `STARTING`). */
export type LeanState = "off" | "isolating" | "starting" | "ready" | "failed" | "held";
let state: LeanState = "off";
let failure = "";
let session: LeanNotebook | null = null;
let starting: Promise<LeanNotebook | null> | null = null;
/** The worker running Lean's server, and the channel its loading progress comes on, while it runs. */
let server: Worker | null = null;
let progressChannel: BroadcastChannel | null = null;
/** Which notebook the document holds, and its cells' ids in order, as last synced. */
let docKey: unknown = null;
let syncedIds: string[] = [];
/** Each cell's editor lives in a container of its own, created once: the notebook rebuilds its cells on
 *  every render, and moves the container into the new cell rather than making a new editor (disposing
 *  the editor Lean's extension tracks as active leaves the infoview on a stale position). */
const views = new Map<string, { view: CellView; box: HTMLElement }>();
const pending = new Map<string, { el: HTMLElement; src: string }>();

let infoviewEl: HTMLElement | null = null;
/** The infoview's host. It must never move in the DOM (its iframe would reload), so the panel shows or
 *  hides it in place. */
export function infoview(): HTMLElement {
  if (!infoviewEl) { infoviewEl = document.createElement("div"); infoviewEl.className = "leaninfo"; }
  return infoviewEl;
}

export const leanState = () => state;
/** Why Lean is not running, as a sentence the notebook shows. */
export const leanFailure = () => failure;
/** The cell, and the line in it, Lean was checking when its server stopped (null: none, or not known). */
let stoppedAt: { id: string; line: number } | null = null;
export const leanStoppedAt = () => stoppedAt;
/** The first line (1-based) of the document Lean is still checking, from its `$/lean/fileProgress`. */
let checkingLine: number | null = null;

/** Where Lean is in loading, while it loads (null once it has checked the notebook, or before it starts):
 *  the editor, then Lean's download (reported by its worker, packages/engine-host/src/worker-lean-server.ts),
 *  then Lean loading its library and checking the notebook for the first time. */
export type LeanProgress = { phase: "editor" } | { phase: "starting" } | { phase: "download"; loaded: number; total: number } | { phase: "checking" };
let progress: LeanProgress | null = null;
export const leanProgress = () => progress;
const setProgress = (p: LeanProgress | null) => { progress = p; progressSoon(); };
/** Tells the notebook where Lean is, once a frame at most: Lean reports its checking many times a second. */
let progressFrame = 0;
const progressSoon = () => {
  if (!progressFrame) progressFrame = requestAnimationFrame(() => { progressFrame = 0; hooks?.onProgress(); });
};
/** Where Lean is in checking the document while it does: the first line it has still to check, of how many,
 *  and the cell (and line in it) that line is in. */
export function leanChecking(): { line: number; lines: number; at: { id: string; line: number } | null } | null {
  if (!session || !busy || checkingLine === null) return null;
  return { line: checkingLine, lines: session.lineCount(), at: session.cellAt(checkingLine) };
}

export interface LeanHooks {
  dark: boolean;
  onSource(id: string, src: string): void;
  onMessages(id: string, messages: LeanMessage[]): void;
  onState(): void;
  onProgress(): void;
  /** Lean has finished (or started) checking the document as it is now. */
  onChecked?(): void;
  /** The packs of modules (lean/courses/…, scripts/lean-courses.mjs) a server needs for these imports. */
  packs?(imports: string[]): string[];
}
let hooks: LeanHooks | null = null;
/** The theme Lean should show: the notebook's, which can change after Lean has started. */
let dark = true;

const setState = (s: LeanState, why = "") => {
  state = s; failure = why;
  if (s === "failed") settled();   // ("ready" is the editor: Lean itself is still loading)
  hooks?.onState();
};
const notStarted = (why: string) => setState("failed", `Lean did not start: ${why}`);
/** A browser gives each of its threads a small stack (Chromium: 500 KB to a worker, against the 8 MB Lean's
 *  threads have natively), and Lean compiled to wasm needs more of it per level of recursion than native
 *  Lean: Lean that elaborates deep enough runs out of it, and the thread's error stops the whole server. */
const OUT_OF_STACK = "it ran out of stack. A browser gives Lean far less stack than it has natively, and something here nests too deeply for it (a long do block, say: smaller definitions help)";

/** Set while Lean starts, until it has checked its first document, and cleared when the page is left. A page
 *  that finds it set was loaded after the browser stopped the page before it while Lean was starting:
 *  out of memory, most likely (Lean and its library take over a gigabyte; iOS Safari ends such a page,
 *  reloads it, and gives up with "A problem repeatedly occurred" once Lean has stopped it a few times).
 *  Lean then waits to be asked, so the rest of the notebook still works. */
const STARTING = "chalkmath.lean.starting";
const HELD = "Lean did not start: the last time it started here, the browser stopped the page, most likely because Lean needs more memory than it allows a page (over a gigabyte)";
const marked = () => { try { return localStorage.getItem(STARTING) !== null; } catch { return false; } };
const mark = (on: boolean) => { try { if (on) localStorage.setItem(STARTING, String(Date.now())); else localStorage.removeItem(STARTING); } catch { /* private mode */ } };
/** Whether Lean is starting in this page: the mark is set while it is and the page is shown. */
let marking = false;
/** Lean has checked its first document, or stopped on its own. */
const settled = () => { if (marking) { marking = false; mark(false); } };
addEventListener("pagehide", () => { if (marking) mark(false); });
addEventListener("pageshow", () => { if (marking) mark(true); });   // back from the back-forward cache
let held = marked();

/** Browsers that honor `Cross-Origin-Embedder-Policy: credentialless`, which leaves images from other
 *  sites loading (require-corp, Safari's only option, blocks those that do not opt in). */
const credentialless = () => "chrome" in window || /Firefox\//.test(navigator.userAgent);

/** Registers the header-adding service worker and reloads, unless that already happened in this tab
 *  (a browser without service workers, or one that refuses them, would reload forever). */
async function isolate(): Promise<void> {
  try { localStorage.setItem(PREF, "on"); } catch { /* private mode */ }
  if (!("serviceWorker" in navigator)) { notStarted("this browser has no service workers, which Lean cells need to isolate the page"); return; }
  if (sessionStorage.getItem("chalkmath.isolating")) {
    notStarted("the page could not be cross-origin isolated (its service worker was not allowed to add the headers)");
    return;
  }
  setState("isolating");
  sessionStorage.setItem("chalkmath.isolating", "1");
  await navigator.serviceWorker.register(`coi-sw.js?coep=${credentialless() ? "credentialless" : "require-corp"}`);
  await navigator.serviceWorker.ready;
  location.reload();
}

/** On page load: a browser that has used Lean cells keeps its service worker; once isolated, forget the
 *  reload guard. */
export function initLeanIsolation() {
  if (self.crossOriginIsolated) { sessionStorage.removeItem("chalkmath.isolating"); return; }
  let wanted = false;
  try { wanted = localStorage.getItem(PREF) === "on"; } catch { /* private mode */ }
  if (wanted && "serviceWorker" in navigator && !navigator.serviceWorker.controller && !sessionStorage.getItem("chalkmath.isolating")) void isolate();
}

/** Starts Lean (once) for a notebook that has Lean cells. */
export function ensureLean(h: LeanHooks): Promise<LeanNotebook | null> {
  hooks = h;
  if (starting) return starting;
  dark = h.dark;
  if (held) { if (state !== "held") setState("held", HELD); return Promise.resolve(null); }
  if (typeof __LEAN_BUILT__ === "boolean" && !__LEAN_BUILT__) {
    notStarted("this copy of ChalkMath was built without Lean itself (npm run lean-wasm, then npm run bundle)");
    return Promise.resolve(null);
  }
  if (!self.crossOriginIsolated) { void isolate(); return Promise.resolve(null); }
  marking = true; mark(true);
  setState("starting");
  setProgress({ phase: "editor" });
  starting = (async () => {
    try {
      const url = new URL(versioned("lean/lean-editor.js"), location.href).href;
      const mod = (await import(url)) as { startLean(o: LeanOptions): Promise<LeanNotebook> };
      const worker = startServer();
      const started = dark;
      const next = await mod.startLean({ worker, infoview: infoview(), dark: started,
        onSource: (id, src) => hooks?.onSource(id, src), onMessages: (id, ms) => hooks?.onMessages(id, ms) });
      if (worker !== server) { next.dispose(); return null; }   // its server stopped, and Lean was started again
      session = next;
      if (dark !== started) session.setDark(dark);   // the theme changed while Lean was starting
      setState("ready");
      if (docKey !== null) { session.setCells(lastCells); }
      mountSoon();
      return session;
    } catch (e) {
      progress = null;
      notStarted(e instanceof Error ? e.message : String(e));
      return null;
    }
  })();
  return starting;
}

/** Starts Lean's server: a worker (packages/engine-host/src/worker-lean-server.ts) that reports its loading,
 *  and its end when it ends by itself, on a channel of its own. */
function startServer(): Worker {
  const channel = `chalkmath-lean-${crypto.randomUUID()}`;
  const bc = progressChannel = new BroadcastChannel(channel);
  bc.onmessage = (e: MessageEvent<{ phase: string; loaded?: number; total?: number; code?: number }>) => {
    const p = e.data;
    if (p.phase === "exit") { exited(worker, p.code!); return; }
    if (p.phase === "done") settled();
    setProgress(p.phase === "download" ? { phase: "download", loaded: p.loaded!, total: p.total! }
      : p.phase === "checking" ? { phase: "checking" } : null);
  };
  setProgress({ phase: "starting" });   // a download is reported only for what this browser does not have
  serverImports = importsOf(lastCells);
  const packs = hooks?.packs?.(serverImports) ?? [];
  const worker = server = new Worker(`${versioned("lean/lean-server.worker.js")}&progress=${channel}${packs.length ? `&packs=${encodeURIComponent(packs.join(","))}` : ""}`);
  // Lean's own progress reports: which version of the document it is checking, and whether it is done
  worker.addEventListener("message", (e: MessageEvent<{ method?: string; params?: { textDocument?: { version?: number }; processing?: unknown[] } }>) => {
    if (e.data?.method !== "$/lean/fileProgress" || worker !== server) return;
    checkedVersion = e.data.params?.textDocument?.version ?? -1;
    const left = (e.data.params?.processing ?? []) as { range: { start: { line: number } } }[];
    busy = left.length > 0;
    checkingLine = busy ? Math.min(...left.map((p) => p.range.start.line)) + 1 : null;
    hooks?.onChecked?.();
    progressSoon();
  });
  worker.addEventListener("error", (e) => {
    e.preventDefault();   // said on the Lean cells, not as an error of the page's own
    if (state === "failed" || worker !== server) return;   // the dying worker reports more than once
    stopped(/Maximum call stack size exceeded|too much recursion/.test(e.message) ? OUT_OF_STACK : e.message || "its server stopped");
  });
  return worker;
}

/** The modules a document imports: the `import` lines its first cell starts with. */
function importsOf(cells: { src: string }[]): string[] {
  const out: string[] = [];
  for (const line of (cells[0]?.src ?? "").split("\n")) {
    const m = /^import\s+(\S+)\s*$/.exec(line);
    if (m) out.push(m[1]!);
    else if (line.trim() && !line.startsWith("--")) break;
  }
  return out;
}
/** What the running server imports (null: Lean has not started). Lean loads a file's imports once per process, as it
 *  first checks the file, and exits to be started again for others (`exited`). */
let serverImports: string[] | null = null;
export const leanServerImports = () => (session ? serverImports : null);

/** Lean's server has stopped: before it had its library loaded, Lean did not start; after, it stopped while checking. */
function stopped(why: string) {
  const ran = state === "ready" && (progress === null || progress.phase === "checking");
  setProgress(null);
  if (!ran) { notStarted(why); return; }
  stoppedAt = checkingLine === null ? null : session?.cellAt(checkingLine) ?? null;
  setState("failed", `Lean stopped: ${why}.`);
}

/** Lean's server ended its process. Natively Lean's watchdog then starts another: a file's imports are loaded
 *  once per process, so when they change, the file worker exits with 2 to be started again with the new ones
 *  (Lean.Server.FileWorker `setupImports`). Here the page does that, and on any other code Lean stopped. */
function exited(worker: Worker, code: number) {
  if (worker !== server || state === "failed") return;
  if (code === 2 && session) { void restartLean(); return; }
  stopped(`its server exited (code ${code})`);
}

/** Starts Lean when it was held (`STARTING`): the reader asked to try again. */
export function startLeanAnyway(h: LeanHooks): Promise<LeanNotebook | null> {
  held = false;
  mark(false);
  return ensureLean(h);
}

/** Whether Lean can be started again in the page: it stopped, or did not start, after its server did. */
export const leanRestartable = () => state === "failed" && server !== null;

/** Starts a new server for Lean in the page, in place of the one it has: after that one stopped (out of
 *  stack, say), or exited to be started again. The cells' editors and the infoview stay, and what was typed
 *  meanwhile is there; Lean's files come from the browser's store, but it loads its library and checks the
 *  notebook again from the start. Lean that did not start (no editor yet) starts again from the beginning. */
export async function restartLean(): Promise<void> {
  if (!hooks) return;
  const old = server, oldChannel = progressChannel;
  const end = () => { old?.terminate(); oldChannel?.close(); };
  stoppedAt = null; checkingLine = null; checkedVersion = -1; busy = true;
  server = null; progressChannel = null;   // what the old server says from now on is not heard
  if (!session) { end(); starting = null; setState("off"); void ensureLean(hooks); return; }
  marking = true; mark(true);
  setState("ready");
  setProgress({ phase: "starting" });
  hooks.onChecked?.();
  // the old server goes before the new one starts: each holds over a gigabyte
  try { await session.restart(() => { end(); return startServer(); }); }
  catch (e) { stopped(e instanceof Error ? e.message : String(e)); }
}

/** The version Lean last reported on, and whether it was still checking it. */
let checkedVersion = -1;
let busy = true;
/** Whether Lean has finished checking the document as it is now, so its messages are the final word on it. */
export const leanChecked = () => state === "ready" && !!session && !busy && checkedVersion === session.version();
/** Replaces one cell's source from outside its views (an exercise's statement, a prelude). */
export function setLeanSource(id: string, src: string) {
  const c = lastCells.find((x) => x.id === id);
  if (c) c.src = src;
  session?.setSource(id, src);
}

let lastCells: { id: string; src: string }[] = [];
/** Makes the document hold `doc`'s Lean cells, in order. Sources typed into a view are already there; a
 *  different notebook, or cells added, removed or reordered, replace the document (Lean re-checks it). */
export function syncLean(doc: unknown, cells: { id: string; src: string; fixed?: boolean }[]) {
  const ids = cells.map((c) => c.id);
  const same = doc === docKey && ids.length === syncedIds.length && ids.every((id, i) => id === syncedIds[i]);
  lastCells = cells;
  // a cell no view edits (an exercise's statement, a course's prelude) is pushed when the notebook changes it
  if (same) { for (const c of cells) if (c.fixed) session?.setSource(c.id, c.src); return; }
  docKey = doc; syncedIds = ids;
  session?.setCells(cells);
}

function mountNow(id: string, el: HTMLElement) {
  el.textContent = "";   // the source shown while Lean was starting
  el.classList.remove("pending");
  let v = views.get(id);
  if (!v) {
    const box = document.createElement("div");
    box.className = "leanbox";
    el.append(box);
    v = { view: session!.mount(id, box), box };
    views.set(id, v);
  } else {
    el.append(v.box);
  }
}

/** Shows cell `id`'s editor in `el`: at once when it has one, else its source until the editor is made. */
export function mountLean(id: string, el: HTMLElement, src: string) {
  if (session && views.has(id)) { pending.delete(id); mountNow(id, el); return; }
  el.textContent = src; el.classList.add("pending"); pending.set(id, { el, src });
  if (session) mountSoon();
}

/** Makes the editors of the cells waiting for one a few at a time, the one nearest the reader's view first,
 *  between which the page draws and answers: each takes tens of milliseconds, and a lesson has a dozen or two
 *  (all at once, the page froze for the best part of a second as Lean's editor started). */
let mounting = false;
function mountSoon() {
  if (mounting || !pending.size) return;
  mounting = true;
  setTimeout(function step() {
    const t0 = performance.now();
    while (session && pending.size && performance.now() - t0 < 12) {
      let next: string | null = null, far = Infinity;
      for (const [id, p] of pending) {
        if (!p.el.isConnected) { pending.delete(id); continue; }
        const r = p.el.getBoundingClientRect();
        const d = r.bottom < 0 ? -r.bottom : r.top > innerHeight ? r.top - innerHeight : 0;
        if (d < far) { far = d; next = id; }
      }
      if (next === null) break;
      const el = pending.get(next)!.el;
      pending.delete(next);
      mountNow(next, el);
    }
    if (session && pending.size) setTimeout(step, 0); else mounting = false;
  }, 0);
}

/** Follows the notebook's theme. */
export function setLeanDark(d: boolean) { dark = d; session?.setDark(d); }

export function focusLean(id: string) {
  const p = pending.get(id);
  if (p && session && p.el.isConnected) { pending.delete(id); mountNow(id, p.el); }   // wanted now
  views.get(id)?.view.focus();
}

/** Disposes the editors of cells that are gone (from the notebook, or with the notebook). */
export function unmountLean(keep: (id: string) => boolean) {
  for (const [id, v] of views) if (!keep(id)) { v.view.dispose(); v.box.remove(); views.delete(id); }
  for (const id of pending.keys()) if (!keep(id)) pending.delete(id);
}
