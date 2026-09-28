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

export type { LeanMessage };
declare const __BUILD_ID__: string;
declare const __LEAN_BUILT__: boolean;
const stamp = typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev";
const PREF = "chalkmath.lean";

export type LeanState = "off" | "isolating" | "starting" | "ready" | "failed";
let state: LeanState = "off";
let failure = "";
let session: LeanNotebook | null = null;
let starting: Promise<LeanNotebook | null> | null = null;
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
export const leanFailure = () => failure;

/** Where Lean is in loading, while it loads (null once it has checked the notebook, or before it starts):
 *  the editor, then Lean's download (reported by its worker, packages/engine-host/src/worker-lean-server.ts),
 *  then Lean loading its library and checking the notebook for the first time. */
export type LeanProgress = { phase: "editor" } | { phase: "download"; loaded: number; total: number } | { phase: "checking" };
let progress: LeanProgress | null = null;
export const leanProgress = () => progress;
const setProgress = (p: LeanProgress | null) => { progress = p; hooks?.onProgress(); };

export interface LeanHooks {
  dark: boolean;
  onSource(id: string, src: string): void;
  onMessages(id: string, messages: LeanMessage[]): void;
  onState(): void;
  onProgress(): void;
}
let hooks: LeanHooks | null = null;

const setState = (s: LeanState, why = "") => { state = s; failure = why; hooks?.onState(); };

/** Browsers that honor `Cross-Origin-Embedder-Policy: credentialless`, which leaves images from other
 *  sites loading (require-corp, Safari's only option, blocks those that do not opt in). */
const credentialless = () => "chrome" in window || /Firefox\//.test(navigator.userAgent);

/** Registers the header-adding service worker and reloads, unless that already happened in this tab
 *  (a browser without service workers, or one that refuses them, would reload forever). */
async function isolate(): Promise<void> {
  try { localStorage.setItem(PREF, "on"); } catch { /* private mode */ }
  if (!("serviceWorker" in navigator)) { setState("failed", "this browser has no service workers, which Lean cells need to isolate the page"); return; }
  if (sessionStorage.getItem("chalkmath.isolating")) {
    setState("failed", "the page could not be cross-origin isolated (its service worker was not allowed to add the headers)");
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
  if (typeof __LEAN_BUILT__ === "boolean" && !__LEAN_BUILT__) {
    setState("failed", "this copy of ChalkMath was built without Lean itself (npm run lean-wasm, then npm run bundle)");
    return Promise.resolve(null);
  }
  if (!self.crossOriginIsolated) { void isolate(); return Promise.resolve(null); }
  setState("starting");
  setProgress({ phase: "editor" });
  starting = (async () => {
    try {
      const url = new URL(`lean/lean-editor.js?v=${stamp}`, location.href).href;
      const mod = (await import(url)) as { startLean(o: LeanOptions): Promise<LeanNotebook> };
      const channel = `chalkmath-lean-${crypto.randomUUID()}`;
      const bc = new BroadcastChannel(channel);
      bc.onmessage = (e: MessageEvent<{ phase: string; loaded?: number; total?: number }>) => {
        const p = e.data;
        if (p.phase === "done") bc.close();
        setProgress(p.phase === "download" ? { phase: "download", loaded: p.loaded!, total: p.total! }
          : p.phase === "checking" ? { phase: "checking" } : null);
      };
      setProgress({ phase: "download", loaded: 0, total: 0 });
      const worker = new Worker(`lean/lean-server.worker.js?v=${stamp}&progress=${channel}`);
      worker.addEventListener("error", (e) => { setProgress(null); setState("failed", e.message || "Lean's server stopped"); });
      session = await mod.startLean({ worker, infoview: infoview(), dark: h.dark,
        onSource: (id, src) => hooks?.onSource(id, src), onMessages: (id, ms) => hooks?.onMessages(id, ms) });
      setState("ready");
      if (docKey !== null) { session.setCells(lastCells); }
      for (const [id, p] of pending) if (p.el.isConnected) mountNow(id, p.el);
      pending.clear();
      return session;
    } catch (e) {
      progress = null;
      setState("failed", e instanceof Error ? e.message : String(e));
      return null;
    }
  })();
  return starting;
}

let lastCells: { id: string; src: string }[] = [];
/** Makes the document hold `doc`'s Lean cells, in order. Sources typed into a view are already there; a
 *  different notebook, or cells added, removed or reordered, replace the document (Lean re-checks it). */
export function syncLean(doc: unknown, cells: { id: string; src: string }[]) {
  const ids = cells.map((c) => c.id);
  const same = doc === docKey && ids.length === syncedIds.length && ids.every((id, i) => id === syncedIds[i]);
  lastCells = cells;
  if (same) return;
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

/** Shows cell `id`'s editor in `el` (now, or when Lean has started). */
export function mountLean(id: string, el: HTMLElement, src: string) {
  if (session) mountNow(id, el);
  else { el.textContent = src; el.classList.add("pending"); pending.set(id, { el, src }); }
}

export function focusLean(id: string) { views.get(id)?.view.focus(); }

/** Disposes the editors of cells that are gone (from the notebook, or with the notebook). */
export function unmountLean(keep: (id: string) => boolean) {
  for (const [id, v] of views) if (!keep(id)) { v.view.dispose(); v.box.remove(); views.delete(id); }
  for (const id of pending.keys()) if (!keep(id)) pending.delete(id);
}
