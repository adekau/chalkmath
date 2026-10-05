/**
 * Where the open notebooks are kept between visits (ARCHITECTURE.md §4a).
 *
 * Each browser tab keeps its own autosave, under a key with the tab's id, so two tabs never overwrite
 * each other's notebooks. The id lasts as long as the tab, reloads included (sessionStorage), so a
 * reload finds its own notebooks. A tab holds a Web Lock named after its id while it is open; an
 * autosave whose lock nobody holds belongs to a tab that is gone, and the next tab to start adopts
 * it: its notebooks open there, and its key is folded into the new tab's. So closing the browser and
 * opening it again brings every notebook back, and opening a second tab beside a live one does not
 * copy (and later fork) the first tab's notebooks.
 *
 * An autosave that cannot be read is set aside under a `.bad.` key rather than overwritten by the next
 * save, which would lose the only copy of the notebooks in it.
 */

export const KEY = "chalkmath.autosave";
/** The single key every tab shared before autosaves were per tab, and the one before the rename. */
export const LEGACY_KEYS = [KEY, "lemma.autosave"];
const BAD = `${KEY}.bad.`;
export const keyOf = (tabId: string) => `${KEY}.${tabId}`;

/** What the browser keeps for a tab: every open notebook, which one is current, and whether each had
 *  unsaved changes. */
export interface Autosave<F = unknown> { chalkmath: 1; active: number; docs: { file: F; dirty: boolean; inLibrary?: boolean }[] }

/** The part of `Storage` used here (and faked by the tests). */
export interface KV {
  getItem(key: string): string | null;
  setItem(key: string, value: string): void;
  removeItem(key: string): void;
  readonly length: number;
  key(i: number): string | null;
}

/** The autosaves no open tab owns: other tabs' keys whose tab is gone (`live` lists the ids of the
 *  open ones), and the legacy single key. Never this tab's own, nor one set aside as unreadable. */
export function orphans(store: KV, ownId: string, live: ReadonlySet<string>): string[] {
  const out: string[] = [];
  for (let i = 0; i < store.length; i++) {
    const k = store.key(i);
    if (!k || k.startsWith(BAD)) continue;
    if (LEGACY_KEYS.includes(k)) out.push(k);
    else if (k.startsWith(`${KEY}.`)) {
      const id = k.slice(KEY.length + 1);
      if (id !== ownId && !live.has(id)) out.push(k);
    }
  }
  return out;
}

/** One autosave's notebooks, in either format: a tab's `Autosave`, or a bare notebook file (the
 *  format before there were tabs). `null` when it is not one. */
export function parseAutosave(text: string): Autosave | null {
  let v: unknown;
  try { v = JSON.parse(text); } catch { return null; }
  if (!v || typeof v !== "object") return null;
  const o = v as Record<string, unknown>;
  if ("chalkmath" in o) {
    if (!Array.isArray(o.docs) || !o.docs.every((d) => d && typeof d === "object" && "file" in d && d.file && typeof d.file === "object")) return null;
    return { chalkmath: 1, active: typeof o.active === "number" ? o.active : 0, docs: o.docs as Autosave["docs"] };
  }
  return Array.isArray(o.cells) ? { chalkmath: 1, active: 0, docs: [{ file: o, dirty: false }] } : null;
}

/** Gather what this tab should open: its own autosave first, then the orphans' notebooks, merged and
 *  written back under its own key. A key is removed only once what it held is safe elsewhere (merged
 *  into this tab's key, or set aside), so a full storage loses nothing: the orphans stay, and are
 *  adopted next time. Run it where no other tab can run it at the same time (the `chalkmath.autosave`
 *  lock), or two new tabs could adopt the same orphan. */
export function gather(store: KV, ownId: string, live: ReadonlySet<string>, now = Date.now()): { merged: Autosave | null; setAside: string[] } {
  const own = keyOf(ownId);
  const found = [own, ...orphans(store, ownId, live)].flatMap((k) => {
    const text = store.getItem(k);
    return text === null ? [] : [{ k, text, a: parseAutosave(text) }];
  });
  let merged: Autosave | null = null;
  for (const f of found) if (f.a) { if (!merged) merged = f.a; else merged.docs.push(...f.a.docs); }
  const setAside: string[] = [];
  const safe = new Set<string>();
  found.forEach((f, i) => {
    if (f.a) return;
    const k = `${BAD}${now}.${i}`;
    try { store.setItem(k, f.text); setAside.push(k); safe.add(f.k); } catch { /* no room to set it aside: it stays where it is */ }
  });
  try {
    if (merged) {
      store.setItem(own, JSON.stringify(merged));
      for (const f of found) if (f.a) safe.add(f.k);
    }
    for (const k of safe) if (k !== own || !merged) store.removeItem(k);
  } catch { /* storage full: what was not merged stays where it is */ }
  return { merged, setAside };
}
