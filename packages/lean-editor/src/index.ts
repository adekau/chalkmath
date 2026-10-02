/**
 * @chalkmath/lean-editor — Lean cells: the VS Code editor with the Lean 4 extension (lean4monaco) and its
 * infoview, on Lean's language server compiled to wasm (packages/engine-host/src/worker-lean-server.ts).
 *
 * One Lean document per notebook. Every Lean cell is a stretch of that document, between separator lines
 * (`--⁅cell⁆`, a Lean comment), and each cell's editor is a view of the one model that hides every line
 * outside its stretch. So the server sees one file — definitions carry from cell to cell, editing a cell
 * re-elaborates it and the cells after it — and every position the extension and the infoview use is a
 * real position in that file: nothing is translated.
 *
 * The notebook owns layout and output: it mounts a view per cell and shows the messages this module
 * reports for the cell's lines (errors, warnings, `#eval` results).
 */
import { LeanMonaco, LeanMonacoEditor } from "lean4monaco";
import * as monaco from "monaco-editor";

export const SEPARATOR = "--⁅cell⁆";

export type { LeanMessage, CellView, LeanNotebook, LeanOptions } from "./types.js";
import type { LeanMessage, LeanNotebook, LeanOptions } from "./types.js";

/** LeanMonaco, speaking LSP to a web worker instead of a WebSocket (monaco-languageclient's `WorkerDirect`). */
class WorkerLeanMonaco extends LeanMonaco {
  constructor(private readonly worker: Worker) { super(); }
  protected override getWebSocketOptions(): never {
    return { $type: "WorkerDirect", worker: this.worker } as never;
  }
}

const SEVERITY: Record<number, LeanMessage["severity"]> = {
  [monaco.MarkerSeverity.Error]: "error", [monaco.MarkerSeverity.Warning]: "warning",
  [monaco.MarkerSeverity.Info]: "info", [monaco.MarkerSeverity.Hint]: "hint",
};

const colorTheme = (dark: boolean | undefined) => dark ? "Default Dark Modern" : "Default Light Modern";

export async function startLean(o: LeanOptions): Promise<LeanNotebook> {
  const lm = new WorkerLeanMonaco(o.worker);
  lm.setInfoviewElement(o.infoview);
  await lm.start({
    websocket: { url: "" },
    vscode: {
      "workbench.colorTheme": colorTheme(o.dark),
      "editor.wordWrap": "on",
      "editor.minimap.enabled": false,
      "lean4.input.eagerReplacementEnabled": true,
    },
  });
  // The document's own editor lives off screen: the extension opens the file through it, and each cell's
  // view shares its model.
  const holder = document.createElement("div");
  holder.style.cssText = "position:absolute;left:-10000px;top:0;width:600px;height:200px";
  document.body.append(holder);
  const doc = new LeanMonacoEditor();
  await doc.start(holder, "/notebook/Notebook.lean", "");
  const model = doc.editor.getModel()!;

  let ids: string[] = [];
  /** 1-based [first, last] line of each cell, from the separators. */
  let ranges = new Map<string, [number, number]>();
  let lastSources = new Map<string, string>();
  const views = new Map<string, Set<{ editor: monaco.editor.IStandaloneCodeEditor; id: string }>>();
  let lastMessages = new Map<string, string>();
  let applying = false;

  const recompute = () => {
    const n = model.getLineCount();
    const seps: number[] = [];
    for (let l = 1; l <= n; l++) if (model.getLineContent(l) === SEPARATOR) seps.push(l);
    ranges = new Map();
    let start = 1;
    ids.forEach((id, i) => {
      const end = i < seps.length ? seps[i]! - 1 : n;
      ranges.set(id, [start, Math.max(start, end)]);
      start = end + 2;
    });
  };
  const source = (id: string) => {
    const r = ranges.get(id);
    if (!r) return "";
    return model.getValueInRange(new monaco.Range(r[0], 1, r[1], model.getLineMaxColumn(r[1])));
  };
  const hide = (editor: monaco.editor.IStandaloneCodeEditor, id: string) => {
    const r = ranges.get(id), n = model.getLineCount();
    if (!r) return;
    const hidden: monaco.IRange[] = [];
    if (r[0] > 1) hidden.push(new monaco.Range(1, 1, r[0] - 1, 1));
    if (r[1] < n) hidden.push(new monaco.Range(r[1] + 1, 1, n, 1));
    (editor as unknown as { setHiddenAreas(r: monaco.IRange[], source?: unknown): void }).setHiddenAreas(hidden, HIDDEN);
    editor.updateOptions({ lineNumbers: (l: number) => String(l - r[0] + 1) });
  };
  const HIDDEN = {};
  const refreshViews = () => { for (const [id, set] of views) for (const v of set) hide(v.editor, id); };
  const reportMessages = () => {
    const markers = monaco.editor.getModelMarkers({ resource: model.uri });
    for (const id of ids) {
      const r = ranges.get(id)!;
      const ms: LeanMessage[] = markers
        .filter((m) => m.startLineNumber >= r[0] && m.startLineNumber <= r[1])
        .map((m) => ({ severity: SEVERITY[m.severity] ?? "info", line: m.startLineNumber - r[0] + 1, column: m.startColumn,
                       endLine: m.endLineNumber - r[0] + 1, endColumn: m.endColumn, message: m.message }));
      const key = JSON.stringify(ms);
      if (lastMessages.get(id) !== key) { lastMessages.set(id, key); o.onMessages?.(id, ms); }
    }
  };
  model.onDidChangeContent(() => {
    recompute();
    refreshViews();
    if (applying) return;
    for (const id of ids) {
      const s = source(id);
      if (lastSources.get(id) !== s) { lastSources.set(id, s); o.onSource?.(id, s); }
    }
  });
  const markerSub = monaco.editor.onDidChangeMarkers((uris) => {
    if (uris.some((u) => u.toString() === model.uri.toString())) reportMessages();
  });

  /** Replaces a span of whole lines, keeping the edit on the undo stack of the shared model. */
  const edit = (range: monaco.IRange, text: string) => {
    applying = true;
    try { model.pushEditOperations([], [{ range, text, forceMoveMarkers: true }], () => null); }
    finally { applying = false; }
    for (const id of ids) lastSources.set(id, source(id));
  };

  return {
    setCells(cells) {
      ids = cells.map((c) => c.id);
      applying = true;
      try { model.setValue(cells.map((c) => c.src).join(`\n${SEPARATOR}\n`)); }
      finally { applying = false; }
      recompute();
      refreshViews();
      lastSources = new Map(ids.map((id) => [id, source(id)]));
    },
    insertCell(index, id, src) {
      const n = model.getLineCount();
      if (ids.length === 0) {
        ids = [id];
        edit(model.getFullModelRange(), src);
      } else if (index >= ids.length) {
        const endCol = model.getLineMaxColumn(n);
        ids = [...ids, id];
        edit(new monaco.Range(n, endCol, n, endCol), `\n${SEPARATOR}\n${src}`);
      } else {
        const first = ranges.get(ids[index]!)![0];
        ids = [...ids.slice(0, index), id, ...ids.slice(index)];
        edit(new monaco.Range(first, 1, first, 1), `${src}\n${SEPARATOR}\n`);
      }
      recompute();
      refreshViews();
    },
    removeCell(id) {
      const i = ids.indexOf(id);
      if (i < 0) return;
      const [a, b] = ranges.get(id)!;
      const n = model.getLineCount();
      // take the cell with one adjacent separator
      const range = i < ids.length - 1 ? new monaco.Range(a, 1, b + 2, 1)
        : i > 0 ? new monaco.Range(a - 2, model.getLineMaxColumn(a - 2), n, model.getLineMaxColumn(n))
        : model.getFullModelRange();
      ids = ids.filter((x) => x !== id);
      for (const v of views.get(id) ?? []) v.editor.dispose();
      views.delete(id);
      edit(range, "");
      recompute();
      refreshViews();
      lastMessages.delete(id);
    },
    source,
    setSource(id, src) {
      const r = ranges.get(id);
      if (!r || source(id) === src) return;
      edit(new monaco.Range(r[0], 1, r[1], model.getLineMaxColumn(r[1])), src);
      recompute();
      refreshViews();
    },
    version() { return model.getVersionId(); },
    messages(id) { return JSON.parse(lastMessages.get(id) ?? "[]") as LeanMessage[]; },
    mount(id, el) {
      const editor = monaco.editor.create(el, {
        model, automaticLayout: true, scrollBeyondLastLine: false, minimap: { enabled: false },
        folding: false, glyphMargin: false, overviewRulerLanes: 0, lineDecorationsWidth: 6,
        scrollbar: { vertical: "hidden", alwaysConsumeMouseWheel: false }, wordWrap: "on",
        renderLineHighlightOnlyWhenFocus: true, fixedOverflowWidgets: true,
      });
      const view = { editor, id };
      if (!views.has(id)) views.set(id, new Set());
      views.get(id)!.add(view);
      hide(editor, id);
      const grow = () => { el.style.height = `${Math.max(editor.getContentHeight(), 24)}px`; editor.layout(); };
      editor.onDidContentSizeChange(grow);
      grow();
      // keep the cursor inside the cell (select-all and ctrl+end would otherwise reach hidden lines)
      editor.onDidChangeCursorSelection((e) => {
        const r = ranges.get(id);
        if (!r) return;
        const s = e.selection;
        const clamp = (l: number) => Math.min(Math.max(l, r[0]), r[1]);
        if (s.startLineNumber < r[0] || s.endLineNumber > r[1]) {
          const a = clamp(s.startLineNumber), b = clamp(s.endLineNumber);
          editor.setSelection(new monaco.Selection(a, a === s.startLineNumber ? s.startColumn : 1, b,
            b === s.endLineNumber ? s.endColumn : model.getLineMaxColumn(b)));
        }
      });
      // and keep its edges: Backspace at its first column or Delete at its last would join the cell to
      // the hidden separator line
      editor.onKeyDown((e) => {
        const r = ranges.get(id), p = editor.getPosition(), sel = editor.getSelection();
        if (!r || !p || !sel?.isEmpty()) return;
        const atStart = p.lineNumber === r[0] && p.column === 1;
        const atEnd = p.lineNumber === r[1] && p.column === model.getLineMaxColumn(r[1]);
        if ((e.keyCode === monaco.KeyCode.Backspace && atStart) || (e.keyCode === monaco.KeyCode.Delete && atEnd)) {
          e.preventDefault();
          e.stopPropagation();
        }
      });
      return {
        focus() {
          const r = ranges.get(id);
          if (r) editor.setPosition({ lineNumber: r[0], column: 1 });
          editor.focus();
        },
        dispose() { editor.dispose(); views.get(id)?.delete(view); },
      };
    },
    setDark(dark) { lm.updateVSCodeOptions({ "workbench.colorTheme": colorTheme(dark) }); },
    dispose() {
      markerSub.dispose();
      for (const set of views.values()) for (const v of set) v.editor.dispose();
      doc.dispose();
      lm.dispose();
      holder.remove();
    },
  };
}
