/** The types a host needs, without the editor itself (so a page can declare them before it loads it). */
export interface LeanMessage {
  severity: "error" | "warning" | "info" | "hint";
  /** 1-based, relative to the cell's first line. */
  line: number;
  column: number;
  endLine: number;
  endColumn: number;
  message: string;
}

export interface CellView {
  focus(): void;
  dispose(): void;
}

export interface LeanNotebook {
  /** Replaces every Lean cell, in document order. */
  setCells(cells: { id: string; src: string }[]): void;
  /** Inserts a cell at `index` among the Lean cells. */
  insertCell(index: number, id: string, src: string): void;
  removeCell(id: string): void;
  source(id: string): string;
  /** Replaces a cell's source from outside its views (an exercise's fixed statement, a prelude). */
  setSource(id: string, src: string): void;
  /** The document's version: Lean's `$/lean/fileProgress` names the version it is checking, so a host
   *  can tell when what it shows has been checked. */
  version(): number;
  messages(id: string): LeanMessage[];
  /** The cell holding a 1-based line of the document, and the line in it (1-based). */
  cellAt(line: number): { id: string; line: number } | null;
  /** Shows cell `id` in `el`, which grows with its content. */
  mount(id: string, el: HTMLElement): CellView;
  /** Switches the editors and the infoview to the dark or light theme. */
  setDark(dark: boolean): void;
  dispose(): void;
}

export interface LeanOptions {
  /** The worker hosting Lean's server (worker-lean-server.ts). */
  worker: Worker;
  /** Where the infoview (goals, messages at the cursor) goes. */
  infoview: HTMLElement;
  dark?: boolean;
  /** A cell's source changed by typing in its view. */
  onSource?(id: string, src: string): void;
  /** A cell's messages changed. */
  onMessages?(id: string, messages: LeanMessage[]): void;
}
