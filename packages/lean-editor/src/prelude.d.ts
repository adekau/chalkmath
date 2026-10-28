/** The Lean `src` without its show-only commands, for a course's prelude (see prelude.js). */
export function leanForPrelude(src: string): string;
export interface LessonCell { type?: string | undefined; src: string; lean?: boolean | undefined; leanSolution?: string | undefined; leanDefSolution?: string | undefined }
export function authorLean(cells: LessonCell[], start?: string): string[];
export function preludePart(title: string, cells: LessonCell[]): string | null;
export function preludeOf(parts: (string | null)[]): string;
export function scopeOf(src: string): string;
export function textHash(s: string): string;
export function moduleName(course: string, m: number): string;
export function moduleSource(course: string, parts: (string | null)[], m: number): string;
export interface ModuleEntry { name: string; length: number; hash: string; scope: string }
export function moduleEntry(course: string, parts: (string | null)[], m: number): ModuleEntry;
export function importedPrelude(entry: ModuleEntry, prelude: string): string | null;
