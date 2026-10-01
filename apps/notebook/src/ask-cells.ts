/**
 * `?` lookups: the notebook's side of @chalkmath/ask (packages/ask).
 *
 * A math cell that starts with `?` (or `let name = ?…`) is a question. A language model running on
 * this machine answers it — from its own knowledge when the answer is standard (a formula, a
 * constant), else by searching and reading pages — as source text the engine then evaluates like any
 * other cell. The lookup is saved with the cell, so running the notebook again does not ask again.
 *
 * The model is Chrome's built-in one (Gemini Nano, the Prompt API) where the browser has it, which
 * downloads nothing from this page; elsewhere a WebGPU model through WebLLM, loaded only when a
 * lookup needs it (dist/ask/webllm.js) and downloaded once from Hugging Face; or, when the reader
 * chooses it, a model served by Ollama on this computer (`http://localhost:11434`), which can be
 * larger than a browser can hold.
 *
 * Searches go to Wikipedia (no key, and it answers other origins) and, when the reader sets one, a
 * SearXNG-style endpoint that queries the web's search engines. They are the one place the notebook
 * sends what the reader typed: the question's search terms, never the notebook. The first search
 * asks first.
 */
import { lookup, wikipedia, webSearch, validAnswer, AskError, type AskResult, type Model, type Source } from "@chalkmath/ask";

export type { AskResult };
export { AskError };
declare const __BUILD_ID__: string;
const stamp = typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev";

/** A question cell: `?question`, or `let name = ?question`. */
export const ASK_CELL = /^\s*(?:let\s+([A-Za-z_][A-Za-z0-9_]*)\s*=\s*)?\?\s*([\s\S]*\S)\s*$/;

export interface AskSettings {
  /** Which model: Chrome's built-in one when there is one, else WebGPU ("auto"); or one of them, or Ollama's. */
  backend: "auto" | "chrome" | "webllm" | "ollama";
  /** The WebGPU model (a WebLLM model id). */
  model: string;
  /** Ollama's address on this computer, and the model it serves (`ollama pull <name>`). */
  ollamaUrl: string;
  ollamaModel: string;
  /** Let the model answer standard knowledge itself, and fall back on its memory when searches fail. */
  knowledge: boolean;
  wikipedia: boolean;
  /** A SearXNG-style search endpoint (`https://searx.example` or a URL with `{q}`), or "". */
  searchUrl: string;
  /** A page reader for sites that refuse cross-origin reads (a URL with `{url}`, or a prefix), or "". */
  reader: string;
  /** The reader has agreed to searches leaving the machine. */
  searchOk: boolean;
}

/** WebLLM's models worth a lookup, smallest first, with the GPU memory WebLLM says each needs. */
export const WEBGPU_MODELS: [id: string, label: string][] = [
  ["Qwen3-1.7B-q4f16_1-MLC", "Qwen3 1.7B (needs about 2 GB of GPU memory)"],
  ["Llama-3.2-3B-Instruct-q4f16_1-MLC", "Llama 3.2 3B (about 2.3 GB)"],
  ["Qwen3-4B-q4f16_1-MLC", "Qwen3 4B (about 3.4 GB)"],
  ["Phi-4-mini-instruct-q4f16_1-MLC", "Phi-4 mini (about 3.4 GB)"],
  ["Qwen3.5-4B-q4f16_1-MLC", "Qwen3.5 4B (about 3.9 GB)"],
  ["Llama-3.1-8B-Instruct-q4f16_1-MLC", "Llama 3.1 8B (about 5 GB; much better at reading)"],
  ["Qwen3-8B-q4f16_1-MLC", "Qwen3 8B (about 5.7 GB; much better at reading)"],
  ["Qwen3.5-9B-q4f16_1-MLC", "Qwen3.5 9B (about 6.4 GB; the strongest here)"],
];

const KEY = "chalkmath.ask";
const DEFAULTS: AskSettings = {
  backend: "auto", model: WEBGPU_MODELS[0]![0], ollamaUrl: "http://localhost:11434", ollamaModel: "gemma4:e2b",
  knowledge: true, wikipedia: true, searchUrl: "", reader: "", searchOk: false,
};

export function askSettings(): AskSettings {
  try {
    const s = JSON.parse(localStorage.getItem(KEY) ?? "{}") as Partial<AskSettings>;
    return { ...DEFAULTS, ...s };
  } catch { return { ...DEFAULTS }; }
}
export function setAskSettings(s: Partial<AskSettings>) {
  const prev = askSettings();
  const next = { ...prev, ...s };
  try { localStorage.setItem(KEY, JSON.stringify(next)); } catch { /* private mode */ }
  // another model: the one loaded is let go (a WebGPU model holds gigabytes of GPU memory)
  if (next.backend !== prev.backend || next.model !== prev.model || next.ollamaUrl !== prev.ollamaUrl || next.ollamaModel !== prev.ollamaModel) {
    const old = model; model = null;
    void old?.then((m) => m.unload?.()).catch(() => {});
  }
}

// --- the models ---------------------------------------------------------------------------------

/** Chrome's Prompt API, as much of it as is used here. */
interface LMSession { prompt(input: string, o?: { responseConstraint?: object; signal?: AbortSignal }): Promise<string>; destroy(): void }
interface LMStatic {
  availability(o?: object): Promise<"unavailable" | "downloadable" | "downloading" | "available">;
  create(o?: object): Promise<LMSession>;
}
const chromeLM = (): LMStatic | null => (globalThis as { LanguageModel?: LMStatic }).LanguageModel ?? null;
const LM_OPTS = { expectedInputs: [{ type: "text", languages: ["en"] }], expectedOutputs: [{ type: "text", languages: ["en"] }] };

/** Where a model's download and loading report, as a detail of the lookup's current step. */
let sink: (detail: string) => void = () => {};
let model: Promise<Model> | null = null;

async function chromeAvailable(): Promise<boolean> {
  const lm = chromeLM();
  if (!lm) return false;
  try { return (await lm.availability(LM_OPTS)) !== "unavailable"; } catch { return false; }
}
async function webgpuAvailable(): Promise<boolean> {
  const gpu = (navigator as { gpu?: { requestAdapter(): Promise<unknown> } }).gpu;
  if (!gpu) return false;
  try { return !!(await gpu.requestAdapter()); } catch { return false; }
}

/** What the settings' backend would use on this browser, and why not when it cannot. */
export async function backendStatus(): Promise<{ chrome: boolean; webgpu: boolean }> {
  const [chrome, webgpu] = await Promise.all([chromeAvailable(), webgpuAvailable()]);
  return { chrome, webgpu };
}

function chromeModel(lm: LMStatic): Model {
  return {
    id: "Gemini Nano (Chrome)",
    async complete({ system, user, schema, signal }) {
      // no download monitor here: the model is on the machine by now (loadModel), and Chrome reports a
      // "download" of 100% for every session it creates, which would hide what the lookup is doing
      const s = await lm.create({ ...LM_OPTS, initialPrompts: [{ role: "system", content: system }], ...(signal ? { signal } : {}) });
      try { return await s.prompt(user, { responseConstraint: schema, ...(signal ? { signal } : {}) }); } finally { s.destroy(); }
    },
  };
}

async function webgpuModel(id: string): Promise<Model> {
  const mod = (await import(new URL(`ask/webllm.js?v=${stamp}`, location.href).href)) as typeof import("./webllm.js");
  let last = -1;
  return mod.createEngine(new URL(`ask/webllm-worker.js?v=${stamp}`, location.href).href, id, (fraction, text) => {
    const pct = Math.floor(fraction * 100);
    if (pct === last) return;
    last = pct;
    // WebLLM reports fetching and then loading onto the GPU; "Finish" is the end of both
    sink(/fetch|download/i.test(text) ? `downloading the model, once: ${pct}%` : pct < 100 ? `loading the model onto the GPU: ${pct}%` : "");
  });
}

/** Ollama's native chat endpoint, held to the schema by its `format`. Thinking is turned off: the
 *  schema is the answer, and on a CPU every word of thought costs seconds. */
function ollamaModel(base: string, name: string): Model {
  const url = `${base.replace(/\/+$/, "")}/api/chat`;
  let think = true;   // whether to send `think: false` (a model that cannot think may refuse the field)
  const call = async (body: object, signal?: AbortSignal) => {
    let r: Response;
    try { r = await fetch(url, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify(body), ...(signal ? { signal } : {}) }); }
    catch (e) {
      if (signal?.aborted) throw e;
      throw new AskError(`Ollama did not answer at ${base}. Is it running, and does OLLAMA_ORIGINS allow ${location.origin}? (Start it with OLLAMA_ORIGINS=${location.origin} ollama serve.)`);
    }
    const d = await r.json().catch(() => ({})) as { message?: { content?: string }; error?: string };
    if (!r.ok) throw Object.assign(new AskError(`Ollama: ${d.error ?? `answered ${r.status}`}${r.status === 404 ? ` (run: ollama pull ${name})` : ""}`), { status: r.status });
    return d.message?.content ?? "";
  };
  return {
    id: `${name} (Ollama)`,
    async complete({ system, user, schema, signal }) {
      const body = { model: name, stream: false, format: schema, options: { temperature: 0, num_ctx: 8192 },
        messages: [{ role: "system", content: system }, { role: "user", content: user }] };
      if (think) {
        try { return await call({ ...body, think: false }, signal); }
        catch (e) { if (!(e instanceof AskError && /think/i.test(e.message))) throw e; think = false; }
      }
      return call(body, signal);
    },
  };
}

async function loadModel(): Promise<Model> {
  const s = askSettings();
  if (s.backend === "ollama") return ollamaModel(s.ollamaUrl || DEFAULTS.ollamaUrl, s.ollamaModel || DEFAULTS.ollamaModel);
  const lm = chromeLM();
  if (s.backend !== "webllm" && lm && await chromeAvailable()) {
    // Chrome downloads its model the first time a page creates a session, which it allows only
    // shortly after a click or key press; if it refuses, a WebGPU model is the fallback
    if ((await lm.availability(LM_OPTS)) === "available") return chromeModel(lm);
    try {
      (await lm.create({ ...LM_OPTS, monitor(m: EventTarget) {
        m.addEventListener("downloadprogress", (e) => {
          const done = (e as ProgressEvent).loaded ?? 0;
          sink(done < 1 ? `downloading Chrome's model, once: ${Math.round(done * 100)}%` : "preparing Chrome's model");
        });
      } })).destroy();
      return chromeModel(lm);
    } catch (e) {
      if (s.backend === "chrome" || !(await webgpuAvailable())) {
        throw new AskError(`Chrome's built-in model could not be downloaded (${e instanceof Error ? e.message : String(e)}). Run the cell again with Enter or its Run button: Chrome starts the download only right after a key press or click.`);
      }
    }
  }
  if (s.backend === "chrome") throw new AskError("This browser has no built-in model (Chrome's Prompt API). Choose the WebGPU model in the lookup settings.");
  if (!(await webgpuAvailable())) {
    throw new AskError("Lookups need a model on this computer: Chrome's built-in model, or WebGPU for a downloaded one. This browser has neither.");
  }
  return webgpuModel(s.model);
}

// --- a lookup -----------------------------------------------------------------------------------

export interface LookupHooks {
  /** A step of the lookup begins ("Searching Wikipedia for …"). */
  onProgress(line: string): void;
  /** How the current step is getting on, when there is something to say: a model's download. */
  onDetail(detail: string): void;
  /** Ask the reader whether searches may leave the machine (the first time only); a stop closes the question. */
  confirmSearch(signal: AbortSignal): Promise<boolean>;
  signal: AbortSignal;
  forceSearch?: boolean;
}

const today = () => {
  const d = new Date();
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, "0")}-${String(d.getDate()).padStart(2, "0")}`;
};

export async function runLookup(question: string, h: LookupHooks): Promise<AskResult> {
  sink = h.onDetail;
  try {
    const s = askSettings();
    if (!model) { h.onProgress("Loading the model"); model = loadModel(); }
    // a stop while the model loads (a download can take minutes) ends the lookup; the load goes on,
    // and the next lookup uses it
    let m: Model;
    const stopped = new Promise<never>((_, reject) => {
      if (h.signal.aborted) reject(new AskError("Stopped."));
      h.signal.addEventListener("abort", () => reject(new AskError("Stopped.")), { once: true });
    });
    const loading = model;
    try { m = await Promise.race([loading, stopped]); } catch (e) {
      if (!(e instanceof AskError && e.message === "Stopped.") && model === loading) model = null;
      throw e;
    }
    const f = globalThis.fetch.bind(globalThis);
    const sources: Source[] = [];
    if (s.wikipedia) sources.push(wikipedia(f));
    if (s.searchUrl.trim()) sources.push(webSearch(f, s.searchUrl.trim()));
    return await lookup(question, {
      model: m, sources, fetch: f, reader: s.reader.trim() || undefined, useKnowledge: s.knowledge,
      forceSearch: !!h.forceSearch, today: today(), onProgress: h.onProgress, signal: h.signal,
      beforeSearch: async () => {
        if (askSettings().searchOk) return true;
        const ok = await h.confirmSearch(h.signal);
        if (ok) setAskSettings({ searchOk: true });
        return ok;
      },
    });
  } finally { sink = () => {}; }
}

/** The models Ollama has (for the settings' list), or null when it does not answer. */
export async function ollamaModels(base: string): Promise<string[] | null> {
  try {
    const r = await fetch(`${base.replace(/\/+$/, "")}/api/tags`);
    const d = await r.json() as { models?: { name?: string }[] };
    return (d.models ?? []).map((m) => m.name ?? "").filter(Boolean);
  } catch { return null; }
}

/** Run the chosen model once on a small question held to a schema, timed: whether it works here, and
 *  how long a lookup's steps will take. A WebGPU model is downloaded first if it has not been. */
export async function testModel(onDetail: (d: string) => void): Promise<{ ms: number; reply: string; model: string }> {
  sink = onDetail;
  try {
    model ??= loadModel();
    let m: Model;
    try { m = await model; } catch (e) { model = null; throw e; }
    onDetail("asking it a question");
    const t0 = performance.now();
    const reply = await m.complete({
      system: "Answer with JSON only.",
      user: "A prism's base has area 6 and its height is 4. What is its volume, and is that a fact you could look up? Reply as {\"volume\": number, \"lookup\": boolean}.",
      schema: { type: "object", properties: { volume: { type: "number" }, lookup: { type: "boolean" } }, required: ["volume", "lookup"] },
    });
    return { ms: performance.now() - t0, reply, model: m.id };
  } finally { sink = () => {}; }
}

/** A lookup saved in a notebook file, if it has every field a lookup produces and an answer a lookup
 *  could give (a number, a grid of numbers, a checked formula); a file is not trusted beyond that. */
export function savedAsk(x: unknown): AskResult | undefined {
  if (!x || typeof x !== "object") return undefined;
  const a = x as Record<string, unknown>;
  const str = (v: unknown) => typeof v === "string";
  const strs = (v: unknown) => Array.isArray(v) && v.every(str);
  const ok = str(a["question"]) && str(a["source"]) && str(a["rowsAre"]) && str(a["model"]) && str(a["at"])
    && ["number", "list", "table", "formula"].includes(a["shape"] as string) && ["table", "text", "knowledge", "memory"].includes(a["via"] as string)
    && strs(a["columns"]) && strs(a["notes"]) && strs(a["trail"])
    && Array.isArray(a["cites"]) && a["cites"].every((c) => !!c && typeof c === "object" && str((c as { title?: unknown }).title) && str((c as { url?: unknown }).url))
    && Array.isArray(a["flagged"]) && a["flagged"].every((f) => Array.isArray(f) && f.length === 2 && f.every((n) => Number.isInteger(n)))
    && (a["params"] === undefined || strs(a["params"])) && (a["rowLabels"] === undefined || strs(a["rowLabels"])) && (a["latex"] === undefined || str(a["latex"]))
    && (a["vars"] === undefined || (Array.isArray(a["vars"]) && a["vars"].every((v) => !!v && typeof v === "object" && str((v as { name?: unknown }).name) && str((v as { meaning?: unknown }).meaning))));
  if (!ok) return undefined;
  const r = x as AskResult;
  return validAnswer(r.shape, r.source, r.params ?? []) && (r.params ?? []).every((p) => /^[A-Za-z_\u0391-\u03c9][A-Za-z0-9_\u0391-\u03c9]*$/.test(p)) ? r : undefined;
}

/** The engine source a question cell evaluates: the answer, bound when the cell says `let name =`;
 *  a formula with variables binds a function of them. */
export function askSource(name: string | undefined, r: AskResult): string {
  if (!name) return r.source;
  return r.shape === "formula" && r.params?.length ? `let ${name}(${r.params.join(", ")}) = ${r.source}` : `let ${name} = ${r.source}`;
}
