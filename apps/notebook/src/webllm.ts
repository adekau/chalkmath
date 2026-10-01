/**
 * The WebGPU model for `?` lookups (ask-cells.ts), bundled on its own (dist/ask/webllm.js) so the
 * notebook loads it only when a lookup needs it and Chrome's built-in model is not there. The model
 * runs in a worker (dist/ask/webllm-worker.js); its weights come from Hugging Face on first use and
 * stay in the browser's cache.
 */
import { CreateWebWorkerMLCEngine, type InitProgressReport } from "@mlc-ai/web-llm";
import type { Model } from "@chalkmath/ask";

export async function createEngine(workerUrl: string, modelId: string, progress: (fraction: number, text: string) => void): Promise<Model> {
  const worker = new Worker(workerUrl, { type: "module" });
  const engine = await CreateWebWorkerMLCEngine(worker, modelId, {
    initProgressCallback: (r: InitProgressReport) => progress(r.progress, r.text),
  }).catch((e: unknown) => { worker.terminate(); throw e; });
  return {
    async unload() { try { await engine.unload(); } finally { worker.terminate(); } },
    id: modelId.replace(/-q\d+f\d+(_\d+)?-MLC$/, ""),
    context: 7000,   // a 4k-token context, less the prompt and the reply
    async complete({ system, user, schema, signal }) {
      const stop = () => { void engine.interruptGenerate(); };
      signal?.addEventListener("abort", stop);
      try {
        const r = await engine.chat.completions.create({
          messages: [{ role: "system", content: system }, { role: "user", content: user }],
          temperature: 0, max_tokens: 1024,
          response_format: { type: "json_object", schema: JSON.stringify(schema) },
          // Qwen3 thinks aloud before answering unless told not to; the schema is the answer
          ...(modelId.startsWith("Qwen3") ? { extra_body: { enable_thinking: false } } : {}),
        });
        return r.choices[0]?.message.content ?? "";
      } finally { signal?.removeEventListener("abort", stop); }
    },
  };
}
