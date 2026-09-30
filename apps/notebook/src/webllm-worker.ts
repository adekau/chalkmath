// The worker the WebGPU model runs in (webllm.ts): WebLLM's own handler, answering the page's engine.
import { WebWorkerMLCEngineHandler } from "@mlc-ai/web-llm";

const handler = new WebWorkerMLCEngineHandler();
self.onmessage = (msg: MessageEvent) => { handler.onmessage(msg); };
