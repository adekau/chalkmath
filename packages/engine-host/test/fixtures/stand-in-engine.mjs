#!/usr/bin/env node
// A stand-in for the native engine, for the host's failure paths: newline-delimited JSON-RPC on stdio
// like engine/Main.lean, where method "die" exits, "hang" never answers, "garbage" answers with a line
// that is not JSON, "slow" answers after 150 ms with the number it was given, and anything else answers with the process id (so a restart shows).
import { createInterface } from "node:readline";
for await (const line of createInterface({ input: process.stdin })) {
  const { id, method, params } = JSON.parse(line);
  if (method === "die") process.exit(3);
  if (method === "slow") { await new Promise((r) => setTimeout(r, 150)); process.stdout.write(JSON.stringify({ jsonrpc: "2.0", id, result: { pid: process.pid, i: params.i } }) + "\n"); continue; }
  if (method === "hang") continue;
  if (method === "garbage") { process.stdout.write("Stack overflow detected. Aborting.\n"); continue; }
  process.stdout.write(JSON.stringify({ jsonrpc: "2.0", id, result: { pid: process.pid, text: "λx. x" } }) + "\n");
}
