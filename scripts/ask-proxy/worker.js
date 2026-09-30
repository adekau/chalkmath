// A page reader for `?` lookups (packages/ask, apps/notebook/src/ask-cells.ts), as a Cloudflare Worker.
//
// Most sites do not let a page on another origin read them, so a lookup that finds a page through
// web search cannot read it from the browser. This worker fetches the page and returns it with CORS
// headers, for the notebook's origins only: it is not an open proxy. Deploy it with
//   npx wrangler deploy scripts/ask-proxy/worker.js --name chalkmath-reader --compatibility-date 2026-09-01
// set ORIGINS (comma-separated, e.g. "https://adekau.github.io,http://localhost:4173") in its
// variables, and put `https://chalkmath-reader.<you>.workers.dev/?url={url}` in Run › Lookup settings.
// It sends no cookies and keeps nothing.

const MAX_BYTES = 5_000_000;
const DEFAULT_ORIGINS = "https://adekau.github.io,http://localhost:4173";

export default {
  async fetch(request, env) {
    const origins = (env?.ORIGINS ?? DEFAULT_ORIGINS).split(",").map((s) => s.trim()).filter(Boolean);
    const origin = request.headers.get("Origin") ?? "";
    const allowed = origins.includes(origin);
    const cors = allowed ? { "Access-Control-Allow-Origin": origin, "Vary": "Origin" } : {};
    if (request.method === "OPTIONS") return new Response(null, { status: allowed ? 204 : 403, headers: { ...cors, "Access-Control-Allow-Methods": "GET", "Access-Control-Max-Age": "86400" } });
    if (!allowed) return new Response("This reader serves the ChalkMath notebook only.", { status: 403 });
    if (request.method !== "GET") return new Response("GET only", { status: 405, headers: cors });
    let target;
    try { target = new URL(new URL(request.url).searchParams.get("url") ?? ""); } catch { return new Response("?url= must be a URL", { status: 400, headers: cors }); }
    if (target.protocol !== "https:" && target.protocol !== "http:") return new Response("http and https only", { status: 400, headers: cors });
    let r;
    try {
      r = await fetch(target.href, { redirect: "follow", headers: { "User-Agent": "ChalkMath page reader (https://github.com/adekau/chalkmath)", "Accept": "text/html,text/plain;q=0.9,*/*;q=0.5" } });
    } catch (e) {
      return new Response(`Could not fetch ${target.host}: ${e instanceof Error ? e.message : String(e)}`, { status: 502, headers: cors });
    }
    const type = r.headers.get("content-type") ?? "";
    if (!/text\/|html|xml|json/i.test(type)) return new Response(`Not a text page (${type || "no type"})`, { status: 415, headers: cors });
    // read at most MAX_BYTES: a page is text, and a lookup reads its tables and paragraphs
    const reader = r.body?.getReader();
    const chunks = [];
    let size = 0;
    while (reader) {
      const { done, value } = await reader.read();
      if (done) break;
      size += value.byteLength;
      if (size > MAX_BYTES) { await reader.cancel(); break; }
      chunks.push(value);
    }
    return new Response(new Blob(chunks), { status: r.status, headers: { ...cors, "Content-Type": type, "Cache-Control": "public, max-age=3600" } });
  },
};
