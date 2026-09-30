// A page reader for `?` lookups (packages/ask, apps/notebook/src/ask-cells.ts), as a Cloudflare Worker.
//
// Most sites do not let a page on another origin read them, so a lookup that finds a page through
// web search cannot read it from the browser. This worker fetches the page and returns it with CORS
// headers. Deploy it with
//   npx wrangler deploy scripts/ask-proxy/worker.js --name chalkmath-reader --compatibility-date 2026-09-01
// and put `https://chalkmath-reader.<you>.workers.dev/?url={url}` in Run › Lookup settings.
//
// Who can use it: ORIGINS (comma-separated; default the public notebook) is checked against the
// request's Origin header, which stops other web pages from using the reader through visitors'
// browsers, but not a program that sends the header itself. Set TOKEN (a secret: `npx wrangler secret
// put TOKEN`) to require `&token=…` as well, and put it in the reader URL in your settings
// (`…/?token=…&url={url}`); a rate-limiting rule on the route limits what a leaked token costs. To
// use the reader from a local copy, add its origin to ORIGINS (e.g. "http://localhost:4173").
// It sends no cookies and keeps nothing.

const MAX_BYTES = 5_000_000;
const DEFAULT_ORIGINS = "https://adekau.github.io";

export default {
  async fetch(request, env) {
    const origins = (env?.ORIGINS ?? DEFAULT_ORIGINS).split(",").map((s) => s.trim()).filter(Boolean);
    const origin = request.headers.get("Origin") ?? "";
    const allowed = origins.includes(origin);
    const cors = allowed ? { "Access-Control-Allow-Origin": origin, "Vary": "Origin" } : {};
    if (request.method === "OPTIONS") return new Response(null, { status: allowed ? 204 : 403, headers: { ...cors, "Access-Control-Allow-Methods": "GET", "Access-Control-Max-Age": "86400" } });
    if (!allowed) return new Response("This reader serves the ChalkMath notebook only.", { status: 403 });
    if (request.method !== "GET") return new Response("GET only", { status: 405, headers: cors });
    const params = new URL(request.url).searchParams;
    if (env?.TOKEN && params.get("token") !== env.TOKEN) return new Response("A token is required.", { status: 401, headers: cors });
    let target;
    try { target = new URL(params.get("url") ?? ""); } catch { return new Response("?url= must be a URL", { status: 400, headers: cors }); }
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
    // a response with no body (204, 304) cannot be given one
    const empty = r.status === 204 || r.status === 205 || r.status === 304;
    return new Response(empty ? null : new Blob(chunks), { status: r.status, headers: { ...cors, "Content-Type": type, "Cache-Control": "public, max-age=3600" } });
  },
};
