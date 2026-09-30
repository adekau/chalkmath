/**
 * Where a lookup searches, and how it reads what it finds. Nothing here knows a subject: a source is
 * a search box and a way to read a result, so a new kind of question needs no new code.
 *
 * - **Wikipedia** needs no key and answers a page's own origin (CORS), so it works from a static
 *   page with nothing to configure. Its articles are full of tables.
 * - **Web search** is any endpoint that answers SearXNG's JSON (`?q=…&format=json`): a SearXNG
 *   instance queries Google, DuckDuckGo, Bing and Brave for you. The reader supplies its URL.
 * - Most sites do not allow a page on another origin to read them, so a web result is read directly
 *   when it allows that, and otherwise through a **page reader** the reader configures (a proxy that
 *   returns the page with CORS headers, like `scripts/ask-proxy/worker.js`).
 */
import { readPage, type PageContent } from "./html.js";

export type Fetch = (url: string, init?: RequestInit) => Promise<Response>;

export interface Hit { title: string; url: string; snippet: string; source: string }
export interface Page extends PageContent { title: string; url: string; source: string }

export interface Source {
  /** Shown in progress lines and the result's trail: "Wikipedia", "web search". */
  name: string;
  search(query: string, signal?: AbortSignal): Promise<Hit[]>;
}

const UA = "ChalkMath/0.1 (https://github.com/adekau/chalkmath)";

async function json(fetch: Fetch, url: string, signal?: AbortSignal, headers: Record<string, string> = {}): Promise<unknown> {
  const r = await fetch(url, { signal: signal ?? null, headers });
  if (!r.ok) throw new Error(`${new URL(url).host} answered ${r.status}`);
  return r.json();
}

const stripTags = (s: string) => s.replace(/<[^>]*>/g, "").replace(/&quot;/g, "\"").replace(/&amp;/g, "&").replace(/&#0?39;/g, "'");

export function wikipedia(fetch: Fetch, lang = "en"): Source {
  return {
    name: "Wikipedia",
    async search(query, signal) {
      const u = `https://${lang}.wikipedia.org/w/api.php?action=query&list=search&format=json&origin=*&srlimit=5&srsearch=${encodeURIComponent(query)}`;
      const d = await json(fetch, u, signal, { "Api-User-Agent": UA }) as { query?: { search?: { title: string; snippet?: string }[] } };
      return (d.query?.search ?? []).map((s) => ({
        title: s.title, url: `https://${lang}.wikipedia.org/wiki/${encodeURIComponent(s.title.replace(/ /g, "_"))}`,
        snippet: stripTags(s.snippet ?? ""), source: "Wikipedia",
      }));
    },
  };
}

/** A SearXNG-style JSON endpoint. `endpoint` is either a URL with `{q}` where the query goes, or an
 *  instance's base URL (`/search?q=…&format=json` is appended). */
export function webSearch(fetch: Fetch, endpoint: string): Source {
  const url = (q: string) => endpoint.includes("{q}") ? endpoint.replace("{q}", encodeURIComponent(q))
    : `${endpoint.replace(/\/+$/, "").replace(/\/search$/, "")}/search?format=json&q=${encodeURIComponent(q)}`;
  return {
    name: "web search",
    async search(query, signal) {
      const d = await json(fetch, url(query), signal) as { results?: { title?: string; url?: string; content?: string }[] };
      return (d.results ?? []).filter((r) => r.url && /^https?:/.test(r.url)).slice(0, 8)
        .map((r) => ({ title: r.title ?? r.url!, url: r.url!, snippet: r.content ?? "", source: new URL(r.url!).host.replace(/^www\./, "") }));
    },
  };
}

/** A Wikipedia article's URL, as the language and title its REST API takes. */
function wikiTitle(url: string): { lang: string; title: string } | null {
  const m = /^https?:\/\/([a-z-]+)\.(?:m\.)?wikipedia\.org\/wiki\/([^?#]+)/.exec(url);
  return m ? { lang: m[1]!, title: m[2]! } : null;
}

export interface ReadOptions {
  /** A page reader: a URL with `{url}` where the page's URL goes, or a prefix it is appended to. */
  reader?: string | undefined;
  signal?: AbortSignal | undefined;
}

/** Read a search result: Wikipedia through its REST API, anything else directly if it allows that,
 *  else through the reader. Null when the page cannot be read from here. */
export async function readHit(fetch: Fetch, hit: Hit, opts: ReadOptions = {}): Promise<Page | null> {
  const wiki = wikiTitle(hit.url);
  const tries: string[] = wiki
    ? [`https://${wiki.lang}.wikipedia.org/api/rest_v1/page/html/${wiki.title}`]
    : [hit.url, ...(opts.reader ? [opts.reader.includes("{url}") ? opts.reader.replace("{url}", encodeURIComponent(hit.url)) : opts.reader + hit.url] : [])];
  for (const u of tries) {
    try {
      const r = await fetch(u, { signal: opts.signal ?? null, headers: wiki ? { "Api-User-Agent": UA } : {} });
      if (!r.ok) continue;
      const body = await r.text();
      return { title: hit.title, url: hit.url, source: hit.source, ...readPage(body, r.headers.get("content-type") ?? "") };
    } catch (e) {
      if (opts.signal?.aborted) throw e;
      // a site that refuses cross-origin reads fails as a network error: try the reader
    }
  }
  return null;
}
