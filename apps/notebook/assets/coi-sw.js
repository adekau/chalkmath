// Cross-origin isolation for a static host, which cannot send the headers itself (GitHub Pages cannot).
// Lean cells run Lean's language server as threaded WebAssembly, which needs SharedArrayBuffer, which a
// page only gets when it is cross-origin isolated. The notebook registers this worker the first time a
// notebook has Lean cells (apps/notebook/src/lean-cells.ts); it adds COOP and COEP to every response of
// this origin. COEP is `credentialless` where the browser supports it, so images from other sites keep
// loading; elsewhere (Safari) `require-corp`, under which only images that opt in do.
const coep = new URL(self.location.href).searchParams.get("coep") === "require-corp" ? "require-corp" : "credentialless";

self.addEventListener("install", () => self.skipWaiting());
self.addEventListener("activate", (event) => event.waitUntil(self.clients.claim()));

self.addEventListener("fetch", (event) => {
  const request = event.request;
  // a request the browser may only answer from its cache, from another origin, cannot be re-fetched here
  if (request.cache === "only-if-cached" && request.mode !== "same-origin") return;
  if (new URL(request.url).origin !== self.location.origin) return;
  event.respondWith(fetch(request).then((response) => {
    if (response.status === 0) return response;   // opaque: nothing to add
    const headers = new Headers(response.headers);
    headers.set("Cross-Origin-Opener-Policy", "same-origin");
    headers.set("Cross-Origin-Embedder-Policy", coep);
    return new Response(response.body, { status: response.status, statusText: response.statusText, headers });
  }));
});
