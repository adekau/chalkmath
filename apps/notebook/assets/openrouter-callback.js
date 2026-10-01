// Where OpenRouter sends the reader back after "Sign in with OpenRouter" (apps/notebook/src/ask-cells.ts,
// signInOpenRouter): trade the code for a key (OAuth PKCE, with the verifier the notebook kept), save the
// key in the lookup settings, and close. The notebook hears of it through a storage event. The code is
// taken off the address bar at once, so it is neither kept in history nor sent anywhere else.
(async () => {
  const msg = (t) => { document.getElementById("msg").textContent = t; };
  const code = new URLSearchParams(location.search).get("code");
  history.replaceState(null, "", location.pathname);
  const PKCE = "chalkmath.openrouter.pkce", KEY = "chalkmath.ask";
  let verifier = null;
  try { verifier = localStorage.getItem(PKCE); } catch { /* storage off */ }
  if (!code || !verifier) { msg("No sign-in is in progress. Start it from Run › Lookup settings in ChalkMath."); return; }
  try {
    const r = await fetch("https://openrouter.ai/api/v1/auth/keys", {
      method: "POST", headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ code, code_verifier: verifier, code_challenge_method: "S256" }),
    });
    const d = await r.json().catch(() => ({}));
    if (!r.ok || typeof d.key !== "string") throw new Error(d.error?.message ?? `OpenRouter answered ${r.status}`);
    let s = {};
    try { s = JSON.parse(localStorage.getItem(KEY) ?? "{}") ?? {}; } catch { s = {}; }
    localStorage.setItem(KEY, JSON.stringify({ ...s, openrouterKey: d.key, backend: "openrouter" }));
    localStorage.removeItem(PKCE);
    msg("Signed in to OpenRouter. You can close this window and go back to ChalkMath.");
    setTimeout(() => window.close(), 900);
  } catch (e) {
    try { localStorage.removeItem(PKCE); } catch { /* storage off */ }
    msg(`The sign-in did not complete: ${e instanceof Error ? e.message : String(e)}. Try again from Run › Lookup settings.`);
  }
})();
