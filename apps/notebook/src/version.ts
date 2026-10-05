/** Which build this is, and the version of each file the page loads (scripts/bundle.mjs). */
declare const __BUILD_ID__: string;
declare const __ASSET_VERSIONS__: Record<string, string>;

/** The build: the commit it was made from, for the About box and error reports. */
export const BUILD = typeof __BUILD_ID__ === "string" ? __BUILD_ID__ : "dev";

/** `file`, a path in the published site, with its version: a hash of its contents, so a browser fetches
 *  it again when it changed and not on every deploy (the engine's wasm and the Lean editor are megabytes).
 *  A file the build did not version carries the build instead. */
export const versioned = (file: string) => `${file}?v=${(typeof __ASSET_VERSIONS__ === "object" && __ASSET_VERSIONS__[file]) || BUILD}`;
