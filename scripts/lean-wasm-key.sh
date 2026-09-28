#!/usr/bin/env bash
# The name of the release that holds Lean for wasm32 (scripts/build-lean-wasm-compiler.sh's output) built
# from this checkout: `lean-wasm-<lean version>-<hash of every input of that build>`. The Lean for wasm
# workflow (.github/workflows/lean-wasm.yml) publishes it; the Pages deploy downloads it by this name, so
# a deploy only ever ships the Lean its own sources describe.
set -euo pipefail
cd "$(dirname "$0")/.."
INPUTS=(engine/lean-toolchain engine/wasm/emscripten-version engine/wasm/lean-runtime-emscripten.patch
        engine/wasm/lean-compiler-emscripten.patch engine/wasm/uv-posix.c engine/wasm/server/*
        scripts/build-lean-wasm-runtime.sh scripts/build-lean-wasm-compiler.sh scripts/lean-wasm-symtab.py
        scripts/lean-wasm-oleans.py)
VER=$(sed -E 's/.*:v//' engine/lean-toolchain)
HASH=$(for f in "${INPUTS[@]}"; do printf '%s\n' "$f"; sha256sum < "$f"; done | sha256sum | cut -c1-12)
echo "lean-wasm-$VER-$HASH"
