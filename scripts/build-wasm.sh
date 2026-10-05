#!/usr/bin/env bash
# Lean -> C -> wasm. Requires: emcc on PATH (emsdk), elan, git.
# Output: apps/notebook/dist/engine-lean.{js,wasm}
#
# The Lean runtime + Init for wasm32 come from scripts/build-lean-wasm-runtime.sh (built from source
# for the toolchain pinned in engine/lean-toolchain; cached under engine/toolchains/). The engine's
# own C comes from `lake build` with the host toolchain — Lean's C output is target-independent.
# Std modules the engine imports are built the same way into libStd.a (Std is not part of Init).
set -euo pipefail
cd "$(dirname "$0")/../engine"
VER=$(sed -E 's/.*:v//' lean-toolchain)
TC=${LEAN_WASM_TOOLCHAIN:-toolchains/lean-$VER-wasm32}
# always: the runtime script is incremental, and rebuilds libStd.a when the engine imports more of Std
../scripts/build-lean-wasm-runtime.sh
lake build                                     # produces .lake/build/ir/**/*.c
OUT=../apps/notebook/dist; mkdir -p "$OUT"
# NOTE: no -pthread. The runtime is built single-threaded (MULTI_THREAD=OFF); -pthread would force
# COOP/COEP headers (SharedArrayBuffer) on the host page, a real constraint for "self-hostable".
# -sDEFAULT_TO_CXX: the Lean runtime is C++ (debug.cpp uses iostreams), so the link needs libc++ even
# though the driver is emcc and every input here is C; newer emscripten no longer assumes it.
# -DLEAN_EMSCRIPTEN: lean.h's 32-bit layout for static scalars (see build-lean-wasm-runtime.sh)
# The stack: optimized builds put static data below emscripten's stack (64 KB by default), so an
# overflow would overwrite it silently; --stack-first puts the stack at the bottom of memory, where an
# overflow traps, and the worker then reports the engine crashed (packages/engine-host/src/worker-lean.ts).
emcc -O2 -DLEAN_EMSCRIPTEN -sDEFAULT_TO_CXX=1 -o "$OUT/engine-lean.js" \
  -I "$TC/include" -I toolchains/src/libuv/include -L "$TC/lib" \
  c/shim.c c/uv-stubs.c $(find .lake/build/ir/MathEngine -name '*.c') .lake/build/ir/MathEngine.c \
  -lStd -lInit -lleanrt \
  -sMODULARIZE=1 -sEXPORT_NAME=createMathEngine -sENVIRONMENT=worker,node \
  -sEXPORTED_FUNCTIONS=_mathengine_init,_mathengine_call,_mathengine_free,_malloc,_free \
  -sEXPORTED_RUNTIME_METHODS=ccall,cwrap,UTF8ToString,stringToUTF8,lengthBytesUTF8 \
  -sALLOW_MEMORY_GROWTH=1 -sEXIT_RUNTIME=0 -fwasm-exceptions \
  -sSTACK_SIZE=1MB -Wl,--stack-first
ls -la "$OUT"/engine-lean.*
