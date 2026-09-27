#!/usr/bin/env bash
# Build the Lean runtime + Init for wasm32 from source ("Road B" in book/SPIKE-RESULTS.md).
#
# Lean stopped shipping a prebuilt linux_wasm32 runtime after v4.15.0, so for a current toolchain
# we build the two static libraries a Lean program needs ourselves:
#   libleanrt.a  src/runtime/*.cpp from the leanprover/lean4 tag matching engine/lean-toolchain,
#                compiled with em++ using the flags src/CMakeLists.txt uses for Emscripten
#                (USE_GMP=OFF, USE_MIMALLOC=OFF, MMAP=OFF, MULTI_THREAD=OFF; no -pthread, no LTO)
#   libInit.a    C emitted for every Init module by the *same* host `lean` that built the toolchain's
#                .oleans (`lean --c`), compiled with emcc.
#   libStd.a     the same for the Std modules the engine imports, transitively (step 5).
# The Lean compiler itself is never built; the host toolchain from elan does all elaboration.
#
# Requires: elan toolchain from engine/lean-toolchain, emcc/em++/emar (emsdk), git, curl.
# Output:   engine/toolchains/lean-<ver>-wasm32/{include,lib/libleanrt.a,lib/libInit.a,lib/libStd.a}
# Patch:    engine/wasm/lean-runtime-emscripten.patch (the two stub signatures from lean4#14973)
set -euo pipefail
cd "$(dirname "$0")/../engine"
VER=$(sed -E 's/.*:v//' lean-toolchain)
TAG="v$VER"
LEAN=$(elan which lean)   # elan resolves the pin in engine/lean-toolchain
PREFIX=$("$LEAN" --print-prefix)
GITHASH=$("$LEAN" -g)
TC=$PWD/toolchains/lean-$VER-wasm32
SRC=$PWD/toolchains/src/lean4-$TAG
UV=$PWD/toolchains/src/libuv
JOBS=${JOBS:-$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)}
mkdir -p toolchains/src "$TC/include/lean" "$TC/lib" "$TC/obj/runtime/uv" "$TC/obj/Init" "$TC/c"

# 1. Sources: lean4 at the pinned tag (runtime only is used) + libuv headers (io.cpp includes uv.h).
if [ ! -d "$SRC" ]; then
  git clone --depth 1 --branch "$TAG" https://github.com/leanprover/lean4 "$SRC"
  (cd "$SRC" && git apply "$OLDPWD/wasm/lean-runtime-emscripten.patch")
fi
if [ ! -d "$UV" ]; then
  git clone --depth 1 --branch v1.48.0 https://github.com/libuv/libuv "$UV"   # version pinned by lean4's own CMake
fi

# 2. Generated headers (what CMake's configure_file would produce), mimalloc off.
cp "$SRC/src/include/lean/"*.h "$TC/include/lean/"
cat > "$TC/include/lean/version.h" <<H
#pragma once
#define LEAN_VERSION_MAJOR $(cut -d. -f1 <<<"$VER")
#define LEAN_VERSION_MINOR $(cut -d. -f2 <<<"$VER")
#define LEAN_VERSION_PATCH $(cut -d. -f3 <<<"$VER")
#define LEAN_VERSION_IS_RELEASE 1
#define LEAN_SPECIAL_VERSION_DESC ""
#define LEAN_VERSION_STRING "$VER"
#define LEAN_PLATFORM_TARGET "wasm32-unknown-emscripten"
#define LEAN_MANUAL_ROOT "https://lean-lang.org/doc/reference/$TAG/"
H
cat > "$TC/include/lean/config.h" <<H
#pragma once
#include <lean/version.h>
/* no LEAN_MIMALLOC: the wasm build uses the libc allocator (USE_MIMALLOC=OFF) */
#define LEAN_IS_STAGE0 0
H
echo "#define LEAN_GITHASH \"$GITHASH\"" > "$TC/include/githash.h"

# 3. libleanrt.a
if [ ! -f "$TC/lib/libleanrt.a" ]; then
  echo "== compiling runtime ($SRC/src/runtime)"
  CXXFLAGS="-std=c++20 -Wall -Wextra -O3 -DNDEBUG -DLEAN_EXPORTING -D__CLANG__ -DLEAN_BUILD_TYPE=\"Release\" -ffp-contract=off -DLEAN_EMSCRIPTEN -fwasm-exceptions -I$TC/include -I$SRC/src -I$SRC/src/include -I$UV/include"
  RT="debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module io hash byteslice platform alloc allocprof sharecommon stack_overflow process object_ref mpn mutex libuv uv/net_addr uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal openssl"
  export CXXFLAGS SRC TC
  echo "$RT" | tr ' ' '\n' | xargs -P "$JOBS" -I{} bash -c 'em++ $CXXFLAGS -c "$SRC/src/runtime/{}.cpp" -o "$TC/obj/runtime/{}.o"'
  emar rcs "$TC/lib/libleanrt.a" $(for s in $RT; do echo "$TC/obj/runtime/$s.o"; done)
fi

# The flags every emitted C file is compiled with. LEAN_EMSCRIPTEN matters to lean.h itself: it makes
# LEAN_SCALAR_PTR_LITERAL, which emitted C uses for static objects' 64-bit scalars (a Name literal's
# precomputed hash), fill two 32-bit slots; without it the hash is truncated and those names miss in
# every hash map keyed by Name. The flags are recorded beside the archives, and a change rebuilds them.
CFLAGS="-O3 -DNDEBUG -DLEAN_EXPORTING -DLEAN_EMSCRIPTEN -ffp-contract=off -fwasm-exceptions -I$TC/include"
export CFLAGS
if [ "$CFLAGS" != "$(cat "$TC/obj/cflags.txt" 2>/dev/null)" ]; then
  rm -rf "$TC/lib/libInit.a" "$TC/lib/libStd.a" "$TC/obj/Init" "$TC/obj/Std" "$TC/obj/std-modules.txt"
  printf '%s' "$CFLAGS" > "$TC/obj/cflags.txt"
fi

# 4. libInit.a: emit C with the host lean, compile with emcc.
if [ ! -f "$TC/lib/libInit.a" ]; then
  echo "== emitting C for Init with $LEAN"
  export LEAN LEAN_PATH="$PREFIX/lib/lean" TC
  (cd "$PREFIX/src/lean" && { echo Init.lean; find Init -name '*.lean'; } | xargs -P "$JOBS" -I{} bash -c 'f={}; o="$TC/c/${f%.lean}.c"; mkdir -p "$(dirname "$o")"; [ -f "$o" ] || "$LEAN" -R . --c="$o" "$f"')
  echo "== compiling $(find "$TC/c" -name '*.c' | wc -l | tr -d ' ') Init modules"
  (cd "$TC/c" && find Init Init.c -name '*.c' | xargs -P "$JOBS" -I{} bash -c 'c={}; o="$TC/obj/Init/${c%.c}.o"; mkdir -p "$(dirname "$o")"; [ -f "$o" ] || emcc $CFLAGS -c "$c" -o "$o"')
  find "$TC/obj/Init" -name '*.o' > "$TC/obj/init-objs.txt"
  emar rcs "$TC/lib/libInit.a" $(cat "$TC/obj/init-objs.txt")
fi
# 5. libStd.a: the Std modules the engine imports, transitively (Std is not part of Init; only the
#    engine's own imports are elaborated, since e.g. Std.Tactic.BVDecide is heavy and Std.Net needs
#    libuv). The list is kept beside the archive and the step reruns when a new import widens it.
STD_MODS=$(python3 - "$PREFIX/src/lean" "$PWD/MathEngine" <<'PY'
import re, os, sys
root, eng = sys.argv[1], sys.argv[2]
imp = re.compile(r'^\s*(?:(?:public|private|meta|all)\s+)*import\s+(.+)$', re.M)
def imports(text):
    text = re.sub(r'/-.*?-/', '', text, flags=re.S)
    return [t for m in imp.finditer(text) for t in m.group(1).split() if t.startswith('Std.')]
seen, order = set(), []
def visit(m):
    if m in seen: return
    seen.add(m)
    path = os.path.join(root, m.replace('.', '/') + '.lean')
    if os.path.exists(path):
        for d in imports(open(path, encoding='utf8').read()): visit(d)
    order.append(m)
for f in sorted(os.listdir(eng)):
    if f.endswith('.lean'):
        for d in imports(open(os.path.join(eng, f), encoding='utf8').read()): visit(d)
print('\n'.join(order))
PY
)
if [ ! -f "$TC/lib/libStd.a" ] || [ "$STD_MODS" != "$(cat "$TC/obj/std-modules.txt" 2>/dev/null)" ]; then
  echo "== emitting C for $(wc -w <<<"$STD_MODS" | tr -d ' ') Std modules with $LEAN"
  mkdir -p "$TC/obj/Std"
  export LEAN LEAN_PATH="$PREFIX/lib/lean" TC
  (cd "$PREFIX/src/lean" && tr ' ' '\n' <<<"$STD_MODS" | sed 's#\.#/#g; s#$#.lean#' | xargs -P "$JOBS" -I{} bash -c 'f={}; o="$TC/c/${f%.lean}.c"; mkdir -p "$(dirname "$o")"; [ -f "$o" ] || "$LEAN" -R . --c="$o" "$f"')
  echo "== compiling Std modules"
  (cd "$TC/c" && find Std -name '*.c' | xargs -P "$JOBS" -I{} bash -c 'c={}; o="$TC/obj/Std/${c%.c}.o"; mkdir -p "$(dirname "$o")"; [ -f "$o" ] || emcc $CFLAGS -c "$c" -o "$o"')
  rm -f "$TC/lib/libStd.a"
  emar rcs "$TC/lib/libStd.a" $(find "$TC/obj/Std" -name '*.o')
  printf '%s' "$STD_MODS" > "$TC/obj/std-modules.txt"
fi
ls -la "$TC/lib"
