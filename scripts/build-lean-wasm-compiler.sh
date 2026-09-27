#!/usr/bin/env bash
# Lean itself — parser, elaborator, kernel, IR interpreter, language server — for wasm32, so the
# notebook can run Lean cells in the browser. The engine build (build-wasm.sh) links one compiled Lean
# program against the runtime and Init; this links the whole compiler.
#
# Requires: what build-lean-wasm-runtime.sh requires (elan toolchain from engine/lean-toolchain,
#           emsdk, git), plus node and python3.
# Output:   engine/toolchains/lean-<ver>-wasm32/compiler/
#             bin/lean.{js,wasm}           the `lean` command-line driver, for Node (it compiles the oleans)
#             lean-server.{js,wasm}        Lean's file worker for a web worker (engine/wasm/server/)
#             lean-initialize.json       the watchdog's `initialize` reply, for the in-browser watchdog
#             lean-lib.pack.gz             the 32-bit library, packed for the worker
#             lib/lean/**.olean            Init compiled by that driver: 32-bit oleans (step 7)
#
# How it differs from Lean's own Emscripten recipe (src/CMakeLists.txt), which the v4.15.0 linux_wasm32
# release was built with:
#   - Static link with a generated symbol table (scripts/lean-wasm-symtab.py) instead of MAIN_MODULE=1
#     plus EXPORT_ALL: the IR interpreter finds compiled code by name, and on that release 42% of the
#     elaborating thread went to Emscripten's JavaScript dlsym. engine/wasm/lean-compiler-emscripten.patch
#     points `lookup_symbol_in_cur_exe` at the table.
#   - The C for Init/Std/Lean is emitted by the host `lean` from the tagged sources, as the runtime
#     script does for Init, not taken from stage0 (which lags the tag).
#   - Threads stay on (-pthread, MULTI_THREAD): the language server reads LSP messages while elaboration
#     runs in tasks, and elaboration waits on promises other tasks resolve. So everything is compiled a
#     second time here, with -pthread, into its own tree; the engine's single-threaded libraries are
#     untouched, and only a page hosting Lean cells needs cross-origin isolation (COOP/COEP).
set -euo pipefail
cd "$(dirname "$0")/../engine"
VER=$(sed -E 's/.*:v//' lean-toolchain)
TAG="v$VER"
LEAN=$(elan which lean)
PREFIX=$("$LEAN" --print-prefix)
SRC=$PWD/toolchains/src/lean4-$TAG
UV=$PWD/toolchains/src/libuv
TC=$PWD/toolchains/lean-$VER-wasm32
OUT=$TC/compiler
JOBS=${JOBS:-$(sysctl -n hw.logicalcpu 2>/dev/null || nproc)}
SCRIPTS=$(cd ../scripts && pwd)

# 0. The runtime script fetches and patches the sources and writes the generated headers.
../scripts/build-lean-wasm-runtime.sh
if ! (cd "$SRC" && git apply --reverse --check "$OLDPWD/wasm/lean-compiler-emscripten.patch" 2>/dev/null); then
  (cd "$SRC" && git apply "$OLDPWD/wasm/lean-compiler-emscripten.patch")
fi
mkdir -p "$OUT"/{c,obj/c,obj/cpp,bin,lib/lean}

EMFLAGS="-O3 -DNDEBUG -pthread -fwasm-exceptions"
CFLAGS="$EMFLAGS -DLEAN_EXPORTING -ffp-contract=off -I$TC/include"
CXXFLAGS="-std=c++20 $EMFLAGS -DLEAN_EXPORTING -D__CLANG__ -DLEAN_BUILD_TYPE=\"Release\" -ffp-contract=off \
  -DLEAN_EMSCRIPTEN -DLEAN_MULTI_THREAD -Wno-unused-parameter -I$TC/include -I$SRC/src -I$SRC/src/include -I$UV/include"
export LEAN CFLAGS CXXFLAGS OUT SRC

# 1. C for every module in the closure of Lean's library roots (the `Init`, `Std` and `Lean` lean_libs of
#    src/lakefile.toml.in), emitted by the host lean against the toolchain's oleans.
MODS=$(python3 "$SCRIPTS/lean-wasm-oleans.py" --closure "$PREFIX/src/lean" Init Std Lean Lean.Compiler.IR.EmitLLVM Lean.Compiler.LCNF.Probing)
echo "== emitting C for $(wc -l <<<"$MODS" | tr -d ' ') modules"
(cd "$PREFIX/src/lean" && sed 's#\.#/#g' <<<"$MODS" | LEAN_PATH="$PREFIX/lib/lean" xargs -P "$JOBS" -I{} bash -c \
  'o="$OUT/c/{}.c"; [ -f "$o" ] && exit 0; mkdir -p "$(dirname "$o")"; "$LEAN" -R . --c="$o.tmp" "{}.lean" && mv "$o.tmp" "$o"')

# 2. Compile it.
echo "== compiling the emitted C"
(cd "$OUT/c" && find . -name '*.c' | xargs -P "$JOBS" -I{} bash -c \
  'o="$OUT/obj/c/{}.o"; [ -f "$o" ] && exit 0; mkdir -p "$(dirname "$o")"; emcc $CFLAGS -c "{}" -o "$o.tmp" && mv "$o.tmp" "$o"')

# 3. The C++ half: runtime (again, threaded), kernel, library, util, initialize, and the shell's `lean_main`.
sed 's/@[A-Z_]*@//g' "$SRC/src/util/ffi.cpp" > "$OUT/ffi.cpp"
RT="debug thread mpz utf8 object apply exception interrupt memory stackinfo compact init_module io hash byteslice platform alloc allocprof sharecommon stack_overflow process object_ref mpn mutex libuv uv/net_addr uv/event_loop uv/timer uv/tcp uv/udp uv/dns uv/system uv/signal openssl"
CPP=$( { for s in $RT; do echo "runtime/$s.cpp"; done
         (cd "$SRC/src" && ls kernel/*.cpp library/*.cpp library/constructions/*.cpp util/*.cpp initialize/*.cpp shell/lean.cpp) ; } | grep -v -e '^shell/lean_js' -e '^util/ffi.cpp' )   # ffi.cpp: the configured copy is compiled below
echo "== compiling $(wc -l <<<"$CPP" | tr -d ' ') C++ files"
xargs -P "$JOBS" -I{} bash -c 'o="$OUT/obj/cpp/{}.o"; [ -f "$o" ] && exit 0; mkdir -p "$(dirname "$o")"; em++ $CXXFLAGS -c "$SRC/src/{}" -o "$o.tmp" && mv "$o.tmp" "$o"' <<<"$CPP"
[ -f "$OUT/obj/cpp/ffi.o" ] || em++ $CXXFLAGS -c "$OUT/ffi.cpp" -o "$OUT/obj/cpp/ffi.o"
[ -f "$OUT/obj/cpp/uv-stubs.o" ] || emcc $CFLAGS -I"$UV/include" -c c/uv-stubs.c -o "$OUT/obj/cpp/uv-stubs.o"

# 4. The symbol table over everything both binaries link (replaces dlsym; see the header comment). The
#    two `main`s (the CLI's and the language server's) are left out of it and linked separately.
find "$OUT/obj" -name '*.o' ! -name symtab.o ! -path '*/shell/lean.cpp.o' ! -path '*/server/*' | sort > "$OUT/objs.txt"
echo "== symbol table over $(wc -l < "$OUT/objs.txt" | tr -d ' ') objects"
xargs "$(dirname "$(command -v emcc)")/../bin/llvm-nm" --defined-only --extern-only < "$OUT/objs.txt" > "$OUT/nm.txt"
find "$OUT/c" -name '*.c' | sort > "$OUT/c-files.txt"
python3 "$SCRIPTS/lean-wasm-symtab.py" "$OUT/symtab.c" "$OUT/nm.txt" "$OUT/c-files.txt"
emcc $CFLAGS -O1 -c "$OUT/symtab.c" -o "$OUT/obj/symtab.o"
{ cat "$OUT/objs.txt"; echo "$OUT/obj/symtab.o"; } > "$OUT/link.rsp"
# PROXY_TO_PTHREAD keeps the JS main thread free to start the task manager's workers and to service the
# filesystem calls pthreads proxy to it; the stacks are sized for the elaborator's recursion.
LINKFLAGS="$EMFLAGS -sPROXY_TO_PTHREAD=1 -sPTHREAD_POOL_SIZE=2 -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=512MB \
  -sMAXIMUM_MEMORY=4GB -sSTACK_SIZE=16MB -sDEFAULT_PTHREAD_STACK_SIZE=8MB -sDEFAULT_TO_CXX=1"

# 5. The command-line driver, for Node: what compiles the oleans.
echo "== linking bin/lean.js"
emcc -o "$OUT/bin/lean.js" @"$OUT/link.rsp" "$OUT/obj/cpp/shell/lean.cpp.o" $LINKFLAGS -lnodefs.js -sENVIRONMENT=node -sEXIT_RUNTIME=1

# 6. The language server's file worker (engine/wasm/server/): LeanWorker.lean's `main`, with stdin/stdout
#    over leanweb.c's shared-memory queue. The host (packages/engine-host/src/lean-server.ts) writes the
#    library into the virtual filesystem, then calls `main`.
echo "== linking lean-server.js"
mkdir -p "$OUT/obj/server"
LEAN_PATH="$PREFIX/lib/lean" "$LEAN" --c="$OUT/server-LeanWorker.c" wasm/server/LeanWorker.lean
emcc $CFLAGS -c "$OUT/server-LeanWorker.c" -o "$OUT/obj/server/LeanWorker.o"
emcc $CFLAGS -c wasm/server/leanweb.c -o "$OUT/obj/server/leanweb.o"
emcc -o "$OUT/lean-server.js" @"$OUT/link.rsp" "$OUT/obj/server/LeanWorker.o" "$OUT/obj/server/leanweb.o" $LINKFLAGS \
  -sMODULARIZE=1 -sEXPORT_NAME=createLeanServer -sENVIRONMENT=web,worker,node -sINVOKE_RUN=0 -sEXIT_RUNTIME=0 \
  -sEXPORTED_FUNCTIONS=_main,_malloc,_free -sEXPORTED_RUNTIME_METHODS=callMain,FS,HEAPU8,HEAP32
LEAN_PATH="$PREFIX/lib/lean" "$LEAN" wasm/server/capabilities.lean > "$OUT/lean-initialize.json"
ls -la "$OUT/bin" "$OUT"/lean-server.*

# 7. 32-bit oleans for Init, compiled by the CLI (what `import Init`, every file's implicit import, loads),
#    packed for the worker: [u32 LE length of a JSON index [[path, size], ...]] [index] [files], gzipped.
echo "== compiling Init to 32-bit oleans"
python3 "$SCRIPTS/lean-wasm-oleans.py" "$OUT/bin/lean.js" "$PREFIX/src/lean" "$OUT/lib/lean" "$JOBS" Init
python3 - "$OUT/lib/lean" "$OUT/lean-lib.pack.gz" <<'PY'
import gzip, json, os, struct, sys
root, out = sys.argv[1], sys.argv[2]
files = sorted(os.path.relpath(os.path.join(d, f), root) for d, _, fs in os.walk(root) for f in fs
               if f.endswith(('.olean', '.olean.server', '.olean.private', '.ir', '.ir.sig')))
index = json.dumps([[f, os.path.getsize(os.path.join(root, f))] for f in files]).encode()
with gzip.open(out, 'wb', compresslevel=6) as z:
    z.write(struct.pack('<I', len(index)) + index)
    for f in files:
        z.write(open(os.path.join(root, f), 'rb').read())
print(f'lean-lib.pack.gz: {len(files)} files, {os.path.getsize(out)} bytes')
PY
