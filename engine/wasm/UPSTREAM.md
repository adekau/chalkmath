# Upstream notes for leanprover/lean4 (not yet reported)

Findings from building the Lean runtime for wasm32 on v4.33.1 (see `book/SPIKE-RESULTS.md`), rechecked on v4.34.1:
all of §1–§3 are still present there, and the patch applies unchanged. Each item is
patched locally in `lean-runtime-emscripten.patch` or worked around in `../c/uv-stubs.c`. Nothing here
has been filed; review the project's contribution guidelines (`CONTRIBUTING.md`, RFC/issue templates,
`stage0` update rules) before opening anything.

## 1. Draft issue: `String.toList` builds `[]` with `lean_box_uint32(0)` (breaks 32-bit / wasm32)

**Title:** `string_to_list_core` builds the empty list with `lean_box_uint32(0)`, which is a heap object on 32-bit

**Description**

`src/runtime/object.cpp`, `string_to_list_core`:

```cpp
obj_res  r = lean_box_uint32(0);   // intended: the `List.nil` scalar
```

On 64-bit `lean_box_uint32(v)` is `lean_box(v)`, so this is the scalar `nil` and everything works.
On 32-bit (`sizeof(void*) == 4`, e.g. Emscripten wasm32) `lean_box_uint32` allocates a constructor
object (`lean_alloc_ctor(0, 0, 4)`). The resulting "nil" has tag 0, so compiled pattern matching
(`lean_obj_tag`) still treats it as `[]`, but runtime code that tests `lean_is_scalar` does not.
`lean_string_mk` is one such caller: it walks the list until `lean_is_scalar(o)`, reads the fake
cell's fields as `head`/`tail`, and never terminates (the `std::string` grows until `bad_alloc`).

Every `String.toList` result carries this bogus terminator, so any 32-bit program that passes a
`toList` result (or a suffix of it) back to `String.ofList` / `String.mk` hangs. Because
`List.takeWhile` returns its input unchanged when every element matches, this shows up in ordinary
lexer code: `String.ofList ((s.toList).takeWhile Char.isDigit)` hangs when the digits run to the
end of the string, but works when they don't (a fresh list from `Array.toList` is used then).

**Reproduction** (wasm32; a native 32-bit build should behave the same)

```lean
def main : IO Unit := do
  let s := "x"
  IO.println (String.ofList s.toList)   -- hangs, then std::bad_alloc
```

Observed with the v4.15.0 `linux_wasm32` release runtime and with v4.33.1 built from source with
Emscripten 5.0.6 (`USE_GMP=OFF USE_MIMALLOC=OFF MMAP=OFF MULTI_THREAD=OFF`). Heap dump from an
instrumented `lean_string_mk` on `"0".toList`:

```
cell 0 @0x5704c rc=1 tag=1 other=2 head=0x57064 tail=0x57424    -- cons '0'
cell 1 @0x57424 rc=3 tag=0 other=0 head=0 tail=0x18            -- "nil": a 0-field ctor object, not lean_box(0)
```

**Fix**

```cpp
obj_res  r = lean_box(0);
```

Same pattern worth checking elsewhere: any `lean_box_uint32(0)` / `box_uint32(0)` used as a
constructor-0 scalar. `grep -rn "box_uint32(0)" src/runtime` found only this site on v4.33.1.

**Versions:** Lean 4.33.1 (819816b2e0a3bf405af45ae5c7af2491d8f5bee6), Emscripten 5.0.6, macOS 14.6 host.

## 2. Related, already tracked upstream

- **#6817 / PR #13298** — `io.cpp` references libuv symbols under `LEAN_EMSCRIPTEN`. On v4.33.1 the
  set is larger than the PR covers: `uv_strerror`, `uv_os_tmpdir`, `uv_fs_mkstemp`, `uv_fs_mkdtemp`,
  `uv_fs_stat`, `uv_fs_lstat`, `uv_fs_link`, `uv_fs_unlink`, `uv_fs_req_cleanup` (metadata, hard
  links and unlink moved to libuv after the PR was written). Worth a comment on the PR if it is
  still open. Our workaround: `../c/uv-stubs.c` defines them with the `uv.h` prototypes and returns
  `UV_ENOSYS`.
- **#14973** (2026-09-08) — `lean_uv_event_loop_alive` and `lean_uv_os_get_group` Emscripten stubs
  don't match their declarations. Confirmed; the two-line fix is in our patch.

## 3. Possible follow-up: arity mismatch on `lean_io_create_tempfile` / `lean_io_create_tempdir`

After the zero-cost `BaseIO` change (#10625), `Init/System/IO.c` declares and calls
`lean_io_create_tempfile()` / `lean_io_create_tempdir()` with no arguments, while `io.cpp` defines
them as taking a `lean_object * w`. Native linkers don't check signatures; `wasm-ld` warns:

```
wasm-ld: warning: function signature mismatch: lean_io_create_tempfile
>>> defined as () -> i32 in libInit.a(IO.o)
>>> defined as (i32) -> i32 in libleanrt.a(io.o)
```

and inserts a trapping thunk, so calling `IO.FS.createTempFile` on wasm would trap. Not exercised
by us. Likely fix: drop the unused parameter in `io.cpp` (check other `IO` externs for the same drift).

## 4. Build notes that may help a future "wasm32 CI" discussion

- The runtime (34 files) compiles cleanly with `em++ -std=c++20 -DLEAN_EMSCRIPTEN` after the
  #14973 fix, without `-pthread`, with `MULTI_THREAD=OFF`.
- `Init` C emitted by the host `lean --c` matches the checked-in `stage0/stdlib/Init/*.c` for
  629 of 631 files at v4.33.1.
- `-sSAFE_HEAP=1` reports an unaligned 64-bit load in `Init.Data.ByteArray.Extra`'s initializer
  (`lean_ctor_get_uint64` at a 4-byte-aligned scalar offset); tolerated by wasm, but a
  `LEAN_CASSERT`-style alignment story for 32-bit scalar areas may be worth raising.

## 5. Lean itself on wasm32 (v4.34.1): findings from building the compiler and server

Building the whole compiler — `lean` and the language server's file worker — for wasm32 with Emscripten
(`scripts/build-lean-wasm-compiler.sh`, patch `lean-compiler-emscripten.patch`) turned up more of the same
kind, each one silent on 64-bit native targets:

- **World-token arity drift beyond §3.** `lean_run_init`, `lean_compacted_region_read`/`_free`,
  `mk_compacted_region` (via `lean_save_module_data`) and the tempfile/tempdir pair still take the `object *`
  world argument that `@[extern]` IO functions stopped receiving with #10625. On wasm32 the call traps.
- **`lean_internal_get_default_max_heartbeat` / `_max_memory`** are declared `(_ : Unit) → Nat` in
  `Lean/Shell.lean`, so the emitted call passes the unit, but the C++ definitions take no arguments.
- **Std.Async stubs missing:** `lean_uv_tcp_wait_readable`, `lean_uv_tcp_cancel_recv`, `lean_uv_tcp_try_accept`,
  `lean_uv_udp_wait_readable`, `lean_uv_udp_cancel_recv` have no `LEAN_EMSCRIPTEN` branch (undefined at link).
- **`get_loaded_libs` uses `dl_iterate_phdr`**, which Emscripten lacks; a static wasm link is one module whose
  function pointers are table indices from 0.
- **The interpreter needs `dlsym` over the executable** (`lookup_symbol_in_cur_exe`), which a static wasm link
  does not provide. We generate a name-hash → address table at build time; an upstream answer could be an
  opt-in table emitted by the build, or preferring the interpreter wholesale on such targets.
- **Emitted C must be compiled with `-DLEAN_EMSCRIPTEN`** (§1's neighbor): `LEAN_SCALAR_PTR_LITERAL` splits
  64-bit scalars in static objects only under that define. The define is in Lean's own CMake, but anyone
  compiling `lean --c` output for wasm32 by hand (as `lake` would for a wasm target) gets truncated Name hashes
  and a Lean that fails at initialization ("unknown parser category"). Keying it on `__EMSCRIPTEN__` or
  `UINTPTR_MAX` in lean.h would remove the trap.
- **`lean_main`'s NODEFS mounts use `EM_ASM`**, which under `-sPROXY_TO_PTHREAD` runs on the pthread, whose
  filesystem is the main thread's; the mounts must be `MAIN_THREAD_EM_ASM`.
- **`IO.appPath` reads `__filename`**, which only exists under Node; in a web worker there is no executable.
  We let the host name a path (`Module.leanAppPath`).
- **`LEAN_NUM_THREADS` is ignored under `LEAN_EMSCRIPTEN`.** In a browser each thread is a web worker; one
  started beyond Emscripten's pre-created pool only becomes ready when the main thread yields, and Lean's task
  manager starts a thread whenever a pooled task waits on another — so a busy server stalls. The host has to
  be able to cap it (we honor the variable and pre-create 32 workers).
- **Oleans are pointer-size specific,** so a wasm32 Lean needs the library compiled by a wasm32 Lean; the
  release's `linux_wasm32` build ships none for its own use in a browser. Init at v4.34.1 is 649 modules, whose
  `.olean.private` parts (needed by `import` of an ordinary file) are most of the ~114 MB compressed.
