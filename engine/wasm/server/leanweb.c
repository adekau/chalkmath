/*
 * stdin/stdout of LeanWorker.lean, for a threaded Emscripten build.
 *
 * Lean's `main` runs on a pthread (PROXY_TO_PTHREAD); the web worker's own JS thread receives the
 * page's messages. Filesystem calls from a pthread are proxied to that JS thread, so a blocking read of
 * the real stdin there would wait on the very thread that has to deliver the input. Instead:
 *
 *   input   a ring buffer in wasm memory. The host writes LSP bytes at `leanweb_in_buf()` and advances
 *           the write counter with Atomics.store + Atomics.notify; `leanweb_read` waits on that counter
 *           with a futex, on the Lean thread, without involving the JS thread.
 *   output  `leanweb_write` copies the bytes and queues them to the JS thread, which frees the copy and
 *           calls `Module.leanwebOut(fd, bytes)`. Queued calls run in order, so the LSP stream stays
 *           framed.
 *
 * The counters are free-running uint32 byte counts; the ring holds `w - r` unread bytes.
 */
#include <lean/lean.h>
#include <emscripten.h>
#include <emscripten/threading.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define LEANWEB_IN_CAP (1u << 22)   /* 4 MiB: a whole file's text fits several times over */

static uint8_t in_buf[LEANWEB_IN_CAP];
static _Atomic uint32_t in_w, in_r;

EMSCRIPTEN_KEEPALIVE uint8_t * leanweb_in_buf(void) { return in_buf; }
EMSCRIPTEN_KEEPALIVE uint32_t leanweb_in_cap(void) { return LEANWEB_IN_CAP; }
EMSCRIPTEN_KEEPALIVE _Atomic uint32_t * leanweb_in_w(void) { return &in_w; }
EMSCRIPTEN_KEEPALIVE _Atomic uint32_t * leanweb_in_r(void) { return &in_r; }

/* LeanWeb.read : USize → IO ByteArray */
LEAN_EXPORT lean_obj_res leanweb_read(size_t n) {
    uint32_t r = atomic_load(&in_r), w;
    while ((w = atomic_load(&in_w)) == r)
        emscripten_futex_wait((void *)&in_w, w, INFINITY);
    uint32_t avail = w - r;
    size_t k = n < avail ? n : avail;
    lean_object * arr = lean_alloc_sarray(1, k, k);
    uint8_t * dst = lean_sarray_cptr(arr);
    for (size_t i = 0; i < k; i++) dst[i] = in_buf[(r + i) % LEANWEB_IN_CAP];
    atomic_store(&in_r, r + (uint32_t)k);
    return lean_io_result_mk_ok(arr);
}

/* LeanWeb.write : UInt8 → @& ByteArray → IO Unit */
LEAN_EXPORT lean_obj_res leanweb_write(uint8_t fd, b_lean_obj_arg bytes) {
    size_t len = lean_sarray_size(bytes);
    uint8_t * copy = malloc(len ? len : 1);
    memcpy(copy, lean_sarray_cptr(bytes), len);
    /* HEAPU8 inside EM_ASM is the module's current view, valid after memory growth */
    MAIN_THREAD_ASYNC_EM_ASM({ const b = HEAPU8.slice($1, $1 + $2); _free($1); Module.leanwebOut($0, b); }, fd, copy, len);
    return lean_io_result_mk_ok(lean_box(0));
}

/* LeanWeb.setEnv : @& String → @& String → IO Unit (Lean's IO has no setter; libc's environment is shared by
   every thread of the module) */
LEAN_EXPORT lean_obj_res leanweb_setenv(b_lean_obj_arg name, b_lean_obj_arg value) {
    setenv(lean_string_cstr(name), lean_string_cstr(value), 1);
    return lean_io_result_mk_ok(lean_box(0));
}
