/*
 * The libuv filesystem calls Lean's runtime makes under LEAN_EMSCRIPTEN, on POSIX.
 *
 * io.cpp uses libuv for file metadata, hard links, unlink and temp files even in an Emscripten build
 * (leanprover/lean4#6817), synchronously (no loop, no callback). The engine never reaches them, so its
 * link stubs them out (engine/c/uv-stubs.c); Lean itself does: `import` checks that oleans exist, the
 * frontend reads metadata. This file implements them on the POSIX calls Emscripten's libc provides
 * (its virtual filesystem in a browser, the host's under Node), with libuv's conventions: 0 or a
 * negative errno, the stat in `req->statbuf`, the created path in `req->path`, the fd in `req->result`.
 * Linked into the compiler build (scripts/build-lean-wasm-compiler.sh) instead of engine/c/uv-stubs.c.
 */
#include <uv.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

const char * uv_strerror(int err) { return strerror(-err); }

int uv_os_tmpdir(char * buffer, size_t * size) {
    const char * dir = getenv("TMPDIR");
    if (!dir || !*dir) dir = "/tmp";
    size_t n = strlen(dir);
    while (n > 1 && dir[n - 1] == '/') n--;
    if (n + 1 > *size) { *size = n + 1; return UV_ENOBUFS; }
    memcpy(buffer, dir, n);
    buffer[n] = 0;
    *size = n;
    return 0;
}

static void req_init(uv_fs_t * req, uv_fs_type type) {
    memset(req, 0, sizeof(*req));
    req->fs_type = type;
}

static int finish(uv_fs_t * req, int r) {
    req->result = r < 0 ? -errno : r;
    return r < 0 ? -errno : 0;
}

static void to_uv_stat(struct stat const * st, uv_stat_t * out) {
    memset(out, 0, sizeof(*out));
    out->st_dev = st->st_dev;
    out->st_mode = st->st_mode;
    out->st_nlink = st->st_nlink;
    out->st_uid = st->st_uid;
    out->st_gid = st->st_gid;
    out->st_rdev = st->st_rdev;
    out->st_ino = st->st_ino;
    out->st_size = st->st_size;
    out->st_blksize = st->st_blksize;
    out->st_blocks = st->st_blocks;
    out->st_atim.tv_sec = st->st_atim.tv_sec;  out->st_atim.tv_nsec = st->st_atim.tv_nsec;
    out->st_mtim.tv_sec = st->st_mtim.tv_sec;  out->st_mtim.tv_nsec = st->st_mtim.tv_nsec;
    out->st_ctim.tv_sec = st->st_ctim.tv_sec;  out->st_ctim.tv_nsec = st->st_ctim.tv_nsec;
    out->st_birthtim = out->st_ctim;
}

static int do_stat(uv_fs_t * req, const char * path, int follow) {
    struct stat st;
    int r = follow ? stat(path, &st) : lstat(path, &st);
    if (r == 0) { to_uv_stat(&st, &req->statbuf); req->ptr = &req->statbuf; }
    return finish(req, r);
}

int uv_fs_stat(uv_loop_t * loop, uv_fs_t * req, const char * path, uv_fs_cb cb) {
    (void)loop; (void)cb; req_init(req, UV_FS_STAT); return do_stat(req, path, 1);
}

int uv_fs_lstat(uv_loop_t * loop, uv_fs_t * req, const char * path, uv_fs_cb cb) {
    (void)loop; (void)cb; req_init(req, UV_FS_LSTAT); return do_stat(req, path, 0);
}

int uv_fs_link(uv_loop_t * loop, uv_fs_t * req, const char * path, const char * new_path, uv_fs_cb cb) {
    (void)loop; (void)cb; req_init(req, UV_FS_LINK); return finish(req, link(path, new_path));
}

int uv_fs_unlink(uv_loop_t * loop, uv_fs_t * req, const char * path, uv_fs_cb cb) {
    (void)loop; (void)cb; req_init(req, UV_FS_UNLINK); return finish(req, unlink(path));
}

/* The template ends in XXXXXX (io.cpp: "tmp.XXXXXXXX"); the created path goes to req->path. */
int uv_fs_mkstemp(uv_loop_t * loop, uv_fs_t * req, const char * tpl, uv_fs_cb cb) {
    (void)loop; (void)cb; req_init(req, UV_FS_MKSTEMP);
    char * path = strdup(tpl);
    if (!path) return finish(req, (errno = ENOMEM, -1));
    int fd = mkstemp(path);
    if (fd < 0) { free(path); return finish(req, -1); }
    req->path = path;
    return finish(req, fd);
}

int uv_fs_mkdtemp(uv_loop_t * loop, uv_fs_t * req, const char * tpl, uv_fs_cb cb) {
    (void)loop; (void)cb; req_init(req, UV_FS_MKDTEMP);
    char * path = strdup(tpl);
    if (!path) return finish(req, (errno = ENOMEM, -1));
    if (!mkdtemp(path)) { free(path); return finish(req, -1); }
    req->path = path;
    return finish(req, 0);
}

void uv_fs_req_cleanup(uv_fs_t * req) {
    if (req->fs_type == UV_FS_MKSTEMP || req->fs_type == UV_FS_MKDTEMP) free((void *)req->path);
    req->path = NULL;
    req->ptr = NULL;
}
