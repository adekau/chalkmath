#!/usr/bin/env python3
"""Compile Lean's own library to 32-bit .olean files with the wasm build of Lean, under Node.

An .olean is a memory image with pointer-sized fields, so the 64-bit oleans elan ships cannot be
loaded by a wasm32 Lean; its library has to be compiled by the wasm build itself. This is how Lean's
own Emscripten recipe produces them (`lean_main` in `src/util/shell.cpp`: "This mode is used to
compile 32-bit oleans").

  usage: lean-wasm-oleans.py LEAN_JS SRC_ROOT OUT_LIB JOBS ROOT_MODULE...
         lean-wasm-oleans.py --closure SRC_ROOT ROOT_MODULE...    (just list the modules)

Compiles every module the ROOT_MODULEs import, transitively, in dependency order and JOBS at a time,
into OUT_LIB (mirroring the toolchain's lib/lean). A module whose .olean is newer than its source
and its imports' .oleans is skipped, so an interrupted run resumes. Options mirror the core build
(`src/CMakeLists.txt`, `src/lakefile.toml.in`).
"""
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, FIRST_COMPLETED, wait

IMPORT = re.compile(r'^\s*(?:(?:public|private|meta|all)\s+)*import\s+(?:(?:public|private|meta|all)\s+)*(.+)$', re.M)
OPTS = ['-Dinterpreter.prefer_native=false', '-Dlinter.coreInternal=true']


def imports_of(src: str) -> list[str]:
    text = re.sub(r'/-.*?-/', '', open(src, encoding='utf8').read(), flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    header = []
    for line in text.split('\n'):
        s = line.strip()
        if not s or s in ('module', 'prelude'):
            continue
        m = IMPORT.match(line)
        if not m:
            break
        header += [t for t in m.group(1).split() if t not in ('all', 'public', 'private', 'meta')]
    return header


def closure(src_root: str, roots: list[str]) -> dict[str, list[str]]:
    """Every module the roots import, transitively, with its direct imports."""
    deps: dict[str, list[str]] = {}
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in deps:
            continue
        deps[m] = imports_of(os.path.join(src_root, *m.split('.')) + '.lean')
        stack += deps[m]
    return deps


def main() -> None:
    if sys.argv[1] == '--closure':   # lean-wasm-oleans.py --closure SRC_ROOT ROOT_MODULE...: list the modules
        print('\n'.join(sorted(closure(sys.argv[2], sys.argv[3:]))))
        return
    lean_js, src_root, out_lib, jobs, *roots = sys.argv[1:]
    jobs = int(jobs)
    path = lambda m, ext: os.path.join(out_lib, *m.split('.')) + ext
    src_of = lambda m: os.path.join(src_root, *m.split('.')) + '.lean'
    deps = closure(src_root, roots)

    def stale(m: str) -> bool:
        o = path(m, '.olean')
        if not os.path.exists(o):
            return True
        t = os.path.getmtime(o)
        return os.path.getmtime(src_of(m)) > t or any(os.path.getmtime(path(d, '.olean')) > t for d in deps[m])

    env = dict(os.environ, LEAN_PATH=out_lib)
    done: set[str] = set()
    failed: list[str] = []
    running = {}
    started = time.time()
    total = len(deps)

    def compile_one(m: str) -> tuple[str, int, str, float]:
        os.makedirs(os.path.dirname(path(m, '')), exist_ok=True)
        t0 = time.time()
        p = subprocess.run(['node', '--stack-size=65500', lean_js, *OPTS, '-R', src_root,
                            '-o', path(m, '.olean'), '-i', path(m, '.ilean'), src_of(m)],
                           env=env, capture_output=True, text=True)
        return m, p.returncode, (p.stdout + p.stderr)[-4000:], time.time() - t0

    with ThreadPoolExecutor(jobs) as pool:
        while len(done) + len(failed) < total:
            ready = [m for m in deps if m not in done and m not in running and m not in failed
                     and all(d in done for d in deps[m])]
            for m in ready:
                if not stale(m):
                    done.add(m)
                    continue
                if len(running) < jobs:
                    running[m] = pool.submit(compile_one, m)
            if not running:
                if len(done) + len(failed) < total and not any(
                        all(d in done for d in deps[m]) for m in deps if m not in done and m not in failed):
                    break  # the rest depend on a failure
                continue
            finished, _ = wait(running.values(), return_when=FIRST_COMPLETED)
            for f in finished:
                m, rc, out, dt = f.result()
                del running[m]
                if rc == 0:
                    done.add(m)
                    print(f'[{len(done)}/{total}] {m} ({dt:.1f}s)', flush=True)
                else:
                    failed.append(m)
                    print(f'FAILED {m} (exit {rc}):\n{out}', flush=True)
    print(f'{len(done)}/{total} modules in {time.time() - started:.0f}s; failed: {failed or "none"}')
    sys.exit(1 if failed or len(done) < total else 0)


if __name__ == '__main__':
    main()
