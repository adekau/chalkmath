import Lean.Server.FileWorker
/-!
# Lean's file worker, in a browser

`lean --worker` is the process Lean's language server starts for each open file: it reads LSP messages
on stdin and writes them on stdout, and it is what answers the Lean 4 extension's requests (diagnostics,
goals, hovers, the infoview's RPC). A web page cannot start processes, so this program *is* the worker:
the web worker hosting the wasm module (`packages/engine-host/src/worker-lean-server.ts`) plays Lean's
watchdog, and stdin/stdout are a shared-memory queue (`leanweb.c`) instead of pipes.

The olean search path is set here rather than from `IO.appDir`, which has no meaning in a browser: the
host mounts the 32-bit library at `/lib/lean`, or wherever `LEAN_PATH` says. For the same reason `LAKE`
points at a path that does not exist, so the worker never looks for Lake next to the application.
-/
open Lean

namespace LeanWeb

/-- Blocks until the host has queued at least one byte, then returns up to `n` of them. -/
@[extern "leanweb_read"] opaque read (n : USize) : IO ByteArray
/-- Hands bytes to the host: `fd` 1 is the LSP stream, 2 is the log. -/
@[extern "leanweb_write"] opaque write (fd : UInt8) (b : @& ByteArray) : IO Unit
/-- Sets an environment variable (Lean's `IO` has no setter). -/
@[extern "leanweb_setenv"] opaque setEnv (name value : @& String) : IO Unit

/-- stdin over the queue, with a buffer so `getLine` (LSP headers) and `read` (bodies) can share it. -/
def stdin : IO IO.FS.Stream := do
  let pending ← IO.mkRef ByteArray.empty
  let fill (need : Nat) : IO Unit := do
    while (← pending.get).size < need do
      let more ← read (USize.ofNat (max 65536 (need - (← pending.get).size)))
      pending.modify (· ++ more)
  let take (n : Nat) : IO ByteArray := do
    let buf ← pending.get
    pending.set (buf.extract n buf.size)
    return buf.extract 0 n
  return {
    flush := pure ()
    -- the LSP reader asks for a message body by its exact length, so wait for all of it
    read := fun n => do fill n.toNat; take n.toNat
    write := fun _ => pure ()
    getLine := do
      let mut i := 0
      repeat
        let buf ← pending.get
        let mut j := i
        while j < buf.size && buf[j]! != 10 do
          j := j + 1
        if j < buf.size then
          return String.fromUTF8! (← take (j + 1))
        i := buf.size
        fill (buf.size + 1)
      return ""
    putStr := fun _ => pure ()
    isTty := pure false
  }

def out (fd : UInt8) : IO.FS.Stream where
  flush := pure ()
  read := fun _ => pure .empty
  write := write fd
  getLine := pure ""
  putStr := fun s => write fd s.toUTF8
  isTty := pure false

end LeanWeb

def main (_args : List String) : IO UInt32 := do
  let libs := (← IO.getEnv "LEAN_PATH").map System.SearchPath.parse |>.getD ["/lib/lean"]
  searchPathRef.set libs
  -- No Lake in a browser: `setupFile` finds its binary by `LAKE` before `IO.appDir` (which has no
  -- meaning here) and treats a missing binary as a file without a lakefile, on the plain search path.
  LeanWeb.setEnv "LAKE" "/lake-is-not-available-in-the-browser"
  let _ ← IO.setStdin (← LeanWeb.stdin)
  let _ ← IO.setStdout (LeanWeb.out 1)
  let _ ← IO.setStderr (LeanWeb.out 2)
  Server.FileWorker.workerMain {}
