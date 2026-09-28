import Lean.Server.Watchdog
/-! Prints the reply Lean's watchdog gives to `initialize` (`Lean.Server.Watchdog.initAndRunWatchdog`),
for the in-browser watchdog to give instead. Run by scripts/build-lean-wasm-compiler.sh. -/
open Lean Lsp

def initializeResult : InitializeResult where
  capabilities := Server.Watchdog.mkLeanServerCapabilities
  serverInfo? := some { name := "Lean 4 Server", version? := "0.3.0" }

#eval IO.println (toJson initializeResult).compress
