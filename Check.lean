/-
  `lake exe check`: thin Cli shim around `Ix.Cli.CheckCmd.runCheckCmd`.

  The Aiur kernel typechecking logic lives in `Ix/Cli/CheckCmd.lean`
  and is the implementation behind `ix check`. This binary exists so
  that day-to-day Lean iteration can rebuild a small exe (`lake exe
  check`) instead of the full `ix` binary while still hitting the
  identical code path.

  All flags + behavior match `ix check` 1:1. See its help for details.
-/
import Cli
import Ix.Cli.CheckCmd

open Cli

def kernelCmd : Cli.Cmd := `[Cli|
  kernel VIA Ix.Cli.CheckCmd.runCheckCmd;
  "Typecheck Lean / `.ixe` constants through the IxVM Aiur kernel"

  FLAGS:
    interp;                 "Use the Aiur interpreter (richer per-execution error diagnostics) instead of the compiled bytecode runner."
    "keep-going";           "Continue past failures and report them at the end instead of halting on the first."
    "ixe"       : String;   "Path to a serialized `.ixe` env. When set, the binary reads the env from disk instead of using the compiled-in Lean env."
    "claim"     : String;   "32-byte hex address of a persisted `Ix.Claim` in `~/.ix/store/`. When set, runs the `verify_claim` entrypoint once over the claim's witness against the `--ixe` env (single execution, skips per-const iteration)."
    "stats-out" : String;   "Redirect the per-circuit statistics dump to this file (only used when exactly one constant is targeted)."

  ARGS:
    ...names : String; "Fully-qualified Lean.Name(s) to check. With none, iterate every named constant in the env (sorted)."
]

def main (args : List String) : IO UInt32 :=
  kernelCmd.validate args
