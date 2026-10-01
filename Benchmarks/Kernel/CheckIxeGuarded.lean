/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Watchdog

/-! # An environment check run to completion under the watchdog (untrusted tooling)

`kernel-check-ixe --guarded [--memory-max <GB>] [--binary <path>] <input.ixe>
<output.jsonl> [args...]`: when one constant's check exceeds the driver's
watchdog limits (`CHECK_IXE_WATCH_MS`, `CHECK_IXE_WATCH_MB`), the environment
check exits with code 3 and records the constant's address in
`<output>.runaway`; this reruns it, in a fresh process, with every recorded
address skipped (`CHECK_IXE_SKIP`), until it exits with another code, which
is the exit code. `--binary` runs another driver with the same contract
(`kernel-check-ixe-opt`); the default is this executable. With
`--memory-max`, every run is a memory-capped cgroup scope of its own
(`Ix.Watchdog.run`: `MemoryMax`, no swap, the whole scope killed at the cap,
exit code 137).

Until 2026-10-01 this was `scripts/check-ixe-guarded.sh`, run inside a
`systemd-run --user --scope -p MemoryMax=…` line. -/

namespace Benchmarks.Kernel.CheckIxeGuarded

structure Options where
  binary : Option String := none
  memoryMaxGb : Option Nat := none
  rest : Array String := #[]

def usage : String :=
  "usage: kernel-check-ixe --guarded [--memory-max <GB>] [--binary <path>] \
   <input.ixe> <output.jsonl> [limit]"

def parseArgs : List String → Options → Option Options
  | "--binary" :: b :: rest, o => parseArgs rest { o with binary := some b }
  | "--memory-max" :: g :: rest, o => g.toNat?.bind fun n => parseArgs rest { o with memoryMaxGb := some n }
  | rest, o => if rest.length < 2 then none else some { o with rest := rest.toArray }

def run (args : List String) : IO UInt32 := do
  let some o := parseArgs args {} | IO.eprintln usage; return 2
  let binary ← match o.binary with
    | some b => pure b
    | none => do pure (← IO.appPath).toString
  let output := o.rest[1]!
  let runaway : System.FilePath := output ++ ".runaway"
  if ← runaway.pathExists then IO.FS.removeFile runaway
  repeat
    let recorded ← if ← runaway.pathExists then IO.FS.lines runaway else pure #[]
    let env := #[("CHECK_IXE_SKIP", some (",".intercalate recorded.toList))]
    let code ← match o.memoryMaxGb with
      | some gb => Ix.Watchdog.run gb binary o.rest (env := env)
      | none => do
        let child ← IO.Process.spawn { cmd := binary, args := o.rest, env }
        child.wait
    if code != 3 then return code
    let skipped ← if ← runaway.pathExists then IO.FS.lines runaway else pure #[]
    IO.eprintln s!"check-ixe-guarded: restarting with {skipped.size} skipped"
  return 0

end Benchmarks.Kernel.CheckIxeGuarded
