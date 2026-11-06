import Benchmarks.Kernel.CheckIxe

/-! # An environment check run to completion under the watchdog (untrusted tooling)

`kernel-check-ixe --guarded [--binary <path>] [--load stream|eager]
[--jobs <n>] <input.ixe> <output.jsonl> [limit]`: when one constant's check
exceeds the driver's watchdog limits (`CHECK_IXE_WATCH_MS`,
`CHECK_IXE_WATCH_MB`), the environment check exits with code 3 and records
the constant's address in `<output>.runaway`; this reruns it, in a fresh
process, with every recorded address skipped (`CHECK_IXE_SKIP`), until it
exits with another code, which is the exit code. The arguments after
`--binary` are the environment check's. `--binary` runs another build of the
driver with the same contract (an earlier revision, for comparison); the
default is this executable. Nothing caps a run's memory: the driver's
watchdog bounds one constant's RSS, not the whole check, so wrap the command
in `systemd-run --user --scope -p MemoryMax=<GB>G` to cap it. -/

namespace Benchmarks.Kernel.CheckIxeGuarded

structure Options where
  binary : Option String := none
  rest : Array String := #[]
  output : String := ""

def usage : String :=
  "usage: kernel-check-ixe --guarded [--binary <path>] \
   [--load stream|eager] [--jobs <n>] <input.ixe> <output.jsonl> [limit]"

def parseArgs : List String → Options → Option Options
  | "--binary" :: b :: rest, o => parseArgs rest { o with binary := some b }
  | rest, o => do
    let check ← Benchmarks.Kernel.CheckIxe.parseArgs rest
    some { o with rest := rest.toArray, output := check.output.toString }

def run (args : List String) : IO UInt32 := do
  let some o := parseArgs args {} | IO.eprintln usage; return 2
  let binary ← match o.binary with
    | some b => pure b
    | none => do pure (← IO.appPath).toString
  let runaway : System.FilePath := o.output ++ ".runaway"
  if ← runaway.pathExists then IO.FS.removeFile runaway
  repeat
    let recorded ← if ← runaway.pathExists then IO.FS.lines runaway else pure #[]
    let env := #[("CHECK_IXE_SKIP", some (",".intercalate recorded.toList))]
    let child ← IO.Process.spawn { cmd := binary, args := o.rest, env }
    let code ← child.wait
    if code != 3 then return code
    let skipped ← if ← runaway.pathExists then IO.FS.lines runaway else pure #[]
    IO.eprintln s!"check-ixe-guarded: restarting with {skipped.size} skipped"
  return 0

end Benchmarks.Kernel.CheckIxeGuarded
