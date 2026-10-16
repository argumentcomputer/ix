module
public import Ix.CompileDriver

public section

/-!
# The Lean compile drivers' options, from the CLI's environment

The driver (`Ix.CompileM.compileEnvFold`, and the pipeline above it)
reads no environment variable and no `/proc` file; it takes
`Ix.CompileM.DriverOptions`. `ix compile-lean` and `ix validate-lean` build
the options here:
- `IX_SHARING_LIMITS` (set by `--sharing-limits`, or directly): the sharing
  construction's limits;
- `IX_COMPILE_DBG`: phase timings and the per-wave trace.

Under `IX_COMPILE_DBG` the pipeline prints the process's resident set size
after the compile phase, read here.
-/

namespace Ix.Cli

/-- The process's resident set size, from `/proc/self/status` (`?` where it
    cannot be read). -/
def residentSetSize : IO String := do
  try
    let status ← IO.FS.readFile "/proc/self/status"
    let rss := (status.splitOn "\n").findSome? fun l =>
      if l.startsWith "VmRSS" then (l.splitOn ":")[1]? else none
    return (rss.getD "?").trimAscii.toString
  catch _ => return "?"

/-- The drivers' options from the environment; `dbg` forces the debug
    traces on. An invalid `IX_SHARING_LIMITS` is an error naming it. -/
def driverOptionsFromEnv (dbg : Bool := false) :
    IO (Except String Ix.CompileM.DriverOptions) := do
  match ← Ix.CompileM.compilerSharingLimitsFromEnv with
  | .error e => return .error e
  | .ok sharingLimits =>
    let dbg := dbg || (← IO.getEnv "IX_COMPILE_DBG").isSome
    return .ok { sharingLimits, dbg
                 memory := if dbg then some residentSetSize else none }

end Ix.Cli

end
