module
public import Cli
public import Ix.Common
public import Ix.CompileDriver
import Std.Internal.UV.System

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

/-- `--sharing-limits SPEC`: validate the override (the format of
`Ix.Sharing.Exact.Limits.withOverrides`, which also accepts the Rust limit
keys) and publish it through `IX_SHARING_LIMITS`, which both compilers read.
Returns the parse error, if any. -/
def applySharingLimitsFlag (p : Cli.Parsed) : IO (Option String) := do
  let some flag := p.flag? "sharing-limits" | return none
  let spec := flag.as! String
  match Ix.CompileM.compilerSharingLimits.withOverrides spec with
  | .error e => return some s!"--sharing-limits: {e}"
  | .ok _ =>
    Std.Internal.UV.System.osSetenv Ix.CompileM.sharingLimitsEnvVar spec
    return none

/-- The certified compiler runs at the default sharing limits: `Ix.Cert.compileReport`,
the function its correctness theorem is about, fixes them, and other limits can
change which constants compile. A valid override (`--sharing-limits`, or a nonempty
`IX_SHARING_LIMITS`) is therefore refused there, with the reason; the uncertified
compilers (`--streamed`, `--rust`) take one. An invalid override is reported by its
parser first. -/
def certifiedLimitsRefusal (p : Cli.Parsed) : IO (Option String) := do
  let inherited := (← IO.getEnv Ix.CompileM.sharingLimitsEnvVar).any (!·.trimAscii.isEmpty)
  unless (p.flag? "sharing-limits").isSome || inherited do return none
  return some "the certified compiler runs at the default sharing limits, which its \
correctness theorem fixes; --sharing-limits and IX_SHARING_LIMITS apply only to the \
uncertified compilers (--streamed, --rust)"

/-- Failures listed root causes first: a constant that failed only because a
    dependency is missing is a cascade, listed after the ones that name the
    cause (a refusal's message must be visible in the bounded listing). -/
def rootCausesFirst {α : Type} (xs : List (α × String)) : List (α × String) :=
  let cascade (e : String) := e.startsWith "missingConstant" || e.startsWith "missing constant"
  xs.filter (!cascade ·.2) ++ xs.filter (cascade ·.2)

/-- The canonical Merkle root of `env`'s stored constants, formatted as a hex string. -/
def rootOf (env : Ixon.Env) : String :=
  toString ((Ix.Merkle.merkleRootCanonical (env.consts.toArray.map (·.1))).getD Ix.Merkle.zeroAddress)

/-- Initial `CompileEnvStatus` for `original` and `failures` prior to finalization and serialization. -/
def statusOf (original : Ixon.Env) (failures : Std.HashMap Ix.Name String) :
    Ix.CompileM.CompileEnvStatus :=
  let ungrounded := (failures.toArray.map fun (n, r) => (n.pretty, r)).qsort (fun a b => a.1 < b.1)
  { root := rootOf original, ungrounded, nonCanonical := #[], bytes := 0, named := 0, uniqueAnon := 0 }

end Ix.Cli

end
