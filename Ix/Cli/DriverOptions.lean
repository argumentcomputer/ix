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
- `IX_COMPILE_DBG`: phase timings and the per-wave trace;
- `IX_PASS3_CHECK_PLANS=1`: Pass 3's plan-table check
  (`DriverOptions.checkPlans`): every clique plan and row set a table
  supplies is recomputed and compared, and a difference fails the compile;
- `IX_AUXGEN_IXC` (AuxGen's measurement modes, never needed otherwise;
  `Ix.CompileM.AuxIxcOptions`): `shadow`, `fallback`, `failClosed` or
  `fallbackEager` runs the wave fold with its aux tails asking IxC in that mode
  (production's is `fallback`), each tail tracing its counts; `measure` times the Source
  service's work alone and compiles nothing: the pipeline prints the
  measurement and returns an error ("nothing compiled"), so `ix compile-lean`
  exits 1 by design. A further `,asks=inductive` makes the service ask for
  every block that holds an inductive, `,asks=below` only for the blocks with
  a Type-level `.below` (M2b's production); production asks also for the
  blocks the recursor generator can ask past the fast paths
  (`,asks=recursors`, `Ix.AuxGen.Ixc.recursorsMayAsk`; AuxGen M4b). The
  recursor generator and the elimination decision ask IxC as in production;
  `,rec=off` leaves them on `Ix.Tc` (M3's production).

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

/-- AuxGen's measurement mode from `IX_AUXGEN_IXC` (see the module
    docstring); an unknown word is an error naming it. -/
def auxIxcOptionsOf (value : String) : Except String Ix.CompileM.AuxIxcOptions := do
  let words := (value.splitOn ",").map (·.trimAscii.toString)
  let mut opts : Ix.CompileM.AuxIxcOptions := { trace := true, recursors := true }
  for (w, i) in words.zipIdx do
    if i == 0 then
      if w == "measure" then opts := { opts with measureOnly := true }
      else match Ix.AuxGen.IxcMode.ofString? w with
        | some mode => opts := { opts with mode }
        | none => throw s!"IX_AUXGEN_IXC: unknown mode '{w}' (shadow, fallback, failClosed, fallbackEager, measure)"
    else if w == "asks=below" then opts := { opts with asks := .below }
    else if w == "asks=inductive" then opts := { opts with asks := .inductive }
    else if w == "asks=recursors" then opts := { opts with asks := .recursors }
    else if w == "rec=off" then opts := { opts with recursors := false }
    else throw s!"IX_AUXGEN_IXC: unknown option '{w}' (asks=below, asks=inductive, asks=recursors, rec=off)"
  return opts

/-- The drivers' options from the environment; `dbg` forces the debug
    traces on. An invalid `IX_SHARING_LIMITS` or `IX_AUXGEN_IXC` is an error
    naming it. -/
def driverOptionsFromEnv (dbg : Bool := false) :
    IO (Except String Ix.CompileM.DriverOptions) := do
  match ← Ix.CompileM.compilerSharingLimitsFromEnv with
  | .error e => return .error e
  | .ok sharingLimits =>
    let dbg := dbg || (← IO.getEnv "IX_COMPILE_DBG").isSome
    let auxIxc ← match ← IO.getEnv "IX_AUXGEN_IXC" with
      | none => pure none
      | some v => match auxIxcOptionsOf v with
        | .ok o => pure (some o)
        | .error e => return .error e
    let checkPlans := (← IO.getEnv "IX_PASS3_CHECK_PLANS") == some "1"
    return .ok { sharingLimits, dbg, auxIxc, checkPlans
                 memory := if dbg then some residentSetSize else none }

end Ix.Cli

end
