import IxAIVerify.Aiur
import IxAIVerify.Trajectory

/-!
# Command-line helpers shared by `ixai` and `ixai-verify`

Flag lookup, the scratch directory of a verification, how a route result is printed and exits, and
the trajectory check both executables offer (`ixai check`, `ixai-verify trajectory`).
-/

namespace IxAIVerify.Cli

open IxAI IxAIVerify

/-- The value after the first occurrence of `name`. -/
def flag (args : List String) (name : String) : Option String :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some v
  | _ => none

/-- The values after every occurrence of `name`, in order. -/
def flags (args : List String) (name : String) : List String :=
  match args with
  | k :: tl => (if k == name then tl.take 1 else []) ++ flags tl name
  | [] => []

/-- The scratch directory base: `IXAI_VERIFY_WORK`, default `/tmp`. -/
def workBase : IO System.FilePath := do
  return System.FilePath.mk ((← IO.getEnv "IXAI_VERIFY_WORK").getD "/tmp")

/-- Run `k` in a fresh scratch directory `ixai-verify-N` under `workBase`, removed afterwards. -/
def withWorkDir {α : Type} (k : System.FilePath → IO α) : IO α := do
  let dir := (← workBase) / s!"ixai-verify-{← IO.monoNanosNow}"
  IO.FS.createDirAll dir
  try k dir finally
    try IO.FS.removeDirAll dir catch _ => pure ()

/-- The exit code of a route's status: `0` verified, `1` rejected, `3` attested, `4` incomplete. -/
def _root_.IxAIVerify.RouteStatus.exitCode : RouteStatus → UInt32
  | .verified => 0
  | .rejected => 1
  | .attested => 3
  | .incomplete => 4

/-- A route result with its hypotheses, if it names any. -/
def printRoute (r : RouteResult) : IO Unit := do
  IO.println s!"[{r.kind}] {r.status.label}"
  for d in r.detail do IO.println s!"  {d}"
  unless r.hypotheses.isEmpty do
    IO.println "hypotheses:"
    for h in r.hypotheses do IO.println s!"  - {h}"

/-- Check the trajectory in `file` against the consumer's job: a named job (`--job`, default
`default`), or one identified by digest (`--job-digest`); `--weights` binds the returned weights. -/
def trajectoryCommand (file : System.FilePath) (args : List String) : IO UInt32 := do
  let job? := match flag args "--job-digest" with
    | some h => (Digest.ofHex? h).bind fun d => (jobOfDigest? d).map (·, some d)
    | none => ((namedJobs.find? (·.1 == (flag args "--job").getD "default")).map (·.2)).map (·, none)
  let some (job, expected) := job?
    | IO.println "REJECT: no expected job: name one with --job (default, default-bf16, default-f32) or --job-digest"; return 1
  let weights := (flag args "--weights").bind Digest.ofHex?
  if (flag args "--weights").isSome && weights.isNone then
    IO.println "REJECT: malformed --weights digest"; return 1
  let v := checkTrajectory job expected weights (← IO.FS.readFile file)
  for l in showTrajectoryVerdict v do IO.println l
  return if v.accepted then 0 else 1

end IxAIVerify.Cli
