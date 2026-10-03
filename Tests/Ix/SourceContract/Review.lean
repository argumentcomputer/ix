module

public import LSpec
public import Ix.Meta
public import Ix.EnvScope
public import Ix.CompileDriver
public import Ix.Compile.ResourceProfile
public import Ix.Compile.Equations

/-!
# Resource review probes as source-level checks

Each namespace of `Tests.Ix.SourceContract.ReviewFixture` is compiled as `ix
compile --anon --profile profiles/lean-core.profile` compiles it: its
definitions seed the closure, the profile source is built by
`Ix.Compile.ResourceProfile.build` (generated `case` lines included), and the
native compiler validates resources. A violation must be rejected by resource
admission; a control must compile.
-/

public section

namespace Tests.Ix.SourceContract.Review

open Lean LSpec

def fixtureModule : Name := `Tests.Ix.SourceContract.ReviewFixture

structure Probe where
  /-- The namespace under `fixtureModule`. -/
  name : String
  accepted : Bool
  /-- Review finding the probe pins. -/
  finding : String
  /-- Compile as `ix compile --equations` does: realize the unfolding
  equations of the closure and bind them by generated directives. -/
  equations : Bool := false
  /-- Equation directives `(definition, theorem)`, names relative to the
  namespace, appended to the profile source as a forged profile would (the
  CLI refuses them in a written profile). -/
  forced : List (String × String) := []
  /-- What a rejection message must contain. -/
  reason : String := "resource admission"

def probe (name : String) (accepted : Bool) (finding : String) : Probe :=
  { name, accepted, finding }

def probes : List Probe := [
  probe "A01" false "F1", probe "A04" false "F1", probe "B07" false "F1", probe "A03b" false "F1",
  probe "M01" true "F1", probe "M02" true "F1", probe "I06" true "F1",
  probe "A05b" false "F2", probe "X07" false "F2", probe "OS09" true "F2",
  probe "I08" false "F4", probe "I01" false "F4",
  { name := "E04", accepted := false, finding := "F3", forced := [("dup", "dup_eq")],
    reason := "an unfolding equation depends on an axiom other than propext" },
  { name := "E01", accepted := false, finding := "F3", equations := true },
  { name := "Q06", accepted := true, finding := "F3", equations := true },
  probe "P03" false "F5", probe "C09" false "F5",
  probe "S02" false "F7"]

/-- The definitions and theorems of a probe's namespace. -/
def roots (env : Environment) (ns : Name) : List Name :=
  env.constants.toList.filterMap fun (name, info) =>
    match info with
    | .defnInfo _ | .thmInfo _ => if name.getPrefix == ns then some name else none
    | _ => none

/-- Compile one probe with the core profile; `.ok` when it compiles, else the
compiler's message. -/
def compileProbe (env : Environment) (profile : String) (directory : System.FilePath)
    (probe : Probe) : IO (Except String Unit) := do
  let ns := fixtureModule ++ probe.name.toName
  let seeds := roots env ns
  if seeds.isEmpty then return .error s!"no definitions in {ns}"
  let (env, constList, equations) ← if probe.equations then do
      let (env, closed, found, _) ← Ix.Compile.Equations.close env seeds
      let (env, found, _) := Ix.Compile.Equations.carryContracts env found
      pure (env, closed, found.toList.map fun a => s!"equation {a.definition} {a.equation}\n")
    else pure (env, Ix.EnvScope.collectDeps env seeds, [])
  let constList ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants env constList
  let source ← match Ix.Compile.ResourceProfile.build profile env constList with
    | .ok source => pure source
    | .error message => return .error message
  let forced := probe.forced.map fun (d, t) => s!"equation {ns ++ d.toName} {ns ++ t.toName}\n"
  let source := String.join (source :: equations ++ forced)
  let output := directory / s!"{probe.name}.ixe"
  try
    let status ← Ix.CompileM.rsCompileEnvBytesProfileSourceFFI constList output.toString
      false true source
    if status.ungrounded.isEmpty then return .ok ()
    return .error s!"ungrounded constants: {status.ungrounded.map (·.1)}"
  catch error =>
    return .error (toString error)

private def verdicts : IO (Bool × Nat × Nat × Option String) := do
  let env ← getCompileEnv #[fixtureModule]
  let profile ← IO.FS.readFile "profiles/lean-core.profile"
  let directory ← IO.FS.createTempDir
  try
    let mut failures := #[]
    for probe in probes do
      match ← compileProbe env profile directory probe, probe.accepted with
      | .ok (), true => pure ()
      | .error message, false =>
        unless (message.splitOn probe.reason).length > 1 do
          failures := failures.push s!"{probe.name} ({probe.finding}): rejected without `{probe.reason}`: {message.take 300}"
      | .ok (), false => failures := failures.push s!"{probe.name} ({probe.finding}): violation accepted"
      | .error message, true =>
        failures := failures.push s!"{probe.name} ({probe.finding}): control rejected: {message.take 300}"
    if failures.isEmpty then return (true, probes.length, 0, none)
    return (false, probes.length - failures.size, failures.size, some ("\n".intercalate failures.toList))
  finally
    IO.FS.removeDirAll directory

/-- Review F7: an annotated declaration with a native implementation
(`String.push`, `@[extern]`, given a registered contract here) is admitted
only as an explicit assumption; its model body is never checked or inlined. -/
private def nativeImplementations : IO (Bool × Nat × Nat × Option String) := do
  let env ← getCompileEnv #[fixtureModule]
  let some info := env.find? `String.push | return (false, 0, 1, some "String.push is missing")
  let contract ← IO.ofExcept <| (Ix.Compile.SourceContract.ofTelescope info #[
    { binder := .position 0, uses := .many, value := .unique }]).mapError toString
  let env ← IO.ofExcept <| (Ix.Compile.registerSourceContract env contract).mapError toString
  let constants := [(`String.push, info)]
  let refused := (Ix.Compile.ResourceProfile.checkNative none env constants).toOption.isNone &&
    (Ix.Compile.ResourceProfile.checkNative (some "standard\n") env constants).toOption.isNone
  let assumed := (Ix.Compile.ResourceProfile.checkNative (some "assume String.push\n") env constants).toOption.isSome
  let plain := (Ix.Compile.ResourceProfile.checkNative none (← getCompileEnv #[fixtureModule]) constants).toOption.isSome
  if refused && assumed && plain then return (true, 1, 0, none)
  return (false, 0, 1, some s!"refused {refused}, assumed {assumed}, unannotated {plain}")

def suite : List TestSeq := [
  .individualIO "review probes: violations rejected, controls accepted (core profile)" none verdicts .done,
  .individualIO "an annotated native implementation must be a profile assumption" none
    nativeImplementations .done,
  test "a written profile may not contain generated directives"
    ((Ix.Compile.ResourceProfile.checkWritten "cases\ncase List.casesOn\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten "cases\nequation dup dup_eq\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten "cases # case in a comment\n").toOption.isSome)
]

end Tests.Ix.SourceContract.Review

end
