module

public import LSpec
public import Ix.Meta
public import Ix.EnvScope
public import Ix.CompileDriver
public import Ix.Compile.ResourceProfile

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

def probes : List Probe := [
  ⟨"A01", false, "F1"⟩, ⟨"A04", false, "F1"⟩, ⟨"B07", false, "F1"⟩, ⟨"A03b", false, "F1"⟩,
  ⟨"M01", true, "F1"⟩, ⟨"M02", true, "F1"⟩, ⟨"I06", true, "F1"⟩,
  ⟨"A05b", false, "F2"⟩, ⟨"X07", false, "F2"⟩, ⟨"OS09", true, "F2"⟩]

/-- The definitions of a probe's namespace. -/
def roots (env : Environment) (ns : Name) : List Name :=
  env.constants.toList.filterMap fun (name, info) =>
    match info with
    | .defnInfo _ => if name.getPrefix == ns then some name else none
    | _ => none

/-- Compile one probe with the core profile; `.ok` when it compiles, else the
compiler's message. -/
def compileProbe (env : Environment) (profile : String) (directory : System.FilePath)
    (probe : Probe) : IO (Except String Unit) := do
  let ns := fixtureModule ++ probe.name.toName
  let seeds := roots env ns
  if seeds.isEmpty then return .error s!"no definitions in {ns}"
  let constList := Ix.EnvScope.collectDeps env seeds
  let constList ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants env constList
  let source ← IO.ofExcept <|
    Ix.Compile.ResourceProfile.build profile env (constList.map (·.1))
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
        unless (message.splitOn "resource admission").length > 1 do
          failures := failures.push s!"{probe.name} ({probe.finding}): rejected outside resource admission: {message.take 300}"
      | .ok (), false => failures := failures.push s!"{probe.name} ({probe.finding}): violation accepted"
      | .error message, true =>
        failures := failures.push s!"{probe.name} ({probe.finding}): control rejected: {message.take 300}"
    if failures.isEmpty then return (true, probes.length, 0, none)
    return (false, probes.length - failures.size, failures.size, some ("\n".intercalate failures.toList))
  finally
    IO.FS.removeDirAll directory

def suite : List TestSeq := [
  .individualIO "review probes: violations rejected, controls accepted (core profile)" none verdicts .done,
  test "a written profile may not contain generated directives"
    ((Ix.Compile.ResourceProfile.checkWritten "cases\ncase List.casesOn\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten "cases # case in a comment\n").toOption.isSome)
]

end Tests.Ix.SourceContract.Review

end
