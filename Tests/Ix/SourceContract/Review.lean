module

public import LSpec
public import Ix.Meta
public import Ix.EnvScope
public import Ix.CompileDriver
public import Ix.Compile.ResourceProfile
public import Ix.Compile.Equations
public import Ix.Compile.CheckEquations

/-!
# Resource review probes as source-level checks

Each namespace of `Tests.Ix.SourceContract.ReviewFixture` is compiled as `ix
compile --anon --profile profiles/lean-core.profile` compiles it: its
definitions seed the closure, the profile source is built by
`Ix.Compile.ResourceProfile.build` (generated `case` lines included), and the
native compiler validates resources. A violation must be rejected by resource
admission; a control must compile. Strict, plain and standard probes are
compiled with `profiles/lean-core-strict.profile` (no shareable types),
`profiles/lean-core-plain.profile` (usage crossing on plain data) or the
standard profile instead.
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
  /-- The profile source file, relative to the repository root. -/
  profile : String := "profiles/lean-core.profile"

def probe (name : String) (accepted : Bool) (finding : String) : Probe :=
  { name, accepted, finding }

/-- A probe compiled with the strict Lean core profile (no shareable types). -/
def strictProbe (name : String) (accepted : Bool) (finding : String) : Probe :=
  { name, accepted, finding, profile := "profiles/lean-core-strict.profile" }

/-- A probe compiled with the plain-data Lean core profile (setting S6). -/
def plainProbe (name : String) (accepted : Bool) (finding : String) : Probe :=
  { name, accepted, finding, profile := "profiles/lean-core-plain.profile" }

/-- A probe compiled with the standard profile (no `--profile`). -/
def standardProbe (name : String) (accepted : Bool) (finding : String) : Probe :=
  { name, accepted, finding, profile := "" }

/-- Review R2-3: the refusal of annotated recursion outside a bound equation. -/
def recursionReason : String := "annotated recursive definition"

/-- Review F7 and R2-2: the refusal of an annotated declaration whose Lean body
is only a model of the code that runs. -/
def nativeReason : String := "has a native implementation"

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
  probe "S02" false "F7",
  probe "F06" false "S1", probe "LitString" false "S1", probe "FreshLocal" true "S1",
  strictProbe "F06" false "S1",
  probe "N07" false "S2", strictProbe "N07" false "S2",
  probe "LinearAdd" true "S2", strictProbe "LinearAdd" false "S2",
  probe "OS09" true "S2", strictProbe "OS09" false "S2",
  strictProbe "LinearId" true "S2", strictProbe "FreshLocal" true "S2", strictProbe "M01" true "S2",
  -- Review R2-3: annotated recursion is admitted only through a bound
  -- equation: refused under the standard profile and under a profile
  -- without `--equations`, and checked through the equation with it.
  { probe "Q06" false "R2-3" with reason := recursionReason },
  { standardProbe "Q06" false "R2-3" with reason := recursionReason }] ++
  (["W03", "E11", "J06", "Z03", "M12"].flatMap fun name => [
    { standardProbe name false "R2-3" with reason := recursionReason },
    { probe name false "R2-3" with reason := recursionReason },
    { strictProbe name false "R2-3" with reason := recursionReason },
    { probe name false "R2-3" with equations := true },
    { strictProbe name false "R2-3" with equations := true }]) ++
  -- Review R2-2: an annotated partial (opaque) definition is native: refused
  -- unless assumed; an unannotated one compiles.
  [{ standardProbe "V10" false "R2-2" with reason := nativeReason },
   { probe "V10" false "R2-2" with reason := nativeReason },
   { probe "V03" false "R2-2" with reason := nativeReason },
   { strictProbe "V03" false "R2-2" with reason := nativeReason },
   standardProbe "PartialPlain" true "R2-2", probe "PartialPlain" true "R2-2"] ++
  -- Setting S6: usage crosses on plain data (linear Nats used any number of
  -- times or dropped), is enforced on functions, and ownership is unchanged.
  [plainProbe "N07" true "S6", plainProbe "LinearAdd" true "S6", plainProbe "OS09" true "S6",
   plainProbe "LinearId" true "S6", plainProbe "M01" true "S6", plainProbe "FreshLocal" true "S6",
   plainProbe "LinearFunction" false "S6", probe "LinearFunction" false "S6",
   strictProbe "LinearFunction" false "S6",
   plainProbe "A05b" false "S6", plainProbe "X07" false "S6", plainProbe "F06" false "S6",
   plainProbe "P03" false "S6", plainProbe "A01" false "S6",
   { plainProbe "E11" false "S6" with equations := true },
   { plainProbe "E11" false "S6" with reason := recursionReason },
   { plainProbe "Q06" true "S6" with equations := true }]

/-- The safe definitions, theorems and opaques (`partial def`s) of a probe's
namespace. -/
def roots (env : Environment) (ns : Name) : List Name :=
  env.constants.toList.filterMap fun (name, info) =>
    match info with
    | .defnInfo d => if name.getPrefix == ns && d.safety != .unsafe then some name else none
    | .thmInfo _ | .opaqueInfo _ => if name.getPrefix == ns then some name else none
    | _ => none

/-- Compile one probe as `ix compile --anon` does, with its profile source
(`""`: the standard profile), including the compile-boundary checks
(`checkNative`, `checkRecursion`); the compile status, the realized
associations and the output path, or the first message refusing it. -/
def compileProbeStatus (env : Environment) (profile : String) (directory : System.FilePath)
    (probe : Probe) :
    IO (Except String (Ix.CompileM.CompileEnvStatus × Array Ix.Compile.Equations.Association ×
      System.FilePath)) := do
  let ns := fixtureModule ++ probe.name.toName
  let seeds := roots env ns
  if seeds.isEmpty then return .error s!"no definitions in {ns}"
  let (env, constList, found) ← if probe.equations then do
      let (env, closed, found, _) ← Ix.Compile.Equations.close env seeds
      let (env, found, _) := Ix.Compile.Equations.carryContracts env found
      pure (env, closed, found)
    else pure (env, Ix.EnvScope.collectDeps env seeds, #[])
  let constList ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants env constList
  let output := directory / s!"{probe.name}.ixe"
  if profile.isEmpty then
    if let .error message := Ix.Compile.ResourceProfile.checkNative none env constList then
      return .error message
    if let .error message ← Ix.Compile.ResourceProfile.checkRecursion none env constList [] then
      return .error message
    try
      return .ok (← Ix.CompileM.rsCompileEnvBytesAnonFFI constList output.toString false, found, output)
    catch error =>
      return .error (toString error)
  let source ← match Ix.Compile.ResourceProfile.build profile env constList with
    | .ok source => pure source
    | .error message => return .error message
  let equations := found.toList.map fun a => s!"equation {a.definition} {a.equation}\n"
  let forced := probe.forced.map fun (d, t) => s!"equation {ns ++ d.toName} {ns ++ t.toName}\n"
  let source := String.join (source :: equations ++ forced)
  let bound := found.toList.map (·.definition) ++ probe.forced.map fun (d, _) => ns ++ d.toName
  if let .error message ← Ix.Compile.ResourceProfile.checkRecursion (some source) env constList bound then
    return .error message
  try
    let status ← Ix.CompileM.rsCompileEnvBytesProfileSourceFFI constList output.toString
      false true source
    return .ok (status, found, output)
  catch error =>
    return .error (toString error)

/-- Compile one probe; `.ok` when it compiles, else the compiler's message. -/
def compileProbe (env : Environment) (profile : String) (directory : System.FilePath)
    (probe : Probe) : IO (Except String Unit) := do
  match ← compileProbeStatus env profile directory probe with
  | .ok (status, _, _) =>
    if status.ungrounded.isEmpty then return .ok ()
    return .error s!"ungrounded constants: {status.ungrounded.map (·.1)}"
  | .error message => return .error message

private def verdicts : IO (Bool × Nat × Nat × Option String) := do
  let env ← getCompileEnv #[fixtureModule]
  let directory ← IO.FS.createTempDir
  try
    let mut failures := #[]
    for probe in probes do
      let profile ← if probe.profile.isEmpty then pure "" else IO.FS.readFile probe.profile
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
  -- Review R2-2: an annotated `partial def` (an opaque run through its
  -- `_unsafe_rec` twin) likewise, and only through the profile's assumption.
  let env ← getCompileEnv #[fixtureModule]
  let loop := fixtureModule ++ `V10.loop
  let some loopInfo := env.find? loop | return (false, 0, 1, some s!"{loop} is missing")
  let partials := [(loop, loopInfo)]
  let partialRefused := (Ix.Compile.ResourceProfile.checkNative none env partials).toOption.isNone &&
    (Ix.Compile.ResourceProfile.checkNative (some "standard\n") env partials).toOption.isNone
  let partialAssumed :=
    (Ix.Compile.ResourceProfile.checkNative (some s!"assume {loop}\n") env partials).toOption.isSome
  let recursiveDefinition := Ix.Compile.ResourceProfile.native env (fixtureModule ++ `Q06.down)
  if refused && assumed && plain && partialRefused && partialAssumed && !recursiveDefinition then
    return (true, 1, 0, none)
  return (false, 0, 1, some s!"refused {refused}, assumed {assumed}, unannotated {plain}, \
    partial refused {partialRefused}, partial assumed {partialAssumed}, \
    recursive definition native {recursiveDefinition}")

/-- Strict setting S3: the sidecar of a compile under the core profile with
equations (Q06) lists its checked pair with both addresses, the profile and
the carried contracts; `Ix.Compile.CheckEquations.verify` accepts it against
the closure and refuses every tampered variant. -/
private def checkedEquations : IO (Bool × Nat × Nat × Option String) := do
  let env ← getCompileEnv #[fixtureModule]
  let profile ← IO.FS.readFile "profiles/lean-core.profile"
  let directory ← IO.FS.createTempDir
  try
    let probe : Probe := { name := "Q06", accepted := true, finding := "S3", equations := true }
    let (status, found, output) ← match ← compileProbeStatus env profile directory probe with
      | .ok result => pure result
      | .error message => return (false, 0, 1, some message)
    let some bytes := bytesOfHex status.resourceProfile
      | return (false, 0, 1, some "the compile reported no profile bytes")
    let address := toString (Address.blake3 bytes)
    let record : Ix.Compile.Equations.ResourceRecord :=
      { root := status.root, profile := some (address, status.resourceProfile),
        checked := status.resourceEquations }
    let closure ← IO.ofExcept (Ixon.runGetExact Ixon.Env.getEnv (← IO.FS.readBinFile output))
    let verify (found : Array Ix.Compile.Equations.Association)
        (record : Ix.Compile.Equations.ResourceRecord) :=
      Ix.Compile.CheckEquations.verify closure (Ix.Compile.Equations.toJson found #[] (some record))
    let accepted := match verify found record with
      | .ok report => report.entries.size == 1 && report.entries.all (·.contracts.size == 1)
      | .error _ => false
    let swapped := record.checked.map fun (d, t, da, _) => (d, t, da, da)
    let flipped := found.map fun a => { a with contracts := a.contracts.map fun c =>
      { c with value := { c.value with owned := if c.value.owned == .unique then .shared else .unique } } }
    let otherAddress := toString (Address.blake3 "another profile".toUTF8)
    let tampered := [
      ("wrong theorem address", verify found { record with checked := swapped }),
      ("missing pair", verify found { record with checked := #[] }),
      ("duplicated pair", verify found { record with checked := record.checked ++ record.checked }),
      ("other profile address", verify found { record with profile := some (otherAddress, status.resourceProfile) }),
      ("other root", verify found { record with root := otherAddress }),
      ("other contract", verify flipped record)]
    let failures := tampered.filterMap fun (what, result) =>
      if result.toOption.isSome then some what else none
    if accepted && failures.isEmpty then return (true, 1 + tampered.length, 0, none)
    return (false, 0, 1, some s!"accepted {accepted}, tampered sidecars accepted: {failures}")
  finally
    IO.FS.removeDirAll directory

/-- A no-break space (U+00A0). -/
def nbsp : String := String.singleton (Char.ofNat 0xa0)

/-- Second review R2-4: a generated directive behind a vertical tab, a form
feed or a no-break space (the review's smuggling profiles) is refused by the
Lean guard (`build`), and the native parser refuses it on its own when the
text reaches it without that guard. E01's `dup` moves `xs` twice; the
smuggled `equation dup dup_eq` would check it through `dup xs = xs`. -/
private def smuggledDirectives : IO (Bool × Nat × Nat × Option String) := do
  let env ← getCompileEnv #[fixtureModule]
  let core ← IO.FS.readFile "profiles/lean-core.profile"
  let ns := fixtureModule ++ `E01
  let constList ← IO.ofExcept <| Ix.Compile.prepareRegisteredConstants env
    (Ix.EnvScope.collectDeps env (roots env ns))
  let line := s!"equation {ns ++ `dup} {ns ++ `dup_eq}\n"
  let directory ← IO.FS.createTempDir
  try
    let mut failures := #[]
    for (what, hidden) in [("vertical tab", "\x0b"), ("form feed", "\x0c"), ("no-break space", nbsp)] do
      let written := core ++ hidden ++ line
      if (Ix.Compile.ResourceProfile.build written env constList).toOption.isSome then
        failures := failures.push s!"{what}: the Lean guard accepted the written profile"
      -- Without the Lean guard, after the compiler's own `generated` line too.
      for text in [written, written ++ "generated\n", core ++ "generated\n" ++ hidden ++ line] do
        let rejected ← try
            let _ ← Ix.CompileM.rsCompileEnvBytesProfileSourceFFI constList
              (directory / "smuggled.ixe").toString false true text
            pure false
          catch error => pure (((toString error).splitOn "resource profile source").length > 1)
        unless rejected do failures := failures.push s!"{what}: the native parser accepted it"
    -- A plain written `equation` line is refused by both as well.
    let rejected ← try
        let _ ← Ix.CompileM.rsCompileEnvBytesProfileSourceFFI constList
          (directory / "plain.ixe").toString false true (core ++ line)
        pure false
      catch _ => pure true
    unless rejected do failures := failures.push "a written equation line reached the checker"
    if failures.isEmpty then return (true, 1, 0, none)
    return (false, 0, 1, some ("\n".intercalate failures.toList))
  finally
    IO.FS.removeDirAll directory

def suite : List TestSeq := [
  .individualIO "review probes: violations rejected, controls accepted (standard, core, strict and plain profiles)" none verdicts .done,
  .individualIO "an annotated native implementation must be a profile assumption" none
    nativeImplementations .done,
  .individualIO "check-equations verifies the checked pairs a sidecar lists" none
    checkedEquations .done,
  .individualIO "generated directives cannot be smuggled into a written profile" none
    smuggledDirectives .done,
  test "a written profile may not contain generated directives"
    ((Ix.Compile.ResourceProfile.checkWritten "cases\ncase List.casesOn\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten "cases\nequation dup dup_eq\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten "cases\ngenerated\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten "cases\n\x0bcase sel\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten "cases\n\x0ccase sel\n").toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten ("cases\n" ++ nbsp ++ "equation dup dup_eq\n")).toOption.isNone &&
     (Ix.Compile.ResourceProfile.checkWritten ("cases\r\n# a comment may say anything" ++ nbsp ++ "\n")).toOption.isSome &&
     (Ix.Compile.ResourceProfile.checkWritten "cases # case in a comment\n").toOption.isSome)
]

end Tests.Ix.SourceContract.Review

end
