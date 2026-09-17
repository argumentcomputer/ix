import CompilatrixTests.Ixby.Fri.Examples
import CompilatrixTests.Ixby.Native.Support

namespace CompilatrixTests.Ixby.Fri

open Lean Compilatrix.Tools.Check Compilatrix.Ixby.LeanFrontend
open Examples

def compileImage (env : Environment) (entry : Name) (equalities : Array Name := #[]) : IO Image := do
  let (result, _) ← (compile entry (setup := Compilatrix.Ixby.Runtime.buildWire)
    (sourceEqualities := equalities)).toIO
      { fileName := "FRI source replacement regression", fileMap := default,
        maxRecDepth := 16384, maxHeartbeats := 0 } { env }
  let image ← checked result
  discard <| checked image.certifyWireRuntime
  return image

private def rejects (env : Environment) (name : Name) (reason : String := "") : IO Unit := do
  let (result, _) ← (checkSourceReplacement name).toIO
    { fileName := "source replacement rejection", fileMap := default } { env }
  match result with
  | .error message => need (message.startsWith reason) s!"wrong replacement rejection: {message}"
  | .ok _ => throw (IO.userError s!"invalid source replacement admitted: {name}")

def checking (env : Environment) : IO Unit := do
  for name in #[`missingSourceEquality, ``original, ``unchanged_eq,
      ``conditional_eq, ``polymorphic_eq, ``propext] do
    rejects env name
  -- These declarations exist only in a temporary test environment. Even a
  -- well-typed equality with the right names must fail on an extra axiom.
  let some (.thmInfo originalTheorem) := env.find? ``original_eq |
    throw (IO.userError "missing replacement fixture theorem")
  let assumption := `CompilatrixTests.Ixby.Fri.injectedAssumption
  let poisonedName := `CompilatrixTests.Ixby.Fri.injectedEquality
  let poisoned ← checked ((env.addDeclCore 100000 1024 (.axiomDecl {
    name := assumption, levelParams := [], type := originalTheorem.type, isUnsafe := false }) none).mapError
      (fun _ => "could not construct the axiom rejection fixture"))
  let poisoned ← checked ((poisoned.addDeclCore 100000 1024 (.thmDecl {
    name := poisonedName, levelParams := [], type := originalTheorem.type,
    value := mkConst assumption }) none).mapError (fun _ => "could not construct the tainted equality fixture"))
  rejects poisoned poisonedName "source replacement has an unsupported axiom:"
  let (mono, _) ← (Compiler.LCNF.getMonoDecl? ``target).toIO
    { fileName := "replacement arity mutation", fileMap := default } { env }
  let some mono := mono | throw (IO.userError "missing replacement target LCNF")
  let some (.defnInfo targetInfo) := env.find? ``target |
    throw (IO.userError "missing replacement target definition")
  let localTarget := `CompilatrixTests.Ixby.Fri.localTarget
  let localEquality := `CompilatrixTests.Ixby.Fri.localEquality
  let localEnv ← checked ((env.addDeclCore 100000 1024
    (.defnDecl { targetInfo with name := localTarget }) none).mapError
      (fun _ => "could not construct the local replacement definition"))
  let localType := originalTheorem.type.replace fun term => match term with
    | .const name levels => if name == ``target then some (.const localTarget levels) else none
    | _ => none
  let localEnv ← checked ((localEnv.addDeclCore 100000 1024 (.thmDecl {
    originalTheorem with name := localEquality, type := localType }) none).mapError
      (fun _ => "could not construct the local replacement theorem"))
  rejects localEnv localEquality "source replacement has no target LCNF:"
  let wrongArity := Compiler.LCNF.saveMonoDeclCore localEnv
    { mono with name := localTarget, params := #[] }
  rejects wrongArity localEquality "source replacement changes monomorphic arity:"
  let externalBody := Compiler.LCNF.saveMonoDeclCore localEnv
    { mono with name := localTarget, value := .extern { entries := [.opaque] } }
  rejects externalBody localEquality "source replacement cannot replace externs:"
  let originalImage ← compileImage env ``original
  let protectedImage ← compileImage env ``original #[``protected_eq]
  need (protectedImage.state.sourceReplacementRejection.any
    (·.startsWith "source replacement touches an installed runtime body:"))
    "protected helper did not reach the installed-body guard"
  let selected ← compileImage env ``original #[``original_eq]
  need (selected.state.sourceReplacementRejection.isNone &&
    selected.state.sourceReplacements == #[⟨``original, ``target, ``original_eq⟩])
    "source equality selection metadata"
  need (selected.state.functionNames[``original]? == selected.state.functionNames[``target]? &&
    selected.state.functionNames[``target]? == some selected.program.entry)
    "selected root did not use the theorem's exact target"
  for equalities in #[#[`missingSourceEquality], #[``original_eq, ``original_eq],
      #[``original_eq, ``reverse_eq], #[``original_eq, ``chain_eq], #[``protected_eq],
      #[``original_eq, `missingSourceEquality], Array.replicate 33 ``original_eq] do
    let fallback ← compileImage env ``original equalities
    need (fallback.state.sourceReplacementRejection.isSome &&
      fallback.state.sourceReplacements.isEmpty && fallback.program == originalImage.program)
      s!"invalid source request did not preserve the complete original image: {equalities}"
  let shared ← compileImage env ``second #[``original_eq, ``second_eq]
  need (shared.state.sourceReplacementRejection.isNone &&
    shared.state.sourceReplacements.size == 2 &&
    shared.state.functionNames[``second]? == shared.state.functionNames[``target]?)
    "independent sources could not share an equal target"
  for n in #[0, 1, 17, 2 ^ 80 + 19] do
    let args := #[Ix.Ixby.Value.scalar (.nat n)]
    for image in #[originalImage, selected, shared] do
      let actual := Ix.Ixby.execute image.state.limits image.program args 10000
      need (Native.same actual (.ok (.scalar (.nat n)))) "source replacement changed execution"
  IO.println "FRI replacement checking: exact targets, shared targets and whole-image fallbacks passed"

end CompilatrixTests.Ixby.Fri
