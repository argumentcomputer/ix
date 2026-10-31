module

public import LSpec
public import Ix.CompileDriver
public import Ix.CompileResource
public import Ix.Meta

public section

namespace Tests.Ix.SourceContract.Driver

open Lean LSpec Ix.Compile Ix.CompileM

private def plainSource : ConstantInfo := .axiomInfo {
  name := `SourceContractDriver.identityType, levelParams := []
  type := .forallE `x (.sort .zero) (.sort .zero) .default
  isUnsafe := false }

private def annotation : BinderAnnotation := {
  origin := 0, binder := `x, uses := .affine, value := .localUnique }

private def markedSource : ConstantInfo := .axiomInfo {
  name := plainSource.name, levelParams := []
  type := .forallE `x (.mdata annotation.toMetadata (.sort .zero)) (.sort .zero) .default
  isUnsafe := false }

private def constants (source : ConstantInfo) := [(source.name, source)]

private def ioTest (description : String) (check : IO Bool) : TestSeq :=
  .individualIO description none (do return (← check, 0, 0, none)) .done

private def unsupported (result : Except String α) : Bool :=
  match result with
  | .error message => (message.splitOn "external resource interface is absent").length > 1
  | .ok _ => false

private def placement : IO Bool := do
  let env ← getFileEnv "Tests/Ix/SourceContract/PlacementFixture.lean"
  let some source := env.find? `SemanticPlacement.etaExpanded | return false
  let .ok contract := SourceContract.ofTelescope source #[{ binder := .position 1, uses := .linear }]
    | return false
  let input : CompileInput := { constants := constants source, contracts := #[contract] }
  let .ok [(_, decorated)] := input.prepare | return false
  let .defnInfo cv := (Id.run ((_root_.Ix.CanonM.canonConst decorated).run {})).1 | return false
  let .lam _ _ frame _ _ := cv.value | return false
  let .mdata data (.lam n ty _ bi _) _ := frame | return false
  let inspect := _root_.Ix.SemanticContract.inspect
  let g := _root_.Ix.Expr.mkConst (_root_.Ix.Name.fromLeanName `Nat.succ) #[]
  let zero := _root_.Ix.Expr.mkBVar 0
  let kept := _root_.Ix.Expr.mkLam n ty (_root_.Ix.Expr.mkApp g zero) bi
  let malformed := _root_.Ix.Expr.mkMData data.pop kept
  let some original := sourceBody? source | return false
  let some prepared := sourceBody? decorated | return false
  let checks := #[
    ("actual prepared-source presence", [(source.type, false), (original, false),
      (decorated.type, true), (prepared, true)].all fun (e, expected) =>
        exprHasSemanticContracts e == expected && SemanticPresence.spec e == expected &&
        SemanticPresence.runWith (fun _ => 0) e == expected),
    ("prepared source and preserved binder inspect", data.size == 3 &&
      (inspect cv.cnst.type).toOption == some true && (inspect cv.value).toOption == some true),
    ("malformed colliding payload retains exact refusal", match inspect malformed with
        | .error error => error == "malformed semantic contract frame" | _ => false)]
  for (label, ok) in checks do
    unless ok do throw (IO.userError s!"semantic placement: {label}")
  return true

def suite : List TestSeq := [
  ioTest "prepared semantic lambda: source presence, binder inspection and malformed-frame refusal" placement,
  ioTest "ordinary source preflight preserves declarations and validates names" do
    let env ← Lean.mkEmptyEnvironment
    let sources := constants plainSource
    for prepare in [prepareSourceConstants, prepareRegisteredConstants env] do
      if (prepare sources).toOption != some sources then return false
      if (prepare (sources ++ sources)).toOption.isSome then return false
      if (prepare [(`wrongName, plainSource)]).toOption.isSome then return false
    return true,
  ioTest "ordinary source preflight cannot bypass reserved semantic metadata" do
    let env ← Lean.mkEmptyEnvironment
    let source : ConstantInfo := .axiomInfo {
      name := plainSource.name, levelParams := []
      type := .mdata (({} : Lean.MData).setNat `ix.contract.unknown 1) plainSource.type
      isUnsafe := false }
    for prepare in [prepareSourceConstants, prepareRegisteredConstants env] do
      if (prepare (constants source)).toOption.isSome then return false
      let .ok marked := prepare (constants markedSource) | return false
      if marked == constants markedSource then return false
    return true,
  ioTest "parallel source preflight checks every batch and its final remainder" do
    let sources := (List.range 2049).map fun i =>
      let name := Lean.Name.num plainSource.name i
      let source : ConstantInfo := .axiomInfo {
        name, levelParams := [], type := plainSource.type, isUnsafe := false }
      (name, source)
    if (checkOrdinaryConstants sources (fun _ => false)).toOption != some true then return false
    for index in [1023, 1024, 2048] do
      let marked := sources.mapIdx fun i (name, source) =>
        if i != index then (name, source) else
          let source : ConstantInfo := .axiomInfo {
            name, levelParams := []
            type := .mdata (({} : Lean.MData).setNat `ix.contract.unknown 1) source.type
            isUnsafe := false }
          (name, source)
      if (checkOrdinaryConstants marked (fun _ => false)).toOption != some false then return false
    return true,
  ioTest "Lean constant-list driver rejects an unadmitted annotated axiom" do
    return unsupported (← compileLeanConstsValidated (constants markedSource) (numWorkers := 1)),
  ioTest "explicit Lean input rejects a missing annotation registry" do
    match ← compileLeanInput (.plain (constants markedSource)) (numWorkers := 1) with
    | .error message => return (message.splitOn "missingContract").length > 1
    | .ok _ => return false,
  ioTest "explicit Lean input requires an assumption for an annotated axiom" do
    let .ok contract := SourceContract.ofTelescope plainSource #[
      { binder := .position 0, uses := .linear }]
      | return false
    let input : CompileInput := { constants := constants plainSource, contracts := #[contract] }
    return unsupported (← compileLeanInputValidated input (numWorkers := 1)),
  ioTest "measure-only input preserves ordinary production bytes" do
    let input := CompileInput.plain (constants plainSource)
    let .ok plain ← compileLeanInput input (numWorkers := 1) | return false
    let hinted := { input with measureHints := #[⟨plainSource, .position 0, some 1⟩] }
    let .ok measured ← compileLeanInput hinted (numWorkers := 1) | return false
    return plain.bytes == measured.bytes,
  ioTest "Rust FFI rejects source contracts without creating an artifact in either output mode" do
    let directory ← IO.FS.createTempDir
    try
      for allowPartial in [false, true] do
        let output := directory / s!"contracts-{allowPartial}.ixe"
        let rejected ← try
          let _ ← rsCompileEnvBytesFFI (constants markedSource) output.toString allowPartial
          pure false
        catch error =>
          pure ((error.toString.splitOn "unresolved source binder contracts").length > 1)
        if !rejected || (← output.pathExists) ||
            (← (System.FilePath.mk (output.toString ++ ".tmp")).pathExists) then
          return false
      return true
    finally
      IO.FS.removeDirAll directory
]

end Tests.Ix.SourceContract.Driver

end
