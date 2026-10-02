module

public import LSpec
public import Ix.CompileDriver
public import Ix.Cli.CompileCmd

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

def suite : List TestSeq := [
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
    return unsupported (← compileLeanConsts (constants markedSource) (numWorkers := 1)),
  ioTest "explicit Lean input rejects a missing annotation registry" do
    match ← compileLeanInput (.plain (constants markedSource)) (numWorkers := 1) with
    | .error message => return (message.splitOn "missingContract").length > 1
    | .ok _ => return false,
  ioTest "explicit Lean input requires an assumption for an annotated axiom" do
    let .ok contract := SourceContract.ofTelescope plainSource #[
      { binder := .position 0, uses := .linear }]
      | return false
    let input : CompileInput := { constants := constants plainSource, contracts := #[contract] }
    return unsupported (← compileLeanInput input (numWorkers := 1)),
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
      IO.FS.removeDirAll directory,
  ioTest "unprepared Rust FFI hands back every marked list without compiling, in every output mode" do
    let directory ← IO.FS.createTempDir
    try
      let semanticSource : ConstantInfo := .axiomInfo {
        name := plainSource.name, levelParams := []
        type := .mdata (({} : Lean.MData).setNat `ix.contract.unknown 1) plainSource.type
        isUnsafe := false }
      for source in [markedSource, semanticSource] do
        for allowPartial in [false, true] do
          for strictAnon in [false, true] do
            let output := directory / s!"unprepared-{allowPartial}-{strictAnon}.ixe"
            let result ← rsCompileEnvBytesUnpreparedFFI (constants source)
              output.toString allowPartial strictAnon
            if result.isSome || (← output.pathExists) ||
                (← (System.FilePath.mk (output.toString ++ ".tmp")).pathExists) then
              return false
      return true
    finally
      IO.FS.removeDirAll directory,
  ioTest "unprepared Rust FFI compiles an unmarked list exactly as the prepared FFI" do
    let directory ← IO.FS.createTempDir
    try
      for strictAnon in [false, true] do
        let prepared := directory / s!"prepared-{strictAnon}.ixe"
        let unprepared := directory / s!"unprepared-{strictAnon}.ixe"
        let expected ← if strictAnon
          then rsCompileEnvBytesAnonFFI (constants plainSource) prepared.toString false
          else rsCompileEnvBytesFFI (constants plainSource) prepared.toString false
        let some status ← rsCompileEnvBytesUnpreparedFFI (constants plainSource)
            unprepared.toString false strictAnon
          | return false
        if status.root != expected.root || status.bytes != expected.bytes ||
            status.named != expected.named || status.uniqueAnon != expected.uniqueAnon ||
            status.ungrounded != expected.ungrounded then
          return false
        if (← IO.FS.readBinFile prepared) != (← IO.FS.readBinFile unprepared) then
          return false
      return true
    finally
      IO.FS.removeDirAll directory
]

end Tests.Ix.SourceContract.Driver

end
