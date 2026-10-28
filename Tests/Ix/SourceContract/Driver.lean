module

public import LSpec
public import Ix.CompileDriver
public import Ix.CompileResource
public import Ix.Compile.Image.Develop
public import Ix.Compile.Image.RawExact
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

open _root_.Ix.Compile.Image in
private def placement : IO Bool := do
  let env ← getFileEnv "Tests/Ix/SourceContract/PlacementFixture.lean"
  let some source := env.find? `SemanticPlacement.etaExpanded | return false
  let .ok contract := SourceContract.ofTelescope source #[{ binder := .position 1, uses := .linear }]
    | return false
  let input : CompileInput := { constants := constants source, contracts := #[contract] }
  let .ok [(_, decorated)] := input.prepare | return false
  let .defnInfo cv := (Id.run ((_root_.Ix.CanonM.canonConst decorated).run {})).1 | return false
  let .lam _ _ frame _ _ := cv.value | return false
  let .mdata data raw@(.lam n ty _ bi _) _ := frame | return false
  let eq := RawExact.exprEq
  let inspect := _root_.Ix.SemanticContract.inspect
  let g := _root_.Ix.Expr.mkConst (_root_.Ix.Name.fromLeanName `Nat.succ) #[]
  let zero := _root_.Ix.Expr.mkBVar 0
  let body := _root_.Ix.Expr.mkApp g zero
  let kept := _root_.Ix.Expr.mkLam n ty body bi
  let expected := _root_.Ix.Expr.mkMData data kept
  let run := fun fuel st e => (hinst fuel g 0 e).run st
  let reaches := fun fuel st e out => (run fuel st e).toOption.any fun (r, _) => eq r.1 out
  let exhausted := fun fuel st e => match run fuel st e with
    | .error error => error == developExhausted | _ => false
  let .ok ((out, tag), warm) := run 4 {} frame | return false
  let .ok ((plain, _), plainWarm) := run 3 {} raw | return false
  let badData := data.pop
  let bad : _root_.Ix.Expr := .mdata badData raw frame.getHash
  let malformed := _root_.Ix.Expr.mkMData badData kept
  let native := #[(_root_.Ix.Name.fromLeanName `native.hint, _root_.Ix.DataValue.ofNat 7)]
  let record := #[(_root_.Ix.Name.fromLeanName `_ix.inline, _root_.Ix.DataValue.ofNat 0)]
  let nested := _root_.Ix.Expr.mkMData data (_root_.Ix.Expr.mkLam n ty
    (_root_.Ix.Expr.mkMData data (_root_.Ix.Expr.mkLam n ty
      (_root_.Ix.Expr.mkApp (_root_.Ix.Expr.mkBVar 2) zero) bi)) bi)
  let nestedOut := _root_.Ix.Expr.mkMData data (_root_.Ix.Expr.mkLam n ty expected bi)
  let some original := sourceBody? source | return false
  let some prepared := sourceBody? decorated | return false
  let checks := #[
    ("actual prepared-source presence", [(source.type, false), (original, false),
      (decorated.type, true), (prepared, true)].all fun (e, expected) =>
        exprHasSemanticContracts e == expected && SemanticPresence.spec e == expected &&
        SemanticPresence.runWith (fun _ => 0) e == expected),
    ("prepared source and preserved binder inspect", data.size == 3 &&
      (inspect cv.cnst.type).toOption == some true && (inspect cv.value).toOption == some true &&
      eq out expected && tag == .no && (inspect out).toOption == some true),
    ("actual instantiateWith cold/warm", (instantiateWith {} cv.value #[g]).toOption.any fun (first, state) =>
      eq first expected && (instantiateWith state cv.value #[g]).toOption.any fun (next, after) =>
        eq next expected && after.insts.size == state.insts.size),
    ("full frame cache and ordinary eta", eq plain g && reaches 1 warm frame expected &&
      (instProbe warm g frame 0).any (fun r => eq r.1 expected && r.2 == .no)),
    ("both mixed cache orders", reaches 16 plainWarm frame expected && reaches 16 warm raw g),
    ("cold fuel boundary and warm zero", [0, 1, 2, 3].all (fun fuel => exhausted fuel {} frame) &&
      reaches 4 {} frame expected && exhausted 0 warm frame),
    ("plain cache cannot bypass protected structural fuel", exhausted 1 plainWarm frame &&
      exhausted 2 plainWarm frame && reaches 3 plainWarm frame expected),
    ("plain metadata still eta-reduces; adjacent records preserve frames", [native, record].all fun md =>
      reaches 16 {} (_root_.Ix.Expr.mkMData md raw) (_root_.Ix.Expr.mkMData md g) &&
      reaches 16 {} (_root_.Ix.Expr.mkMData md frame) (_root_.Ix.Expr.mkMData md expected)),
    ("nested semantic binders", reaches 16 {} nested nestedOut && (inspect nestedOut).toOption == some true),
    ("malformed colliding payload retains exact refusal", !eq bad frame &&
      reaches 16 warm bad malformed && match inspect malformed with
        | .error error => error == "malformed semantic contract frame" | _ => false)]
  for (label, ok) in checks do
    unless ok do throw (IO.userError s!"semantic placement: {label}")
  return true

def suite : List TestSeq := [
  ioTest "prepared semantic lambda survives development, caches, fuel and malformed-frame controls" placement,
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
