module

public import LSpec
public import Ix.CompileCertified
public import Ix.ModeCheck
public import Ix.Meta

/-!
  Source-contract driver tests (`Tests.Ix.SourceContract.Driver`).
-/

public section

namespace Tests.Ix.SourceContract.Driver

open Lean LSpec Ix.Compile Ix.CompileM

private def plainSource : ConstantInfo := .axiomInfo {
  name := `SourceContractDriver.identityType, levelParams := []
  type := .forallE `x (.sort .zero) (.sort .zero) .default
  isUnsafe := false }

private def annotation : BinderAnnotation := {
  origin := 0, binder := `x, uses := .many, value := .unique }

private def markedSource : ConstantInfo := .axiomInfo {
  name := plainSource.name, levelParams := []
  type := .forallE `x (.mdata annotation.toMetadata (.sort .zero)) (.sort .zero) .default
  isUnsafe := false }

private def constants (source : ConstantInfo) := [(source.name, source)]

private def ioTest (description : String) (check : IO Bool) : TestSeq :=
  .individualIO description none (do return (← check, 0, 0, none)) .done

/-- An IO test that reports what the compile said when mode checking did not
refuse an annotated constant with no run body. -/
private def refusalTest (description : String) (result : IO (Except String Ix.CompileM.CertifiedOut)) :
    TestSeq :=
  .individualIO description none (do
    match ← result with
    | .ok _ => return (false, 0, 0, some "compiled")
    | .error message =>
      let ok := (message.splitOn "not in the extern set").length > 1 ||
        (message.splitOn "annotated source is refused").length > 1
      return (ok, 0, 0, if ok then none else some message)) .done

private def compileConsts (consts : List (Lean.Name × ConstantInfo)) :
    IO (Except String Ix.CompileM.CertifiedOut) := do
  match prepareSourceConstants consts >>= fun p => (checkPreparedSource p).map (p, ·) with
  | .error e => return .error e
  | .ok (prepared, annotated) =>
    compileCertifiedPrepared prepared annotated 1 (binderData := true)
      (modeCheck := Ix.ModeCheck.checkArtifact)

private def compileInput (input : CompileInput) :
    IO (Except String Ix.CompileM.CertifiedOut) := do
  match input.prepare >>= fun p => (checkPreparedSource p).map (p, ·) with
  | .error e => return .error e
  | .ok (prepared, annotated) =>
    compileCertifiedPrepared prepared annotated 1 (binderData := true)
      (modeCheck := Ix.ModeCheck.checkArtifact)

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
  refusalTest "Lean constant-list driver refuses an annotated axiom"
    (compileConsts (constants markedSource)),
  ioTest "explicit Lean input rejects a missing annotation registry" do
    match ← compileInput (.plain (constants markedSource)) with
    | .error message => return (message.splitOn "missingContract").length > 1
    | .ok _ => return false,
  refusalTest "explicit Lean input refuses an annotated axiom" (do
    let .ok contract := SourceContract.ofTelescope plainSource #[
      { binder := .position 0, uses := .linear }]
      | return .error "the telescope contract does not resolve"
    compileInput { constants := constants plainSource, contracts := #[contract] }),
  ioTest "measure-only input preserves ordinary production bytes" do
    let input := CompileInput.plain (constants plainSource)
    let .ok plain ← compileInput input | return false
    let hinted := { input with measureHints := #[⟨plainSource, .position 0, some 1⟩] }
    let .ok measured ← compileInput hinted | return false
    return (Ixon.serEnv plain.env).toOption == (Ixon.serEnv measured.env).toOption,
  ioTest "prepared-source preflight rejects unresolved source binder contracts" do
    match checkPreparedSource (constants markedSource) with
    | .error message => return (message.splitOn "unresolved source binder contracts").length > 1
    | .ok _ => return false,
  ioTest "explicit Lean input compiles and mode-checks a valid annotated definition" do
    let tyA : ConstantInfo := .axiomInfo {
      name := `SourceContractDriver.TyA, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
    let defId : ConstantInfo := .defnInfo {
      name := `SourceContractDriver.idOnce, levelParams := []
      type := .forallE `x (.const tyA.name []) (.const tyA.name []) .default
      value := .lam `x (.const tyA.name []) (.bvar 0) .default
      hints := .abbrev, safety := .safe, all := [`SourceContractDriver.idOnce] }
    let .ok contract := SourceContract.ofTelescope defId #[{ binder := .position 0, uses := .linear }]
      | return false
    let .ok out ← compileInput { constants := [(tyA.name, tyA), (defId.name, defId)], contracts := #[contract] }
      | return false
    let some nd := out.env.named.get? (_root_.Ix.Name.fromLeanName defId.name) | return false
    let some c := out.env.getConst? nd.addr | return false
    return out.annotated && _root_.Ix.Compile.BinderData.hasModes c
]

end Tests.Ix.SourceContract.Driver

end
