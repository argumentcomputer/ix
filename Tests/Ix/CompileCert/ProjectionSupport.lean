import Tests.Ix.CompileCert.SourceModels
import Tests.Ix.CompileCert.Stored

namespace Tests.Ix.CompileCert.ProjectionSupport

open _root_.Ix.CompileCert

def supportLabel : SupportError → String
  | .conflictingNames => "conflicting support names"
  | .setup reason => reason
  | .checking error position => s!"kernel support check {position}: {error}"
  | .changedOriginal => "changed original installed row"

def runRoot (env : Lean.Environment) (produced : Ixon.Env) (root : Lean.Name) : IO Unit := do
    let input ← IO.ofExcept (Stored.rootInput env produced root)
    let accepted ← match checkCompiled input with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError s!"original association {root}: {Compiled.declineLabel error}")
    let installed ← match installSourceNormalized input.source input.roots with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError s!"source normalization {root}: {SourceModels.label error}")
    let some originalCI := input.source.find root | throw (IO.userError "missing original root")
    let .defn header body hint ← IO.ofExcept (exportSourceEntry originalCI)
      | throw (IO.userError "source root not a definition")
    let some replacement := installed.declarations.find? (fun declaration =>
        match declaration with | .defnDecl h _ _ => decide (h.name = header.name) | _ => false)
      | throw (IO.userError "normalized replacement missing")
    let some equation := installed.declarations.find? (fun declaration =>
        match declaration with
        | .thmDecl h _ => decide (h.name = header.name.str "_source_constructor_equation")
        | _ => false)
      | throw (IO.userError "source-owned equation missing")
    let projection ← IO.ofExcept (checkSourceProjectionReceipt input.source
      (.defnDecl header body hint) replacement equation)
    let coverage ← match checkSourceConstructorCover installed projection.site with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError s!"source coverage: {SourceModels.label error}")
    let constructor ← IO.ofExcept (checkSourceCoverInstalledShape coverage)
    let receipt ← IO.ofExcept (checkSourceProjectionInstalled projection constructor)
    let cx : ExportContext := ⟨input.source, input.map, accepted.pins⟩
    let mappings ← input.source.declarations.mapM fun ci => do
      let targetName ← IO.ofExcept (cx.name ci.name)
      pure (sourceName ci.name, targetName)
    let helperMappings ← IO.ofExcept (proposeSourceHelperBindings installed.modelProposal mappings)
    let names := sourceAndHelperNames mappings (helperMappings ++ installed.semanticSupport.nameBindings)
    let support ← IO.ofExcept (([equation, .thmDecl coverage.header coverage.value]).mapM
      (proposeRenamedSupport names))
    let bundle ← match checkAdmittedSupport accepted.toAdmittedArtifact support.toArray with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError s!"target support {root}: {supportLabel error}")
    let endpoint := readInstalledEquationFrame bundle.env (names receipt.data.equation.name)
      (projection.site.owner.numParams + projection.site.ctor.numFields)
    let originalIdentity := checkInstalledAssociation accepted.env bundle.env id
    IO.println s!"SUPPORT {root}: source={coverage.env.consts.length}, target={bundle.env.consts.length}, original-preserved={decide (InstalledRowsPreserved accepted.env bundle.env)}, equation-frame={endpoint.isSome}"
    IO.println s!"ORIGINAL-SEMANTIC-IDENTITY {root}: {repr originalIdentity}"
    IO.println s!"REMAINING-CHECKS {root}: False={checkInstalledPin coverage.env names _root_.Ix.Kernel.falseName 0} Eq={checkInstalledPin coverage.env names _root_.Ix.Kernel.eqName 1} availability={repr (checkInstalledComparisonAvailability coverage.env bundle.env names)} eta={repr (checkInstalledEtaAssociations coverage.env bundle.env names)} universe-links={repr (checkInstalledRuleLevelLinks coverage.env bundle.env names)}"
    IO.println s!"CHECKS names={decide (SemanticNamesAgree accepted names)} telescopes={checkTelescopes coverage.env bundle.env names} types={checkInstalledTypes coverage.env bundle.env names} definitions={checkInstalledDefinitions coverage.env bundle.env names} caps={checkInstalledCapabilities coverage.env bundle.env names} recursors={checkInstalledRecursors coverage.env bundle.env names} constructors={checkInstalledConstructors coverage.env bundle.env names} aggregate={repr (checkSupportedArtifactInstalledAssociation accepted bundle coverage.env names)}"
    for entry in coverage.env.consts do
      let mapped := names entry.name
      match bundle.env.find? mapped with
      | none => IO.println s!"MISSING source={entry.name} mapped={mapped}"
      | some targetEntry =>
        unless entry.toConstantVal.levelParams.length == targetEntry.toConstantVal.levelParams.length do
          IO.println s!"ARITY source={entry.name} source-levels={repr entry.toConstantVal.levelParams} target-levels={repr targetEntry.toConstantVal.levelParams}"
        let typeCheck := checkInstalledMemberExpr coverage.env bundle.env names entry.name
          entry.toConstantVal.type targetEntry.toConstantVal.type
        unless typeCheck == some true do
          IO.println s!"TYPE source={entry.name} mapped={mapped} result={repr typeCheck} source-type={repr entry.toConstantVal.type} target-type={repr targetEntry.toConstantVal.type}"
    unless endpoint.isSome do throw (IO.userError "target equation endpoint missing")
    unless originalIdentity == some true do
      throw (IO.userError "original artifact semantic identity remains unresolved")
    unless checkSupportedArtifactInstalledAssociation accepted bundle coverage.env names == some true do
      throw (IO.userError s!"full installed support association remains unresolved for {root}")

def run (path : String) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  IO.println s!"artifact {path}; bytes={bytes.size}; Blake3={Address.blake3 bytes}"
  let produced ← IO.ofExcept (Ixon.deEnv bytes)
  let env ← getCompileEnv #[Compiled.prefixName]
  let mut failures := 0
  for root in [Compiled.prefixName ++ `Node.val, Compiled.prefixName ++ `Node.kids] do
    try
      runRoot env produced root
      IO.println s!"PASS: full projection support association {root}"
    catch error =>
      failures := failures + 1
      IO.println s!"FAIL: projection support {root}: {error}"
  IO.println s!"projection support coverage: 2/2 outcomes; failures={failures}"
  unless failures == 0 do throw (IO.userError "full projection support association failed")

end Tests.Ix.CompileCert.ProjectionSupport
