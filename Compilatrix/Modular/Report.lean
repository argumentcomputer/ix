import Compilatrix.Modular.Regressions
import Compilatrix.Coverage.Snapshot
import Compilatrix.Tools.Check

/-! Reproducible source-unit fixtures, retained evidence, and fresh replay.
Timings are separate from the deterministic correctness report. -/

namespace Compilatrix.Modular.Report

open Lean System Ixon IxIR

private def ioCheck := @Tools.Check.checked
private def need := Tools.Check.need

private def writeJson (path : FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty 100 ++ "\n")

private def timed (label : String) (action : Unit → Except String α) : IO (α × Json) := do
  let start ← IO.monoNanosNow
  let value ← ioCheck (action ())
  let finish ← IO.monoNanosNow
  return (value, Json.mkObj [("phase", toJson label), ("elapsed_ns", toJson (finish - start))])

def snapshot {constants main config world eraseFuel lowerFuel}
    (compiled : Pipeline.ValidatedCompilation constants main config world eraseFuel lowerFuel) : Json :=
  Json.mkObj [
    ("format", toJson "compilatrix/modular-artifact-comparison/1"),
    ("source_root", toJson main.toHex),
    ("ixir0", Coverage.erasedSnapshot main compiled.erasure.result),
    ("ixir1", Json.mkObj [
      ("artifacts", toJson (compiled.artifact.targetArtifacts.map Coverage.ir1Artifact)),
      ("declarations", Coverage.ir1Entries compiled.artifact.targetDecls),
      ("main", Coverage.byteJson compiled.artifact.main.bytes),
      ("address_map", toJson compiled.artifact.targetAddressMap)])]

def reachable (program : Program) (root : Address) : Nat := Id.run do
  let index := AddressEnv.build program.constants
  let mut seen : Std.HashSet Address := {}
  let mut pending := [root]
  while !pending.isEmpty do
    match pending with
    | [] => pure ()
    | address :: rest =>
        pending := rest
        if !seen.contains address then
          if let some constant := index.get? address then
            seen := seen.insert address
            pending := constantDependencies constant ++ pending
  return seen.size

def observationJson (observation : Observation) : Json :=
  Json.mkObj [
    ("name", toJson observation.name), ("key", toJson observation.key.toHex),
    ("action", toJson observation.action.name), ("candidates", toJson observation.candidates),
    ("proof_obligations", toJson observation.proofObligations),
    ("context_constants", toJson observation.contextConstants),
    ("import_bindings", toJson observation.importBindings),
    ("source_node_work", toJson observation.sourceNodeWork),
    ("query_bytes", toJson observation.queryBytes), ("output_bytes", toJson observation.outputBytes)]

private def checkEditActions (built : Built Fixtures.policy) : IO Unit := do
  for observation in built.observations do
    need (observation.action == if observation.name == "unaffected" then .reused else .produced)
      s!"incorrect dependency-edit reuse for {observation.name}"

private def checkAllHits (built : Built Fixtures.policy) : IO Unit :=
  need (built.observations.all (fun observation => observation.action == .reused))
    "unchanged source evidence was revalidated or regenerated"

private def sourceBytes (fixture : Fixtures.Case) : ByteArray :=
  Encoding.list Input.bytes fixture.inputs

private def storeOf (built : Built Fixtures.policy) : Except String ByteArray :=
  Wire.encodeStore Fixtures.limits (built.units.map (fun unit => (unit.input.name, unit.record)))

structure CaseResult where
  built : Built Fixtures.policy
  summary : Json
  measurements : Json

def runCase (output : FilePath) (fixture : Fixtures.Case)
    (cache : Cache Fixtures.policy := {}) (edited : Bool := false) : IO CaseResult := do
  let policy := Fixtures.policy
  let limits := Fixtures.limits
  let (built, buildTime) ← timed "source_certificates" fun _ => build limits policy fixture.inputs cache
  if edited then checkEditActions built
  else need (built.observations.all (fun observation => observation.action == .produced)) "cold build reused evidence"
  let (compiled, assembleTime) ← timed "assembly_and_IxIR1_lowering" fun _ =>
    assemble limits policy built.units fixture.root
  ioCheck (Fixtures.observe compiled fixture.expected)
  need (reachable compiled.program fixture.root == compiled.program.constants.length)
    "fixture has source declarations outside the selected dependency closure"
  let actual := snapshot compiled.source
  let bytes ← ioCheck (storeOf built)
  let (warm, warmTime) ← timed "unchanged_source_certificates" fun _ => build limits policy fixture.inputs built.cache
  checkAllHits warm
  need ((← ioCheck (storeOf warm)) == bytes) "unchanged cache changed its certificate bytes"
  let (warmCompiled, warmAssemblyTime) ← timed "unchanged_assembly_and_IxIR1_lowering" fun _ =>
    assemble limits policy warm.units fixture.root
  need (snapshot warmCompiled.source == actual) "unchanged modular artifact differs"
  ioCheck (Fixtures.observe warmCompiled fixture.expected)
  let (records, decodeTime) ← timed "decode_retained_store" fun _ => Wire.decodeStore limits bytes
  let (restored, restoreTime) ← timed "check_retained_source_certificates" fun _ =>
    restore limits policy fixture.inputs records
  let (restoredCompiled, restoredAssemblyTime) ← timed "restored_assembly_and_IxIR1_lowering" fun _ =>
    assemble limits policy restored.units fixture.root
  need (snapshot restoredCompiled.source == actual) "retained source evidence changed the artifact"
  need ((← ioCheck (storeOf restored)) == bytes) "restored source evidence changed its bytes"
  ioCheck (Fixtures.observe restoredCompiled fixture.expected)
  let (monolithic, monolithicTime) ← timed "monolithic_compilation" fun _ => .ok
    (Pipeline.compileValidatedWithTrace compiled.program.constants fixture.root
      (compiled.program.config policy) .shared policy.checkFuel policy.eraseFuel
      policy.validateFuel policy.lowerFuel)
  let stats := Ixon.Work.programStats compiled.program.constants
  let monolithicSummary ← match monolithic with
    | .ok comparison =>
        need (snapshot comparison == actual) "modular artifact differs from monolithic compilation"
        pure (Json.mkObj [("status", toJson "accepted"), ("artifact_exact", toJson true)])
    | .error error =>
        need (fixture.name == "wide-600" && stats.certificateCandidates > policy.unit.maxCertificateCandidates)
          s!"unexpected monolithic rejection: {repr error}"
        match error with
        | .resource exceeded =>
            need (exceeded.actual == stats.certificateCandidates &&
              exceeded.limit == policy.unit.maxCertificateCandidates) "wrong monolithic admission boundary"
        | _ => throw (IO.userError "large fixture did not fail the monolithic resource boundary")
        pure (Json.mkObj [("status", toJson "rejected"), ("reason", toJson (reprStr error))])
  if edited then
    let independent ← ioCheck (build limits policy fixture.inputs)
    need ((← ioCheck (storeOf independent)) == bytes) "edited reuse differs from a cold certificate build"
    let independentlyCompiled ← ioCheck (assemble limits policy independent.units fixture.root)
    need (snapshot independentlyCompiled.source == actual) "edited reuse differs from cold compilation"
  IO.FS.createDirAll output
  IO.FS.writeBinFile (output / "source.bin") (sourceBytes fixture)
  IO.FS.writeBinFile (output / "certificates.bin") bytes
  writeJson (output / "artifact.json") actual
  let artifactBytes := (actual.pretty 100 ++ "\n").toUTF8
  let summary := Json.mkObj [
    ("name", toJson fixture.name), ("root", toJson fixture.root.toHex),
    ("expected_value", toJson fixture.expected), ("units", toJson built.units.length),
    ("source_constants", toJson stats.constants), ("certificate_candidates", toJson stats.certificateCandidates),
    ("proof_obligations", toJson (proofObligations compiled.program.constants)),
    ("reachable_source_constants", toJson (reachable compiled.program fixture.root)),
    ("simultaneous_members", toJson compiled.source.memberScope.plan.length),
    ("IxIR1_declarations", toJson compiled.artifact.targetDecls.length),
    ("source_bytes", toJson (sourceBytes fixture).size),
    ("source_blake3", toJson (Address.blake3 (sourceBytes fixture)).toHex),
    ("certificate_store_bytes", toJson bytes.size),
    ("certificate_store_blake3", toJson (Address.blake3 bytes).toHex),
    ("artifact_bytes", toJson artifactBytes.size),
    ("artifact_blake3", toJson (Address.blake3 artifactBytes).toHex),
    ("build", toJson (built.observations.map observationJson)),
    ("unchanged", toJson (warm.observations.map observationJson)),
    ("monolithic", monolithicSummary),
    ("source_and_IR_execution_agree", toJson true),
    ("restored_artifact_exact", toJson true), ("unchanged_artifact_exact", toJson true)]
  let measurements := Json.mkObj [
    ("name", toJson fixture.name),
    ("phases", toJson [buildTime, assembleTime, warmTime, warmAssemblyTime,
      decodeTime, restoreTime, restoredAssemblyTime, monolithicTime])]
  writeJson (output / "summary.json") summary
  return { built, summary, measurements }

def run (output : FilePath) : IO Unit := do
  need (!(← output.pathExists)) "source-modular requires a new output directory"
  let baselineCase ← ioCheck (Fixtures.editCase false)
  let baseline ← runCase (output / "baseline") baselineCase
  let edited ← runCase (output / "edited") (← ioCheck (Fixtures.editCase true)) baseline.built.cache true
  let blobEdited ← runCase (output / "blob-edited") (← ioCheck Fixtures.blobEditCase) baseline.built.cache true
  need (baselineCase.root == (← ioCheck Fixtures.blobEditCase).root) "literal premise edit changed source identity"
  let mutualResult ← runCase (output / "mutual") (← ioCheck Fixtures.mutualCase)
  let small ← runCase (output / "wide-32") (← ioCheck (Fixtures.wideCase 32))
  let large ← runCase (output / "wide-600") (← ioCheck (Fixtures.wideCase 600))
  let regressions ← ioCheck (Regressions.run baselineCase baseline.built)
  let cases := [baseline, edited, blobEdited, mutualResult, small, large]
  let report := Json.mkObj [
    ("format", toJson "compilatrix/modular-source-reference/1"),
    ("policy_preimage", Coverage.byteJson Fixtures.policy.bytes),
    ("monolithic_candidate_limit", toJson Fixtures.policy.unit.maxCertificateCandidates),
    ("comparison_layer", toJson "exact raw/addressed IxIR0, complete IxIR1 artifacts, maps and main"),
    ("cases", toJson (cases.map (·.summary))),
    ("rejections", toJson (regressions.map fun (name, reason) =>
      Json.mkObj [("name", toJson name), ("reason", toJson reason)])),
    ("inclusive_boundaries_passed", toJson true)]
  writeJson (output / "report.json") report
  writeJson (output / "measurements.json") (Json.mkObj [
    ("format", toJson "compilatrix/modular-source-cost-observations/1"),
    ("scope", toJson "one process; each clock includes preparation and checking performed by the named API; no statistical speedup claim"),
    ("cases", toJson (cases.map (·.measurements)))])
  IO.println s!"source-modular ok: {cases.length} cases, {regressions.length} rejected mutations, 611-declaration reachable closure"

private def fixtures : Except String (List Fixtures.Case) := do
  return [← Fixtures.editCase false, ← Fixtures.editCase true, ← Fixtures.blobEditCase,
    ← Fixtures.mutualCase, ← Fixtures.wideCase 32, ← Fixtures.wideCase 600]

def replay (input output : FilePath) : IO Unit := do
  need (!(← output.pathExists)) "source-modular replay requires a new output directory"
  let cases ← ioCheck fixtures
  let mut measurements := []
  let mut baselineCache : Cache Fixtures.policy := {}
  for fixture in cases do
    let directory := input / fixture.name
    need ((← Wire.readBounded (directory / "source.bin") Fixtures.limits.maxBytes) == sourceBytes fixture)
      s!"{fixture.name}: retained source recipe differs"
    let bytes ← Wire.readBounded (directory / "certificates.bin") Fixtures.limits.maxBytes
    let (records, decodeTime) ← timed "decode_retained_store" fun _ => Wire.decodeStore Fixtures.limits bytes
    let (restored, checkTime) ← timed "check_retained_source_certificates" fun _ =>
      restore Fixtures.limits Fixtures.policy fixture.inputs records
    let (compiled, assembleTime) ← timed "assembly_and_IxIR1_lowering" fun _ =>
      assemble Fixtures.limits Fixtures.policy restored.units fixture.root
    ioCheck (Fixtures.observe compiled fixture.expected)
    let actual := snapshot compiled.source
    let retainedArtifact ← Wire.readBounded (directory / "artifact.json") Fixtures.limits.maxBytes
    need ((actual.pretty 100 ++ "\n").toUTF8 == retainedArtifact) s!"{fixture.name}: replayed artifact differs"
    need ((← ioCheck (storeOf restored)) == bytes) s!"{fixture.name}: replayed certificate bytes differ"
    let warm ← ioCheck (build Fixtures.limits Fixtures.policy fixture.inputs restored.cache)
    checkAllHits warm
    if fixture.name == "baseline" then baselineCache := restored.cache
    if fixture.name == "edited" || fixture.name == "blob-edited" then
      let changed ← ioCheck (build Fixtures.limits Fixtures.policy fixture.inputs baselineCache)
      checkEditActions changed
      need ((← ioCheck (storeOf changed)) == bytes) "fresh restored cache has incorrect dependency invalidation"
    IO.FS.createDirAll (output / fixture.name)
    writeJson (output / fixture.name / "artifact.json") actual
    IO.FS.writeBinFile (output / fixture.name / "certificates.bin") bytes
    measurements := Json.mkObj [("name", toJson fixture.name),
      ("phases", toJson [decodeTime, checkTime, assembleTime])] :: measurements
  writeJson (output / "replay.json") (Json.mkObj [
    ("format", toJson "compilatrix/modular-source-replay/1"),
    ("cases", toJson cases.length), ("all_artifacts_exact", toJson true),
    ("all_certificate_bytes_exact", toJson true), ("dependency_edits_rechecked", toJson true)])
  writeJson (output / "measurements.json") (toJson measurements.reverse)
  IO.println s!"source-modular replay ok: {cases.length} independently checked cases"

end Compilatrix.Modular.Report
