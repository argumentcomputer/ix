import Compilatrix.Modular.Report
import Compilatrix.IxIR1.ReaddressIndexTests

/-! Modular assembly observations with complete retained artifacts. The
existing six-case source evidence matrix remains byte-for-byte comparable;
the additional width series separates addressing from the other assembly
operations and compares the retained list implementation on the same input. -/

namespace Benchmark.Assembly

open Lean System Compilatrix Compilatrix.Modular Compilatrix.Tools.Check

private def ioCheck := @Compilatrix.Tools.Check.checked

private def writeJson (path : FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty 100 ++ "\n")

private def timed (samples : IO.Ref (Array Json)) (label : String)
    (action : Unit → Except String α) : IO α := do
  let start ← IO.monoNanosNow
  let value ← ioCheck (action ())
  let finish ← IO.monoNanosNow
  samples.modify (·.push (Json.mkObj [("phase", toJson label), ("elapsed_ns", toJson (finish - start))]))
  return value

private def widths (profile : String) : Except String (List Nat) :=
  match profile with
  | "smoke" => .ok [32]
  | "reference" => .ok [32, 64, 128, 256, 600]
  | _ => .error "profile must be smoke or reference"

private def sourceBytes (fixture : Fixtures.Case) : ByteArray :=
  IxIR.Encoding.list Input.bytes fixture.inputs

private def storeBytes (built : Built Fixtures.policy) : Except String ByteArray :=
  Wire.encodeStore Fixtures.limits (built.units.map fun unit => (unit.input.name, unit.record))

private def rawSnapshot (declarations : List (Ixon.Address × IxIR1.Decl)) (main : IxIR1.Code) : Json :=
  Json.mkObj [("declarations", Coverage.ir1Entries declarations), ("main", Coverage.byteJson main.bytes)]

private def retainCase (directory : FilePath) (width : Nat) (fixture : Fixtures.Case)
    (built : Built Fixtures.policy) (compiled : Compiled Fixtures.policy fixture.root .shared) : IO Json := do
  ioCheck (Fixtures.observe compiled fixture.expected)
  let reachable := Report.reachable compiled.program fixture.root
  need (reachable == compiled.program.constants.length) "profile contains unreachable source declarations"
  let source := sourceBytes fixture
  let store ← ioCheck (storeBytes built)
  let artifact := Report.snapshot compiled.source
  let lowering := compiled.source.lowering
  let raw := rawSnapshot lowering.raw lowering.mainCode
  let addressed := IxIR1.ReaddressIndexTests.snapshot lowering.result
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "source.bin") source
  IO.FS.writeBinFile (directory / "certificates.bin") store
  for (name, value) in [("artifact.json", artifact), ("raw.json", raw), ("addressed.json", addressed)] do
    writeJson (directory / name) value
  let fileIdentity := fun value =>
    let bytes := (value.pretty 100 ++ "\n").toUTF8
    Json.mkObj [("bytes", toJson bytes.size), ("blake3", toJson (Ixon.Address.blake3 bytes))]
  let summary := Json.mkObj [
    ("width", toJson width), ("units", toJson built.units.length),
    ("source_constants", toJson compiled.program.constants.length), ("reachable_source_constants", toJson reachable),
    ("raw_IxIR1_declarations", toJson lowering.raw.length),
    ("emitted_IxIR1_declarations", toJson lowering.result.declarations.length),
    ("source_root", toJson fixture.root), ("expected_value", toJson fixture.expected),
    ("source_bytes", toJson source.size), ("source_blake3", toJson (Ixon.Address.blake3 source)),
    ("certificate_bytes", toJson store.size), ("certificate_blake3", toJson (Ixon.Address.blake3 store)),
    ("artifact", fileIdentity artifact), ("raw", fileIdentity raw), ("addressed", fileIdentity addressed),
    ("reference_addressing_exact", toJson true), ("source_and_IR_execution_agree", toJson true)]
  writeJson (directory / "summary.json") summary
  return summary

private def profileCase (directory : FilePath) (width : Nat) : IO (Json × Json) := do
  let samples ← IO.mkRef #[]
  let fixture ← ioCheck (Fixtures.wideCase width)
  let policy := Fixtures.policy
  let built ← timed samples "build_source_units" fun _ => build Fixtures.limits policy fixture.inputs
  let program ← timed samples "program_preflight" fun _ => do
    let program ← programOf Fixtures.limits policy built.units
    ensure ((candidates program.constants).contains fixture.root) "main is not an exported source declaration"
    return program
  let ectx ← timed samples "source_context" fun _ => .ok (program.source policy)
  let erasure ← timed samples "erasure_and_IxIR0_addressing" fun _ =>
    (EraseAddressed.runWithTrace (EraseValidator.eraseCtxOf ectx) program.constants
      (.ref fixture.root) policy.eraseFuel).mapError reprStr
  let context : Context := {
    constants := program.constants, blobs := program.blobs,
    declarations := erasure.result.raw, natBlock := program.natBlock }
  let evidence ← timed samples "imported_evidence" fun _ => importedEvidence context built.units
  let _ ← timed samples "close_members" fun _ => closeMembers context evidence.2 context.scope.plan
  let entry ← timed samples "entry_certificate" fun _ =>
    (@EraseValidator.certifySharedClosedExpr context.scope context.source context.target
      (@EraseValidator.CoverageDB.oracle context.scope _ _ evidence.1)
      (Pipeline.validatedMainFrame fixture.root) Pipeline.validatedMainSource
      policy.eraseFuel policy.validateFuel).mapError reprStr
  need (EraseValidator.CertifiedSharedExpr.target (scope := context.scope) entry ==
    (.ref fixture.root : IxIR0.Expr)) "profiled entry certificate differs"
  let raw ← timed samples "IxIR1_raw_lowering" fun _ =>
    match (IxIR1.Lower.lowerAllIndexedAction erasure.result.declarations erasure.result.main
        .shared policy.lowerFuel).run {} with
    | .error message _ => .error message
    | .ok value _ => .ok value
  let reserved := IxIR1.Lower.constructorIdentities erasure.result.declarations
  let addressed ← timed samples "IxIR1_indexed_addressing" fun _ => IxIR1.ReaddressAll.run reserved raw.1 raw.2
  let reference ← timed samples "IxIR1_reference_addressing" fun _ =>
    IxIR1.ReaddressAll.runReferenceCertified reserved raw.1 raw.2
  need (IxIR1.ReaddressIndexTests.snapshot addressed == IxIR1.ReaddressIndexTests.snapshot reference.val)
    "indexed addressing differs from the reference builder"
  let prepared ← timed samples "prepare_audit_indexes" fun _ => .ok (addressed.prepareAudit raw.1)
  let semantic ← timed samples "indexed_semantic_audit" fun _ => .ok (prepared.val.semanticAudit addressed raw.1 raw.2)
  let exactImage ← timed samples "indexed_exact_image_audit" fun _ => .ok (prepared.val.rebuildImageAudit addressed raw.1 raw.2)
  let referenceSemantic ← timed samples "reference_semantic_audit" fun _ => .ok (addressed.semanticAudit raw.1 raw.2)
  let referenceExact ← timed samples "reference_exact_source_audit" fun _ => .ok (addressed.rebuildSemanticAudit raw.1 raw.2)
  need (semantic && exactImage && referenceSemantic && referenceExact) "profiled address audit failed"
  let compiled ← timed samples "assembly_total" fun _ => assemble Fixtures.limits policy built.units fixture.root
  let lowering := compiled.source.lowering
  need (rawSnapshot raw.1 raw.2 == rawSnapshot lowering.raw lowering.mainCode)
    "profiled lowering differs from ordinary assembly"
  need (IxIR1.ReaddressIndexTests.snapshot addressed == IxIR1.ReaddressIndexTests.snapshot lowering.result)
    "profiled addressing differs from ordinary assembly"
  need (Coverage.erasedSnapshot fixture.root erasure.result ==
    Coverage.erasedSnapshot fixture.root compiled.source.erasure.result) "profiled erasure differs from ordinary assembly"
  let summary ← retainCase directory width fixture built compiled
  IO.println s!"assembly wide-{width}: {program.constants.length} reachable declarations, exact reference artifact"
  return (summary, Json.mkObj [("width", toJson width), ("phases", toJson (← samples.get))])

def produce (directory : FilePath) (profile : String) : IO Unit := do
  let counts ← ioCheck (widths profile)
  need (!(← directory.pathExists)) "assembly-scaling requires a new output directory"
  IO.FS.createDirAll directory
  let regressions ← IxIR1.ReaddressIndexTests.run
  Report.run (directory / "modular")
  let results ← counts.mapM fun count => profileCase (directory / "profiles" / s!"wide-{count}") count
  writeJson (directory / "report.json") (Json.mkObj [
    ("format", toJson "compilatrix/assembly-scaling/1"), ("profile", toJson profile),
    ("policy_preimage", Coverage.byteJson Fixtures.policy.bytes),
    ("aggregate_limits", toJson (reprStr Fixtures.limits)),
    ("cases", toJson (results.map (·.1))), ("address_regressions", regressions)])
  writeJson (directory / "measurements.json") (Json.mkObj [
    ("format", toJson "compilatrix/assembly-scaling-cost-observations/1"),
    ("scope", toJson "fixed-order observations; separate calls; overlapping checks are not additive; no timing threshold"),
    ("cases", toJson (results.map (·.2)))])
  IO.println s!"assembly-scaling ok: {counts.length} widths, complete source matrix and reference address comparisons"

private def retainedEqual (input output : FilePath) : IO Unit := do
  for name in ["source.bin", "certificates.bin", "artifact.json", "raw.json", "addressed.json", "summary.json"] do
    need ((← Wire.readBounded (input / name) Fixtures.limits.maxBytes) == (← IO.FS.readBinFile (output / name)))
      s!"retained assembly {name} differs"

def replay (input output : FilePath) : IO Unit := do
  need (!(← output.pathExists)) "assembly-scaling replay requires a new output directory"
  let reportBytes ← Wire.readBounded (input / "report.json") Fixtures.limits.maxBytes
  let reportText ← present (String.fromUTF8? reportBytes) "retained assembly report is not UTF-8"
  let report ← ioCheck (Json.parse reportText)
  need ((← strField report "format") == "compilatrix/assembly-scaling/1") "retained assembly format differs"
  let profile ← strField report "profile"
  let counts ← ioCheck (widths profile)
  need ((← field report "policy_preimage") == Coverage.byteJson Fixtures.policy.bytes &&
    (← strField report "aggregate_limits") == reprStr Fixtures.limits) "retained assembly policy differs"
  let regressions ← IxIR1.ReaddressIndexTests.run
  need ((← field report "address_regressions") == regressions) "retained address regression matrix differs"
  let rows ← arrField report "cases"
  need (rows.size == counts.length) "retained assembly width inventory differs"
  IO.FS.createDirAll output
  Report.replay (input / "modular") (output / "modular")
  let mut observations : Array Json := #[]
  for index in [:counts.length] do
    let width := counts[index]!
    let source := input / "profiles" / s!"wide-{width}"
    let destination := output / "profiles" / s!"wide-{width}"
    let fixture ← ioCheck (Fixtures.wideCase width)
    need ((← Wire.readBounded (source / "source.bin") Fixtures.limits.maxBytes) == sourceBytes fixture)
      "retained assembly source recipe differs"
    let bytes ← Wire.readBounded (source / "certificates.bin") Fixtures.limits.maxBytes
    let samples ← IO.mkRef #[]
    let records ← timed samples "decode_retained_store" fun _ => Wire.decodeStore Fixtures.limits bytes
    let restored ← timed samples "check_retained_units" fun _ => restore Fixtures.limits Fixtures.policy fixture.inputs records
    let compiled ← timed samples "assembly_total" fun _ =>
      assemble Fixtures.limits Fixtures.policy restored.units fixture.root
    let lowering := compiled.source.lowering
    let reference ← ioCheck (IxIR1.ReaddressAll.runReferenceCertified
      lowering.result.reserved lowering.raw lowering.mainCode)
    need (IxIR1.ReaddressIndexTests.snapshot reference.val == IxIR1.ReaddressIndexTests.snapshot lowering.result)
      "retained assembly differs from the reference addresser"
    let summary ← retainCase destination width fixture restored compiled
    need (summary == rows[index]!) "retained assembly summary differs"
    retainedEqual source destination
    observations := observations.push (Json.mkObj [("width", toJson width), ("phases", toJson (← samples.get))])
  writeJson (output / "replay.json") (Json.mkObj [
    ("format", toJson "compilatrix/assembly-scaling-replay/1"), ("profile", toJson profile),
    ("widths", toJson counts), ("all_artifact_and_certificate_bytes_exact", toJson true),
    ("reference_addressing_exact", toJson true)])
  writeJson (output / "measurements.json") (toJson observations)
  IO.println s!"assembly-scaling replay ok: {counts.length} widths and the complete source evidence matrix"

end Benchmark.Assembly
