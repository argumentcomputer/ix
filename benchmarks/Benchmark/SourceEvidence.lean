import Compilatrix.Modular.Report
import Compilatrix.Modular.PreparationTests

/-! Source-unit cost observations on the unchanged modular fixture family.
Full artifact and certificate files are retained separately from clocks. -/

namespace Benchmark.SourceEvidence

open Lean System Compilatrix Compilatrix.Modular Compilatrix.Tools.Check

private def ioCheck := @Compilatrix.Tools.Check.checked

private def writeJson (path : FilePath) (value : Json) : IO Unit :=
  IO.FS.writeFile path (value.pretty 100 ++ "\n")

private def timed (samples : IO.Ref (Array Json)) (label : String)
    (action : Unit → Except String α) : IO α := do
  let start ← IO.monoNanosNow
  let result ← ioCheck (action ())
  let finish ← IO.monoNanosNow
  samples.modify (·.push (Json.mkObj [("phase", toJson label), ("elapsed_ns", toJson (finish - start))]))
  return result

private def widths : String → Except String (List Nat)
  | "smoke" => .ok [32]
  | "reference" => .ok [32, 64, 128, 256, 600]
  | _ => .error "profile must be smoke or reference"

private def sourceBytes (fixture : Fixtures.Case) := IxIR.Encoding.list Input.bytes fixture.inputs

private def storeBytes (built : Built Fixtures.policy) : Except String ByteArray :=
  Wire.encodeStore Fixtures.limits (built.units.map fun unit => (unit.input.name, unit.record))

private structure UnitInput where
  unit : CheckedUnit Fixtures.policy
  imports : List (CheckedUnit Fixtures.policy)

private structure PreparedInput extends UnitInput where
  prepared : Preparation Fixtures.limits Fixtures.policy unit.input imports

private def unitInputs (built : Built Fixtures.policy) : Except String (List UnitInput) :=
  built.units.mapM fun unit => do
    let imports ← unit.input.imports.mapM fun name =>
      match built.units.find? (·.input.name == name) with
      | some imported => .ok imported
      | none => .error "profile import is absent"
    return { unit, imports }

private def unitView (unit : CheckedUnit Fixtures.policy) :=
  (unit.input, unit.interfaces, unit.context.constants, unit.context.blobs,
    unit.context.declarations, unit.context.natBlock, unit.record)

private def sameUnits (first second : List (CheckedUnit Fixtures.policy)) : IO Unit :=
  need (first.map unitView == second.map unitView) "profiled source checking changed complete unit data"

private def retainCase (directory : FilePath) (width : Nat) (fixture : Fixtures.Case)
    (built : Built Fixtures.policy) (compiled : Compiled Fixtures.policy fixture.root .shared) : IO Json := do
  ioCheck (Fixtures.observe compiled fixture.expected)
  let reachable := Report.reachable compiled.program fixture.root
  need (reachable == compiled.program.constants.length) "source profile contains unreachable declarations"
  let source := sourceBytes fixture
  let store ← ioCheck (storeBytes built)
  let artifact := ((Report.snapshot compiled.source).pretty 100 ++ "\n").toUTF8
  IO.FS.createDirAll directory
  IO.FS.writeBinFile (directory / "source.bin") source
  IO.FS.writeBinFile (directory / "certificates.bin") store
  IO.FS.writeBinFile (directory / "artifact.json") artifact
  let summary := Json.mkObj [
    ("width", toJson width), ("units", toJson built.units.length),
    ("source_constants", toJson compiled.program.constants.length),
    ("reachable_source_constants", toJson reachable),
    ("source_root", toJson fixture.root), ("expected_value", toJson fixture.expected),
    ("IxIR1_declarations", toJson compiled.artifact.targetDecls.length),
    ("source_bytes", toJson source.size), ("source_blake3", toJson (Ixon.Address.blake3 source)),
    ("certificate_bytes", toJson store.size), ("certificate_blake3", toJson (Ixon.Address.blake3 store)),
    ("artifact_bytes", toJson artifact.size), ("artifact_blake3", toJson (Ixon.Address.blake3 artifact)),
    ("source_and_IR_execution_agree", toJson true), ("fresh_prepared_unit_data_exact", toJson true)]
  writeJson (directory / "summary.json") summary
  return summary

private def profileCase (directory : FilePath) (width : Nat) : IO (Json × Json) := do
  let samples ← IO.mkRef #[]
  let fixture ← ioCheck (Fixtures.wideCase width)
  let built ← timed samples "cold_build" fun _ => build Fixtures.limits Fixtures.policy fixture.inputs
  let warm ← timed samples "unchanged_build" fun _ => build Fixtures.limits Fixtures.policy fixture.inputs built.cache
  need (warm.observations.all (·.action == .reused)) "unchanged source evidence was regenerated"
  sameUnits built.units warm.units
  let store ← ioCheck (storeBytes built)
  let records ← timed samples "decode_retained_store" fun _ => Wire.decodeStore Fixtures.limits store
  let restored ← timed samples "restore_source_units" fun _ => restore Fixtures.limits Fixtures.policy fixture.inputs records
  sameUnits built.units restored.units
  let _ ← timed samples "aggregate_preflight" fun _ => preflightInputs Fixtures.limits Fixtures.policy fixture.inputs
  let recordSizes ← timed samples "cache_record_preflight" fun _ =>
    built.cache.units.mapM fun unit => unit.record.preflight Fixtures.limits
  need (recordSizes.length == built.units.length) "profiled cache preflight omitted a unit"
  let inputs ← ioCheck (unitInputs built)
  let prepared ← timed samples "prepare_units_fresh" fun _ =>
    inputs.mapM fun entry => prepare Fixtures.limits Fixtures.policy entry.unit.input entry.imports
  let known ← timed samples "prepare_units_with_addresses" fun _ =>
    inputs.mapM fun entry => do
      let facts ← match built.cache.addressEvidence? entry.unit.input with
        | some facts => .ok facts
        | none => .error "profiled canonical-address lookup missed"
      let prepared ← prepareChecked Fixtures.limits Fixtures.policy entry.unit.input entry.imports (some facts)
      return ({ toUnitInput := entry, prepared } : PreparedInput)
  let _ ← timed samples "canonical_address_checks" fun _ => do
    for entry in inputs do
      for (address, constant) in entry.unit.input.constants do
        let actual ← constant.addressChecked.mapError reprStr
        ensure (actual == address) "profiled canonical address differs"
  let _ ← timed samples "usage_checks" fun _ => do
    for (entry, context) in inputs.zip prepared do
      let source := context.source
      for (_, constant) in entry.unit.input.constants do
        let _ ← (Ixon.UsageCheck.checkConstant source.resolve constant Fixtures.policy.checkFuel).mapError reprStr
  let encoded ← timed samples "encode_inputs" fun _ => .ok (built.units.map fun unit => unit.input.bytes)
  need (encoded == built.units.map (·.input.bytes)) "profiled source encoding differs"
  let interfaces ← timed samples "encode_interfaces" fun _ =>
    .ok (inputs.map fun entry => entry.imports.map CheckedUnit.interface)
  need (interfaces == built.units.map (·.interfaces)) "profiled dependency interfaces differ"
  let found ← timed samples "lookup_checked_units" fun _ =>
    (inputs.zip prepared).mapM fun (entry, context) =>
      match built.cache.find? entry.unit.input entry.imports context with
      | some unit => .ok unit
      | none => .error "profiled checked-unit lookup missed"
  sameUnits found built.units
  let fresh ← timed samples "check_units_fresh" fun _ => inputs.mapM fun entry =>
    checkUnit Fixtures.limits Fixtures.policy entry.unit.input entry.imports entry.unit.record
  let reused ← timed samples "check_units_prepared" fun _ => known.mapM fun entry =>
    checkUnitPrepared Fixtures.limits Fixtures.policy entry.unit.input entry.imports entry.prepared entry.unit.record
  sameUnits fresh built.units
  sameUnits reused built.units
  let produced ← timed samples "produce_units_prepared" fun _ => known.mapM fun entry =>
    produceUnitPrepared Fixtures.limits Fixtures.policy entry.unit.input entry.imports entry.prepared
  sameUnits produced built.units
  let observed ← timed samples "unit_observations" fun _ => .ok (built.units.map (observation · .reused))
  need (observed.map (·.key) == built.units.map (·.key)) "profiled observation keys differ"
  let compiled ← timed samples "assembly_total" fun _ => assemble Fixtures.limits Fixtures.policy built.units fixture.root
  let summary ← retainCase directory width fixture built compiled
  IO.println s!"source evidence wide-{width}: {compiled.program.constants.length} reachable declarations, exact prepared records"
  return (summary, Json.mkObj [("width", toJson width), ("phases", toJson (← samples.get))])

def produce (directory : FilePath) (profile : String) : IO Unit := do
  let counts ← ioCheck (widths profile)
  need (!(← directory.pathExists)) "source-evidence requires a new output directory"
  IO.FS.createDirAll directory
  let regressions ← PreparationTests.run
  Report.run (directory / "modular")
  let cases ← counts.mapM fun count => profileCase (directory / "profiles" / s!"wide-{count}") count
  writeJson (directory / "report.json") (Json.mkObj [
    ("format", toJson "compilatrix/source-evidence-reference/1"), ("profile", toJson profile),
    ("policy_preimage", Coverage.byteJson Fixtures.policy.bytes), ("aggregate_limits", toJson (reprStr Fixtures.limits)),
    ("cases", toJson (cases.map (·.1))), ("preparation_regressions", regressions)])
  writeJson (directory / "measurements.json") (Json.mkObj [
    ("format", toJson "compilatrix/source-evidence-cost-observations/1"),
    ("scope", toJson "fixed-order separate calls; diagnostic intervals overlap; no timing threshold"),
    ("cases", toJson (cases.map (·.2)))])
  IO.println s!"source-evidence ok: {counts.length} widths, exact source matrix and prepared unit checks"

def replay (input output : FilePath) : IO Unit := do
  need (!(← output.pathExists)) "source-evidence replay requires a new output directory"
  let bytes ← Wire.readBounded (input / "report.json") Fixtures.limits.maxBytes
  let source ← present (String.fromUTF8? bytes) "retained source-evidence report is not UTF-8"
  let report ← ioCheck (Json.parse source)
  need ((← strField report "format") == "compilatrix/source-evidence-reference/1") "retained source-evidence format differs"
  need ((← field report "policy_preimage") == Coverage.byteJson Fixtures.policy.bytes &&
    (← strField report "aggregate_limits") == reprStr Fixtures.limits) "retained source-evidence policy differs"
  let counts ← ioCheck (widths (← strField report "profile"))
  need ((← field report "preparation_regressions") == (← PreparationTests.run)) "retained preparation regressions differ"
  need ((← arrField report "cases").size == counts.length) "retained source-evidence width count differs"
  IO.FS.createDirAll output
  Report.replay (input / "modular") (output / "modular")
  let mut summaries := []
  let mut measured := []
  for width in counts do
    let directory := input / "profiles" / s!"wide-{width}"
    let fixture ← ioCheck (Fixtures.wideCase width)
    need ((← Wire.readBounded (directory / "source.bin") Fixtures.limits.maxBytes) == sourceBytes fixture)
      "retained source-evidence recipe differs"
    let samples ← IO.mkRef #[]
    let store ← Wire.readBounded (directory / "certificates.bin") Fixtures.limits.maxBytes
    let records ← timed samples "decode_retained_store" fun _ => Wire.decodeStore Fixtures.limits store
    let built ← timed samples "restore_source_units" fun _ => restore Fixtures.limits Fixtures.policy fixture.inputs records
    let compiled ← timed samples "assembly_total" fun _ => assemble Fixtures.limits Fixtures.policy built.units fixture.root
    let warm ← ioCheck (build Fixtures.limits Fixtures.policy fixture.inputs built.cache)
    need (warm.observations.all (·.action == .reused)) "retained source-evidence cache missed"
    sameUnits warm.units built.units
    let destination := output / "profiles" / s!"wide-{width}"
    let summary ← retainCase destination width fixture built compiled
    for file in ["source.bin", "certificates.bin", "artifact.json", "summary.json"] do
      need ((← Wire.readBounded (directory / file) Fixtures.limits.maxBytes) ==
        (← IO.FS.readBinFile (destination / file))) s!"retained source-evidence {file} differs"
    summaries := summary :: summaries
    measured := Json.mkObj [("width", toJson width), ("phases", toJson (← samples.get))] :: measured
  need ((← field report "cases") == toJson summaries.reverse) "retained source-evidence case report differs"
  writeJson (output / "replay.json") (Json.mkObj [
    ("format", toJson "compilatrix/source-evidence-replay/1"), ("widths", toJson counts.length),
    ("all_source_certificate_artifact_bytes_exact", toJson true), ("retained_certificates_rechecked", toJson true)])
  writeJson (output / "measurements.json") (toJson measured.reverse)
  IO.println s!"source-evidence replay ok: {counts.length} widths, exact source artifacts and independent certificate checking"

end Benchmark.SourceEvidence
