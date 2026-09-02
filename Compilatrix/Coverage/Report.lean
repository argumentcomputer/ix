import Compilatrix.Coverage.Run
import Compilatrix.Coverage.StdContact
import Compilatrix.IxIR1.WellModedGen

/-! The production negative boundary and the pre-existing generated IR corpus
accompany the positive synthetic Ixon cases in one deterministic report. -/

namespace Compilatrix.Coverage

open Lean Compilatrix.Ixon

deriving instance ToJson for Catalog.Stats
deriving instance ToJson for IxIR1.WellModedGen.Summary

private def productionInput (loaded : Catalog.Loaded)
    (constants : List (Address × Constant)) (root : Address) : Except String Json := do
  let stored := loaded.pieces.toList.flatMap (·.constants.toList)
  let records ← constants.mapM fun (address, constant) => do
    let some record := stored.find? (·.address == address)
      | throw "production source snapshot lost an original byte record"
    if record.constant != constant then throw "production source snapshot changed a constant"
    return Json.mkObj [("key", toJson address), ("bytes", byteJson record.bytes)]
  let references := constants.flatMap (fun entry => CatalogContactFixture.dependencies entry.2)
  let blobs := loaded.blobs.filter (fun entry => references.contains entry.1)
  return Json.mkObj [
    ("root", toJson root), ("constants", toJson records),
    ("blob_inputs", toJson (blobs.map fun (address, bytes) =>
      Json.mkObj [("key", toJson address), ("bytes", byteJson bytes)])),
    ("provenance", Json.mkObj [
      ("members_root", toJson loaded.manifest.membersRoot),
      ("content_root", toJson loaded.manifest.contentRoot),
      ("piece_hash", toJson CatalogContactFixture.expectedPieceHash),
      ("toolchain", toJson "leanprover/lean4:v4.33.1"),
      ("source_pin", toJson "git:ix@6f18ea907b78d06f7dc0917c43beb385561c35f4")]),
    ("check_fuel", toJson UsageCheck.defaultFuel), ("limits", toJson Pipeline.defaultLimits)]

private def productionCase (loaded : Catalog.Loaded) (name rootKind : String)
    (constants : List (Address × Constant)) (root rejected : Address)
    (details : Json) : Except String CaseResult := do
  if !CatalogContactFixture.freezesAt constants rejected then
    throw s!"{name}: production freezeNeeded rejection drifted"
  let input ← productionInput loaded constants root
  let failure := Json.mkObj [("stage", toJson "usage"), ("code", toJson "freezeNeeded"),
    ("root", toJson rejected), ("message", Json.null)]
  return {
    name
    row := Json.mkObj [
      ("name", toJson name), ("origin", toJson "production-ixon"),
      ("root_kind", toJson rootKind), ("root", toJson root),
      ("source_constants", toJson constants.length), ("last_accepted_stage", toJson "ixon"),
      ("rejection", failure), ("observation", Json.null),
      ("ir1_root", Json.null), ("hpt_roots", Json.null), ("features", Json.null),
      ("snapshot", toJson s!"{name}.json"), ("object", Json.null)]
    snapshot := Json.mkObj [("format", toJson "compilatrix/source-case/1"),
      ("input", input), ("compilation", Json.null), ("observations", failure), ("details", details)] }

def productionCases (loaded : Catalog.Loaded) : Except String (List CaseResult) := do
  let some rejected := loaded.constants.find? (fun entry =>
      entry.1.toHex == CatalogContactFixture.expectedPipelineAddress)
    | throw "production contact lost the rejected constant"
  let closure := CatalogContactFixture.dependencyClosure loaded.constants rejected.1
  if closure.length != 17 || !CatalogContactFixture.isClosed loaded.constants closure ||
      CatalogContactFixture.dependencyClosure closure rejected.1 != closure then
    throw "production dependency closure drifted"
  for entry in closure do
    if entry.1 != rejected.1 && CatalogContactFixture.isClosed loaded.constants
        (closure.filter (fun candidate => candidate.1 != entry.1)) then
      throw "production dependency closure contains a removable constant"
  -- Missing definitions alter telescope/erasure decisions, so deleting all
  -- dependencies is not a valid minimization of this production failure.
  match Pipeline.checkProgram [rejected] with
  | .error (.usage root (.typeBinderRuntimeUse .linear)) =>
      if root != rejected.1 then throw "isolated production rejection changed root"
  | _ => throw "isolated production context diagnostic drifted"
  let full ← productionCase loaded "std-contact" "environment" loaded.constants
    loaded.manifest.contentRoot rejected.1 (toJson loaded.stats)
  let minimized ← productionCase loaded "std-failure-closure" "constant" closure rejected.1 rejected.1
    (Json.mkObj [
      ("parent_environment", toJson loaded.manifest.contentRoot),
      ("original_constants", toJson loaded.constants.length),
      ("closure_keys", toJson (closure.map (·.1))),
      ("closed", toJson true), ("single_deletion_minimal", toJson true),
      ("isolated_rejection", Json.mkObj [
        ("code", toJson "typeBinderRuntimeUse"), ("uses", toJson "linear")])])
  return [full, minimized]

def generatedCorpus : Except String Json := do
  match IxIR1.WellModedGen.checkCorpus with
  | some failure => throw s!"generated IxIR0 corpus failed: {repr failure}"
  | none =>
      return Json.mkObj [
        ("origin", toJson "generated-ixir0"),
        ("seed", toJson IxIR1.WellModedGen.defaultSeed),
        ("summary", toJson (IxIR1.WellModedGen.summarize)),
        ("property", toJson "IxIR0/IxIR1 value agreement and result reclamation, or exact lowering rejection")]

def report (results : List CaseResult) (corpus : Json) : Json :=
  Json.mkObj [
    ("format", toJson "compilatrix/source-coverage/1"),
    ("policy_version", toJson (1 : Nat)),
    ("source_cases", toJson (results.map (·.row))),
    ("generated_ir_corpus", corpus)]

end Compilatrix.Coverage
