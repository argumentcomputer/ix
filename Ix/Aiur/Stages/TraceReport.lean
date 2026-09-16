module

public import Lean.Data.Json
public import Ix.Aiur.Compiler
public import Ix.Aiur.Stages.TracePlan

public section

namespace Aiur.TraceReport

open Lean Bytecode TracePlan

private def spanJson (span : Span) : Json :=
  Json.mkObj [("start", toJson span.start), ("size", toJson span.size)]

private def layoutJson (layout : Bytecode.FunctionLayout) : Json :=
  Json.mkObj [
    ("inputs", toJson layout.inputSize),
    ("selectors", toJson layout.selectors),
    ("auxiliaries", toJson layout.auxiliaries),
    ("lookups", toJson layout.lookups),
    ("main_width", toJson layout.width)]

private def spaceJson (space : BranchSpace) : Json :=
  Json.mkObj [
    ("auxiliaries", spanJson space.auxiliaries),
    ("lookups", spanJson space.lookups),
    ("seeds", spanJson space.seeds)]

private def readJson (read : ExternalRead) : Json :=
  let (kind, metadata) : String × List (String × Json) := match read.kind with
    | .callResult callee => ("call_result", [("callee", toJson callee)])
    | .returnedCall callee => ("returned_call", [("callee", toJson callee)])
    | .storePointer width => ("store_pointer", [("memory_width", toJson width)])
    | .loadValues width => ("load_values", [("memory_width", toJson width)])
    | .ioInfo => ("io_info", [])
    | .ioValues length => ("io_values", [("length", toJson length)])
    | .bigUintResults => ("big_uint_results", [])
  Json.mkObj ([("kind", toJson kind), ("inputs", toJson read.inputs),
    ("seed", spanJson read.seed)] ++ metadata)

mutual
  private partial def blockJson (block : BlockPlan) : Json :=
    Json.mkObj [
      ("operations", toJson block.operations),
      ("control", controlJson block.control)]

  private partial def controlJson (control : Control) : Json :=
    match control with
    | .returnRow selector values => Json.mkObj [
        ("kind", toJson "return"), ("selector", toJson selector), ("values", toJson values)]
    | .yieldRow selector values => Json.mkObj [
        ("kind", toJson "yield"), ("selector", toJson selector), ("values", toJson values)]
    | .branch discriminant arms fallback witnesses space =>
      Json.mkObj ([("kind", toJson "match")] ++
        branchJson discriminant arms fallback witnesses space)
    | .continueWith discriminant arms fallback witnesses space merges columns continuation =>
      Json.mkObj ([("kind", toJson "match_continue"),
        ("merge_values", toJson merges), ("merge_columns", spanJson columns),
        ("continuation", blockJson continuation)] ++
        branchJson discriminant arms fallback witnesses space)

  private partial def branchJson (discriminant : ValueId) (arms : Array (G × BlockPlan))
      (fallback : Option BlockPlan) (witnesses : Span) (space : BranchSpace) : List (String × Json) :=
    [("discriminant", toJson discriminant),
     ("arms", Json.arr <| arms.map fun (value, block) =>
       Json.mkObj [("value", toJson (toString value.n)), ("block", blockJson block)]),
     ("fallback", (fallback.map blockJson).getD Json.null),
     ("default_witnesses", spanJson witnesses),
     ("shared", spaceJson space)]
end

private def operationJson (plan : FunctionPlan) (op : Operation) : Json :=
  Json.mkObj [
    ("index", toJson op.index),
    ("bytecode", toJson (reprStr op.opcode)),
    ("inputs", toJson op.inputs),
    ("outputs", toJson op.outputs),
    ("output_degrees", toJson op.outputDegrees),
    ("auxiliaries", spanJson op.auxiliaries),
    ("lookups", spanJson op.lookups),
    ("external_read", (op.externalRead.map readJson).getD Json.null),
    ("row_needed", toJson (plan.rowOperations.contains op.index)),
    ("preparation_needed", toJson (plan.preparationOperations.contains op.index)),
    ("alias_check_needed", toJson (plan.aliasCheckOperations.contains op.index))]

private def functionJson (aliases : Array String) (plan : FunctionPlan) : Json :=
  let reads := plan.operations.filter (·.externalRead.isSome)
  let preparationArithmetic := plan.operations.filter fun op =>
    plan.preparationOperations.contains op.index && op.externalRead.isNone
  Json.mkObj [
    ("index", toJson plan.index),
    ("names", toJson aliases),
    ("layout", layoutJson plan.layout),
    ("output_size", toJson plan.outputSize),
    ("real_rows", Json.null),
    ("static_operation_sites", toJson plan.operations.size),
    ("static_external_read_sites", toJson reads.size),
    ("preparation_arithmetic_sites", toJson (preparationArithmetic.map (·.index))),
    ("row_operation_sites", toJson plan.rowOperations),
    ("preparation_operation_sites", toJson plan.preparationOperations),
    ("alias_check_operation_sites", toJson plan.aliasCheckOperations),
    ("singleton_main_bytes_per_real_row", toJson (8 * plan.layout.width)),
    ("canonical_seed_words", toJson plan.seedWords),
    ("canonical_seed_bytes", toJson plan.canonicalSeedBytes),
    ("guarded_u8_seed_bytes", toJson plan.guardedU8SeedBytes),
    ("guarded_u8_requires_payload_checks", toJson true),
    ("values", Json.arr <| plan.values.map fun value => Json.mkObj [
      ("degree", toJson value.degree), ("producer", toJson value.producer),
      ("input", toJson value.input), ("row_inputs", toJson value.rowInputs),
      ("preparation_inputs", toJson value.preparationInputs)]),
    ("operations", Json.arr (plan.operations.map (operationJson plan))),
    ("body", blockJson plan.body)]

private def aliases (compiled : CompiledToplevel) : Array (Array String) :=
  let names := compiled.nameMap.fold
    (init := Array.replicate compiled.bytecode.functions.size (#[] : Array String))
    fun names name index => names.set! index (names[index]!.push (toString name))
  names.map fun names => names.qsort (· < ·)

private def circuitJson (top : Toplevel) (names : Array (Array String))
    (index : Nat) (circuit : Circuit) : Json := Id.run do
  let mut selectorBase := circuit.layout.inputSize
  let mut members := #[]
  for member in circuit.members do
    members := members.push <| Json.mkObj [
      ("function", toJson member), ("names", toJson names[member]!),
      ("selector_base", toJson selectorBase),
      ("auxiliary_base", toJson (circuit.layout.inputSize + circuit.layout.selectors)),
      ("real_rows", Json.null)]
    selectorBase := selectorBase + top.functions[member]!.layout.selectors
  let name := if circuit.members.size == 1 then
      (names[circuit.members[0]!]![0]?).getD s!"function_{circuit.members[0]!}"
    else circuit.name
  let branchless := if circuit.members.size == 1 && circuit.layout.selectors == 1 then
      match top.functions[circuit.members[0]!]!.body.ctrl with
      | .return .. | .yield .. => true
      | _ => false
    else false
  return Json.mkObj [
    ("index", toJson index), ("name", toJson name),
    ("layout", layoutJson circuit.layout), ("branchless", toJson branchless),
    ("members", Json.arr members), ("real_rows", Json.null), ("padded_height", Json.null)]

/-- A deterministic static inventory. Dynamic row weights and timings are
absent explicitly; the report is not a compatibility digest or a benchmark. -/
def program (label : String) (compiled : CompiledToplevel) : Except String Json := do
  let top := compiled.bytecode
  let plan ← TracePlan.program top
  let names := aliases compiled
  let functions := plan.functions.filterMap fun plan => plan.map fun plan =>
    functionJson names[plan.index]! plan
  let memories := top.memorySizes.mapIdx fun index width => Json.mkObj [
    ("index", toJson (top.circuits.size + index)), ("kind", toJson "memory"),
    ("value_width", toJson width), ("main_width", toJson (width + 3)),
    ("canonical_seed_bytes_per_real_row", toJson (8 * (width + 1))),
    ("preserve_zero_multiplicity_rows", toJson true), ("real_rows", Json.null)]
  let bytes := (#[("bytes1", 3, 256), ("bytes2", 10, 65536)] : Array (String × Nat × Nat))
    |>.mapIdx fun index (name, width, height) => Json.mkObj [
      ("index", toJson (top.circuits.size + top.memorySizes.size + index)),
      ("kind", toJson name), ("main_width", toJson width), ("fixed_height", toJson height),
      ("canonical_seed_bytes", toJson (8 * width * height)), ("always_active", toJson true)]
  pure <| Json.mkObj [
    ("program", toJson label), ("library_function_count", toJson top.functions.size),
    ("constrained_function_count", toJson functions.size),
    ("functions", Json.arr functions),
    ("circuits", Json.arr <| top.circuits.mapIdx (circuitJson top names)),
    ("primitive_circuits", Json.arr (memories ++ bytes))]

def document (programs : Array Json) : Json :=
  Json.mkObj [
    ("schema_version", toJson (1 : Nat)),
    ("field_modulus", toJson (toString gSize.toNat)),
    ("seed_encoding", toJson "canonical_u64"),
    ("compact_encoding", toJson "guarded_u8_estimate_only"),
    ("row_weights", Json.null),
    ("programs", Json.arr programs)]

end Aiur.TraceReport

end
