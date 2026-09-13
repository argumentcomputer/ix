import Compilatrix.Ixby.Lean

/-! A static inventory of the actual in-memory reference image. This report is
not a canonical image encoding, source certificate, or execution capacity
measurement. Counts include every emitted block, including runtime helpers. -/

namespace Compilatrix.Ixby.LeanFrontend

open Lean Ix.Ixby

private def counts (names : Array String) : Json :=
  let counts := names.foldl (fun (acc : Std.TreeMap String Nat) name =>
    acc.insert name (acc.getD name 0 + 1)) {}
  Json.mkObj (counts.toList.map fun (name, count) => (name, toJson count))

private def operationName : Op → String
  | .copy .. => "copy"
  | .primitive .. => "primitive"
  | .construct .. => "construct"
  | .project .. => "project"
  | .closure .. => "closure"
  | .call .. => "call"
  | .callSelf .. => "callSelf"
  | .apply .. => "apply"

private def instructionName : Instr → String
  | .letOp op _ => operationName op
  | .ret .. => "ret"
  | .tailCall .. => "tailCall"
  | .tailCallSelf .. => "tailCallSelf"
  | .tailApply .. => "tailApply"
  | .caseCtor .. => "caseCtor"
  | .caseNat .. => "caseNat"
  | .branch .. => "branch"

def Image.report (image : Image) : Json := Id.run do
  let limits := image.state.limits
  let blocks := image.program.functions.flatMap (·.blocks)
  let primitives := blocks.filterMap fun block => match block.instruction with
    | .letOp (.primitive op _) _ => some (reprStr op)
    | _ => none
  let constructors := image.state.constructorNames.toList.mergeSort (fun a b => a.2 ≤ b.2)
  return Json.mkObj [
    ("format", toJson "compilatrix-lean-ixby-reference-inventory/1"),
    ("source_entry", toJson (toString image.sourceEntry)),
    ("source_certified", .bool false),
    ("canonical_image", .null),
    ("canonical_profile", .null),
    ("entry", toJson image.program.entry),
    ("functions", toJson image.program.functions.size),
    ("blocks", toJson blocks.size),
    ("constructors", toJson image.program.constructors.size),
    ("maximum_function_blocks", toJson (image.program.functions.foldl (fun n f => max n f.blocks.size) 0)),
    ("maximum_frame_locals", toJson (blocks.foldl (fun n b => max n b.locals) 0)),
    ("maximum_function_arity", toJson (image.program.functions.foldl (fun n f => max n f.arity) 0)),
    ("reference_limits", Json.mkObj [
      ("functions", toJson limits.functions), ("constructors", toJson limits.constructors),
      ("blocks", toJson limits.blocks), ("locals", toJson limits.locals),
      ("operands", toJson limits.operands), ("continuations", toJson limits.continuations),
      ("inputNodes", toJson limits.inputNodes), ("natBits", toJson limits.natBits),
      ("stringBytes", toJson limits.stringBytes), ("byteArrayBytes", toJson limits.byteArrayBytes)]),
    ("instruction_counts", counts (blocks.map (instructionName ·.instruction))),
    ("primitive_counts", counts primitives),
    ("function_inventory", .arr (image.state.functions.mapIdx fun index slot => Json.mkObj [
      ("index", toJson index), ("name", toJson (toString slot.name)),
      ("arity", toJson slot.arity), ("blocks", toJson image.program.functions[index]!.blocks.size)])),
    ("constructor_inventory", toJson (constructors.map fun (name, index) => Json.mkObj [
      ("index", toJson index), ("name", toJson (toString name)),
      ("fields", toJson image.program.constructors[index]!.fields)]))]

end Compilatrix.Ixby.LeanFrontend
