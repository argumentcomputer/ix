import Aiur.Trace.Export
import Aiur.Execution.FFI

namespace Aiur.Trace
open Lean

structure Matrix where
  chip : String
  width : Nat
  height : Nat
  unpadded_height : Nat
  values : Array Nat
  multiplicities : Array Nat
  deriving FromJson

structure Matrices where
  matrices : Array Matrix
  deriving FromJson

structure Result where
  execution : Execution.Result
  trace : Matrices

@[extern "aiur_lean_execute"]
private opaque executeJson (request : @& String) : IO String

/-- Execute and populate using the companion plan. This path additionally runs
the Rust diagnostic checker; callers can then use the original Lean checker. -/
def run (exported : Execution.Export (ZMod p)) [NeZero p] (plan : Json)
    (entry : String) (args : Array Nat) (hints : Array (Execution.HintEntry (ZMod p)) := #[])
    (pad : Bool := true) : IO (Except String Result) := do
  let request := do
    let program ← exported.toJson p ZMod.val
    let hints ← exported.prepareHints hints
    pure <| Json.mkObj [("program", program), ("trace", plan), ("entry", toJson entry),
      ("flat_args", toJson args), ("hints", Execution.hintsJson ZMod.val hints), ("pad_trace", toJson pad),
      ("compare_reference", toJson true)]
  match request with
  | .error e => return .error e
  | .ok request =>
    let response ← executeJson request.compress
    return do
      let response ← Json.parse response
      if let .ok error := response.getObjValAs? String "error" then throw error
      let result ← response.getObjVal? "ok"
      return ⟨← fromJson? result, ← fromJson? (← result.getObjVal? "trace")⟩

private def readType (fuel : Nat) (value : Json) : Except String Ty := do
  match fuel with
  | 0 => throw "type nesting too deep"
  | fuel + 1 =>
    match ← value.getObjValAs? String "kind" with
    | "field" => pure .field
    | "ptr" => return .ptr (← readType fuel (← value.getObjVal? "target"))
    | "enum" => return .enum (← value.getObjValAs? String "name")
    | "tuple" => return .tuple (← (← value.getObjValAs? (List Json) "items").mapM (readType fuel))
    | _ => throw "invalid wire type"

/-- Physical rows, including the activation column and silent padding. -/
def Result.paddedRows (result : Result) (p : Nat) [NeZero p] : Except String (List (Circuit.WeightedRow (ZMod p))) := do
  let rows ← result.trace.matrices.toList.mapM fun matrix => do
    unless matrix.values.size == matrix.height * matrix.width && matrix.multiplicities.size == matrix.height &&
        matrix.unpadded_height ≤ matrix.height && matrix.values.all (· < p) do throw "malformed trace matrix"
    return (List.range matrix.height).map fun i =>
      Circuit.WeightedRow.mk ⟨matrix.chip, (List.range matrix.width).map fun column =>
        ((matrix.values[i * matrix.width + column]?.getD 0 : Nat) : ZMod p)⟩
        (Int.ofNat (matrix.multiplicities[i]?.getD 0))
  return rows.flatten

/-- Project active rows to the certified physical circuit. Inactive rows must
provide nothing. `Activation.active_rule_iff` proves the local-rule bridge;
the Lean checker still checks the complete projected trace. -/
def Result.rows (result : Result) (p : Nat) [NeZero p] : Except String (List (Circuit.WeightedRow (ZMod p))) := do
  let rows ← result.trace.matrices.toList.mapM fun matrix => do
    unless matrix.width > 0 && matrix.values.size == matrix.height * matrix.width &&
        matrix.multiplicities.size == matrix.height && matrix.unpadded_height ≤ matrix.height &&
        matrix.values.all (· < p) do throw "malformed activated trace matrix"
    let rows ← (List.range matrix.height).mapM fun i => do
      let active := matrix.values[i * matrix.width + matrix.width - 1]?.getD 0
      let count := matrix.multiplicities[i]?.getD 0
      if active == 0 then
        unless count == 0 do throw "inactive row provides a claim"
        return []
      unless active == 1 do throw "non-boolean row activation"
      return [Circuit.WeightedRow.mk ⟨matrix.chip, (List.range (matrix.width - 1)).map fun column =>
        ((matrix.values[i * matrix.width + column]?.getD 0 : Nat) : ZMod p)⟩ (Int.ofNat count)]
    return rows.flatten
  return rows.flatten

def Result.rom (result : Result) (p : Nat) [NeZero p] : Except String (WireROM (ZMod p)) := do
  let types ← result.execution.memory_types.toList.mapM fun (type, width) => do
    return (← readType 1024 type, width)
  let entries ← result.execution.memory.toList.mapM fun entry => do
    unless entry.address < p do throw "ROM address exceeds field capacity"
    let words ← entry.cell.getObjValAs? (List Nat) "value"
    unless words.all (· < p) do throw "noncanonical ROM value"
    -- Type IDs are proof-level views, not physical memory columns. Include
    -- every declared view of the width; unused invalid encodings are harmless.
    return (types.filter (fun (_, width) => width == words.length)).map fun (type, _) =>
      ((entry.address : ZMod p), WireValue.mk type (words.map Nat.cast))
  return ⟨entries.flatten⟩

/-- The physical deduplication proof uses these untyped cells directly; typed
views are reconstructed only in its source-level soundness theorem. -/
def Result.widthROM (result : Result) (p : Nat) [NeZero p] : Except String (WidthROM (ZMod p)) := do
  let entries ← result.execution.memory.toList.mapM fun entry => do
    unless entry.address < p do throw "ROM address exceeds field capacity"
    let words ← entry.cell.getObjValAs? (List Nat) "value"
    unless words.all (· < p) do throw "noncanonical ROM value"
    return ((entry.address : ZMod p), words.map Nat.cast)
  return ⟨entries⟩

end Aiur.Trace
