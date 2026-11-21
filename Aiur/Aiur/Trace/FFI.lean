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

structure Matrices where
  matrices : Array Matrix

structure Result where
  execution : Execution.Result
  trace : Matrices

@[extern "aiur_lean_execute"]
private opaque executeRaw (package hints : @& ByteArray) (request : @& String) : IO ByteArray

open Aiur.Ixon in
private def getMatrix : GetM Matrix := do
  let chip ← getString
  let width ← getNat
  let height ← getNat
  let unpadded_height ← getNat
  let values ← getArray getNat
  let multiplicities ← getArray getNat
  return { chip, width, height, unpadded_height, values, multiplicities }

/-- Execute and populate using the companion plan. This path additionally runs
the Rust diagnostic checker; callers can then use the original Lean checker. -/
def run (exported : Execution.Export (ZMod p)) [NeZero p] (plan : ByteArray)
    (entry : String) (args : Array Nat) (hints : Array (Execution.HintEntry (ZMod p)) := #[])
    (pad : Bool := true) : IO (Except String Result) := do
  let inputs := do
    let package ← Artifact.package exported p ZMod.val (some plan)
    let hints ← Artifact.hints ZMod.val (← exported.prepareHints hints)
    pure (package, hints)
  match inputs with
  | .error e => return .error e
  | .ok (package, hints) =>
    let request := Json.mkObj [("entry", toJson entry), ("flat_args", toJson args),
      ("pad_trace", toJson pad), ("compare_reference", toJson true)]
    let response ← executeRaw package hints request.compress
    return do
      let (execution, trace) ← Execution.decodeResponse response
        (Aiur.Ixon.getOption (Aiur.Ixon.getArray getMatrix))
      let some matrices := trace | throw "execution returned no trace"
      return ⟨execution, ⟨matrices⟩⟩

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
  let types := result.execution.memory_types.toList
  let entries ← result.execution.memory.toList.mapM fun entry => do
    unless entry.address < p do throw "ROM address exceeds field capacity"
    let words := entry.value.toList
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
    let words := entry.value.toList
    unless words.all (· < p) do throw "noncanonical ROM value"
    return ((entry.address : ZMod p), words.map Nat.cast)
  return ⟨entries⟩

end Aiur.Trace
