/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LookupExpressions

/-! Compare complete native operation and sequence expression trees, including
metadata, cursor movement, equations, and superposed physical lookup slots.
The corpus supplies the actual native operations, inputs, and assignments. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.OpEmitter Aiur.NativeAIR.Compiler

namespace AiurTests.OperationExpressions

private abbrev Reader := StateT (ByteArray × Nat) (Except String)

private def takeBytes (count : Nat) : Reader ByteArray := do
  let (bytes, cursor) ← get
  if cursor + count > bytes.size then throw s!"operation snapshot truncated at {cursor}"
  set (bytes, cursor + count)
  return bytes.extract cursor (cursor + count)

private def readNat (count : Nat := 8) : Reader Nat := do
  let bytes ← takeBytes count
  let mut value := 0
  for index in [:count] do value := value + bytes[index]!.toNat * 256^index
  return value

private def readCount (limit : Nat := 1024) : Reader Nat := do
  let count ← readNat
  unless count ≤ limit do throw s!"operation snapshot count exceeds {limit}"
  return count

private def readField : Reader G := do
  let value ← readNat
  unless value < gSize.toNat do throw "noncanonical operation field value"
  return G.ofNat value

private def readBool : Reader Bool := do
  match ← readNat 1 with
  | 0 => return false
  | 1 => return true
  | _ => throw "invalid operation boolean"

private def readList (count : Nat) (reader : Reader α) : Reader (List α) :=
  (List.range count).mapM fun _ => reader

private def readValues : Reader (List G) := do readList (← readCount) readField

private def readString : Reader String := do
  let bytes ← takeBytes (← readCount)
  let some string := String.fromUTF8? bytes | throw "invalid operation text"
  return string

private def readOption (reader : Reader α) : Reader (Option α) := do
  if ← readBool then return some (← reader) else return none

private def readIndices : Reader (Array Nat) := do
  return (← readList (← readCount) readNat).toArray

private def readExpr : Nat → Reader Expr
  | 0 => throw "operation expression exceeds snapshot depth bound"
  | fuel + 1 => do
    match ← readNat 1 with
    | 0 => return .konst (← readField)
    | 1 =>
      let source ← match ← readNat 1 with
        | 0 => pure Source.preprocessed | 1 => pure Source.main | 2 => pure Source.stage2
        | _ => throw "invalid operation column source"
      let offset ← match ← readNat 1 with
        | 0 => pure RowOffset.current | 1 => pure RowOffset.next
        | _ => throw "invalid operation row offset"
      return .var ⟨source, offset, ← readNat⟩
    | 2 => return .publicInput (← readNat)
    | 3 => return .isFirstRow
    | 4 => return .isLastRow
    | 5 => return .isTransition
    | 6 => return .add (← readExpr fuel) (← readExpr fuel)
    | 7 => return .sub (← readExpr fuel) (← readExpr fuel)
    | 8 => return .mul (← readExpr fuel) (← readExpr fuel)
    | 9 => return .neg (← readExpr fuel)
    | _ => throw "invalid operation expression tag"

private def readMap : Reader (Array RowExpr) := do
  return (← readList (← readCount) do
    return RowExpr.mk (← readExpr 64) (← readNat)).toArray

private def readOp : Reader Bytecode.Op := do
  match ← readNat 1 with
  | 0 => return .const (← readField)
  | 1 => return .add (← readNat) (← readNat)
  | 2 => return .sub (← readNat) (← readNat)
  | 3 => return .mul (← readNat) (← readNat)
  | 4 => return .eqZero (← readNat)
  | 5 => return .call (← readNat) (← readIndices) (← readNat) (← readBool)
  | 6 => return .store (← readIndices)
  | 7 => return .load (← readNat) (← readNat)
  | 8 => return .assertEq (← readIndices) (← readIndices) (← readOption readString)
  | 9 => return .ioGetInfo (← readNat) (← readIndices)
  | 10 => return .ioSetInfo (← readNat) (← readIndices) (← readNat) (← readNat)
  | 11 => return .ioRead (← readNat) (← readNat) (← readNat)
  | 12 => return .ioWrite (← readNat) (← readIndices)
  | 13 => return .u8BitDecomposition (← readNat)
  | 14 => return .u8ShiftLeft (← readNat)
  | 15 => return .u8ShiftRight (← readNat)
  | 16 => return .u8Xor (← readNat) (← readNat)
  | 17 => return .u8Add (← readNat) (← readNat)
  | 18 => return .u8Mul (← readNat) (← readNat)
  | 19 => return .u8Sub (← readNat) (← readNat)
  | 20 => return .u8And (← readNat) (← readNat)
  | 21 => return .u8Or (← readNat) (← readNat)
  | 22 => return .u8LessThan (← readNat) (← readNat)
  | 23 => return .u32LessThan (← readNat) (← readNat)
  | 24 => return .u8XorSplit7 (← readNat) (← readNat)
  | 25 => return .u8XorSplit4 (← readNat) (← readNat)
  | 26 => return .debug (← readString) (← readOption readIndices)
  | 27 => return .u8RangeCheck (← readNat) (← readNat)
  | 28 => return .unconstrainedBigUintDivMod (← readNat) (← readNat)
  | 29 => return .unconstrainedGToBytes (← readNat)
  | 30 => return .unconstrainedGInverse (← readNat)
  | 31 => return .unconstrainedU32Add (← readIndices) (← readIndices)
  | 32 => return .unconstrainedU32Add3 (← readIndices) (← readIndices) (← readIndices)
  | 33 => return .u32ToField (← readIndices)
  | _ => throw "invalid operation constructor tag"

private def assignment (row : Array G) : Values G :=
  ⟨(fun source _ => match source with | .main => row | _ => #[]), #[], 1, 0, 1⟩

private def callData (calls : List (Bytecode.AIR.Call × (Fin 6 → G))) :=
  calls.map fun (call, gap) => (call, List.ofFn gap)

private def sameEmission (left right : AIR.OpsEmission) : Bool :=
  left.values == right.values && left.column == right.column && left.equations == right.equations &&
    left.queries == right.queries && callData left.calls == callData right.calls

private def readSequence (rows : List (Array G)) (label : String) : Reader (List LookupEmitter.QueryExpr) := do
  let first ← readNat
  let lookup ← readNat
  let selector ← readExpr 64
  let rank ← readExpr 64
  let inputs ← readMap
  let ops ← readList (← readCount) readOp
  unless inputs.all (·.expr.noConstantNegs) do throw s!"invalid incoming normal form: {label}"
  let some emitted := emitOps selector rank ops inputs first
    | throw s!"symbolic operation sequence rejected native inputs: {label}"
  let column ← readNat
  let lookupEnd ← readNat
  let nativeMap ← readMap
  let equations ← readList (← readCount) (readExpr 64)
  unless column == emitted.column && lookupEnd == lookup + emitted.queries.length do
    throw s!"native operation cursor differs: {label}"
  unless nativeMap == emitted.values do
    throw s!"native output expression or degree differs: {label}; ops {repr ops}"
  unless equations == emitted.equations do
    throw s!"native operation constraint trees differ: {label}; ops {repr ops}"
  unless emitted.values.all (·.expr.noConstantNegs) do
    throw s!"native output lost the negation invariant: {label}"
  for (row, seed) in rows.zipIdx do
    let expected ← readList nativeMap.size do return (← readField, ← readBool)
    let equationValues ← readList equations.length readField
    let values := assignment row
    let some evaluated := emitted.eval values | throw s!"symbolic evaluation failed: {label}, {seed}"
    unless evaluated.values.toList.map (fun value => (value.value, value.constant)) == expected &&
        evaluated.equations == equationValues do
      throw s!"native operation values differ: {label}, assignment {seed}"
    let some inputValues := evalRows values inputs | throw "undefined native input expressions"
    let some s := evalExpr values selector | throw "undefined native selector"
    let some r := evalExpr values rank | throw "undefined native rank"
    let some valued := AIR.emitOps (fun index => row[index]?.getD 0) s r ops inputValues first
      | throw s!"valued operation sequence rejected symbolic inputs: {label}"
    unless sameEmission evaluated valued do throw s!"symbolic/valued sequence differs: {label}, {seed}"
  return LookupEmitter.queryParts lookup selector emitted.queries

private def readReport (rows : List (Array G)) (index : Nat) : Reader (Nat × Nat) := do
  let branchless ← readBool
  let writers ← readCount 3
  unless writers == 1 || writers == 3 do throw "unexpected native writer count"
  let mut queries := []
  for writer in [:writers] do
    queries := queries ++ (← readSequence rows s!"report {index}, writer {writer}")
  let count ← readCount 64
  for slot in [:count] do
    let native : ExprLookup := ⟨← readExpr 64, ← readList (← readCount) (readExpr 64)⟩
    let expected := LookupEmitter.slot branchless queries slot
    unless native == expected do throw s!"native lookup expression trees differ: report {index}, slot {slot}"
    for (row, seed) in rows.zipIdx do
      let weight ← readField
      let message ← readValues
      let values := assignment row
      unless expected.eval goldilocksOps values == some (weight, message) do
        throw s!"native slot values differ: report {index}, slot {slot}, assignment {seed}"
      let some parts := queries.mapM (LookupEmitter.QueryExpr.eval values)
        | throw "undefined raw query expressions"
      unless weight == AIR.querySlotMultiplicity parts slot &&
          message == AIR.slotMessage branchless (AIR.querySlotParts parts slot) do
        throw "symbolic slot and valued query parts differ"
  return (writers, if writers == 3 then 1 else 0)

private def readCorpus : Reader Unit := do
  let header := "Aiur operation expressions v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "operation snapshot version differs"
  unless (← readCount) == 4 do throw "incomplete operation assignments"
  let rows ← readList 4 do return (← readValues).toArray
  unless rows.all (·.size == 512) do throw "operation assignment width differs"
  unless (← readCount) == 876 do throw "incomplete operation expression corpus"
  let mut sequences := 0
  let mut shared := 0
  for index in [:876] do
    let (count, combined) ← readReport rows index
    sequences := sequences + count
    shared := shared + combined
  unless sequences == 1752 && shared == 438 do throw "incomplete native operation coverage"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "operation snapshot has trailing bytes"

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok _ => IO.println "operation expressions: 1,752 native sequences, 7,008 assignments and 438 shared-slot cases match"

end AiurTests.OperationExpressions

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.OperationExpressions.run path
  | _ => throw (IO.userError "expected native operation expression snapshot")
