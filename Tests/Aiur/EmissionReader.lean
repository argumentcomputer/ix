/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LookupExpressions

/-! Test transport for native expression trees and operation constructors. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.OpEmitter

namespace AiurTests.EmissionReader

abbrev Reader := StateT (ByteArray × Nat) (Except String)

def takeBytes (count : Nat) : Reader ByteArray := do
  let (bytes, cursor) ← get
  if cursor + count > bytes.size then throw s!"operation snapshot truncated at {cursor}"
  set (bytes, cursor + count)
  return bytes.extract cursor (cursor + count)

def readNat (count : Nat := 8) : Reader Nat := do
  let bytes ← takeBytes count
  let mut value := 0
  for index in [:count] do value := value + bytes[index]!.toNat * 256^index
  return value

def readCount (limit : Nat := 1024) : Reader Nat := do
  let count ← readNat
  unless count ≤ limit do throw s!"operation snapshot count exceeds {limit}"
  return count

def readField : Reader G := do
  let value ← readNat
  unless value < gSize.toNat do throw "noncanonical operation field value"
  return G.ofNat value

def readBool : Reader Bool := do
  match ← readNat 1 with
  | 0 => return false
  | 1 => return true
  | _ => throw "invalid operation boolean"

def readList (count : Nat) (reader : Reader α) : Reader (List α) :=
  (List.range count).mapM fun _ => reader

def readValues : Reader (List G) := do readList (← readCount) readField

def readString : Reader String := do
  let bytes ← takeBytes (← readCount)
  let some string := String.fromUTF8? bytes | throw "invalid operation text"
  return string

def readOption (reader : Reader α) : Reader (Option α) := do
  if ← readBool then return some (← reader) else return none

def readIndices : Reader (Array Nat) := do
  return (← readList (← readCount) readNat).toArray

def readExpr : Nat → Reader Expr
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

def readMap : Reader (Array RowExpr) := do
  return (← readList (← readCount) do
    return RowExpr.mk (← readExpr 64) (← readNat)).toArray

def readOp : Reader Bytecode.Op := do
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

def readBlock : Nat → Reader Bytecode.Block
  | 0 => throw "native control tree exceeds snapshot depth bound"
  | fuel + 1 => do
    let ops := (← readList (← readCount) readOp).toArray
    let ctrl : Bytecode.Ctrl ← match ← readNat 1 with
      | 0 => pure (Bytecode.Ctrl.return (← readNat) (← readIndices))
      | 1 => pure (Bytecode.Ctrl.yield (← readNat) (← readIndices))
      | tag => do
        unless tag == 2 || tag == 3 do throw "invalid native control tag"
        let index ← readNat
        let branches := (← readList (← readCount) do
          return (← readField, ← readBlock fuel)).toArray
        let fallback ← readOption (readBlock fuel)
        if tag == 2 then pure (Bytecode.Ctrl.match index branches fallback)
        else pure (Bytecode.Ctrl.matchContinue index branches fallback (← readNat) (← readNat) (← readNat) (← readBlock fuel))
    return ⟨ops, ctrl⟩

def assignment (row : Array G) : Values G :=
  ⟨(fun source _ => match source with | .main => row | _ => #[]), #[], 1, 0, 1⟩

def blockCallData (calls : List (G × (Bytecode.AIR.Call × (Fin 6 → G)))) :=
  calls.map fun (gate, call, gap) => (gate, call, List.ofFn gap)

def sameBlockEmission (left right : AIR.BlockEmission) : Bool :=
  left.values == right.values && left.column == right.column && left.lookup == right.lookup &&
    left.equations == right.equations &&
    left.queries.map (fun part => (part.slot, part.selector, part.message)) ==
      right.queries.map (fun part => (part.slot, part.selector, part.message)) &&
    left.returns == right.returns && left.yields == right.yields && blockCallData left.calls == blockCallData right.calls

end AiurTests.EmissionReader
