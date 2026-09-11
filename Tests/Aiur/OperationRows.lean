/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.OperationRows
import Ix.Aiur.Proofs.SelectorMessages

/-! Compare evaluated native operation emission with Lean, including every
operation constructor, constant folding, virtual/materialized values, logical
output reuse, column allocation, constraints and selector-gated query parts. -/

open Aiur Aiur.AIR Aiur.Bytecode

namespace AiurTests.OperationRows

private def fixtures : List (List Op) := [
  [.const 0], [.const 1], [.const (0 - 1)],
  [.add 0 1], [.add 0 3], [.add 3 4],
  [.sub 1 2], [.sub 0 3], [.sub 3 4],
  [.mul 0 3], [.mul 1 3], [.mul 2 1], [.mul 3 4], [.mul 5 6],
  [.eqZero 0], [.eqZero 1], [.eqZero 2], [.eqZero 3], [.eqZero 4], [.eqZero 5],
  [.call 17 #[3, 4, 5] 0 false], [.call 17 #[3, 4, 5] 2 false],
  [.call 17 #[3, 4, 5] 0 true], [.call 17 #[3, 4, 5] 2 true],
  [.store #[]], [.store #[0, 3, 4]], [.load 0 3], [.load 3 4],
  [.assertEq #[] #[] none], [.assertEq #[0, 3, 4] #[1, 4, 3] (some "row")],
  [.ioGetInfo 0 #[1, 2]], [.ioRead 0 0 0], [.ioRead 0 3 2],
  [.ioSetInfo 0 #[1, 2] 3 4], [.ioWrite 0 #[3, 4]],
  [.debug "row" none], [.debug "row" (some #[3, 4])],
  [.u8BitDecomposition 3], [.u8ShiftLeft 3], [.u8ShiftRight 3],
  [.u8Xor 3 4], [.u8Add 3 4], [.u8Sub 3 4], [.u8And 3 4], [.u8Or 3 4],
  [.u8LessThan 3 4], [.u8RangeCheck 3 4], [.u8Mul 3 4],
  [.u8XorSplit7 3 4], [.u8XorSplit4 3 4], [.u32LessThan 3 4],
  [.unconstrainedBigUintDivMod 3 4], [.unconstrainedGToBytes 3], [.unconstrainedGInverse 4],
  [.unconstrainedU32Add #[0, 1, 2, 3] #[4, 5, 6, 7]],
  [.unconstrainedU32Add3 #[0, 1, 2, 3] #[4, 5, 6, 7] #[7, 6, 5, 4]],
  [.u32ToField #[0, 1, 2, 3]], [],
  [.const 0, .mul 8 3],
  [.mul 3 4, .add 8 3, .eqZero 9],
  [.unconstrainedGToBytes 3, .u8RangeCheck 8 9, .u8Add 8 9,
    .assertEq #[16] #[3] none, .unconstrainedGInverse 17],
  [.store #[3, 4], .load 2 8, .call 17 #[9, 10] 2 false, .u8Xor 11 12],
  [.ioRead 0 0 4, .unconstrainedU32Add #[8, 9, 10, 11] #[0, 1, 2, 7],
    .u32ToField #[12, 13, 14, 15]],
  [.eqZero 0, .add 8 1, .sub 9 1, .mul 10 7],
  [.unconstrainedBigUintDivMod 3 4, .call 17 #[8, 9] 0 false, .debug "row" none]]

private def inputValues (row : Nat → G) : Array RowValue := #[
  RowValue.konst 0, RowValue.konst 1, RowValue.konst (0 - 1),
  RowValue.variable (row 0), RowValue.variable (row 1),
  RowValue.variable (row 0 + row 1), RowValue.variable (row 2), RowValue.konst 257]

private def row (seed : Nat) (selector : G) (index : Nat) : G :=
  let choices : Array G := #[0, 1, 255, 256, 0 - 1, 0 - 2,
    G.ofNat (2 ^ 32 - 1), G.ofNat (2 ^ 32), G.ofNat (2 ^ 48 - 1), 17, 3, 65536]
  match index with
  | 0 => choices[seed]?.getD 0
  | 1 => choices[(seed + 1) % 12]?.getD 0
  | 2 => choices[(seed + 2) % 12]?.getD 0
  | 3 => selector
  | index => choices[(seed + 5 * index) % 12]?.getD 0

private def appendNat (out : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut out := out
  for i in [:8] do
    out := out.push ((value >>> (8 * i)) % 256).toUInt8
  return out

private def appendValues (out : ByteArray) (values : List G) : ByteArray :=
  values.foldl (fun out value => appendNat out value.n) (appendNat out values.length)

private def encode (branchless : Bool) (selector : G) (emission : OpsEmission) : ByteArray := Id.run do
  let mut out := appendNat ByteArray.empty emission.column
  out := appendNat out emission.values.size
  for value in emission.values do
    out := appendNat out value.value.n
    out := appendNat out value.degree
    out := appendNat out (if value.constant then 1 else 0)
  out := appendValues out emission.equations
  out := appendNat out emission.queries.length
  for query in emission.queries do
    out := appendNat out selector.n
    out := appendValues out (gateMessage branchless selector query)
  return out

private def expected : Except String (Array (String × ByteArray)) := do
  if fixtures.length != 65 then throw "incomplete operation fixture corpus"
  let mut records := #[("header", appendNat "Aiur operation rows v1\n".toUTF8 fixtures.length)]
  for branchless in [false, true] do
    for seed in [:12] do
      for selector in ([0, 1, 2, 0 - 1] : List G) do
        let row := row seed selector
        for (ops, index) in fixtures.zipIdx do
          let label := s!"fixture {index}, seed {seed}, selector {selector.n}, branchless {branchless}"
          let some emission := emitOps row selector (row 2) ops (inputValues row) 4
            | throw s!"unexpected rejected emission: {label}"
          records := records.push (label, encode branchless selector emission)
  return records

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  let records ← match expected with
    | .ok records => pure records
    | .error error => throw (IO.userError error)
  unless records.size == 6241 do
    throw (IO.userError s!"incomplete operation-row corpus: {records.size - 1}")
  let mut position := 0
  for (label, expected) in records do
    unless position + expected.size ≤ native.size do
      throw (IO.userError s!"short operation-row snapshot at {label}")
    for i in [:expected.size] do
      unless native[position + i]! == expected[i]! do
        throw (IO.userError s!"operation-row mismatch at {label}, byte {i} (absolute {position + i}): {native[position + i]!} / {expected[i]!}")
    position := position + expected.size
  unless position == native.size do
    throw (IO.userError s!"extra operation-row snapshot data: {native.size - position} bytes")
  IO.println "operation rows: 6,240 native/Lean assignments across all 34 constructors and output-reusing sequences match"

end AiurTests.OperationRows

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.OperationRows.run path
  | _ => throw (IO.userError "expected native operation-row snapshot path")
