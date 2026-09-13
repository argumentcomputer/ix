/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.MemoryColumns

open Aiur Aiur.AIR

namespace AiurTests.MemoryRows

private def appendNat (out : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut out := out
  for i in [:8] do
    out := out.push ((value >>> (8 * i)) % 256).toUInt8
  return out

private def appendValues (out : ByteArray) (values : List G) : ByteArray :=
  values.foldl (fun out value => appendNat out value.n) (appendNat out values.length)

private def row (height pattern index width : Nat) : MemoryColumns width := fun column =>
  let choices : List G := [0, 1, 0 - 1, 255, 256, G.ofNat (2^32), G.ofNat (2^48 - 1), 17]
  let selector : G := match pattern % 8 with
    | 0 => 0
    | 1 => 1
    | 2 => if index < (height + 1) / 2 then 1 else 0
    | 3 => if index + 1 == height then 1 else 0
    | 4 => if index % 2 == 0 then 1 else 0
    | 5 => 2
    | 6 => 0 - 1
    | _ => choices[(index + pattern) % 8]?.getD 0
  if pattern == 0 then 0
  else match column.val with
    | 0 => if pattern < 8 && selector == 0 then 0 else choices[(3 * index + pattern) % 8]?.getD 0
    | 1 => selector
    | 2 => if pattern < 16 then (0 - 1) + G.ofNat index else G.ofNat (255 + 2 * index)
    | column => choices[(5 * column + 3 * index + pattern) % 8]?.getD 0

private def expected : ByteArray × Nat := Id.run do
  let mut out := appendNat "Aiur memory rows v1\n".toUTF8 25
  let mut checked := 0
  for width in [0, 1, 2, 4, 8] do
    for height in [0, 1, 2, 4, 8] do
      for value in [width, height, 3 + width, 1, 24] do
        out := appendNat out value
      for pattern in [:24] do
        let matrix := fun index : Fin height => row height pattern index.val width
        for index in List.finRange height do
          out := appendValues out (memoryMatrixEquations width height matrix index)
          let (multiplicity, message) := memoryColumnLookup width (matrix index)
          out := appendNat out multiplicity.n
          out := appendValues out message
          checked := checked + 1
  return (out, checked)

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  let (expected, checked) := expected
  unless checked == 1800 do throw (IO.userError "incomplete memory-row corpus")
  unless native.size == expected.size do
    throw (IO.userError s!"memory-row snapshot size differs: {native.size} / {expected.size}")
  for i in [:expected.size] do
    unless native[i]! == expected[i]! do
      throw (IO.userError s!"memory-row mismatch at byte {i}: {native[i]!} / {expected[i]!}")
  IO.println s!"memory rows: {checked} native/Lean assignments across 25 width/height pairs match"

end AiurTests.MemoryRows

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.MemoryRows.run path
  | _ => throw (IO.userError "expected native memory-row snapshot path")
