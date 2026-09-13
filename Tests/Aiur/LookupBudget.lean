/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LookupBudget

/-! Native/Lean guard comparison across all u8 exponents, machine/field
boundaries, active-position indexing and malformed metadata lengths. -/

open Aiur

namespace AiurTests.LookupBudget

private def appendResult (bytes : ByteArray) (result : Option Nat) : ByteArray := Id.run do
  let mut bytes := bytes.push (if result.isSome then 1 else 0)
  let value := result.getD 0
  for index in [:8] do
    bytes := bytes.push ((value >>> (8 * index)) % 256).toUInt8
  return bytes

private def expected : ByteArray := Id.run do
  let mut out := "Aiur lookup budget v1\n".toUTF8
  let p := gSize.toNat
  let cases := [0, 1, 2, 3, 4, 255, 65536, 2 ^ 31, 2 ^ 32, 2 ^ 32 - 1,
    p / 2 - 1, p - 3, p - 2, p - 1, p, 2 ^ 64 - 1]
  for slots in cases do
    for degree in [:256] do
      out := appendResult out (lookupQueryBound [slots] [true] [degree])
      out := appendResult out (lookupQueryBound [2 ^ 64 - 1, slots, 2 ^ 64 - 1]
        [false, true, false] [degree])
      out := appendResult out (lookupQueryBound [slots, 3] [true, true] [degree, 31])
      out := appendResult out (lookupQueryBound [3, slots] [true, true] [31, degree])
  let slots := [2, 7, 0, 13]
  for slotCount in [:5] do
    for activeCount in [:5] do
      for mask in [:2 ^ activeCount] do
        let active := (List.range activeCount).map fun bit => mask &&& (2 ^ bit) != 0
        for degreeCount in [:6] do
          for degree in [0, 1, 31, 63, 64, 255] do
            out := appendResult out (lookupQueryBound (slots.take slotCount) active
              (List.replicate degreeCount degree))
  return out

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  unless expected.size == "Aiur lookup budget v1\n".toUTF8.size + 21964 * 9 do
    throw (IO.userError "incomplete lookup-budget corpus")
  unless native.size == expected.size do
    throw (IO.userError s!"lookup-budget snapshot size differs: {native.size} / {expected.size}")
  for i in [:expected.size] do
    unless native[i]! == expected[i]! do
      throw (IO.userError s!"lookup-budget mismatch at byte {i}: {native[i]!} / {expected[i]!}")
  IO.println "lookup budget: 21,964 native/Lean boundary, alignment and active-height checks match"

end AiurTests.LookupBudget

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.LookupBudget.run path
  | _ => throw (IO.userError "expected native lookup-budget snapshot path")
