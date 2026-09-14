/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ByteColumns

open Aiur

namespace AiurTests.TraceHeights

private def append (out : ByteArray) (heights : List Nat) (active : List Bool) (degrees : List Nat) : ByteArray :=
  out.push (if fixedTraceHeights heights active degrees then 1 else 0)

private def expected : ByteArray := Id.run do
  let mut out := "Aiur fixed trace heights v1\n".toUTF8
  for height in [0, 1, 2, 3, 256, 65536, 2^31, 2^32, 2^63, 2^64 - 1] do
    for degree in [:256] do
      out := append out [height] [true] [degree]
      out := append out [0, height, 0] [false, true, false] [degree]
      out := append out [0, height, 65536] [true, true, true] [2, degree, 16]
  let heights := [0, 256, 0, 65536]
  for heightCount in [:5] do
    for activeCount in [:5] do
      for mask in [:2^activeCount] do
        let active := (List.range activeCount).map fun bit => (mask &&& (2^bit)) != 0
        for degreeCount in [:6] do
          for degree in [0, 1, 7, 8, 9, 15, 16, 17, 63, 64, 255] do
            out := append out (heights.take heightCount) active (List.replicate degreeCount degree)
  return out

def run (path : System.FilePath) : IO Unit := do
  let native ← IO.FS.readBinFile path
  let reference := expected
  unless reference.size == "Aiur fixed trace heights v1\n".toUTF8.size + 17910 do
    throw (IO.userError "incomplete fixed-trace-height corpus")
  unless native.size == reference.size do
    throw (IO.userError s!"fixed-trace-height snapshot size differs: {native.size} / {reference.size}")
  for index in [:reference.size] do
    unless native[index]! == reference[index]! do
      throw (IO.userError s!"fixed-trace-height mismatch at byte {index}: {native[index]!} / {reference[index]!}")
  IO.println "fixed trace heights: all 17,910 native/Lean checks match"

end AiurTests.TraceHeights

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.TraceHeights.run path
  | _ => throw (IO.userError "expected native fixed-trace-height snapshot path")
