/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.LogUpAccumulator
import Tests.Aiur.EmissionReader

/-! Comparison with direct native logUp, its symbolic schoolbook reference,
and native stage-2 traces. The corpus includes every group size, empty groups,
uneven tails, variable argument widths, poles and arbitrary extension-valued
coordinates. Malformed reads are tested only through the checked Lean model. -/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)
open LogUp (Coordinates)

namespace AiurTests.LogUp

private def counts : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 17, 23, 24, 25, 31, 32, 33, 63, 64, 65]

private def readExtension : Reader Extension := do return ⟨← readField, ← readField⟩

private def readVector (readValue : Reader W) : Reader (Array W) := do
  return (← readList (← readCount 4096) readValue).toArray

private def readLookups : Reader (List Lookup) := do
  readList (← readCount) do
    return ⟨← readNat, ← readList (← readCount) readNat⟩

private def readDirectCases {W : Type} [Lean.Grind.CommRing W] [DecidableEq W]
    (readValue : Reader W) : Reader Unit := do
  unless (← readCount 10000) == 2376 do throw "incomplete direct logUp cases"
  for count in counts do
    for groupSize in [:9] do
      for seed in [:12] do
        unless (← readNat) == count && (← readNat) == groupSize && (← readNat) == seed do
          throw "direct logUp case order differs"
        let lookups ← readLookups
        unless lookups.length == count do throw "direct logUp lookup count differs"
        let nodes ← readVector readValue
        let current ← readVector readValue
        let next ← readVector readValue
        let publics ← readVector readValue
        let delta ← readVector readValue
        let isLast ← readValue
        let expected := (← readVector readValue).toList
        let evaluate := fun lookups nodes current next publics delta size =>
          NativeAIR.LogUp.constraintValues lookups nodes current next publics delta isLast size
        unless evaluate lookups nodes current next publics delta groupSize == some expected do
          throw s!"native logUp differs: {count} lookups, group {groupSize}, assignment {seed}"
        unless expected.length == 2 * NativeAIR.LogUp.groupCount groupSize count do throw "logUp coordinate count differs"
        unless evaluate lookups nodes current.pop next publics delta groupSize == none do throw "short current row accepted"
        unless evaluate lookups nodes current (next.extract 0 1) publics delta groupSize == none do throw "short next row accepted"
        unless evaluate lookups nodes current next (publics.extract 0 3) delta groupSize == none do throw "short public input accepted"
        unless evaluate lookups nodes current next publics (delta.extract 0 1) groupSize == none do throw "short delta accepted"
        unless evaluate (lookups ++ [⟨nodes.size, []⟩]) nodes current next publics delta groupSize == none do
          throw "out-of-range multiplicity accepted"
        unless evaluate (lookups ++ [⟨0, [nodes.size]⟩]) nodes current next publics delta groupSize == none do
          throw "out-of-range argument accepted"
        for invalid in [9, 256, 2^64 - 1] do
          unless evaluate lookups nodes current next publics delta invalid == none do throw "oversized logUp group accepted"

private def readDirect : Reader Unit := do
  let header := "Aiur grouped logup v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "logUp snapshot version differs"
  readDirectCases readField
  readDirectCases readExtension

private def baseCoordinates (values : Array Extension) : Array G :=
  (Coordinates.flatten (values.toList.map Coordinates.fromExtension)).toArray

private def readStages : Reader Unit := do
  let header := "Aiur grouped logup stages v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "stage-2 snapshot version differs"
  unless (← readNat) == 27 do throw "incomplete stage-2 batches"
  let mut totalRows := 0
  for groupSize in [:9] do
    for seed in [:3] do
      unless (← readNat) == groupSize && (← readNat) == seed do throw "stage-2 batch order differs"
      let beta ← readExtension
      let gamma ← readExtension
      let mut entering ← readExtension
      unless (← readNat) == 5 do throw "incomplete stage-2 circuits"
      for (expectedHeight, expectedLookups) in [(1, 0), (2, 1), (4, 9), (8, 17), (4, 25)] do
        let height ← readNat
        let count ← readNat
        let width ← readNat
        unless height == expectedHeight && count == expectedLookups &&
            width == NativeAIR.LogUp.groupCount groupSize count do throw "stage-2 circuit shape differs"
        let matrix ← readVector readExtension
        unless matrix.size == height * width do throw "stage-2 matrix length differs"
        let leaving ← readExtension
        let normalizer ← readField
        unless normalizer != 0 do throw "zero last-row normalizer"
        let delta := (Coordinates.fromExtension (leaving - entering)).scale normalizer.inverse
        let publics := baseCoordinates #[beta, gamma, entering, leaving]
        let mut running : Extension := 0
        for row in [:height] do
          let lookups ← readList (← readCount) do return (← readField, (← readVector readField).toList)
          unless lookups.length == count do throw "stage-2 row lookup count differs"
          let native := (← readVector readField).toList
          let betaPair := Coordinates.fromExtension beta
          let gammaPair := Coordinates.fromExtension gamma
          let entries := NativeAIR.LogUp.fieldEntries (NativeAIR.LogUp.compress betaPair gammaPair lookups)
          unless entries.all (fun entry => entry.2 != 0) do throw "unexpected stage-2 pole"
          let rowFraction := NativeAIR.LogUp.lookupFractions betaPair gammaPair lookups
          let before := running
          for group in [:width] do
            unless matrix[row * width + group]? == some running do throw "native partial accumulator differs"
            let chunk := NativeAIR.LogUp.chunk groupSize group lookups
            running := running + NativeAIR.LogUp.lookupFractions betaPair gammaPair chunk
          unless running == before + rowFraction do throw "grouping changes the row fraction"
          let current := baseCoordinates (matrix.extract (row * width) ((row + 1) * width))
          let nextIndex := (row + 1) % height
          let next := baseCoordinates (matrix.extract (nextIndex * width) ((nextIndex + 1) * width))
          let isLast := if row + 1 == height then normalizer else 0
          let evaluated := NativeAIR.LogUp.equations lookups current next publics
            #[delta.c0, delta.c1] isLast groupSize
          unless evaluated.map Coordinates.flatten == some native do throw "native stage-2 equations differ"
          unless native.all (· == 0) do throw "native stage-2 equations do not vanish"
          let some first := Coordinates.read current 0 | throw "missing stage-2 first accumulator"
          let some following := Coordinates.read next 0 | throw "missing stage-2 next accumulator"
          unless following.toExtension - first.toExtension + (delta.scale isLast).toExtension == rowFraction do
            throw "stage-2 row does not telescope"
          totalRows := totalRows + 1
        unless entering + running == leaving do throw "native circuit accumulator differs"
        entering := leaving
  unless totalRows == 513 do throw "incomplete stage-2 row corpus"

private def runReader (reader : Reader Unit) (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match reader.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok (_, (_, cursor)) =>
    unless cursor == bytes.size do throw (IO.userError "logUp snapshot has trailing bytes")

def run (direct stages : System.FilePath) : IO Unit := do
  runReader readDirect direct
  IO.println "logUp: 4752 native direct/reference cases and 42768 rejected malformed inputs match"
  runReader readStages stages
  IO.println "logUp stages: 27 batches, 135 circuits and 513 complete rows match native accumulators and equations"

end AiurTests.LogUp

def main (args : List String) : IO Unit := do
  match args with
  | [direct, stages] => AiurTests.LogUp.run direct stages
  | _ => throw (IO.userError "expected native direct logUp and stage-2 snapshots")
