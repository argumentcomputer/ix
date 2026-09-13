/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Interpolation
import Tests.Aiur.EmissionReader

/-! Replay actual native FRI row and matrix folds against the checked
interpolator, using known coefficient polynomials and arbitrary matrix rows.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)

namespace AiurTests.Interpolation

private def readExtension : Reader Extension := return ⟨← readField, ← readField⟩

private def readDomain (bits : Nat) : Reader Domain.Subgroup := do
  let some domain := Domain.ofLogSize bits | throw "invalid interpolation domain"
  return domain

private def sample (seed : Nat) : Extension := ⟨G.ofNat (seed * 67 + 3), G.ofNat (seed * 13 + 1)⟩

private def coefficients (arity variant : Nat) : List Extension :=
  match variant with
  | 0 => []
  | 1 => [sample 1]
  | 2 => (List.range arity).map (fun index => if index + 1 == arity then 1 else 0)
  | _ => (List.range arity).map (fun index => sample (index + 17))

private def checkValues (expected : List Extension) : Reader Unit := do
  unless (← readCount expected.length) == expected.length do throw "native interpolation input length differs"
  unless (← readList expected.length readExtension) == expected do throw "native interpolation inputs differ"

private def readCorpus : Reader (List Nat) := do
  let header := "Aiur FRI interpolation v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "interpolation version differs"
  let mut rows := 0
  let mut evaluations := 0
  for parentBits in [:33] do
    let parent ← readDomain parentBits
    for arityBits in [:min parentBits 6 + 1] do
      let arity ← readDomain arityBits
      let size := Domain.size arity
      let mask := 2^(parentBits - arityBits) - 1
      let indices := [0, mask / 2, mask] |>.mergeSort (· ≤ ·) |>.eraseDups
      unless (← readCount 3) == indices.length do throw "interpolation index inventory differs"
      for index in indices do
        unless (← readNat) == index do throw "native interpolation index differs"
        let nodes := (Polynomial.foldingNodes parent arity index).map Extension.ofBase
        let scale ← readField
        unless scale == NativeAIR.Interpolation.foldScale parent arity index do throw "native interpolation normalizer differs"
        for variant in [:4] do
          let polynomial := coefficients size variant
          let values := nodes.map (fun node => Quotient.horner node polynomial)
          checkValues polynomial
          checkValues values
          let samples := NativeAIR.Interpolation.foldSamples parent arity index values
          if arityBits ≤ 3 then
            let candidate := NativeAIR.Interpolation.coefficients samples (Extension.ofBase scale)
            unless candidate.length ≤ size && (Polynomial.sub candidate polynomial).all (· == 0) do
              throw "constructed interpolating coefficients differ from the native source polynomial"
            let vanishing := Polynomial.fromRoots nodes
            for node in nodes do
              unless (node * Extension.ofBase scale) * Quotient.horner node (Polynomial.divide node vanishing) == 1 do
                throw "interpolation diagonal weight differs"
          let points := [0, Extension.ofBase 7, sample 41,
            Extension.ofBase (FriDomain.foldNode parent arity index 0),
            Extension.ofBase (FriDomain.foldNode parent arity index (size - 1))]
          for point in points do
            unless (← readExtension) == point do throw "native interpolation challenge differs"
            let result ← readExtension
            unless NativeAIR.Interpolation.foldRow parent arity index values point == some result &&
                Quotient.horner point polynomial == result do throw "native FRI row interpolation differs"
            evaluations := evaluations + 1
          rows := rows + 1
  let mut matrices := 0
  let mut matrixRows := 0
  for parentBits in [1:10] do
    let parent ← readDomain parentBits
    for arityBits in [1:min parentBits 6 + 1] do
      let arity ← readDomain arityBits
      let size := Domain.size arity
      let height := 2^(parentBits - arityBits)
      let data := (List.range (2^parentBits)).map (fun index => sample (index + parentBits * 19))
      for point in [0, sample 41, 1] do
        unless (← readExtension) == point do throw "native matrix folding challenge differs"
        checkValues data
        unless (← readCount height) == height do throw "native folded matrix height differs"
        let folded ← readList height readExtension
        unless folded.length == height do throw "native folded matrix height differs"
        for index in [:height] do
          let row := (data.drop (index * size)).take size
          unless NativeAIR.Interpolation.foldRow parent arity index row point == folded[index]? do
            throw "native FRI matrix fold differs"
          matrixRows := matrixRows + 1
        matrices := matrices + 1
  let counts := [rows, evaluations, matrices, matrixRows]
  unless counts == [2436, 12180, 117, 3006] do throw "incomplete interpolation corpus"
  unless (← readList 4 readNat) == counts do throw "interpolation coverage totals differ"
  let empty ← readDomain 0
  let binary ← readDomain 1
  unless NativeAIR.Interpolation.evaluate 1 0 [] == some 0 &&
      NativeAIR.Interpolation.foldRow empty binary 0 [0, 1] 0 == none &&
      NativeAIR.Interpolation.foldRow binary empty 2 [1] 0 == none &&
      NativeAIR.Interpolation.foldRow binary binary 0 [1] 0 == none &&
      NativeAIR.Interpolation.foldRow binary binary 0 [1, 2, 3] 0 == none do
    throw "interpolation helper boundaries differ"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "interpolation snapshot has trailing bytes"
  return counts

end AiurTests.Interpolation

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.Interpolation.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok (counts, _) => IO.println s!"Native FRI interpolation rows, challenge evaluations, matrices and matrix rows match: {counts}"
  | _ => throw (IO.userError "expected native FRI interpolation snapshot")
