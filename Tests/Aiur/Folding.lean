/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Folding
import Tests.Aiur.EmissionReader

/-! Replay native row and matrix folds of global polynomials, including
partial coefficient blocks and distinct rows attaining the agreement bound.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)

namespace AiurTests.Folding

private def readExtension : Reader Extension := return ⟨← readField, ← readField⟩

private def readDomain (bits : Nat) : Reader Domain.Subgroup := do
  let some domain := Domain.ofLogSize bits | throw "invalid folding domain"
  return domain

private def sample (seed : Nat) : Extension := ⟨G.ofNat (seed * 67 + 3), G.ofNat (seed * 13 + 1)⟩

private def coefficients (arity variant : Nat) : List Extension :=
  let length := match variant with
    | 0 => 0 | 1 => 1 | 2 => arity - 1 | 3 => arity
    | 4 => arity + 1 | 5 => 2 * arity + 1 | 6 => 3 * arity | _ => 3 * arity + 2
  (List.range length).map (fun index =>
    if variant == 6 then (if index + 1 == length then 1 else 0)
    else if variant == 7 && index > arity then 0
    else sample (index + 17))

private def checkValues (expected : List Extension) : Reader Unit := do
  unless (← readCount expected.length) == expected.length do throw "native folding vector length differs"
  unless (← readList expected.length readExtension) == expected do throw "native folding vector differs"

private def checkFolded (arity : Domain.Subgroup) (challenge : Extension)
    (polynomial : List Extension) : Reader (List Extension) := do
  let folded := NativeAIR.Folding.foldCoefficients arity challenge polynomial
  checkValues folded
  let size := Domain.size arity
  unless folded.length == (polynomial.length + size - 1) / size do
    throw "folded coefficient bound differs"
  return folded

private def readCorpus : Reader (List Nat) := do
  let header := "Aiur global FRI folding v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "global folding version differs"
  let mut rows := 0
  let mut evaluations := 0
  for parentBits in [:33] do
    let parent ← readDomain parentBits
    for arityBits in [:min parentBits 6 + 1] do
      let arity ← readDomain arityBits
      let child ← readDomain (parentBits - arityBits)
      let size := Domain.size arity
      let mask := Domain.size child - 1
      let indices := [0, mask / 2, mask] |>.mergeSort (· ≤ ·) |>.eraseDups
      unless (← readCount 3) == indices.length do throw "folding index inventory differs"
      for index in indices do
        unless (← readNat) == index do throw "native folding index differs"
        let nodes := (Polynomial.foldingNodes parent arity index).map Extension.ofBase
        let childPoint := Extension.ofBase (FriDomain.queryPoint child index)
        for variant in [:8] do
          let polynomial := coefficients size variant
          let values := nodes.map (fun node => Quotient.horner node polynomial)
          checkValues polynomial
          checkValues values
          let row := NativeAIR.Folding.rowCoefficients arity childPoint polynomial
          unless row.length ≤ size && nodes.map (fun node => Quotient.horner node row) == values do
            throw "restriction to the folding coset differs"
          let challenges := [0, sample 41, 1,
            Extension.ofBase (FriDomain.foldNode parent arity index 0),
            Extension.ofBase (FriDomain.foldNode parent arity index (size - 1))]
          for challenge in challenges do
            unless (← readExtension) == challenge do throw "native folding challenge differs"
            let folded ← checkFolded arity challenge polynomial
            let result ← readExtension
            unless Interpolation.foldRow parent arity index values challenge == some result &&
                Quotient.horner childPoint folded == result && Quotient.horner challenge row == result do
              throw "native row fold differs from the global folded polynomial"
            evaluations := evaluations + 1
          rows := rows + 1
  let mut matrices := 0
  let mut matrixRows := 0
  for parentBits in [1:10] do
    let parent ← readDomain parentBits
    for arityBits in [1:min parentBits 6 + 1] do
      let arity ← readDomain arityBits
      let child ← readDomain (parentBits - arityBits)
      let size := Domain.size arity
      for variant in [:8] do
        let polynomial := coefficients size variant
        let data := (List.range (Domain.size parent)).map (fun index =>
          Quotient.horner (Extension.ofBase (FriDomain.queryPoint parent index)) polynomial)
        checkValues polynomial
        checkValues data
        for challenge in [0, sample 41, 1] do
          unless (← readExtension) == challenge do throw "native matrix folding challenge differs"
          let folded ← checkFolded arity challenge polynomial
          unless (← readCount (Domain.size child)) == Domain.size child do throw "native folded matrix height differs"
          let result ← readList (Domain.size child) readExtension
          for index in [:Domain.size child] do
            let row := (data.drop (index * size)).take size
            let expected := Quotient.horner (Extension.ofBase (FriDomain.queryPoint child index)) folded
            unless result[index]? == some expected &&
                Interpolation.foldRow parent arity index row challenge == some expected do
              throw "native matrix fold differs from the global folded polynomial"
            matrixRows := matrixRows + 1
          matrices := matrices + 1
  let mut pairs := 0
  let mut pairEvaluations := 0
  for arityBits in [:7] do
    let arity ← readDomain arityBits
    let parent ← readDomain (arityBits + 2)
    let size := Domain.size arity
    let challenges := (Polynomial.foldingNodes parent arity 1).map Extension.ofBase ++ [0, sample 41]
    let left := (List.range size).map (fun index => sample (index + 7))
    let right := left.set (size / 2) (sample (size / 2 + 7) + sample 131)
    unless challenges.eraseDups == challenges && left != right do throw "row agreement preconditions differ"
    checkValues left
    checkValues right
    let mut agreements := 0
    for challenge in challenges do
      unless (← readExtension) == challenge do throw "native row comparison challenge differs"
      let first ← readExtension
      let second ← readExtension
      unless Interpolation.foldRow parent arity 1 left challenge == some first &&
          Interpolation.foldRow parent arity 1 right challenge == some second do
        throw "native distinct row folds differ"
      if first == second then agreements := agreements + 1
      pairEvaluations := pairEvaluations + 1
    unless (← readNat) == agreements && agreements == size - 1 do throw "distinct rows miss the sharp agreement bound"
    pairs := pairs + 1
  let counts := [rows, evaluations, matrices, matrixRows, pairs, pairEvaluations]
  unless counts == [4872, 24360, 936, 24048, 7, 141] do throw "incomplete global folding corpus"
  unless (← readList 6 readNat) == counts do throw "global folding coverage totals differ"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "global folding snapshot has trailing bytes"
  return counts

end AiurTests.Folding

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.Folding.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok (counts, _) => IO.println s!"Native global FRI rows, evaluations, matrices, matrix rows, distinct pairs and pair evaluations match: {counts}"
  | _ => throw (IO.userError "expected native global FRI folding snapshot")
