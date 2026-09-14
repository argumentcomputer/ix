/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Polynomial
import Tests.Aiur.EmissionReader

/-! Compare the native final-polynomial Horner iterator and independent
upstream coefficient operations over both native fields.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader

namespace AiurTests.Polynomial

private def baseSample (seed : Nat) : G := if seed == 2 then 0 - 1 else G.ofNat seed

private def extensionSample (seed : Nat) : ProofCodec.Extension :=
  if seed < 3 then .ofBase (baseSample seed) else ⟨G.ofNat (seed * 67), G.ofNat (seed + 1)⟩

private def coefficients [OfNat R 0] [OfNat R 1] (length seed : Nat) (sample : Nat → R) : List R :=
  (List.range length).map fun index =>
    if seed == 0 then 0
    else if seed == 1 then if index + 1 == length then 1 else 0
    else if seed == 2 && index ≥ length / 2 then 0
    else sample (seed * 67 + index * 13 + 3)

private def readCases [Lean.Grind.CommRing R] [BEq R] [LawfulBEq R]
    (sample : Nat → R) (readValue : Reader R) : Reader (List Nat) := do
  let readValues := do readList (← readCount) readValue
  let domain ← readValues
  unless domain == (List.range 80).map sample do throw "native polynomial sample domain differs"
  let mut count := 0
  let mut divisions := 0
  let mut zeroCases := 0
  let mut rootSets := 0
  let mut repeatedSets := 0
  for length in [0, 1, 2, 3, 4, 7, 8, 9, 16, 31, 32, 65] do
    for rightLength in [0, 1, length, length + 3] do
      for seed in [:8] do
        let left ← readValues
        let right ← readValues
        unless left == coefficients length seed sample && right == coefficients rightLength seed sample do
          throw "polynomial coefficient inventory differs"
        let root ← readValue
        let point ← readValue
        unless root == sample seed && point == (if seed % 3 == 0 then root else sample (seed + 19)) do
          throw "polynomial evaluation point inventory differs"
        let atPoint ← readValue
        let atRoot ← readValue
        let rightValue ← readValue
        unless atPoint == Quotient.horner point left && atRoot == Quotient.horner root left &&
            rightValue == Quotient.horner point right do throw "native Horner iterator differs"
        let added ← readValues
        let difference ← readValues
        unless added == Polynomial.add left right && difference == Polynomial.sub left right do
          throw "native coefficient addition or subtraction differs"
        unless Quotient.horner point added == atPoint + rightValue &&
            Quotient.horner point difference == atPoint - rightValue do throw "coefficient evaluation identity differs"
        if left.isEmpty then
          unless (Polynomial.divide root left).isEmpty do throw "total empty quotient differs"
        else
          let quotient ← readValues
          let remainder ← readValue
          unless quotient == Polynomial.divide root left && remainder == atRoot do
            throw "native synthetic quotient or remainder differs"
          unless quotient.length + 1 == left.length &&
              (point - root) * Quotient.horner point quotient + remainder == atPoint do
            throw "synthetic division identity differs"
          divisions := divisions + 1
        let roots ← readNat
        let agreements ← readNat
        unless roots == domain.countP (fun value => Quotient.horner value left == 0) &&
            agreements == domain.countP (fun value => Quotient.horner value difference == 0) do
          throw "native polynomial root counts differ"
        if left.all (· == 0) then zeroCases := zeroCases + 1
        else unless roots < left.length do throw "polynomial exceeds its distinct-root bound"
        unless difference.all (· == 0) || agreements < max left.length right.length do
          throw "different polynomials exceed their agreement bound"
        count := count + 1
  for length in [0, 1, 2, 3, 7, 16, 31, 32, 63] do
    for variant in [:4] do
      let roots ← readValues
      let expected := (List.range length).map fun index => sample
        (if variant == 0 then index else if variant == 1 then length - index - 1
          else if variant == 2 then 0 else index / 2)
      unless roots == expected do throw "native root-set inventory differs"
      let polynomial ← readValues
      unless polynomial == Polynomial.fromRoots roots do throw "native vanishing coefficients differ"
      unless polynomial.length == roots.length + 1 && polynomial.getLast? == some 1 do
        throw "native vanishing polynomial is not monic"
      for point in [sample 0, sample 2, sample 17, sample 79] do
        let value ← readValue
        unless value == Quotient.horner point polynomial && value == LogUp.product (roots.map (point - ·)) do
          throw "native vanishing evaluation differs"
      let rootCount ← readNat
      unless rootCount == domain.countP (fun point => Quotient.horner point polynomial == 0) && rootCount ≤ roots.length do
        throw "native vanishing root count differs"
      let repeated := roots.eraseDups.length != roots.length
      if repeated then repeatedSets := repeatedSets + 1
      else unless rootCount == roots.length do throw "native distinct-root polynomial lost a root"
      rootSets := rootSets + 1
  return [count, divisions, zeroCases, rootSets, repeatedSets]

private def readCorpus : Reader (List Nat × List Nat) := do
  let header := "Aiur coefficient polynomials v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "polynomial snapshot version differs"
  let base ← readCases baseSample readField
  let extension ← readCases extensionSample (do return ⟨← readField, ← readField⟩)
  unless (← readList 10 readNat) == base ++ extension do throw "native polynomial coverage totals differ"
  unless base == [384, 352, 80, 36, 14] && extension == base do throw "incomplete native polynomial corpus"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "polynomial snapshot has trailing bytes"
  return (base, extension)

end AiurTests.Polynomial

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.Polynomial.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok (counts, _) => IO.println s!"Native polynomial arithmetic/divisions/zero cases/root sets/repeated sets match: {counts}"
  | _ => throw (IO.userError "expected native coefficient polynomial snapshot")
