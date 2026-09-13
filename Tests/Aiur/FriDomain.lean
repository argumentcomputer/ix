/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FriDomain
import Tests.Aiur.EmissionReader

/-! Actual native reversal, coset points and FRI folding at every sampled
interpolation node, including singleton helpers and full machine widths.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader

namespace AiurTests.FriDomain

private def samples (bits exhaustive : Nat) : List Nat :=
  let mask := 2^bits - 1
  (List.range (min (mask + 1) exhaustive) ++ [mask, mask / 2, mask - 1] ++
    (List.range 16).map (fun seed => seed * 0x0a3751c9 % 2^bits)).mergeSort (· ≤ ·) |>.eraseDups

private def checkedIndices (expected : List Nat) : Reader Unit := do
  unless (← readCount expected.length) == expected.length do throw "FRI domain index inventory differs"

private def readDomain (bits : Nat) : Reader Domain.Subgroup := do
  let some domain := Domain.ofLogSize bits | throw "invalid FRI domain logarithm"
  return domain

private def readCorpus : Reader (List Nat) := do
  let header := "Aiur FRI domains v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "FRI domain version differs"
  let wordBits ← readCount 64
  unless wordBits == 32 || wordBits == 64 do throw "unsupported FRI native word width"
  let mut reversals := 0
  for bits in [:wordBits + 1] do
    let indices := samples bits 1024
    checkedIndices indices
    for index in indices do
      unless (← readNat) == index do throw "native bit reversal index differs"
      let reversed ← readNat
      unless FriDomain.reverseBits bits index == reversed &&
          FriDomain.wordReverse wordBits bits index == reversed &&
          FriDomain.reverseBits bits reversed == index do throw "native bit reversal differs"
      reversals := reversals + 1
  let emptyWidth ← readNat
  unless emptyWidth == 2^(wordBits - 1) && FriDomain.wordReverse wordBits 0 1 == emptyWidth &&
      FriDomain.reverseBits 0 1 == 0 do throw "native zero-width overflow differs"
  let mut points := 0
  for bits in [:33] do
    let domain ← readDomain bits
    let indices := samples bits 1024
    checkedIndices indices
    for index in indices do
      unless (← readNat) == index do throw "FRI query index differs"
      unless (← readField) == FriDomain.queryPoint domain index do throw "FRI query point differs"
      unless (← readField) == FriDomain.inputPoint domain index do throw "FRI input coset point differs"
      points := points + 1
  let mut nested := 0
  for parentBits in [:33] do
    let parent ← readDomain parentBits
    for childBits in [:parentBits + 1] do
      let child ← readDomain childBits
      let indices := samples childBits 4
      checkedIndices indices
      for index in indices do
        unless (← readNat) == index do throw "FRI nested index differs"
        let point ← readField
        unless point == FriDomain.queryPoint parent index && point == FriDomain.queryPoint child index do
          throw "FRI final-domain point differs"
        nested := nested + 1
  let mut rows := 0
  let mut slots := 0
  for parentBits in [:33] do
    let parent ← readDomain parentBits
    for arityBits in [:min parentBits 8 + 1] do
      let arity ← readDomain arityBits
      let height := parentBits - arityBits
      let child ← readDomain height
      let mask := 2^height - 1
      let indices := [0, mask / 2, mask, 0x0a3751c9 % 2^height] |>.mergeSort (· ≤ ·) |>.eraseDups
      checkedIndices indices
      for index in indices do
        unless (← readNat) == index do throw "FRI folding index differs"
        for slot in [:Domain.size arity] do
          let node ← readField
          let power ← readField
          let folded : ProofCodec.Extension := ⟨← readField, ← readField⟩
          unless node == FriDomain.foldNode parent arity index slot &&
              node == FriDomain.queryPoint parent (index * Domain.size arity + slot) do
            throw "native FRI folding node differs"
          unless power == FriDomain.queryPoint child index && power == node.pow (Domain.size arity) do
            throw "native FRI reduced point differs"
          unless folded == ProofCodec.Extension.mk (G.ofNat (slot + 1)) (G.ofNat (slot * 19 + 3)) do
            throw "native FRI fold_row selected a different evaluation"
          slots := slots + 1
        rows := rows + 1
  let counts := [reversals, points, nested, rows, slots]
  unless counts == [if wordBits == 64 then 58295 else 24951, 24951, 9617, 990, 50042] do
    throw "incomplete FRI domain corpus"
  unless (← readList 5 readNat) == counts do throw "FRI domain coverage totals differ"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "FRI domain snapshot has trailing bytes"
  return counts

end AiurTests.FriDomain

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.FriDomain.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok (counts, _) => IO.println s!"FRI native reversals, query points, nested points, rows and fold nodes match: {counts}"
  | _ => throw (IO.userError "expected native FRI domain snapshot")
