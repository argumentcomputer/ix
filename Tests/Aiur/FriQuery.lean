/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.FriQuery
import Tests.Aiur.EmissionReader

/-! Replay the actual private FRI query routine using calls captured through
the public verifier's folding hook. Inputs come from known source polynomials
and ordinary native PCS proofs, including every authenticated input row.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)

namespace AiurTests.FriQuery

private structure Source where
  logSize : Nat
  columns : List (List G)

private structure Opening where
  arity : Domain.Subgroup
  siblings : List (List Extension)

private def readExtension : Reader Extension := return ⟨← readField, ← readField⟩

private def domain (bits : Nat) : Reader Domain.Subgroup := do
  let some result := Domain.ofLogSize bits | throw "invalid query domain"
  return result

private def readValues (read : Reader R) (length : Nat) : Reader (List R) := do
  unless (← readCount length) == length do throw "native query vector length differs"
  readList length read

private def checkValues [BEq R] (read : Reader R) (expected : List R) : Reader Unit := do
  unless (← readValues read expected.length) == expected do throw "native query vector differs"

private def layout (index finalBits : Nat) : List (List Nat) :=
  let offsets := match index with
    | 0 => [[0]] | 1 => [[2]] | 2 => [[6, 2], [2, 0]] | _ => [[3, 6], [3]]
  offsets.map (List.map (fun bits => bits + finalBits + if finalBits == 0 then 0 else 1))

private def polynomial (seed bits column : Nat) : List G :=
  (List.range (2^bits)).map (fun index => G.ofNat (seed * 101 + column * 29 + index * 13 + 1))

private def sources (caseIndex finalBits layoutIndex : Nat) : List (List Source) :=
  (layout layoutIndex finalBits).zipIdx.map fun (matrices, batch) =>
    matrices.zipIdx.map fun (bits, matrix) =>
      ⟨bits, (List.range (2 + matrix)).map (polynomial (caseIndex + batch * 7 + matrix) bits)⟩

private def readSources (expected : List (List Source)) : Reader Unit := do
  unless (← readCount expected.length) == expected.length do throw "query source batch count differs"
  for batch in expected do
    unless (← readCount batch.length) == batch.length do throw "query source matrix count differs"
    for source in batch do
      unless (← readNat) == source.logSize do throw "query source height differs"
      unless (← readCount source.columns.length) == source.columns.length do throw "query source width differs"
      for coefficients in source.columns do checkValues readField coefficients

/-- Derive each quotient polynomial from its known source coefficients.
The native input-reduction routine is not used to obtain these values. -/
private def groupedPolynomials (input : List (List Source)) (points : List Extension)
    (alpha : Extension) (blowup : Nat) : List (Nat × List Extension) := Id.run do
  let terms := input.flatten.flatMap fun source =>
    points.flatMap fun point => source.columns.map fun coefficients =>
      (source.logSize + blowup, Polynomial.divide point (coefficients.map Extension.ofBase))
  let heights := terms.map Prod.fst |>.mergeSort (· ≥ ·) |>.eraseDups
  return heights.map fun height =>
    let (_, coefficients) := terms.foldl (fun (power, sum) (logHeight, polynomial) =>
      if height == logHeight then (power * alpha, Polynomial.add sum (Polynomial.scale power polynomial))
      else (power, sum)) (1, [])
    (height, coefficients)

private def reducedOpenings (initial : Domain.Subgroup) (index : Nat)
    (polynomials : List (Nat × List Extension)) : Reader (List (Nat × Extension)) :=
  polynomials.mapM fun (height, coefficients) => do
    let current ← domain height
    unless height ≤ initial.val do throw "input exceeds the global query domain"
    let reducedIndex := index / 2^(initial.val - height)
    return (height, Quotient.horner (Extension.ofBase (FriDomain.inputPoint current reducedIndex)) coefficients)

private def checkInputRows (input : List (List Source)) (initial : Domain.Subgroup) (indices : List Nat)
    (blowup : Nat) (rows : List (List (List (List G)))) : Reader Unit := do
  for (batch, queries) in input.zip rows do
    for (index, matrices) in indices.zip queries do
      for (source, row) in batch.zip matrices do
        let current ← domain (source.logSize + blowup)
        let point := FriDomain.inputPoint current (index / 2^(initial.val - current.val))
        unless row == source.columns.map (Quotient.horner point) do throw "authenticated native input row differs from its source polynomial"

private def checkGuards (initial final : Domain.Subgroup) (index : Nat)
    (openings : List (Nat × Extension)) (rounds : List NativeAIR.FriQuery.Round)
    (finalPolynomial : List Extension) : Reader Unit := do
  unless (NativeAIR.FriQuery.run initial final (Domain.size initial) openings rounds).isNone &&
      (NativeAIR.FriQuery.run initial final index [] rounds).isNone &&
      (NativeAIR.FriQuery.check initial final index openings rounds (Polynomial.add [1] finalPolynomial)).isNone do
    throw "query admission or final polynomial guard differs"
  let some (height, value) := openings.head? | throw "missing initial query input"
  unless (NativeAIR.FriQuery.run initial final index ((height + 1, value) :: openings.tail) rounds).isNone &&
      (NativeAIR.FriQuery.run initial final index ((height, value) :: openings) rounds).isNone do
    throw "initial or duplicated reduced height was accepted"
  if let round :: rest := rounds then
    let singleton ← domain 0
    unless (NativeAIR.FriQuery.run initial initial index openings rounds).isNone &&
        (NativeAIR.FriQuery.run initial final index openings ({ round with arity := singleton } :: rest)).isNone &&
        (NativeAIR.FriQuery.run initial final index openings ({ round with siblings := 0 :: round.siblings } :: rest)).isNone do
      throw "query round shape or terminal height guard differs"

private def readCase (caseIndex blowup finalBits maxArity layoutIndex : Nat) : Reader (Nat × Nat × Nat) := do
  let input := sources caseIndex finalBits layoutIndex
  let queries := 1 + layoutIndex + finalBits
  let globalBits := ((layout layoutIndex finalBits).flatten.foldl max 0) + blowup
  unless (← readList 6 readNat) == [blowup, finalBits, maxArity, queries, layoutIndex, globalBits] do
    throw "native query profile differs"
  let initial ← domain globalBits
  let final ← domain (finalBits + blowup)
  readSources input
  let points ← readValues readExtension (1 + layoutIndex % 2)
  let some first := points.head? | throw "missing opening point"
  unless points == (if layoutIndex % 2 == 0 then [first] else [first, first + ⟨19, 3⟩]) do
    throw "native query opening points differ"
  for batch in input do
    for source in batch do
      for point in points do
        checkValues readExtension (source.columns.map fun coefficients =>
          Quotient.horner point (coefficients.map Extension.ofBase))
  let inputRows ← input.mapM fun batch =>
    readList queries (batch.mapM fun source => readValues readField source.columns.length)
  let random ← readList (← readCount 34) readExtension
  let some alpha := random.head? | throw "missing query batching challenge"
  let indices ← readList queries do
    unless (← readNat) == globalBits do throw "native query sample width differs"
    let index ← readNat
    unless index < Domain.size initial do throw "native query index exceeds its domain"
    return index
  let roundCount ← readCount 32
  unless random.length == roundCount + 1 do throw "native query challenge count differs"
  let openings ← readList roundCount do
    let arityBits ← readNat
    unless 0 < arityBits && arityBits ≤ maxArity do throw "native query arity exceeds its profile"
    let arity ← domain arityBits
    let siblings ← readList queries (readValues readExtension (Domain.size arity - 1))
    return Opening.mk arity siblings
  unless (openings.map (fun opening => opening.arity.val)).sum + final.val == initial.val do
    throw "native query round heights do not reach the final domain"
  let finalPolynomial ← readValues readExtension (2^finalBits)
  checkInputRows input initial indices blowup inputRows
  let polynomials := groupedPolynomials input points alpha blowup
  let callCount ← readNat
  unless callCount == queries * roundCount do throw "native query fold call count differs"
  let results ← indices.zipIdx.mapM fun (index, query) => do
    let reduced ← reducedOpenings initial index polynomials
    let rounds ← (openings.zip random.tail).mapM fun (opening, challenge) => do
      let some siblings := opening.siblings[query]? | throw "missing native query siblings"
      return NativeAIR.FriQuery.Round.mk opening.arity challenge siblings
    let some result := NativeAIR.FriQuery.check initial final index reduced rounds finalPolynomial
      | throw "native accepted query fails checked reconstruction or final evaluation"
    unless result.rows.length == roundCount && result.state.domain == final &&
        result.state.index == index / 2^(globalBits - final.val) do
      throw "checked query chain dimensions differ"
    for (round, row) in rounds.zip result.rows do
      unless (← readList 3 readNat) == [row.index, row.domain.val, round.arity.val] &&
          (← readExtension) == round.challenge do
        throw "native query fold metadata differs"
      checkValues readExtension row.values
      let folded ← readExtension
      let parent ← domain (row.domain.val + round.arity.val)
      unless Interpolation.foldRow parent round.arity row.index row.values round.challenge == some folded do
        throw "native query row folding differs"
    checkGuards initial final index reduced rounds finalPolynomial
    return result
  for result in results do
    unless (← readNat) == result.state.index && (← readExtension) == result.state.value &&
        Quotient.horner (Extension.ofBase (FriDomain.queryPoint final result.state.index)) finalPolynomial == result.state.value do
      throw "native query final index or polynomial value differs"
  return (queries, roundCount, callCount)

private def readCorpus : Reader (List Nat) := do
  let header := "Aiur native FRI query chains v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "FRI query version differs"
  let mut cases := 0
  let mut totalQueries := 0
  let mut totalRounds := 0
  let mut totalCalls := 0
  for blowup in [1:3] do
    for finalBits in [:3] do
      for maxArity in [1:5] do
        for layoutIndex in [:4] do
          let (queries, rounds, calls) ← try readCase cases blowup finalBits maxArity layoutIndex
            catch message => throw s!"query case {cases}: {message}"
          cases := cases + 1
          totalQueries := totalQueries + queries
          totalRounds := totalRounds + rounds
          totalCalls := totalCalls + calls
  let counts := [cases, totalQueries, totalRounds, totalCalls]
  unless counts == [96, 336, 246, 1030] do throw "incomplete native query corpus"
  unless (← readList 4 readNat) == counts do throw "native query coverage totals differ"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "native query snapshot has trailing bytes"
  return counts

end AiurTests.FriQuery

def main (args : List String) : IO Unit := do
  match args with
  | [path] =>
    match AiurTests.FriQuery.readCorpus.run ((← IO.FS.readBinFile path), 0) with
    | .error message => throw (IO.userError message)
    | .ok (counts, _) => IO.println s!"Native FRI proofs, queries, rounds and fold calls match: {counts}"
  | _ => throw (IO.userError "expected native FRI query snapshot")
