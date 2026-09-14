/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.VerifierAccumulator
import Tests.Aiur.EmissionReader

/-! Combined comparison with native graph, LogUp and selector calls. The
native test reproduces the verifier's private wiring/fold/recombination;
its constructed openings are arithmetic fixtures, not authenticated proofs.
-/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)

namespace AiurTests.VerifierArithmetic

open NativeAIR.VerifierArithmetic

private def readExtension : Reader Extension := do return ⟨← readField, ← readField⟩
private def readExtensions : Reader (List Extension) := do readList (← readCount 100000) readExtension
private def readPair : Reader ProofShape.Pair := do return ⟨← readExtensions, ← readExtensions⟩
private def readClaims : Reader (List (List G)) := do readList (← readCount) readValues
private def readChallenges : Reader Challenges := do
  return ⟨← readExtension, ← readExtension, ← readExtension, ← readExtension⟩

private def readOpening (circuits : Array KeyCodec.Circuit) : Reader ProofShape.Row := do
  let index ← readNat
  let some circuit := circuits[index]? | throw "opening circuit index out of bounds"
  let bits ← readNat
  unless bits < 256 do throw "opening exponent is not a byte"
  let main ← readPair
  let stage2 ← readPair
  let preprocessed ← readOption readPair
  let quotient ← readExtensions
  let accumulator ← readExtension
  let row : ProofShape.Row := ⟨index, circuit, bits.toUInt8, main, stage2, preprocessed, quotient, accumulator⟩
  unless row.fits ⟨1, 0, 0, 1, 64, 0, 0⟩ do throw "opening fixture is not shaped"
  unless row.preprocessed.isNone == (row.circuit.preprocessedWidth == 0) do throw "opening preprocessed slot differs"
  return row

private def readEvaluation (challenges : Challenges) (row : ProofShape.Row) (entering : Extension) : Reader (Nat × Bool) := do
  let selectors : NativeAIR.Domain.Selectors Extension :=
    ⟨← readExtension, ← readExtension, ← readExtension, ← readExtension⟩
  let publics := (← readExtensions).toArray
  let delta := (← readExtensions).toArray
  let nodes := (← readExtensions).toArray
  let user ← readExtensions
  let lookups ← readExtensions
  let composition ← readExtension
  let quotient ← readExtension
  let accepted ← readBool
  let some result := evaluate challenges row entering | throw "opening arithmetic unexpectedly undefined"
  unless result.domain.val == row.logDegree.toNat && result.selectors == selectors do throw "opening domain/selectors differ"
  unless NativeAIR.VerifierArithmetic.publics challenges entering row.accumulator == publics do
    throw "opening public coordinates differ"
  unless deltaScaled result.domain entering row.accumulator == delta do throw "opening normalized delta differs"
  unless result.nodeValues == nodes do throw "opening graph node values differ"
  unless result.userValues == user && result.lookupValues == lookups do throw "opening constraint order/coordinates differ"
  unless result.constraints.length == row.circuit.constraintCount do throw "opening constraint count differs"
  unless Quotient.composition challenges.alpha result.constraints == composition do throw "opening Horner fold differs"
  unless result.quotientValue == quotient do throw "opening quotient recombination differs"
  unless result.accepts challenges.alpha == accepted && check challenges row entering == some accepted do
    throw "opening arithmetic acceptance differs"
  unless (composition == NativeAIR.Domain.vanishing result.domain challenges.zeta * quotient) == accepted do
    throw "opening quotient polynomial identity differs"
  return (nodes.size, accepted)

private def checkGuards (challenges : Challenges) (row : ProofShape.Row) (entering : Extension) (accepted : Bool) : Reader Unit := do
  let badCurrent := { row with stage2 := { row.stage2 with current := [] } }
  let badNext := { row with stage2 := { row.stage2 with next := [] } }
  let badQuotient := { row with quotient := row.quotient ++ [0] }
  let badLog := { row with logDegree := 33 }
  let badRoot := { row with circuit := { row.circuit with graph :=
    { row.circuit.graph with zeros := row.circuit.graph.zeros ++ [row.circuit.graph.nodes.length] } } }
  for malformed in [badCurrent, badNext, badQuotient, badLog, badRoot] do
    unless (evaluate challenges malformed entering).isNone do throw "malformed opening read accepted"
  let some domain := NativeAIR.Domain.ofLogSize row.logDegree.toNat | throw "opening domain missing"
  for pole in [1, Extension.ofBase (NativeAIR.Domain.lastPoint domain)] do
    unless (evaluate { challenges with zeta := pole } row entering).isNone do throw "opening selector pole accepted"
  if row.preprocessed.isSome then
    unless (evaluate challenges { row with preprocessed := none } entering).isNone do
      throw "missing preprocessed opening accepted"
  if accepted then
    let first :: rest := row.quotient | throw "empty shaped quotient"
    unless check challenges { row with quotient := (first + 1) :: rest } entering == some false do
      throw "altered opening quotient accepted"

private def readCorpus : Reader Unit := do
  let header := "Aiur verifier arithmetic v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "verifier arithmetic snapshot version differs"
  unless (← readNat) == 10 do throw "incomplete opening circuits"
  let circuits := (← readList 10 do
    let bytes ← takeBytes (← readCount 1000000)
    let some (circuit, []) := KeyCodec.readCircuit bytes.data.toList | throw "invalid opening circuit"
    return circuit).toArray
  unless (← readNat) == 960 do throw "incomplete opening assignments"
  let mut nodeCount := 0
  let mut acceptedCount := 0
  for index in [:circuits.size] do
    let some circuit := circuits[index]? | throw "missing opening circuit"
    let largest := 31 - (ProofShape.quotientDegree circuit).log2
    for bits in [0, 1, 2, 4, 8, 16, 24, largest] do
      for seed in [:12] do
        unless (← readNat) == seed do throw "opening seed order differs"
        let challenges ← readChallenges
        let entering ← readExtension
        let row ← readOpening circuits
        unless row.circuitIndex == index && row.logDegree.toNat == bits do throw "opening fixture order differs"
        let (nodes, accepted) ← readEvaluation challenges row entering
        unless accepted == (seed % 2 == 0) do throw "opening acceptance inventory differs"
        nodeCount := nodeCount + nodes
        if accepted then acceptedCount := acceptedCount + 1
        checkGuards challenges row entering accepted
  unless nodeCount == 32064 && acceptedCount == 480 do throw "incomplete opening node/acceptance coverage"
  unless (← readNat) == 72 do throw "incomplete claim assignments"
  let mut definedClaims := 0
  for seed in [:12] do
    for count in [0, 1, 2, 3, 7, 16] do
      let challenges ← readChallenges
      let claims ← readClaims
      unless claims.length == count do throw "public claim count differs"
      for claim in claims do
        unless claimMessage challenges claim == (← readExtension) do throw "public claim compression differs"
      let expected ← readOption readExtension
      unless initialAccumulator challenges claims == expected do throw "initial accumulator differs"
      unless expected.isSome == (seed % 3 != 0 || count == 0) do throw "public claim pole inventory differs"
      if expected.isSome then definedClaims := definedClaims + 1
      unless (verify challenges claims []).isNone do throw "empty active circuit list accepted"
  unless definedClaims == 52 do throw "incomplete public claim pole coverage"
  unless (← readNat) == 48 do throw "incomplete accumulator chains"
  let mut acceptedChains := 0
  let mut unbalancedChains := 0
  let mut rejectedChains := 0
  for _seed in [:12] do
    for count in [1, 2, 3, 10] do
      let challenges ← readChallenges
      let claims ← readClaims
      unless (← readNat) == count do throw "accumulator chain length differs"
      let some initial := initialAccumulator challenges claims | throw "unexpected chain claim pole"
      let mut entering := initial
      let mut rows := []
      for _ in [:count] do
        let row ← readOpening circuits
        let _ ← readEvaluation challenges row entering
        rows := rows ++ [row]
        entering := row.accumulator
      let expected ← readOption readBool
      unless verify challenges claims rows == expected do throw "ordered accumulator chain differs"
      match expected with
      | some true => acceptedChains := acceptedChains + 1
      | some false => unbalancedChains := unbalancedChains + 1
      | none => rejectedChains := rejectedChains + 1
  unless acceptedChains == 16 && unbalancedChains == 16 && rejectedChains == 16 do
    throw "incomplete final/interior accumulator rejection coverage"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "verifier arithmetic snapshot has trailing bytes"

def run (path : System.FilePath) : IO Unit := do
  match readCorpus.run ((← IO.FS.readBinFile path), 0) with
  | .error error => throw (IO.userError error)
  | .ok _ =>
    IO.println "verifier arithmetic: 960 openings, 32064 node values and malformed reads/quotients/poles match"
    IO.println "verifier accumulators: 52 defined/20 rejected claim cases and 16 accepted/16 unbalanced/16 rejected chains match"

end AiurTests.VerifierArithmetic

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.VerifierArithmetic.run path
  | _ => throw (IO.userError "expected native verifier arithmetic snapshot")
