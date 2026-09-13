/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CheckedCircuit
import Tests.Aiur.EmissionReader

/-! Native guard decisions across operand widths, scopes and control trees. -/

open Aiur Aiur.Bytecode Aiur.NativeAIR Aiur.NativeAIR.OpEmitter
open Aiur.NativeAIR.BlockEmitter AiurTests.EmissionReader

namespace AiurTests.EmissionChecks

private def readCorpus : Reader (Nat × Nat × Nat) := do
  let header := "Aiur emission checks v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "emission check snapshot version differs"
  let scopes ← readList (← readCount) readNat
  unless scopes == [0, 1, 2, 3, 4, 7, 8, 9, 12, 16, 2^64 - 9, 2^64 - 2, 2^64 - 1] do
    throw "emission check snapshot scope boundaries differ"
  let mut operationChecks := 0
  let mut sequenceChecks := 0
  let mut controlChecks := 0
  for group in [:← readCount] do
    let mut ops := #[]
    for index in [:← readCount] do
      let op ← readOp
      ops := ops.push op
      unless (← readNat) == op.outputSize do throw s!"logical output size differs: group {group}, operation {index}"
      for available in scopes do
        let valid ← readBool
        unless valid == op.emissionInputs available do
          throw s!"operand check differs: group {group}, operation {index}, scope {available}"
        let expected ← readOption readNat
        unless expected == checkEmissionOps [op] available do
          throw s!"single operation scope differs: group {group}, operation {index}, scope {available}"
        if valid && available ≤ 32 && op.outputSize ≤ 64 then
          let some emitted := emitOp (.konst 1) (.konst 0) available op (advice 0 available)
            | throw "checked operation failed to emit"
          unless emitted.outputs.size == op.outputSize do throw "checked operation output size differs"
        operationChecks := operationChecks + 1
    for available in scopes do
      let expected ← readOption readNat
      unless expected == checkEmissionOps ops.toList available do
        throw s!"operation sequence scope differs: group {group}, scope {available}"
      if let some next := expected then
        if available ≤ 32 && next ≤ 128 then
          let some emitted := emitOps (.konst 1) (.konst 0) ops.toList (advice 0 available) available
            | throw "checked operation sequence failed to emit"
          unless emitted.values.size == next do throw "checked sequence final scope differs"
      sequenceChecks := sequenceChecks + 1
  for index in [:← readCount] do
    let block ← readBlock 64
    for _ in [:← readCount] do
      let available ← readNat
      let selectors ← readNat
      let yieldSize ← readOption readNat
      let valid ← readBool
      unless valid == block.emissionChecks available selectors yieldSize do
        throw s!"control scope differs: block {index}, values {available}, selectors {selectors}, yields {yieldSize}"
      if valid && available ≤ 32 then
        let selectorTable := CircuitEmitter.selectorExprs available selectors
        let some entry := blockSelector selectorTable block | throw "checked block selector is absent"
        let some emitted := emitBlock selectorTable ⟨0, available, .konst 0⟩ entry
            (advice 0 available) (available + selectors) 0 block
          | throw "checked block failed to emit"
        unless emitted.yields.all (fun part => yieldSize == some part.values.size) do
          throw "checked block escaping yield width differs"
      controlChecks := controlChecks + 1
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "emission check snapshot has trailing bytes"
  unless (operationChecks, sequenceChecks, controlChecks) == (1365, 1157, 6500) do
    throw "emission check snapshot coverage differs"
  return (operationChecks, sequenceChecks, controlChecks)

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok ((operations, sequences, controls), _) =>
    IO.println s!"emission checks: {operations} operations, {sequences} sequences and {controls} control scopes match"

end AiurTests.EmissionChecks

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.EmissionChecks.run path
  | _ => throw (IO.userError "expected native emission check snapshot")
