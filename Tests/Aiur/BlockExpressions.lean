/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.BlockLookups
import Tests.Aiur.EmissionReader

/-! Compare actual native control trees and full symbolic block emission,
including incoming gates distinct from block entries and prior outer yields. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.OpEmitter Aiur.NativeAIR.Compiler
open Aiur.NativeAIR.BlockEmitter AiurTests.EmissionReader

namespace AiurTests.BlockExpressions



private def readEvaluatedMap (size : Nat) : Reader (Array AIR.RowValue) := do
  return (← readList size do return AIR.RowValue.mk (← readField) (← readNat) (← readBool)).toArray

private def readReport (index : Nat) : Reader Nat := do
  let label := s!"block {index}"
  let branchless ← readBool
  let context : Context := ⟨← readNat, ← readNat, ← readExpr 256⟩
  let selectors := (← readList (← readCount) (readExpr 256)).toArray
  let column ← readNat
  let lookup ← readNat
  let incoming ← readExpr 256
  let inputs ← readMap
  let block ← readBlock 64
  let entry ← readExpr 256
  unless blockSelector selectors block == some entry do throw s!"native block selector differs: {label}"
  let some emitted := emitBlock selectors context incoming inputs column lookup block
    | throw s!"symbolic block rejected native inputs: {label}"
  unless (← readNat) == emitted.column && (← readNat) == emitted.lookup do
    throw s!"native block cursors differ: {label}"
  let nativeMap ← readMap
  unless nativeMap == emitted.values do throw s!"native block value expressions or degrees differ: {label}"
  let equations ← readList (← readCount 8192) (readExpr 256)
  unless equations == emitted.equations do throw s!"native block constraint trees differ: {label}"
  unless inputs.all (·.expr.noConstantNegs) && emitted.values.all (·.expr.noConstantNegs) do
    throw s!"block lost the negation invariant: {label}"
  let lookupCount ← readCount 4096
  unless lookupCount == emitted.lookup + 2 do throw "incomplete native lookup range"
  let lookups ← readList lookupCount do
    return ExprLookup.mk (← readExpr 256) (← readList (← readCount) (readExpr 256))
  for (native, slot) in lookups.zipIdx do
    unless native == BlockEmitter.lookup branchless emitted slot do
      throw s!"native block lookup expression trees differ: {label}, slot {slot}"
  let yields ← readList (← readCount) do
    return YieldExpr.mk (← readExpr 256) (← readMap)
  let expectedYields := [YieldExpr.mk (.konst 99) inputs, YieldExpr.mk (.konst 100) inputs] ++ emitted.yields
  unless yields.map (fun part => (part.selector, part.values)) ==
      expectedYields.map (fun part => (part.selector, part.values)) do
    throw s!"native escaping yield expression trees differ: {label}"
  let count ← readCount
  unless count == 4 do throw "incomplete native block assignments"
  for seed in [:count] do
    let row := (← readList (← readCount 8192) readField).toArray
    let values := assignment row
    let outputValues ← readEvaluatedMap nativeMap.size
    let equationValues ← readList equations.length readField
    let some evaluated := emitted.eval values | throw s!"undefined block expression: {label}, assignment {seed}"
    unless evaluated.values == outputValues && evaluated.equations == equationValues do
      throw s!"native block expression values differ: {label}, assignment {seed}"
    let some inputValues := evalRows values inputs | throw "undefined incoming block expressions"
    let some selected := selectors.mapM (evalExpr values) | throw "undefined block selectors"
    let some s := evalExpr values incoming | throw "undefined incoming gate"
    let some rank := evalExpr values context.rank | throw "undefined rank"
    let some valued := block.emitRow (fun index => row[index]?.getD 0) (selectorAt selected)
        (context.valued rank) s inputValues column lookup
      | throw s!"valued block rejected symbolic inputs: {label}"
    unless sameBlockEmission evaluated valued do throw s!"symbolic/valued block differs: {label}, assignment {seed}"
    for (native, slot) in lookups.zipIdx do
      let weight ← readField
      let message ← readList native.args.length readField
      unless native.eval goldilocksOps values == some (weight, message) do
        throw s!"native lookup values differ: {label}, slot {slot}, assignment {seed}"
      let expected := if slot == 0 then
          (0, AIR.slotMessage branchless (valued.returns.map fun part => (part.1, AIR.functionMessage part.2)))
        else (AIR.querySlotMultiplicity valued.queries slot, AIR.slotMessage branchless (AIR.querySlotParts valued.queries slot))
      unless (weight, message) == expected do throw s!"symbolic/valued lookup differs: {label}, slot {slot}"
    for yielded in yields do
      let gate ← readField
      let outputs ← readEvaluatedMap yielded.values.size
      unless yielded.eval values == some (gate, outputs) do throw s!"native yield values differ: {label}, assignment {seed}"
  return count

private def readCorpus : Reader Unit := do
  let header := "Aiur block expressions v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "block snapshot version differs"
  unless (← readCount) == 384 do throw "incomplete native control tree corpus"
  let mut assignments := 0
  for index in [:384] do assignments := assignments + (← readReport index)
  unless assignments == 1536 do throw "incomplete native block coverage"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "block snapshot has trailing bytes"

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok _ => IO.println "block expressions: 384 native control trees and 1,536 assignments match"

end AiurTests.BlockExpressions

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.BlockExpressions.run path
  | _ => throw (IO.userError "expected native block expression snapshot")
