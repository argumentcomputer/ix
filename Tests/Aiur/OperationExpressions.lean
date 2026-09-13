/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Tests.Aiur.EmissionReader
import Ix.Aiur.Proofs.EmissionAllocation

/-! Compare complete native operation and sequence expression trees, including
metadata, cursor movement, equations, and superposed physical lookup slots.
The corpus supplies the actual native operations, inputs, and assignments. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.OpEmitter Aiur.NativeAIR.Compiler

namespace AiurTests.OperationExpressions

open AiurTests.EmissionReader

private def assignment (row : Array G) : Values G :=
  ⟨(fun source _ => match source with | .main => row | _ => #[]), #[], 1, 0, 1⟩

private def callData (calls : List (Bytecode.AIR.Call × (Fin 6 → G))) :=
  calls.map fun (call, gap) => (call, List.ofFn gap)

private def sameEmission (left right : AIR.OpsEmission) : Bool :=
  left.values == right.values && left.column == right.column && left.equations == right.equations &&
    left.queries == right.queries && callData left.calls == callData right.calls

private def readSequence (rows : List (Array G)) (label : String) : Reader (List LookupEmitter.QueryExpr × Nat) := do
  let first ← readNat
  let lookup ← readNat
  let selector ← readExpr 64
  let rank ← readExpr 64
  let inputs ← readMap
  let ops ← readList (← readCount) readOp
  unless inputs.all (·.expr.noConstantNegs) do throw s!"invalid incoming normal form: {label}"
  let some emitted := emitOps selector rank ops inputs first
    | throw s!"symbolic operation sequence rejected native inputs: {label}"
  let column ← readNat
  let lookupEnd ← readNat
  let nativeMap ← readMap
  let equations ← readList (← readCount) (readExpr 64)
  unless column == emitted.column && lookupEnd == lookup + emitted.queries.length do
    throw s!"native operation cursor differs: {label}"
  unless nativeMap == emitted.values do
    throw s!"native output expression or degree differs: {label}; ops {repr ops}"
  unless equations == emitted.equations do
    throw s!"native operation constraint trees differ: {label}; ops {repr ops}"
  unless emitted.values.all (·.expr.noConstantNegs) do
    throw s!"native output lost the negation invariant: {label}"
  let validDegrees := inputs.all fun row => row.degree != 0 || row.expr.isConstant
  if validDegrees then
    let initial : Concrete.Bytecode.LayoutMState :=
      ⟨{ inputSize := inputs.size, selectors := 0, auxiliaries := first, lookups := lookup },
        .empty, rowDegrees inputs, #[]⟩
    let layout := ((ops.toArray.forM Concrete.Bytecode.opLayout).run initial).2
    unless rowDegrees nativeMap == layout.degrees && column == layout.functionLayout.auxiliaries do
      throw s!"native operation degrees or column allocation differs from compiler: {label}"
    unless emitted.values.all (fun row => row.degree != 0 || row.expr.isConstant) do
      throw s!"native operation lost the degree-zero constant invariant: {label}"
  for (row, seed) in rows.zipIdx do
    let expected ← readList nativeMap.size do return (← readField, ← readBool)
    let equationValues ← readList equations.length readField
    let values := assignment row
    let some evaluated := emitted.eval values | throw s!"symbolic evaluation failed: {label}, {seed}"
    unless evaluated.values.toList.map (fun value => (value.value, value.constant)) == expected &&
        evaluated.equations == equationValues do
      throw s!"native operation values differ: {label}, assignment {seed}"
    let some inputValues := evalRows values inputs | throw "undefined native input expressions"
    let some s := evalExpr values selector | throw "undefined native selector"
    let some r := evalExpr values rank | throw "undefined native rank"
    let some valued := AIR.emitOps (fun index => row[index]?.getD 0) s r ops inputValues first
      | throw s!"valued operation sequence rejected symbolic inputs: {label}"
    unless sameEmission evaluated valued do throw s!"symbolic/valued sequence differs: {label}, {seed}"
  return (LookupEmitter.queryParts lookup selector emitted.queries, if validDegrees then 1 else 0)

private def readReport (rows : List (Array G)) (index : Nat) : Reader (Nat × Nat × Nat) := do
  let branchless ← readBool
  let writers ← readCount 3
  unless writers == 1 || writers == 3 do throw "unexpected native writer count"
  let mut queries := []
  let mut allocations := 0
  for writer in [:writers] do
    let (parts, checked) ← readSequence rows s!"report {index}, writer {writer}"
    queries := queries ++ parts
    allocations := allocations + checked
  let count ← readCount 64
  for slot in [:count] do
    let native : ExprLookup := ⟨← readExpr 64, ← readList (← readCount) (readExpr 64)⟩
    let expected := LookupEmitter.slot branchless queries slot
    unless native == expected do throw s!"native lookup expression trees differ: report {index}, slot {slot}"
    for (row, seed) in rows.zipIdx do
      let weight ← readField
      let message ← readValues
      let values := assignment row
      unless expected.eval goldilocksOps values == some (weight, message) do
        throw s!"native slot values differ: report {index}, slot {slot}, assignment {seed}"
      let some parts := queries.mapM (LookupEmitter.QueryExpr.eval values)
        | throw "undefined raw query expressions"
      unless weight == AIR.querySlotMultiplicity parts slot &&
          message == AIR.slotMessage branchless (AIR.querySlotParts parts slot) do
        throw "symbolic slot and valued query parts differ"
  return (writers, (if writers == 3 then 1 else 0), allocations)

private def readCorpus : Reader Nat := do
  let header := "Aiur operation expressions v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "operation snapshot version differs"
  unless (← readCount) == 4 do throw "incomplete operation assignments"
  let rows ← readList 4 do return (← readValues).toArray
  unless rows.all (·.size == 512) do throw "operation assignment width differs"
  unless (← readCount) == 876 do throw "incomplete operation expression corpus"
  let mut sequences := 0
  let mut shared := 0
  let mut allocations := 0
  for index in [:876] do
    let (count, combined, checked) ← readReport rows index
    sequences := sequences + count
    shared := shared + combined
    allocations := allocations + checked
  unless sequences == 1752 && shared == 438 do throw "incomplete native operation coverage"
  unless allocations == 1168 do throw "incomplete degree-valid compiler allocation coverage"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "operation snapshot has trailing bytes"
  return allocations

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok (allocations, _) =>
    IO.println s!"operation expressions: 1,752 native sequences, 7,008 assignments, 438 shared-slot cases and {allocations} compiler allocations match"

end AiurTests.OperationExpressions

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.OperationExpressions.run path
  | _ => throw (IO.userError "expected native operation expression snapshot")
