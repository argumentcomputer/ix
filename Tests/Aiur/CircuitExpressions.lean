/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CircuitCompletion
import Tests.Aiur.EmissionReader

/-! Actual native function and circuit records drive both symbolic and valued
emission. Check all frontend expression trees, physical slots, and metadata. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.OpEmitter Aiur.NativeAIR.Compiler
open Aiur.NativeAIR.CircuitEmitter AiurTests.EmissionReader

namespace AiurTests.CircuitExpressions

private def readLayout : Reader Bytecode.FunctionLayout := do
  return ⟨← readNat, ← readNat, ← readNat, ← readNat⟩

private def sameMember (left right : AIR.MemberEmission) : Bool :=
  left.functionIndex == right.functionIndex && left.selectorBase == right.selectorBase &&
    left.function.layout == right.function.layout && left.function.entry == right.function.entry &&
    left.function.constrained == right.function.constrained && sameBlockEmission left.body right.body

private def sameEmission (left right : AIR.CircuitEmission) : Bool :=
  left.members.length == right.members.length && (left.members.zip right.members).all (fun (a, b) => sameMember a b) &&
    left.selector == right.selector && left.multiplicity == right.multiplicity &&
    List.ofFn left.rankBytes == List.ofFn right.rankBytes &&
    left.width == right.width && left.selectorStart == right.selectorStart && left.selectorCount == right.selectorCount &&
    left.lookupCount == right.lookupCount && left.branchless == right.branchless && left.equations == right.equations &&
    left.queries.map (fun part => (part.slot, part.selector, part.message)) ==
      right.queries.map (fun part => (part.slot, part.selector, part.message)) && left.returns == right.returns

private def readCircuit (program : Bytecode.Toplevel) (circuit : Bytecode.Circuit) (label : String) : Reader Nat := do
  unless circuit.validateRowCounts program do throw s!"native circuit fails checked selector bounds: {label}"
  unless 7 ≤ circuit.layout.auxiliaries && circuit.members.all (fun index =>
      program.functions[index]!.layout.inputSize ≤ circuit.layout.inputSize &&
      program.functions[index]!.layout.auxiliaries ≤ circuit.layout.auxiliaries) do
    throw s!"native circuit fails compiler column bounds: {label}"
  let some emitted := emitCircuit program circuit | throw s!"symbolic circuit rejected native inputs: {label}"
  unless (← readBool) == emitted.branchless do throw s!"native circuit branchless decision differs: {label}"
  unless (← readNat) == emitted.width && (← readNat) == emitted.selectorStart && (← readNat) == emitted.selectorCount do
    throw s!"native circuit column layout differs: {label}"
  unless emitted.readBound ≤ emitted.width do throw s!"circuit read premise exceeds native width: {label}"
  let equations ← readList (← readCount 8192) (readExpr 256)
  unless equations == emitted.equations do throw s!"native circuit constraint trees differ: {label}"
  let lookups ← readList (← readCount 4096) do
    return ExprLookup.mk (← readExpr 256) (← readList (← readCount) (readExpr 256))
  unless lookups == emitted.lookups do throw s!"native circuit lookup trees differ: {label}"
  let inactiveValues := zeroValues circuit.layout.width
  let some inactive := emitted.eval inactiveValues
    | throw s!"inactive circuit row has an undefined expression: {label}"
  unless inactive.equations.all (· == 0) do throw s!"inactive circuit equation is nonzero: {label}"
  let some compiled := compileCircuit (circuitWidths circuit) program circuit
    | throw s!"base compilation rejected native circuit expressions: {label}"
  let count ← readCount
  unless count == 4 do throw "incomplete native circuit assignments"
  for seed in [:count] do
    let row := (← readList (← readCount 8192) readField).toArray
    unless row.size == emitted.width do throw "native circuit assignment has wrong width"
    let values := assignment row
    let expectedEquations ← readList equations.length readField
    let some evaluated := emitted.eval values | throw s!"undefined circuit expression: {label}, assignment {seed}"
    unless evaluated.equations == expectedEquations do throw s!"native circuit values differ: {label}, assignment {seed}"
    let some valued := circuit.emitRow (fun index => row[index]?.getD 0) program
      | throw s!"valued circuit rejected symbolic inputs: {label}"
    unless sameEmission evaluated valued do throw s!"symbolic/valued circuit differs: {label}, assignment {seed}"
    let some buffer := compiled.base.graph.sweep goldilocksOps values
      | throw s!"compiled circuit sweep is undefined: {label}"
    let some graphLookups := compiled.base.graph.lookups.mapM (readLookup buffer)
      | throw s!"compiled circuit lookup roots are undefined: {label}"
    unless graphLookups == List.ofFn (fun slot : Fin valued.lookupCount => valued.lookup slot.val) do
      throw s!"compiled circuit lookup meanings differ: {label}, assignment {seed}"
    unless compiled.base.graph.zeros.all (fun root => buffer[root]? == some 0) == valued.equations.all (· == 0) do
      throw s!"compiled circuit satisfaction differs: {label}, assignment {seed}"
    for (lookup, slot) in lookups.zipIdx do
      let weight ← readField
      let message ← readList lookup.args.length readField
      unless lookup.eval goldilocksOps values == some (weight, message) do
        throw s!"native circuit lookup values differ: {label}, slot {slot}, assignment {seed}"
      unless valued.lookup slot == (weight, message) do throw s!"symbolic/valued circuit lookup differs: {label}, slot {slot}"
  return count

private def readCorpus : Reader Unit := do
  let header := "Aiur circuit expressions v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "circuit snapshot version differs"
  unless (← readCount) == 12 do throw "incomplete native circuit programs"
  let mut reports := 0
  let mut assignments := 0
  for seed in [:12] do
    let functions := (← readList (← readCount) do
      return Bytecode.Function.mk (← readBlock 64) (← readLayout) (← readBool) (← readBool)).toArray
    let circuits := (← readList (← readCount) do
      return Bytecode.Circuit.mk "native" (← readIndices) (← readLayout)).toArray
    unless functions.size == 4 && circuits.size == 8 do throw "incomplete native circuit shapes"
    for (function, index) in functions.toList.zipIdx do
      let layout := ((Concrete.Bytecode.blockLayout function.body).run
        (.new function.layout.inputSize)).2.functionLayout
      unless function.layout == { layout with lookups := layout.lookups + 1 } do
        throw s!"native function layout differs from compiler: program {seed}, function {index}"
    let program : Bytecode.Toplevel := ⟨functions, #[], circuits⟩
    for (circuit, index) in circuits.toList.zipIdx do
      assignments := assignments + (← readCircuit program circuit s!"program {seed}, circuit {index}")
      reports := reports + 1
  unless reports == 96 && assignments == 384 do throw "incomplete native circuit coverage"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "circuit snapshot has trailing bytes"

def run (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok _ => IO.println "circuit expressions: 96 native circuit bounds, 48 compiler function layouts, 384 assignments and 96 inactive zero rows match"

end AiurTests.CircuitExpressions

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.CircuitExpressions.run path
  | _ => throw (IO.userError "expected native circuit expression snapshot")
