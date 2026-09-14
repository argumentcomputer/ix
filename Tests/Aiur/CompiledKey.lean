/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.CompiledKey
import Tests.Aiur.EmissionReader

/-! Compare complete native keys and wide matrix assignments with the checked
compiler and physical row models. Structurally valid altered keys must fail
the executable circuit-binding check. -/

open Aiur Aiur.NativeAIR Aiur.NativeAIR.Compiler Aiur.NativeAIR.CircuitEmitter
open AiurTests.EmissionReader

namespace AiurTests.CompiledKeys

private def readLayout : Reader Bytecode.FunctionLayout := do
  return ⟨← readNat, ← readNat, ← readNat, ← readNat⟩

private def readColumns (width : Nat) : Reader (Array G) := do
  let columns := (← readList (← readCount 65536) readField).toArray
  unless columns.size == width do throw "native key matrix width differs"
  return columns

private def readValues (widths : GraphWidths) : Reader (Values G) := do
  let pre ← readColumns widths.preprocessed
  let preNext ← readColumns widths.preprocessed
  let main ← readColumns widths.main
  let mainNext ← readColumns widths.main
  let stage2 ← readColumns widths.stage2
  let stage2Next ← readColumns widths.stage2
  let publics ← readColumns widths.publics
  return {
    columns := fun source offset => match source, offset with
      | .preprocessed, .current => pre | .preprocessed, .next => preNext
      | .main, .current => main | .main, .next => mainNext
      | .stage2, .current => stage2 | .stage2, .next => stage2Next
    publics, isFirstRow := ← readField, isLastRow := ← readField, isTransition := ← readField }

private def readCircuit (program : Bytecode.Toplevel) (index : Nat) (artifact : KeyCodec.Circuit) : Reader Nat := do
  unless (← readCount) == 4 do throw "incomplete native key assignments"
  for seed in [:4] do
    let label := s!"circuit {index}, assignment {seed}"
    let values ← readValues artifact.widths
    let equations ← readList (← readCount 65536) readField
    let lookups ← readList (← readCount 65536) do
      return (← readField, ← readList (← readCount 65536) readField)
    let some buffer := artifact.graph.sweep goldilocksOps values | throw s!"undefined native graph: {label}"
    unless artifact.graph.zeros.all (fun root => buffer[root]? == some 0) == equations.all (· == 0) do
      throw s!"native key graph satisfaction differs: {label}"
    unless artifact.graph.lookups.mapM (readLookup buffer) == some lookups do
      throw s!"native key graph lookup values differ: {label}"
    if index < program.circuits.size then
      let source := program.circuits[index]!
      let some symbolic := compileNativeCircuit artifact.widths program source
        | throw s!"compilation at native widths rejected: {label}"
      unless symbolic.base.graph == artifact.graph do throw s!"widened graph differs: {label}"
      let some emission := source.emitNativeRow (fun column => (values.columns .main .current)[column]?.getD 0) program
        | throw s!"native key function row rejected: {label}"
      unless emission.equations == equations &&
          List.ofFn (fun slot : Fin emission.lookupCount => emission.lookup slot.val) == lookups do
        throw s!"native key function meaning differs: {label}"
    else if index < program.circuits.size + program.memorySizes.size then
      let width := program.memorySizes[index - program.circuits.size]!
      let current := CompiledKey.columns values .main .current (3 + width)
      let next := CompiledKey.columns values .main .next (3 + width)
      unless AIR.memoryColumnEquations width current next values.isTransition == equations &&
          [AIR.memoryColumnLookup width current] == lookups do
        throw s!"native key memory meaning differs: {label}"
    else if index == program.circuits.size + program.memorySizes.size then
      unless equations.isEmpty && lookups == (AIR.Byte1Kind.all.map fun kind => AIR.byte1ColumnLookup kind
          (CompiledKey.columns values .preprocessed .current 11) (CompiledKey.columns values .main .current 3)) do
        throw s!"native key byte1 meaning differs: {label}"
    else
      unless equations.isEmpty && lookups == (AIR.Byte2Kind.all.map fun kind => AIR.byte2ColumnLookup kind
          (CompiledKey.columns values .preprocessed .current 14) (CompiledKey.columns values .main .current 10)) do
        throw s!"native key byte2 meaning differs: {label}"
  return 4

private def rejectAltered (program : Bytecode.Toplevel) (original altered : KeyCodec.Key) (label : String) : Reader Unit := do
  unless altered != original do throw s!"ineffective altered-key case: {label}"
  unless KeyCodec.decodeCanonical (KeyCodec.encode altered) == some altered do
    throw s!"altered key must retain valid canonical syntax: {label}"
  if CompiledKey.check program altered then throw s!"altered native key accepted: {label}"

private def alterations (program : Bytecode.Toplevel) (key : KeyCodec.Key) : Reader Nat := do
  let some first := key.circuits.head? | throw "missing native function circuit"
  let some lookup := first.graph.lookups.head? | throw "missing native function lookup"
  let changedCircuits : List (String × KeyCodec.Circuit) := [
    ("unused node", { first with graph.nodes := first.graph.nodes ++ [.konst 17] }),
    ("missing constraint", { first with graph.zeros := first.graph.zeros.drop 1 }),
    ("extra constraint", { first with graph := { first.graph with
      nodes := first.graph.nodes ++ [.konst 0], zeros := first.graph.zeros ++ [first.graph.nodes.length] } }),
    ("missing lookup", { first with graph.lookups := first.graph.lookups.drop 1 }),
    ("zeroed provider", { first with graph := { first.graph with
      nodes := first.graph.nodes ++ [.konst 0],
      lookups := first.graph.lookups.set 0 { lookup with multiplicity := first.graph.nodes.length } } }),
    ("extended message", { first with graph.lookups := first.graph.lookups.set 0 { lookup with args := lookup.args ++ [lookup.multiplicity] } }),
    ("main width", { first with mainWidth := first.mainWidth + 1 }),
    ("preprocessed width", { first with preprocessedWidth := first.preprocessedWidth + 1 }),
    ("preprocessed height", { first with preprocessedHeight := first.preprocessedHeight + 1 }),
    ("lookup grouping", { first with lookupGroupSize := if first.lookupGroupSize == 1 then 2 else 1 })]
  for (label, raw) in changedCircuits do
    let some degree := raw.computedDegree | throw s!"undefined altered graph degree: {label}"
    let circuit := { raw with maxConstraintDegree := degree }
    rejectAltered program key { key with circuits := key.circuits.set 0 circuit } label
  rejectAltered program key { key with circuits := key.circuits.reverse, preprocessedIndices := key.preprocessedIndices.reverse } "reversed circuit order"
  rejectAltered program key { key with circuits := first :: key.circuits, preprocessedIndices := none :: key.preprocessedIndices } "extra circuit"
  rejectAltered program key { key with circuits := key.circuits.tail, preprocessedIndices := key.preprocessedIndices.tail } "missing circuit"
  rejectAltered program key { key with preprocessedIndices := key.preprocessedIndices.set 0 (some 0) } "preprocessed index"
  return changedCircuits.length + 4

private def rejectComponents (program : Bytecode.Toplevel) (key : KeyCodec.Key) : Reader Nat := do
  if program.callComponents.isEmpty then return 0
  let components := program.callComponents
  let invalid := [
    components.pop,
    components.set! 0 ⟨program.functions.size, false⟩,
    components.set! 1 ⟨1, false⟩,
    components.set! 0 ⟨3, false⟩]
  for components in invalid do
    let altered := { program with callComponents := components }
    if altered.validCallComponents then throw "component rejection fixture is valid"
    if CompiledKey.check altered key then throw "invalid component certificate accepted"
  return invalid.length

private def readCorpus : Reader (Nat × Nat × Nat) := do
  let header := "Aiur compiled keys v3\n".toUTF8
  unless (← takeBytes header.size) == header do throw "compiled-key snapshot version differs"
  unless (← readCount) == 24 do throw "incomplete native key systems"
  let mut circuitCount := 0
  let mut assignments := 0
  let mut rejections := 0
  for seed in [:24] do
    let functions := (← readList (← readCount) do
      return Bytecode.Function.mk (← readBlock 64) (← readLayout) (← readBool) (← readBool)).toArray
    let circuits := (← readList (← readCount) do
      return Bytecode.Circuit.mk "native" (← readIndices) (← readLayout)).toArray
    let memorySizes ← readIndices
    let components := (← readList (← readCount) do
      return Bytecode.CallComponent.mk (← readNat) (← readBool)).toArray
    let program : Bytecode.Toplevel := ⟨functions, memorySizes, circuits, components⟩
    unless components.size == (if seed < 12 then 0 else 4) do
      throw "incomplete native component policies"
    unless components.isEmpty || program.validCallComponents do
      throw "invalid native component fixture"
    let bytes ← takeBytes (← readCount 1048576)
    let some key := KeyCodec.decodeCanonical bytes | throw s!"native key rejected: system {seed}"
    unless key.parameters.logBlowup == 1 + seed % 3 do throw "incomplete native lookup-group budgets"
    unless CompiledKey.check program key do throw s!"native key differs from compiled program: system {seed}"
    unless functions.size == 4 && circuits.size == 8 && memorySizes == #[0, 1, 2, 4, 8] && key.circuits.length == 15 do
      throw "incomplete native key circuit families"
    for (artifact, index) in key.circuits.zipIdx do
      assignments := assignments + (← readCircuit program index artifact)
      circuitCount := circuitCount + 1
    rejections := rejections + (← alterations program key)
    rejections := rejections + (← rejectComponents program key)
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "compiled-key snapshot has trailing bytes"
  return (circuitCount, assignments, rejections)

def run (path : System.FilePath) : IO Unit := do
  match readCorpus.run (← IO.FS.readBinFile path, 0) with
  | .error error => throw (IO.userError error)
  | .ok ((circuits, assignments, rejections), _) =>
    unless circuits == 360 && assignments == 1440 && rejections == 384 do
      throw (IO.userError "incomplete native key coverage")
    IO.println s!"compiled keys: 24 native systems (12 component layouts), {circuits} circuits, {assignments} assignments match; 336 valid altered keys and 48 invalid component certificates rejected"

end AiurTests.CompiledKeys

def main (args : List String) : IO Unit := do
  match args with
  | [path] => AiurTests.CompiledKeys.run path
  | _ => throw (IO.userError "expected native compiled-key snapshot")
