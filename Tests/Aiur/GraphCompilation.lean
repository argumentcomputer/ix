/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.GraphCompilation

open Aiur Aiur.NativeAIR Aiur.NativeAIR.Compiler

namespace AiurTests.GraphCompilation

private abbrev Reader := StateT (ByteArray × Nat) (Except String)

private def takeBytes (count : Nat) : Reader ByteArray := do
  let (bytes, cursor) ← get
  if cursor + count > bytes.size then throw s!"compiler snapshot truncated at {cursor}"
  set (bytes, cursor + count)
  return bytes.extract cursor (cursor + count)

private def readNat (count : Nat := 8) : Reader Nat := do
  let bytes ← takeBytes count
  let mut value := 0
  for index in [:count] do value := value + bytes[index]!.toNat * 256^index
  return value

private def readField : Reader G := do
  let value ← readNat
  unless value < gSize.toNat do throw "noncanonical compiler field value"
  return G.ofNat value

private def readList (count : Nat) (reader : Reader α) : Reader (List α) :=
  (List.range count).mapM fun _ => reader

private def readValues : Reader (Array G) := do
  return (← readList (← readNat) readField).toArray

private def readColumn : Reader ColRef := do
  let source ← match ← readNat 1 with
    | 0 => pure Source.preprocessed | 1 => pure Source.main | 2 => pure Source.stage2
    | _ => throw "invalid compiler column source"
  let offset ← match ← readNat 1 with
    | 0 => pure RowOffset.current | 1 => pure RowOffset.next
    | _ => throw "invalid compiler row offset"
  return ⟨source, offset, ← readNat⟩

private def readExpr : Nat → Reader Expr
  | 0 => throw "compiler expression exceeds snapshot depth bound"
  | fuel + 1 => do
    match ← readNat 1 with
    | 0 => return .konst (← readField)
    | 1 => return .var (← readColumn)
    | 2 => return .publicInput (← readNat)
    | 3 => return .isFirstRow
    | 4 => return .isLastRow
    | 5 => return .isTransition
    | 6 => return .add (← readExpr fuel) (← readExpr fuel)
    | 7 => return .sub (← readExpr fuel) (← readExpr fuel)
    | 8 => return .mul (← readExpr fuel) (← readExpr fuel)
    | 9 => return .neg (← readExpr fuel)
    | _ => throw "invalid compiler expression tag"

private def readNode : Reader Node := do
  match ← readNat 1 with
  | 0 => return .konst (← readField)
  | 1 => return .var (← readColumn)
  | 2 => return .publicInput (← readNat)
  | 3 => return .isFirstRow
  | 4 => return .isLastRow
  | 5 => return .isTransition
  | 6 => return .add (← readNat) (← readNat)
  | 7 => return .sub (← readNat) (← readNat)
  | 8 => return .mul (← readNat) (← readNat)
  | 9 => return .neg (← readNat)
  | _ => throw "invalid compiler node tag"

private def readSpec : Reader (GraphWidths × List ExprLookup × List Expr) := do
  let widths : GraphWidths := ⟨← readNat, ← readNat, ← readNat, ← readNat⟩
  let lookups ← readList (← readNat) do
    let multiplicity ← readExpr 64
    let args ← readList (← readNat) (readExpr 64)
    return ExprLookup.mk multiplicity args
  let constraints ← readList (← readNat) (readExpr 64)
  return (widths, lookups, constraints)

private def nodeDegree (degrees : Array Nat) : Node → Option Nat
  | .konst _ | .publicInput _ | .isTransition => some 0
  | .var _ | .isFirstRow | .isLastRow => some 1
  | .add a b | .sub a b => return max (← degrees[a]?) (← degrees[b]?)
  | .mul a b => return (← degrees[a]?) + (← degrees[b]?)
  | .neg a => degrees[a]?

private def readGraph : Reader BaseCompilation := do
  let nodes ← readList (← readNat) readNode
  let mut degrees : Array Nat := #[]
  for node in nodes do
    let native ← readNat
    let some expected := nodeDegree degrees node | throw "native compiler emitted an invalid child read"
    unless native == expected && native < 2^32 do throw "compiled node degree differs"
    degrees := degrees.push expected
  let zeros ← readList (← readNat) readNat
  let lookups ← readList (← readNat) do
    let multiplicity ← readNat
    let args ← readList (← readNat) readNat
    return Lookup.mk multiplicity args
  let lookupEnd ← readNat
  let maximum ← readNat
  let some zeroDegrees := zeros.mapM (fun index => degrees[index]?) | throw "invalid native zero root"
  unless maximum == zeroDegrees.foldl max 0 do throw "compiled maximum degree differs"
  return ⟨⟨nodes, zeros, lookups⟩, lookupEnd⟩

private def readAssignment (widths : GraphWidths) (lookups : List ExprLookup) (constraints : List Expr)
    (compiled : BaseCompilation) : Reader Nat := do
  let preCurrent ← readValues
  let preNext ← readValues
  let mainCurrent ← readValues
  let mainNext ← readValues
  let stageCurrent ← readValues
  let stageNext ← readValues
  let publics ← readValues
  let indicators ← readValues
  unless preCurrent.size == widths.preprocessed && preNext.size == widths.preprocessed &&
      mainCurrent.size == widths.main && mainNext.size == widths.main &&
      stageCurrent.size == widths.stage2 && stageNext.size == widths.stage2 &&
      publics.size == widths.publics && indicators.size == 3 do throw "compiler assignment dimensions differ"
  let values : Values G := ⟨(fun source offset => match source, offset with
      | .preprocessed, .current => preCurrent | .preprocessed, .next => preNext
      | .main, .current => mainCurrent | .main, .next => mainNext
      | .stage2, .current => stageCurrent | .stage2, .next => stageNext),
    publics, indicators[0]?.getD 0, indicators[1]?.getD 0, indicators[2]?.getD 0⟩
  let native ← readValues
  unless compiled.graph.sweep goldilocksOps values == some native do throw "compiled graph sweep differs"
  let nativePrefix ← readValues
  unless sweepFrom goldilocksOps values.withoutStage2 (compiled.graph.nodes.take compiled.lookupEnd) #[] == some nativePrefix do
    throw "stored lookup-prefix sweep differs"
  unless compiled.graph.sweepLookupPrefix goldilocksOps values == some (nativePrefix.extract 0 compiled.graph.lookupPrefix) do
    throw "root-derived lookup-prefix sweep differs"
  let original ← readValues
  unless evalExprs goldilocksOps values constraints == some original.toList do throw "source constraint evaluation differs"
  let some zeroValues := readNodes native compiled.graph.zeros | throw "compiled zero root cannot be read"
  unless zeroValues.all (· == 0) == original.all (· == 0) do throw "constraint satisfaction changed during compilation"
  let nativeLookups ← readList lookups.length do
    let multiplicity ← readField
    let args ← readValues
    return (multiplicity, args.toList)
  unless lookups.mapM (ExprLookup.eval goldilocksOps values) == some nativeLookups do throw "source lookup evaluation differs"
  unless compiled.graph.lookups.mapM (readLookup native) == some nativeLookups do throw "compiled lookup evaluation differs"
  return native.size

private def readCorpus : Reader (Nat × Nat × Nat × Nat) := do
  let header := "Aiur graph compilation v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "invalid graph compiler snapshot header"
  let count ← readNat
  unless count == 1484 do throw "compiler graph case count differs"
  let mut assignments := 0
  let mut nodeValues := 0
  let mut shortened := 0
  for index in [:count] do
    let (widths, lookups, constraints) ← readSpec
    let native ← readGraph
    let some expected := compileBase widths lookups constraints | throw s!"Lean rejected native graph {index}"
    unless native == expected do throw s!"compiled graph structure differs at case {index}"
    unless checkedGraphPrefix widths native.graph == some native.graph.lookupPrefix do throw "compiled graph failed its layout guard"
    unless native.graph.lookupPrefix ≤ native.lookupEnd && native.lookupEnd ≤ native.graph.nodes.length do throw "invalid stored lookup prefix"
    if native.graph.lookupPrefix < native.lookupEnd then shortened := shortened + 1
    for _ in [:8] do
      nodeValues := nodeValues + (← readAssignment widths lookups constraints native)
      assignments := assignments + 1
  unless shortened > 0 do throw "compiler corpus does not cover folded unused lookup nodes"
  let rejected ← readNat
  unless rejected == 38 do throw "compiler rejection case count differs"
  for index in [:rejected] do
    let (widths, lookups, constraints) ← readSpec
    unless (compileBase widths lookups constraints).isNone do throw s!"Lean accepted native rejection {index}"
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "trailing compiler snapshot bytes"
  return (count, rejected, assignments, nodeValues)

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: aiur-graph-compilation-tests <native-snapshot>")
  let bytes ← IO.FS.readBinFile path
  match readCorpus.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok ((graphs, rejected, assignments, nodes), _) =>
    IO.println s!"graph compilation: {graphs} complete graphs, {rejected} rejected specifications, {assignments} assignments, {nodes} node values match native Rust"
    return 0

end AiurTests.GraphCompilation

def main := AiurTests.GraphCompilation.main
