/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ExpressionGraph

open Aiur Aiur.NativeAIR

namespace AiurTests.ExpressionGraph

private def appendNat (out : ByteArray) (value : Nat) : ByteArray := Id.run do
  let mut out := out
  for index in [:8] do out := out.push ((value >>> (8 * index)) % 256).toUInt8
  return out

private def nodeChoices : List Node := Id.run do
  let indices := [0, 1, 3, 7, 8, 65535, 2^32 - 1]
  let mut choices : Array Node := #[.konst 0, .konst 1, .konst (0 - 1), .konst 65536,
    .isFirstRow, .isLastRow, .isTransition]
  for source in [Source.preprocessed, .main, .stage2] do
    for offset in [RowOffset.current, .next] do
      for index in indices do choices := choices.push (.var ⟨source, offset, index⟩)
  for index in indices do choices := choices.push (.publicInput index)
  for left in indices do
    for right in indices do
      choices := choices ++ #[.add left right, .sub left right, .mul left right]
  for index in indices do choices := choices.push (.neg index)
  return choices.toList

private def appendShapes (out : ByteArray) (nodes : List Node) : ByteArray := Id.run do
  let mut out := out
  let count := nodes.length
  for width in [0, 1, 4, 8] do
    let widths : GraphWidths := ⟨width, width + 1, width + 2, width⟩
    let contexts : List (List Nat × List Lookup) := [
      ([], []), ([0], []), ([count - 1], []), ([count], []),
      ([], [⟨0, []⟩]), ([], [⟨count - 1, [0]⟩]), ([], [⟨0, [count]⟩])]
    for (zeros, lookups) in contexts do
      out := match checkedGraphPrefix widths ⟨nodes, zeros, lookups⟩ with
        | none => out.push 0
        | some lookupEnd => appendNat (out.push 1) lookupEnd
  return out

private def expectedShapes : ByteArray × Nat := Id.run do
  let mut out := appendShapes "Aiur graph shapes v1\n".toUTF8 []
  let mut checked := 28
  for count in [1, 2, 4, 8] do
    for index in [:count] do
      for node in nodeChoices do
        out := appendShapes out ((List.replicate count (.konst 0)).set index node)
        checked := checked + 28
  return (out, checked)

private abbrev Reader := StateT (ByteArray × Nat) (Except String)

private def takeBytes (count : Nat) : Reader ByteArray := do
  let (bytes, cursor) ← get
  if cursor + count > bytes.size then throw s!"graph snapshot truncated at {cursor}"
  set (bytes, cursor + count)
  return bytes.extract cursor (cursor + count)

private def readNat (count : Nat) : Reader Nat := do
  let bytes ← takeBytes count
  let mut value := 0
  for index in [:count] do value := value + bytes[index]!.toNat * 256^index
  return value

private def readList (count : Nat) (read : Reader α) : Reader (List α) :=
  (List.range count).mapM fun _ => read

private def readValues : Reader (Array G) := do
  let count ← readNat 8
  return (← readList count (return G.ofNat (← readNat 8))).toArray

private def readNode : Reader Node := do
  match ← readNat 1 with
  | 0 => return .konst (G.ofNat (← readNat 2))
  | 1 => return .konst (G.ofNat (← readNat 8))
  | 2 => return .publicInput (← readNat 1)
  | 3 => return .isFirstRow
  | 4 => return .isLastRow
  | 5 => return .isTransition
  | 6 => return .add (← readNat 2) (← readNat 2)
  | 7 => return .sub (← readNat 2) (← readNat 2)
  | 8 => return .mul (← readNat 2) (← readNat 2)
  | 9 => return .neg (← readNat 2)
  | tag =>
    if tag < 10 || tag > 15 then throw s!"invalid graph node tag {tag}"
    let source := match (tag - 10) / 2 with | 0 => Source.preprocessed | 1 => .main | _ => .stage2
    let offset := if (tag - 10) % 2 == 0 then RowOffset.current else .next
    return .var ⟨source, offset, ← readNat 2⟩

private def readCircuit : Reader (GraphWidths × Graph) := do
  let main ← readNat 2
  let preprocessed ← readNat 2
  let _ ← readNat 4
  let _ ← readNat 2
  let groupSize ← readNat 1
  unless 1 ≤ groupSize && groupSize ≤ 8 do throw "invalid graph lookup group size"
  let nodes ← readList (← readNat 2) readNode
  let zeros ← readList (← readNat 2) (readNat 2)
  let lookups ← readList (← readNat 2) do
    let multiplicity ← readNat 2
    let args ← readList (← readNat 2) (readNat 2)
    return Lookup.mk multiplicity args
  let stage2 := max 1 ((lookups.length + groupSize - 1) / groupSize) * 2
  return (⟨preprocessed, main, stage2, 8⟩, ⟨nodes, zeros, lookups⟩)

private def readAssignment (widths : GraphWidths) (graph : Graph) (trees : Array Expr) : Reader Nat := do
  let preCurrent ← readValues
  let preNext ← readValues
  let mainCurrent ← readValues
  let mainNext ← readValues
  let stageCurrent ← readValues
  let stageNext ← readValues
  let publics ← readValues
  let first := G.ofNat (← readNat 8)
  let last := G.ofNat (← readNat 8)
  let transition := G.ofNat (← readNat 8)
  let values : Values G := ⟨(fun source offset => match source, offset with
      | .preprocessed, .current => preCurrent | .preprocessed, .next => preNext
      | .main, .current => mainCurrent | .main, .next => mainNext
      | .stage2, .current => stageCurrent | .stage2, .next => stageNext),
    publics, first, last, transition⟩
  for source in [Source.preprocessed, .main, .stage2] do
    for offset in [RowOffset.current, .next] do
      unless (values.columns source offset).size == widths.width source do throw "native graph column width mismatch"
  unless publics.size == widths.publics do throw "native graph public width mismatch"
  let full ← readValues
  let prefixValues ← readValues
  let zeros ← readValues
  let lookups ← readList (← readNat 8) do
    let multiplicity := G.ofNat (← readNat 8)
    let args ← readValues
    return (multiplicity, args.toList)
  unless graph.sweep goldilocksOps values == some full do throw "native graph full sweep differs"
  unless graph.sweepLookupPrefix goldilocksOps values == some prefixValues do throw "native graph lookup sweep differs"
  unless readNodes full graph.zeros == some zeros.toList do throw "native graph constraints differ"
  unless graph.lookups.mapM (readLookup prefixValues) == some lookups do throw "native graph lookups differ"
  unless trees.size == full.size do throw "unfolded graph size differs"
  for index in [:trees.size] do
    let some expr := trees[index]? | throw "unfolded graph index missing"
    unless expr.eval goldilocksOps values == full[index]? do throw s!"unfolded graph value differs at {index}"
  return full.size

private def readGraphs : Reader (Nat × Nat) := do
  let header := "Aiur expression graphs v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "native graph snapshot version differs"
  let mut checked := 0
  let mut nodes := 0
  let count ← readNat 8
  unless count == 10 do throw "incomplete native graph circuit corpus"
  for _ in [:count] do
    let bytes ← takeBytes (← readNat 8)
    let ((widths, graph), (_, consumed)) ← match readCircuit.run (bytes, 0) with
      | .error error => throw error
      | .ok result => pure result
    unless consumed == bytes.size do throw "native graph circuit has trailing bytes"
    let some lookupEnd := checkedGraphPrefix widths graph | throw "actual native graph layout rejected"
    unless lookupEnd ≤ graph.nodes.length do throw "native graph lookup prefix out of range"
    let some trees := graph.unfold | throw "actual native graph unfolding failed"
    let assignments ← readNat 8
    unless assignments == 24 do throw "incomplete native graph assignment corpus"
    for _ in [:assignments] do
      nodes := nodes + (← readAssignment widths graph trees)
      checked := checked + 1
  let (bytes, cursor) ← get
  unless cursor == bytes.size do throw "native graph snapshot has trailing bytes"
  return (checked, nodes)

def run (shapePath graphPath : System.FilePath) : IO Unit := do
  let shapeBytes ← IO.FS.readBinFile shapePath
  let (expected, checked) := expectedShapes
  unless checked == 88228 && nodeChoices.length == 210 do throw (IO.userError "incomplete graph-shape corpus")
  unless shapeBytes == expected do throw (IO.userError "native/Lean graph-shape checks differ")
  IO.println s!"graph shapes: {checked} native/Lean layouts match"
  let graphBytes ← IO.FS.readBinFile graphPath
  match readGraphs.run (graphBytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok ((assignments, nodes), _) =>
    IO.println s!"expression graphs: {assignments} native/Lean assignments, {nodes} node values match"

end AiurTests.ExpressionGraph

def main (args : List String) : IO Unit := do
  match args with
  | [shapePath, graphPath] => AiurTests.ExpressionGraph.run shapePath graphPath
  | _ => throw (IO.userError "expected native graph-shape and expression-graph snapshots")
