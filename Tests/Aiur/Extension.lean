/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.ExtensionField
import Tests.Aiur.EmissionReader

/-! Comparison with the pinned native field implementation and its actual
compiled graphs. Coordinate inputs, all operations and every graph node are
checked independently, including full-width exponents and zero inverses. -/

open Aiur Aiur.NativeAIR AiurTests.EmissionReader
open ProofCodec (Extension)

namespace AiurTests.ExtensionArithmetic

private def readExtension : Reader Extension := do return ⟨← readField, ← readField⟩
private def readExtensions : Reader (List Extension) := do readList (← readCount 100000) readExtension

private def readArithmetic : Reader Unit := do
  let header := "Aiur extension arithmetic v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "extension arithmetic snapshot version differs"
  let bases ← readCount
  unless bases == 16 do throw "incomplete base inverse cases"
  for _ in [:bases] do
    let value ← readField
    unless value.inverse == (← readField) do throw "native base inverse differs"
  let values ← readExtensions
  unless values.length == 384 do throw "incomplete extension coordinates"
  let powers ← readList (← readCount) (readNat 16)
  let p := gSize.toNat
  let expected := [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64,
    p - 2, p - 1, p, 2^64 - 1, 2^64, p * p - 2, 2^127 + 1, 2^128 - 1]
  unless powers == expected do throw "incomplete extension exponents"
  let mut inverses := 0
  for value in values do
    unless -value == (← readExtension) do throw "native extension negation differs"
    unless value * value == (← readExtension) do throw "native extension square differs"
    unless value.conjugate == (← readExtension) do throw "native extension conjugate differs"
    unless value.norm == (← readField) do throw "native extension norm differs"
    let inverse ← readOption readExtension
    unless value.tryInverse == inverse do throw "native extension inverse differs"
    if let some inverse := inverse then
      unless value * inverse == 1 do throw "extension inverse does not cancel"
      inverses := inverses + 1
    for exponent in powers do
      unless value.power exponent == (← readExtension) do throw s!"native extension power differs at {exponent}"
  unless inverses == 383 do throw "incomplete extension inverse cases"
  for left in values do
    for right in values do
      unless left + right == (← readExtension) do throw "native extension addition differs"
      unless left - right == (← readExtension) do throw "native extension subtraction differs"
      unless left * right == (← readExtension) do throw "native extension multiplication differs"

private def readAssignment (circuit : KeyCodec.Circuit) (trees : Array Expr) : Reader Nat := do
  let preCurrent := (← readExtensions).toArray
  let preNext := (← readExtensions).toArray
  let mainCurrent := (← readExtensions).toArray
  let mainNext := (← readExtensions).toArray
  let stageCurrent := (← readExtensions).toArray
  let stageNext := (← readExtensions).toArray
  let publics := (← readExtensions).toArray
  let first ← readExtension
  let last ← readExtension
  let transition ← readExtension
  let values : Values Extension := ⟨(fun source offset => match source, offset with
      | .preprocessed, .current => preCurrent | .preprocessed, .next => preNext
      | .main, .current => mainCurrent | .main, .next => mainNext
      | .stage2, .current => stageCurrent | .stage2, .next => stageNext),
    publics, first, last, transition⟩
  for source in [Source.preprocessed, .main, .stage2] do
    for offset in [RowOffset.current, .next] do
      unless (values.columns source offset).size == circuit.widths.width source do throw "extension graph width differs"
  unless publics.size == circuit.widths.publics do throw "extension graph public width differs"
  let buffer := (← readExtensions).toArray
  let constraints ← readExtensions
  let lookups ← readList (← readCount) do return (← readExtension, ← readExtensions)
  unless circuit.graph.sweep Extension.evalOps values == some buffer do throw "native extension sweep differs"
  unless readNodes buffer circuit.graph.zeros == some constraints do throw "native extension constraint roots differ"
  unless circuit.graph.lookups.mapM (readLookup buffer) == some lookups do throw "native extension lookup roots differ"
  unless trees.size == buffer.size do throw "extension graph unfolding length differs"
  for index in [:trees.size] do
    let some expr := trees[index]? | throw "extension graph expression missing"
    unless expr.eval Extension.evalOps values == buffer[index]? do throw "extension expression evaluation differs"
  return buffer.size

private def readGraphs : Reader Unit := do
  let header := "Aiur extension graphs v1\n".toUTF8
  unless (← takeBytes header.size) == header do throw "extension graph snapshot version differs"
  let circuits ← readCount
  unless circuits == 10 do throw "incomplete extension graphs"
  let mut nodes := 0
  for _ in [:circuits] do
    let bytes ← takeBytes (← readCount 1000000)
    let some (circuit, []) := KeyCodec.readCircuit bytes.data.toList | throw "invalid extension graph circuit"
    let some _ := checkedGraphPrefix circuit.widths circuit.graph | throw "invalid extension graph reads"
    let some trees := circuit.graph.unfold | throw "extension graph does not unfold"
    let assignments ← readCount
    unless assignments == 24 do throw "incomplete extension graph assignments"
    for _ in [:assignments] do nodes := nodes + (← readAssignment circuit trees)
  unless nodes == 8016 do throw "incomplete extension graph nodes"

private def runReader (reader : Reader Unit) (path : System.FilePath) : IO Unit := do
  let bytes ← IO.FS.readBinFile path
  match reader.run (bytes, 0) with
  | .error error => throw (IO.userError error)
  | .ok (_, (_, cursor)) =>
    unless cursor == bytes.size do throw (IO.userError "extension snapshot has trailing bytes")

def run (arithmetic graphs : System.FilePath) : IO Unit := do
  runReader readArithmetic arithmetic
  IO.println "extension arithmetic: 16 base inverses, 384 values, 7680 powers and 147456 ordered pairs match native"
  runReader readGraphs graphs
  IO.println "extension graphs: 240 assignments and 8016 node values match native and expression evaluation"

end AiurTests.ExtensionArithmetic

def main (args : List String) : IO Unit := do
  match args with
  | [arithmetic, graphs] => AiurTests.ExtensionArithmetic.run arithmetic graphs
  | _ => throw (IO.userError "expected native extension arithmetic and graph snapshots")
