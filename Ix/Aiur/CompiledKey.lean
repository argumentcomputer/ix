/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.NativeCompiledRows
import Ix.Aiur.Proofs.CircuitCompletion
import Ix.Aiur.Proofs.ByteColumns
import Ix.Aiur.LookupGroups

/-! Reconstruct the complete native circuit list from the selected bytecode.
The comparison includes ordered graph nodes, constraints, lookups, dimensions,
degrees, grouping and preprocessed indices. Commitment contents and proof
verification are separate from this executable graph-binding check. -/

namespace Aiur.NativeAIR.CompiledKey
open Compiler CircuitEmitter

def main (index : Nat) : Expr := .var ⟨.main, .current, index⟩
def next (index : Nat) : Expr := .var ⟨.main, .next, index⟩
def preprocessed (index : Nat) : Expr := .var ⟨.preprocessed, .current, index⟩

def memoryEquations : List Expr :=
  let selector := main 1
  let transition := (next 1).frontMul .isTransition
  [selector.frontMul (selector.frontSub (.konst 1)),
    (main 0).frontMul ((Expr.konst 1).frontSub selector),
    transition.frontMul (selector.frontSub (.konst 1)),
    transition.frontMul (((main 2).frontAdd (.konst 1)).frontSub (next 2))]

def memoryLookup (width : Nat) : ExprLookup :=
  ⟨(main 0).frontNeg,
    [Expr.konst 1, .konst (G.ofNat width), main 2].map ((main 1).frontMul) ++
      (List.ofFn fun i : Fin width => (main 1).frontMul (main (3 + i.val)))⟩

def byte1Lookup (kind : AIR.Byte1Kind) : ExprLookup :=
  ⟨(main kind.column.val).frontNeg, match kind with
    | .bits => [.konst 2, preprocessed 0] ++ List.ofFn (fun i : Fin 8 => preprocessed (1 + i.val))
    | .shiftLeft => [.konst 3, preprocessed 0, preprocessed 9]
    | .shiftRight => [.konst 4, preprocessed 0, preprocessed 10]⟩

def byte2Lookup (kind : AIR.Byte2Kind) : ExprLookup :=
  ⟨(main kind.column.val).frontNeg, [.konst kind.channel, preprocessed 0, preprocessed 1] ++ match kind with
    | .xor => [preprocessed 2]
    | .add => [preprocessed 3]
    | .sub => [preprocessed 4]
    | .and => [preprocessed 5]
    | .or => [preprocessed 6]
    | .lessThan => [preprocessed 7]
    | .range => []
    | .mul => [preprocessed 8, preprocessed 9]
    | .split7 => [preprocessed 10, preprocessed 11]
    | .split4 => [preprocessed 12, preprocessed 13]⟩

def circuit (logBlowup mainWidth preprocessedWidth preprocessedHeight groupSize : Nat)
    (base : BaseCompilation) : Option KeyCodec.Circuit := do
  let raw : KeyCodec.Circuit := ⟨mainWidth, preprocessedWidth, preprocessedHeight, 0, groupSize, base.graph⟩
  let degree ← raw.computedDegree
  let result := LookupGroups.retune { raw with maxConstraintDegree := degree } (2^logBlowup)
  if result.valid then some result else none

def functionCircuit (logBlowup : Nat) (program : Bytecode.Toplevel) (source : Bytecode.Circuit) : Option KeyCodec.Circuit := do
  let compiled ← compileNativeCircuit (circuitWidths source) program source
  let groupSize := if compiled.emission.branchless && 2 ≤ compiled.emission.lookups.length then 2 else 1
  circuit logBlowup source.layout.width 0 0 groupSize compiled.base

def memoryCircuit (logBlowup width : Nat) : Option KeyCodec.Circuit := do
  let base ← compileBase ⟨0, 3 + width, 0, 0⟩ [memoryLookup width] memoryEquations
  circuit logBlowup (3 + width) 0 0 1 base

def byte1Circuit (logBlowup : Nat) : Option KeyCodec.Circuit := do
  let base ← compileBase ⟨11, 3, 0, 0⟩ (AIR.Byte1Kind.all.map byte1Lookup) []
  circuit logBlowup 3 11 256 2 base

def byte2Circuit (logBlowup : Nat) : Option KeyCodec.Circuit := do
  let base ← compileBase ⟨14, 10, 0, 0⟩ (AIR.Byte2Kind.all.map byte2Lookup) []
  circuit logBlowup 10 14 65536 2 base

def circuits (logBlowup : Nat) (program : Bytecode.Toplevel) : Option (List KeyCodec.Circuit) := do
  let functions ← program.circuits.toList.mapM (functionCircuit logBlowup program)
  let memories ← program.memorySizes.toList.mapM (memoryCircuit logBlowup)
  let byte1 ← byte1Circuit logBlowup
  let byte2 ← byte2Circuit logBlowup
  return functions ++ memories ++ [byte1, byte2]

def preprocessedIndices (program : Bytecode.Toplevel) : List (Option Nat) :=
  List.replicate (program.circuits.size + program.memorySizes.size) none ++ [some 0, some 1]

def check (program : Bytecode.Toplevel) (key : KeyCodec.Key) : Bool :=
  (program.callComponents.isEmpty || program.validCallComponents) &&
    (circuits key.parameters.logBlowup program == some key.circuits &&
      key.preprocessedIndices == preprocessedIndices program)

end Aiur.NativeAIR.CompiledKey
