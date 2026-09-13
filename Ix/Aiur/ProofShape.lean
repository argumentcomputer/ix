/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.ProofCodec
import Ix.Aiur.Proofs.ByteColumns

/-! Checked extraction of the native verifier's per-active-circuit opening
records. This mirrors `System::verify_shape` using checked indexed reads.
The Aiur guards additionally bind fixed trace heights and the lookup budget.
Opened values are claims about polynomials; shape checks alone do not prove
that they arise from a satisfying execution trace.
-/

namespace Aiur.NativeAIR.ProofShape

open ProofCodec (Extension Data)

structure Pair where
  current : List Extension
  next : List Extension
  deriving DecidableEq, Repr

def pair : List (List Extension) → Option Pair
  | [current, next] => some ⟨current, next⟩
  | _ => none

def single : List α → Option α
  | [value] => some value
  | _ => none

def activeIndices (proof : Data) : List Nat :=
  proof.active.zipIdx.filterMap fun (active, index) => if active then some index else none

def quotientDegree (circuit : KeyCodec.Circuit) : Nat :=
  (max circuit.maxConstraintDegree 2 - 1).nextPowerOfTwo

structure Row where
  circuitIndex : Nat
  circuit : KeyCodec.Circuit
  logDegree : UInt8
  stage1 : Pair
  stage2 : Pair
  preprocessed : Option Pair
  quotient : List Extension
  accumulator : Extension
  deriving DecidableEq, Repr

def readPreprocessed (proof : Data) : Option Nat → Option (Option Pair)
  | none => some none
  | some slot => (proof.preprocessed >>= fun opened => opened[slot]? >>= pair).map some

def readRow (key : KeyCodec.Key) (proof : Data) (index position : Nat) : Option Row := do
  let circuit ← key.circuits[index]?
  let preprocessedIndex ← key.preprocessedIndices[index]?
  let degree ← proof.logDegrees[position]?
  let stage1 ← pair (← proof.stage1[position]?)
  let stage2 ← pair (← proof.stage2[position]?)
  let quotient ← single (← proof.quotient[position]?)
  let accumulator ← proof.accumulators[position]?
  let preprocessed ← readPreprocessed proof preprocessedIndex
  return ⟨index, circuit, degree, stage1, stage2, preprocessed, quotient, accumulator⟩

def Pair.hasWidth (values : Pair) (width : Nat) : Bool :=
  values.current.length == width && values.next.length == width

def Row.fits (parameters : KeyCodec.Parameters) (row : Row) : Bool :=
  row.stage1.hasWidth row.circuit.mainWidth && row.stage2.hasWidth row.circuit.widths.stage2 &&
  (match row.preprocessed with | none => true | some values => values.hasWidth row.circuit.preprocessedWidth) &&
  row.quotient.length == quotientDegree row.circuit * 2 &&
  row.logDegree.toNat + (quotientDegree row.circuit).log2 ≤ 32 - parameters.logBlowup

def header (key : KeyCodec.Key) (proof : Data) : Bool :=
  let active := (activeIndices proof).length
  let preprocessed := (key.preprocessedIndices.filter Option.isSome).length
  !key.circuits.isEmpty && proof.active.length == key.circuits.length && active > 0 &&
  key.preprocessedIndices.length == key.circuits.length &&
  proof.logDegrees.length == active &&
  key.preprocessedCommitment.isNone == (preprocessed == 0) &&
  (proof.preprocessed.getD []).length == preprocessed &&
  proof.stage1.length == active && proof.stage2.length == active &&
  proof.quotient.length == active && proof.accumulators.length == active

def inactivePreprocessed (key : KeyCodec.Key) (proof : Data) : Bool :=
  (key.preprocessedIndices.zip proof.active).all fun (slot, active) =>
    match slot, active with
    | some index, false => (proof.preprocessed.getD [])[index]? == some []
    | _, _ => true

def rows (key : KeyCodec.Key) (proof : Data) : Option (List Row) :=
  (activeIndices proof).zipIdx.mapM fun (index, position) => readRow key proof index position

def check (key : KeyCodec.Key) (proof : Data) : Option (List Row) := do
  if header key proof && inactivePreprocessed key proof then
    let result ← rows key proof
    if result.all (Row.fits key.parameters) then some result else none
  else none

def fixedHeights (key : KeyCodec.Key) (proof : Data) : Bool :=
  fixedTraceHeights (key.circuits.map (·.preprocessedHeight)) proof.active
    (proof.logDegrees.map UInt8.toNat)

def queryBound (key : KeyCodec.Key) (proof : Data) : Option Nat :=
  lookupQueryBound (key.circuits.map (·.graph.lookups.length)) proof.active
    (proof.logDegrees.map UInt8.toNat)

end Aiur.NativeAIR.ProofShape
