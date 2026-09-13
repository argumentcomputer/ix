module
public import Ix.MultiStark.Verify.Key

/-! Sparse native proof-shape admission. All proof-side per-circuit arrays
use ACTIVE position, while preprocessed openings retain the full key slot map.
The admitted class uses native-builder preprocessing heights and slot order.
This module performs no transcript, accumulator, AIR, or PCS verification. -/

public section
@[expose] section

namespace MultiStark.Verify.Shape

inductive Error where
  | key (error : KeyError)
  | activation | count | points | width | height | preprocessing
  deriving BEq, DecidableEq, Repr, Inhabited

def ceilLog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

def quotientLog (circuit : Circuit) : Nat := ceilLog2 (max 2 circuit.maxConstraintDegree - 1)

def quotientDegree (circuit : Circuit) : Nat := 2 ^ quotientLog circuit

structure CircuitValues where
  index : Nat
  circuit : Circuit
  logDegree : Nat
  stage1 : Array Ext × Array Ext
  stage2 : Array Ext × Array Ext
  preprocessed : Array Ext × Array Ext
  quotient : Array Ext
  deriving BEq, DecidableEq, Repr

def getAt {α : Type} (values : Array α) (index : Nat) : Except Error α :=
  match values[index]? with | some value => .ok value | none => .error .count

def twoRows (width : Nat) (rows : Array (Array Ext)) : Except Error (Array Ext × Array Ext) := do
  match rows.toList with
  | [current, next] =>
    ensure (current.size == width && next.size == width) .width
    return (current, next)
  | _ => throw .points

def oneRow (width : Nat) (rows : Array (Array Ext)) : Except Error (Array Ext) := do
  match rows.toList with
  | [values] =>
    ensure (values.size == width) .width
    return values
  | _ => throw .points

def preprocessedRows (circuit : Circuit) (logDegree : Nat) (prep : OpenedRound) :
    Option Nat → Except Error (Array Ext × Array Ext)
  | none => .ok (#[], #[])
  | some slot => do
    -- Active preprocessing uses the canonical table's pinned height.
    ensure (logDegree == circuit.preprocessedHeight.log2) .height
    twoRows circuit.preprocessedWidth (← getAt prep slot)

def inactivePreprocessed (prep : OpenedRound) : Option Nat → Except Error Unit
  | none => .ok ()
  | some slot => do
    ensure (← getAt prep slot).isEmpty .preprocessing

def activeValues (key : Key) (proof : Proof) (circuit : Circuit) (prepIndex : Option Nat)
    (index pos : Nat) : Except Error CircuitValues := do
  let logDegree := (← getAt proof.logDegrees pos).toNat
  ensure (logDegree + quotientLog circuit + key.params.logBlowup ≤ 32) .height
  let stage1 ← twoRows circuit.mainWidth (← getAt proof.stage1 pos)
  let stage2 ← twoRows circuit.stage2Width (← getAt proof.stage2 pos)
  let preprocessed ← preprocessedRows circuit logDegree (proof.preprocessed.getD #[]) prepIndex
  let quotient ← oneRow (2 * quotientDegree circuit) (← getAt proof.quotient pos)
  return { index, circuit, logDegree, stage1, stage2, preprocessed, quotient }

def checkCircuits (key : Key) (proof : Proof) : List Circuit → Nat → Nat → Except Error (List CircuitValues)
  | [], _, _ => .ok []
  | circuit :: circuits, index, pos => do
    let active ← getAt proof.active index
    let prepIndex ← getAt key.preprocessedIndices index
    if active then
      let value ← activeValues key proof circuit prepIndex index pos
      let rest ← checkCircuits key proof circuits (index + 1) (pos + 1)
      return value :: rest
    else
      inactivePreprocessed (proof.preprocessed.getD #[]) prepIndex
      checkCircuits key proof circuits (index + 1) pos

def check (key : Key) (proof : Proof) : Except Error (Array CircuitValues) := do
  (validateKey key).mapError Error.key
  ensure (proof.active.size == key.circuits.size && proof.active.any id) .activation
  let activeCount := (proof.active.filter id).size
  ensure (proof.logDegrees.size == activeCount && proof.accumulators.size == activeCount &&
      proof.stage1.size == activeCount && proof.stage2.size == activeCount &&
      proof.quotient.size == activeCount) .count
  let prepCount := (key.preprocessedIndices.filter Option.isSome).size
  ensure ((proof.preprocessed.getD #[]).size == prepCount) .preprocessing
  return (← checkCircuits key proof key.circuits.toList 0 0).toArray

end MultiStark.Verify.Shape
