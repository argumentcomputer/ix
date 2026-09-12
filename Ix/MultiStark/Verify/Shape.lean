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
    unless current.size == width && next.size == width do throw .width
    return (current, next)
  | _ => throw .points

def oneRow (width : Nat) (rows : Array (Array Ext)) : Except Error (Array Ext) := do
  match rows.toList with
  | [values] =>
    unless values.size == width do throw .width
    return values
  | _ => throw .points

def check (key : Key) (proof : Proof) : Except Error (Array CircuitValues) := do
  (validateKey key).mapError Error.key
  unless proof.active.size == key.circuits.size && proof.active.any id do throw .activation
  let activeCount := (proof.active.filter id).size
  unless proof.logDegrees.size == activeCount && proof.accumulators.size == activeCount &&
      proof.stage1.size == activeCount && proof.stage2.size == activeCount &&
      proof.quotient.size == activeCount do throw .count
  let prepCount := (key.preprocessedIndices.filter Option.isSome).size
  let prep := proof.preprocessed.getD #[]
  unless prep.size == prepCount do throw .preprocessing
  let mut pos := 0
  let mut values : Array CircuitValues := #[]
  for index in [0:key.circuits.size] do
    let circuit ← getAt key.circuits index
    let active ← getAt proof.active index
    let prepIndex ← getAt key.preprocessedIndices index
    if active then
      let logDegree := (← getAt proof.logDegrees pos).toNat
      unless logDegree + quotientLog circuit + key.params.logBlowup ≤ 32 do throw .height
      let stage1 ← twoRows circuit.mainWidth (← getAt proof.stage1 pos)
      let stage2 ← twoRows circuit.stage2Width (← getAt proof.stage2 pos)
      let preprocessed ← match prepIndex with
        | none => pure (#[], #[])
        | some slot => do
          -- The supported class is honest native-builder trace geometry.
          -- A table circuit's active trace has its pinned preprocessing height.
          unless logDegree == circuit.preprocessedHeight.log2 do throw .height
          twoRows circuit.preprocessedWidth (← getAt prep slot)
      let quotient ← oneRow (2 * quotientDegree circuit) (← getAt proof.quotient pos)
      values := values.push { index, circuit, logDegree, stage1, stage2, preprocessed, quotient }
      pos := pos + 1
    else
      match prepIndex with
      | none => pure ()
      | some slot => unless (← getAt prep slot).isEmpty do throw .preprocessing
  return values

end MultiStark.Verify.Shape
