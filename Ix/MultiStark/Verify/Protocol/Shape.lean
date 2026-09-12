module
public import Ix.MultiStark.Verify.Shape
public import Ix.MultiStark.Verify.Protocol.Key

/-! Sparse proof admission: canonical circuit positions advance on every
step, active positions only on active circuits. Preprocessed openings keep
their full key-owned slot map, including empty inactive slots. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def TwoRows (width : Nat) (rows : Array (Array Ext)) (result : Array Ext × Array Ext) : Prop :=
  rows.toList = [result.1, result.2] ∧ result.1.size = width ∧ result.2.size = width

def OneRow (width : Nat) (rows : Array (Array Ext)) (result : Array Ext) : Prop :=
  rows.toList = [result] ∧ result.size = width

def PreprocessedRows (circuit : Circuit) (logDegree : Nat) (prep : OpenedRound) :
    Option Nat → (Array Ext × Array Ext) → Prop
  | none, result => (#[], #[]) = result
  | some slot, result =>
    logDegree = circuit.preprocessedHeight.log2 ∧
      ∃ rows, prep[slot]? = some rows ∧ TwoRows circuit.preprocessedWidth rows result

def InactivePreprocessed (prep : OpenedRound) : Option Nat → Prop
  | none => True
  | some slot => prep[slot]? = some #[]

def ActiveCircuitValues (key : Key) (proof : Proof) (circuit : Circuit) (prepIndex : Option Nat)
    (index pos : Nat) (result : Shape.CircuitValues) : Prop :=
  ∃ degree, proof.logDegrees[pos]? = some degree ∧
    degree.toNat + Shape.quotientLog circuit + key.params.logBlowup ≤ 32 ∧
    ∃ rows1 stage1, proof.stage1[pos]? = some rows1 ∧ TwoRows circuit.mainWidth rows1 stage1 ∧
      ∃ rows2 stage2, proof.stage2[pos]? = some rows2 ∧ TwoRows circuit.stage2Width rows2 stage2 ∧
        ∃ preprocessed, PreprocessedRows circuit degree.toNat (proof.preprocessed.getD #[]) prepIndex preprocessed ∧
          ∃ rows quotient, proof.quotient[pos]? = some rows ∧ OneRow (2 * Shape.quotientDegree circuit) rows quotient ∧
            (⟨index, circuit, degree.toNat, stage1, stage2, preprocessed, quotient⟩ : Shape.CircuitValues) = result

def ShapeCircuits (key : Key) (proof : Proof) : List Circuit → Nat → Nat → List Shape.CircuitValues → Prop
  | [], _, _, result => [] = result
  | circuit :: circuits, index, pos, result =>
    ∃ active prepIndex, proof.active[index]? = some active ∧ key.preprocessedIndices[index]? = some prepIndex ∧
      match active with
      | false => InactivePreprocessed (proof.preprocessed.getD #[]) prepIndex ∧
        ShapeCircuits key proof circuits (index + 1) pos result
      | true => ∃ value rest, ActiveCircuitValues key proof circuit prepIndex index pos value ∧
        ShapeCircuits key proof circuits (index + 1) (pos + 1) rest ∧ value :: rest = result

def ShapeAccepted (key : Key) (proof : Proof) (result : Array Shape.CircuitValues) : Prop :=
  let activeCount := (proof.active.filter id).size
  let prepCount := (key.preprocessedIndices.filter Option.isSome).size
  KeyAdmissible key ∧ (proof.active.size = key.circuits.size ∧ true ∈ proof.active) ∧
    (proof.logDegrees.size = activeCount ∧ proof.accumulators.size = activeCount ∧
      proof.stage1.size = activeCount ∧ proof.stage2.size = activeCount ∧ proof.quotient.size = activeCount) ∧
    (proof.preprocessed.getD #[]).size = prepCount ∧
    ShapeCircuits key proof key.circuits.toList 0 0 result.toList

end MultiStark.Verify.Protocol
