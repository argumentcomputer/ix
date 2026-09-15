module
public import Ix.MultiStark.Verify.Pcs.Check
public import Ix.MultiStark.Verify.Protocol.Shape
public import Ix.MultiStark.Verify.Protocol.FriCheck

/-! The PCS opens the OOD values admitted by the sparse shape relation. The
trace-domain generator fixes the second point; quotient slices deliberately
use that same trace degree. All canonical preprocessing slots are retained.
The resulting openings are observed before the complete FRI relation. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def TwoPoints (logDegree width : Nat) (zeta : Ext) (rows : Array Ext × Array Ext) (result : Pcs.Matrix) : Prop :=
  ∃ generator, TwoAdicGenerator logDegree generator ∧
    (⟨logDegree, width, #[⟨zeta, rows.1⟩, ⟨Arithmetic.scale zeta generator, rows.2⟩]⟩ : Pcs.Matrix) = result

def ActiveMatrices (zeta : Ext) : List Shape.CircuitValues → (List Pcs.Matrix × List Pcs.Matrix × List Pcs.Matrix) → Prop
  | [], result => ([], [], []) = result
  | value :: values, result =>
    ∃ main lookup more, TwoPoints value.logDegree value.circuit.mainWidth zeta value.stage1 main ∧
      TwoPoints value.logDegree value.circuit.stage2Width zeta value.stage2 lookup ∧
      ActiveMatrices zeta values more ∧
      (main :: more.1, lookup :: more.2.1,
        (⟨value.logDegree, 2 * Shape.quotientDegree value.circuit, #[⟨zeta, value.quotient⟩]⟩ : Pcs.Matrix) :: more.2.2) = result

def PreprocessedMatrix (circuit : Circuit) (values : Array Shape.CircuitValues) (zeta : Ext) (index : Nat)
    (result : Pcs.Matrix) : Prop :=
  match values.find? (·.index == index) with
  | some value => TwoPoints value.logDegree circuit.preprocessedWidth zeta value.preprocessed result
  | none => (⟨circuit.preprocessedHeight.log2, circuit.preprocessedWidth, #[]⟩ : Pcs.Matrix) = result

def PreprocessedMatrices (key : Key) (values : Array Shape.CircuitValues) (zeta : Ext) :
    List Circuit → Nat → List Pcs.Matrix → Prop
  | [], _, result => [] = result
  | circuit :: circuits, index, result =>
    match key.preprocessedIndices[index]? with
    | none => False
    | some none => PreprocessedMatrices key values zeta circuits (index + 1) result
    | some (some _) =>
      ∃ matrix rest, PreprocessedMatrix circuit values zeta index matrix ∧
        PreprocessedMatrices key values zeta circuits (index + 1) rest ∧ matrix :: rest = result

def PcsRounds (key : Key) (proof : Proof) (zeta : Ext) (result : Array Pcs.Round) : Prop :=
  ∃ values, ShapeAccepted key proof values ∧
    ∃ matrices, ActiveMatrices zeta values.toList matrices ∧
      let rounds : Array Pcs.Round := #[⟨proof.commitments.stage1, matrices.1.toArray⟩,
        ⟨proof.commitments.stage2, matrices.2.1.toArray⟩, ⟨proof.commitments.quotient, matrices.2.2.toArray⟩]
      match key.preprocessed with
      | none => rounds = result
      | some commitment =>
        ∃ prep, PreprocessedMatrices key values zeta key.circuits.toList 0 prep ∧
          rounds.push ⟨commitment, prep.toArray⟩ = result

def PcsAccepted (limits : Fri.Limits) (key : Key) (proof : Proof) (zeta : Ext)
    (state : Transcript.Challenger) (challenges : Fri.Challenges) (final : Transcript.Challenger) : Prop :=
  ∃ rounds middle, PcsRounds key proof zeta rounds ∧ RoundsObserved limits.transcript rounds.toList state middle ∧
    FriAccepted limits key.params rounds proof.fri middle challenges final

end MultiStark.Verify.Protocol
