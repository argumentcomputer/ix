module
public import Ix.MultiStark.Verify.Protocol.Pcs
public import Ix.MultiStark.Verify.Proofs.Shape
public import Ix.MultiStark.Verify.Proofs.FriCheck

public section

namespace MultiStark.Verify.Proofs

theorem twoPoints_refines (logDegree width : Nat) (zeta : Ext) (rows : Array Ext × Array Ext) (result : Pcs.Matrix) :
    Pcs.twoPoints logDegree width zeta rows = .ok result ↔ Protocol.TwoPoints logDegree width zeta rows result := by
  simp only [Pcs.twoPoints, bind_ok_iff, mapError_ok_iff, twoAdicGenerator_refines, pure_ok_iff, Protocol.TwoPoints]

theorem activeMatrices_refines (zeta : Ext) (values : List Shape.CircuitValues)
    (result : List Pcs.Matrix × List Pcs.Matrix × List Pcs.Matrix) :
    Pcs.activeMatrices zeta values = .ok result ↔ Protocol.ActiveMatrices zeta values result := by
  induction values generalizing result with
  | nil => simp [Pcs.activeMatrices, Protocol.ActiveMatrices]
  | cons value values ih =>
    simp only [Pcs.activeMatrices, bind_ok_iff, twoPoints_refines, ih, pure_ok_iff,
      Protocol.ActiveMatrices, exists_and_left]

theorem preprocessedMatrix_refines (circuit : Circuit) (values : Array Shape.CircuitValues) (zeta : Ext)
    (index : Nat) (result : Pcs.Matrix) :
    Pcs.preprocessedMatrix circuit values zeta index = .ok result ↔
      Protocol.PreprocessedMatrix circuit values zeta index result := by
  unfold Pcs.preprocessedMatrix Protocol.PreprocessedMatrix
  cases values.find? (·.index == index) <;> simp [twoPoints_refines]

theorem preprocessedMatrices_refines (key : Key) (values : Array Shape.CircuitValues) (zeta : Ext)
    (circuits : List Circuit) (index : Nat) (result : List Pcs.Matrix) :
    Pcs.preprocessedMatrices key values zeta circuits index = .ok result ↔
      Protocol.PreprocessedMatrices key values zeta circuits index result := by
  induction circuits generalizing index result with
  | nil => simp [Pcs.preprocessedMatrices, Protocol.PreprocessedMatrices]
  | cons circuit circuits ih =>
    simp only [Pcs.preprocessedMatrices, Protocol.PreprocessedMatrices]
    cases key.preprocessedIndices[index]? with
    | none => simp
    | some slot =>
      cases slot <;>
        simp only [bind_ok_iff, preprocessedMatrix_refines, ih, pure_ok_iff, exists_and_left]

theorem pcs_rounds_refines (key : Key) (proof : Proof) (zeta : Ext) (result : Array Pcs.Round) :
    Pcs.rounds key proof zeta = .ok result ↔ Protocol.PcsRounds key proof zeta result := by
  unfold Pcs.rounds Protocol.PcsRounds
  cases key.preprocessed <;>
    simp only [bind_ok_iff, mapError_ok_iff, shape_check_refines, activeMatrices_refines,
      preprocessedMatrices_refines, pure_ok_iff]

theorem pcs_check_refines (limits : Fri.Limits) (key : Key) (proof : Proof) (zeta : Ext)
    (state final : Transcript.Challenger) (challenges : Fri.Challenges) :
    Pcs.check limits key proof zeta state = .ok (challenges, final) ↔
      Protocol.PcsAccepted limits key proof zeta state challenges final := by
  simp only [Pcs.check, bind_ok_iff, mapError_ok_iff, pcs_rounds_refines, Prod.exists,
    unit_exists_iff, observeOpenings_refines, fri_check_refines, Protocol.PcsAccepted, exists_and_left]

end MultiStark.Verify.Proofs
