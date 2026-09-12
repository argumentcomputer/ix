module
public import Ix.MultiStark.Verify.Protocol.Replay
public import Ix.MultiStark.Verify.Fri.Transcript

/-! Independent FRI admission and Fiat-Shamir relations. Geometry is fixed by
the verifier's input matrices and the authenticated arity schedule. Query
indices and folding challenges are derived states, never proof advice. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

open Transcript (Challenger)

def PointsObserved (limits : Transcript.Limits) : List Pcs.PointOpening → Challenger → Challenger → Prop
  | [], state, final => state = final
  | opening :: rest, state, final =>
    ∃ middle, ExtensionsObserved limits opening.values.toList state middle ∧
      PointsObserved limits rest middle final

def MatricesObserved (limits : Transcript.Limits) : List Pcs.Matrix → Challenger → Challenger → Prop
  | [], state, final => state = final
  | matrix :: rest, state, final =>
    ∃ middle, PointsObserved limits matrix.points.toList state middle ∧
      MatricesObserved limits rest middle final

def RoundsObserved (limits : Transcript.Limits) : List Pcs.Round → Challenger → Challenger → Prop
  | [], state, final => state = final
  | round :: rest, state, final =>
    ∃ middle, MatricesObserved limits round.matrices.toList state middle ∧
      RoundsObserved limits rest middle final

def FriShape (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round) (proof : FriProof)
    (result : Array Nat × Nat × Nat) : Prop :=
  let arities := proof.commitOpenings.map (·.logArity.toNat)
  let logFinal := params.logBlowup + params.logFinalPolyLen
  let logGlobal := arities.toList.sum + logFinal
  let matrices := rounds.flatMap (·.matrices)
  0 < params.numQueries ∧ params.numQueries ≤ limits.queries ∧
  (proof.commits.size = proof.commitOpenings.size ∧
    proof.commits.size = proof.commitPow.size ∧ proof.inputOpenings.size = rounds.size) ∧
  logFinal ≤ 32 ∧
  (∀ opening ∈ proof.commitOpenings, 1 ≤ opening.logArity.toNat ∧
    opening.logArity.toNat ≤ params.maxLogArity ∧ opening.logArity.toNat ≤ 32) ∧
  (∀ opening ∈ proof.commitOpenings, 2 ^ opening.logArity.toNat ≤ limits.foldArity) ∧
  (∀ opening ∈ proof.commitOpenings, opening.siblings.size = params.numQueries ∧
    ∀ siblings ∈ opening.siblings, siblings.size = 2 ^ opening.logArity.toNat - 1) ∧
  logGlobal ≤ 32 ∧ matrices ≠ #[] ∧
  (∀ matrix ∈ matrices, matrix.logDegree + params.logBlowup ≤ 32) ∧
  matrices.foldl (fun height matrix => max height (matrix.logDegree + params.logBlowup)) 0 = logGlobal ∧
  proof.finalPoly.size = 2 ^ params.logFinalPolyLen ∧
  (∀ round ∈ rounds, round.matrices ≠ #[]) ∧
  (∀ round ∈ rounds, ∀ matrix ∈ round.matrices, matrix.points ≠ #[]) ∧
  (∀ round ∈ rounds, ∀ matrix ∈ round.matrices, ∀ opening ∈ matrix.points,
    opening.values.size = matrix.width) ∧
  (arities, logGlobal, logFinal) = result

def CommitChallenges (limits : Transcript.Limits) (bits : Nat) :
    List MerkleCap → List Field → Challenger → List Ext → Challenger → Prop
  | [], [], state, [], final => state = final
  | cap :: caps, witness :: witnesses, state, beta :: betas, final =>
    ∃ capState powState betaState,
      CapObserved limits cap state capState ∧ Grinding limits bits witness capState powState ∧
      ExtensionDraw limits powState beta betaState ∧
      CommitChallenges limits bits caps witnesses betaState betas final
  | _, _, _, _, _ => False

def QueryDraws (bits : Nat) : Nat → Challenger → List Nat → Challenger → Prop
  | 0, state, [], final => state = final
  | count + 1, state, index :: rest, final =>
    ∃ middle, BitsDraw bits state index middle ∧ QueryDraws bits count middle rest final
  | _, _, _, _ => False

def FriTranscriptAction (limits : Transcript.Limits) (params : Parameters) (proof : FriProof)
    (arities : Array Nat) (logGlobal : Nat) (state : Challenger)
    (alpha : Ext) (betas : List Ext) (indices : List Nat) (final : Challenger) : Prop :=
  ∃ alphaState commitState polyState arityState powState,
    ExtensionDraw limits state alpha alphaState ∧
    CommitChallenges limits params.commitPowBits proof.commits.toList proof.commitPow.toList
      alphaState betas commitState ∧
    ExtensionsObserved limits proof.finalPoly.toList commitState polyState ∧
    WordObservations Ix.Ixby.goldilocksModulus limits arities.toList polyState arityState ∧
    Grinding limits params.queryPowBits proof.queryPow arityState powState ∧
    QueryDraws logGlobal params.numQueries powState indices final

def FriTranscript (limits : Fri.Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state : Challenger) (challenges : Fri.Challenges) (final : Challenger) : Prop :=
  FriShape limits params rounds proof (challenges.arities, challenges.logGlobal, challenges.logFinal) ∧
    FriTranscriptAction limits.transcript params proof challenges.arities challenges.logGlobal
      state challenges.alpha challenges.betas.toList challenges.indices.toList final

end MultiStark.Verify.Protocol
