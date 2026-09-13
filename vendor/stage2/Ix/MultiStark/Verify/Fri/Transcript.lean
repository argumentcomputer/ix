module
public import Ix.MultiStark.Verify.Fri.Basic

public section
@[expose] section

namespace MultiStark.Verify.Fri

def shape (limits : Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) : Except Error (Array Nat × Nat × Nat) := do
  ensure (decide (0 < params.numQueries)) .query
  ensure (decide (params.numQueries ≤ limits.queries)) .limit
  ensure (proof.commits.size == proof.commitOpenings.size &&
      proof.commits.size == proof.commitPow.size &&
      proof.inputOpenings.size == rounds.size) .count
  ensure (decide (params.logBlowup + params.logFinalPolyLen ≤ 32)) .height
  let arities := proof.commitOpenings.map (·.logArity.toNat)
  ensure (proof.commitOpenings.all fun opening =>
    1 ≤ opening.logArity.toNat && opening.logArity.toNat ≤ params.maxLogArity &&
      opening.logArity.toNat ≤ 32) .arity
  -- Every shift is admitted before the width-dependent checks below.
  ensure (proof.commitOpenings.all fun opening => 2 ^ opening.logArity.toNat ≤ limits.foldArity) .limit
  ensure (proof.commitOpenings.all fun opening => opening.siblings.size == params.numQueries &&
    opening.siblings.all (·.size == 2 ^ opening.logArity.toNat - 1)) .count
  let logFinal := params.logBlowup + params.logFinalPolyLen
  let logGlobal := arities.toList.sum + logFinal
  ensure (decide (logGlobal ≤ 32)) .height
  let matrices := rounds.flatMap (·.matrices)
  ensure (!matrices.isEmpty) .empty
  ensure (matrices.all (fun matrix => matrix.logDegree + params.logBlowup ≤ 32)) .height
  let expected := matrices.foldl (fun height matrix => max height (matrix.logDegree + params.logBlowup)) 0
  ensure (expected == logGlobal) .height
  ensure (proof.finalPoly.size == 2 ^ params.logFinalPolyLen) .count
  ensure (rounds.all fun round => !round.matrices.isEmpty) .empty
  -- Current native PCS rejects matrices opened at no points. Inactive
  -- preprocessing therefore remains outside its accepted proof class.
  ensure (rounds.all fun round => round.matrices.all fun matrix => !matrix.points.isEmpty) .point
  ensure (rounds.all fun round => round.matrices.all fun matrix =>
    matrix.points.all (·.values.size == matrix.width)) .width
  return (arities, logGlobal, logFinal)

def commitPhase (limits : Transcript.Limits) (bits : Nat) :
    List MerkleCap → List Field → Transcript.Action (List Ext)
  | [], [] => pure []
  | commitment :: commitments, witness :: witnesses => do
    Transcript.observeCap limits commitment
    Transcript.checkWitness limits bits witness
    let beta ← Transcript.sampleExt limits
    let rest ← commitPhase limits bits commitments witnesses
    return beta :: rest
  | _, _ => throw .fieldRange

def queryIndices (bits : Nat) : Nat → Transcript.Action (List Nat)
  | 0 => pure []
  | count + 1 => do
    let index ← Transcript.sampleBits bits
    let rest ← queryIndices bits count
    return index :: rest

def replayAction (limits : Transcript.Limits) (params : Parameters) (proof : FriProof)
    (arities : Array Nat) (logGlobal : Nat) : Transcript.Action (Ext × List Ext × List Nat) := do
  let alpha ← Transcript.sampleExt limits
  let betas ← commitPhase limits params.commitPowBits proof.commits.toList proof.commitPow.toList
  Transcript.observeExts limits proof.finalPoly.toList
  Transcript.observeNats limits arities.toList
  Transcript.checkWitness limits params.queryPowBits proof.queryPow
  let indices ← queryIndices logGlobal params.numQueries
  return (alpha, betas, indices)

/-- Begins AFTER the PCS has observed its claimed OOD evaluations. PoW with
zero bits is inert; variable arities are observed only before query PoW. -/
def replay (limits : Limits) (params : Parameters) (rounds : Array Pcs.Round)
    (proof : FriProof) (state : Transcript.Challenger) :
    Except Error (Challenges × Transcript.Challenger) := do
  let (arities, logGlobal, logFinal) ← shape limits params rounds proof
  let ((alpha, betas, indices), next) ←
    ((replayAction limits.transcript params proof arities logGlobal).run state).mapError Error.transcript
  return (⟨alpha, betas.toArray, indices.toArray, arities, logGlobal, logFinal⟩, next)

end MultiStark.Verify.Fri
