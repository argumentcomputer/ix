/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Transcript
import Ix.Aiur.Proofs.Challenger
import Ix.Aiur.Proofs.VerifierAccumulator

namespace Aiur.NativeAIR.Transcript

open Challenger
open ProofCodec (Extension)

theorem seed_length (parameters : KeyCodec.Parameters) : (seed parameters).length = 70 := by
  simp only [seed, parameterWords, List.flatMap_cons, List.flatMap_nil, List.length_append,
    KeyCodec.encodeNat_length, List.length_nil]
  rfl

theorem circuitShape_length (circuit : KeyCodec.Circuit) : (circuitShape circuit).length = 7 := by
  simp only [circuitShape, List.length_map, List.length_cons, List.length_nil]

theorem shape_length (key : KeyCodec.Key) : (shape key).length = 1 + 7 * key.circuits.length := by
  have length (circuits : List KeyCodec.Circuit) : (circuits.flatMap circuitShape).length = 7 * circuits.length := by
    induction circuits with
    | nil => rfl
    | cons circuit circuits ih =>
      simp only [List.flatMap_cons, List.length_append, circuitShape_length, List.length_cons, ih]
      omega
  simp only [shape, List.length_cons, length]
  omega

theorem fieldsBytes_length (values : List G) : (fieldsBytes values).length = 8 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [fieldsBytes, List.flatMap_cons, List.length_append, ProofCodec.encodeField,
      KeyCodec.encodeNat_length, List.length_cons] at *
    omega

theorem observeFields_bytes (state : State) (values : List G) :
    values.foldl observeField state = observeBytes state (fieldsBytes values) := by
  induction values generalizing state with
  | nil => rfl
  | cons value values ih =>
    simp only [List.foldl_cons, ih, fieldsBytes, List.flatMap_cons, observeBytes_append]
    rfl

theorem claimsFields_framing (claims : List (List G)) :
    claimsFields claims = G.ofNat claims.length :: claims.flatMap (fun claim => G.ofNat claim.length :: claim) := rfl

/-- Actual native observation order, including the full activation bitmap
and all claim boundaries, before either lookup challenge is drawn. -/
theorem lookupState_schedule (key : KeyCodec.Key) (proof : ProofCodec.Data) (claims : List (List G)) :
    lookupState key proof claims =
      (claimsFields claims).foldl observeField
        ((proof.logDegrees.map (fun degree => G.ofNat degree.toNat)).foldl observeField
          (observeCap
            (observeCap
              ((proof.active.map (fun active => if active then 1 else 0)).foldl observeField
                ((shape key).foldl observeField (initial (seed key.parameters))))
              (key.preprocessedCommitment.getD []))
            proof.commitments.stage1)) := by
  simp only [lookupState, prefixBytes, observeBytes_append, observeFields_bytes, observeCap]

theorem lookupState_valid (key : KeyCodec.Key) (proof : ProofCodec.Data) (claims : List (List G)) :
    (lookupState key proof claims).Valid := observeBytes_valid (initial_valid _) _

theorem accumulatorState_valid (proof : ProofCodec.Data) {state : State} (valid : state.Valid) :
    (accumulatorState proof state).Valid := observeExtensions_valid (observeCap_valid valid _) _

/-- Sampling transitions with the states on both sides of each native
observation. The final state is the one passed into polynomial verification. -/
structure Replay.Reads (hash : Hash32) (fuel : Nat) (key : KeyCodec.Key)
    (proof : ProofCodec.Data) (claims : List (List G)) (result : Replay) : Prop where
  states : ∃ afterBeta afterGamma afterAlpha,
    sampleExtension hash fuel (lookupState key proof claims) = some (result.challenges.beta, afterBeta) ∧
    sampleExtension hash fuel (observeExtension afterBeta result.challenges.beta) =
      some (result.challenges.gamma, afterGamma) ∧
    sampleExtension hash fuel (accumulatorState proof (observeExtension afterGamma result.challenges.gamma)) =
      some (result.challenges.alpha, afterAlpha) ∧
    sampleExtension hash fuel (observeCap afterAlpha proof.commitments.quotient) =
      some (result.challenges.zeta, result.state)

theorem replay_success {hash : Hash32} {fuel : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {result : Replay} (accepted : replay hash fuel key proof claims = some result) :
    result.Reads hash fuel key proof claims := by
  simp only [replay, bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.exists] at accepted
  obtain ⟨beta, afterBeta, first, gamma, afterGamma, second, alpha, afterAlpha, third,
    zeta, final, fourth, rfl⟩ := accepted
  exact ⟨afterBeta, afterGamma, afterAlpha, first, second, third, fourth⟩

theorem Replay.Reads.complete {hash : Hash32} {fuel : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {result : Replay} (reads : result.Reads hash fuel key proof claims) :
    replay hash fuel key proof claims = some result := by
  obtain ⟨afterBeta, afterGamma, afterAlpha, first, second, third, fourth⟩ := reads.states
  simp only [replay, first, second, third, fourth, bind, pure, Option.bind_some]

theorem replay_iff (hash : Hash32) (fuel : Nat) (key : KeyCodec.Key) (proof : ProofCodec.Data)
    (claims : List (List G)) (result : Replay) : replay hash fuel key proof claims = some result ↔
      result.Reads hash fuel key proof claims := ⟨replay_success, Replay.Reads.complete⟩

theorem replay_mono {hash : Hash32} {fuel more : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {result : Replay} (accepted : replay hash fuel key proof claims = some result)
    (bound : fuel ≤ more) : replay hash more key proof claims = some result := by
  obtain ⟨afterBeta, afterGamma, afterAlpha, first, second, third, fourth⟩ := (replay_success accepted).states
  exact (Replay.Reads.complete ⟨afterBeta, afterGamma, afterAlpha, sampleExtension_mono first bound,
    sampleExtension_mono second bound, sampleExtension_mono third bound, sampleExtension_mono fourth bound⟩)

theorem replay_unique {hash : Hash32} {fuel other : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {left right : Replay} (first : replay hash fuel key proof claims = some left)
    (second : replay hash other key proof claims = some right) : left = right := by
  have one := replay_mono first (Nat.le_max_left fuel other)
  have two := replay_mono second (Nat.le_max_right fuel other)
  exact Option.some.inj (one.symm.trans two)

theorem replay_valid {hash : Hash32} {fuel : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {result : Replay} (accepted : replay hash fuel key proof claims = some result) :
    result.state.Valid := by
  obtain ⟨afterBeta, afterGamma, afterAlpha, first, second, third, fourth⟩ := (replay_success accepted).states
  have beta := sampleExtension_valid first (lookupState_valid key proof claims)
  have gamma := sampleExtension_valid second (observeExtension_valid beta _)
  have alpha := sampleExtension_valid third (accumulatorState_valid proof (observeExtension_valid gamma _))
  exact sampleExtension_valid fourth (observeCap_valid alpha _)

theorem verifyArithmetic_success {hash : Hash32} {fuel : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {rows : List ProofShape.Row} {result : Replay}
    (accepted : verifyArithmetic hash fuel key proof claims rows = some result) :
    replay hash fuel key proof claims = some result ∧
      VerifierArithmetic.verify result.challenges claims rows = some true := by
  simp only [verifyArithmetic, bind, Option.bind_eq_some_iff] at accepted
  obtain ⟨replayed, replayRead, check, arithmetic, accepted⟩ := accepted
  cases check with
  | false => cases accepted
  | true => cases accepted; exact ⟨replayRead, arithmetic⟩

theorem verifyArithmetic_iff (hash : Hash32) (fuel : Nat) (key : KeyCodec.Key) (proof : ProofCodec.Data)
    (claims : List (List G)) (rows : List ProofShape.Row) (result : Replay) :
    verifyArithmetic hash fuel key proof claims rows = some result ↔
      replay hash fuel key proof claims = some result ∧
        VerifierArithmetic.verify result.challenges claims rows = some true := by
  constructor
  · exact verifyArithmetic_success
  · rintro ⟨replayed, accepted⟩
    simp only [verifyArithmetic, replayed, accepted, bind, Option.bind_some, ↓reduceIte]

theorem verifyArithmetic_mono {hash : Hash32} {fuel more : Nat} {key : KeyCodec.Key} {proof : ProofCodec.Data}
    {claims : List (List G)} {rows : List ProofShape.Row} {result : Replay}
    (accepted : verifyArithmetic hash fuel key proof claims rows = some result) (bound : fuel ≤ more) :
    verifyArithmetic hash more key proof claims rows = some result := by
  obtain ⟨replayed, arithmetic⟩ := verifyArithmetic_success accepted
  exact (verifyArithmetic_iff _ _ _ _ _ _ _).mpr ⟨replay_mono replayed bound, arithmetic⟩

end Aiur.NativeAIR.Transcript

namespace Aiur.BoundVerifier
open NativeAIR

/-- The checked selected key and proof supply the entire transcript. This
conclusion still needs PCS authentication and the cryptographic bad-event
analysis before it can imply a satisfying execution trace. -/
theorem CompiledBackend.transcript_row {selection : Selection} (backend : CompiledBackend selection)
    {bytes : ByteArray} (checked : CheckedProof backend.keyData bytes) {hash : Challenger.Hash32}
    {fuel : Nat} {claims : List (List G)} {result : Transcript.Replay}
    (accepted : Transcript.verifyArithmetic hash fuel backend.keyData checked.data claims checked.rows = some result)
    {position : Nat} {row : ProofShape.Row} (present : checked.rows[position]? = some row) :
    result.Reads hash fuel backend.keyData checked.data claims ∧
      row.Sourced backend.keyData checked.data row.circuitIndex position ∧ row.Fits backend.keyData.parameters ∧
      ∃ initial before evaluation,
        VerifierArithmetic.initialAccumulator result.challenges claims = some initial ∧
        (initial :: checked.rows.map (·.accumulator))[position]? = some before ∧
        VerifierArithmetic.evaluate result.challenges row before = some evaluation ∧
        Quotient.composition result.challenges.alpha evaluation.constraints =
          Domain.vanishing evaluation.domain result.challenges.zeta * evaluation.quotientValue := by
  obtain ⟨replayed, arithmetic⟩ := Transcript.verifyArithmetic_success accepted
  obtain ⟨_, sourced, fits⟩ := checked.row present
  exact ⟨Transcript.replay_success replayed, sourced, fits, VerifierArithmetic.verify_row arithmetic present⟩

end Aiur.BoundVerifier
