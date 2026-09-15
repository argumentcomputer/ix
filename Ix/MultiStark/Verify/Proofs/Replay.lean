module
public import Ix.MultiStark.Verify.Proofs.Transcript
public import Ix.MultiStark.Verify.Protocol.Replay

public section

namespace MultiStark.Verify.Proofs

open Transcript (Challenger Limits Challenges)

theorem observeNat_refines (limits : Limits) (value : Nat) (state final : Challenger) :
    ((Transcript.observeNat limits value).run state = .ok ((), final)) ↔
      value < Ix.Ixby.goldilocksModulus ∧
        Protocol.Observed limits state (Codec.Wire.littleEndian 8 value) final := by
  by_cases canonical : value < Ix.Ixby.goldilocksModulus
  · simp only [Transcript.observeNat, canonical, ↓reduceDIte, Transcript.observeField,
      observeBytes_refines, true_and]
  · simp only [Transcript.observeNat, canonical, ↓reduceDIte, false_and, action_throw_ok_iff]

theorem observeChunks_refines (limits : Limits) (chunks : List Bytes) (state final : Challenger) :
    ((Transcript.observeChunks limits chunks).run state = .ok ((), final)) ↔
      Protocol.Observations limits chunks state final := by
  induction chunks generalizing state with
  | nil => simp only [Transcript.observeChunks, action_pure_ok_iff, Protocol.Observations, true_and]
  | cons bytes rest ih =>
    simp only [Transcript.observeChunks, action_bind_ok_iff, unit_exists_iff,
      observeBytes_refines, ih, Protocol.Observations]

theorem observeNats_refines (limits : Limits) (words : List Nat) (state final : Challenger) :
    ((Transcript.observeNats limits words).run state = .ok ((), final)) ↔
      Protocol.WordObservations Ix.Ixby.goldilocksModulus limits words state final := by
  induction words generalizing state with
  | nil => simp only [Transcript.observeNats, action_pure_ok_iff, Protocol.WordObservations, true_and]
  | cons word rest ih =>
    simp only [Transcript.observeNats, action_bind_ok_iff, unit_exists_iff, observeNat_refines,
      Protocol.WordObservations, ih, and_assoc, exists_and_left]

theorem observeExt_refines (limits : Limits) (value : Ext) (state final : Challenger) :
    ((Transcript.observeExt limits value).run state = .ok ((), final)) ↔
      Protocol.ExtensionObserved limits value state final :=
  observeChunks_refines limits _ state final

theorem observeExts_refines (limits : Limits) (values : List Ext) (state final : Challenger) :
    ((Transcript.observeExts limits values).run state = .ok ((), final)) ↔
      Protocol.ExtensionsObserved limits values state final := by
  induction values generalizing state with
  | nil => simp only [Transcript.observeExts, action_pure_ok_iff, Protocol.ExtensionsObserved, true_and]
  | cons value rest ih =>
    simp only [Transcript.observeExts, action_bind_ok_iff, unit_exists_iff, observeExt_refines,
      Protocol.ExtensionsObserved, ih]

theorem observeFields_refines (limits : Limits) (values : Array Field) (state final : Challenger) :
    ((Transcript.observeFields limits values).run state = .ok ((), final)) ↔
      Protocol.FieldsObserved limits values state final :=
  observeChunks_refines limits _ state final

theorem observeCap_refines (limits : Limits) (cap : MerkleCap) (state final : Challenger) :
    ((Transcript.observeCap limits cap).run state = .ok ((), final)) ↔
      Protocol.CapObserved limits cap state final :=
  observeChunks_refines limits _ state final

theorem observeClaimList_refines (limits : Limits) (claims : List (Array Field))
    (state final : Challenger) :
    ((Transcript.observeClaimList limits claims).run state = .ok ((), final)) ↔
      Protocol.ClaimListObserved limits claims state final := by
  induction claims generalizing state with
  | nil => simp only [Transcript.observeClaimList, action_pure_ok_iff, Protocol.ClaimListObserved, true_and]
  | cons claim rest ih =>
    simp only [Transcript.observeClaimList, action_bind_ok_iff, unit_exists_iff, observeNat_refines,
      observeFields_refines, Protocol.ClaimListObserved, ih, and_assoc, exists_and_left]

theorem observeClaims_refines (limits : Limits) (claims : Array (Array Field))
    (state final : Challenger) :
    ((Transcript.observeClaims limits claims).run state = .ok ((), final)) ↔
      Protocol.ClaimsObserved limits claims state final := by
  simp only [Transcript.observeClaims, action_bind_ok_iff, unit_exists_iff, observeNat_refines,
    observeClaimList_refines, Protocol.ClaimsObserved, and_assoc, exists_and_left]

theorem sampleExt_refines (limits : Limits) (state final : Challenger) (value : Ext) :
    ((Transcript.sampleExt limits).run state = .ok (value, final)) ↔
      Protocol.ExtensionDraw limits state value final := by
  cases value with
  | mk c0 c1 =>
    simp only [Transcript.sampleExt, action_bind_ok_iff,
      action_pure_ok_iff, Protocol.ExtensionDraw]
    simp only [Transcript.sampleField, StateT.run, sampleField_refines,
      Ix.Ixby.ExtGoldilocks.mk.injEq, and_assoc]
    constructor
    · rintro ⟨v0, middle, first, v1, last, second, rfl, rfl, rfl⟩
      exact ⟨middle, first, second⟩
    · rintro ⟨middle, first, second⟩
      exact ⟨c0, middle, first, c1, final, second, rfl, rfl, rfl⟩

theorem observeParameters_refines (limits : Limits) (words : List Nat) (state final : Challenger) :
    ((Transcript.observeParameters limits words).run state = .ok ((), final)) ↔
      Protocol.WordObservations 65536 limits words state final := by
  induction words generalizing state with
  | nil => simp only [Transcript.observeParameters, action_pure_ok_iff, Protocol.WordObservations, true_and]
  | cons word rest ih =>
    by_cases bounded : word < 65536
    · simp only [Transcript.observeParameters, bounded, Nat.not_le.mpr bounded, ↓reduceIte,
        action_bind_ok_iff, unit_exists_iff, observeBytes_refines, Protocol.WordObservations, ih, true_and]
    · simp only [Transcript.observeParameters, bounded, Nat.le_of_not_gt bounded, ↓reduceIte,
        Protocol.WordObservations, false_and, action_throw_ok_iff]

theorem seed_refines (limits : Limits) (params : Parameters) (final : Challenger) :
    Transcript.seed limits params = .ok final ↔ Protocol.Seeded limits params final := by
  simp only [Transcript.seed, bind_ok_iff, pure_ok_iff, Prod.exists,
    unit_exists_iff, action_bind_ok_iff, observeBytes_refines, observeParameters_refines,
    Protocol.Seeded, Parameters.words, exists_eq_right]

theorem beforeLookup_refines (limits : Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) (state final : Challenger) :
    ((Transcript.beforeLookup limits key claims proof).run state = .ok ((), final)) ↔
      Protocol.BeforeLookup limits key claims proof state final := by
  simp only [Transcript.beforeLookup, action_bind_ok_iff, unit_exists_iff, observeNats_refines,
    observeCap_refines, observeClaims_refines, Protocol.BeforeLookup, exists_and_left]

theorem prefixReplay_refines (limits : Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) (state final : Challenger) (challenges : Challenges) :
    ((Transcript.prefixReplay limits key claims proof).run state = .ok (challenges, final)) ↔
      Protocol.Prefix limits key claims proof state challenges final := by
  cases challenges with
  | mk lookup fingerprint alpha zeta =>
    simp only [Transcript.prefixReplay, action_bind_ok_iff, action_pure_ok_iff,
      unit_exists_iff,
      beforeLookup_refines, sampleExt_refines, observeExt_refines,
      observeCap_refines, observeExts_refines, Protocol.Prefix, Challenges.mk.injEq,
      and_assoc]
    constructor
    · rintro ⟨s0, h0, l, s1, h1, s2, h2, f, s3, h3, s4, h4, s5, h5, s6, h6,
        a, s7, h7, s8, h8, z, s9, h9, rfl, rfl, rfl, rfl, rfl⟩
      exact ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    · rintro ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      exact ⟨s0, h0, lookup, s1, h1, s2, h2, fingerprint, s3, h3, s4, h4, s5, h5, s6, h6,
        alpha, s7, h7, s8, h8, zeta, final, h9, rfl, rfl, rfl, rfl, rfl⟩

theorem replay_refines (limits : Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) (final : Challenger) (challenges : Challenges) :
    Transcript.replay limits key claims proof = .ok (challenges, final) ↔
      Protocol.TranscriptPrefix limits key claims proof challenges final := by
  simp only [Transcript.replay, bind_ok_iff, seed_refines, prefixReplay_refines,
    Protocol.TranscriptPrefix]

end MultiStark.Verify.Proofs
