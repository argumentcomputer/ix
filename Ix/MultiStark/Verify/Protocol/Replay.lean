module
public import Ix.MultiStark.Verify.Protocol.Transcript
public import Ix.MultiStark.Verify.Transcript.Replay

/-! Declarative observation sequences and the multi-stark Fiat-Shamir
prefix. Every intermediate state is related by a byte observation or a
bounded first-canonical draw. The relation does not invoke `seed`,
`prefixReplay`, or `replay`, and preserves the final state passed to PCS. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

open Transcript (Challenger Limits Challenges)

def Observations (limits : Limits) : List Bytes → Challenger → Challenger → Prop
  | [], state, final => state = final
  | bytes :: rest, state, final =>
    ∃ middle, Observed limits state bytes middle ∧ Observations limits rest middle final

def WordObservations (bound : Nat) (limits : Limits) : List Nat → Challenger → Challenger → Prop
  | [], state, final => state = final
  | word :: rest, state, final =>
    word < bound ∧ ∃ middle, Observed limits state (Codec.Wire.littleEndian 8 word) middle ∧
      WordObservations bound limits rest middle final

def ExtensionObserved (limits : Limits) (value : Ext) (state final : Challenger) : Prop :=
  Observations limits [Codec.Wire.littleEndian 8 value.c0.val,
    Codec.Wire.littleEndian 8 value.c1.val] state final

def ExtensionsObserved (limits : Limits) : List Ext → Challenger → Challenger → Prop
  | [], state, final => state = final
  | value :: rest, state, final =>
    ∃ middle, ExtensionObserved limits value state middle ∧
      ExtensionsObserved limits rest middle final

def FieldsObserved (limits : Limits) (values : Array Field) (state final : Challenger) : Prop :=
  Observations limits (values.toList.map (fun value => Codec.Wire.littleEndian 8 value.val)) state final

def CapObserved (limits : Limits) (cap : MerkleCap) (state final : Challenger) : Prop :=
  Observations limits (cap.toList.map (·.bytes)) state final

def ClaimListObserved (limits : Limits) : List (Array Field) → Challenger → Challenger → Prop
  | [], state, final => state = final
  | claim :: rest, state, final =>
    claim.size < Ix.Ixby.goldilocksModulus ∧ ∃ lengthState fieldsState,
      Observed limits state (Codec.Wire.littleEndian 8 claim.size) lengthState ∧
      FieldsObserved limits claim lengthState fieldsState ∧
      ClaimListObserved limits rest fieldsState final

def ClaimsObserved (limits : Limits) (claims : Array (Array Field)) (state final : Challenger) : Prop :=
  claims.size < Ix.Ixby.goldilocksModulus ∧ ∃ middle,
    Observed limits state (Codec.Wire.littleEndian 8 claims.size) middle ∧
    ClaimListObserved limits claims.toList middle final

def ExtensionDraw (limits : Limits) (state : Challenger) (value : Ext) (final : Challenger) : Prop :=
  ∃ middle, FieldDrawWithin limits.sampleAttempts state value.c0 middle ∧
    FieldDrawWithin limits.sampleAttempts middle value.c1 final

def Seeded (limits : Limits) (params : Parameters) (final : Challenger) : Prop :=
  ∃ tagged, Observed limits {} "multi-stark/v0".toUTF8.data tagged ∧
    WordObservations 65536 limits
      [params.logBlowup, params.capHeight, params.logFinalPolyLen, params.maxLogArity,
        params.numQueries, params.commitPowBits, params.queryPowBits] tagged final

def BeforeLookup (limits : Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) (state final : Challenger) : Prop :=
  ∃ shapeState activeState preprocessedState mainState degreeState,
    WordObservations Ix.Ixby.goldilocksModulus limits key.shapeWords.toList state shapeState ∧
    WordObservations Ix.Ixby.goldilocksModulus limits
      (proof.active.toList.map (fun active => if active then 1 else 0)) shapeState activeState ∧
    CapObserved limits (key.preprocessed.getD #[]) activeState preprocessedState ∧
    CapObserved limits proof.commitments.stage1 preprocessedState mainState ∧
    WordObservations Ix.Ixby.goldilocksModulus limits
      (proof.logDegrees.toList.map (·.toNat)) mainState degreeState ∧
    ClaimsObserved limits claims degreeState final

def Prefix (limits : Limits) (key : Key) (claims : Array (Array Field)) (proof : Proof)
    (state : Challenger) (challenges : Challenges) (final : Challenger) : Prop :=
  ∃ start lookupState lookupObserved fingerprintState fingerprintObserved
      lookupCapState accumulatorState alphaState quotientState,
    BeforeLookup limits key claims proof state start ∧
    ExtensionDraw limits start challenges.lookup lookupState ∧
    ExtensionObserved limits challenges.lookup lookupState lookupObserved ∧
    ExtensionDraw limits lookupObserved challenges.fingerprint fingerprintState ∧
    ExtensionObserved limits challenges.fingerprint fingerprintState fingerprintObserved ∧
    CapObserved limits proof.commitments.stage2 fingerprintObserved lookupCapState ∧
    ExtensionsObserved limits proof.accumulators.toList lookupCapState accumulatorState ∧
    ExtensionDraw limits accumulatorState challenges.alpha alphaState ∧
    CapObserved limits proof.commitments.quotient alphaState quotientState ∧
    ExtensionDraw limits quotientState challenges.zeta final

def TranscriptPrefix (limits : Limits) (key : Key) (claims : Array (Array Field)) (proof : Proof)
    (challenges : Challenges) (final : Challenger) : Prop :=
  ∃ initial, Seeded limits key.params initial ∧ Prefix limits key claims proof initial challenges final

end MultiStark.Verify.Protocol
