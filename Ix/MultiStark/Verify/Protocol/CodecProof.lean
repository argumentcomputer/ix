module
public import Ix.MultiStark.Verify.Protocol.Wire
public import Ix.MultiStark.Verify.Codec.Proof

/-! The current shared-multiproof wire grammar. Every vector length is a
fixed little-endian u64; every extension uses c0 then c1. The canonical
admitted class must satisfy both the consuming read grammar and the bounded
write grammar for the SAME bytes. There is no legacy transport alternative. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol.Wire

def CapRead : ReadRel MerkleCap := VectorRead 8 DigestRead
def RoundRead : ReadRel OpenedRound := VectorRead 8 (VectorRead 8 (VectorRead 8 ExtRead))
def BatchValuesRead : ReadRel (Array (Array (Array Field))) := VectorRead 8 (VectorRead 8 (VectorRead 8 FieldRead))
def SiblingsRead : ReadRel (Array (Array Ext)) := VectorRead 8 (VectorRead 8 ExtRead)

def CommitmentsRead (state : Codec.Wire.ReadState) (value : Commitments) (final : Codec.Wire.ReadState) : Prop :=
  ∃ first second, CapRead state value.stage1 first ∧ CapRead first value.stage2 second ∧ CapRead second value.quotient final

def BatchOpeningRead (state : Codec.Wire.ReadState) (value : BatchOpening) (final : Codec.Wire.ReadState) : Prop :=
  ∃ middle, BatchValuesRead state value.values middle ∧ CapRead middle value.frontier final

def CommitPhaseStepRead (state : Codec.Wire.ReadState) (value : CommitPhaseStep) (final : Codec.Wire.ReadState) : Prop :=
  ∃ first second, ByteRead state value.logArity first ∧ SiblingsRead first value.siblings second ∧ CapRead second value.frontier final

def FriRead (state : Codec.Wire.ReadState) (value : FriProof) (final : Codec.Wire.ReadState) : Prop :=
  ∃ s1 s2 s3 s4 s5,
    VectorRead 8 CapRead state value.commits s1 ∧ VectorRead 8 FieldRead s1 value.commitPow s2 ∧
    VectorRead 8 BatchOpeningRead s2 value.inputOpenings s3 ∧ VectorRead 8 CommitPhaseStepRead s3 value.commitOpenings s4 ∧
    VectorRead 8 ExtRead s4 value.finalPoly s5 ∧ FieldRead s5 value.queryPow final

def ProofRead (state : Codec.Wire.ReadState) (value : Proof) (final : Codec.Wire.ReadState) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6 s7 s8,
    VectorRead 8 BoolRead state value.active s1 ∧ CommitmentsRead s1 value.commitments s2 ∧
    VectorRead 8 ExtRead s2 value.accumulators s3 ∧ VectorRead 8 ByteRead s3 value.logDegrees s4 ∧
    FriRead s4 value.fri s5 ∧ RoundRead s5 value.quotient s6 ∧ OptionRead RoundRead s6 value.preprocessed s7 ∧
    RoundRead s7 value.stage1 s8 ∧ RoundRead s8 value.stage2 final

def CapWritten : WriteRel MerkleCap := VectorWritten 8 DigestWritten
def RoundWritten : WriteRel OpenedRound := VectorWritten 8 (VectorWritten 8 (VectorWritten 8 ExtWritten))
def BatchValuesWritten : WriteRel (Array (Array (Array Field))) := VectorWritten 8 (VectorWritten 8 (VectorWritten 8 FieldWritten))
def SiblingsWritten : WriteRel (Array (Array Ext)) := VectorWritten 8 (VectorWritten 8 ExtWritten)

def CommitmentsWritten (value : Commitments) (state final : Codec.Wire.WriteState) : Prop :=
  ∃ first second, CapWritten value.stage1 state first ∧ CapWritten value.stage2 first second ∧ CapWritten value.quotient second final

def BatchOpeningWritten (value : BatchOpening) (state final : Codec.Wire.WriteState) : Prop :=
  ∃ middle, BatchValuesWritten value.values state middle ∧ CapWritten value.frontier middle final

def CommitPhaseStepWritten (value : CommitPhaseStep) (state final : Codec.Wire.WriteState) : Prop :=
  ∃ first second, ByteWritten value.logArity state first ∧ SiblingsWritten value.siblings first second ∧ CapWritten value.frontier second final

def FriWritten (value : FriProof) (state final : Codec.Wire.WriteState) : Prop :=
  ∃ s1 s2 s3 s4 s5,
    VectorWritten 8 CapWritten value.commits state s1 ∧ VectorWritten 8 FieldWritten value.commitPow s1 s2 ∧
    VectorWritten 8 BatchOpeningWritten value.inputOpenings s2 s3 ∧ VectorWritten 8 CommitPhaseStepWritten value.commitOpenings s3 s4 ∧
    VectorWritten 8 ExtWritten value.finalPoly s4 s5 ∧ FieldWritten value.queryPow s5 final

def ProofWritten (value : Proof) (state final : Codec.Wire.WriteState) : Prop :=
  ∃ s1 s2 s3 s4 s5 s6 s7 s8,
    VectorWritten 8 BoolWritten value.active state s1 ∧ CommitmentsWritten value.commitments s1 s2 ∧
    VectorWritten 8 ExtWritten value.accumulators s2 s3 ∧ VectorWritten 8 ByteWritten value.logDegrees s3 s4 ∧
    FriWritten value.fri s4 s5 ∧ RoundWritten value.quotient s5 s6 ∧ OptionWritten RoundWritten value.preprocessed s6 s7 ∧
    RoundWritten value.stage1 s7 s8 ∧ RoundWritten value.stage2 s8 final

def CanonicalProof (limits : DecodeLimits) (bytes : Bytes) (value : Proof) : Prop :=
  Decoded limits bytes ProofRead value ∧ Written limits (ProofWritten value) bytes

end MultiStark.Verify.Protocol.Wire
