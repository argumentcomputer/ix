module
public import Ix.MultiStark.Verify.Source
public import Ix.MultiStark.Verify.Protocol.Check
public import Ix.MultiStark.Verify.Protocol.CodecKey
public import Ix.MultiStark.Verify.Protocol.CodecProof
public import Ix.MultiStark.Verify.Protocol.Claim

/-! The byte-facing source relation. The aggregate key comes from the fixed
configuration, C is public, and the native statement is derived by the exact
aggregate binding equations. Only proof material is a private input. The
relation does not approve a configuration, assert Ixon truth, or discharge
Stage 2/Flock/KZG soundness or compiler/reflection assumptions. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def Stage2ProtocolAcceptsClaim (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes) : Prop :=
  ∃ key proof,
    Wire.CanonicalKey config.decode config.aggregate.aggregateKey key ∧ KeyAdmissible key ∧
    Wire.CanonicalProof config.decode proofBytes proof ∧
    Stage2ProtocolAccepts config.verifier key #[NativeAggregateClaim config.aggregate claim] proof

def Stage2ProtocolAcceptsBytes (config : SourceConfig) (publicClaim proofBytes : Bytes) : Prop :=
  ∃ claim, Wire.CanonicalClosedClaim publicClaim claim ∧ Stage2ProtocolAcceptsClaim config claim proofBytes

end MultiStark.Verify.Protocol
