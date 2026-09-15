module
public import Ix.MultiStark.Verify.Protocol.Pcs
public import Ix.MultiStark.Verify.Protocol.Ood

/-! The complete deterministic relation on typed Stage 2 data. There is no
reference to an executable acceptance bit: the admitted shape, Fiat-Shamir
states, OOD equations, and authenticated PCS/FRI openings must all hold for
the same key, expected claims, and proof. Byte decoding and application key/
claim approval are separate boundaries, as are cryptographic assumptions. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def Stage2ProtocolAccepts (limits : Fri.Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) : Prop :=
  ∃ values challenges state evaluations friChallenges final,
    ShapeAccepted key proof values ∧ TranscriptPrefix limits.transcript key claims proof challenges state ∧
    OodAccepted challenges claims values proof.accumulators evaluations ∧
    PcsAccepted limits key proof challenges.zeta state friChallenges final

end MultiStark.Verify.Protocol
