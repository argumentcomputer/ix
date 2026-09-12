module
public import Ix.MultiStark.Verify.Check
public import Ix.MultiStark.Verify.Protocol.Check
public import Ix.MultiStark.Verify.Proofs.Pcs
public import Ix.MultiStark.Verify.Proofs.Ood

public section

namespace MultiStark.Verify.Proofs

theorem checkTyped_refines (limits : Fri.Limits) (key : Key) (claims : Array (Array Field)) (proof : Proof) :
    checkTyped limits key claims proof = .ok () ↔ Protocol.Stage2ProtocolAccepts limits key claims proof := by
  simp only [checkTyped, bind_ok_iff, mapError_ok_iff, shape_check_refines, Prod.exists,
    replay_refines, ood_check_refines, pcs_check_refines, pure_ok_iff, and_true,
    Protocol.Stage2ProtocolAccepts, exists_and_left]

theorem verifyTyped_refines (limits : Fri.Limits) (key : Key) (claims : Array (Array Field)) (proof : Proof) :
    verifyTyped limits key claims proof = true ↔ Protocol.Stage2ProtocolAccepts limits key claims proof :=
  (verifyTyped_iff limits key claims proof).trans (checkTyped_refines limits key claims proof)

/-- Deterministic implementation soundness, not cryptographic proof soundness. -/
theorem verifyTyped_sound (limits : Fri.Limits) (key : Key) (claims : Array (Array Field)) (proof : Proof)
    (accepted : verifyTyped limits key claims proof = true) : Protocol.Stage2ProtocolAccepts limits key claims proof :=
  (verifyTyped_refines limits key claims proof).mp accepted

/-- Complete for the explicitly admitted typed class and the SAME resource
limits, including sampling exhaustion. No unbounded-success premise is used. -/
theorem verifyTyped_complete (limits : Fri.Limits) (key : Key) (claims : Array (Array Field)) (proof : Proof)
    (supported : Protocol.Stage2ProtocolAccepts limits key claims proof) : verifyTyped limits key claims proof = true :=
  (verifyTyped_refines limits key claims proof).mpr supported

end MultiStark.Verify.Proofs
