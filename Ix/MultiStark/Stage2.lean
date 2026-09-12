module
public import Ix.MultiStark.Verify.Source
public import Ix.Claim

/-! Public typed Ixon adapter to the pure source verifier. This explicit host
import is NOT in `Ix.MultiStark.Verify`: production `Ix.Claim` transitively
imports native hashing. Neither host serialization nor this adapter is used
as a guest-side verifier oracle or a protocol-refinement proof. -/

public section
@[expose] section

namespace MultiStark.Stage2

/-- The original typed claim must be closed and have a 32-byte root before
serialization. The source then repeats canonical byte admission itself. -/
def stage2Verify (config : Verify.SourceConfig) (claim : Ix.Claim) (proofBytes : ByteArray) : Bool :=
  match claim with
  | .checkEnv root none =>
    root.hash.size == 32 && Verify.stage2VerifyBytes config (Ix.Claim.ser claim).data proofBytes.data
  | _ => false

def claimWrapper (config : Verify.SourceConfig) (claim : Ix.Claim) (proofBytes : ByteArray) : Option Ix.Claim :=
  if stage2Verify config claim proofBytes then some claim else none

end MultiStark.Stage2
