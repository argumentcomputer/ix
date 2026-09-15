module
public import Ix.MultiStark.Verify.Pcs.Rounds
public import Ix.MultiStark.Verify.Fri

public section
@[expose] section

namespace MultiStark.Verify.Pcs

inductive CheckError where
  | rounds (error : Error)
  | transcript (error : Transcript.Error)
  | fri (error : Fri.Error)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Complete PCS authentication after the multi-stark transcript sampled ζ. -/
def check (limits : Fri.Limits) (key : Key) (proof : Proof) (zeta : Ext)
    (state : Transcript.Challenger) : Except CheckError (Fri.Challenges × Transcript.Challenger) := do
  let rounds ← (rounds key proof zeta).mapError CheckError.rounds
  let (_, state) ← ((observeOpenings limits.transcript rounds).run state).mapError CheckError.transcript
  (Fri.check limits key.params rounds proof.fri state).mapError CheckError.fri

end MultiStark.Verify.Pcs
