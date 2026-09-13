module
public import Ix.MultiStark.Verify.Transcript
public import Ix.MultiStark.Verify.Ood
public import Ix.MultiStark.Verify.Pcs

/-! Complete pure deterministic protocol checking on typed native data.
The caller owns the expected native claims and key. Public Ixon applications
must use the claim-bound source wrapper, not accept privately chosen claims.
The independent typed protocol refinement is in `Proofs.Check`; composing
executable phases alone is not that proof. Byte decoding, application policy,
and cryptographic soundness remain separate obligations. -/

public section
@[expose] section

namespace MultiStark.Verify

inductive CheckError where
  | shape (error : Shape.Error)
  | transcript (error : Transcript.Error)
  | ood (error : Ood.Error)
  | pcs (error : Pcs.CheckError)
  deriving BEq, DecidableEq, Repr, Inhabited

def checkTyped (limits : Fri.Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) : Except CheckError Unit := do
  let values ← (Shape.check key proof).mapError CheckError.shape
  let (challenges, state) ← (Transcript.replay limits.transcript key claims proof).mapError CheckError.transcript
  let _ ← (Ood.check challenges claims values proof.accumulators).mapError CheckError.ood
  let _ ← (Pcs.check limits key proof challenges.zeta state).mapError CheckError.pcs
  return ()

def verifyTyped (limits : Fri.Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) : Bool := (checkTyped limits key claims proof).isOk

/-- Boolean success is exactly a successful complete typed check, not a
separate host acceptance hook. This is plumbing, not protocol refinement. -/
theorem verifyTyped_iff (limits : Fri.Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) : verifyTyped limits key claims proof = true ↔
      checkTyped limits key claims proof = .ok () := by
  unfold verifyTyped
  cases checkTyped limits key claims proof with
  | error error => simp [Except.isOk, Except.toBool]
  | ok result => cases result; simp [Except.isOk, Except.toBool]

end MultiStark.Verify
