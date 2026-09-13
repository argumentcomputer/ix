module
public import Ix.MultiStark.Verify.Transcript.Basic

/-! The Stage 2 Fiat-Shamir prefix up to and including OOD zeta. Shape,
activation, all claims and all commitments are observed in native order.
The returned state is the continuation used by the PCS/FRI verifier. -/

public section
@[expose] section

namespace MultiStark.Verify.Transcript

structure Challenges where
  lookup : Ext
  fingerprint : Ext
  alpha : Ext
  zeta : Ext
  deriving BEq, DecidableEq, Repr

def observeClaimList (limits : Limits) : List (Array Field) → Action Unit
  | [] => pure ()
  | claim :: rest => do
    observeNat limits claim.size
    observeFields limits claim
    observeClaimList limits rest

def observeClaims (limits : Limits) (claims : Array (Array Field)) : Action Unit := do
  observeNat limits claims.size
  observeClaimList limits claims.toList

def beforeLookup (limits : Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) : Action Unit := do
  observeNats limits key.shapeWords.toList
  observeNats limits (proof.active.toList.map (fun active => if active then 1 else 0))
  observeCap limits (key.preprocessed.getD #[])
  observeCap limits proof.commitments.stage1
  observeNats limits (proof.logDegrees.toList.map (·.toNat))
  observeClaims limits claims

def prefixReplay (limits : Limits) (key : Key) (claims : Array (Array Field))
    (proof : Proof) : Action Challenges := do
  beforeLookup limits key claims proof
  let lookup ← sampleExt limits
  observeExt limits lookup
  let fingerprint ← sampleExt limits
  observeExt limits fingerprint
  observeCap limits proof.commitments.stage2
  observeExts limits proof.accumulators.toList
  let alpha ← sampleExt limits
  observeCap limits proof.commitments.quotient
  let zeta ← sampleExt limits
  return { lookup, fingerprint, alpha, zeta }

def replay (limits : Limits) (key : Key) (claims : Array (Array Field)) (proof : Proof) :
    Except Error (Challenges × Challenger) := do
  let initial ← seed limits key.params
  (prefixReplay limits key claims proof).run initial

end MultiStark.Verify.Transcript
