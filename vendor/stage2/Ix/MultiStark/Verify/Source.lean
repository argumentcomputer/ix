module
public import Ix.MultiStark.Verify.Check
public import Ix.MultiStark.Verify.Codec
public import Ix.MultiStark.Verify.Claim

/-! The claim-bound source program to be compiled into IxBy. Configuration
is closed over by the approved guest (or checked against approved constants),
never a freely chosen private key. Configuration construction alone does not
approve an aggregate program's claim semantics or its security parameters.
The first adapter supports ONLY canonical closed CheckEnv claims. -/

public section
@[expose] section

namespace MultiStark.Verify

structure SourceConfig where
  aggregate : AggregateConfig
  decode : DecodeLimits := {}
  verifier : Fri.Limits := {}
  deriving BEq, Repr

inductive SourceError where
  | keyDecode (error : DecodeError)
  | keyShape (error : KeyError)
  | proofDecode (error : DecodeError)
  | check (error : CheckError)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The aggregate key used for verification is the SAME fixed bytes hashed
into the allowed-child identity. There is no proof-supplied expected claim,
allowed identity, entrypoint, or key override in this interface. -/
def checkClaim (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes) :
    Except SourceError Unit := do
  let key ← (Codec.decodeKey config.decode config.aggregate.aggregateKey).mapError SourceError.keyDecode
  (validateKey key.value).mapError SourceError.keyShape
  let proof ← (Codec.decodeProof config.decode proofBytes).mapError SourceError.proofDecode
  (checkTyped config.verifier key.value #[config.aggregate.expectedClaim claim] proof.value).mapError SourceError.check

def stage2Verify (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes) : Bool :=
  (checkClaim config claim proofBytes).isOk

/-- The public claim is returned only on successful claim-bound verification.
The explicit target result ABI maps `some C` to canonical C bytes and `none`
to the erased value; no default Lean Option constructor layout is assumed. -/
def claimWrapper (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes) : Option ClosedCheckEnv :=
  if stage2Verify config claim proofBytes then some claim else none

/-- Pure canonical public transport boundary. Wrong kinds, assumptions,
trailing bytes, and malformed roots fail before proof verification. -/
def stage2VerifyBytes (config : SourceConfig) (publicClaim proofBytes : Bytes) : Bool :=
  match decodeClosedCheckEnv publicClaim with
  | .error _ => false
  | .ok claim => stage2Verify config claim.value proofBytes

def claimBytesWrapper (config : SourceConfig) (publicClaim proofBytes : Bytes) : Option Bytes :=
  if stage2VerifyBytes config publicClaim proofBytes then some publicClaim else none

theorem stage2Verify_iff (config : SourceConfig) (claim : ClosedCheckEnv) (proofBytes : Bytes) :
    stage2Verify config claim proofBytes = true ↔ checkClaim config claim proofBytes = .ok () := by
  unfold stage2Verify
  cases checkClaim config claim proofBytes with
  | error error => simp [Except.isOk, Except.toBool]
  | ok result => cases result; simp [Except.isOk, Except.toBool]

theorem claimWrapper_some_iff (config : SourceConfig) (claim output : ClosedCheckEnv) (proofBytes : Bytes) :
    claimWrapper config claim proofBytes = some output ↔
      output = claim ∧ stage2Verify config claim proofBytes = true := by
  unfold claimWrapper
  split
  · rename_i accepted
    constructor
    · intro equal; exact ⟨(Option.some.inj equal).symm, accepted⟩
    · rintro ⟨rfl, _⟩; rfl
  · rename_i rejected
    constructor
    · intro equal; cases equal
    · intro both; exact False.elim (rejected both.2)

theorem claimBytesWrapper_some_iff (config : SourceConfig) (publicClaim output proofBytes : Bytes) :
    claimBytesWrapper config publicClaim proofBytes = some output ↔
      output = publicClaim ∧ stage2VerifyBytes config publicClaim proofBytes = true := by
  unfold claimBytesWrapper
  split
  · rename_i accepted
    constructor
    · intro equal; exact ⟨(Option.some.inj equal).symm, accepted⟩
    · rintro ⟨rfl, _⟩; rfl
  · rename_i rejected
    constructor
    · intro equal; cases equal
    · intro both; exact False.elim (rejected both.2)

/-- Success retains the canonical public bytes AND the typed claim whose
expected native statement was checked. This theorem does not assert the
cryptographic truth of that statement or approve the configuration. -/
theorem stage2VerifyBytes_binding (config : SourceConfig) (publicClaim proofBytes : Bytes)
    (accepted : stage2VerifyBytes config publicClaim proofBytes = true) :
    ∃ claim : ClosedCheckEnv, claim.bytes = publicClaim ∧ stage2Verify config claim proofBytes = true := by
  cases decoded : decodeClosedCheckEnv publicClaim with
  | error error => simp [stage2VerifyBytes, decoded] at accepted
  | ok checked =>
    refine ⟨checked.value, Except.ok.inj checked.encoded, ?_⟩
    simpa only [stage2VerifyBytes, decoded] using accepted

end MultiStark.Verify
