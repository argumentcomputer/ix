module
public import Ix.MultiStark.Verify.Protocol.Wire
public import Ix.MultiStark.Verify.Claim
public import Ix.MultiStark.Verify.Codec.Claims

/-! Public closed-CheckEnv framing and the current native aggregate statement.
The caller supplies C publicly. Both keys and entrypoints occur in the
allowed-identity preimage; the public claim bytes occur in the claim preimage.
Hash binding/aggregate-program truth remain explicit cryptographic/policy
obligations, not consequences of these deterministic byte equations. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

def ClosedClaimBytes (claim : ClosedCheckEnv) : Bytes := #[0xe5] ++ claim.root.bytes ++ #[0]

def AllowedIdentityBytes (config : AggregateConfig) : Bytes :=
  Ix.Ixby.Blake3.hash config.ixvmKey ++ Wire.LittleEndianBytes 8 config.verifyClaimEntry.val ++
    Ix.Ixby.Blake3.hash config.aggregateKey ++ Wire.LittleEndianBytes 8 config.aggregateEntry.val

def DigestWords (digest : Digest) : Array Field :=
  (Array.range 8).map fun index => Ix.Ixby.Goldilocks.reduce
    (Wire.LittleEndianValue (digest.bytes.extract (4 * index) (4 * index + 4)).toList)

def NativeAggregateClaim (config : AggregateConfig) (claim : ClosedCheckEnv) : Array Field :=
  #[0, config.aggregateEntry] ++
    DigestWords ⟨Ix.Ixby.Blake3.hash (AllowedIdentityBytes config), Ix.Ixby.Blake3.hash_size _⟩ ++
    DigestWords ⟨Ix.Ixby.Blake3.hash (ClosedClaimBytes claim), Ix.Ixby.Blake3.hash_size _⟩

namespace Wire

def ClosedClaimRead (state : Codec.Wire.ReadState) (value : ClosedCheckEnv) (final : Codec.Wire.ReadState) : Prop :=
  ∃ first second, ByteRead state 0xe5 first ∧ DigestRead first value.root second ∧ ByteRead second 0 final

def CanonicalClosedClaim (bytes : Bytes) (value : ClosedCheckEnv) : Prop :=
  Decoded { bytes := 34, vector := 0, items := 0 } bytes ClosedClaimRead value ∧ ClosedClaimBytes value = bytes

def ClaimsRead : ReadRel (Array (Array Field)) := VectorRead 8 (VectorRead 8 FieldRead)
def ClaimsWritten : WriteRel (Array (Array Field)) := VectorWritten 8 (VectorWritten 8 FieldWritten)

def CanonicalClaims (limits : DecodeLimits) (bytes : Bytes) (value : Array (Array Field)) : Prop :=
  Decoded limits bytes ClaimsRead value ∧ Written limits (ClaimsWritten value) bytes

end Wire
end MultiStark.Verify.Protocol
