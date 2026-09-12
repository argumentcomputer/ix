module
public import Ix.MultiStark.Verify.Codec.Wire
public import Ix.Ixby.Blake3

/-! Pure claim-to-native-statement binding for closed aggregate roots.
This is a source-verifier component, not proof verification. The public Ixon
adapter checks the same canonical bytes outside the pure implementation. -/

public section
@[expose] section

namespace MultiStark.Verify

structure ClosedCheckEnv where
  root : Digest
  deriving BEq, DecidableEq, Repr

/-- Exactly the production Ixon serialization of `.checkEnv root none`.
The type does not permit erasing another claim kind or an assumption set. -/
def ClosedCheckEnv.bytes (claim : ClosedCheckEnv) : Bytes :=
  #[0xe5] ++ claim.root.bytes ++ #[0]

theorem ClosedCheckEnv.bytes_size (claim : ClosedCheckEnv) : claim.bytes.size = 34 := by
  simp [ClosedCheckEnv.bytes, claim.root.size]

def decodeClosedCheckEnv (bytes : Bytes) :
    Except DecodeError (Codec.Canonical (fun claim : ClosedCheckEnv => .ok claim.bytes) bytes) := do
  let claim ← Codec.Wire.decode { bytes := 34, vector := 0, items := 0 } bytes do
    unless (← Codec.Wire.readByte) == 0xe5 do throw .tag
    let root ← Codec.Wire.readDigest
    unless (← Codec.Wire.readByte) == 0 do throw .tag
    return ClosedCheckEnv.mk root
  Codec.Wire.canonicalize (fun claim => .ok claim.bytes) bytes claim

/-- Policy data owned by the application. Constructing this record does not
certify its approval or its key codecs. The approved guest must close over
these exact values, or enforce their approved digest inside the guest. -/
structure AggregateConfig where
  ixvmKey : Bytes
  verifyClaimEntry : Field
  aggregateKey : Bytes
  aggregateEntry : Field
  deriving BEq, DecidableEq, Repr

def hash (bytes : Bytes) : Digest :=
  ⟨Ix.Ixby.Blake3.hash bytes, Ix.Ixby.Blake3.hash_size bytes⟩

/-- The current 80-byte allowed-child identity, including both keys and both
entry points. Native Stage 2 is verified under `aggregateKey`, not a private
key supplied by the proof. -/
def AggregateConfig.allowedIdentity (config : AggregateConfig) : Bytes :=
  (hash config.ixvmKey).bytes ++ Codec.Wire.littleEndian 8 config.verifyClaimEntry.val ++
    (hash config.aggregateKey).bytes ++ Codec.Wire.littleEndian 8 config.aggregateEntry.val

theorem AggregateConfig.allowedIdentity_size (config : AggregateConfig) :
    config.allowedIdentity.size = 80 := by
  simp [AggregateConfig.allowedIdentity, hash, Ix.Ixby.Blake3.hash_size,
    Codec.Wire.littleEndian]

/-- Four digest bytes per Goldilocks word, little-endian, in digest order.
No 256-bit digest is reduced to one field element. -/
def packDigest (digest : Digest) : Array Field :=
  (Array.range 8).map fun i => Ix.Ixby.Goldilocks.reduce
    (Codec.Wire.fromLittleEndian (digest.bytes.extract (4 * i) (4 * i + 4)))

theorem packDigest_size (digest : Digest) : (packDigest digest).size = 8 := by
  simp [packDigest]

/-- Exact 18-word native aggregate claim:
`[function-channel=0, aggregate-entry, hash(allowed)[8], hash(public-C)[8]]`.
The two digest preimages and both key/entry pairs are source-side data, not
facts obtained from a host parser or native verifier. -/
def AggregateConfig.expectedClaim (config : AggregateConfig) (claim : ClosedCheckEnv) : Array Field :=
  #[0, config.aggregateEntry] ++ packDigest (hash config.allowedIdentity) ++
    packDigest (hash claim.bytes)

theorem AggregateConfig.expectedClaim_size (config : AggregateConfig) (claim : ClosedCheckEnv) :
    (config.expectedClaim claim).size = 18 := by
  simp [AggregateConfig.expectedClaim, packDigest_size]

end MultiStark.Verify
