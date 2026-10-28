module
public import Ix.Aggr.Verification
public import Ix.Aggr.Backend
public import Ix.Store

public section
namespace Ix.Cli.Compression

@[extern "rs_compression_check_claim"]
opaque checkClaim (claim statement : @& ByteArray) : IO Unit

/-- The KZG curve compiled into this executable: `"bn254"`. -/
@[extern "rs_compression_curve"]
opaque curve : IO String

/-- Select development parameters when `devSrs` is set; otherwise require
authenticated production parameters for the compiled curve. -/
@[extern "rs_compression_setup"]
opaque describeSetup (devSrs : Bool) : IO String

/-- Run every stage into the empty directory `dir`, reusing the fixed
preprocessing and development SRS caches under `cacheRoot`. -/
@[extern "rs_compression_run"]
opaque compress (vk proof claim statement : @& ByteArray) (dir cacheRoot : @& String)
  (devSrs : Bool) (logHeight : UInt32) (terminalPlonk : Bool) : IO ByteArray

/-- Verify with the verifying key compiled in under the packet's id, whose pinned
aggregation program fixes the statement for `claim`, and return the setup
class: `"ignition"` or `"development"`. Development proofs need
`devSrs`.
Needs neither the aggregation backend nor a GPU. -/
@[extern "rs_compression_verify"]
opaque verify (proof claim : @& ByteArray) (devSrs : Bool) : IO String

/-- Caches shared by every compression run: fixed preprocessing keyed by the
executable and verifying key, and development SRS files. -/
def cacheDir : IO System.FilePath := do
  return (← StoreIO.toIO Store.getHomeDir) / ".ix/compression/cache"

-- Reserve the family prefix, including unknown versions, so they fail closed.
def isCompressed (proof : ByteArray) : Bool :=
  proof.extract 0 5 == "IXCMP".toUTF8 || proof.extract 0 4 == "IXBN".toUTF8

def readProof (addr : Address) : IO Ixon.Proof := do
  let bytes ← StoreIO.toIO (Store.read addr)
  IO.ofExcept (Aggr.decodeAggregateWrapperAt addr bytes)

/-- The root statement a compressed proof of `claim` must expose: the public
claim of the backend's `ix_aggr` entrypoint, serialized as one batch claim. -/
def statementBytes (backend : Aggr.VerificationBackend) (claim : Ix.Claim) : ByteArray :=
  MultiStark.serializeClaims
    #[Aggr.aggregateOuterClaim backend.allowed backend.aggrIdx claim]

def verifyProof (addr : Address) (wrapper : Ixon.Proof) (devSrs : Bool) : IO UInt32 := do
  let claim := Ix.Claim.ser wrapper.claim
  let setup ← verify wrapper.proof claim devSrs
  match setup with
  | "development" =>
    IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} (not production-secure)"
  | "ignition" =>
    IO.println s!"ok: proof {addr} verifies claim {Address.blake3 claim} under the Aztec Ignition powers of tau"
  | _ =>
    throw <| IO.userError s!"unsupported compression setup: {setup}"
  return 0

end Ix.Cli.Compression
end
