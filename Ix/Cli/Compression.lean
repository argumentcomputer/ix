module
public import Ix.Aggr.Verification
public import Ix.Aggr.Backend
public import Ix.Store

public section
namespace Ix.Cli.Compression

@[extern "rs_compression_check_claim"]
opaque checkClaim (claim statement : @& ByteArray) : IO Unit

/-- Describe the setup a new run proves under: the configured Filecoin cache,
or the development setup when `devSrs` allows it. Fails when neither applies. -/
@[extern "rs_compression_setup"]
opaque describeSetup (devSrs : Bool) : IO String

/-- Run every stage into the empty directory `dir`, reusing the fixed
preprocessing and development SRS caches under `cacheRoot`. -/
@[extern "rs_compression_run"]
opaque compress (vk proof claim statement : @& ByteArray) (dir cacheRoot : @& String)
  (devSrs : Bool) (logHeight : UInt32) : IO ByteArray

/-- Verify with the profile bundled under the packet's id, whose pinned
aggregation program fixes the statement for `claim`, and return the setup
class: `"filecoin"` or `"development"`. Development proofs need `devSrs`.
Needs neither the aggregation backend nor a GPU. -/
@[extern "rs_compression_verify"]
opaque verify (proof claim : @& ByteArray) (devSrs : Bool) : IO String

/-- Caches shared by every compression run: fixed preprocessing keyed by the
executable and profile, and development SRS files. -/
def cacheDir : IO System.FilePath := do
  return (← StoreIO.toIO Store.getHomeDir) / ".ix/compression/cache"

-- Reserve the family prefix, including unknown versions, so they fail closed.
def isCompressed (proof : ByteArray) : Bool :=
  proof.extract 0 5 == "IXCMP".toUTF8

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
  if setup == "development" then
    IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} (not production-secure)"
  else
    IO.println s!"ok: proof {addr} verifies claim {Address.blake3 claim} under the Filecoin powers of tau"
  return 0

end Ix.Cli.Compression
end
