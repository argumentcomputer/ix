module
public import Ix.Aggr.Verification
public import Ix.Aggr.Backend
public import Ix.Store

public section
namespace Ix.Cli.Compression

@[extern "rs_compression_check_claim"]
opaque checkClaim (claim statement : @& ByteArray) : IO Unit

/-- Select development parameters when `devSrs` is set; otherwise require
the configured Filecoin cache. -/
@[extern "rs_compression_setup"]
opaque describeSetup (devSrs : Bool) : IO String

/-- Run every stage into the empty directory `dir`, reusing the fixed
preprocessing and development SRS caches under `cacheRoot`. -/
@[extern "rs_compression_run"]
opaque compress (vk proof claim statement : @& ByteArray) (dir cacheRoot : @& String)
  (devSrs : Bool) (logHeight : UInt32) : IO ByteArray

/-- Verify with the trusted Filecoin verifying key selected by the packet's id, whose
pinned aggregation program fixes the statement for `claim`, and return `"filecoin"`.
Needs neither the aggregation backend nor a GPU. -/
@[extern "rs_compression_verify"]
opaque verify (proof claim : @& ByteArray) : IO String

/-- Verify with an explicitly selected development key and a statement derived
independently from the aggregation backend. -/
@[extern "rs_compression_verify_development"]
opaque verifyDevelopment (proof claim statement verifyingKey : @& ByteArray) : IO Unit

/-- Caches shared by every compression run: fixed preprocessing keyed by
circuit and setup semantics, and development SRS files. -/
def cacheDir : IO System.FilePath := do
  return (← StoreIO.toIO Store.getHomeDir) / ".ix/compression/cache"

/-- Reserve a fresh run directory; concurrent or repeated runs never reuse
another run's checkpoints. `root?` supplies a hermetic root for tests. -/
def newRunDir (addr : Address) (height : Nat) (development : Bool)
    (root? : Option System.FilePath := none) : IO System.FilePath := do
  let root ← match root? with
    | some root => pure root
    | none => pure ((← StoreIO.toIO Store.getHomeDir) / ".ix/compression")
  let root := if development then root / "development" else root
  let parent := root / "runs" / toString addr / toString height
  IO.FS.createDirAll parent
  let pid ← IO.Process.getPID
  let stamp ← IO.monoNanosNow
  let dir := parent / s!"{pid}-{stamp}"
  IO.FS.createDir dir
  return dir

-- Reserve the family prefix, including unknown versions, so they fail closed.
def isCompressed (proof : ByteArray) : Bool :=
  proof.extract 0 5 == "IXCMP".toUTF8

/-- The key ID in a v4 compressed-proof envelope. It selects a development
cache entry; cryptographic verification still authenticates the selected key. -/
def verifyingKeyId (proof : ByteArray) : Except String Address := do
  let tag := ByteArray.mk #[73, 88, 67, 77, 80, 0, 0, 4]
  unless proof.extract 0 tag.size == tag do
    throw "unsupported compressed proof version"
  if proof.size < tag.size + 32 then
    throw "truncated compressed proof"
  return Address.mk (proof.extract tag.size (tag.size + 32))

/-- Development keys are addressed by key ID, independently of any run path.
Production verification never consults this directory. -/
def developmentKeyPath (proof : ByteArray)
    (root? : Option System.FilePath := none) : IO System.FilePath := do
  let id ← IO.ofExcept (verifyingKeyId proof)
  let root ← match root? with
    | some root => pure root
    | none => pure ((← StoreIO.toIO Store.getHomeDir) / ".ix/compression")
  return root / "development/verifying-keys" / s!"{id}.bin"

/-- Publish a development key only after checking its proof and independently
expected statement. Atomic replacement keeps readers from seeing partial keys. -/
def cacheDevelopmentKey (proof claim statement verifyingKey : ByteArray)
    (root? : Option System.FilePath := none) : IO System.FilePath := do
  verifyDevelopment proof claim statement verifyingKey
  let path ← developmentKeyPath proof root?
  IO.FS.createDirAll path.parent.get!
  let pid ← IO.Process.getPID
  let stamp ← IO.monoNanosNow
  let tmp := System.FilePath.mk s!"{path}.tmp.{pid}.{stamp}"
  IO.FS.writeBinFile tmp verifyingKey
  IO.FS.rename tmp path
  return path

def readDevelopmentKey (proof : ByteArray) : IO ByteArray := do
  let path ← developmentKeyPath proof
  unless (← path.pathExists) do
    throw <| IO.userError s!"development verifying key not found at {path}; generate it with ix compress --dev-srs or supply --dev-vk PATH"
  IO.FS.readBinFile path

def readProof (addr : Address) : IO Ixon.Proof := do
  let bytes ← StoreIO.toIO (Store.read addr)
  IO.ofExcept (Aggr.decodeAggregateWrapperAt addr bytes)

/-- The root statement a compressed proof of `claim` must expose: the public
claim of the backend's `ix_aggr` entrypoint, serialized as one batch claim. -/
def statementBytes (backend : Aggr.VerificationBackend) (claim : Ix.Claim) : ByteArray :=
  MultiStark.serializeClaims
    #[Aggr.aggregateOuterClaim backend.allowed backend.aggrIdx claim]

def verifyProof (addr : Address) (wrapper : Ixon.Proof) : IO UInt32 := do
  let claim := Ix.Claim.ser wrapper.claim
  let _ ← verify wrapper.proof claim
  IO.println s!"ok: proof {addr} verifies claim {Address.blake3 claim} under the Filecoin powers of tau"
  return 0

def verifyDevelopmentProof (addr : Address) (wrapper : Ixon.Proof)
    (verifyingKey : ByteArray) (backend : Aggr.VerificationBackend) : IO UInt32 := do
  let .checkEnv _ _ := wrapper.claim |
    throw <| IO.userError "development compression verification requires an aggregate CheckEnv claim"
  let claim := Ix.Claim.ser wrapper.claim
  verifyDevelopment wrapper.proof claim (statementBytes backend wrapper.claim) verifyingKey
  IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} (not production-secure)"
  return 0

end Ix.Cli.Compression
end
