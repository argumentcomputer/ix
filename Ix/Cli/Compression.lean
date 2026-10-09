module
public import Ix.Aggr.Verification
public import Ix.Store

public section
namespace Ix.Cli.Compression

@[extern "rs_compression_check_claim"]
opaque checkClaim (claim : @& ByteArray) : IO Unit

@[extern "rs_compression_worker"]
opaque worker (json : @& String) : IO Unit

@[extern "rs_compression_run"]
opaque compress (vk proof claim : @& ByteArray) (dir registry : @& String)
  (resume resident : Bool) (logHeight : UInt32) : IO ByteArray

@[extern "rs_compression_verify"]
opaque verify (dir : @& String) (proof claim : @& ByteArray) : IO Unit

@[extern "rs_compression_import_verifier"]
opaque importVerifier (file digest registry : @& String) : IO String

def registryDir : IO System.FilePath := do
  return (← StoreIO.toIO Store.getHomeDir) / ".ix/verifiers"

-- Reserve the family prefix, including unknown versions, so they fail closed.
def isCompressed (proof : ByteArray) : Bool :=
  proof.extract 0 5 == "IXCMP".toUTF8

def readProof (addr : Address) : IO Ixon.Proof := do
  let bytes ← StoreIO.toIO (Store.read addr)
  IO.ofExcept (Aggr.decodeAggregateWrapperAt addr bytes)

def verifyProof (addr : Address) (wrapper : Ixon.Proof)
    (devSrs : Bool) : IO UInt32 := do
  unless devSrs do
    throw <| IO.userError "compressed proofs currently use a known-trapdoor development SRS; --dev-srs is required (not production-secure)"
  verify (← registryDir).toString wrapper.proof (Ix.Claim.ser wrapper.claim)
  IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 (Ix.Claim.ser wrapper.claim)} (not production-secure)"
  return 0

end Ix.Cli.Compression
end
