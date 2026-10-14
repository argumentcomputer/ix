module
public import Ix.Aggr.Verification
public import Ix.Store

public section
namespace Ix.Cli.Compression

@[extern "rs_compression_check_claim"]
opaque checkClaim (claim : @& ByteArray) : IO Unit

@[extern "rs_compression_worker"]
opaque worker (json : @& String) : IO Unit

/-- Describe the setup a new run proves under: the configured Filecoin cache,
or the development setup when `devSrs` allows it. Fails when neither applies. -/
@[extern "rs_compression_setup"]
opaque describeSetup (devSrs : Bool) : IO String

@[extern "rs_compression_run"]
opaque compress (vk proof claim : @& ByteArray) (dir registry : @& String)
  (resume resident devSrs : Bool) (logHeight : UInt32) : IO ByteArray

/-- Verify and return the setup class the proof was made under:
`"filecoin"` or `"development"`. Development proofs need `devSrs`. -/
@[extern "rs_compression_verify"]
opaque verify (dir : @& String) (proof claim : @& ByteArray) (devSrs : Bool) : IO String

/-- Register a verifier and return its setup class and profile id, separated by
a space. Development verifiers need `devSrs`. -/
@[extern "rs_compression_import_verifier"]
opaque importVerifier (file digest registry : @& String) (devSrs : Bool) : IO String

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
  let claim := Ix.Claim.ser wrapper.claim
  let setup ← verify (← registryDir).toString wrapper.proof claim devSrs
  if setup == "development" then
    IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} (not production-secure)"
  else
    IO.println s!"ok: proof {addr} verifies claim {Address.blake3 claim} under the Filecoin powers of tau"
  return 0

end Ix.Cli.Compression
end
