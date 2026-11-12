module
public import Ix.Aggr.Verification
public import Ix.Store

public section
namespace Ix.Cli.Compression

@[extern "rs_compression_check_claim"]
opaque checkClaim (claim statement : @& ByteArray) : IO Unit

/-- The KZG curve compiled into this executable: `"bn254"`. -/
@[extern "rs_compression_curve"]
opaque curve : IO String

/-- Describe the inner KZG setup and validate the independent final-setup
selection. Development inner KZG needs development keys for a final proof. -/
@[extern "rs_compression_setup"]
opaque describeSetup (devKzgSrs devFinalSrs : Bool) (finalProof : UInt8) : IO String

/-- Run the stages in `dir`, resuming checked proofs unless `fresh` replaces
them. Fixed preprocessing, parameters and proving keys under `cacheRoot`
remain reusable. A nonempty `fixedRoot` is the layout (`.ixl` bytes) of `proof`. -/
@[extern "rs_compression_run"]
opaque compress (vk proof claim statement fixedRoot : @& ByteArray) (dir cacheRoot : @& String)
  (devKzgSrs devFinalSrs : Bool) (finalProof : UInt8) (fresh : Bool := false) : IO ByteArray

/-- The versioned normalization layout (`.ixl` bytes) for the aggregation
backend's key. -/
@[extern "rs_compression_release_root_layout"]
opaque releaseRootLayout (vk : @& ByteArray) : IO ByteArray

/-- Check that `statement` belongs to `claim` and to the aggregation backend the
bundled verifying keys were derived for, as the default verifier requires. -/
@[extern "rs_compression_check_release_statement"]
opaque checkReleaseStatement (claim statement : @& ByteArray) : IO Unit

/-- Per-circuit rows of one root wrap execution of `rawProof`, as a JSON array.
`invocation` is in Ixon (`Ix.AiurInvocation`). -/
@[extern "rs_compression_root_rows"]
opaque rootRows (aggrArtifact : @& String) (invocation : @& ByteArray)
  (rawProof : @& ByteArray) : IO String

/-- The fixed root layout (`.ixl` bytes) holding every row-count array in the JSON array
`rows`, with `headroom` extra doublings per circuit. -/
@[extern "rs_compression_root_layout"]
opaque rootLayout (aggrArtifact rows : @& String)
  (headroom claimLen : UInt32) : IO ByteArray

/-- Wrap the aggregate root `rawProof` once more and prove the wrap in the fixed
shape of `layout`; returns the normalized proof bytes. -/
@[extern "rs_compression_normalize_root"]
opaque normalizeRoot (aggrArtifact : @& String) (invocation : @& ByteArray)
  (rawProof layout : @& ByteArray) : IO ByteArray

/-- Write the FRI worker's root input directory `dir` without compressing. -/
@[extern "rs_compression_write_root"]
opaque writeRoot (vk proof claim statement fixedRoot : @& ByteArray) (dir : @& String) : IO Unit

/-- Verify a compressed proof under the bundled release keys. Development
proofs require `devSrs`; verification needs no proving setup or GPU. -/
@[extern "rs_compression_verify"]
opaque verify (proof claim : @& ByteArray) (devSrs : Bool) : IO String

/-- Verify a final development proof with the caller's independent bundle pin.
The proof itself cannot authorize its key or a different circuit. -/
@[extern "rs_compression_verify_development"]
opaque verifyDevelopment (proof claim bundle : @& ByteArray)
  (trustedDigest : @& String) (devSrs : Bool) : IO String

/-- Check the Ignition SRS against its pin and publish the fixed
preprocessing of every stage of the bundled version for the aggregation
backend `vk` to the fixed cache under `cacheRoot`; with `plonk`, also build
the PLONK cache. Present entries are only checked. -/
@[extern "rs_compression_prepare"]
opaque prepare (vk : @& ByteArray) (cacheRoot : @& String) (devKzgSrs plonk : Bool) : IO Unit

/-- Return the GPU memory this process's Aiur prover retains between proofs to
the driver. The compression worker is another process and cannot reuse it. -/
@[extern "rs_compression_release_gpu_memory"]
opaque releaseGpuMemory : IO Unit

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

/-- A 64-character content address loads from the store; other inputs are
serialized proof-wrapper files. Prefix a hexadecimal filename with `./` to
select it as a path. File inputs do not require a store entry. -/
def readProofInput (input : String) : IO (Address × Ixon.Proof) := do
  if let some addr := Address.fromString input then
    return (addr, ← readProof addr)
  let bytes ← IO.FS.readBinFile input
  let addr := Address.blake3 bytes
  let wrapper ← IO.ofExcept (Aggr.decodeAggregateWrapperAt addr bytes)
  return (addr, wrapper)

/-- Verify the compressed proof `wrapper`, stored at `addr`, and print what its
claim states: `statement`, the claim's kind, subject and conditions
(`Ix.Cli.ClaimPolicy.statement`). -/
def verifyProof (addr : Address) (wrapper : Ixon.Proof) (devSrs : Bool) (statement : String) :
    IO UInt32 := do
  let claim := Ix.Claim.ser wrapper.claim
  let setup ← verify wrapper.proof claim devSrs
  match setup with
  | "development" =>
    IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} (not production-secure)"
  | "ignition" =>
    IO.println s!"ok: proof {addr} verifies claim {Address.blake3 claim} under the Aztec Ignition powers of tau"
  | "groth16" =>
    IO.println s!"ok: Groth16 proof {addr} verifies claim {Address.blake3 claim} under the admitted circuit-specific setup"
  | _ =>
    throw <| IO.userError s!"unsupported compression setup: {setup}"
  IO.println statement
  return 0

end Ix.Cli.Compression
end
