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

/-- Describe the inner KZG setup and validate the independent final-setup
selection. Development inner KZG needs development keys for a final proof. -/
@[extern "rs_compression_setup"]
opaque describeSetup (devKzgSrs devFinalSrs : Bool) (finalProof : UInt8) : IO String

/-- Run the stages in `dir`, resuming checked proofs unless `fresh` replaces
them. Fixed preprocessing, parameters and proving keys under `cacheRoot`
remain reusable. A nonempty `fixedRoot` is the JSON layout of `proof`. -/
@[extern "rs_compression_run"]
opaque compress (vk proof claim statement : @& ByteArray) (fixedRoot dir cacheRoot : @& String)
  (devKzgSrs devFinalSrs : Bool) (finalProof : UInt8) (fresh : Bool := false) : IO ByteArray

/-- The versioned normalization layout for the aggregation backend's key. -/
@[extern "rs_compression_release_root_layout"]
opaque releaseRootLayout (vk : @& ByteArray) : IO String

/-- Per-circuit rows of one root wrap execution of `proof`, as a JSON array. -/
@[extern "rs_compression_root_rows"]
opaque rootRows (system : @& Aiur.AiurSystem) (aggrIdx : @& Nat)
  (allowed ixvmVk claim proof : @& ByteArray) : IO String

/-- The fixed root layout holding every row-count array in the JSON array
`rows`, with `headroom` extra doublings per circuit. -/
@[extern "rs_compression_root_layout"]
opaque rootLayout (system : @& Aiur.AiurSystem) (rows : @& String)
  (headroom claimLen : UInt32) : IO String

/-- Wrap the aggregate root `proof` once more and prove the wrap in the fixed
shape of `layout`; returns the normalized proof bytes. -/
@[extern "rs_compression_normalize_root"]
opaque normalizeRoot (system : @& Aiur.AiurSystem) (aggrIdx : @& Nat)
  (allowed ixvmVk claim proof : @& ByteArray) (layout : @& String) : IO ByteArray

/-- Write the FRI worker's root input directory `dir` without compressing. -/
@[extern "rs_compression_write_root"]
opaque writeRoot (vk proof claim statement : @& ByteArray) (fixedRoot dir : @& String) : IO Unit

/-- Normalize `wrapper`'s aggregate root to `layout` under `backend`. -/
def normalize (backend : Aggr.VerificationBackend) (wrapper : Ixon.Proof)
    (layout : String) : IO ByteArray :=
  normalizeRoot backend.system backend.aggrIdx backend.allowed backend.ixvmVk
    (Ix.Claim.ser wrapper.claim) wrapper.proof layout

/-- Verify a compressed proof under the bundled release keys. Development
proofs require `devSrs`; verification needs no proving setup or GPU. -/
@[extern "rs_compression_verify"]
opaque verify (proof claim : @& ByteArray) (devSrs : Bool) : IO String

/-- Verify a final development proof with the caller's independent bundle pin.
The proof itself cannot authorize its key or a different circuit. -/
@[extern "rs_compression_verify_development"]
opaque verifyDevelopment (proof claim bundle : @& ByteArray)
  (trustedDigest : @& String) (devSrs : Bool) : IO String

/-- The claim a merge proves by the merge rule alone: kind 0 joins `left`
and `right`, kind 1 imports `left` unchanged. -/
@[extern "rs_compression_merged_claim"]
opaque mergedClaim (kind : UInt8) (left right : @& ByteArray) : IO ByteArray

/-- Merge compressed proofs under the merge release in the key directory
`keys`, or the bundled one when `keys` is empty: kind 0 joins the left and
right proofs, kind 1 imports the left one. The merge stage is kept in `dir`
and reused while its proof verifies, unless `fresh`. Returns the merged
compressed proof. -/
@[extern "rs_compression_merge"]
opaque merge (kind : UInt8) (leftClaim leftProof rightClaim rightProof : @& ByteArray)
  (keys dir cacheRoot : @& String) (devKzgSrs : Bool) (fresh : Bool := false) : IO ByteArray

/-- Verify a merged compressed proof under the merge release in the key
directory `keys`, or the bundled one when `keys` is empty. -/
@[extern "rs_compression_verify_merged"]
opaque verifyMerged (proof claim : @& ByteArray) (keys : @& String) (devSrs : Bool) : IO String

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

/-- The root statement a compressed proof of `claim` must expose: the public
claim of the backend's `ix_aggr` entrypoint, serialized as one batch claim. -/
def statementBytes (backend : Aggr.VerificationBackend) (claim : Ix.Claim) : ByteArray :=
  MultiStark.serializeClaims
    #[Aggr.aggregateOuterClaim backend.allowed backend.aggrIdx claim]

/-- Verify a compressed proof. With `mergeKeys`, it is a merged proof under
the merge release in that key directory. -/
def verifyProof (addr : Address) (wrapper : Ixon.Proof) (devSrs : Bool)
    (mergeKeys : Option String := none) : IO UInt32 := do
  let claim := Ix.Claim.ser wrapper.claim
  let setup ← match mergeKeys with
    | some keys => verifyMerged wrapper.proof claim keys devSrs
    | none => verify wrapper.proof claim devSrs
  match setup with
  | "development" =>
    IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} (not production-secure)"
  | "ignition" =>
    IO.println s!"ok: proof {addr} verifies claim {Address.blake3 claim} under the Aztec Ignition powers of tau"
  | "groth16" =>
    IO.println s!"ok: Groth16 proof {addr} verifies claim {Address.blake3 claim} under the admitted circuit-specific setup"
  | _ =>
    throw <| IO.userError s!"unsupported compression setup: {setup}"
  if let .checkEnv _ (some base) := wrapper.claim then
    IO.println s!"[verify] conditional: the claim holds only provided every \
      constant under {base} is well-typed; it is not a standalone certificate"
  return 0

end Ix.Cli.Compression
end
