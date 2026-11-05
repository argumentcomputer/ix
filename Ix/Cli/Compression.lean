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
remain reusable. A nonempty `fixedRoot` is the JSON layout of `proof`. -/
@[extern "rs_compression_run"]
opaque compress (vk proof claim statement : @& ByteArray) (fixedRoot dir cacheRoot : @& String)
  (devKzgSrs devFinalSrs : Bool) (finalProof : UInt8) (fresh : Bool := false) : IO ByteArray

/-- Write the FRI worker's root input directory `dir` without compressing. -/
@[extern "rs_compression_write_root"]
opaque writeRoot (vk proof claim statement : @& ByteArray) (fixedRoot dir : @& String) : IO Unit

/-- Verify a compressed proof under the bundled release keys, which belong
to the retired legacy aggregation backend. Development proofs require
`devSrs`; verification needs no proving setup or GPU. -/
@[extern "rs_compression_verify"]
opaque verify (proof claim : @& ByteArray) (devSrs : Bool) : IO String

/-- Verify a recursive KZG proof of `claim` under the verifying key `vk`,
admitted only if its BLAKE3 digest is `trustedDigest` (hexadecimal), for the
root statement `expected` the caller derived from its own aggregation
backend. Development keys require `devSrs`. -/
@[extern "rs_compression_verify_with_vk"]
opaque verifyWithVk (proof claim expected vk : @& ByteArray) (trustedDigest : @& String)
  (devSrs : Bool) : IO String

/-- The recursive verifying key every compression of roots of the backend
key `vk` normalized to `layout` proves to, derived from those inputs and
the inner KZG setup alone. -/
@[extern "rs_compression_derive_vk"]
opaque deriveVk (vk : @& ByteArray) (layout cacheRoot : @& String)
  (devKzgSrs : Bool) : IO ByteArray

/-- Verify a final development proof with the caller's independent bundle pin.
The proof itself cannot authorize its key or a different circuit. -/
@[extern "rs_compression_verify_development"]
opaque verifyDevelopment (proof claim bundle : @& ByteArray)
  (trustedDigest : @& String) (devSrs : Bool) : IO String

/-- Check the Ignition SRS against its pin and, with a nonempty `layout`,
publish the fixed preprocessing of the first KZG and recursive stages for
roots of the aggregation backend key `vk` normalized to `layout` to the
fixed cache under `cacheRoot`; with `plonk`, also build the PLONK cache of
the bundled recursive key. Present entries are only checked. -/
@[extern "rs_compression_prepare"]
opaque prepare (vk : @& ByteArray) (layout cacheRoot : @& String) (devKzgSrs plonk : Bool) : IO Unit

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

/-- Report a compressed proof that verified under `setup`. -/
def reportVerified (addr : Address) (claim : ByteArray) (setup : String) : IO Unit := do
  match setup with
  | "development" =>
    IO.println s!"ok: development proof {addr} verifies claim {Address.blake3 claim} (not production-secure)"
  | "ignition" =>
    IO.println s!"ok: proof {addr} verifies claim {Address.blake3 claim} under the Aztec Ignition powers of tau"
  | "groth16" =>
    IO.println s!"ok: Groth16 proof {addr} verifies claim {Address.blake3 claim} under the admitted circuit-specific setup"
  | _ =>
    throw <| IO.userError s!"unsupported compression setup: {setup}"

end Ix.Cli.Compression
end
