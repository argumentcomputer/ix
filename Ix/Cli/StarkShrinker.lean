/-
  Endpoint 1 native `Fp^3` STARK shrinker FFI bindings and envelope prefix checks.
  Supports both `--stark-128` (transparent Protocol v6) and `--stark-128-zk`
  (Protocol v6-zk, hiding by design, not formally stated) with zero trusted setup.
  The hashes are 32-byte BLAKE3: about 85-bit post-quantum collision resistance.
-/
module
public import Ix.Cli.FormalKeys
public import Ix.Store

public section
namespace Ix.Cli.StarkShrinker

/-- 9-byte magic prefix of Endpoint 1 shrunk `Fp^3` STARK envelopes (`IXSTARK6\0`). -/
def magic : ByteArray := "IXSTARK6\x00".toUTF8

/-- Whether `proof` carries an Endpoint 1 `IXSTARK6\0` shrunk STARK envelope. -/
def isShrunk (proof : ByteArray) : Bool :=
  proof.extract 0 magic.size == magic

/-- Schema version of an `IXSTARK6\0` envelope (bytes `9..11` little-endian), or
`none` if `proof` does not start with the `IXSTARK6\0` magic or is truncated.
Version `1` is the Aiur `.ixa` shrinker; version `2` is the compact 1-circuit
Plonkish `FixedRoot` shrinker. -/
def envelopeVersion (proof : ByteArray) : Option UInt16 :=
  if isShrunk proof then
    match proof.data[magic.size]?, proof.data[magic.size + 1]? with
    | some lo, some hi => some (lo.toUInt16 ||| (hi.toUInt16 <<< 8))
    | _, _ => none
  else
    none

/-- Return the 32-byte BLAKE3 content digest pinned for `verifier` in
`tools/formal-aiur.keys`. -/
def pinnedVerifierDigest : IO ByteArray := do
  let pin ← FormalKeys.pinned "verifier"
  let some addr := Address.fromString pin.identity
    | throw (IO.userError s!"malformed verifier artifact pin in tools/formal-aiur.keys: {pin.identity}")
  return addr.hash

/-- Shrink an inner Protocol `v6` proof into a self-verified `IXSTARK6\0` v1
envelope under `--stark-128` (`isZk = false`) or `--stark-128-zk` (`isZk = true`)
using the Aiur recursive verifier `.ixa` artifact. -/
@[extern "rs_stark_shrinker_shrink"]
opaque shrinkRaw (verifierArtifact : @& String) (expectedArtifactDigest : @& ByteArray)
  (innerVk innerClaims innerProof : @& ByteArray)
  (isZk compact hasDevice : Bool) (device : UInt32) : IO ByteArray

/-- Independently verify an `IXSTARK6\0` v1 envelope against the pinned verifier
artifact, expected inner VK digest, and expected claim digest, returning the
formatted honest trust & ZK metadata banner. -/
@[extern "rs_stark_shrinker_verify"]
opaque verifyRaw (verifierArtifact : @& String) (expectedArtifactDigest : @& ByteArray)
  (envelope expectedInnerVkDigest expectedClaimDigest : @& ByteArray) : IO String

/-- Shrink a normalized `FixedRoot` aggregate root (`CheckEnv`) into a compact
`~400 KiB` 1-circuit Plonkish `IXSTARK6\0` v2 envelope under `--stark-128`
(`isZk = false`) or `--stark-128-zk` (`isZk = true`). -/
@[extern "rs_stark_shrinker_shrink_fixed_root"]
opaque shrinkFixedRootRaw (innerVk layoutBytes innerProof expectedClaim : @& ByteArray)
  (isZk compact hasDevice : Bool) (device : UInt32) : IO ByteArray

/-- Independently verify a compact 1-circuit Plonkish `IXSTARK6\0` v2 envelope
against the trusted aggregate verifying key, release `FixedRoot` layout, and
expected statement bytes (no `.ixa` recursive verifier artifact required),
returning the formatted honest trust & ZK metadata banner. -/
@[extern "rs_stark_shrinker_verify_fixed_root"]
opaque verifyFixedRootRaw (innerVk layoutBytes envelope expectedClaim : @& ByteArray) : IO String

end Ix.Cli.StarkShrinker
end
