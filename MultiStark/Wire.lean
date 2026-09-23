module
public import Blake3.Rust
public import Ix.Aiur.Protocol

/-! Host encoding for the generic verifier's digest-bound inputs. -/

public section
namespace MultiStark

/-- The 8 little-endian bytes of `n` as a `u64`. -/
def u64le (n : Nat) : Array UInt8 :=
  (Array.range 8).map (fun i => UInt8.ofNat ((n >>> (8 * i)) % 256))

/-- Serialize public claims to `read_claims`'s wire format (which is also what
the prover's Fiat-Shamir transcript observes): a length-prefixed list of
length-prefixed claims, every word a little-endian `u64`. -/
def serializeClaims (claims : Array (Array Aiur.G)) : ByteArray := Id.run do
  let mut out : Array UInt8 := u64le claims.size
  for c in claims do
    out := out ++ u64le c.size
    for g in c do
      out := out ++ u64le g.val.toNat
  return ⟨out⟩

/-- Assemble `verify_multi_stark_proof`'s public input from the serialized vk
(`AiurSystem.vkBytes`) and claims (`serializeClaims`): vk digest ++ claims
digest, each as 8 packed-4-byte field elements (the entrypoint's format). The FRI parameters are read in-circuit from the digest-bound vk, not
passed publicly. The proof/vk/claims advice itself goes through the
natively-built IO buffer (`executeMultiStark` / `proveMultiStark`, which take
the raw byte blobs directly: channel 0 = the verified native proof transport
returned by `AiurSystem.proofToAdviceBytes`, 1 = vk, 2 = claims, each under
key `[0]`). -/
def digestGs (bytes : ByteArray) : Array Aiur.G :=
  let h := (Blake3.Rust.hash bytes).val.data
  (Array.range 8).map fun i =>
    .ofNat (h[4*i]!.toNat + 256 * h[4*i+1]!.toNat
      + 65536 * h[4*i+2]!.toNat + 16777216 * h[4*i+3]!.toNat)

def verifierPubInput (vkBytes claimBytes : ByteArray) : Array Aiur.G :=
  digestGs vkBytes ++ digestGs claimBytes


end MultiStark
end
