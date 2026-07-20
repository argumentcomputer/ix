module
public import Blake3.Rust
public import Ix.Aiur.Meta
public import Ix.Aiur.Protocol
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.IxVM.Blake3
public import Ix.MultiStark.Goldilocks
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak
public import Ix.MultiStark.Pcs
public import Ix.MultiStark.SystemDeserialize
public import Ix.MultiStark.Verifier
public import Ix.MultiStark.Tests

/-!
# Multi-STARK proof verifier (Aiur)

The recursive verifier. Its public statement is purely existential: *"there
exists a valid multi-stark proof, under the FRI parameters given as public
input, for the constraint system with this Blake3 digest and these public
claims."* The proof itself is **non-deterministic advice** (fed on IO channel 0,
never hashed or otherwise bound as a public input): the Fiat-Shamir transcript
replay plus the Merkle/OOD/FRI checks are exactly what make any accepted advice
a valid proof — a hash binding of the proof bytes would add nothing to the
statement, while costing an extra in-circuit hash over those bytes.

The verifying key and claims, by contrast, ARE digest-bound (`system_digest`,
`claims_digest`): they determine *what was proven*.

Fixed protocol assumptions (our system): `queryProofOfWorkBits = 0`,
`capHeight = 0`, `maxLogArity = 1`, `logFinalPolyLen = 0`. The variable FRI
parameters (`num_queries`, `commit_pow_bits`, `log_blowup`) are public inputs.
-/

public section

namespace MultiStark

def entrypoints := ⟦
  -- Public inputs: the Blake3 digests of the verifying key and the claims
  -- (32 bytes = 4 little-endian u64 lanes each) plus the variable FRI parameters. The
  -- proof is pure non-deterministic advice on IO channel 0 — see the module
  -- docstring. One stream per channel (0 = proof, 1 = vk, 2 = claims), each
  -- registered under key `[0]` on its channel.
  pub fn verify_multi_stark_proof(system_digest: [[U8; 8]; 4], claims_digest: [[U8; 8]; 4], num_queries: G, commit_pow_bits: G, log_blowup: G) {
    -- Proof advice from IO channel 0: deserialize directly from the IO arena
    -- by byte offset (no materialized byte stream), assert fully consumed.
    -- The byte FETCHES inside the readers are unconstrained (the proof is
    -- advice — same trust model as the former `#read_byte_stream`); the
    -- parse structure itself stays constrained.
    let (idx, len) = io_get_info(0, [0]);
    let (proof, stop) = read_proof(idx);
    assert_eq!(stop, idx + len);
    -- Verifying key (`System<AiurCircuit>`) from IO channel 1: bind the bytes
    -- to the public Blake3 `system_digest` (hashed straight from the IO arena
    -- — no byte list), then reconstruct the system via indexed reads and
    -- assert full consumption.
    let (sidx, slen) = io_get_info(1, [0]);
    assert_eq!(b3_to_digest(b3_io(1, sidx, slen)), system_digest);
    let (sys, send) = read_system(sidx);
    assert_eq!(send, sidx + slen);
    -- Public claims (`&[&[Val]]`) from IO channel 2: bind the bytes to the
    -- public Blake3 `claims_digest`, then deserialize. Binding them as a
    -- public input is what makes the lookup argument sound (a prover cannot
    -- choose claims adaptively).
    let (cidx, clen) = io_get_info(2, [0]);
    let cbytes = #read_byte_stream(2, cidx, clen);
    assert_eq!(b3_to_digest(blake3(cbytes)), claims_digest);
    let (claims, crest) = read_claims(cbytes);
    assert_eq!(load(crest), ListNode.Nil);
    -- Structural + accumulator + PCS checks.
    assert_eq!(verify(proof), 1);
    -- Step 3 + 5: prover-faithful Fiat-Shamir replay and the out-of-domain
    -- composition/quotient check, `composition(ζ)·inv_vanishing(ζ) == quotient(ζ)`.
    assert_eq!(ood_verify(sys, proof, claims, num_queries, commit_pow_bits, log_blowup), 1);
    ()
  }
⟧

/-- The FULL Multi-STARK verifier toplevel: `core` (lists/options) +
`byteStream` (`U64`, `flatten_u64`, `read_byte_stream`, …) + the deserializer,
the Blake3 hash, and the entrypoint — unpruned, including entries inherited
from the shared modules (`blake3_test`/`blake3_bench`). Only `multiStarkTests`
builds on this; production uses `multiStark` (pruned). -/
def multiStarkFull : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← IxVM.core.merge IxVM.byteStream
  let t ← t.merge MultiStark.goldilocks
  let t ← t.merge deserialize
  let t ← t.merge IxVM.blake3
  let t ← t.merge systemDeserialize
  let t ← t.merge pcs
  let t ← t.merge verifier
  t.merge entrypoints

/-- The production Multi-STARK verifier toplevel: `multiStarkFull` pruned to
`verify_multi_stark_proof`'s call closure. Every compiled function is a
committed circuit whose openings pad every proof of the verifier's execution,
so functions only reachable from unrelated entries (kernel-oriented helpers of
the shared modules, test/bench entries) cost real proof bytes if kept. -/
def multiStark : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← multiStarkFull
  pure (t.prune [`verify_multi_stark_proof])

/-! ## Lean-side input assembly

Callers of `verify_multi_stark_proof` (tests, benchmarks) must reproduce the
verifier's wire formats byte-for-byte — the vk and claims are Blake3
digest-bound. These helpers are that recipe's single home. -/

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
digest ++ the variable FRI parameters. The proof/vk/claims advice itself goes
through the natively-built IO buffer (`executeMultiStark` /
`proveMultiStark`, which take the raw byte blobs directly), or through
`verifierInput` on the Lean-buffer fallback path. -/
def verifierPubInput (vkBytes claimBytes : ByteArray)
    (commitParams : Aiur.CommitmentParameters) (friParams : Aiur.FriParameters) :
    Array Aiur.G :=
  let digestGs : ByteArray → Array Aiur.G :=
    fun b => (Blake3.Rust.hash b).val.data.map .ofUInt8
  digestGs vkBytes ++ digestGs claimBytes ++
    #[.ofNat friParams.numQueries, .ofNat friParams.commitProofOfWorkBits,
      .ofNat commitParams.logBlowup]

/-- Assemble `verify_multi_stark_proof`'s inputs from the serialized proof, vk
(`AiurSystem.vkBytes`), and claims (`serializeClaims`): the public input
(`verifierPubInput`) and the IO buffer (channel 0 = proof advice, 1 = vk,
2 = claims, each under key `[0]`). The Lean-built buffer boxes every byte
into a `G` and is marshalled across FFI — prefer the raw-bytes entrypoints
(`executeMultiStark` / `proveMultiStark`) off the hot path. -/
def verifierInput (proofBytes vkBytes claimBytes : ByteArray)
    (commitParams : Aiur.CommitmentParameters) (friParams : Aiur.FriParameters) :
    Array Aiur.G × Aiur.IOBuffer :=
  let gs := fun (b : ByteArray) => b.data.map Aiur.G.ofUInt8
  let pubInput := verifierPubInput vkBytes claimBytes commitParams friParams
  let io := (((default : Aiur.IOBuffer).extend 0 #[.ofNat 0] (gs proofBytes)).extend
    1 #[.ofNat 0] (gs vkBytes)).extend 2 #[.ofNat 0] (gs claimBytes)
  (pubInput, io)

/-- The verifier toplevel PLUS its self-test entrypoints
(`Ix/MultiStark/Tests.lean`), unpruned. Kept separate from `multiStark`
because every `pub fn` adds a circuit to the compiled system — the production
verifier should not carry test-only width. Use this toplevel only to run the
`*_test` entrypoints. -/
def multiStarkTests : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← multiStarkFull
  t.merge tests

end MultiStark

end
