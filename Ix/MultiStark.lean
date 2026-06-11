module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
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
input, for the constraint system with this keccak-256 digest and these public
claims."* The proof itself is **non-deterministic advice** (fed on IO channel 0,
never hashed or otherwise bound as a public input): the Fiat-Shamir transcript
replay plus the Merkle/OOD/FRI checks are exactly what make any accepted advice
a valid proof — a hash binding of the proof bytes would add nothing to the
statement, while costing one keccak-f per 136 bytes in-circuit.

The verifying key and claims, by contrast, ARE digest-bound (`system_digest`,
`claims_digest`): they determine *what was proven*.

Fixed protocol assumptions (our system): `queryProofOfWorkBits = 0`,
`capHeight = 0`, `maxLogArity = 1`, `logFinalPolyLen = 0`. The variable FRI
parameters (`num_queries`, `commit_pow_bits`, `log_blowup`) are public inputs.
-/

public section

namespace MultiStark

def entrypoints := ⟦
  -- Public inputs: the keccak-256 digests of the verifying key and the claims
  -- (4 little-endian u64 lanes each) plus the variable FRI parameters. The
  -- proof is pure non-deterministic advice on IO channel 0 — see the module
  -- docstring. One stream per channel (0 = proof, 1 = vk, 2 = claims), each
  -- registered under key `[0]` on its channel.
  pub fn verify_multi_stark_proof(system_digest: [[U8; 8]; 4], claims_digest: [[U8; 8]; 4], num_queries: G, commit_pow_bits: G, log_blowup: G) {
    -- Proof advice from IO channel 0: deserialize, assert fully consumed.
    let (idx, len) = io_get_info(0, [0]);
    let bytes = #read_byte_stream(0, idx, len);
    let (proof, rest) = read_proof(bytes);
    assert_eq!(load(rest), ListNode.Nil);
    -- Verifying key (`System<AiurCircuit>`) from IO channel 1: bind the bytes
    -- to the public keccak-256 `system_digest`, then reconstruct the system.
    let (sidx, slen) = io_get_info(1, [0]);
    let sbytes = #read_byte_stream(1, sidx, slen);
    assert_eq!(keccak256(sbytes), system_digest);
    let (sys, srest) = read_system(sbytes);
    assert_eq!(load(srest), ListNode.Nil);
    -- Public claims (`&[&[Val]]`) from IO channel 2: bind the bytes to the
    -- public keccak-256 `claims_digest`, then deserialize. Binding them as a
    -- public input is what makes the lookup argument sound (a prover cannot
    -- choose claims adaptively).
    let (cidx, clen) = io_get_info(2, [0]);
    let cbytes = #read_byte_stream(2, cidx, clen);
    assert_eq!(keccak256(cbytes), claims_digest);
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

/-- The standalone Multi-STARK verifier toplevel: `core` (lists/options) +
`byteStream` (`U64`, `flatten_u64`, `read_byte_stream`, …) + the deserializer,
the keccak-256 implementation, and the entrypoint. -/
def multiStark : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← IxVM.core.merge IxVM.byteStream
  let t ← t.merge MultiStark.goldilocks
  let t ← t.merge deserialize
  let t ← t.merge keccak
  let t ← t.merge systemDeserialize
  let t ← t.merge pcs
  let t ← t.merge verifier
  t.merge entrypoints

/-- The verifier toplevel PLUS its self-test entrypoints
(`Ix/MultiStark/Tests.lean`). Kept separate from `multiStark` because every
`pub fn` adds a circuit to the compiled system — the production verifier should
not carry test-only width. Use this toplevel only to run the `*_test`
entrypoints. -/
def multiStarkTests : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← multiStark
  t.merge tests

end MultiStark

end
