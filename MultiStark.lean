module
public import MultiStark.FFI
public import Blake3.Rust
public import Ix.Aiur.Meta
public import Ix.Aiur.Protocol
public import Ix.Aiur.Library.Core
public import Ix.Aiur.Library.ByteStream
public import Ix.Aiur.Library.Blake3
public import MultiStark.Goldilocks
public import MultiStark.Wire
public import MultiStark.Deserialize
public import MultiStark.Keccak
public import MultiStark.Pcs
public import MultiStark.SystemDeserialize
public import MultiStark.Verifier
public import MultiStark.VerifierFunctionGroups

/-!
# Multi-STARK proof verifier (Aiur)

The verifier entrypoint's public statement is purely existential: *"there
exists a valid multi-stark proof for the constraint system with this Blake3
digest and these public claims."* The FRI parameters (blowup, query count,
PoW bits, …) are NOT separate public inputs: they live in the verifying key,
which the statement already binds through `system_digest` — repeating them
publicly would be redundant. The proof itself is
**non-deterministic advice** (fed on IO channel 0,
never hashed or otherwise bound as a public input): the Fiat-Shamir transcript
replay plus the Merkle/OOD/FRI checks are exactly what make any accepted advice
a valid proof — a hash binding of the proof bytes would add nothing to the
statement, while costing an extra in-circuit hash over those bytes.

The verifying key and claims, by contrast, ARE digest-bound (`system_digest`,
`claims_digest`): they determine *what was proven*.

Fixed protocol assumptions (our system): `capHeight = 0`, `maxLogArity = 1`,
`logFinalPolyLen = 0`. The variable FRI parameters (`num_queries`,
`commit_pow_bits`, `query_pow_bits`, `log_blowup`) are read from the
digest-bound verifying key.
-/

public section

namespace MultiStark

def entrypoints := ⟦
  -- Public inputs: the Blake3 digests of the verifying key and the claims,
  -- each as 8 field elements of 4 packed LE bytes (32 bytes; 4-byte packing
  -- is injective in Goldilocks where 8-byte limbs are not, and costs 16
  -- input columns instead of 64). The proof is pure
  -- non-deterministic advice on IO channel 0 — see the module docstring. One
  -- stream per channel (0 = proof, 1 = vk, 2 = claims), each registered under
  -- key `[0]` on its channel.
  pub fn verify_multi_stark_proof(system_digest: [G; 8], claims_digest: [G; 8]) {
    -- Proof advice from IO channel 0: a batch of trace shards (see
    -- `MultiStark/Verifier.lean`, batch verification), deserialized
    -- directly from the IO arena by byte offset and asserted fully consumed
    -- inside `verify_batch_at`. The byte FETCHES inside the readers are
    -- unconstrained (the proof is advice); the parse structure itself stays
    -- constrained.
    let (idx, len) = io_get_info(0, [0]);
    -- Verifying key (`System<AiurCircuit>`) from IO channel 1: fetch the raw
    -- bytes once as advice, then constrain both the hash and deserialization
    -- against that exact byte stream (the same binding pattern as IxVM).
    let (sidx, slen) = io_get_info(1, [0]);
    let sbytes = #read_byte_stream(1, sidx, slen);
    assert_eq!(@b3_pack(@blake3(sbytes)), system_digest);
    let (sys, srest) = @read_system(sbytes);
    assert_eq!(load(srest), ListNode.Nil);
    -- Public claims (`&[&[Val]]`) from IO channel 2: bind the bytes to the
    -- public Blake3 `claims_digest`, then deserialize. The batch's own
    -- claims (in its headers, bound by the batch transcript) must equal
    -- them, which is what ties the public statement to the lookup argument.
    let (cidx, clen) = io_get_info(2, [0]);
    let cbytes = #read_byte_stream(2, cidx, clen);
    assert_eq!(@b3_pack(@blake3(cbytes)), claims_digest);
    let (claims, crest) = @read_claims(cbytes);
    assert_eq!(load(crest), ListNode.Nil);
    -- Policy, batch transcript, every shard's shape/OOD/PCS checks, and the
    -- residual balance.
    assert_eq!(@verify_batch_at(sys, idx, len, claims), 1);
    ()
  }
⟧

/-- Shared verifier circuits, without verification or aggregation entrypoints. -/
def verifierBase : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← Aiur.Library.core.merge Aiur.Library.byteStream
  let t ← t.merge MultiStark.goldilocks
  let t ← t.merge deserialize
  let t ← t.merge Aiur.Library.blake3
  let t ← t.merge systemDeserialize
  let t ← t.merge pcs
  t.merge verifier

/-- The generic verifier, pruned to its single public entrypoint. -/
def multiStark : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← verifierBase
  let t ← t.merge entrypoints
  pure (t.prune [`verify_multi_stark_proof])


end MultiStark

end
