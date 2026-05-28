module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize
public import Ix.MultiStark.Keccak
public import Ix.MultiStark.Pcs
public import Ix.MultiStark.SystemDeserialize
public import Ix.MultiStark.Verifier

/-!
# Multi-STARK proof verifier (Aiur)

A recursive-verifier scaffold that (a) deserializes a `multi_stark::prover::Proof`
(`Ix/MultiStark/Deserialize.lean`) and (b) binds the received byte stream to a
public digest: it recomputes `keccak256` (`Ix/MultiStark/Keccak.lean`, the hash
multi-stark uses) over the bytes and asserts it equals the digest passed as
public input.

The remaining verification logic (FRI, Merkle, Fiat-Shamir) will hang off
`read_proof`.
-/

public section

namespace MultiStark

def entrypoints := ⟦
  -- Public input: the 32-byte keccak-256 digest of the proof, as 4 little-endian
  -- byte lanes. Read the proof bytes non-deterministically from IO key `[0]`,
  -- deserialize into a `Proof` object (asserting the whole stream was consumed),
  -- then recompute keccak-256 over the same bytes and assert it equals `digest`
  -- — binding the IO-fed bytes to the public commitment.
  pub fn verify_multi_stark_proof(digest: [[U8; 8]; 4], system_digest: [[U8; 8]; 4]) {
    -- Proof from IO key [0]: deserialize, assert fully consumed, and bind the
    -- bytes to the public keccak-256 `digest`.
    let (idx, len) = io_get_info([0]);
    let bytes = #read_byte_stream(idx, len);
    let (proof, rest) = read_proof(bytes);
    assert_eq!(load(rest), ListNode.Nil);
    assert_eq!(keccak256(bytes), digest);
    -- Verifying key (`System<AiurCircuit>`) from IO key [1]: bind the bytes to
    -- the public keccak-256 `system_digest`, then reconstruct the system.
    let (sidx, slen) = io_get_info([1]);
    let sbytes = #read_byte_stream(sidx, slen);
    assert_eq!(keccak256(sbytes), system_digest);
    let (_sys, srest) = read_system(sbytes);
    assert_eq!(load(srest), ListNode.Nil);
    -- Structural + accumulator + Fiat-Shamir checks (OOD will use `_sys`).
    assert_eq!(verify(proof), 1);
    ()
  }
⟧

/-- The standalone Multi-STARK verifier toplevel: `core` (lists/options) +
`byteStream` (`U64`, `flatten_u64`, `read_byte_stream`, …) + the deserializer,
the keccak-256 implementation, and the entrypoint. -/
def multiStark : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← IxVM.core.merge IxVM.byteStream
  let t ← t.merge deserialize
  let t ← t.merge keccak
  let t ← t.merge systemDeserialize
  let t ← t.merge pcs
  let t ← t.merge verifier
  t.merge entrypoints

end MultiStark

end
