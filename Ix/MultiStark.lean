module
public import Ix.Aiur.Meta
public import Ix.IxVM.Core
public import Ix.IxVM.ByteStream
public import Ix.MultiStark.Deserialize

/-!
# Multi-STARK proof verifier (Aiur)

Step 1 towards a recursive verifier: an Aiur entrypoint scaffold that
deserializes a `multi_stark::prover::Proof` (see `Ix/MultiStark/Deserialize.lean`).

The deserializer is the wire-format reader; the actual verification logic will
hang off `read_proof`. For now the entrypoint builds the `Proof` object and
discards it.
-/

public section

namespace MultiStark

def entrypoints := ⟦
  -- Read the proof bytes non-deterministically from IO key `[0]`, deserialize
  -- into a `Proof` object, and assert the whole stream was consumed. The proof
  -- is then discarded — actual verification logic will hang off `read_proof`.
  pub fn verify_multi_stark_proof() {
    let (idx, len) = io_get_info([0]);
    let bytes = #read_byte_stream(idx, len);
    let (_proof, rest) = read_proof(bytes);
    assert_eq!(load(rest), ListNode.Nil);
    ()
  }
⟧

/-- The standalone Multi-STARK verifier toplevel: `core` (lists/options) +
`byteStream` (`U64`, `flatten_u64`, `read_byte_stream`, …) + the deserializer
and entrypoint. -/
def multiStark : Except Aiur.Global Aiur.Source.Toplevel := do
  let t ← IxVM.core.merge IxVM.byteStream
  let t ← t.merge deserialize
  t.merge entrypoints

end MultiStark

end
