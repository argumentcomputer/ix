import Blake3.Pure
import IxCC.Ixon.Address

/-!
# Pure BLAKE3 addresses

`Blake3.Pure.hash` is a total Lean implementation of unkeyed 32-byte BLAKE3
(Blake3.lean, the pinned revision; standard axioms only), compiled natively
like the rest of our code. Every address IxCC computes is this
hash (`Address.blake3`, `IxCC.Ixon.Hash`, is defined as it), so no address on the
verifier path comes from foreign code (the erased checker's internal keys are
not addresses; `IxCC.Ixon.Hash`).
-/

namespace IxCC.Ixon

/-- BLAKE3 of arbitrary bytes as an `Address`, computed by `Blake3.Pure`. -/
def Address.blake3Pure (x : ByteArray) : Address :=
  let digest := Blake3.Pure.hash x
  ⟨digest.val, digest.property⟩

end IxCC.Ixon
