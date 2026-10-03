import Blake3.Pure
import Compilatrix.Ixon.Address

/-!
# Pure BLAKE3 addresses

`Blake3.Pure.hash` is a total Lean implementation of unkeyed 32-byte BLAKE3
(Blake3.lean, the pinned revision; standard axioms only), compiled natively
like the rest of our code. Ingress authenticates every object of an Ixon
environment with it, so reading a closure involves no foreign hash
function. `Compilatrix.Ixon.Hash` keeps the Rust backend (`Address.blake3`)
for its existing users.
-/

namespace Compilatrix.Ixon

/-- BLAKE3 of arbitrary bytes as an `Address`, computed by `Blake3.Pure`. -/
def Address.blake3Pure (x : ByteArray) : Address :=
  let digest := Blake3.Pure.hash x
  ⟨digest.val, digest.property⟩

end Compilatrix.Ixon
