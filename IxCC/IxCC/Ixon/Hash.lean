import Blake3.Rust
import IxCC.Ixon.Address

/-!
# Content hashing

Low-level BLAKE3 primitives over canonical artifact serializations. The hash
itself is FFI (Rust blake3 via Blake3.lean) — an active entry in the tracked
`docs/trusted-extern-ledger.md`: assumed semantics is the BLAKE3
function; the endgame replacement is a verified Lean implementation
compiled by our own backend.

The semantic `Constant.address?` boundary lives in `Ixon.Sharing`, after the
layer-2 recompression check. IxIR declaration preimages and address APIs live
in their respective `IxIR0/Serialize.lean` and `IxIR1/Serialize.lean` modules.
This module intentionally exposes no unchecked constant-address helper.

NB: no `#guard`/`#eval` here — executing the FFI at elaboration needs
the Blake3 shared lib loaded in the interpreter (`--load-dynlib`),
which the nix-built dependency artifact doesn't provide. Execution
tests live in the compiled `tests` executable (`Tests.lean`), run as a
flake check.
-/

namespace IxCC.Ixon

/-- blake3 of arbitrary bytes as an `Address`. -/
def Address.blake3 (x : ByteArray) : Address :=
  let digest := Blake3.Rust.hash x
  ⟨digest.val, digest.property⟩

namespace Address

/-- The exact pairwise cryptographic premise used by semantic-address
theorems. It deliberately does not assert impossible global injectivity of a
fixed-width hash. -/
def Blake3NoCollision (left right : ByteArray) : Prop :=
  Address.blake3 left = Address.blake3 right → left = right

end Address

end IxCC.Ixon
