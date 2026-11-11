import Blake3.Rust
import IxCC.Ixon.PureHash

/-!
# Content hashing

`Address.blake3` is the content hash of every address IxCC computes: object
and blob authentication, Merkle roots, projection keys, catalog file hashes,
resource commitments. It is pure BLAKE3 (`Address.blake3Pure`, a total Lean
implementation, `IxCC.Ixon.PureHash`), the function the statements and the
certified kernel's admission hash are about, so no address on the verifier
path comes from foreign code and no theorem depends on the `native_decide`
length proof inside the Blake3 package's `HasherOps.hash`
(`IxCC/docs/byte-contract.md`, "The hash").

The Rust backend (Blake3.lean's `Blake3.Rust`, the trust ledger's native
interface) stays imported for one user: the erased type checker's incremental
hasher (`Blake3.Rust.Hasher`, `IxCC.Ixon.V3.Tc`), which builds the checker's
internal hash-consing and cache keys. Those keys are not addresses of anything
a claim or a statement names: a collision among them can change only the
checker's verdict, which no theorem uses, and their length proofs are
explicit (`V3.Tc.finishHash`).

The semantic `Constant.address?` boundary lives in `Ixon.Sharing`, after the
layer-2 recompression check. IxIR declaration preimages and address APIs live
in their respective `IxIR0/Serialize.lean` and `IxIR1/Serialize.lean` modules.
This module intentionally exposes no unchecked constant-address helper.
-/

namespace IxCC.Ixon

/-- BLAKE3 of arbitrary bytes as an `Address`: pure BLAKE3. -/
def Address.blake3 (x : ByteArray) : Address := Address.blake3Pure x

/-- `Address.blake3` is pure BLAKE3. -/
theorem Address.blake3_eq_pure : Address.blake3 = Address.blake3Pure := rfl

namespace Address

/-- The exact pairwise cryptographic premise used by semantic-address
theorems. It deliberately does not assert impossible global injectivity of a
fixed-width hash. -/
def Blake3NoCollision (left right : ByteArray) : Prop :=
  Address.blake3 left = Address.blake3 right → left = right

end Address

end IxCC.Ixon
