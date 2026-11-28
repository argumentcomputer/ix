import IxCC.Ixon.PureHash

/-!
# Content hashing

`Address.blake3` is the content hash of every address IxCC computes: object
and blob authentication, Merkle roots, projection keys, resource
commitments. It is pure BLAKE3 (`Address.blake3Pure`, a total Lean
implementation, `IxCC.Ixon.PureHash`), the function the statements and the
certified kernel's admission hash are about, so no address on the verifier
path comes from foreign code and no theorem depends on the `native_decide`
length proof inside the Blake3 package's `HasherOps.hash`
(`IxCC/docs/byte-contract.md`, "The hash").

No IxCC module imports the Blake3 package's Rust backend (`Blake3.Rust`):
its one user, the erased type checker's incremental hasher, was deleted with
the checker by the switch to the certified kernel, so no IxCC executable
links the Rust hasher (`IxCC/docs/trusted-extern-ledger.md`).

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
