import Blake3.Rust
import Ix.Compiler.Ixon.Address
import Ix.Compiler.Ixon.Const

/-!
# Content hashing

Low-level BLAKE3 primitives over canonical artifact serializations. The hash
itself is FFI (Rust blake3 via Blake3.lean) — an active entry in the tracked
`docs/compiler/trusted-extern-ledger.md`: assumed semantics is the BLAKE3
function; the endgame replacement is a verified Lean implementation
compiled by our own backend.

The semantic `Constant.address?` boundary lives in `Ixon.Sharing`, after the
layer-2 recompression check. IxIR declaration preimages and address APIs live
in their respective `IxIR0/Serialize.lean` and `IxIR1/Serialize.lean` modules.
This module intentionally exposes no unchecked constant-address helper.

Runtime hash vectors and artifact identities are checked by the compiled
`compiler-tests` executable (`Tests/Compiler/Tests.lean`). The pinned Blake3
dependency precompiles its native libraries; the compiler proof fence records
any native proof leaves that arise through that dependency.
-/

namespace Ix.Compiler.Ixon

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

/-- Hash of a bare serialized expression. This is only a local cache key:
table indices have meaning inside a `Constant.Frame`, so this is deliberately
not named `address` and must not be used as a semantic object identity. -/
def Expr.serializedHash (e : Expr) : Address :=
  .blake3 (runPut (putExpr e))

end Ix.Compiler.Ixon
