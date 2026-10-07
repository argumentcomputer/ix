module
public import Lean.ToExpr
public import Ix.Common
public import IxC.Address.Core
public import Blake3.Rust

public section

/-! The host-facing address module: the pure key from `Ix.Address.Core`, the
`Lean.ToExpr` instances, and `Address.blake3` over the Rust BLAKE3 backend.
Certified code imports `Ix.Address.Core` (no hashing) or `Ix.Address.Pure`
(`Address.blake3Pure`, the pure Lean implementation) instead.

Every BLAKE3 digest of `Ix` is finalized by `Address.ofHasher`, which passes the
package's length bound (`length < 2 ^ System.Platform.numBits`) explicitly, proved by
cases on the word size (`Address.digestLen_lt_wordBound`). The package's `hash` and
the default argument of its `finalizeWithLength` prove that bound `by native_decide`,
whose auxiliary axiom would otherwise enter the axioms of every function that hashes
and of every theorem whose statement mentions one. The calls, and so the digests, are
the package's. -/

deriving instance Lean.ToExpr for ByteArray
deriving instance Lean.ToExpr for Address

/-- The 32-byte BLAKE3 digest length is below the platform's word bound, by cases on the
word size (`System.Platform.numBits` is 32 or 64): the proof the hashing calls pass to
`finalizeWithLength` in place of its default `by native_decide`. -/
theorem Address.digestLen_lt_wordBound : 32 < 2 ^ System.Platform.numBits := by
  cases System.Platform.numBits_eq with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

/-- Finalize a Rust BLAKE3 hasher to its 32-byte digest, as an `Address`: the package's
`finalizeWithLength` with length 32 (the call `Blake3.Rust.hash` makes), with the bound
passed explicitly (`Address.digestLen_lt_wordBound`), so no `native_decide`. -/
def Address.ofHasher (h : Blake3.Rust.Hasher) : Address :=
  ⟨(Blake3.Rust.Hasher.finalizeWithLength h 32 Address.digestLen_lt_wordBound).val⟩

/-- Compute the Blake3 hash of a `ByteArray`, returning an `Address`: `init`, `update`,
then the finalization, the calls of `Blake3.Rust.hash`, finalized by `Address.ofHasher`. -/
def Address.blake3 (x: ByteArray) : Address :=
  Address.ofHasher ((Blake3.Rust.Hasher.init ()).update x)

instance : Inhabited Address where
  default := Address.blake3 ⟨#[]⟩

end
