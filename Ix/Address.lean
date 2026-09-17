module
public import Lean.ToExpr
public import Ix.Common
public import Ix.Address.Core
public import Blake3.Rust

public section

/-! The host-facing address module: the pure key from `Ix.Address.Core`, the
`Lean.ToExpr` instances, and `Address.blake3` over the Rust BLAKE3 backend.
Certified code imports `Ix.Address.Core` (no hashing) or `Ix.Address.Pure`
(`Address.blake3Pure`, the pure Lean implementation) instead. -/

deriving instance Lean.ToExpr for ByteArray
deriving instance Lean.ToExpr for Address

/-- Compute the Blake3 hash of a `ByteArray`, returning an `Address`. -/
def Address.blake3 (x: ByteArray) : Address := ⟨(Blake3.Rust.hash x).val⟩

instance : Inhabited Address where
  default := Address.blake3 ⟨#[]⟩

end
