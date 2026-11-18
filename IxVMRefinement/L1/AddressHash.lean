import Ix.Address.Pure

/-! # The address of 32 bytes, and the pure BLAKE3 address as a digest

`ixAddr` reads 32 bytes as an `Address`; `blake3Pure_eq` states `Address.blake3Pure` as
`Blake3.Pure.digest` of the bytes. Both are facts about the pure definitions only (`Ix.Address.Pure`,
the Blake3 package's `Blake3.Pure`), with nothing of the circuit, so a module that needs them
(the committed role data's codec) does not depend on the circuit's program. `L1.Hashed` uses them
for the loaders' addresses. -/

namespace IxVM.Refinement.L1

/-- The address with these 32 bytes. -/
def ixAddr (d : Vector UInt8 32) : Address := ⟨⟨d.toArray⟩⟩

/-- `Address.blake3Pure` is `Blake3.Pure.digest` of the bytes. -/
theorem blake3Pure_eq (bytes : List UInt8) :
    Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr (Blake3.Pure.digest bytes) := by
  first
  | rfl
  | (simp [Address.blake3Pure, Blake3.Pure.hash, ixAddr]; done)
  | (unfold Address.blake3Pure Blake3.Pure.hash ixAddr; simp)

end IxVM.Refinement.L1
