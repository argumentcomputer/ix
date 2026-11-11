import IxCC.Ixon.Hash
import IxCC.Ixon.V3.Support
import Lean.Declaration
import Std.Data.TreeMap

/-! Pure representation helpers for the pinned anonymous typechecker.
No ix native integer-conversion or frontend FFI is imported. The helpers the
rest of IxCC also uses (address order and hexadecimal reading, the `Nat`
literal bytes) are in `IxCC/Ixon/V3/Support.lean`; this module keeps the
checker's own hashing helpers. -/

namespace IxCC.Ixon.V3.Tc

def finishHash (h : Blake3.Rust.Hasher) : Address :=
  let digest := h.finalizeWithLength 32 (by
    cases System.Platform.numBits_eq with
    | inl h32 => rw [h32]; decide
    | inr h64 => rw [h64]; decide)
  ⟨digest.val, digest.property⟩

def tcUInt64BytesLE (x : UInt64) : ByteArray :=
  ⟨(Array.range 8).map fun i => (x >>> (8 * i).toUInt64).toUInt8⟩

end IxCC.Ixon.V3.Tc
