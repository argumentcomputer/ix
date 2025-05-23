import Ix.Unsigned

namespace Archon

inductive Transparent
  | constant : UInt128 → Transparent
  | incremental
  deriving Inhabited

namespace Transparent

def toString : Transparent → String
  | constant u128 => s!"Constant{u128}"
  | incremental => "Incremental"

def toBytes : @& Transparent → ByteArray
  | constant u128 => ⟨#[0]⟩ ++ u128.toLEBytes
  | incremental => ⟨#[1]⟩

/--
Function meant for testing that tells whether the Lean→Rust mapping of Transparent
results on the same expression as deserializing the provided bytes.
-/
@[extern "rs_transparent_is_equivalent_to_bytes"]
opaque isEquivalentToBytes : @& Transparent → @& ByteArray → Bool

end Transparent

end Archon
