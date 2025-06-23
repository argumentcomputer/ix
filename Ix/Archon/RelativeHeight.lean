namespace Archon

inductive RelativeHeight
  | base
  | div2 (n : UInt8)
  | mul2 (n : UInt8)
  deriving Inhabited

namespace RelativeHeight

def toString : RelativeHeight → String
  | base => "Base"
  | div2 n => s!"Div2({n})"
  | mul2 n => s!"Mul2({n})"

instance : ToString RelativeHeight := ⟨toString⟩

def toBytes : @& RelativeHeight → ByteArray
  | base => ⟨#[0]⟩
  | div2 n => ⟨#[1, n]⟩
  | mul2 n => ⟨#[2, n]⟩

/--
Function meant for testing that tells whether the Lean→Rust mapping of RelativeHeight
results on the same expression as deserializing the provided bytes.
-/
@[extern "rs_relative_height_is_equivalent_to_bytes"]
opaque isEquivalentToBytes : @& RelativeHeight → @& ByteArray → Bool

end RelativeHeight

end Archon
