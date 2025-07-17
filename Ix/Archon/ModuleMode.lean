import Ix.Unsigned

namespace Archon

inductive ModuleMode
  | inactive
  | active (logHeight : UInt8) (depth : UInt64)
  deriving Inhabited, Repr

namespace ModuleMode

def toString : ModuleMode → String
  | inactive => "Inactive"
  | active logHeight depth => s!"Active({logHeight}, {depth})"

instance : ToString ModuleMode := ⟨toString⟩

def toBytes : @& ModuleMode → ByteArray
  | inactive => ⟨#[0]⟩
  | active logHeight depth => ⟨#[1, logHeight]⟩ ++ depth.toLEBytes

/--
Function meant for testing that tells whether the Lean→Rust mapping of ModuleMode
results on the same expression as deserializing the provided bytes.
-/
@[extern "rs_module_mode_is_equivalent_to_bytes"]
opaque isEquivalentToBytes : @& ModuleMode → @& ByteArray → Bool

end ModuleMode

end Archon
