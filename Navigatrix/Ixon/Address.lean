import Navigatrix.Ixon.Serialize

/-!
# Content addresses

32-byte blake3 hashes of canonical Ixon serializations (see ix's
`docs/Ixon.md` and `docs/kernel_identity.md`). This module is the pure
data side only — hash *computation* arrives with the Blake3 FFI wiring
(deferred to the store/importer work; see `plans/pre-implementation.md`).
-/

namespace Navigatrix.Ixon

/-- A 32-byte content address. -/
structure Address where
  hash : ByteArray
  deriving Inhabited

instance : BEq Address := ⟨fun a b => a.hash.data == b.hash.data⟩

instance : Hashable Address := ⟨fun a => hash a.hash.data⟩

instance : Repr Address :=
  ⟨fun a _ => "Address " ++ repr a.hash.data⟩

instance : Serialize Address where
  put a := putBytes a.hash
  get := Address.mk <$> getBytes 32

/-- Construct from a byte array, checking the length. -/
def Address.ofBytes? (bytes : ByteArray) : Option Address :=
  if bytes.size == 32 then some ⟨bytes⟩ else none

end Navigatrix.Ixon
