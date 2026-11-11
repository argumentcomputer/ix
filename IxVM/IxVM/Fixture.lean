import Aiur.Ixon

/-! The committed IxVM witness fixture (`fixtures/nat-add-comm.ixf`): the
Ixon v5 bytes of a small environment's constants (each carrying its binder
data), blobs and role table, with their addresses and IxVM tag hints, and a
correctly hashed but ill-typed proof the verifier must reject. The file is in
Ixon serialization:

```text
fixture    = "IXVMFIX\0" nat(version) string(wire format) string(name)
             address serialized(invalid proof) list(serialized constants)
             list(serialized blobs) list(serialized roles)
serialized = address bytes nat(hint)
address    = 32 raw bytes
```

`crates/ixvm` reads the same grammar. -/

namespace IxVM
open Aiur.Ixon

structure Serialized where
  address : Array Nat
  bytes : Array Nat
  hint : Nat
  deriving Inhabited, BEq, Repr

structure Fixture where
  format : String
  name : String
  address : Array Nat
  invalidProof : Serialized
  constants : Array Serialized
  blobs : Array Serialized
  roles : Array Serialized := #[]
  deriving Inhabited, BEq, Repr

namespace Fixture

def magic : ByteArray := "IXVMFIX\x00".toUTF8
/-- Version 3: Ixon v5 records. (Version 2 carried binder data beside the
records, which IxVM no longer reads.) -/
def version : Nat := 3

private def putAddress (address : Array Nat) : PutM Unit := do
  unless address.size == 32 && address.all (· < 256) do throw "fixture address is not 32 bytes"
  raw ⟨address.map Nat.toUInt8⟩

private def putSerialized (s : Serialized) : PutM Unit := do
  putAddress s.address
  unless s.bytes.all (· < 256) do throw "fixture bytes are not bytes"
  bytes ⟨s.bytes.map Nat.toUInt8⟩
  nat s.hint

def encode (f : Fixture) : Except String ByteArray := Aiur.Ixon.run do
  raw magic
  nat version
  str f.format
  str f.name
  putAddress f.address
  putSerialized f.invalidProof
  array f.constants putSerialized
  array f.blobs putSerialized
  array f.roles putSerialized

private def getAddress : GetM (Array Nat) := do
  return (← getRaw 32).data.map UInt8.toNat

private def getSerialized : GetM Serialized := do
  let address ← getAddress
  let bytes := (← getBytes).data.map UInt8.toNat
  return { address, bytes, hint := ← getNat }

/-- A fixture of version 3, or of version 2 (its binder data, which follow the
roles there, skipped), with its version. -/
def decodeVersioned (bytes : ByteArray) : Except String (Nat × Fixture) := Aiur.Ixon.decode (do
  unless (← getRaw magic.size).data == magic.data do fail "not an IxVM fixture"
  let v ← getNat
  unless v == 2 || v == version do fail s!"unsupported IxVM fixture version {v}"
  let format ← getString
  let name ← getString
  let address ← getAddress
  let invalidProof ← getSerialized
  let constants ← getArray getSerialized
  let blobs ← getArray getSerialized
  let roles ← getArray getSerialized
  if v == 2 then
    discard <| getArray (do let _ ← getAddress; getArray getNat)
  return (v, { format, name, address, invalidProof, constants, blobs, roles })) bytes

def decode (bytes : ByteArray) : Except String Fixture := do
  let (v, f) ← decodeVersioned bytes
  unless v == version do throw s!"unsupported IxVM fixture version {v}"
  return f

end Fixture
end IxVM
