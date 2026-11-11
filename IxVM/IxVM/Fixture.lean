import Aiur.Ixon

/-! The committed IxVM witness fixture (`fixtures/nat-add-comm.ixf`): the
Ixon v4 bytes of a small environment's constants, blobs and role table, with
their addresses and IxVM tag hints, and a correctly hashed but ill-typed
proof the verifier must reject. The file is in Ixon serialization:

```text
fixture    = "IXVMFIX\0" nat(version) string(wire format) string(name)
             address serialized(invalid proof) list(serialized constants)
             list(serialized blobs) list(serialized roles)
             [version 2: list(address nats(binder-data stream values))]
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
  /-- The binder data (D2) of the records, as IxVM reads them from IO channel 8:
  per record its address and its stream values (`Ix/IxVM/PwHints.lean`). Version 2
  only. -/
  binderData : Array (Array Nat × Array Nat) := #[]
  deriving Inhabited, BEq, Repr

namespace Fixture

def magic : ByteArray := "IXVMFIX\x00".toUTF8
def version : Nat := 2

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
  array f.binderData fun (a, vs) => do putAddress a; nats vs.toList

private def getAddress : GetM (Array Nat) := do
  return (← getRaw 32).data.map UInt8.toNat

private def getSerialized : GetM Serialized := do
  let address ← getAddress
  let bytes := (← getBytes).data.map UInt8.toNat
  return { address, bytes, hint := ← getNat }

def decode (bytes : ByteArray) : Except String Fixture := Aiur.Ixon.decode (do
  unless (← getRaw magic.size).data == magic.data do fail "not an IxVM fixture"
  let v ← getNat
  unless v == 1 || v == version do fail s!"unsupported IxVM fixture version {v}"
  let format ← getString
  let name ← getString
  let address ← getAddress
  let invalidProof ← getSerialized
  let constants ← getArray getSerialized
  let blobs ← getArray getSerialized
  let roles ← getArray getSerialized
  let binderData ← if v == 1 then pure #[] else
    getArray (do let a ← getAddress; pure (a, ← getArray getNat))
  return { format, name, address, invalidProof, constants, blobs, roles, binderData }) bytes

end Fixture
end IxVM
