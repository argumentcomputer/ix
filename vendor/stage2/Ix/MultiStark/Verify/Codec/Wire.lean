module
public import Ix.MultiStark.Verify.Basic

/-! Total bounded fixed-integer binary IO. Native proof bytes use bincode's
little-endian fixed-int layout, not its variable-integer encoding. There is
no allocation from a hostile length before collection/global admission. -/

public section
@[expose] section

namespace MultiStark.Verify.Codec

structure Canonical {α : Type} (encode : α → Except DecodeError Bytes) (bytes : Bytes) where
  value : α
  encoded : encode value = .ok bytes

namespace Wire

def littleEndian (width n : Nat) : Bytes :=
  (Array.range width).map fun i => (n >>> (8 * i)).toUInt8

def fromLittleEndian (bytes : Bytes) : Nat :=
  bytes.toList.foldr (fun byte n => byte.toNat + 256 * n) 0

structure ReadState where
  bytes : Bytes
  offset : Nat := 0
  vectorLimit : Nat
  items : Nat

abbrev Reader := StateT ReadState (Except DecodeError)

def readBytes (count : Nat) : Reader Bytes := fun state => do
  ensure (state.offset + count ≤ state.bytes.size) .truncated
  return (state.bytes.extract state.offset (state.offset + count), { state with offset := state.offset + count })

def readByte : Reader UInt8 := fun state =>
  match state.bytes[state.offset]? with
  | none => .error .truncated
  | some byte => .ok (byte, { state with offset := state.offset + 1 })

def readTag (expected : UInt8) : Reader Unit := fun state => do
  let (actual, final) ← readByte.run state
  ensure (actual == expected) .tag
  return ((), final)

def readNat (width : Nat) : Reader Nat := return fromLittleEndian (← readBytes width)

def readBool : Reader Bool := do
  match ← readByte with
  | 0 => return false
  | 1 => return true
  | _ => throw .tag

def readField : Reader Field := do
  let n ← readNat 8
  if canonical : n < Ix.Ixby.goldilocksModulus then return ⟨n, canonical⟩
  else throw .field

def readExt : Reader Ext := return ⟨← readField, ← readField⟩

def readDigest : Reader Digest := do
  let bytes ← readBytes 32
  if size : bytes.size = 32 then return ⟨bytes, size⟩
  else throw .truncated

def readRepeatedFrom {α : Type} (element : Reader α) : Nat → List α → Reader (List α)
  | 0, reversed => pure reversed.reverse
  | count + 1, reversed => do
    let value ← element
    readRepeatedFrom element count (value :: reversed)

/-- Tail-recursive collection avoids using one native stack frame per
admitted vector element. The accumulator is restored to wire order once. -/
def readRepeated {α : Type} (element : Reader α) (count : Nat) : Reader (List α) :=
  readRepeatedFrom element count []

def readCounted {α : Type} (count : Nat) (element : Reader α) : Reader (Array α) := fun state => do
  ensure (count ≤ state.vectorLimit) .vectorLimit
  ensure (count ≤ state.items) .itemLimit
  let (values, final) ← (readRepeated element count).run { state with items := state.items - count }
  return (values.toArray, final)

def readVectorWidth {α : Type} (width : Nat) (element : Reader α) : Reader (Array α) := do
  readCounted (← readNat width) element

def readVector {α : Type} (element : Reader α) : Reader (Array α) :=
  readVectorWidth 8 element

def readOption {α : Type} (element : Reader α) : Reader (Option α) := do
  match ← readByte with
  | 0 => return none
  | 1 => return some (← element)
  | _ => throw .tag

def decode {α : Type} (limits : DecodeLimits) (bytes : Bytes) (reader : Reader α) :
    Except DecodeError α := do
  ensure (bytes.size ≤ limits.bytes) .byteLimit
  let (value, state) ← reader.run { bytes, vectorLimit := limits.vector, items := limits.items }
  ensure (state.offset == bytes.size) .trailing
  return value

structure WriteState where
  bytes : Bytes := #[]
  limit : Nat
  vectorLimit : Nat
  items : Nat

abbrev Writer := StateT WriteState (Except DecodeError)

def writeBytes (bytes : Bytes) : Writer Unit := fun state => do
  ensure (state.bytes.size + bytes.size ≤ state.limit) .byteLimit
  return ((), { state with bytes := state.bytes ++ bytes })

def writeByte (byte : UInt8) : Writer Unit := writeBytes #[byte]

def writeNat (width n : Nat) : Writer Unit := fun state => do
  ensure (n < 2 ^ (8 * width)) .integerRange
  (writeBytes (littleEndian width n)).run state

def writeBool (value : Bool) : Writer Unit := writeByte (if value then 1 else 0)
def writeField (value : Field) : Writer Unit := writeNat 8 value.val
def writeExt (value : Ext) : Writer Unit := do writeField value.c0; writeField value.c1
def writeDigest (digest : Digest) : Writer Unit := writeBytes digest.bytes

def writeList {α : Type} (element : α → Writer Unit) : List α → Writer Unit
  | [] => pure ()
  | value :: values => do
    element value
    writeList element values

def writeCounted {α : Type} (element : α → Writer Unit) (values : Array α) : Writer Unit := fun state => do
  ensure (values.size ≤ state.vectorLimit) .vectorLimit
  ensure (values.size ≤ state.items) .itemLimit
  (writeList element values.toList).run { state with items := state.items - values.size }

def writeVectorWidth {α : Type} (width : Nat) (element : α → Writer Unit)
    (values : Array α) : Writer Unit := do
  writeNat width values.size
  writeCounted element values

def writeVector {α : Type} (element : α → Writer Unit) (values : Array α) : Writer Unit :=
  writeVectorWidth 8 element values

def writeOption {α : Type} (element : α → Writer Unit) : Option α → Writer Unit
  | none => writeByte 0
  | some value => do writeByte 1; element value

def encode (limits : DecodeLimits) (writer : Writer Unit) : Except DecodeError Bytes := do
  let (_, state) ← writer.run {
    limit := limits.bytes, vectorLimit := limits.vector, items := limits.items }
  return state.bytes

def canonicalize {α : Type} (encode : α → Except DecodeError Bytes)
    (bytes : Bytes) (value : α) : Except DecodeError (Canonical encode bytes) :=
  match encoded : encode value with
  | .error error => .error error
  | .ok actual =>
    if equal : actual = bytes then .ok ⟨value, equal ▸ encoded⟩
    else .error .nonCanonical

end Wire
end MultiStark.Verify.Codec
