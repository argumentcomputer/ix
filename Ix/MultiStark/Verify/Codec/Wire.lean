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

def readBytes (count : Nat) : Reader Bytes := do
  let state ← get
  if state.offset + count > state.bytes.size then throw .truncated
  set { state with offset := state.offset + count }
  return state.bytes.extract state.offset (state.offset + count)

def readByte : Reader UInt8 := do
  let state ← get
  match state.bytes[state.offset]? with
  | none => throw .truncated
  | some byte =>
    set { state with offset := state.offset + 1 }
    return byte

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

def readCounted {α : Type} (count : Nat) (element : Reader α) : Reader (Array α) := do
  let state ← get
  if count > state.vectorLimit then throw .vectorLimit
  if count > state.items then throw .itemLimit
  set { state with items := state.items - count }
  let mut values := #[]
  for _ in [0:count] do values := values.push (← element)
  return values

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
  if bytes.size > limits.bytes then throw .byteLimit
  let (value, state) ← reader.run { bytes, vectorLimit := limits.vector, items := limits.items }
  unless state.offset == bytes.size do throw .trailing
  return value

structure WriteState where
  bytes : Bytes := #[]
  limit : Nat
  vectorLimit : Nat
  items : Nat

abbrev Writer := StateT WriteState (Except DecodeError)

def writeBytes (bytes : Bytes) : Writer Unit := do
  let state ← get
  if state.bytes.size + bytes.size > state.limit then throw .byteLimit
  set { state with bytes := state.bytes ++ bytes }

def writeByte (byte : UInt8) : Writer Unit := writeBytes #[byte]

def writeNat (width n : Nat) : Writer Unit := do
  if n ≥ 2 ^ (8 * width) then throw .integerRange
  writeBytes (littleEndian width n)

def writeBool (value : Bool) : Writer Unit := writeByte (if value then 1 else 0)
def writeField (value : Field) : Writer Unit := writeNat 8 value.val
def writeExt (value : Ext) : Writer Unit := do writeField value.c0; writeField value.c1
def writeDigest (digest : Digest) : Writer Unit := writeBytes digest.bytes

def writeCounted {α : Type} (element : α → Writer Unit) (values : Array α) : Writer Unit := do
  let state ← get
  if values.size > state.vectorLimit then throw .vectorLimit
  if values.size > state.items then throw .itemLimit
  set { state with items := state.items - values.size }
  for value in values do element value

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
