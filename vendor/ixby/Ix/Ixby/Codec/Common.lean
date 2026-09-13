module
public import Ix.Ixby.Profile

/-! Bounded, strict binary IO for the experimental IxBy crypto codec. All
lengths and indices are explicit little-endian integers, never native sizes.
These helpers are not standalone program/value admission boundaries. -/

public section
@[expose] section

namespace Ix.Ixby.Codec

abbrev Bytes := Array UInt8
abbrev wireVersion : Nat := 0
abbrev semanticVersion : Nat := 0

inductive Error where
  | profile (error : ProfileError)
  | header
  | version
  | tag (value : Nat)
  | integerRange
  | nonCanonical
  | truncated
  | trailing
  | byteLimit
  | countLimit
  | nodeLimit
  | depthLimit
  deriving BEq, DecidableEq, Repr, Inhabited

/-- An accepted decoded value carries its exact re-encoding equation. This
does not assert encoder completeness/injectivity, hash security, or execution. -/
structure Decoded {α : Type} (encode : α → Except Error Bytes) (bytes : Bytes) where
  value : α
  canonical : encode value = .ok bytes

namespace Internal

structure WriteState where
  bytes : Bytes := #[]
  limit : Nat
  nodes : Nat

abbrev Encoder := StateT WriteState (Except Error)

def writeBytes (bytes : Bytes) : Encoder Unit := do
  let state ← get
  if state.bytes.size + bytes.size > state.limit then throw .byteLimit
  set { state with bytes := state.bytes ++ bytes }

def writeByte (byte : UInt8) : Encoder Unit := writeBytes #[byte]

/-- No silent narrowing, including otherwise unused projection/member indices. -/
def writeNat (width n : Nat) : Encoder Unit := do
  if n ≥ 2 ^ (8 * width) then throw .integerRange
  writeBytes (bytesLE width n)

def writeU32 (n : Nat) : Encoder Unit := writeNat 4 n

def writeHeader (magic : String) : Encoder Unit := do
  writeBytes magic.toUTF8.data
  writeU32 wireVersion

def writeVector {α : Type} (write : α → Encoder Unit) (values : Array α) : Encoder Unit := do
  writeU32 values.size
  for value in values do write value

def writeNode : Encoder Unit := do
  let state ← get
  match state.nodes with
  | 0 => throw .nodeLimit
  | nodes + 1 => set { state with nodes }

def encode (limit nodes : Nat) (write : Encoder Unit) : Except Error Bytes := do
  let (_, state) ← write.run { limit, nodes }
  return state.bytes

structure ReadState where
  bytes : Bytes
  offset : Nat := 0
  nodes : Nat

abbrev Decoder := StateT ReadState (Except Error)

def readBytes (count : Nat) : Decoder Bytes := do
  let state ← get
  if state.offset + count > state.bytes.size then throw .truncated
  let bytes := state.bytes.extract state.offset (state.offset + count)
  set { state with offset := state.offset + count }
  return bytes

def readByte : Decoder UInt8 := do
  let state ← get
  match state.bytes[state.offset]? with
  | none => throw .truncated
  | some byte =>
    set { state with offset := state.offset + 1 }
    return byte

def readNat (width : Nat) : Decoder Nat := return natOfBytesLE (← readBytes width)
def readU32 : Decoder Nat := readNat 4

def readHeader (magic : String) : Decoder Unit := do
  unless (← readBytes magic.utf8ByteSize) == magic.toUTF8.data do throw .header
  unless (← readU32) == wireVersion do throw .version

def readCount (bound : Nat) : Decoder Nat := do
  let count ← readU32
  if count > bound then throw .countLimit
  return count

/-- Never preallocate from a hostile count. Bounds are checked before the loop,
and missing bytes abort as soon as a required element cannot be read. -/
def readVector {α : Type} (bound : Nat) (read : Decoder α) : Decoder (Array α) := do
  let count ← readCount bound
  let mut values := #[]
  for _ in [0:count] do values := values.push (← read)
  return values

def readNode : Decoder Unit := do
  let state ← get
  match state.nodes with
  | 0 => throw .nodeLimit
  | nodes + 1 => set { state with nodes }

def decode {α : Type} (limit nodes : Nat) (bytes : Bytes) (read : Decoder α) :
    Except Error α := do
  if bytes.size > limit then throw .byteLimit
  let (value, state) ← read.run { bytes, nodes }
  unless state.offset == bytes.size do throw .trailing
  return value

/-- Re-encoding is an explicit acceptance check. The returned proof is checked
by Lean; it is not a claimed inverse law for arbitrary encoder inputs. -/
def canonicalize {α : Type} (encode : α → Except Error Bytes) (bytes : Bytes) (value : α) :
    Except Error (Decoded encode bytes) :=
  match encoding : encode value with
  | .error error => .error error
  | .ok actual =>
    if equal : actual = bytes then .ok ⟨value, equal ▸ encoding⟩
    else .error .nonCanonical

end Internal
end Ix.Ixby.Codec
