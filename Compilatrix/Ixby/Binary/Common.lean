import Ix.Ixby

/-! Binary IO for the complete functional Ixby runtime. This format has no
proving-profile admission rules. Naturals use minimal unsigned LEB128;
word/field values retain their distinct fixed-width representations. -/

namespace Compilatrix.Ixby.Binary

open Ix.Ixby

abbrev Bytes := Array UInt8
abbrev version : Nat := 1
abbrev semantics : Nat := 0

structure Artifact where
  limits : Limits
  maxSteps : Nat
  program : Program
  deriving BEq, Repr, Inhabited

/-- Loader resource bounds are chosen by the caller, independently of the
execution capacities stored in the artifact. They do not change scalar types. -/
structure DecodeLimits where
  bytes : Nat := 67108864
  integerBytes : Nat := 8192
  valueNodes : Nat := 1048576
  valueDepth : Nat := 1024
  deriving BEq, Repr, Inhabited

inductive Error where
  | reference (error : Ix.Ixby.Error)
  | header | version | nonCanonical | truncated | trailing
  | tag (value : Nat)
  | byteLimit | integerLimit | countLimit | nodeLimit | depthLimit
  deriving BEq, DecidableEq, Repr, Inhabited

structure Decoded {α : Type} (encode : α → Except Error Bytes) (bytes : Bytes) where
  value : α
  canonical : encode value = .ok bytes

namespace Internal

abbrev Encoder := StateT Bytes (Except Error)

def writeBytes (bytes : Bytes) : Encoder Unit := modify (· ++ bytes)
def writeByte (byte : UInt8) : Encoder Unit := modify (·.push byte)

def writeNatural (n : Nat) : Encoder Unit := do
  let width := n.log2 / 7 + 1
  let mut n := n
  for i in [:width] do
    let digit := n % 128
    writeByte (digit + if i + 1 < width then 128 else 0).toUInt8
    n := n / 128

def writeHeader (magic : String) : Encoder Unit := do
  writeBytes magic.toUTF8.data
  writeBytes (bytesLE 4 version)
  writeBytes (bytesLE 4 semantics)

def writeVector {α : Type} (write : α → Encoder Unit) (values : Array α) : Encoder Unit := do
  writeNatural values.size
  for value in values do write value

def encode (write : Encoder Unit) : Except Error Bytes := do
  return (← write.run #[]).2

structure ReadState where
  bytes : Bytes
  limits : DecodeLimits
  offset : Nat := 0
  nodes : Nat

abbrev Decoder := StateT ReadState (Except Error)

def readBytes (count : Nat) : Decoder Bytes := do
  let state ← get
  if state.offset + count > state.bytes.size then throw .truncated
  set { state with offset := state.offset + count }
  return state.bytes.extract state.offset (state.offset + count)

def readByte : Decoder UInt8 := do
  let state ← get
  let some byte := state.bytes[state.offset]? | throw .truncated
  set { state with offset := state.offset + 1 }
  return byte

def readNatural : Decoder Nat := do
  let mut value := 0
  let mut weight := 1
  for i in [:(← get).limits.integerBytes] do
    let byte := (← readByte).toNat
    let digit := byte % 128
    value := value + digit * weight
    if byte < 128 then
      if i > 0 && digit == 0 then throw .nonCanonical
      return value
    weight := weight * 128
  throw .integerLimit

def readHeader (magic : String) : Decoder Unit := do
  unless (← readBytes magic.utf8ByteSize) == magic.toUTF8.data do throw .header
  unless natOfBytesLE (← readBytes 4) == version do throw .version
  unless natOfBytesLE (← readBytes 4) == semantics do throw .version

def readCount (bound : Nat) : Decoder Nat := do
  let count ← readNatural
  if count > bound then throw .countLimit
  return count

/-- Every vector element in this format occupies at least one byte. Check
counts before iterating, and never preallocate from a decoded count. -/
def readVector {α : Type} (bound : Nat) (read : Decoder α) : Decoder (Array α) := do
  let state ← get
  let count ← readCount (min bound (state.bytes.size - state.offset))
  let mut values := #[]
  for _ in [:count] do values := values.push (← read)
  return values

def readNode : Decoder Unit := do
  let state ← get
  match state.nodes with
  | 0 => throw .nodeLimit
  | nodes + 1 => set { state with nodes }

def decode {α : Type} (limits : DecodeLimits) (bytes : Bytes) (read : Decoder α) :
    Except Error α := do
  if bytes.size > limits.bytes then throw .byteLimit
  let (value, state) ← read.run { bytes, limits, nodes := limits.valueNodes }
  unless state.offset == bytes.size do throw .trailing
  return value

def canonicalize {α : Type} (encode : α → Except Error Bytes) (bytes : Bytes) (value : α) :
    Except Error (Decoded encode bytes) :=
  match encoding : encode value with
  | .error error => .error error
  | .ok actual =>
    if equal : actual = bytes then .ok ⟨value, equal ▸ encoding⟩
    else .error .nonCanonical

end Internal
end Compilatrix.Ixby.Binary
