/-!
# Ixon serialization primitives

Byte-level plumbing for the Ixon v2 codec, mirroring ix's format family
(`ix/Ix/Ixon.lean`): `PutM`/`GetM`, minimal little-endian u64s, and the
`Tag0`/`Tag2`/`Tag4` headers.

v2 decoders are **strict**: non-minimal size encodings, large-form sizes
that fit the small form, and trailing bytes are all rejected, so that
byte-equality and value-equality coincide — content addressing demands
exactly one spelling per value.
-/

namespace Navigatrix.Ixon

/-- Serialization writer monad: accumulate bytes. -/
abbrev PutM := StateM ByteArray

/-- Deserialization state: input bytes and cursor. -/
structure GetState where
  bytes : ByteArray
  idx : Nat

/-- Deserialization monad: cursor over bytes, `String` errors. -/
abbrev GetM := StateT GetState (Except String)

def runPut (m : PutM Unit) : ByteArray :=
  (m.run .empty).2

/-- Run a decoder, requiring full consumption of the input. -/
def runGet (m : GetM α) (bytes : ByteArray) : Except String α := do
  let (a, st) ← m.run ⟨bytes, 0⟩
  if st.idx != st.bytes.size then
    throw s!"trailing bytes: consumed {st.idx} of {st.bytes.size}"
  return a

class Serialize (α : Type) where
  put : α → PutM Unit
  get : GetM α

def ser [Serialize α] (a : α) : ByteArray :=
  runPut (Serialize.put a)

def de [Serialize α] (bytes : ByteArray) : Except String α :=
  runGet Serialize.get bytes

/-! ## Primitives -/

def putU8 (x : UInt8) : PutM Unit :=
  modify fun s => s.push x

def getU8 : GetM UInt8 := do
  let st ← get
  if h : st.idx < st.bytes.size then
    let b := st.bytes[st.idx]
    set { st with idx := st.idx + 1 }
    return b
  else
    throw "EOF"

/-- Count bytes needed to represent a u64 in minimal little-endian form. -/
def u64ByteCount (x : UInt64) : UInt8 :=
  if x == 0 then 0
  else if x < 0x100 then 1
  else if x < 0x10000 then 2
  else if x < 0x1000000 then 3
  else if x < 0x100000000 then 4
  else if x < 0x10000000000 then 5
  else if x < 0x1000000000000 then 6
  else if x < 0x100000000000000 then 7
  else 8

/-- Write a u64 in minimal little-endian bytes. -/
def putU64TrimmedLE (x : UInt64) : PutM Unit := do
  let n := u64ByteCount x
  for i in [0:n.toNat] do
    putU8 ((x >>> (i.toUInt64 * 8)).toUInt8)

/-- Read a u64 from `n` little-endian bytes. -/
def getU64TrimmedLE (n : Nat) : GetM UInt64 := do
  let mut x : UInt64 := 0
  for i in [0:n] do
    let b ← getU8
    x := x ||| (b.toUInt64 <<< (i.toUInt64 * 8))
  return x

def putBytes (x : ByteArray) : PutM Unit :=
  modify fun s => s.append x

def getBytes (len : Nat) : GetM ByteArray := do
  let st ← get
  if st.idx + len ≤ st.bytes.size then
    let chunk := st.bytes.extract st.idx (st.idx + len)
    set { st with idx := st.idx + len }
    return chunk
  else
    throw s!"EOF: need {len} bytes at index {st.idx}, size {st.bytes.size}"

/-- Read a byte that must be exactly 0 or 1 (canonical Bool). -/
def getBool01 : GetM Bool := do
  match ← getU8 with
  | 0 => return false
  | 1 => return true
  | b => throw s!"expected Bool byte (0 or 1), got {b}"

/-! ## Tag headers

`TagN`: an N-bit flag plus a size. Header byte layout (high to low):
`[flag:N][large:1][small: 7-N]`. If `large = 0`, the size is the small
field; otherwise the small field holds `byteCount - 1` and the size
follows in minimal little-endian bytes. -/

structure Tag0 where
  size : UInt64
  deriving BEq, Repr

structure Tag2 where
  flag : UInt8
  size : UInt64
  deriving BEq, Repr

structure Tag4 where
  flag : UInt8
  size : UInt64
  deriving BEq, Repr

def putTag0 (t : Tag0) : PutM Unit := do
  if t.size < 128 then
    putU8 t.size.toUInt8
  else
    let n := u64ByteCount t.size
    putU8 (0x80 ||| (n - 1))
    putU64TrimmedLE t.size

def getTag0 : GetM Tag0 := do
  let b ← getU8
  if b &&& 0x80 == 0 then
    return ⟨(b &&& 0x7F).toUInt64⟩
  else
    let n := (b &&& 0x7F) + 1
    let size ← getU64TrimmedLE n.toNat
    if u64ByteCount size != n then throw "getTag0: non-minimal size"
    if size < 128 then throw "getTag0: size must use small form"
    return ⟨size⟩

def putTag2 (t : Tag2) : PutM Unit := do
  if t.size < 32 then
    putU8 ((t.flag <<< 6) ||| t.size.toUInt8)
  else
    let n := u64ByteCount t.size
    putU8 ((t.flag <<< 6) ||| 0x20 ||| (n - 1))
    putU64TrimmedLE t.size

def getTag2 : GetM Tag2 := do
  let b ← getU8
  let flag := b >>> 6
  if b &&& 0x20 == 0 then
    return ⟨flag, (b &&& 0x1F).toUInt64⟩
  else
    let n := (b &&& 0x1F) + 1
    let size ← getU64TrimmedLE n.toNat
    if u64ByteCount size != n then throw "getTag2: non-minimal size"
    if size < 32 then throw "getTag2: size must use small form"
    return ⟨flag, size⟩

def putTag4 (t : Tag4) : PutM Unit := do
  if t.size < 8 then
    putU8 ((t.flag <<< 4) ||| t.size.toUInt8)
  else
    let n := u64ByteCount t.size
    putU8 ((t.flag <<< 4) ||| 0x08 ||| (n - 1))
    putU64TrimmedLE t.size

def getTag4 : GetM Tag4 := do
  let b ← getU8
  let flag := b >>> 4
  if b &&& 0x08 == 0 then
    return ⟨flag, (b &&& 0x07).toUInt64⟩
  else
    let n := (b &&& 0x07) + 1
    let size ← getU64TrimmedLE n.toNat
    if u64ByteCount size != n then throw "getTag4: non-minimal size"
    if size < 8 then throw "getTag4: size must use small form"
    return ⟨flag, size⟩

end Navigatrix.Ixon
