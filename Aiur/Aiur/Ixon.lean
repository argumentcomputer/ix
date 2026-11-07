module
public import Init.Data.ByteArray
public import Init.Data.String

public section

/-! The Ixon v4 primitives that Aiur artifacts are written with.

The Aiur package does not depend on Ix, so it carries the few Ixon
conventions its artifact grammar (`Aiur.Artifact`) needs:

* a `nat` is an unsigned integer in Ixon's TagN code with no flag bits
  (`Ixon.putTagN 0 0`, Rust `ixon::tag::TagN::put(0, 0, _)`);
* a count or length is a `nat`; a list is its count followed by its items;
* bytes and strings are a `nat` length followed by the raw (UTF-8) bytes;
* a bool is one byte, 0 or 1; an option is the byte 0, or the byte 1 and the
  value;
* a sum is one tag byte followed by the variant's fields in order.

TagN is bijective and the readers check every tag, so the encoding is
canonical. This module is a `module` so that Ix can import it: `Ix.AiurArtifact`
pins `tagN0` to `Ixon.putTagN 0 0`. The Rust copy is `aiur::ixon`. -/

namespace Aiur.Ixon

/-- Append `v` in Ixon's TagN code with no flag bits. Rung ends for `f = 0`:
128, 16512, 82048, 16859264 and 4311826560. -/
def tagN0 (out : ByteArray) (v : UInt64) : ByteArray :=
  let n := v.toNat
  if n < 128 then out.push n.toUInt8
  else if n < 16512 then
    let d := n - 128
    (out.push (128 + d / 256).toUInt8).push (d % 256).toUInt8
  else if n < 82048 then le (out.push 192) (n - 16512) 2
  else if n < 16859264 then le (out.push 193) (n - 82048) 3
  else if n < 4311826560 then le (out.push 194) (n - 16859264) 4
  else le (out.push 195) (n - 4311826560) 8
where
  le (out : ByteArray) (x : Nat) : Nat → ByteArray
    | 0 => out
    | k + 1 => le (out.push (x % 256).toUInt8) (x / 256) k

/-! ## Writing -/

/-- A writer that fails on values the grammar cannot represent. -/
abbrev PutM := EStateM String ByteArray

def run (put : PutM Unit) (capacity : Nat := 1 <<< 16) : Except String ByteArray :=
  match put.run (ByteArray.emptyWithCapacity capacity) with
  | .ok _ bytes => .ok bytes
  | .error e _ => .error e

@[inline] def u8 (x : UInt8) : PutM Unit := modify (·.push x)

/-- Bytes written verbatim, with no length (magic numbers, nested objects). -/
@[inline] def raw (bytes : ByteArray) : PutM Unit := modify (·.append bytes)

def nat (n : Nat) : PutM Unit := do
  unless n < 2 ^ 64 do throw s!"integer {n} exceeds UInt64"
  modify (tagN0 · n.toUInt64)

@[inline] def bool (b : Bool) : PutM Unit := u8 (if b then 1 else 0)

def bytes (b : ByteArray) : PutM Unit := do
  nat b.size
  raw b

def str (s : String) : PutM Unit := bytes s.toUTF8

@[specialize] def list (xs : List α) (item : α → PutM Unit) : PutM Unit := do
  nat xs.length
  for x in xs do item x

@[specialize] def array (xs : Array α) (item : α → PutM Unit) : PutM Unit := do
  nat xs.size
  for x in xs do item x

def nats (xs : List Nat) : PutM Unit := list xs nat

@[specialize] def option (x : Option α) (item : α → PutM Unit) : PutM Unit :=
  match x with
  | none => u8 0
  | some x => do u8 1; item x

/-! ## Reading -/

structure Cursor where
  bytes : ByteArray
  pos : Nat := 0

/-- A strict reader over one complete buffer. -/
abbrev GetM := EStateM String Cursor

def fail (message : String) : GetM α := do
  throw s!"ixon: {message} at byte {(← get).pos}"

/-- Decode a complete buffer, rejecting trailing bytes. -/
def decode (get : GetM α) (bytes : ByteArray) : Except String α :=
  match get.run { bytes } with
  | .ok a cursor =>
    if cursor.pos == bytes.size then .ok a
    else .error s!"ixon: {bytes.size - cursor.pos} trailing bytes at byte {cursor.pos}"
  | .error e _ => .error e

def remaining : GetM Nat := do
  let c ← get
  return c.bytes.size - c.pos

def getRaw (n : Nat) : GetM ByteArray := do
  let c ← get
  unless c.pos + n ≤ c.bytes.size do fail s!"need {n} bytes, end of input"
  set { c with pos := c.pos + n }
  return c.bytes.extract c.pos (c.pos + n)

def getU8 : GetM UInt8 := do
  let c ← get
  let some b := c.bytes[c.pos]? | fail "need 1 byte, end of input"
  set { c with pos := c.pos + 1 }
  return b

/-- A sum tag below `count`. -/
def getTag (what : String) (count : Nat) : GetM Nat := do
  let tag := (← getU8).toNat
  unless tag < count do fail s!"unknown {what} tag {tag}"
  return tag

private def getLE (width : Nat) : GetM Nat := do
  let bytes ← getRaw width
  return bytes.data.foldr (fun b acc => acc * 256 + b.toNat) 0

def getNat : GetM Nat := do
  let head := (← getU8).toNat
  if head < 128 then return head
  if head < 192 then return 128 + (head - 128) * 256 + (← getU8).toNat
  let value ← match head - 192 with
    | 0 => pure (16512 + (← getLE 2))
    | 1 => pure (82048 + (← getLE 3))
    | 2 => pure (16859264 + (← getLE 4))
    | 3 => pure (4311826560 + (← getLE 8))
    | code => fail s!"invalid TagN code {code}"
  unless value < 2 ^ 64 do fail "TagN value exceeds UInt64"
  return value

def getBool : GetM Bool := return (← getTag "bool" 2) == 1

/-- A count of items occupying at least one byte each. -/
def getCount : GetM Nat := do
  let n ← getNat
  unless n ≤ (← remaining) do fail s!"count {n} exceeds the remaining bytes"
  return n

def getBytes : GetM ByteArray := do getRaw (← getNat)

def getString : GetM String := do
  let some s := String.fromUTF8? (← getBytes) | fail "invalid UTF-8 string"
  return s

@[specialize] def getArray (item : GetM α) : GetM (Array α) := do
  let n ← getCount
  let mut out := Array.mkEmpty n
  for _ in [0:n] do out := out.push (← item)
  return out

@[specialize] def getOption (item : GetM α) : GetM (Option α) := do
  if (← getTag "option" 2) == 1 then return some (← item) else return none

end Aiur.Ixon

end
