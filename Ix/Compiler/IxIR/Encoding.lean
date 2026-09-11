import Ix.Compiler.Ixon.Hash

/-!
# Canonical byte primitives for addressed IR artifacts

IxIR₀ and IxIR₁ use a small private grammar for hash preimages. It is not the
Ixon wire format: domains are versioned independently so changing a backend IR
cannot silently preserve an old artifact identity.

Natural numbers use canonical unsigned LEB128 over arbitrary-precision Lean
`Nat`; unlike a `Nat.toUInt64` shortcut, this is total and cannot truncate.
Variable-length byte strings and arrays carry a LEB128 length, addresses are
exactly 32 raw bytes, and every sum constructor has a one-byte tag. These
rules make every concatenation boundary explicit.
-/

namespace Ix.Compiler.IxIR.Encoding

/-- One tag byte. -/
def tag (value : UInt8) : ByteArray :=
  ByteArray.mk #[value]

/-- Canonical unsigned LEB128 for an arbitrary natural number. -/
def nat (value : Nat) : ByteArray :=
  if _h : value < 128 then
    tag (UInt8.ofNat value)
  else
    tag (UInt8.ofNat (128 + value % 128)) ++ nat (value / 128)
termination_by value
decreasing_by
  apply Nat.div_lt_self
  · omega
  · omega

/-- A Boolean as exactly one byte. -/
def bool : Bool → ByteArray
  | false => tag 0
  | true => tag 1

/-- Length-prefixed raw bytes. -/
def blob (bytes : ByteArray) : ByteArray :=
  nat bytes.size ++ bytes

/-- Length-prefixed UTF-8. -/
def string (value : String) : ByteArray :=
  blob value.toUTF8

/-- A content address in its fixed-width raw representation. -/
def address (value : Ixon.Address) : ByteArray :=
  value.hash

/-- Length-prefixed array preserving source order. -/
def array (encode : α → ByteArray) (values : Array α) : ByteArray :=
  nat values.size ++
    values.foldl (fun output value => output ++ encode value) ByteArray.empty

/-- Length-prefixed list preserving source order. -/
def list (encode : α → ByteArray) (values : List α) : ByteArray :=
  nat values.length ++
    values.foldl (fun output value => output ++ encode value) ByteArray.empty

/-- A versioned ASCII domain prefix. Callers use a trailing NUL to keep the
domain boundary visible to non-Lean implementations. -/
def domain (name : String) : ByteArray :=
  name.toUTF8

/-! Frozen primitive spellings. -/

#guard nat 0 == ByteArray.mk #[0]
#guard nat 127 == ByteArray.mk #[127]
#guard nat 128 == ByteArray.mk #[128, 1]
#guard nat 255 == ByteArray.mk #[255, 1]
#guard nat 16384 == ByteArray.mk #[128, 128, 1]
#guard nat (2 ^ 64) ==
  ByteArray.mk #[128, 128, 128, 128, 128, 128, 128, 128, 128, 2]
#guard array nat #[1, 128] == ByteArray.mk #[2, 1, 128, 1]

end Ix.Compiler.IxIR.Encoding
