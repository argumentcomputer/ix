import Blake3.C
import Blake3.Pure

/-!
# BLAKE3 digests and canonical encodings

Every address, root and commitment in the pipeline is a 32-byte BLAKE3 digest of a canonical byte
encoding, as in Ix. Each kind of object is hashed under its own domain tag, so equal bytes of
different kinds never share an address.

`blake3` uses the native C implementation. `Blake3.Pure.digest` is the total Lean specification
of the same function; the tests check that the two agree.
-/

namespace IxAI

structure Digest where
  bytes : ByteArray

instance : DecidableEq Digest := fun a b =>
  if h : a.bytes.data = b.bytes.data then
    isTrue (by
      obtain ⟨⟨da⟩⟩ := a
      obtain ⟨⟨db⟩⟩ := b
      simp_all)
  else
    isFalse (by intro e; cases e; exact h rfl)

instance : Hashable Digest := ⟨fun d => hash d.bytes.data⟩

def hexByte (b : UInt8) : String :=
  let d := Nat.toDigits 16 b.toNat
  String.join ((if d.length < 2 then '0' :: d else d).map toString)

def Digest.hex (d : Digest) : String := String.join (d.bytes.data.toList.map hexByte)

instance : ToString Digest := ⟨Digest.hex⟩
instance : Repr Digest := ⟨fun d _ => d.hex⟩
instance : Inhabited Digest := ⟨⟨ByteArray.mk (Array.replicate 32 0)⟩⟩

def Digest.short (d : Digest) : String := String.ofList (d.hex.toList.take 12)

/-- Digests are BLAKE3 outputs: 32 bytes. `Enc Digest` writes the bytes with no length prefix, so
every digest that is parsed or constructed from outside must have exactly this length. -/
def Digest.size : Nat := 32

def Digest.wellFormed (d : Digest) : Bool := d.bytes.size == Digest.size

/-- A digest from raw bytes, if there are exactly 32. -/
def Digest.ofBytes? (b : ByteArray) : Option Digest :=
  if b.size == Digest.size then some ⟨b⟩ else none

private def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A digest from 64 hexadecimal digits, either case. -/
def Digest.ofHex? (s : String) : Option Digest := do
  let cs := s.toList
  unless cs.length == 64 do none
  let rec go : List Char → Option (List UInt8)
    | a :: b :: rest => do
      let hi ← hexVal a
      let lo ← hexVal b
      pure ((hi * 16 + lo).toUInt8 :: (← go rest))
    | _ => some []
  let bs ← go cs
  Digest.ofBytes? (ByteArray.mk bs.toArray)

def blake3 (b : ByteArray) : Digest := ⟨(Blake3.C.hash b).val⟩

/-! ## Canonical encoding -/

class Enc (α : Type) where
  /-- Append the encoding of a value. -/
  enc : ByteArray → α → ByteArray

/-- Unsigned LEB128. -/
partial def encNat (b : ByteArray) (n : Nat) : ByteArray :=
  if n < 128 then b.push n.toUInt8 else encNat (b.push ((n % 128) + 128).toUInt8) (n / 128)

instance : Enc Nat := ⟨encNat⟩
instance : Enc Int := ⟨fun b i => encNat b (if i ≥ 0 then 2 * i.toNat else 2 * (-i).toNat - 1)⟩
instance : Enc Bool := ⟨fun b x => b.push (if x then 1 else 0)⟩
instance : Enc UInt64 := ⟨fun b x => encNat b x.toNat⟩
instance : Enc String := ⟨fun b s => let u := s.toUTF8; encNat b u.size ++ u⟩
instance : Enc Digest := ⟨fun b d => b ++ d.bytes⟩

instance {α : Type} [Enc α] : Enc (List α) :=
  ⟨fun b xs => xs.foldl Enc.enc (encNat b xs.length)⟩

instance {α β : Type} [Enc α] [Enc β] : Enc (α × β) := ⟨fun b (x, y) => Enc.enc (Enc.enc b x) y⟩

/-- The BLAKE3 digest of a value's encoding under a domain tag. -/
def digestOf {α : Type} [Enc α] (tag : String) (x : α) : Digest :=
  blake3 (Enc.enc (Enc.enc ByteArray.empty ("ixai/" ++ tag)) x)

end IxAI
