namespace Ixon

def byteCount (x: UInt64) : UInt8 :=
  if      x < 0x0000000000000100 then 1
  else if x < 0x0000000000010000 then 2
  else if x < 0x0000000001000000 then 3
  else if x < 0x0000000100000000 then 4
  else if x < 0x0000010000000000 then 5
  else if x < 0x0001000000000000 then 6
  else if x < 0x0100000000000000 then 7
  else 8

def trimmedLE (x: UInt64) : Array UInt8 :=
  if x == 0 then Array.mkArray1 0 else List.toArray (go 8 x)
  where
    go : Nat → UInt64 → List UInt8
    | _, 0 => []
    | 0, _ => []
    | Nat.succ f, x =>
      Nat.toUInt8 (UInt64.toNat x) :: go f (UInt64.shiftRight x 8)

def fromTrimmedLE (xs: Array UInt8) : UInt64 := List.foldr step 0 xs.toList
  where
    step byte acc := UInt64.shiftLeft acc 8 + (UInt8.toUInt64 byte)

--  F := flag, L := large-bit, X := small-field, A := large_field
-- 0xFFLX_XXXX {AAAA_AAAA, ...}
structure Tag2 where
  flag: Fin 4
  size: UInt64
  deriving Inhabited, Repr, BEq, Hashable

def encodeTag2Head (tag: Tag2) : UInt8 := 
  let t := UInt8.shiftLeft (UInt8.ofNat tag.flag.val) 6
  if tag.size < 32
  then t + (UInt64.toUInt8 tag.size)
  else t + 0b10_0000 + (byteCount tag.size - 1)

def flag2_to_Fin4 (x: UInt8) : Fin 4 :=
  ⟨ x.toNat / 64, by
      have h256 : x.toNat < 256 := UInt8.toNat_lt x
      have h : x.toNat < 64 * 4 := by simpa using h256
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
  ⟩

def decodeTag2Head (head: UInt8) : (Fin 4 × Bool × UInt8) :=
  let flag : Fin 4 := flag2_to_Fin4 head
  let largeBit := (UInt8.land head 0b10_0000 != 0)
  let small := head % 0b10_0000
  (flag, largeBit, small)

--  F := flag, L := large-bit, X := small-field, A := large_field
-- 0xFFFF_LXXX {AAAA_AAAA, ...}
-- "Tag" means the whole thing
-- "Head" means the first byte of the tag
-- "Flag" means the first nibble of the head
structure Tag4 where
  flag: Fin 16
  size: UInt64
  deriving Inhabited, Repr, BEq, Hashable

-- 0xC is a hardcoded exception without small size
def encodeTag4Head (tag: Tag4): UInt8 :=
  let t := UInt8.shiftLeft (UInt8.ofNat tag.flag.val) 4
  if tag.size < 8
  then t + tag.size.toUInt8
  else t + 0b1000 + (byteCount tag.size - 1)

def flag4_to_Fin16 (x: UInt8) : Fin 16 :=
  ⟨ x.toNat / 16, by
      have h256 : x.toNat < 256 := UInt8.toNat_lt x
      have h : x.toNat < 16 * 16 := by simpa using h256
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
  ⟩

-- 0xC is a hardcoded exception without small size
def decodeTag4Head (head: UInt8) : (Fin 16 × Bool × UInt8) :=
  let flag : Fin 16 := flag4_to_Fin16 head
  let largeBit := UInt8.land head 0b1000 != 0
  let small := if flag == 0xC then head % 0b10000 else head % 0b1000
  (flag, largeBit, small)

end Ixon
