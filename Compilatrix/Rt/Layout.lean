import Compilatrix.Lir.Syntax

/-! # Runtime layout (Phase 1)

The machine representation of values, objects and the context block
(design note `plans/x86-v2/04-runtime.md` §2, §3, §6, §8.1), as constants
and word encodings shared by `Rt.lower`, `cx_init`, `Rt.readback` and the
runtime driver (`fixtures/x86/runtime_driver.c`).

**Words** (04 §2). The low bit marks an immediate:

| Value | Word |
| --- | --- |
| `Nat` n < 2^63 | `2n + 1` (a larger one is `fail natOverflow`, 04 §9) |
| field-less constructor with tag k | `2k + 1` |
| □ | `1` |
| a cell | its 8-aligned address, never 0 |

**Cells** (04 §3). An 8-byte header `scan:u8 | cls:u8 | tag:u16 | rc:i32`
(little-endian, so `rc` is the high half), then the fields, one word each.
Phase 1 cells are immortal (04 §8.1): `cls = 0` and `rc = INT32_MIN`, never
freed, bump-allocated from the region.

**Context block** (04 §6). `r15` (Lir's `ctx`) points 64 bytes into the
region; the fields below it, the free-list heads above it; objects start at
the first 64-byte boundary after the 640-byte block. -/

namespace Compilatrix.Rt

open Compilatrix.Lir (Word)

/-! ## Words -/

/-- The first `Nat` without an immediate word (04 §2, §9). -/
def natLimit : Nat := 2 ^ 63

/-- The word of a `Nat`, if it has one. -/
def natWord (n : Nat) : Option Word := if n < natLimit then some (UInt64.ofNat (2 * n + 1)) else none

/-- The word of a field-less constructor. -/
def ctor0Word (tag : Nat) : Word := UInt64.ofNat (2 * tag + 1)

/-- The word of □. -/
def erasedWord : Word := 1

/-! ## Headers -/

/-- The largest constructor tag (04 §3: kinds use `0x7F01` and up). -/
def maxTag : Nat := 0x7EFF

/-- The largest scanned-field count in the header (`0xFF` means the count is
elsewhere, 04 §3). -/
def maxFields : Nat := 254

/-- `rc` of a static or immortal cell: `INT32_MIN`, as the high half. -/
def immortalRc : Nat := 0x80000000

/-- The low half of a header: `scan | cls << 8 | tag << 16`. -/
def headerLow (scan cls tag : Nat) : Nat := scan + 256 * cls + 65536 * tag

/-- A whole header word. -/
def header (scan cls tag rc : Nat) : Word := UInt64.ofNat (headerLow scan cls tag + 2 ^ 32 * rc)

/-- An immortal cell's header (04 §8.1): `cls = 0`, `rc = INT32_MIN`. -/
def immortalHeader (fields tag : Nat) : Word := header fields 0 tag immortalRc

/-- The bytes of a cell with `n` fields. -/
def cellBytes (n : Nat) : Nat := 8 * (1 + n)

/-- The byte offset of field `i`. -/
def fieldOffset (i : Nat) : Int := 8 + 8 * i

/-- The byte offset of the header's tag (`u16`). -/
def tagOffset : Int := 2

/-! ## The context block -/

/-- Context field offsets from `ctx` (04 §6). `entrySp` and `stackLimit`
belong to the wrapper and the prologue (05 §6.1); Lir never stores to them. -/
def entrySpOff : Int := -64
def stackLimitOff : Int := -56
def stackBudgetOff : Int := -48
def bumpOff : Int := -40
def limitOff : Int := -32
def regionBaseOff : Int := -24
/-- Reserved for diagnostic builds. -/
def reservedOffs : List Int := [-16, -8]

/-- `ctx` is this many bytes into the region. -/
def ctxOffset : Nat := 64

/-- The context block's size, from the region base. -/
def ctxBlockBytes : Nat := 640

/-- Objects start at a multiple of this after the block. -/
def objectAlign : Nat := 64

/-- The free-list heads: small classes `1 … 32` and large classes `32 + j`,
`j = 1 … 39`, each at `ctx + 8c` (04 §6). Phase 1 never uses them;
`cx_init` zeroes them. -/
def headClasses : List Nat := (List.range 71).map (· + 1)

def headOffset (c : Nat) : Int := 8 * c

/-- The smallest region `cx_init` accepts (04 §6). -/
def minRegion : Nat := 4096

/-- The first object address of a region at `base` (the next 64-byte
boundary after the context block). -/
def objectsStart (base : Nat) : Nat := (base + ctxBlockBytes + objectAlign - 1) / objectAlign * objectAlign

/-- Driver status codes (04 §6). -/
def statusOk : Nat := 0
def statusOf : Sem.Resource → Nat
  | .heap => 1
  | .stack => 2
  | .natOverflow => 3
def statusTrap : Nat := 4

/-! ## Encoding lemmas

What `Rt.readback_sound` (M2.5) needs of the encodings: immediates are odd
and halve back to their value, the immortal header's scan and tag fields
read back, and the first object is 64-aligned past the context block. -/

theorem natWord_toNat {n : Nat} {w : Word} (h : natWord n = some w) : w.toNat = 2 * n + 1 := by
  unfold natWord natLimit at h
  split at h
  · cases h
    rw [UInt64.toNat_ofNat']
    apply Nat.mod_eq_of_lt
    omega
  · cases h

theorem ctor0Word_toNat {tag : Nat} (h : tag < natLimit) : (ctor0Word tag).toNat = 2 * tag + 1 := by
  unfold ctor0Word natLimit at *
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

/-- An odd word has its low bit set and halves to its value. -/
theorem odd_word {w : Word} {k : Nat} (h : w.toNat = 2 * k + 1) : w &&& 1 = 1 ∧ (w >>> 1).toNat = k := by
  constructor
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, h]
    simp only [UInt64.toNat_one]
    rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rw [UInt64.toNat_shiftRight, h, Nat.shiftRight_eq_div_pow]
    simp
    omega

theorem immortalHeader_toNat {n tag : Nat} (hn : n ≤ maxFields) (ht : tag ≤ maxTag) :
    (immortalHeader n tag).toNat = n + 65536 * tag + 2 ^ 32 * immortalRc := by
  unfold immortalHeader header headerLow maxFields maxTag immortalRc at *
  rw [UInt64.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  omega

/-- The header's `scan` byte is the field count. -/
theorem immortalHeader_scan {n tag : Nat} (hn : n ≤ maxFields) (ht : tag ≤ maxTag) :
    ((immortalHeader n tag) &&& 0xFF).toNat = n := by
  rw [UInt64.toNat_and, immortalHeader_toNat hn ht]
  rw [show (UInt64.toNat 0xFF) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  unfold maxFields maxTag immortalRc at *
  omega

/-- The header's `tag` half-word is the tag. -/
theorem immortalHeader_tag {n tag : Nat} (hn : n ≤ maxFields) (ht : tag ≤ maxTag) :
    (((immortalHeader n tag) >>> 16) &&& 0xFFFF).toNat = tag := by
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight, immortalHeader_toNat hn ht]
  rw [show (UInt64.toNat 0xFFFF) = 2 ^ 16 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow]
  unfold maxFields maxTag immortalRc at *
  simp
  omega

theorem objectsStart_aligned (b : Nat) : objectsStart b % objectAlign = 0 := by
  unfold objectsStart objectAlign ctxBlockBytes
  omega

theorem objectsStart_bounds (b : Nat) :
    b + ctxBlockBytes ≤ objectsStart b ∧ objectsStart b < b + ctxBlockBytes + objectAlign := by
  unfold objectsStart objectAlign ctxBlockBytes
  omega

end Compilatrix.Rt
