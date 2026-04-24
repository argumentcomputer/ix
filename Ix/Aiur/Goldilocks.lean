module

@[expose] public section

namespace Aiur

abbrev gSize : UInt64 := 1 - 2 ^ 32
abbrev G := { u : UInt64 // u < gSize }

def G.ofNat (n : Nat) : G :=
  let n := n.toUInt64
  if h : n < gSize then ⟨n, h⟩
  else ⟨n % gSize, UInt64.mod_lt n (by decide)⟩

instance : OfNat G n := ⟨G.ofNat n⟩

@[inline] def G.ofUInt8 (u8 : UInt8) : G :=
  let u64 := u8.toUInt64
  have h : u64 < gSize := by
    have lt256 : u64 < 256 := by
      simpa [UInt64.lt_iff_toNat_lt] using UInt8.toNat_lt _
    exact UInt64.lt_trans lt256 (by decide)
  ⟨u64, h⟩

instance : Add G where
  add a b := G.ofNat (a.val.toNat + b.val.toNat)

instance : Sub G where
  sub a b := G.ofNat (a.val.toNat + gSize.toNat - b.val.toNat)

instance : Mul G where
  mul a b := G.ofNat (a.val.toNat * b.val.toNat)

/-- Semantic model of Aiur's `eq_zero` primitive. -/
def G.eqZero (x : G) : G := if x = (0 : G) then 1 else 0

/-- The natural number value of a `G` element. -/
abbrev G.n (x : G) : Nat := x.val.toNat

/-- Range predicate for u8 operations. -/
def G.isU8 (x : G) : Prop := x.n < 256

/-- Range predicate for u32 operations. -/
def G.isU32 (x : G) : Prop := x.n < 2 ^ 32

-- Semantic models for unsigned integer operations.
-- These mirror the Aiur circuit gadgets, which force range constraints
-- on their inputs and compute the corresponding bitwise/arithmetic result.

def G.u8And (a b : G) : G := G.ofNat (a.n &&& b.n)
def G.u8Or  (a b : G) : G := G.ofNat (a.n ||| b.n)
def G.u8Xor (a b : G) : G := G.ofNat (a.n ^^^ b.n)
def G.u8LessThan (a b : G) : G := if a.n < b.n then 1 else 0

/-- u8 addition returns `(result % 256, carry)`. -/
def G.u8Add (a b : G) : G × G :=
  (G.ofNat ((a.n + b.n) % 256), G.ofNat ((a.n + b.n) / 256))

/-- u8 subtraction returns `(result % 256, borrow)`. -/
def G.u8Sub (a b : G) : G × G :=
  (G.ofNat ((a.n + 256 - b.n) % 256), if a.n < b.n then 1 else 0)

def G.u8ShiftLeft  (a : G) : G := G.ofNat ((a.n * 2) % 256)
def G.u8ShiftRight (a : G) : G := G.ofNat (a.n / 2)

/-- Bit decomposition: returns an 8-element array (LSB first). -/
def G.u8BitDecomposition (a : G) : Fin 8 → G :=
  fun i => G.ofNat ((a.n >>> i.val) &&& 1)

def G.u32LessThan (a b : G) : G := if a.n < b.n then 1 else 0

-- Requires native evaluation because G.ofNat uses @[extern] Nat.toUInt64
theorem G.one_ne_zero : ¬(1 : G) = (0 : G) := by native_decide

theorem G.add_comm (a b : G) : a + b = b + a := by
  show G.ofNat (a.val.toNat + b.val.toNat) = G.ofNat (b.val.toNat + a.val.toNat)
  congr 1; omega

theorem G.mul_comm (a b : G) : a * b = b * a := by
  show G.ofNat (a.val.toNat * b.val.toNat) = G.ofNat (b.val.toNat * a.val.toNat)
  congr 1; exact Nat.mul_comm _ _

end Aiur

end -- @[expose] public section
