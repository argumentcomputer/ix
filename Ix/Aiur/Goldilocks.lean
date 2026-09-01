module

public section

namespace Aiur

abbrev gSize : UInt64 := 1 - 2 ^ 32
abbrev G := { u : UInt64 // u < gSize }

abbrev G.extensionDegree : Nat := 2

/-- Checked embedding: `none` iff the constant does not fit the field
(constants are exact naturals; overflow means the field is not good for
the circuit and must be an error at the consumer, never a wrap). -/
def G.ofNat? (n : Nat) : Option G :=
  if h : n < gSize.toNat then
    some ⟨n.toUInt64, by
      have : n.toUInt64.toNat = n := Nat.mod_eq_of_lt (Nat.lt_trans h (by decide))
      simp [UInt64.lt_iff_toNat_lt, this, h]⟩
  else none

def G.ofNat (n : Nat) : G :=
  -- Reduce in `Nat` BEFORE narrowing: `toUInt64` wraps mod 2^64, which is
  -- NOT reduction mod p — narrowing first silently corrupts any value
  -- ≥ 2^64 (e.g. products in `Mul`, sums in `Add`/`Sub`, the `pow` chain
  -- behind `G.inverse`). After `% gSize.toNat` the value fits `UInt64`
  -- exactly, so the branch below is always true; it is kept (rather than
  -- proved) to avoid a proof obligation on the numeral.
  let n := (n % gSize.toNat).toUInt64
  if h : n < gSize then ⟨n, h⟩
  else ⟨n % gSize, UInt64.mod_lt n (by decide)⟩

instance : OfNat G n := ⟨G.ofNat n⟩

@[inline] def G.ofUInt8 (u8 : UInt8) : G :=
  let u64 := u8.toUInt64
  have h : u64 < gSize := by
    have lt256 : u64 < 256 := by
      simpa [u64, UInt64.lt_iff_toNat_lt, UInt8.toNat_toUInt64] using UInt8.toNat_lt _
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

/-- u8 multiplication returns `(low byte, high byte)`. -/
def G.u8Mul (a b : G) : G × G :=
  (G.ofNat ((a.n * b.n) % 256), G.ofNat ((a.n * b.n) / 256))

/-- u8 subtraction returns `(result % 256, borrow)`. -/
def G.u8Sub (a b : G) : G × G :=
  (G.ofNat ((a.n + 256 - b.n) % 256), if a.n < b.n then 1 else 0)

def G.u8ShiftLeft  (a : G) : G := G.ofNat ((a.n * 2) % 256)
def G.u8ShiftRight (a : G) : G := G.ofNat (a.n / 2)

/-- Bit decomposition: returns an 8-element array (LSB first). -/
def G.u8BitDecomposition (a : G) : Fin 8 → G :=
  fun i => G.ofNat ((a.n >>> i.val) &&& 1)

def G.u32LessThan (a b : G) : G := if a.n < b.n then 1 else 0

/-- The 8 little-endian bytes of the canonical `u64` value. Semantic model of
the `unconstrained_g_to_bytes` hint. -/
def G.toLeBytes (a : G) : Fin 8 → G :=
  fun i => G.ofUInt8 (a.val >>> (8 * i.val).toUInt64).toUInt8

/-- Canonical little-endian u64 limbs of a natural number, each limb as its
8 LE bytes (as field elements). Semantic model of the limb lists the
`unconstrained_big_uint_div_mod` runtime builds (`biguint_to_klimbs_u64` in
`crates/aiur/src/execute.rs`): zero is the empty list, no trailing zero
limbs. -/
def natToLimbsLE (n : Nat) : List (Array G) :=
  if h : n = 0 then []
  else
    let limb := n % 2^64
    let bytes := Array.ofFn fun (i : Fin 8) => G.ofNat ((limb >>> (8 * i.val)) % 256)
    bytes :: natToLimbsLE (n / 2^64)
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide : (1 : Nat) < 2^64)

/-- Value of one 8-LE-byte limb. Inverse direction of `natToLimbsLE`'s
per-limb encoding; bytes are assumed already validated `< 256`. -/
def limbBytesVal (bytes : Array G) : Nat :=
  (bytes.toList.zipIdx.map fun (b, i) => b.val.toNat <<< (8 * i)).foldl (· + ·) 0

/-- Value of a head-first (little-endian) u64 limb list. -/
def limbsVal (limbs : List (Array G)) : Nat :=
  limbs.foldr (fun limb acc => limbBytesVal limb + acc <<< 64) 0

/-- Exponentiation by squaring. Fuel-structural (64 bits covers any `n < 2⁶⁴`
exponent, in particular `p − 2`). -/
def G.pow (x : G) (n : Nat) : G := go n 64 where
  go (n fuel : Nat) : G := match fuel with
    | 0 => 1
    | fuel + 1 =>
      if n == 0 then 1
      else
        let h := go (n / 2) fuel
        let sq := h * h
        if n % 2 == 0 then sq else sq * x

/-- Fermat inverse `x^(p−2)`, with `0 ↦ 0`. Semantic model of the
`unconstrained_g_inverse` hint. -/
def G.inverse (x : G) : G := G.pow x (gSize.toNat - 2)

theorem G.one_ne_zero : ¬(1 : G) = (0 : G) := by decide

theorem G.add_comm (a b : G) : a + b = b + a := by
  show G.ofNat (a.val.toNat + b.val.toNat) = G.ofNat (b.val.toNat + a.val.toNat)
  congr 1; omega

theorem G.mul_comm (a b : G) : a * b = b * a := by
  show G.ofNat (a.val.toNat * b.val.toNat) = G.ofNat (b.val.toNat * a.val.toNat)
  congr 1; exact Nat.mul_comm _ _

end Aiur

end
