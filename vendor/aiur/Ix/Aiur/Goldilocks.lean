module

public section

namespace Aiur

abbrev gSize : UInt64 := 1 - 2 ^ 32
abbrev G := { u : UInt64 // u < gSize }

abbrev G.extensionDegree : Nat := 2

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

/-- Canonical natural-number semantics for counter certificates. -/
theorem G.ofNat_n (n : Nat) : (G.ofNat n).n = n % gSize.toNat := by
  have hp : 0 < gSize.toNat := by decide
  have hp64 : gSize.toNat < 2 ^ 64 := by decide
  have hn : n % gSize.toNat < gSize.toNat := Nat.mod_lt n hp
  have hn64 : n % gSize.toNat < 2 ^ 64 := by omega
  have hval : ((n % gSize.toNat).toUInt64).toNat = n % gSize.toNat := by
    simp [Nat.mod_eq_of_lt hn64]
  have hlt : (n % gSize.toNat).toUInt64 < gSize := by
    simpa only [UInt64.lt_iff_toNat_lt, hval] using hn
  simp only [G.ofNat, dif_pos hlt, G.n, hval]

theorem G.add_one_n (a : G) : (a + 1).n = (a.n + 1) % gSize.toNat := by
  change (G.ofNat (a.n + (1 : G).n)).n = _
  rw [G.ofNat_n]
  rfl

theorem G.sub_one_add_one (a : G) : (a - 1) + 1 = a := by
  apply Subtype.ext
  apply UInt64.toNat.inj
  change ((a - 1) + 1).n = a.n
  rw [G.add_one_n]
  have subval : (a - 1).n = (a.n + gSize.toNat - 1) % gSize.toNat := by
    change (G.ofNat (a.n + gSize.toNat - (1 : G).n)).n = _
    rw [G.ofNat_n]
    rfl
  rw [subval]
  have ha : a.n < gSize.toNat := by
    simpa only [G.n, UInt64.lt_iff_toNat_lt] using a.property
  have hp : 0 < gSize.toNat := by decide
  by_cases hz : a.n = 0
  · rw [hz]
    have hpred : gSize.toNat - 1 < gSize.toNat := by omega
    simp only [Nat.zero_add, Nat.mod_eq_of_lt hpred]
    have heq : gSize.toNat - 1 + 1 = gSize.toNat := by omega
    rw [heq, Nat.mod_self]
  · have hge : gSize.toNat ≤ a.n + gSize.toNat - 1 := by omega
    have heq : a.n + gSize.toNat - 1 - gSize.toNat = a.n - 1 := by omega
    have hpred : a.n - 1 < gSize.toNat := by omega
    rw [Nat.mod_eq_sub_mod hge, heq, Nat.mod_eq_of_lt hpred]
    have hsucc : a.n - 1 + 1 = a.n := by omega
    rw [hsucc, Nat.mod_eq_of_lt ha]

theorem G.add_n (a b : G) : (a + b).n = (a.n + b.n) % gSize.toNat := by
  change (G.ofNat (a.n + b.n)).n = _
  exact G.ofNat_n _

theorem G.sub_n (a b : G) : (a - b).n = (a.n + gSize.toNat - b.n) % gSize.toNat := by
  change (G.ofNat (a.n + gSize.toNat - b.n)).n = _
  exact G.ofNat_n _

set_option maxHeartbeats 20000 in
set_option maxRecDepth 3000 in
theorem G.add_neg_one_eq_sub (a : G) : a + ((0 : G) - 1) = a - 1 := by
  apply Subtype.ext
  apply UInt64.toNat.inj
  change (a + ((0 : G) - 1)).n = (a - 1).n
  rw [G.add_n, G.sub_n, G.sub_n]
  have hzero : (0 : G).n = 0 := rfl
  have hone : (1 : G).n = 1 := rfl
  rw [hzero, hone, Nat.zero_add]
  have hp : 0 < gSize.toNat := by decide
  have hmod : (gSize.toNat - 1) % gSize.toNat = gSize.toNat - 1 :=
    Nat.mod_eq_of_lt (by omega)
  calc
    _ = (a.n + (gSize.toNat - 1)) % gSize.toNat :=
      congrArg (fun n => (a.n + n) % gSize.toNat) hmod
    _ = _ := congrArg (fun n => n % gSize.toNat) (by omega)


end Aiur

end
