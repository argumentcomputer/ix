import Ix.Cert.Compression.Plonkish
import Aiur.Library.U32.Goldilocks

/-! # Goldilocks-in-BN254 Plonkish Circuit-to-Circuit Compiler

Formalization and soundness proofs for `crates/proof-compression/src/foreign.rs`
(`src/foreign/interval.rs`, `src/foreign/quotient.rs`):
1. Moduli and field definitions (`goldilocksP`, `bn254FrModulus`, `GoldilocksF`,
   `BN254Fr`, `goldilocksP_lt_bn254FrModulus`, `two_pow_194_lt_bn254FrModulus`).
2. Signed coefficients (`signedCoeff`, `signedCoeff_mod_eq`, `abs_signedCoeff_le`)
   and interval arithmetic (`Interval`, `InInterval`, `Interval.add`, `Interval.scale`,
   `Interval.mulNonneg`, `GatePlan`, `arithmeticRange`, `selectionRange`).
3. Canonical 16-bit limb decomposition check (`canonical_iff_lt_goldilocksP`).
4. Direct and quotient gate soundness (`direct_gate_sound`, `quotient_gate_sound`).
5. End-to-end Goldilocks-to-BN254 compiler `foreignCompile` and universal soundness
   theorem `foreign_compile_sound`.
-/

namespace Ix.Cert.Compression.Foreign

open Ix.Cert.Compression.Plonkish

/-! ## 1. Moduli & Field Definitions -/

/-- The Goldilocks prime $p = 2^{64} - 2^{32} + 1 = \text{0xffffffff00000001}$. -/
abbrev goldilocksP : Nat := 0xffffffff00000001

/-- The BN254 scalar field modulus $r > 2^{253}$. -/
abbrev bn254FrModulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- The Goldilocks prime field $\mathbb{F}_p$. -/
abbrev GoldilocksF : Type := Aiur.Library.U32.Goldilocks.F

/-- Construct a `GoldilocksF` element from a natural number. -/
abbrev GoldilocksF.ofNat (n : Nat) : GoldilocksF := (n : GoldilocksF)

theorem goldilocksP_lt_bn254FrModulus : goldilocksP < bn254FrModulus := by decide

theorem two_pow_194_lt_bn254FrModulus : 2 ^ 194 < bn254FrModulus := by decide

theorem two_pow_253_lt_bn254FrModulus : 2 ^ 253 < bn254FrModulus := by decide

theorem two_mul_goldilocksP_lt_bn254FrModulus : 2 * goldilocksP < bn254FrModulus := by decide

/-! ### Primality Certificate for `bn254FrModulus` -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem prime_405928799 : Nat.Prime 405928799 := by
  apply lucas_primality 405928799 (22 : ZMod 405928799)
  · reduce_mod_char
  · intro q hq hd
    have factors : 405928799 - 1 = 2 * 11 * 3691 * 4999 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem prime_12048837557 : Nat.Prime 12048837557 := by
  apply lucas_primality 12048837557 (2 : ZMod 12048837557)
  · reduce_mod_char
  · intro q hq hd
    have factors : 12048837557 - 1 = 2 ^ 2 * 7 ^ 2 * 661 * 93001 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      try replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem prime_5156902474397 : Nat.Prime 5156902474397 := by
  apply lucas_primality 5156902474397 (2 : ZMod 5156902474397)
  · reduce_mod_char
  · intro q hq hd
    have factors : 5156902474397 - 1 = 2 ^ 2 * 107 * 12048837557 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_12048837557] at hd
      subst q; reduce_mod_char; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem prime_1670836401704629 : Nat.Prime 1670836401704629 := by
  apply lucas_primality 1670836401704629 (2 : ZMod 1670836401704629)
  · reduce_mod_char
  · intro q hq hd
    have factors : 1670836401704629 - 1 = 2 ^ 2 * 3 ^ 4 * 5156902474397 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_5156902474397] at hd
      subst q; reduce_mod_char; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem prime_639533339 : Nat.Prime 639533339 := by
  apply lucas_primality 639533339 (2 : ZMod 639533339)
  · reduce_mod_char
  · intro q hq hd
    have factors : 639533339 - 1 = 2 * 229 * 853 * 1637 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    all_goals
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q
      reduce_mod_char
      decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem prime_65865678001877903 : Nat.Prime 65865678001877903 := by
  apply lucas_primality 65865678001877903 (5 : ZMod 65865678001877903)
  · reduce_mod_char
  · intro q hq hd
    have factors : 65865678001877903 - 1 = 2 * 83 * 379 * 1637 * 639533339 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_639533339] at hd
      subst q; reduce_mod_char; decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem prime_13818364434197438864469338081 :
    Nat.Prime 13818364434197438864469338081 := by
  apply lucas_primality 13818364434197438864469338081
    (3 : ZMod 13818364434197438864469338081)
  · reduce_mod_char
  · intro q hq hd
    have factors : 13818364434197438864469338081 - 1 =
        2 ^ 5 * 5 * 823 * 1593227 * 65865678001877903 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_65865678001877903] at hd
      subst q; reduce_mod_char; decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
theorem bn254FrModulus_prime : Nat.Prime bn254FrModulus := by
  apply lucas_primality bn254FrModulus (5 : ZMod bn254FrModulus)
  · reduce_mod_char
  · intro q hq hd
    have factors : bn254FrModulus - 1 =
        2 ^ 28 * 3 ^ 2 * 13 * 29 * 983 * 11003 * 237073 * 405928799 *
        1670836401704629 * 13818364434197438864469338081 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_405928799] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_1670836401704629] at hd
      subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_13818364434197438864469338081] at hd
      subst q; reduce_mod_char; decide

instance : Fact (Nat.Prime bn254FrModulus) := ⟨bn254FrModulus_prime⟩

/-- The BN254 scalar prime field $\mathbb{F}_r$. -/
abbrev BN254Fr : Type := ZMod bn254FrModulus

/-- Canonical natural value in $[0, r)$ of a `BN254Fr` element. -/
abbrev BN254Fr.val (x : BN254Fr) : Nat := ZMod.val x

/-! ## 2. Signed Coefficients & Interval Arithmetic (`src/foreign/interval.rs`) -/

/-- Centered signed representative of a canonical Goldilocks element $x \in [0, p)$:
`x` if $x \le p / 2$, else $x - p$. -/
def signedCoeff (x : Nat) : Int :=
  if x <= goldilocksP / 2 then Int.ofNat x else Int.ofNat x - Int.ofNat goldilocksP

/-- `signedCoeff x` is congruent to `x` modulo `goldilocksP`. -/
theorem signedCoeff_mod_eq (x : Nat) :
    signedCoeff x ≡ Int.ofNat x [ZMOD Int.ofNat goldilocksP] := by
  unfold signedCoeff
  split
  · exact Int.ModEq.refl _
  · rw [Int.modEq_iff_dvd]
    refine ⟨1, ?_⟩
    omega

/-- For any canonical $x < p$, $|signedCoeff(x)| \le p / 2$. -/
theorem abs_signedCoeff_le (x : Nat) (hx : x < goldilocksP) :
    |signedCoeff x| ≤ Int.ofNat (goldilocksP / 2) := by
  rw [abs_le]
  unfold signedCoeff goldilocksP at *
  simp only [Int.ofNat_eq_natCast]
  split <;> constructor <;> omega

/-- Casting `signedCoeff (ZMod.val c)` back to `GoldilocksF` recovers `c`. -/
theorem signedCoeff_cast_goldilocks (c : GoldilocksF) :
    ((signedCoeff (ZMod.val c) : Int) : GoldilocksF) = c := by
  unfold signedCoeff
  simp only [Int.ofNat_eq_natCast]
  split
  · exact ZMod.natCast_zmod_val c
  · push_cast
    have hp : (18446744069414584321 : GoldilocksF) = 0 := rfl
    rw [ZMod.natCast_zmod_val, hp, sub_zero]

/-- Closed integer interval `[min, max]`. -/
structure Interval where
  min : Int
  max : Int
  deriving Repr, DecidableEq

/-- Membership of `v : Int` in `I : Interval`. -/
def InInterval (v : Int) (I : Interval) : Prop :=
  I.min ≤ v ∧ v ≤ I.max

abbrev Interval.InInterval (v : Int) (I : Interval) : Prop :=
  Foreign.InInterval v I

/-- Interval addition. -/
def Interval.add (I₁ I₂ : Interval) : Interval :=
  { min := I₁.min + I₂.min, max := I₁.max + I₂.max }

theorem Interval.add_sound {v₁ v₂ : Int} {I₁ I₂ : Interval}
    (h₁ : InInterval v₁ I₁) (h₂ : InInterval v₂ I₂) :
    InInterval (v₁ + v₂) (Interval.add I₁ I₂) := by
  rcases h₁ with ⟨h1l, h1u⟩
  rcases h₂ with ⟨h2l, h2u⟩
  exact ⟨Int.add_le_add h1l h2l, Int.add_le_add h1u h2u⟩

/-- Interval scaling by a signed integer coefficient `c`. -/
def Interval.scale (c : Int) (I : Interval) : Interval :=
  if 0 ≤ c then
    { min := c * I.min, max := c * I.max }
  else
    { min := c * I.max, max := c * I.min }

theorem Interval.scale_sound (c v : Int) (I : Interval) (h : InInterval v I) :
    InInterval (c * v) (Interval.scale c I) := by
  rcases h with ⟨hl, hu⟩
  unfold InInterval Interval.scale
  split
  · next hc =>
    exact ⟨Int.mul_le_mul_of_nonneg_left hl hc, Int.mul_le_mul_of_nonneg_left hu hc⟩
  · next hc =>
    exact ⟨by nlinarith, by nlinarith⟩

/-- Interval for the product of two non-negative integers bounded by `b₁` and `b₂`. -/
def Interval.mulNonneg (b₁ b₂ : Nat) : Interval :=
  { min := 0, max := Int.ofNat b₁ * Int.ofNat b₂ }

theorem Interval.mulNonneg_sound {a b : Nat} {b₁ b₂ : Nat}
    (ha : a ≤ b₁) (hb : b ≤ b₂) :
    InInterval (Int.ofNat a * Int.ofNat b) (Interval.mulNonneg b₁ b₂) := by
  change 0 ≤ Int.ofNat a * Int.ofNat b ∧ Int.ofNat a * Int.ofNat b ≤ Int.ofNat b₁ * Int.ofNat b₂
  simp only [Int.ofNat_eq_natCast]
  exact ⟨by positivity, by exact_mod_cast Nat.mul_le_mul ha hb⟩

/-- The integer polynomial evaluated by a translated Plonkish gate:
`E(a, b, c) = qm * a * b + qa * a + qb * b + qc * c + k`. -/
def gateIntExpr (qm qa qb qc k a b c : Int) : Int :=
  qm * a * b + qa * a + qb * b + qc * c + k

/-- Interval bound for `gateIntExpr qm qa qb qc k a b c` given `0 ≤ a ≤ ba`,
`0 ≤ b ≤ bb`, `0 ≤ c ≤ bc` (`src/foreign/interval.rs`). -/
def gateInterval (qm qa qb qc k : Int) (ba bb bc : Nat) : Interval :=
  let Im := Interval.scale qm (Interval.mulNonneg ba bb)
  let Ia := Interval.scale qa { min := 0, max := Int.ofNat ba }
  let Ib := Interval.scale qb { min := 0, max := Int.ofNat bb }
  let Ic := Interval.scale qc { min := 0, max := Int.ofNat bc }
  let Ik : Interval := { min := k, max := k }
  Interval.add (Interval.add (Interval.add (Interval.add Im Ia) Ib) Ic) Ik

theorem gateInterval_sound (qm qa qb qc k : Int) {a b c ba bb bc : Nat}
    (ha : a ≤ ba) (hb : b ≤ bb) (hc : c ≤ bc) :
    InInterval (gateIntExpr qm qa qb qc k (Int.ofNat a) (Int.ofNat b) (Int.ofNat c))
      (gateInterval qm qa qb qc k ba bb bc) := by
  have hm := Interval.scale_sound qm (Int.ofNat a * Int.ofNat b)
    (Interval.mulNonneg ba bb) (Interval.mulNonneg_sound ha hb)
  have h1 := Interval.scale_sound qa (Int.ofNat a) { min := 0, max := Int.ofNat ba }
    ⟨Int.natCast_nonneg a, Int.ofNat_le.mpr ha⟩
  have h2 := Interval.scale_sound qb (Int.ofNat b) { min := 0, max := Int.ofNat bb }
    ⟨Int.natCast_nonneg b, Int.ofNat_le.mpr hb⟩
  have h3 := Interval.scale_sound qc (Int.ofNat c) { min := 0, max := Int.ofNat bc }
    ⟨Int.natCast_nonneg c, Int.ofNat_le.mpr hc⟩
  have hk : InInterval k { min := k, max := k } := ⟨Int.le_refl k, Int.le_refl k⟩
  have hsum := Interval.add_sound
    (Interval.add_sound (Interval.add_sound (Interval.add_sound hm h1) h2) h3) hk
  have heq : qm * (Int.ofNat a * Int.ofNat b) + qa * Int.ofNat a +
      qb * Int.ofNat b + qc * Int.ofNat c + k =
      gateIntExpr qm qa qb qc k (Int.ofNat a) (Int.ofNat b) (Int.ofNat c) := by
    unfold gateIntExpr
    ring
  rwa [heq] at hsum

/-- Gate translation plan (`src/foreign/interval.rs:GatePlan`):
either `Direct` (when `(-P, P)` contains `I`) or `Quotient offset bits`. -/
inductive GatePlan where
  | Direct
  | Quotient (offset : Nat) (bits : Nat)
  deriving Repr, DecidableEq

/-- Validity of a `GatePlan` for an interval `I`. -/
def GatePlan.Valid (plan : GatePlan) (I : Interval) : Prop :=
  match plan with
  | .Direct => -(Int.ofNat goldilocksP) < I.min ∧ I.max < Int.ofNat goldilocksP
  | .Quotient offset bits =>
      offset % goldilocksP = 0 ∧
      0 ≤ I.min + Int.ofNat offset ∧
      I.max + Int.ofNat offset < Int.ofNat (2 ^ bits * goldilocksP) ∧
      bits ≤ 144

/-- Acyclic arithmetic range (`src/foreign.rs:207-218`): computes the interval of
`qm * a * b + qa * a + qb * b + k` solving for wire `c` (`qc = -1`), with the
special boolean-subtraction refinement `a - bit * a ∈ [0, ba]` when `bb ≤ 1`. -/
def arithmeticRange (qm qa qb k : Int) (ba bb : Nat) : Interval :=
  if qm == -1 && qa == 1 && qb == 0 && k == 0 && bb <= 1 then
    { min := 0, max := Int.ofNat ba }
  else
    gateInterval qm qa qb 0 k ba bb 0

theorem arithmeticRange_sound (qm qa qb k : Int) {a b ba bb : Nat}
    (ha : a ≤ ba) (hb : b ≤ bb) :
    InInterval (qm * Int.ofNat a * Int.ofNat b + qa * Int.ofNat a + qb * Int.ofNat b + k)
      (arithmeticRange qm qa qb k ba bb) := by
  unfold arithmeticRange
  split
  · next hcond =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
    rcases hcond with ⟨⟨⟨⟨hqm, hqa⟩, hqb⟩, hk⟩, hbb⟩
    subst hqm hqa hqb hk
    unfold InInterval
    simp only [Int.ofNat_eq_natCast]
    rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl <;> omega
  · have h := gateInterval_sound qm qa qb 0 k ha hb (Nat.le_refl 0)
    unfold gateIntExpr at h
    simpa using h

/-- Selection range (`src/foreign.rs:220-254`): for `bit ∈ {0, 1}`,
`bit * yes + (1 - bit) * no` lies in `[0, max(bYes, bNo)]`. -/
def selectionRange (bYes bNo : Nat) : Interval :=
  { min := 0, max := Int.ofNat (Nat.max bYes bNo) }

theorem selectionRange_sound {bit yes no bYes bNo : Nat}
    (hbit : bit ≤ 1) (hyes : yes ≤ bYes) (hno : no ≤ bNo) :
    InInterval (Int.ofNat bit * Int.ofNat yes + (1 - Int.ofNat bit) * Int.ofNat no)
      (selectionRange bYes bNo) := by
  have h1 : yes ≤ Nat.max bYes bNo := Nat.le_trans hyes (Nat.le_max_left bYes bNo)
  have h2 : no ≤ Nat.max bYes bNo := Nat.le_trans hno (Nat.le_max_right bYes bNo)
  unfold InInterval selectionRange
  dsimp only
  simp only [Int.ofNat_eq_natCast]
  rcases (by omega : bit = 0 ∨ bit = 1) with rfl | rfl <;> omega

/-- Boolean gate `x^2 - x = 0` in `BN254Fr` implies `ZMod.val x ≤ 1`. -/
theorem booleanBound_sound (x : BN254Fr) (h : x * x - x = 0) :
    ZMod.val x ≤ 1 := by
  have hprod : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hprod with hx0 | hx1
  · rw [hx0, ZMod.val_zero]; omega
  · have hx1' : x = 1 := sub_eq_zero.mp hx1
    rw [hx1', ZMod.val_one]

/-- Membership of `u : UInt8` cast into `BN254Fr` gives canonical bound `≤ 255`. -/
theorem blake3ByteBound_sound (u : UInt8) :
    ZMod.val (u.toNat : BN254Fr) ≤ 255 := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  · have := u.toNat_lt
    omega
  · have := u.toNat_lt
    unfold bn254FrModulus
    omega

/-! ## 3. Canonical Goldilocks Check (`canonical`, `src/foreign.rs:398-422`) -/

/-- Reconstruct a 64-bit integer from four 16-bit limbs `lo0, lo1, hi0, hi1`. -/
def reconstructU64FromU16 (lo0 lo1 hi0 hi1 : Nat) : Nat :=
  lo0 + 2 ^ 16 * lo1 + 2 ^ 32 * hi0 + 2 ^ 48 * hi1

/-- The canonical Goldilocks high/low word check (`hi = 0xffffffff → lo = 0`). -/
def CanonicalHighLowCheck (lo0 lo1 hi0 hi1 : Nat) : Prop :=
  hi0 + 2 ^ 16 * hi1 = 0xffffffff → lo0 + 2 ^ 16 * lo1 = 0

/-- **Canonical Goldilocks 16-Bit Limb Theorem (`canonical_iff_lt_goldilocksP`)**:
For any four 16-bit limbs `lo0, lo1, hi0, hi1 < 2^16`, the constraint
`(hi0 + 2^16 * hi1 = 0xffffffff → lo0 + 2^16 * lo1 = 0)` holds if and only if
`reconstructU64FromU16 lo0 lo1 hi0 hi1 < goldilocksP`. -/
theorem canonical_iff_lt_goldilocksP (lo0 lo1 hi0 hi1 : Nat)
    (hlo0 : lo0 < 2 ^ 16) (hlo1 : lo1 < 2 ^ 16)
    (hhi0 : hi0 < 2 ^ 16) (hhi1 : hi1 < 2 ^ 16) :
    CanonicalHighLowCheck lo0 lo1 hi0 hi1 ↔
      reconstructU64FromU16 lo0 lo1 hi0 hi1 < goldilocksP := by
  unfold CanonicalHighLowCheck reconstructU64FromU16 goldilocksP
  omega

/-! ## 4. Direct & Quotient Gate Soundness (`constrain_gate`, `src/foreign.rs:695-738`) -/

/-- Any integer `D` divisible by `R > 0` with `-R < D < R` must be `0` in `ℤ`. -/
theorem int_eq_zero_of_dvd_of_lt {D R : Int} (hdvd : R ∣ D)
    (hlow : -R < D) (hhigh : D < R) : D = 0 := by
  rcases hdvd with ⟨k, rfl⟩
  have hk : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hk1 : k ≤ -1 := by omega
      have hR : 0 < R := by omega
      have : R * k ≤ R * (-1) := Int.mul_le_mul_of_nonneg_left hk1 (by omega)
      omega
    · have hk1 : 1 ≤ k := by omega
      have hR : 0 < R := by omega
      have : R * 1 ≤ R * k := Int.mul_le_mul_of_nonneg_left hk1 (by omega)
      omega
  simp [hk]

/-- **Direct Gate Soundness (`direct_gate_sound`)**:
If $E(a,b,c) = q_m a b + q_a a + q_b b + q_c c + k \in (-P, P)$ in $\mathbb{Z}$ and
$E(a,b,c) \equiv 0 \pmod{R}$ (where $R = \text{bn254FrModulus} > 2P$), then
$E(a,b,c) = 0$ in $\mathbb{Z}$ and therefore $E(a,b,c) \equiv 0 \pmod{P}$. -/
theorem direct_gate_sound (qm qa qb qc k a b c : Int)
    (hlow : -(Int.ofNat goldilocksP) < gateIntExpr qm qa qb qc k a b c)
    (hhigh : gateIntExpr qm qa qb qc k a b c < Int.ofNat goldilocksP)
    (hmodR : gateIntExpr qm qa qb qc k a b c ≡ 0 [ZMOD Int.ofNat bn254FrModulus]) :
    gateIntExpr qm qa qb qc k a b c = 0 ∧
      gateIntExpr qm qa qb qc k a b c ≡ 0 [ZMOD Int.ofNat goldilocksP] := by
  have hPR : Int.ofNat goldilocksP < Int.ofNat bn254FrModulus := by
    exact Int.ofNat_lt.mpr goldilocksP_lt_bn254FrModulus
  have hdvd : Int.ofNat bn254FrModulus ∣ gateIntExpr qm qa qb qc k a b c :=
    Int.modEq_zero_iff_dvd.mp hmodR
  have heq0 : gateIntExpr qm qa qb qc k a b c = 0 :=
    int_eq_zero_of_dvd_of_lt hdvd (by omega) (by omega)
  refine ⟨heq0, ?_⟩
  rw [heq0]

/-- Reconstruct a quotient integer from up to 9 16-bit limbs $q_0, \dots, q_8 \in [0, 2^{16})$. -/
def reconstructQuotient9 (q0 q1 q2 q3 q4 q5 q6 q7 q8 : Nat) : Nat :=
  q0 + 2 ^ 16 * q1 + 2 ^ 32 * q2 + 2 ^ 48 * q3 + 2 ^ 64 * q4 +
  2 ^ 80 * q5 + 2 ^ 96 * q6 + 2 ^ 112 * q7 + 2 ^ 128 * q8

theorem reconstructQuotient9_lt (q0 q1 q2 q3 q4 q5 q6 q7 q8 : Nat)
    (h0 : q0 < 2 ^ 16) (h1 : q1 < 2 ^ 16) (h2 : q2 < 2 ^ 16)
    (h3 : q3 < 2 ^ 16) (h4 : q4 < 2 ^ 16) (h5 : q5 < 2 ^ 16)
    (h6 : q6 < 2 ^ 16) (h7 : q7 < 2 ^ 16) (h8 : q8 < 2 ^ 16) :
    reconstructQuotient9 q0 q1 q2 q3 q4 q5 q6 q7 q8 < 2 ^ 144 := by
  unfold reconstructQuotient9
  omega

/-- **Quotient Gate Soundness (`quotient_gate_sound`)**:
If $0 \le E(a,b,c) + \text{offset} < R$, $q' < 2^{144}$ (reconstructed from $m \le 9$
16-bit limbs), $\text{offset} \equiv 0 \pmod{P}$, and
$E(a,b,c) + \text{offset} - P \cdot q' \equiv 0 \pmod{R}$, then
$E(a,b,c) + \text{offset} = P \cdot q'$ in $\mathbb{Z}$, and hence
$E(a,b,c) \equiv 0 \pmod{P}$. -/
theorem quotient_gate_sound (qm qa qb qc k a b c : Int) (offset q' : Nat)
    (hnonneg : 0 ≤ gateIntExpr qm qa qb qc k a b c + Int.ofNat offset)
    (hupper : gateIntExpr qm qa qb qc k a b c + Int.ofNat offset < Int.ofNat bn254FrModulus)
    (hq : q' < 2 ^ 144)
    (hoffset : offset % goldilocksP = 0)
    (hmodR : gateIntExpr qm qa qb qc k a b c + Int.ofNat offset -
      Int.ofNat goldilocksP * Int.ofNat q' ≡ 0 [ZMOD Int.ofNat bn254FrModulus]) :
    gateIntExpr qm qa qb qc k a b c + Int.ofNat offset =
      Int.ofNat goldilocksP * Int.ofNat q' ∧
    gateIntExpr qm qa qb qc k a b c ≡ 0 [ZMOD Int.ofNat goldilocksP] := by
  have hPq_lt : Int.ofNat goldilocksP * Int.ofNat q' < Int.ofNat bn254FrModulus := by
    simp only [Int.ofNat_eq_natCast]
    unfold goldilocksP bn254FrModulus
    omega
  have hPq_nonneg : 0 ≤ Int.ofNat goldilocksP * Int.ofNat q' := by
    simp only [Int.ofNat_eq_natCast]
    unfold goldilocksP
    omega
  have hdvd : Int.ofNat bn254FrModulus ∣
      (gateIntExpr qm qa qb qc k a b c + Int.ofNat offset -
        Int.ofNat goldilocksP * Int.ofNat q') :=
    Int.modEq_zero_iff_dvd.mp hmodR
  have hdiff0 : gateIntExpr qm qa qb qc k a b c + Int.ofNat offset -
      Int.ofNat goldilocksP * Int.ofNat q' = 0 :=
    int_eq_zero_of_dvd_of_lt hdvd (by omega) (by omega)
  have heq : gateIntExpr qm qa qb qc k a b c + Int.ofNat offset =
      Int.ofNat goldilocksP * Int.ofNat q' := by omega
  refine ⟨heq, ?_⟩
  rw [Int.modEq_zero_iff_dvd]
  have hdiv_off : (goldilocksP : Int) ∣ Int.ofNat offset := by
    exact Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero hoffset)
  rcases hdiv_off with ⟨m, hm⟩
  refine ⟨Int.ofNat q' - m, ?_⟩
  simp only [Int.ofNat_eq_natCast] at heq hm ⊢
  rw [mul_sub, ← hm]
  omega

/-! ## 5. End-to-End Foreign Compiler (`foreignCompile` & `foreign_compile_sound`) -/

/-- Universal offset $(P^2 + 4P) \cdot P$, which is a multiple of $P$ and guarantees
$0 \le E(a,b,c) + \text{offset} < 2^{144} P < R$ for every Goldilocks gate with
canonical inputs $a, b, c < P$ and centered coefficients $|q_*| \le P / 2$. -/
def universalGateOffset : Nat :=
  (goldilocksP * goldilocksP + 4 * goldilocksP) * goldilocksP

theorem universalGateOffset_mod : universalGateOffset % goldilocksP = 0 := by
  unfold universalGateOffset
  exact Nat.mul_mod_left _ _

theorem abs_mul_nonneg_bounds {q x B M : Int}
    (hq : |q| ≤ B) (hx0 : 0 ≤ x) (hxM : x ≤ M) (hB : 0 ≤ B) :
    -(B * M) ≤ q * x ∧ q * x ≤ B * M := by
  rcases abs_le.mp hq with ⟨hq_lo, hq_hi⟩
  refine ⟨?_, ?_⟩
  · have h1 : (-B) * x ≤ q * x := Int.mul_le_mul_of_nonneg_right hq_lo hx0
    have h2 : B * x ≤ B * M := Int.mul_le_mul_of_nonneg_left hxM hB
    linarith
  · have h1 : q * x ≤ B * x := Int.mul_le_mul_of_nonneg_right hq_hi hx0
    have h2 : B * x ≤ B * M := Int.mul_le_mul_of_nonneg_left hxM hB
    linarith

theorem universalGateExpr_bounds (qm qa qb qc k : GoldilocksF) {a b c : Nat}
    (ha : a < goldilocksP) (hb : b < goldilocksP) (hc : c < goldilocksP) :
    let E := gateIntExpr
      (signedCoeff (ZMod.val qm))
      (signedCoeff (ZMod.val qa))
      (signedCoeff (ZMod.val qb))
      (signedCoeff (ZMod.val qc))
      (signedCoeff (ZMod.val k))
      (Int.ofNat a) (Int.ofNat b) (Int.ofNat c)
    0 ≤ E + Int.ofNat universalGateOffset ∧
      E + Int.ofNat universalGateOffset < Int.ofNat bn254FrModulus := by
  have hqm := abs_signedCoeff_le (ZMod.val qm) (ZMod.val_lt qm)
  have hqa := abs_signedCoeff_le (ZMod.val qa) (ZMod.val_lt qa)
  have hqb := abs_signedCoeff_le (ZMod.val qb) (ZMod.val_lt qb)
  have hqc := abs_signedCoeff_le (ZMod.val qc) (ZMod.val_lt qc)
  have hk := abs_signedCoeff_le (ZMod.val k) (ZMod.val_lt k)
  have ha_le : a ≤ goldilocksP - 1 := by omega
  have hb_le : b ≤ goldilocksP - 1 := by omega
  have hc_le : c ≤ goldilocksP - 1 := by omega
  rcases Interval.mulNonneg_sound ha_le hb_le with ⟨hab0, hab⟩
  unfold Interval.mulNonneg at hab0 hab
  have hB : (0 : Int) ≤ Int.ofNat (goldilocksP / 2) := Int.natCast_nonneg _
  rcases abs_mul_nonneg_bounds hqm hab0 hab hB with ⟨hm_lo, hm_hi⟩
  rcases abs_mul_nonneg_bounds hqa (Int.natCast_nonneg a) (Int.ofNat_le.mpr ha_le) hB with ⟨ha_lo, ha_hi⟩
  rcases abs_mul_nonneg_bounds hqb (Int.natCast_nonneg b) (Int.ofNat_le.mpr hb_le) hB with ⟨hb_lo, hb_hi⟩
  rcases abs_mul_nonneg_bounds hqc (Int.natCast_nonneg c) (Int.ofNat_le.mpr hc_le) hB with ⟨hc_lo, hc_hi⟩
  rcases abs_le.mp hk with ⟨hk_lo, hk_hi⟩
  dsimp only
  unfold gateIntExpr universalGateOffset goldilocksP bn254FrModulus at *
  rw [mul_assoc (signedCoeff (ZMod.val qm))]
  simp only [Int.ofNat_eq_natCast] at *
  omega

/-- The shared 16-bit range table `"u16"` in `BN254Fr` (`src/foreign.rs:503-506`). -/
def u16Entries : List (List BN254Fr) :=
  List.map (fun (v : Nat) => [(v : BN254Fr)]) (List.range (2 ^ 16))

def u16TableSpec : TableSpec BN254Fr :=
  { name := "u16", width := 1, entries := u16Entries }

/-- Translate a source `GoldilocksF` lookup table to `BN254Fr` with `"src:"` namespace prefix. -/
def translateTable (t : TableSpec GoldilocksF) : TableSpec BN254Fr :=
  { name := "src:" ++ t.name
    width := t.width
    entries := t.entries.map (fun row => row.map (fun v => (ZMod.val v : BN254Fr))) }

/-- Translate a source `LookupConstraint` to the `"src:"`-prefixed table namespace. -/
def translateLookup (l : LookupConstraint) : LookupConstraint :=
  { tableName := "src:" ++ l.tableName, wires := l.wires }

theorem src_prefix_ne_u16 (s : String) : "src:" ++ s ≠ "u16" := by
  intro h
  have hlen := congrArg String.length h
  rw [String.length_append] at hlen
  have : "src:".length = 4 := rfl
  have : "u16".length = 3 := rfl
  omega

theorem src_prefix_inj {s₁ s₂ : String} (h : "src:" ++ s₁ = "src:" ++ s₂) : s₁ = s₂ := by
  have hlist := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at hlist
  exact String.ext (List.append_cancel_left hlist)

theorem u16Entries_mem (row : List BN254Fr) :
    row ∈ u16Entries ↔ ∃ v : Nat, v < 2 ^ 16 ∧ [(v : BN254Fr)] = row := by
  unfold u16Entries
  simp only [List.mem_map, List.mem_range]

attribute [irreducible] u16Entries

/-- Any lookup in `"u16"` against `u16TableSpec :: (tables.map translateTable)` enforces
`ZMod.val (w_fr wire) < 2^16`. -/
theorem u16_lookup_val_lt (tables : List (TableSpec GoldilocksF))
    (wire : Wire) (w_fr : Wire → BN254Fr)
    (h : LookupConstraint.Satisfied (u16TableSpec :: tables.map translateTable)
      { tableName := "u16", wires := [wire] } w_fr) :
    ZMod.val (w_fr wire) < 2 ^ 16 := by
  rcases h with ⟨t, ht, hname, hmem⟩
  simp only [List.mem_cons, List.mem_map] at ht
  rcases ht with rfl | ⟨srcT, _, rfl⟩
  · have hmem' : [w_fr wire] ∈ u16Entries := hmem
    rw [u16Entries_mem] at hmem'
    rcases hmem' with ⟨v, hv, heq⟩
    injection heq with hhead _
    rw [← hhead, ZMod.val_natCast, Nat.mod_eq_of_lt]
    · exact hv
    · unfold bn254FrModulus; omega
  · exfalso
    exact src_prefix_ne_u16 srcT.name hname

/-- Helper lemma: if `x = (n : BN254Fr)` and `n < bn254FrModulus`, then `ZMod.val x = n`. -/
theorem val_eq_of_natCast_eq {x : BN254Fr} {n : Nat}
    (heq : x = (n : BN254Fr)) (hlt : n < bn254FrModulus) :
    ZMod.val x = n := by
  rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- The 4 `"u16"` lookups of the canonical Goldilocks check on wire `v` using
auxiliary wires `base .. base + 7`. -/
def canonicalWireLookups (base : Nat) : List LookupConstraint :=
  [ { tableName := "u16", wires := [base] },
    { tableName := "u16", wires := [base + 1] },
    { tableName := "u16", wires := [base + 2] },
    { tableName := "u16", wires := [base + 3] } ]

/-- The 6 degree-2 Plonkish gates of the canonical Goldilocks check on wire `v`
(`src/foreign.rs:398-422`) using auxiliary wires `base .. base + 7`:
- `lo0 = base`, `lo1 = base + 1`, `hi0 = base + 2`, `hi1 = base + 3`
- `lo = base + 4`, `hi = base + 5`, `inv = base + 6`, `max_hi = base + 7` -/
def canonicalWireGates (v base : Nat) : List (Gate BN254Fr) :=
  let lo0 := base
  let lo1 := base + 1
  let hi0 := base + 2
  let hi1 := base + 3
  let lo := base + 4
  let hi := base + 5
  let inv := base + 6
  let max_hi := base + 7
  [ -- Gate 1: lo0 + 2^16 * lo1 - lo = 0
    { a := lo0, b := lo1, c := lo, qm := 0, qa := 1, qb := (2 ^ 16 : BN254Fr), qc := -1, k := 0 },
    -- Gate 2: hi0 + 2^16 * hi1 - hi = 0
    { a := hi0, b := hi1, c := hi, qm := 0, qa := 1, qb := (2 ^ 16 : BN254Fr), qc := -1, k := 0 },
    -- Gate 3: lo + 2^32 * hi - v = 0
    { a := lo, b := hi, c := v, qm := 0, qa := 1, qb := (2 ^ 32 : BN254Fr), qc := -1, k := 0 },
    -- Gate 4: max_hi * max_hi - max_hi = 0
    { a := max_hi, b := max_hi, c := 0, qm := 1, qa := -1, qb := 0, qc := 0, k := 0 },
    -- Gate 5: (hi - 0xffffffff) * inv + max_hi - 1 = 0
    { a := hi, b := inv, c := max_hi, qm := 1, qa := 0, qb := -(0xffffffff : BN254Fr), qc := 1, k := -1 },
    -- Gate 6: max_hi * lo = 0
    { a := max_hi, b := lo, c := 0, qm := 1, qa := 0, qb := 0, qc := 0, k := 0 } ]

/-- Soundness of the 6-gate + 4-lookup canonical Goldilocks gadget:
any assignment `w_fr` satisfying `canonicalWireGates v base` and `canonicalWireLookups base`
satisfies `ZMod.val (w_fr v) < goldilocksP`. -/
theorem canonicalWireGadget_sound (tables : List (TableSpec GoldilocksF))
    (v base : Nat) (w_fr : Wire → BN254Fr)
    (hgates : ∀ g ∈ canonicalWireGates v base, g.Satisfied w_fr)
    (hlookups : ∀ l ∈ canonicalWireLookups base,
      l.Satisfied (u16TableSpec :: tables.map translateTable) w_fr) :
    ZMod.val (w_fr v) < goldilocksP := by
  have hlo0 : ZMod.val (w_fr base) < 2 ^ 16 :=
    u16_lookup_val_lt tables base w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hlo1 : ZMod.val (w_fr (base + 1)) < 2 ^ 16 :=
    u16_lookup_val_lt tables (base + 1) w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hhi0 : ZMod.val (w_fr (base + 2)) < 2 ^ 16 :=
    u16_lookup_val_lt tables (base + 2) w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hhi1 : ZMod.val (w_fr (base + 3)) < 2 ^ 16 :=
    u16_lookup_val_lt tables (base + 3) w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hg1 := hgates
    { a := base, b := base + 1, c := base + 4,
      qm := 0, qa := 1, qb := (2 ^ 16 : BN254Fr), qc := -1, k := 0 }
    (by simp [canonicalWireGates])
  have hg2 := hgates
    { a := base + 2, b := base + 3, c := base + 5,
      qm := 0, qa := 1, qb := (2 ^ 16 : BN254Fr), qc := -1, k := 0 }
    (by simp [canonicalWireGates])
  have hg3 := hgates
    { a := base + 4, b := base + 5, c := v,
      qm := 0, qa := 1, qb := (2 ^ 32 : BN254Fr), qc := -1, k := 0 }
    (by simp [canonicalWireGates])
  have hg5 := hgates
    { a := base + 5, b := base + 6, c := base + 7,
      qm := 1, qa := 0, qb := -(0xffffffff : BN254Fr), qc := 1, k := -1 }
    (by simp [canonicalWireGates])
  have hg6 := hgates
    { a := base + 7, b := base + 4, c := 0,
      qm := 1, qa := 0, qb := 0, qc := 0, k := 0 }
    (by simp [canonicalWireGates])
  unfold Gate.Satisfied Gate.eval at hg1 hg2 hg3 hg5 hg6
  have hlo_eq : w_fr (base + 4) =
      ((ZMod.val (w_fr base) + 2 ^ 16 * ZMod.val (w_fr (base + 1)) : Nat) : BN254Fr) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination -hg1
  have hlo_val : ZMod.val (w_fr (base + 4)) =
      ZMod.val (w_fr base) + 2 ^ 16 * ZMod.val (w_fr (base + 1)) :=
    val_eq_of_natCast_eq hlo_eq (by unfold bn254FrModulus; omega)
  have hhi_eq : w_fr (base + 5) =
      ((ZMod.val (w_fr (base + 2)) + 2 ^ 16 * ZMod.val (w_fr (base + 3)) : Nat) : BN254Fr) := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination -hg2
  have hhi_val : ZMod.val (w_fr (base + 5)) =
      ZMod.val (w_fr (base + 2)) + 2 ^ 16 * ZMod.val (w_fr (base + 3)) :=
    val_eq_of_natCast_eq hhi_eq (by unfold bn254FrModulus; omega)
  have hv_eq : w_fr v =
      ((reconstructU64FromU16 (ZMod.val (w_fr base)) (ZMod.val (w_fr (base + 1)))
        (ZMod.val (w_fr (base + 2))) (ZMod.val (w_fr (base + 3))) : Nat) : BN254Fr) := by
    unfold reconstructU64FromU16
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination -hg3 - hg1 - (2 ^ 32 : BN254Fr) * hg2
  have hv_val : ZMod.val (w_fr v) =
      reconstructU64FromU16 (ZMod.val (w_fr base)) (ZMod.val (w_fr (base + 1)))
        (ZMod.val (w_fr (base + 2))) (ZMod.val (w_fr (base + 3))) :=
    val_eq_of_natCast_eq hv_eq (by unfold reconstructU64FromU16 bn254FrModulus; omega)
  rw [hv_val, ← canonical_iff_lt_goldilocksP _ _ _ _ hlo0 hlo1 hhi0 hhi1]
  intro hhi_max
  have hhi_cast : w_fr (base + 5) = (0xffffffff : BN254Fr) := by
    rw [← ZMod.natCast_zmod_val (w_fr (base + 5)), hhi_val, hhi_max]
    rfl
  have hmax1 : w_fr (base + 7) = 1 := by
    rw [hhi_cast] at hg5
    linear_combination hg5
  have hlo0_fr : w_fr (base + 4) = 0 := by
    rw [hmax1] at hg6
    linear_combination hg6
  rw [← hlo_val, hlo0_fr, ZMod.val_zero]

/-- The 9 `"u16"` lookups for the 144-bit quotient `q'` of a translated gate,
using auxiliary wires `gbase .. gbase + 8`. -/
def translatedGateLookups (gbase : Nat) : List LookupConstraint :=
  [ { tableName := "u16", wires := [gbase] },
    { tableName := "u16", wires := [gbase + 1] },
    { tableName := "u16", wires := [gbase + 2] },
    { tableName := "u16", wires := [gbase + 3] },
    { tableName := "u16", wires := [gbase + 4] },
    { tableName := "u16", wires := [gbase + 5] },
    { tableName := "u16", wires := [gbase + 6] },
    { tableName := "u16", wires := [gbase + 7] },
    { tableName := "u16", wires := [gbase + 8] } ]

/-- The 10 degree-2 Plonkish gates in `BN254Fr` for a translated Goldilocks gate `g`
(`src/foreign.rs:695-738`), using auxiliary wires `gbase .. gbase + 17`:
- `q0 .. q8 = gbase .. gbase + 8` (9 16-bit quotient limbs)
- `acc1 .. acc7 = gbase + 9 .. gbase + 15` (partial limb sums)
- `q_wire = gbase + 16` (reconstructed 144-bit quotient $q'$)
- `t1 = gbase + 17` (intermediate gate linear combination) -/
def translatedGateGates (g : Gate GoldilocksF) (gbase : Nat) : List (Gate BN254Fr) :=
  let qm : BN254Fr := (signedCoeff (ZMod.val g.qm) : BN254Fr)
  let qa : BN254Fr := (signedCoeff (ZMod.val g.qa) : BN254Fr)
  let qb : BN254Fr := (signedCoeff (ZMod.val g.qb) : BN254Fr)
  let qc : BN254Fr := (signedCoeff (ZMod.val g.qc) : BN254Fr)
  let k : BN254Fr := (signedCoeff (ZMod.val g.k) : BN254Fr)
  let q0 := gbase
  let q1 := gbase + 1
  let q2 := gbase + 2
  let q3 := gbase + 3
  let q4 := gbase + 4
  let q5 := gbase + 5
  let q6 := gbase + 6
  let q7 := gbase + 7
  let q8 := gbase + 8
  let acc1 := gbase + 9
  let acc2 := gbase + 10
  let acc3 := gbase + 11
  let acc4 := gbase + 12
  let acc5 := gbase + 13
  let acc6 := gbase + 14
  let acc7 := gbase + 15
  let q_wire := gbase + 16
  let t1 := gbase + 17
  [ { a := q0, b := q1, c := acc1, qm := 0, qa := 1, qb := (2 ^ 16 : BN254Fr), qc := -1, k := 0 },
    { a := acc1, b := q2, c := acc2, qm := 0, qa := 1, qb := (2 ^ 32 : BN254Fr), qc := -1, k := 0 },
    { a := acc2, b := q3, c := acc3, qm := 0, qa := 1, qb := (2 ^ 48 : BN254Fr), qc := -1, k := 0 },
    { a := acc3, b := q4, c := acc4, qm := 0, qa := 1, qb := (2 ^ 64 : BN254Fr), qc := -1, k := 0 },
    { a := acc4, b := q5, c := acc5, qm := 0, qa := 1, qb := (2 ^ 80 : BN254Fr), qc := -1, k := 0 },
    { a := acc5, b := q6, c := acc6, qm := 0, qa := 1, qb := (2 ^ 96 : BN254Fr), qc := -1, k := 0 },
    { a := acc6, b := q7, c := acc7, qm := 0, qa := 1, qb := (2 ^ 112 : BN254Fr), qc := -1, k := 0 },
    { a := acc7, b := q8, c := q_wire, qm := 0, qa := 1, qb := (2 ^ 128 : BN254Fr), qc := -1, k := 0 },
    -- Gate A: qm * a * b + qa * a + qb * b - t1 + (k + offset) = 0
    { a := g.a, b := g.b, c := t1,
      qm := qm, qa := qa, qb := qb, qc := -1,
      k := k + (universalGateOffset : BN254Fr) },
    -- Gate B: t1 + qc * c - goldilocksP * q_wire = 0
    { a := t1, b := g.c, c := q_wire,
      qm := 0, qa := 1, qb := qc, qc := -(goldilocksP : BN254Fr), k := 0 } ]

/-- Project a `BN254Fr` wire assignment to `GoldilocksF` via canonical reduction mod `goldilocksP`. -/
def projectGoldilocksWire (w_fr : Wire → BN254Fr) : Wire → GoldilocksF :=
  fun i => GoldilocksF.ofNat (BN254Fr.val (w_fr i) % goldilocksP)

/-- Soundness of the translated gate gadget: if `g.a, g.b, g.c` have canonical values `< goldilocksP`
and `w_fr` satisfies `translatedGateGates g gbase` and `translatedGateLookups gbase`,
then `g.Satisfied (projectGoldilocksWire w_fr)` holds in `GoldilocksF`. -/
theorem translatedGateGadget_sound (tables : List (TableSpec GoldilocksF))
    (g : Gate GoldilocksF) (gbase : Nat) (w_fr : Wire → BN254Fr)
    (ha : ZMod.val (w_fr g.a) < goldilocksP)
    (hb : ZMod.val (w_fr g.b) < goldilocksP)
    (hc : ZMod.val (w_fr g.c) < goldilocksP)
    (hgates : ∀ gate ∈ translatedGateGates g gbase, gate.Satisfied w_fr)
    (hlookups : ∀ l ∈ translatedGateLookups gbase,
      l.Satisfied (u16TableSpec :: tables.map translateTable) w_fr) :
    g.Satisfied (projectGoldilocksWire w_fr) := by
  have hq0 := u16_lookup_val_lt tables gbase w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq1 := u16_lookup_val_lt tables (gbase + 1) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq2 := u16_lookup_val_lt tables (gbase + 2) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq3 := u16_lookup_val_lt tables (gbase + 3) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq4 := u16_lookup_val_lt tables (gbase + 4) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq5 := u16_lookup_val_lt tables (gbase + 5) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq6 := u16_lookup_val_lt tables (gbase + 6) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq7 := u16_lookup_val_lt tables (gbase + 7) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq8 := u16_lookup_val_lt tables (gbase + 8) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hg_l1 := hgates
    { a := gbase, b := gbase + 1, c := gbase + 9, qm := 0, qa := 1, qb := (2 ^ 16 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hg_l2 := hgates
    { a := gbase + 9, b := gbase + 2, c := gbase + 10, qm := 0, qa := 1, qb := (2 ^ 32 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hg_l3 := hgates
    { a := gbase + 10, b := gbase + 3, c := gbase + 11, qm := 0, qa := 1, qb := (2 ^ 48 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hg_l4 := hgates
    { a := gbase + 11, b := gbase + 4, c := gbase + 12, qm := 0, qa := 1, qb := (2 ^ 64 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hg_l5 := hgates
    { a := gbase + 12, b := gbase + 5, c := gbase + 13, qm := 0, qa := 1, qb := (2 ^ 80 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hg_l6 := hgates
    { a := gbase + 13, b := gbase + 6, c := gbase + 14, qm := 0, qa := 1, qb := (2 ^ 96 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hg_l7 := hgates
    { a := gbase + 14, b := gbase + 7, c := gbase + 15, qm := 0, qa := 1, qb := (2 ^ 112 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hg_l8 := hgates
    { a := gbase + 15, b := gbase + 8, c := gbase + 16, qm := 0, qa := 1, qb := (2 ^ 128 : BN254Fr), qc := -1, k := 0 }
    (by simp [translatedGateGates])
  have hgA := hgates
    { a := g.a, b := g.b, c := gbase + 17,
      qm := (signedCoeff (ZMod.val g.qm) : BN254Fr),
      qa := (signedCoeff (ZMod.val g.qa) : BN254Fr),
      qb := (signedCoeff (ZMod.val g.qb) : BN254Fr),
      qc := -1,
      k := (signedCoeff (ZMod.val g.k) : BN254Fr) + (universalGateOffset : BN254Fr) }
    (by simp [translatedGateGates])
  have hgB := hgates
    { a := gbase + 17, b := g.c, c := gbase + 16,
      qm := 0, qa := 1,
      qb := (signedCoeff (ZMod.val g.qc) : BN254Fr),
      qc := -(goldilocksP : BN254Fr), k := 0 }
    (by simp [translatedGateGates])
  unfold Gate.Satisfied Gate.eval at hg_l1 hg_l2 hg_l3 hg_l4 hg_l5 hg_l6 hg_l7 hg_l8 hgA hgB
  let q_nat := reconstructQuotient9
    (ZMod.val (w_fr gbase)) (ZMod.val (w_fr (gbase + 1))) (ZMod.val (w_fr (gbase + 2)))
    (ZMod.val (w_fr (gbase + 3))) (ZMod.val (w_fr (gbase + 4))) (ZMod.val (w_fr (gbase + 5)))
    (ZMod.val (w_fr (gbase + 6))) (ZMod.val (w_fr (gbase + 7))) (ZMod.val (w_fr (gbase + 8)))
  have hq_nat_lt : q_nat < 2 ^ 144 :=
    reconstructQuotient9_lt _ _ _ _ _ _ _ _ _ hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hq8
  have hq_wire_eq : w_fr (gbase + 16) = (q_nat : BN254Fr) := by
    dsimp [q_nat, reconstructQuotient9]
    push_cast
    repeat rw [ZMod.natCast_zmod_val]
    linear_combination -(hg_l1 + hg_l2 + hg_l3 + hg_l4 + hg_l5 + hg_l6 + hg_l7 + hg_l8)
  let qm_i := signedCoeff (ZMod.val g.qm)
  let qa_i := signedCoeff (ZMod.val g.qa)
  let qb_i := signedCoeff (ZMod.val g.qb)
  let qc_i := signedCoeff (ZMod.val g.qc)
  let k_i := signedCoeff (ZMod.val g.k)
  let a_n := ZMod.val (w_fr g.a)
  let b_n := ZMod.val (w_fr g.b)
  let c_n := ZMod.val (w_fr g.c)
  let E := gateIntExpr qm_i qa_i qb_i qc_i k_i (Int.ofNat a_n) (Int.ofNat b_n) (Int.ofNat c_n)
  have hE_cast : ((E + Int.ofNat universalGateOffset -
      Int.ofNat goldilocksP * Int.ofNat q_nat : Int) : BN254Fr) = 0 := by
    dsimp [E, gateIntExpr, a_n, b_n, c_n]
    push_cast
    rw [ZMod.natCast_zmod_val (w_fr g.a), ZMod.natCast_zmod_val (w_fr g.b),
        ZMod.natCast_zmod_val (w_fr g.c), ← hq_wire_eq]
    linear_combination hgA + hgB
  have hdvdR : (Int.ofNat bn254FrModulus) ∣
      (E + Int.ofNat universalGateOffset - Int.ofNat goldilocksP * Int.ofNat q_nat) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ bn254FrModulus).mp hE_cast
  have hmodR : E + Int.ofNat universalGateOffset - Int.ofNat goldilocksP * Int.ofNat q_nat ≡
      0 [ZMOD Int.ofNat bn254FrModulus] :=
    Int.modEq_zero_iff_dvd.mpr hdvdR
  have hbounds := universalGateExpr_bounds g.qm g.qa g.qb g.qc g.k ha hb hc
  have hsound := quotient_gate_sound qm_i qa_i qb_i qc_i k_i
    (Int.ofNat a_n) (Int.ofNat b_n) (Int.ofNat c_n)
    universalGateOffset q_nat hbounds.1 hbounds.2 hq_nat_lt universalGateOffset_mod hmodR
  have hdvdP : (Int.ofNat goldilocksP) ∣ E := Int.modEq_zero_iff_dvd.mp hsound.2
  have hE_gl : ((E : Int) : GoldilocksF) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd E goldilocksP).mpr hdvdP
  unfold Gate.Satisfied Gate.eval projectGoldilocksWire BN254Fr.val GoldilocksF.ofNat
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]
  dsimp [E, gateIntExpr, qm_i, qa_i, qb_i, qc_i, k_i, a_n, b_n, c_n] at hE_gl
  push_cast at hE_gl
  rw [signedCoeff_cast_goldilocks g.qm,
      signedCoeff_cast_goldilocks g.qa,
      signedCoeff_cast_goldilocks g.qb,
      signedCoeff_cast_goldilocks g.qc,
      signedCoeff_cast_goldilocks g.k] at hE_gl
  exact hE_gl

/-- All wires referenced in a `Plonkish.Circuit GoldilocksF`. -/
def allReferencedWires (c : Circuit GoldilocksF) : List Wire :=
  List.range c.numWires ++
  c.publicInputs ++
  (c.gates.flatMap fun g => [g.a, g.b, g.c]) ++
  (c.lookups.flatMap fun l => l.wires) ++
  (c.blake3Calls.flatMap fun b => b.inputWires ++ b.outputWires)

theorem mem_allReferencedWires_of_public {c : Circuit GoldilocksF} {w : Wire}
    (h : w ∈ c.publicInputs) : w ∈ allReferencedWires c := by
  unfold allReferencedWires
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem mem_allReferencedWires_of_gate {c : Circuit GoldilocksF} {g : Gate GoldilocksF}
    (hg : g ∈ c.gates) :
    g.a ∈ allReferencedWires c ∧ g.b ∈ allReferencedWires c ∧ g.c ∈ allReferencedWires c := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    unfold allReferencedWires
    simp only [List.mem_append, List.mem_flatMap]
    refine Or.inl (Or.inl (Or.inr ⟨g, hg, ?_⟩))
    simp

theorem mem_allReferencedWires_of_lookup {c : Circuit GoldilocksF} {l : LookupConstraint}
    (hl : l ∈ c.lookups) {w : Wire} (hw : w ∈ l.wires) :
    w ∈ allReferencedWires c := by
  unfold allReferencedWires
  simp only [List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨l, hl, hw⟩)

/-- Upper bound on all wire indices in `c`. -/
def maxWireBound (c : Circuit GoldilocksF) : Nat :=
  (allReferencedWires c).foldl Nat.max c.numWires + 1

/-- **Goldilocks-to-BN254 Plonkish Circuit Compiler (`foreignCompile`)**:
Translates any `c : Plonkish.Circuit GoldilocksF` into a `Plonkish.Circuit BN254Fr`
(`crates/proof-compression/src/foreign.rs:GoldilocksCircuit::translate`). -/
def foreignCompile (c : Circuit GoldilocksF) : Circuit BN254Fr :=
  let refs := allReferencedWires c
  let base0 := maxWireBound c
  let wireBase (idx : Nat) : Nat := base0 + 8 * idx
  let gateStart : Nat := base0 + 8 * refs.length
  let gateBase (idx : Nat) : Nat := gateStart + 18 * idx
  let canonGates := refs.zipIdx.flatMap fun (v, idx) => canonicalWireGates v (wireBase idx)
  let canonLookups := refs.zipIdx.flatMap fun (_, idx) => canonicalWireLookups (wireBase idx)
  let gateGates := c.gates.zipIdx.flatMap fun (g, idx) => translatedGateGates g (gateBase idx)
  let gateLookups := c.gates.zipIdx.flatMap fun (_, idx) => translatedGateLookups (gateBase idx)
  { numWires := gateStart + 18 * c.gates.length
    publicInputs := c.publicInputs
    gates := canonGates ++ gateGates
    tables := u16TableSpec :: c.tables.map translateTable
    lookups := canonLookups ++ gateLookups ++ c.lookups.map translateLookup
    blake3Calls := c.blake3Calls }

/-- If `w_fr` satisfies `foreignCompile c`, then every wire `v ∈ allReferencedWires c`
is canonically bounded (`ZMod.val (w_fr v) < goldilocksP`). -/
theorem foreignCompile_wire_canonical (c : Circuit GoldilocksF)
    (w_fr : Wire → BN254Fr) (hhold : (foreignCompile c).ConstraintsHold w_fr)
    {v : Wire} (hv : v ∈ allReferencedWires c) :
    ZMod.val (w_fr v) < goldilocksP := by
  rcases List.mem_iff_getElem.mp hv with ⟨idx, hidx, hget⟩
  let base := maxWireBound c + 8 * idx
  have hmem_zip : (v, idx) ∈ (allReferencedWires c).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa [List.getElem?_eq_getElem hidx] using hget
  apply canonicalWireGadget_sound c.tables v base w_fr
  · intro g hg
    apply hhold.1 g
    unfold foreignCompile
    rw [List.mem_append]
    left
    rw [List.mem_flatMap]
    exact ⟨(v, idx), hmem_zip, hg⟩
  · intro l hl
    apply hhold.2.1 l
    unfold foreignCompile
    rw [List.mem_append, List.mem_append]
    left; left
    rw [List.mem_flatMap]
    exact ⟨(v, idx), hmem_zip, hl⟩

/-- Map a list of `GoldilocksF` public inputs to `BN254Fr` via canonical embedding. -/
def liftPublicInputs (pub : List GoldilocksF) : List BN254Fr :=
  pub.map (fun x => (ZMod.val x : BN254Fr))

/-- **End-to-End Foreign Compiler Soundness (`foreign_compile_sound`)**:
For *any* `c : Plonkish.Circuit GoldilocksF`, if `w_fr : Wire → BN254Fr` satisfies
`foreignCompile c` with public inputs `pub_fr`, then the projected wire assignment
`fun i => GoldilocksF.ofNat (BN254Fr.val (w_fr i) % goldilocksP)` satisfies `c`
with public inputs `pub_fr.map (fun x => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP))`. -/
theorem foreign_compile_sound (c : Circuit GoldilocksF)
    (pub_fr : List BN254Fr) (w_fr : Wire → BN254Fr)
    (hsat : (foreignCompile c).Satisfies pub_fr w_fr) :
    c.Satisfies
      (pub_fr.map (fun x => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP)))
      (fun i => GoldilocksF.ofNat (BN254Fr.val (w_fr i) % goldilocksP)) := by
  have hhold : (foreignCompile c).ConstraintsHold w_fr := ⟨hsat.2.1, hsat.2.2.1, hsat.2.2.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. Public inputs match
    have hpub := hsat.1
    change c.publicInputs.map w_fr = pub_fr at hpub
    rw [← hpub, List.map_map]
    rfl
  · -- 2. Every gate in c.gates is satisfied
    intro g hg
    rcases List.mem_iff_getElem.mp hg with ⟨idx, hidx, hget⟩
    have hmem_zip : (g, idx) ∈ c.gates.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simpa [List.getElem?_eq_getElem hidx] using hget
    rcases mem_allReferencedWires_of_gate hg with ⟨hga, hgb, hgc⟩
    have ha := foreignCompile_wire_canonical c w_fr hhold hga
    have hb := foreignCompile_wire_canonical c w_fr hhold hgb
    have hc := foreignCompile_wire_canonical c w_fr hhold hgc
    let gbase := (maxWireBound c + 8 * (allReferencedWires c).length) + 18 * idx
    apply translatedGateGadget_sound c.tables g gbase w_fr ha hb hc
    · intro gate hgate
      apply hhold.1 gate
      unfold foreignCompile
      rw [List.mem_append]
      right
      rw [List.mem_flatMap]
      exact ⟨(g, idx), hmem_zip, hgate⟩
    · intro l hl
      apply hhold.2.1 l
      unfold foreignCompile
      rw [List.mem_append, List.mem_append]
      left; right
      rw [List.mem_flatMap]
      exact ⟨(g, idx), hmem_zip, hl⟩
  · -- 3. Every lookup in c.lookups is satisfied
    intro l hl
    have hl_fr : (translateLookup l).Satisfied (foreignCompile c).tables w_fr := by
      apply hhold.2.1 (translateLookup l)
      unfold foreignCompile
      rw [List.mem_append]
      right
      exact List.mem_map_of_mem hl
    rcases hl_fr with ⟨t_fr, ht_fr, hname_fr, hmem_fr⟩
    simp only [foreignCompile, List.mem_cons, List.mem_map] at ht_fr
    rcases ht_fr with rfl | ⟨srcT, hsrcT, rfl⟩
    · exfalso
      exact src_prefix_ne_u16 l.tableName hname_fr.symm
    · have hname : srcT.name = l.tableName := src_prefix_inj hname_fr
      simp only [translateTable, translateLookup, List.mem_map] at hmem_fr
      rcases hmem_fr with ⟨srcRow, hsrcRow, hrow_eq⟩
      refine ⟨srcT, hsrcT, hname, ?_⟩
      have hproj : l.wires.map (fun i => GoldilocksF.ofNat (BN254Fr.val (w_fr i) % goldilocksP)) =
          srcRow := by
        have hmap := congrArg
          (List.map (fun x : BN254Fr => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP)))
          hrow_eq.symm
        rw [List.map_map, List.map_map] at hmap
        simp only [Function.comp_def] at hmap
        rw [hmap]
        have hid : ∀ v : GoldilocksF,
            GoldilocksF.ofNat (BN254Fr.val (ZMod.val v : BN254Fr) % goldilocksP) = v := by
          intro v
          have hv_lt : ZMod.val v < bn254FrModulus :=
            Nat.lt_trans (ZMod.val_lt v) goldilocksP_lt_bn254FrModulus
          unfold BN254Fr.val GoldilocksF.ofNat
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv_lt,
              Nat.mod_eq_of_lt (ZMod.val_lt v), ZMod.natCast_zmod_val]
        calc
          List.map (fun x => GoldilocksF.ofNat (BN254Fr.val (ZMod.val x : BN254Fr) % goldilocksP)) srcRow
            = List.map id srcRow := List.map_congr_left (fun v _ => hid v)
          _ = srcRow := List.map_id srcRow
      rw [hproj]
      exact hsrcRow
  · -- 4. Every BLAKE3 accelerator call in c.blake3Calls is satisfied
    intro b hb
    have hb_fr : b.Satisfied w_fr := hhold.2.2 b hb
    rcases hb_fr with ⟨bytes, hin, hout⟩
    refine ⟨bytes, ?_, ?_⟩
    · have hmap := congrArg
        (List.map (fun x : BN254Fr => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP))) hin
      rw [List.map_map, List.map_map] at hmap
      simp only [Function.comp_def] at hmap
      rw [hmap]
      apply List.map_congr_left
      intro u _
      have hu_p : u.toNat < goldilocksP := by
        have := u.toNat_lt; unfold goldilocksP; omega
      have hu_r : u.toNat < bn254FrModulus :=
        Nat.lt_trans hu_p goldilocksP_lt_bn254FrModulus
      unfold BN254Fr.val GoldilocksF.ofNat
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu_r, Nat.mod_eq_of_lt hu_p]
    · have hmap := congrArg
        (List.map (fun x : BN254Fr => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP))) hout
      rw [List.map_map, List.map_map] at hmap
      simp only [Function.comp_def] at hmap
      rw [hmap]
      apply List.map_congr_left
      intro u _
      have hu_p : u.toNat < goldilocksP := by
        have := u.toNat_lt; unfold goldilocksP; omega
      have hu_r : u.toNat < bn254FrModulus :=
        Nat.lt_trans hu_p goldilocksP_lt_bn254FrModulus
      unfold BN254Fr.val GoldilocksF.ofNat
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu_r, Nat.mod_eq_of_lt hu_p]

/-- Specialization of `foreign_compile_sound` when public inputs `pub : List GoldilocksF`
are lifted into `BN254Fr` via `liftPublicInputs pub`. -/
theorem foreign_compile_sound_lifted (c : Circuit GoldilocksF)
    (pub : List GoldilocksF) (w_fr : Wire → BN254Fr)
    (hsat : (foreignCompile c).Satisfies (liftPublicInputs pub) w_fr) :
    c.Satisfies pub (fun i => GoldilocksF.ofNat (BN254Fr.val (w_fr i) % goldilocksP)) := by
  have h := foreign_compile_sound c (liftPublicInputs pub) w_fr hsat
  have hpub : (liftPublicInputs pub).map
      (fun x => GoldilocksF.ofNat (BN254Fr.val x % goldilocksP)) = pub := by
    unfold liftPublicInputs
    rw [List.map_map]
    have hid : ∀ v : GoldilocksF,
        GoldilocksF.ofNat (BN254Fr.val (ZMod.val v : BN254Fr) % goldilocksP) = v := by
      intro v
      have hv_lt : ZMod.val v < bn254FrModulus :=
        Nat.lt_trans (ZMod.val_lt v) goldilocksP_lt_bn254FrModulus
      unfold BN254Fr.val GoldilocksF.ofNat
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv_lt,
          Nat.mod_eq_of_lt (ZMod.val_lt v), ZMod.natCast_zmod_val]
    calc
      List.map (fun x => GoldilocksF.ofNat (BN254Fr.val (ZMod.val x : BN254Fr) % goldilocksP)) pub
        = List.map id pub := List.map_congr_left (fun v _ => hid v)
      _ = pub := List.map_id pub
  rwa [hpub] at h

end Ix.Cert.Compression.Foreign
