import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign
import Ix.Cert.Compression.FriVerifier
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! # BLS12-381 Field Primality, 5×80-Bit Non-Native `Fq` Arithmetic & Foreign-Field Compiler

Formalizes and proves the field-layer foundation for the BLS12-381 proof-compression
stack (`crates/proof-compression/src/kzg/curve.rs`, `src/recursive/native_field.rs`,
and `src/foreign.rs`):

1. **Exact BLS12-381 Moduli & Primality Certificates (zero `sorry`, zero `native_decide`):**
   - `bls12381FrModulus`: the 255-bit scalar field prime $r = x^4 - x^2 + 1$.
   - `bls12381FrModulus_prime`: self-contained Lucas/Pratt certificate via `lucas_primality`
     over the complete prime factorization of $r - 1$.
   - `bls12381FqModulus`: the 381-bit base field prime $q = \frac{(x-1)^2 r}{3} + x$.
   - `bls12381FqModulus_prime`: self-contained Endomorphism-ECPP primality proof using a
     kernel-checked 136-step double-and-add certificate showing $[u^2] G = -\phi(G)$ on
     $E(\mathbb{Z}/p\mathbb{Z}) : y^2 = x^3 + 4$ for every prime $p \mid q$, forcing
     $[r] G_p = \mathcal{O}_p$ and hence $r - 1 \le 2p$, which contradicts $p^2 \le q$ since
     $4q < (r - 1)^2$.
   - Simultaneously yields the parameterized prime-order lemma
     `bls12381Generator_order_at_prime_dvd_q` and the GLV endomorphism algebra
     (`bls12381EndoAt_add`, `bls12381EndoAt_charpoly`, `order_r_of_endo_eq_at`) reused by
     `CurveMsm.lean` for the mandatory BLS12-381 $G_1$ subgroup check.
2. **5×80-Bit Non-Native `BLS12381::Fq` Limb Arithmetic (`Bls12381FqLimbs`, `native_field.rs`):**
   - `L = 5`, `W = 80`, `TOP_LIMB_BITS = 61`, `QUOTIENT_BITS = 384`, `QUOTIENT_TOP_BITS = 64`,
     `RANGE_BITS = 20`, `CARRY_BITS = 89`, `CARRY_BIAS = 2^88`.
   - Proves 20-bit lookup range soundness (`bls12381_range20_limb80_bound`,
     `bls12381_range20_topLimb61_bound`, `bls12381_range20_quotientTop64_bound`,
     `bls12381_range20_carry89_bound`), paired-limb no-overflow
     (`bls12381_paired_limb_no_overflow`), 5-pair 10-degree convolution telescoping
     (`bls12381_fq_relation_five_pairs_sound`), modular arithmetic corollaries, and 5-limb
     canonical subtraction soundness (`bls12381_fq_canonical_lt_q_sound`).
3. **Goldilocks-in-`BLS12381Fr` Foreign-Field Compiler & FRI Verifier Lifting:**
   - `bls12381ForeignCompile`, `bls12381_direct_gate_sound`, `bls12381_quotient_gate_sound`,
     `bls12381_foreign_compile_sound`, `bls12381_foreign_compile_sound_lifted`, and
     `bls12381_foreign_friVerifier_sound` composing directly with
     `Ix.Cert.Compression.FriVerifier.friVerifierCircuit_sound`.
-/

namespace Ix.Cert.Compression.Bls12381.Field

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.FriVerifier

/-! ## 1. BLS12-381 Field Moduli, Curve Constants & `Fr` Primality Certificate -/

/-- The BLS12-381 scalar field prime modulus $r$ (255-bit prime). -/
abbrev bls12381FrModulus : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The BLS12-381 base field prime modulus $q$ (381-bit prime). -/
abbrev bls12381FqModulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- Magnitude $u = |x| = \text{0xd201000000010000}$ of the BLS12-381 curve seed $x = -u$
(`Bls12381::SUBGROUP_CHECK_SEED` in `crates/proof-compression/src/kzg/curve.rs`). -/
abbrev bls12381Seed : Nat :=
  0xd201000000010000

/-- The BLS12-381 $G_1$ cofactor $h_1 = (x - 1)^2 / 3 = (u + 1)^2 / 3$. -/
abbrev bls12381G1Cofactor : Nat :=
  0x396c8c005555e1568c00aaab0000aaab

/-- Canonical integer representative of the GLV cube root of unity $\beta \in \mathbb{F}_q$
(`ark_bls12_381::g1::BETA`), satisfying $\beta^2 + \beta + 1 \equiv 0 \pmod q$ and
$[u^2] G = (\beta g_x, -g_y)$. -/
abbrev bls12381EndoBetaNat : Nat :=
  0x5f19672fdf76ce51ba69c6076a0f77eaddb3a93be6f89688de17d813620a00022e01fffffffefffe

/-- Standard BLS12-381 $G_1$ generator $x$-coordinate. -/
abbrev bls12381G1GenX : Nat :=
  0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb

/-- Standard BLS12-381 $G_1$ generator $y$-coordinate. -/
abbrev bls12381G1GenY : Nat :=
  0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

theorem bls12381FrModulus_pos : 0 < bls12381FrModulus := by decide
theorem bls12381FqModulus_pos : 0 < bls12381FqModulus := by decide
theorem goldilocksP_lt_bls12381FrModulus : goldilocksP < bls12381FrModulus := by decide
theorem two_pow_194_lt_bls12381FrModulus : 2 ^ 194 < bls12381FrModulus := by decide
theorem two_pow_254_lt_bls12381FrModulus : 2 ^ 254 < bls12381FrModulus := by decide
theorem bls12381FrModulus_seed_identity :
    bls12381Seed ^ 4 + 1 = bls12381FrModulus + bls12381Seed ^ 2 := by decide
theorem bls12381G1Cofactor_identity :
    bls12381G1Cofactor * 3 = (bls12381Seed + 1) ^ 2 := by decide
theorem bls12381G1_order_identity :
    bls12381G1Cofactor * bls12381FrModulus = bls12381FqModulus + bls12381Seed := by decide
theorem four_mul_fq_lt_fr_sub_one_sq :
    4 * bls12381FqModulus < (bls12381FrModulus - 1) ^ 2 := by decide
theorem bls12381EndoBetaNat_poly_mod :
    (bls12381EndoBetaNat * bls12381EndoBetaNat + bls12381EndoBetaNat + 1) % bls12381FqModulus = 0 := by
  decide
theorem bls12381G1Gen_onCurve_mod :
    (bls12381G1GenY * bls12381G1GenY) % bls12381FqModulus =
      (bls12381G1GenX * bls12381G1GenX * bls12381G1GenX + 4) % bls12381FqModulus := by
  decide

/-! ### Self-Contained Lucas/Pratt Primality Certificate for `bls12381FrModulus` -/

private theorem prime_10177 : Nat.Prime 10177 := by norm_num
private theorem prime_18329 : Nat.Prime 18329 := by norm_num
private theorem prime_20921 : Nat.Prime 20921 := by norm_num
private theorem prime_47737 : Nat.Prime 47737 := by norm_num

private theorem prime_125527 : Nat.Prime 125527 := by
  apply lucas_primality 125527 (5 : ZMod 125527)
  · reduce_mod_char
  · intro q hq hd
    have factors : 125527 - 1 = 2 * 3 * 20921 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_20921] at hd; subst q; reduce_mod_char; decide

private theorem prime_859267 : Nat.Prime 859267 := by
  apply lucas_primality 859267 (2 : ZMod 859267)
  · reduce_mod_char
  · intro q hq hd
    have factors : 859267 - 1 = 2 * 3 ^ 2 * 47737 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_47737] at hd; subst q; reduce_mod_char; decide

private theorem prime_906349 : Nat.Prime 906349 := by
  apply lucas_primality 906349 (2 : ZMod 906349)
  · reduce_mod_char
  · intro q hq hd
    have factors : 906349 - 1 = 2 ^ 2 * 3 * 47 * 1607 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide

private theorem prime_2508409 : Nat.Prime 2508409 := by
  apply lucas_primality 2508409 (11 : ZMod 2508409)
  · reduce_mod_char
  · intro q hq hd
    have factors : 2508409 - 1 = 2 ^ 3 * 3 ^ 4 * 7 ^ 2 * 79 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide

private theorem prime_2529403 : Nat.Prime 2529403 := by
  apply lucas_primality 2529403 (2 : ZMod 2529403)
  · reduce_mod_char
  · intro q hq hd
    have factors : 2529403 - 1 = 2 * 3 * 23 * 18329 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_18329] at hd; subst q; reduce_mod_char; decide

private theorem prime_609743 : Nat.Prime 609743 := by
  apply lucas_primality 609743 (5 : ZMod 609743)
  · reduce_mod_char
  · intro q hq hd
    have factors : 609743 - 1 = 2 * 7 * 97 * 449 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd <;>
      (rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide)

private theorem prime_52437899 : Nat.Prime 52437899 := by
  apply lucas_primality 52437899 (2 : ZMod 52437899)
  · reduce_mod_char
  · intro q hq hd
    have factors : 52437899 - 1 = 2 * 43 * 609743 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_609743] at hd; subst q; reduce_mod_char; decide

private theorem prime_110573 : Nat.Prime 110573 := by
  apply lucas_primality 110573 (3 : ZMod 110573)
  · reduce_mod_char
  · intro q hq hd
    have factors : 110573 - 1 = 2 ^ 2 * 7 * 11 * 359 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide

private theorem prime_2653753 : Nat.Prime 2653753 := by
  apply lucas_primality 2653753 (5 : ZMod 2653753)
  · reduce_mod_char
  · intro q hq hd
    have factors : 2653753 - 1 = 2 ^ 3 * 3 * 110573 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_110573] at hd; subst q; reduce_mod_char; decide

private theorem prime_63690073 : Nat.Prime 63690073 := by
  apply lucas_primality 63690073 (7 : ZMod 63690073)
  · reduce_mod_char
  · intro q hq hd
    have factors : 63690073 - 1 = 2 ^ 3 * 3 * 2653753 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_2653753] at hd; subst q; reduce_mod_char; decide

private theorem prime_254760293 : Nat.Prime 254760293 := by
  apply lucas_primality 254760293 (2 : ZMod 254760293)
  · reduce_mod_char
  · intro q hq hd
    have factors : 254760293 - 1 = 2 ^ 2 * 63690073 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul] at hd
    rcases hd with hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_63690073] at hd; subst q; reduce_mod_char; decide

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8000000 in
/-- Self-contained Lucas/Pratt primality certificate for the BLS12-381 scalar-field prime $r$. -/
theorem bls12381FrModulus_prime : Nat.Prime bls12381FrModulus := by
  apply lucas_primality bls12381FrModulus (7 : ZMod bls12381FrModulus)
  · reduce_mod_char
  · intro q hq hd
    have factors : bls12381FrModulus - 1 =
        2 ^ 32 * 3 * 11 * 19 * 10177 * 125527 * 859267 * 906349 ^ 2 *
        2508409 * 2529403 * 52437899 * 254760293 ^ 2 := by norm_num
    rw [factors] at hd
    simp only [hq.dvd_mul, or_assoc] at hd
    rcases hd with hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd | hd
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq (by norm_num)] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_10177] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_125527] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_859267] at hd; subst q; reduce_mod_char; decide
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq prime_906349] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_2508409] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_2529403] at hd; subst q; reduce_mod_char; decide
    · rw [Nat.prime_dvd_prime_iff_eq hq prime_52437899] at hd; subst q; reduce_mod_char; decide
    · replace hd := hq.dvd_of_dvd_pow hd
      rw [Nat.prime_dvd_prime_iff_eq hq prime_254760293] at hd; subst q; reduce_mod_char; decide

instance : Fact (Nat.Prime bls12381FrModulus) := ⟨bls12381FrModulus_prime⟩

/-- The BLS12-381 scalar prime field $\mathbb{F}_r$. -/
abbrev BLS12381Fr : Type := ZMod bls12381FrModulus

/-- Canonical natural value in $[0, r)$ of a `BLS12381Fr` element. -/
abbrev BLS12381Fr.val (x : BLS12381Fr) : Nat := ZMod.val x

/-! ## 2. Endomorphism-ECPP Primality Certificate for `bls12381FqModulus`

For every prime $p \mid q$ (`bls12381FqModulus`), $p \notin \{2, 3\}$, so the short Weierstrass
curve $E_p : y^2 = x^3 + 4$ over $\mathbb{F}_p = \text{ZMod } p$ is nonsingular
($\Delta = -6912 \not\equiv 0 \pmod p$), and $\beta_p = (\text{bls12381EndoBetaNat} : \mathbb{F}_p)$
is a primitive cube root of unity defining the GLV endomorphism $\phi_p(x, y) = (\beta_p x, y)$
with $\phi_p^2(P) + \phi_p(P) + P = \mathcal{O}_p$.

A 136-step affine double-and-add certificate verified modulo $q$ shows $[u^2] G_p = -\phi_p(G_p)$
for every prime $p \mid q$, which algebraically forces $[r] G_p = \mathcal{O}_p$. Since $r$ is
prime and $G_p \ne \mathcal{O}_p$, the $r - 1$ nonzero multiples of $G_p$ map 2-to-1 into
$\mathbb{F}_p$ via their $x$-coordinates, forcing $r - 1 \le 2p$. If $q$ were composite, its
least prime factor $p \mid q$ would satisfy $p^2 \le q$, hence $(r - 1)^2 \le 4p^2 \le 4q$,
contradicting $4q < (r - 1)^2$. Thus $q$ is prime! -/

/-- Short Weierstrass curve $E(\mathbb{F}_p) : y^2 = x^3 + 4$ parameterized by modulus `p`. -/
def bls12381CurveAt (p : Nat) : WeierstrassCurve.Affine (ZMod p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := 0
  a₆ := 4

lemma bls12381CurveAt_equation_iff (p : Nat) (x y : ZMod p) :
    (bls12381CurveAt p).Equation x y ↔ y ^ 2 = x ^ 3 + 4 := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [bls12381CurveAt, zero_mul, add_zero]

lemma bls12381CurveAt_Δ_ne_zero {p : Nat} [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (bls12381CurveAt p).Δ ≠ 0 := by
  have hΔ : (bls12381CurveAt p).Δ = -((6912 : Nat) : ZMod p) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, bls12381CurveAt]
    norm_num
  rw [hΔ, neg_ne_zero]
  intro h0
  have hdvd : p ∣ 6912 := (ZMod.natCast_eq_zero_iff 6912 p).mp h0
  have hfac : 6912 = 2 ^ 8 * 3 ^ 3 := by norm_num
  rw [hfac] at hdvd
  have hp : Nat.Prime p := Fact.out
  rcases hp.dvd_mul.mp hdvd with h2 | h3
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h3))

lemma bls12381CurveAt_nonsingular_of_eq {p : Nat} [Fact (Nat.Prime p)]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x y : ZMod p} (h : y ^ 2 = x ^ 3 + 4) :
    (bls12381CurveAt p).Nonsingular x y :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
    (bls12381CurveAt_Δ_ne_zero hp2 hp3)).mp ((bls12381CurveAt_equation_iff p x y).mpr h)

lemma zmod_two_ne_zero {p : Nat} [Fact (Nat.Prime p)] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hdvd)

lemma zmod_three_ne_zero {p : Nat} [Fact (Nat.Prime p)] (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h0
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hdvd)

lemma beta_cube_eq_one {p : Nat} [Fact (Nat.Prime p)]
    {β : ZMod p} (hβ : β ^ 2 + β + 1 = 0) : β ^ 3 = 1 := by
  linear_combination (β - 1) * hβ

lemma beta_ne_zero {p : Nat} [Fact (Nat.Prime p)]
    {β : ZMod p} (hβ : β ^ 2 + β + 1 = 0) : β ≠ 0 := by
  intro h0
  rw [h0] at hβ
  norm_num at hβ

lemma beta_ne_one {p : Nat} [Fact (Nat.Prime p)] (hp3 : p ≠ 3)
    {β : ZMod p} (hβ : β ^ 2 + β + 1 = 0) : β ≠ 1 := by
  intro h1
  rw [h1] at hβ
  have h3 : (3 : ZMod p) = 0 := by linear_combination hβ
  exact zmod_three_ne_zero hp3 h3

/-- GLV endomorphism $\phi_p(x, y) = (\beta x, y)$ on `bls12381CurveAt p` for any primitive
cube root of unity $\beta \in \mathbb{F}_p$ ($\beta^2 + \beta + 1 = 0$). -/
def bls12381EndoAt (p : Nat) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : ZMod p) (hβ : β ^ 2 + β + 1 = 0) :
    (bls12381CurveAt p).Point → (bls12381CurveAt p).Point
  | .zero => 0
  | .some x y h =>
    .some (β * x) y (bls12381CurveAt_nonsingular_of_eq hp2 hp3 (by
      have heq : y ^ 2 = x ^ 3 + 4 := (bls12381CurveAt_equation_iff p x y).mp h.1
      rw [mul_pow, beta_cube_eq_one hβ, one_mul]
      exact heq))

@[simp]
lemma bls12381EndoAt_zero (p : Nat) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : ZMod p) (hβ : β ^ 2 + β + 1 = 0) :
    bls12381EndoAt p hp2 hp3 β hβ 0 = 0 := rfl

lemma bls12381EndoAt_neg (p : Nat) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : ZMod p) (hβ : β ^ 2 + β + 1 = 0) (P : (bls12381CurveAt p).Point) :
    bls12381EndoAt p hp2 hp3 β hβ (-P) = -(bls12381EndoAt p hp2 hp3 β hβ P) := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [WeierstrassCurve.Affine.Point.neg_some]
    dsimp only [bls12381EndoAt]
    rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.negY, bls12381CurveAt, zero_mul, sub_zero]

/-- The GLV endomorphism $\phi_p(x, y) = (\beta x, y)$ is a group homomorphism on
`(bls12381CurveAt p).Point`. -/
theorem bls12381EndoAt_add (p : Nat) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : ZMod p) (hβ : β ^ 2 + β + 1 = 0) (P Q : (bls12381CurveAt p).Point) :
    bls12381EndoAt p hp2 hp3 β hβ (P + Q) =
      bls12381EndoAt p hp2 hp3 β hβ P + bls12381EndoAt p hp2 hp3 β hβ Q := by
  have hβ0 : β ≠ 0 := beta_ne_zero hβ
  have hβ3 : β ^ 3 = 1 := beta_cube_eq_one hβ
  cases P with
  | zero =>
    change bls12381EndoAt p hp2 hp3 β hβ (0 + Q) = 0 + bls12381EndoAt p hp2 hp3 β hβ Q
    rw [zero_add, zero_add]
  | some x1 y1 h1 =>
    cases Q with
    | zero =>
      change bls12381EndoAt p hp2 hp3 β hβ (.some x1 y1 h1 + 0) =
        bls12381EndoAt p hp2 hp3 β hβ (.some x1 y1 h1) + 0
      rw [add_zero, add_zero]
    | some x2 y2 h2 =>
      by_cases hx : x1 = x2
      · by_cases hy : y1 = (bls12381CurveAt p).negY x2 y2
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          dsimp only [bls12381EndoAt]
          have hneg : (bls12381CurveAt p).negY (β * x2) y2 = (bls12381CurveAt p).negY x2 y2 := by
            simp [WeierstrassCurve.Affine.negY, bls12381CurveAt]
          rw [WeierstrassCurve.Affine.Point.add_of_Y_eq (congrArg (β * ·) hx) (by rwa [hneg])]
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_ne hy]
          dsimp only [bls12381EndoAt]
          have hneg : (bls12381CurveAt p).negY (β * x2) y2 = (bls12381CurveAt p).negY x2 y2 := by
            simp [WeierstrassCurve.Affine.negY, bls12381CurveAt]
          rw [WeierstrassCurve.Affine.Point.add_of_Y_ne (by rwa [hneg])]
          simp only [WeierstrassCurve.Affine.Point.some.injEq]
          set s := (bls12381CurveAt p).slope x1 x2 y1 y2
          set sb := (bls12381CurveAt p).slope (β * x1) (β * x2) y1 y2
          have hy' : y1 ≠ -y2 := by
            simpa [WeierstrassCurve.Affine.negY, bls12381CurveAt] using hy
          have hs : sb = β ^ 2 * s := by
            dsimp only [sb, s]
            rw [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.slope]
            have hbx : β * x1 = β * x2 := congrArg (β * ·) hx
            simp only [hx, ↓reduceIte, WeierstrassCurve.Affine.negY, bls12381CurveAt,
              zero_mul, add_zero, sub_zero, hy', sub_neg_eq_add]
            ring
          have hs2 : sb ^ 2 = β * s ^ 2 := by
            rw [hs]; linear_combination s ^ 2 * β * hβ3
          constructor
          · unfold WeierstrassCurve.Affine.addX
            simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
            rw [hs2]; ring
          · unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
              WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX
            simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
            rw [hs2, hs]
            linear_combination (s * (s ^ 2 - 2 * x1 - x2)) * hβ3
      · have hbx : β * x1 ≠ β * x2 := fun heq => hx (mul_left_cancel₀ hβ0 heq)
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx]
        dsimp only [bls12381EndoAt]
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hbx]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        set s := (bls12381CurveAt p).slope x1 x2 y1 y2
        set sb := (bls12381CurveAt p).slope (β * x1) (β * x2) y1 y2
        have hs : sb = β ^ 2 * s := by
          dsimp only [sb, s]
          rw [WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.slope]
          simp only [hx, hbx, ↓reduceIte]
          have hdx : x1 - x2 ≠ 0 := sub_ne_zero.mpr hx
          have hbdx : β * x1 - β * x2 ≠ 0 := sub_ne_zero.mpr hbx
          rw [div_eq_iff hbdx]
          have hfac : β * x1 - β * x2 = β * (x1 - x2) := by ring
          rw [hfac]
          calc y1 - y2 = (y1 - y2) / (x1 - x2) * (x1 - x2) := (div_mul_cancel₀ _ hdx).symm
            _ = (y1 - y2) / (x1 - x2) * (x1 - x2) * β ^ 3 := by rw [hβ3, mul_one]
            _ = β ^ 2 * ((y1 - y2) / (x1 - x2)) * (β * (x1 - x2)) := by ring
        have hs2 : sb ^ 2 = β * s ^ 2 := by
          rw [hs]; linear_combination s ^ 2 * β * hβ3
        constructor
        · unfold WeierstrassCurve.Affine.addX
          simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
          rw [hs2]; ring
        · unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
            WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX
          simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
          rw [hs2, hs]
          linear_combination (s * (s ^ 2 - 2 * x1 - x2)) * hβ3

lemma bls12381EndoAt_nsmul (p : Nat) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : ZMod p) (hβ : β ^ 2 + β + 1 = 0) (n : Nat) (P : (bls12381CurveAt p).Point) :
    bls12381EndoAt p hp2 hp3 β hβ (n • P) = n • bls12381EndoAt p hp2 hp3 β hβ P := by
  induction n with
  | zero => simp [bls12381EndoAt]
  | succ n ih =>
    rw [succ_nsmul, bls12381EndoAt_add, ih, succ_nsmul]

/-- **Characteristic Polynomial of the GLV Endomorphism (`bls12381EndoAt_charpoly`):**
For every point $P \in E(\mathbb{F}_p)$ on $y^2 = x^3 + 4$ ($p \notin \{2, 3\}$, $\beta^2+\beta+1=0$),
$$\phi_p(\phi_p(P)) + \phi_p(P) + P = \mathcal{O}_p.$$ -/
theorem bls12381EndoAt_charpoly (p : Nat) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : ZMod p) (hβ : β ^ 2 + β + 1 = 0) (P : (bls12381CurveAt p).Point) :
    bls12381EndoAt p hp2 hp3 β hβ (bls12381EndoAt p hp2 hp3 β hβ P) +
      bls12381EndoAt p hp2 hp3 β hβ P + P = 0 := by
  cases P with
  | zero =>
    change bls12381EndoAt p hp2 hp3 β hβ (bls12381EndoAt p hp2 hp3 β hβ 0) +
      bls12381EndoAt p hp2 hp3 β hβ 0 + 0 = 0
    simp [bls12381EndoAt]
  | some x y h =>
    have heq : y ^ 2 = x ^ 3 + 4 := (bls12381CurveAt_equation_iff p x y).mp h.1
    by_cases hx0 : x = 0
    · subst hx0
      have hy0 : y ≠ 0 := by
        intro h0; rw [h0] at heq
        have h4 : (4 : ZMod p) = 0 := by linear_combination -heq
        have h22 : (2 : ZMod p) * 2 = 0 := by linear_combination h4
        rcases mul_eq_zero.mp h22 with h2 | h2 <;> exact zmod_two_ne_zero hp2 h2
      have hy_ne_neg : y ≠ -y := by
        intro hyn
        have h2y : (2 : ZMod p) * y = 0 := by linear_combination hyn
        exact mul_ne_zero (zmod_two_ne_zero hp2) hy0 h2y
      have hne_neg : y ≠ (bls12381CurveAt p).negY 0 y := by
        simpa [WeierstrassCurve.Affine.negY, bls12381CurveAt] using hy_ne_neg
      have hfix : bls12381EndoAt p hp2 hp3 β hβ (.some 0 y h) = .some 0 y h := by
        simp [bls12381EndoAt]
      rw [hfix, hfix]
      have h2p : (WeierstrassCurve.Affine.Point.some 0 y h) +
          (WeierstrassCurve.Affine.Point.some 0 y h) =
          -(WeierstrassCurve.Affine.Point.some 0 y h) := by
        rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne_neg,
          WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        set s := (bls12381CurveAt p).slope 0 0 y y
        have hs0 : s = 0 := by
          dsimp only [s]
          rw [WeierstrassCurve.Affine.slope]
          simp [WeierstrassCurve.Affine.negY, bls12381CurveAt, hy_ne_neg]
        constructor
        · unfold WeierstrassCurve.Affine.addX
          simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
          rw [hs0]; ring
        · unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
            WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX
          simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
          rw [hs0]; ring
      rw [h2p, neg_add_cancel]
    · have hbx_ne : β * x ≠ x := by
        intro heq_bx
        have h1 : (β - 1) * x = 0 := by linear_combination heq_bx
        rcases mul_eq_zero.mp h1 with hb1 | hx
        · exact beta_ne_one hp3 hβ (sub_eq_zero.mp hb1)
        · exact hx0 hx
      dsimp only [bls12381EndoAt]
      have hsum : WeierstrassCurve.Affine.Point.some (β * x) y
            (bls12381CurveAt_nonsingular_of_eq hp2 hp3 (by
              rw [mul_pow, beta_cube_eq_one hβ, one_mul]; exact heq)) +
          WeierstrassCurve.Affine.Point.some x y h =
          -(WeierstrassCurve.Affine.Point.some (β * (β * x)) y
            (bls12381CurveAt_nonsingular_of_eq hp2 hp3 (by
              rw [mul_pow, mul_pow, beta_cube_eq_one hβ, one_mul, one_mul]; exact heq))) := by
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hbx_ne,
          WeierstrassCurve.Affine.Point.neg_some]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        set s := (bls12381CurveAt p).slope (β * x) x y y
        have hs0 : s = 0 := by
          dsimp only [s]
          rw [WeierstrassCurve.Affine.slope]
          simp [hbx_ne]
        constructor
        · unfold WeierstrassCurve.Affine.addX
          simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
          rw [hs0]
          linear_combination -x * hβ
        · unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
            WeierstrassCurve.Affine.negAddY
          simp only [bls12381CurveAt, zero_mul, sub_zero]
          rw [hs0]
          ring
      rw [add_assoc, hsum, add_neg_cancel]

/-- **Algebraic Soundness of the BLS12-381 Endomorphism Order Criterion (`order_r_of_endo_eq_at`):**
For any prime $p \notin \{2, 3\}$, primitive cube root of unity $\beta \in \mathbb{F}_p$, and
point $P \in E(\mathbb{F}_p)$, if $[u^2] P = -\phi_p(P)$ (where $u = \text{bls12381Seed}$),
then $[r] P = \mathcal{O}_p$ (where $r = \text{bls12381FrModulus} = u^4 - u^2 + 1$). -/
theorem order_r_of_endo_eq_at (p : Nat) [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (β : ZMod p) (hβ : β ^ 2 + β + 1 = 0) (P : (bls12381CurveAt p).Point)
    (hEndo : (bls12381Seed ^ 2) • P = -(bls12381EndoAt p hp2 hp3 β hβ P)) :
    bls12381FrModulus • P = 0 := by
  have hu4 : (bls12381Seed ^ 4) • P =
      bls12381EndoAt p hp2 hp3 β hβ (bls12381EndoAt p hp2 hp3 β hβ P) := by
    have hsmul_neg : ∀ (n : Nat) (Q : (bls12381CurveAt p).Point), n • (-Q) = -(n • Q) := by
      intro n Q
      induction n with
      | zero => simp
      | succ n ih => rw [succ_nsmul, ih, succ_nsmul, neg_add]
    have hexp : bls12381Seed ^ 4 = bls12381Seed ^ 2 * bls12381Seed ^ 2 := by ring
    rw [hexp, mul_smul, hEndo, hsmul_neg, ← bls12381EndoAt_nsmul, hEndo,
      bls12381EndoAt_neg, neg_neg]
  have hchar := bls12381EndoAt_charpoly p hp2 hp3 β hβ P
  have hsum : bls12381FrModulus • P + (bls12381Seed ^ 2) • P = (bls12381Seed ^ 2) • P := by
    rw [← add_smul, ← bls12381FrModulus_seed_identity, add_smul, one_smul, hu4, hEndo]
    exact eq_neg_of_add_eq_zero_left (by
      calc bls12381EndoAt p hp2 hp3 β hβ (bls12381EndoAt p hp2 hp3 β hβ P) + P +
            bls12381EndoAt p hp2 hp3 β hβ P
          = bls12381EndoAt p hp2 hp3 β hβ (bls12381EndoAt p hp2 hp3 β hβ P) +
            bls12381EndoAt p hp2 hp3 β hβ P + P := by abel
        _ = 0 := hchar)
  exact add_right_cancel (by simpa only [zero_add] using hsum)

/-! ### 136-Step Kernel-Checked Certificate for `[u^2] G = -φ(G)` Modulo `bls12381FqModulus` -/

private def subMod (q a b : Nat) : Nat :=
  (a + (q - b % q)) % q

private def ecDoubleMod (q x1 y1 inv : Nat) : Option (Nat × Nat) :=
  if (2 * y1 * inv) % q == 1 then
    let s := (3 * x1 * x1 * inv) % q
    let x3 := subMod q (s * s) (2 * x1)
    let y3 := subMod q (s * subMod q x1 x3) y1
    some (x3, y3)
  else
    none

private def ecAddMod (q x1 y1 x2 y2 inv : Nat) : Option (Nat × Nat) :=
  let dx := subMod q x2 x1
  if (dx * inv) % q == 1 then
    let s := (subMod q y2 y1 * inv) % q
    let x3 := subMod q (s * s) (x1 + x2)
    let y3 := subMod q (s * subMod q x1 x3) y1
    some (x3, y3)
  else
    none

private def ecMulBitsMod (q : Nat) (base : Nat × Nat) :
    List Bool → Nat × Nat → List Nat → Option (Nat × Nat)
  | [], acc, [] => some acc
  | false :: bs, acc, inv :: invs =>
    match ecDoubleMod q acc.1 acc.2 inv with
    | some acc' => ecMulBitsMod q base bs acc' invs
    | none => none
  | true :: bs, acc, invD :: invA :: invs =>
    match ecDoubleMod q acc.1 acc.2 invD with
    | some accD =>
      match ecAddMod q accD.1 accD.2 base.1 base.2 invA with
      | some acc' => ecMulBitsMod q base bs acc' invs
      | none => none
    | none => none
  | _, _, _ => none

private def bls12381SeedBits : List Bool := [
  true, false, true, false, false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false
]

private theorem bls12381SeedBits_foldl :
    bls12381SeedBits.foldl (fun acc b => 2 * acc + if b then 1 else 0) 1 = bls12381Seed := by
  decide

private def bls12381CertInvs1 : List Nat := [
  0x3a0ab1094f9aac23ddb7932e0787dc53fbdac85b6e9df9252a6c2653213975f7c75c41318b68544e88a5cf31e7a629f,
  0xe1c24c0d56fa3d8211980fb07694adafba76962f6a91a6151f6a9fa8d9bf53e837a1edc1e4392401a13ff7ba5158432,
  0x131567629f9e3a6a3a1da30532ce1931d318e535662edc150dfebe5869e34a0ef1824f7d4693c7e7326461d4bf9ad3af,
  0x13cc60c53640e42d65401ca51c1ae10abc7aa256fa12e783ca2c2b32c3f8be6f9d0cf9f3b21c925a1ab28ec3937b83b6,
  0xc02fe19ebe0aceb211c3bfb9cf67e61f3b0a0e63dd522b6cd32a0b6922efd345af14ef4aafaf3e0d7de39c1da9be3f0,
  0x1616d9803a659e77544549e5ec75306f898aa2881ff6787ef73844da5cb50083f66a696d2b69fbf692d91ea788029757,
  0x421193c536f316439f69969437d8bd59c5f3b646c3b7a691ad2d180aaeeb9ba3671134ecf1d8df3b081d7c3cee91437,
  0x1136ec87bb90ea49940d884d8f31c370adcccef50e0ba2fbc93e4f7309ea494ff822b5271631412a2b1c8ce3161f87eb,
  0xedadb6946160b2e1faa8f411e7d10808427d9f006c353036f763f76c154e0851335d9c339a61d44501d3f0c282ce924,
  0x11f90bd95ec51ac26644b6a32f1b600a1c5bff7931bb2290ff7d2a1f169872f279d40682b9f37f95a72cd31bb3722823,
  0xa85899ce3846da3ca28907ab3fe6cd38ec478c96d280e516807563480a8b1a80f377e349e90aea5c9fbff44dc0e6eb5,
  0x3a6c6f493550cae92f6972d5444cb25265869bc04c786dff106b026a8bab7d0b44856a2917ce4ba16140debb558c809,
  0x94bf24b40ea9b49435d401672f05c9a1f120dcc241147eba6266aed5560a84ed750ae9c9691eb486d29ddf6d5515b4a,
  0x19272c28ce0bc2af427f06989157e47b67d7211a5d689a8c8442dc16c680d1fdf315e292f0c4686bac26d6ccd07bb7df,
  0xce53e64115bc677827faf2baaaf9d36bab94eac7f2d2e0a26ae1bfcd1ce8a02f9a98972a47724bdb8eb9f5c3bfe9307,
  0x153640e01dea315f8b4537b4b5e21cc5f51e8b347e8097e11318f3a183c2cb9ccbfefb81e39b1e6e9da2690ba45d2a58,
  0xc604208e0cdedc0f2c136fb9c99249530aa1f0268e0273b3810ab908786249a12d4830c0c35015af1d32658b400569d,
  0x8f073bf7957797355d22e919e709d636580e52c750f8ffe0fcb8892b38655dadc39d7dad263021d280cc07408b5a7bb,
  0x6e68e09fb8d2e604b8419cd74ea4a6c2b632f8130e2c4c8e02f6f397948c09f4236f2ea677f7b2c48df4cbdd8a07b3b,
  0x14c3f558ffff9a4263be61a7e3b91ba0a8bf9363b36d20b78f526fdbdeeac7579b62026777cb5953fa4f68614786ce72,
  0xe8785da5a91f326283fd24bfca7ebd17a9b4ae65cd5fe47031742c962d815239f3b83edaedcb1d59a0d59eb22475a9,
  0x9890d93a5984ea767e16565e7a6add53af9e70249def2470b5294b72b225d6fc6ba89afe085f99d55b12ce5eab1009e,
  0xfaeedbce12ef85eef3b4b99d4839d5708e6369c7f3cc2a1d9675bf60cb9bf11347fe83ac74170ee4240f186835f63d4,
  0xf7c1e083a99468c936cf048594f49832156c84835eea11f51d82b85149426ec566a47fcfc782da1517fa3c1f487adec,
  0xf6591dd8add7c90ad80e69674656edb1e1046872a052b77a761527954726e1b7c5957e0ad6f3d61a66d3dc9ffa00e11,
  0x16f91a6d1f0649e95c01a19e2ca49cf5717b60d071e4b28f574429daa03a3a6967972b7d41c4357cab917f2cf7a0b9b6,
  0x180d9208ca7dbd2aaefc7d37627ae477599d7435281dd410842884f64442f5e4876a5ffeba004b149201768221587bca,
  0x62a187c4a52c9bd374379495daf433f788804bca610c88948195f9a14efead1af5e9cd1f77279d4c0b5f37e5522dcdb,
  0x791fb1bfa5f0928a0d1bc5069a795e8faf00c70b33b090b8167ff79d99692b626dab4d3647fc39f24aeac35b7c2052f,
  0x319c74572fb2f11f58160386d2e99fe5a0c330ae4f8a0683c62d59cff0b6774680da643eb938bafe92ff5b6c2d22cd5,
  0xaf5a33306133962f16374d7eca903f96674eb3c36b46d405ec562d138912cecc2e1df7c931fae6828b750836863756b,
  0xaa0e7cfc0b0893078d92eed5ca1a24f932844dfa56a473361c7e2b2abacd9b25bd48dbd22f5f898eb63cb26275da66a,
  0x136cba683dc6d1a8a207368d00c041468c95811dac6f31fb29aec270f60aac98ea21a7c0e8e91708bad16bcec9a8f2ff,
  0x602fa7bb509319883e2c7564bb143e496355cfaaae22f63295d76a7f3308063da28b4f26348e443079085844ff54559,
  0x27123018728b54217a0c4c799341e31e6e6aac9a0bb61cd8b8accdd4b3b3c822dad9c6a29916fdec9cccb0bfa5f163a,
  0x3dc023ce3c6bf578c79fa61d1c1044bbb78eda0e251fc5deb063667d6390e64b0a01313c40572ec772181227cdb3742,
  0xeb55a4b0e71baf7c7c5dcb691c0248ca2b74b4d5601cc95539887acf997d6879fe60ed8d25a9018f6cf5b25fa007f16,
  0x10504ea5219f1760113a111df8e83ae38cbc680fab9e7095687023ffac5191e5953169c92f59c3923b6176fbca9c941c,
  0x3e5c395f983c995e0f069a482a61eb2a7587873d951dbc59a1171c4890e90fe4c3eddb057a5dead39d000ed5c7bb0fa,
  0x13da610889d11f03c763d947ba75ba415597f1eb8bb4cf5d6c49e8d5972c1e83aa97e87818616bc5ef6f8d917e294952,
  0x1198304905043324ebf3f53271cf06f5c1fa341e747fc2e63ae6576d97b92a9b3ca23952ae7f216b2964bd3366d759bb,
  0x11a7783c9c047b8fefd80e7d2dd12ad0b2e246e873e8f46b916769b88bd55dfe49e39be4a4c82c78388e8167c89e3abf,
  0x1298f157f7fa19b88ae3ceb571595802bc33eb44083bb54831c5760a74ab9c17f87c02bff8196bdaa5b2f49beceb880c,
  0x158a5561fbb3de468fd4fb2e7f166138fe2fc569999a6174e3040677313ae034b44a6dc0307c5090b6bf80097c4d4d00,
  0xb3ee5c29b580a6326b49677e418fb0f4c7381e842613372232d589098f2166067c5c29b868744a4d55c9fa30a2fe199,
  0xbe535c6240eb30a1516985e0f56c7d47b9848fff24a92571a243f3b900adba413c4de73ab832ae8ac48174c60898b1e,
  0x86ba8d250db90d9554ac47f8a00a311a7389bf63c05551d5ca2d82ae913936edf2aab645420f4c85e7c6b1aaacac790,
  0xb747fd4c7f644b96482d18e8cf7ac8b966e7fc8f469c1825e002b93b67035b328ef582ca5c22c67ec347cd7b99bc6c5,
  0x1385b0a8d342cc56c5515cbea06247b4e02c62b5c817d8766bde26d0091d4b6ef15f49b7d8a744a00b855f7a45975c30,
  0xdf86c1debb49adbe47e98442e1c3ffc32bd225c484e885c554b471e183f82dd74365c8ad37586f539edeb787f123bad,
  0x2762ec77eeef0d8c83fcbd905f47024eb91dc3e21c335e451a55e70b1a602d9b7ae3c2bc57791582d28080af50200bb,
  0x10167969e08b4c65fb11b1c47aa6b7b40413184d71d98577677bbeb03fd77c9909e0e547aeb79507f7b6cf520e36e670,
  0x574f0eea3a815bf01f8abcc32ad97d67f00e1b6b2cfb481fbfe3e46c42588daab7923fe0f53ac42154fc798ac425134,
  0x9d806e3bc242129d05ae1f42f744f14fd48deddb50f174a399d3dc1eaf5f093727b1780dd21de07d57cdabea32bf2c4,
  0x13d4b6c42328b0b752125c1ab53b929bc2548dc7b1b40fd9f6018f005d92701ff336ae59594f8622487dfdfce3a08eb7,
  0x1193dddf415dd0e86d66a34c845668d6e33e4d6cb07c28d80eea6f89b934451e06d783dc34108fc2757497a065804f59,
  0x50f80fb2cc6173730ef7c8abaa8af1bb52e9220a47da75e1fa08c44cc754c4ef0366f3f8adb516a450ee3a6569b0a50,
  0x19833bb452680c7acbb8adf7d35f00d443df68846bc26c4cbf0848c993cefc30b540a0931a9aade1a378fc15968b3d6b,
  0x104b08170ef5c3c4fb4b8de8c3ac1aef561118963b20459fdd7fc9d517de51dfe9b2967e041ba812f57cbac278b0c4d3,
  0x207a54987e42fa6c957857914fff8d752311592c98ed0bd058e3c2368e3ec601b9fe9c0c6bc58aa48aa2f4fc63c787f,
  0x6d2c1426ba8e5becf161fa3d21d1d4fb2db36857e2280d1ad53352995b0d6c63d88d108ba25d33c4a23056b82579c9c,
  0xdff7370c8b04f9dab3cb137d61bafb39542b16220ced9ff0ecc63e3db38fad4e57577f1a69aed4096cd077b1c6dac37,
  0x30ad3c7658605881e8522e9b32565d49941de0ea929a14415c3dd7f17aeb64aba222773e495067e17b853fa34e5805c,
  0x1882518a35725e794903421a5ee2472c469afc5b6c02ba833a8388d3a17a19114a4c909bf5297b6a3364e34cf310d785,
  0x12d6db586a90b7b81f9cc99b5e2f7770d07cf70d611bcf233a804353cbd15b923a2d5cf8b4394e15e99df35fb3cfe762,
  0x3474f62140f86154b8d1bd1d7112ce6000a177204440f1eb08a9bd1138e6904d2e0c92e3e3b1b273d53424d4a64bcce,
  0x6beb2de8c25d7148b0844519bbb0e80cdbf27e02e9c80311bcd82a41c37d3f5a5bcc133db81e26f88e4f3f55053f604,
  0xdeb7089ffbffeeebed9e3a62a1e61d0891879afb2191fb18172226fbf67af57a4ad0b8b29850ee3cb2cd0a8419edae5
]

private def bls12381CertInvs2 : List Nat := [
  0x2a1f1e905271596a4fd5f4783e6e67451f3679f0c2f22be8dca10a94d83da13316fe211c6f9156e6c254d3406b6633,
  0x8dd266bc8a4327955749a1f6687a936ea86e5631427c1466a31e637c3b21269ce7a79e2d6d66ec3438c8ea30f6cffcb,
  0xeed4f0d90465f25fc86d26bfbc1f98734c161f0ecd18b761f3a543c2e0cbec71dae101d09e36b3384a75e7a931d0134,
  0x1598b0cbcf0959139a824b05ebbb7918cbb623d20234990cfd081290735f3a3f6a40bb13aa0e1c06c500c6ea6041f62d,
  0x80aa2b7a5ed4d7defd36c7373e7f033d1d260f2052a48cad241b50b97de76cf99bef84dc814809fe8f550e30326459d,
  0x807e5b39c22b1204006adf7a729a7a4d96aed8c84a8c3c18599d9a04b800505553d66b71a61eca5a9b2b4a0376eb090,
  0x1630c0fea69febc3c0c0554066bdfb16d450cf99409ac93a0cec6c9c2a1c74b9ac8539ddc867cdf512e0a8767042167c,
  0xfa739a6baf8329682f71021b68b49cdaf35075ad20ae9fd5fdd012e1bc54fe05a82532d0b946f1262fd838842fd7dd0,
  0x40fae3c5170238148b4d5d0c883536074c232fa7e9f1646ab492c22958ec157c76f8fa4f2950761c665d94b9da10bbb,
  0x673d309df8a1f7120889c8a0f8a8bbe3cbc55e620de8ccc71fbd634a9216936bb58a9219cec16a8da114e5d8604fe02,
  0x702521cbf5bea2950055d44e5fe4b96836e2972d702d376fb700276a62b196b59e1b7cf342eef5a22b892f7039720e6,
  0x119f1ef48b4716b02127b311736054f707d7e144d285dc0a33d7c27e93ea3be2e03cf99796c2f33fe099993190f36340,
  0xbd77c54895aae49eced4faebb0016d96a0b5fdf808a698511fca9e7476b3e6f6543bc876fce82f413e9b2ab419937c2,
  0x1340529b5879b3b72d9014b6270bcc2566a61498050a179e03585c94099c965e837051925c56557a053cb415a48fe432,
  0xa4c854db57dd9b0fb1ac40c7e752205b1d3cba752f40be3390b5dd9419f4d6cbe078a59eb86673783309de79416e53,
  0x1e140e7989565469e719ab4900aa46fa61fa7a939967c0456b1ef7062b7b9c9b760515b0b0a5c6233ac3a53a9814016,
  0x165bd7577a581c1479909075f9c7568ef5d52285efbe150bee08ad680b5b9de18760cd008dcf6bd5468eb8a45ac00984,
  0x82b3cf719a58711eb4cd546e1d7488200b89e606b1efd973f32d9597b50ca2e7a322132efd3561f28d2cbdd5b08d89e,
  0x31b09df8f38cbfc0e3ba971df5bd97ff2e7830ffabe78c4f4a861ad5d1ff841f6c0692be5ad644ffe0e060dad5ac97a,
  0x16c9c950169a09f26218236a23e9c2c9f8c10a0514470e122245b72c9dd82b6fd2be59906c47977ed395983638414953,
  0x4d24c5cf06553b0d94f24aaca6e15079ec2d5c5cf0f5308596d5df03bf785b8e4690c571e7f3bff2919b1e20a9003a9,
  0x70c0a6b552aa878f8e2e1c7158a18081b19b3fee774ec6f9333a8831126c1afdc433e633cb55594c96f7f2ccef609f7,
  0x14b464ccc3a292e812fb1bfefba9d5312b06881d6021f8798e633ade30d235d05f81c23b7039abc544f1055262746817,
  0xe69e2e824f61c636723b492b275439228e6a8ec6ca86f7985e991ce12493b07ad9f56119ab138e46a36cc9622ad2dda,
  0x1824787614e31ffecdc4f3d78e0b1100d30762ca275f21581505d27cf2f92d80df8c3484fee57cf7a5e7558bc639f76d,
  0xdce75c90d1033aefdfa739ca912abb8dbf8f96cbcab3c5a5b301bea12a8b586c155fd99513261b04eba79af84af6808,
  0x973a0b9772399b0a88b19a8dc02aa1076292cfdc5650ba63a9add1e26ad51df711b07058c10c817eb85a79ab4c3838b,
  0x8f118e4f59199a05698b139ea8c29eea325a6c0f05d954e52be3333f2d46d235d594a3206097f3c990c866b492abf7e,
  0x1464072492c8e7ae6355abfdc3acab6e6b0d44ea3d1f021c38c36edaf316417fefb8e278ee8d92e1d239316d45a677bb,
  0x2b3b4f7fb50265799bd84342aa798abfbfbb5ff5b28076741aca51ba9412f613dddbba2bf99f7bbb646f361f17e982c,
  0x8d0d1686ec4702fc15d8e87eb65a27dee8f1c64e2e5073b13c697fa162e997b031b704dc7c505b34cfa9c077a53c9f1,
  0xaff742f0226ca5ce04fe4cc1986b828dccbe69a152bbadad65c6237923ddea04f90f8ff56134c73944cea096105c291,
  0x4a1296cfa1247a79931975820227ea26423d14050f00fe8a36a0bfe1ea94d42378905a12c2da9682b1b70793b74074d,
  0x6c0898c9ba792222fb888a665e96ec27b44824d083fb0fec24e5680034122aff27b2644dcb29ff0e54c6ffbe6a34da4,
  0x9bc406a3001124776c0d2558ab18b5b893352b0357da4e2eb08c8d71a9134e84212dc3710032b272d6f9b2dad15cd48,
  0x92e59725bba49941a28c987b6b85525de09c2c93f3fdc38005cb62cf0b4a6160a9dc82dde412ea4296ee5e5e0434393,
  0xbbe56706d264aae0c7ccd0986b3a01f8a2d3f0fe2a8a8950a21b7b4e6bb32fbca0fad95043406c4948e31bca2a81fdd,
  0x13000630678c26d6f0b332de77bc583243e25a62a8bef909aca9dd76862feb3d92fcd47dade21ddb7bf5107bce34e627,
  0x1d78654723a3ec35bb1c392ff7866a5b3cf1d0aa0aeef5279f9e5c5c083621e4b405851b12dc8a4d21c52801f24d9a,
  0x66cd974e0b885bbeb0902e6a2221d3e6b319b069aa4e5ac4adc7fe746f1f3f9b5bcb67561a50f5a356e06dad76716dc,
  0x86f1757ba110aefc3edb8ca4ab18fce49d4818b69bff3ce95f6f257bb9681afaaf139bce4712542f0c3f62294ea96db,
  0x128f740feb7ab15ec815cb53d01a23bd1e0ae757c023a1829b82e8ce143330bcc3d420ca7b5ce74480fae7723ce9128c,
  0xd9e998adcace5df4b4a7cdae83d6aa16c194effc374a78e38ad085ff7b3c54ba1cf8e42187a72babda8c5f1c537e9be,
  0x26b3a477cc4c20b536e854f0d7ee62ff2fc555ef8fd69440ba2c04b9b8c059d146bdad1f4a8130230a301d90f9c17c5,
  0x72927b8008e89996afd4cb761b4d4b555b760f5718b445bc23470a1b2eb0636cc4d19555d2d42542dfced4595b016d5,
  0x189a48ca47f88a1f95c05727ef0653f6ed1fa6963bd340d0e6c514c97b4c4bc60b050ed41dbb9c7545a51848e90cd773,
  0x342fd01833caba6cc5171308dca10ffabc05caf740fa6d3779f70d3696429c7b0665ba42f464209726cd01d304fa28f,
  0x1487cf2edcc111daabc9938e7afe684043d4e39e80a25b78d34837707b48afae4c9d7bc3547f9d02fb17a31e33facd02,
  0x172c9cb937d8a18577024844cf34a6304270c5d1585ed89947ce59e2ce3a05cf335429fcfc9751c17b17f255ac01df04,
  0x9aa23bb3d7260f5191159b04d89581b8af9e062fd30edabc0bed40b6c1f295d311d53b80ad1fa583ac9124297f7d71e,
  0x169fe30e6822d0f80e2e39ff7df61021a7980d18c304793841ca9fe7e5e10bcf68f9d15a321e24865dd672dfefd8ec68,
  0xca10a5b5214e416d3d7a23ea7189e08a605814d96150f79c72cc2f4d3f0174775f615ad5d56bd12496ac84de2a64545,
  0x79fe6b97d3ab2de2967a232b81d8a60c9d20347d57acdbc2ea323bb290c9aed011dbf62d6df3c0ad1edf89c909c31fd,
  0x18024edb2035bc8a723c267d13288c41f1af6a5ae5c5c313458625962858070dfda354606bba1cdb2bd599e923165993,
  0xdee135766830c267cd223801f5b43a2225a16a6ae8f060931d47e617845af4bb3103557b3d3c225434d646bb1615213,
  0x1057cb45a1fd87306b0cffa6da630fb74bff54eaab53d008b14175566bb12dbf4f52d5390e6fdde055f07857c1ffca3e,
  0x18e394775707927dc09e699cecda0b3f0cef31956f6cb6c81481ab9550bedb369e3eb3486d8ae304c886557bc768974a,
  0xc33d176fc78a276973ba90a4df36afa917838b9bea0f7b5d0c29fd94dea06a2ce0b37ecec726aa10e8db90e77a1b0ad,
  0x106351c3bbb36f5856f1db1128147393f3a703dce38c4c8b6a1b3950ed862fa3879939b8fa135d3da777118d7da0ab25,
  0x6585b5cff8aebcc3adc594d0d09cb53b213671c6690e5f61563ae969ea94b7328ed099eabfdf05be0832c8911114759,
  0x10d9d9e0a0ff68d9da16b3e6c8d454c69af1a158b7f4398e45070bb1ae9af4ed3a19dd6fcdb6064007ccbdc9e89bc73c,
  0x4404b8466448fa564393a508c1f06f52600c0727676fe93ea21e88dcdd836c595ebb5a80c0003ba23ec8faa6e80c32d,
  0xcb92d519d869c21cea164293b42e831506c412d0ca7a420f4c78778643bff239110ef8e6f25f43aec42cf450797a109,
  0x123602b110b5787d94e8d673ae9fabe5221b8ac8cedfc2f10699c8d89569a18b13a8d113f7ecd2dcec30d89415d2b4bb,
  0x17b081659aaade109e3be3b2d41d046910821201fba2169acefed98dffd84cb620f80802f48f64b2ddb87fc01f03b4fd,
  0xac3c564ebcae98d4901030c56ad7452ef18efcf529b7136adf0757213410b484cb772e0cc4c49a503921b9a1fc06275,
  0x19f7e6231db59ee258b0a13da99325bb88d7aea7f0464e5f2a616324ac9cd8b8ab59ed714d1e93c5fe09dea2f8df2648,
  0x39ec84d24768e16c3c3b71f6c45d602cc38e8aecf01fb0108ccb9e94fe6779fa2f9f384f7a75bc5ff8bddfa8d99dfc
]

private abbrev bls12381CertQ1X : Nat :=
  0xd3aff0f3b2e6f4878f15a81eabab5d8c9f765bc93ae0a2f0da5ed1941b4924bca4516661600c41a74beeb243695b52d

private abbrev bls12381CertQ1Y : Nat :=
  0x332c926f3b2fecd11c514e777933c8b994de733bdbc6688fae276601803ba0296976fb0b97f36d2fe6456a9444dcc00

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
private theorem ecMulBitsMod_cert1 :
    ecMulBitsMod bls12381FqModulus (bls12381G1GenX, bls12381G1GenY) bls12381SeedBits
      (bls12381G1GenX, bls12381G1GenY) bls12381CertInvs1 =
      some (bls12381CertQ1X, bls12381CertQ1Y) := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 8000000 in
private theorem ecMulBitsMod_cert2 :
    ecMulBitsMod bls12381FqModulus (bls12381CertQ1X, bls12381CertQ1Y) bls12381SeedBits
      (bls12381CertQ1X, bls12381CertQ1Y) bls12381CertInvs2 =
      some ((bls12381EndoBetaNat * bls12381G1GenX) % bls12381FqModulus,
            bls12381FqModulus - bls12381G1GenY) := by
  decide

private lemma natCast_mod_of_dvd {p q : Nat} (hdvd : p ∣ q) (a : Nat) :
    ((a % q : Nat) : ZMod p) = (a : ZMod p) := by
  have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).mpr hdvd
  have hdiv : q * (a / q) + a % q = a := Nat.div_add_mod a q
  have hcast := congrArg (fun n : Nat => (n : ZMod p)) hdiv
  push_cast at hcast
  rw [hq0, zero_mul, zero_add] at hcast
  exact hcast

private lemma natCast_subMod_of_dvd {p q : Nat} (hq : 0 < q) (hdvd : p ∣ q) (a b : Nat) :
    ((subMod q a b : Nat) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  unfold subMod
  rw [natCast_mod_of_dvd hdvd, Nat.cast_add]
  have hlt : b % q < q := Nat.mod_lt b hq
  have hq0 : (q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff q p).mpr hdvd
  have hsum : a + (q - b % q) + b % q = a + q := by omega
  have hcast := congrArg (fun n : Nat => (n : ZMod p)) hsum
  push_cast at hcast
  rw [hq0, add_zero, natCast_mod_of_dvd hdvd] at hcast
  linear_combination hcast

private lemma ecDoubleMod_sound {p q : Nat} [Fact (Nat.Prime p)]
    (hq : 0 < q) (hdvd : p ∣ q)
    {x1 y1 inv x3 y3 : Nat} {P : (bls12381CurveAt p).Point}
    (hP : ∃ h1 : (bls12381CurveAt p).Nonsingular (x1 : ZMod p) (y1 : ZMod p),
      P = .some (x1 : ZMod p) (y1 : ZMod p) h1)
    (hstep : ecDoubleMod q x1 y1 inv = some (x3, y3)) :
    ∃ h3 : (bls12381CurveAt p).Nonsingular (x3 : ZMod p) (y3 : ZMod p),
      2 • P = .some (x3 : ZMod p) (y3 : ZMod p) h3 := by
  obtain ⟨h1, rfl⟩ := hP
  unfold ecDoubleMod at hstep
  split at hstep
  · next hcond =>
    injection hstep with hpair
    injection hpair with hx3 hy3
    have hinv_nat : (2 * y1 * inv) % q = 1 := by simpa using hcond
    have hinv_p : (2 : ZMod p) * (y1 : ZMod p) * (inv : ZMod p) = 1 := by
      have hc := congrArg (fun n : Nat => (n : ZMod p)) hinv_nat
      rw [natCast_mod_of_dvd hdvd] at hc
      simpa [Nat.cast_mul, Nat.cast_ofNat] using hc
    have h2y1_ne : (2 : ZMod p) * (y1 : ZMod p) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hinv_p; exact zero_ne_one hinv_p
    have hy_ne_neg : (y1 : ZMod p) ≠ -(y1 : ZMod p) := by
      intro heq; apply h2y1_ne; linear_combination heq
    have hy_neg : (y1 : ZMod p) ≠ (bls12381CurveAt p).negY (x1 : ZMod p) (y1 : ZMod p) := by
      simpa [WeierstrassCurve.Affine.negY, bls12381CurveAt] using hy_ne_neg
    set sNat := (3 * x1 * x1 * inv) % q
    set sSlope := (bls12381CurveAt p).slope (x1 : ZMod p) (x1 : ZMod p) (y1 : ZMod p) (y1 : ZMod p)
    have hs_p : (sNat : ZMod p) = sSlope := by
      dsimp only [sSlope]
      rw [WeierstrassCurve.Affine.slope]
      simp only [↓reduceIte, WeierstrassCurve.Affine.negY, bls12381CurveAt,
        zero_mul, add_zero, sub_zero, hy_ne_neg, sub_neg_eq_add]
      have hden : (y1 : ZMod p) + (y1 : ZMod p) ≠ 0 := by rwa [← two_mul]
      rw [eq_div_iff hden]
      dsimp only [sNat]
      rw [natCast_mod_of_dvd hdvd]
      push_cast
      calc (3 : ZMod p) * (x1 : ZMod p) * (x1 : ZMod p) * (inv : ZMod p) * ((y1 : ZMod p) + (y1 : ZMod p))
          = (3 : ZMod p) * (x1 : ZMod p) ^ 2 * ((2 : ZMod p) * (y1 : ZMod p) * (inv : ZMod p)) := by ring
        _ = (3 : ZMod p) * (x1 : ZMod p) ^ 2 + 2 * 0 * (x1 : ZMod p) := by rw [hinv_p]; ring
    have hx3_p : (x3 : ZMod p) = (bls12381CurveAt p).addX (x1 : ZMod p) (x1 : ZMod p) sSlope := by
      rw [← hx3, natCast_subMod_of_dvd hq hdvd]
      unfold WeierstrassCurve.Affine.addX
      simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
      push_cast; rw [← hs_p]; ring
    have hy3_p : (y3 : ZMod p) = (bls12381CurveAt p).addY (x1 : ZMod p) (x1 : ZMod p) (y1 : ZMod p) sSlope := by
      rw [← hy3, natCast_subMod_of_dvd hq hdvd]
      push_cast
      rw [natCast_subMod_of_dvd hq hdvd]
      unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.negAddY
      rw [← hx3_p, ← hx3]
      simp only [bls12381CurveAt, zero_mul, sub_zero]
      rw [← hs_p]; ring
    have h2eq : (2 : Nat) • WeierstrassCurve.Affine.Point.some (x1 : ZMod p) (y1 : ZMod p) h1 =
        WeierstrassCurve.Affine.Point.some _ _
          (WeierstrassCurve.Affine.nonsingular_add h1 h1 (fun hxy => hy_neg hxy.right)) := by
      rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_neg]
    have hns3 : (bls12381CurveAt p).Nonsingular (x3 : ZMod p) (y3 : ZMod p) := by
      rw [hx3_p, hy3_p]
      exact WeierstrassCurve.Affine.nonsingular_add h1 h1 (fun hxy => hy_neg hxy.right)
    refine ⟨hns3, ?_⟩
    rw [h2eq]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx3_p.symm, hy3_p.symm⟩
  · cases hstep

private lemma ecAddMod_sound {p q : Nat} [Fact (Nat.Prime p)]
    (hq : 0 < q) (hdvd : p ∣ q)
    {x1 y1 x2 y2 inv x3 y3 : Nat} {P1 P2 : (bls12381CurveAt p).Point}
    (hP1 : ∃ h1 : (bls12381CurveAt p).Nonsingular (x1 : ZMod p) (y1 : ZMod p),
      P1 = .some (x1 : ZMod p) (y1 : ZMod p) h1)
    (hP2 : ∃ h2 : (bls12381CurveAt p).Nonsingular (x2 : ZMod p) (y2 : ZMod p),
      P2 = .some (x2 : ZMod p) (y2 : ZMod p) h2)
    (hstep : ecAddMod q x1 y1 x2 y2 inv = some (x3, y3)) :
    ∃ h3 : (bls12381CurveAt p).Nonsingular (x3 : ZMod p) (y3 : ZMod p),
      P1 + P2 = .some (x3 : ZMod p) (y3 : ZMod p) h3 := by
  obtain ⟨h1, rfl⟩ := hP1
  obtain ⟨h2, rfl⟩ := hP2
  unfold ecAddMod at hstep
  dsimp only at hstep
  split at hstep
  · next hcond =>
    injection hstep with hpair
    injection hpair with hx3 hy3
    have hinv_nat : (subMod q x2 x1 * inv) % q = 1 := by simpa using hcond
    have hinv_p : ((x2 : ZMod p) - (x1 : ZMod p)) * (inv : ZMod p) = 1 := by
      have hc := congrArg (fun n : Nat => (n : ZMod p)) hinv_nat
      rw [natCast_mod_of_dvd hdvd] at hc
      push_cast at hc
      rw [natCast_subMod_of_dvd hq hdvd] at hc
      exact hc
    have hxne : (x1 : ZMod p) ≠ (x2 : ZMod p) := by
      intro heq; rw [heq, sub_self, zero_mul] at hinv_p; exact zero_ne_one hinv_p
    set sNat := (subMod q y2 y1 * inv) % q
    set sSlope := (bls12381CurveAt p).slope (x1 : ZMod p) (x2 : ZMod p) (y1 : ZMod p) (y2 : ZMod p)
    have hs_p : (sNat : ZMod p) = sSlope := by
      dsimp only [sSlope]
      rw [WeierstrassCurve.Affine.slope]
      simp only [hxne, ↓reduceIte]
      have hdx : (x1 : ZMod p) - (x2 : ZMod p) ≠ 0 := sub_ne_zero.mpr hxne
      rw [eq_div_iff hdx]
      dsimp only [sNat]
      rw [natCast_mod_of_dvd hdvd]
      push_cast
      rw [natCast_subMod_of_dvd hq hdvd]
      calc ((y2 : ZMod p) - (y1 : ZMod p)) * (inv : ZMod p) * ((x1 : ZMod p) - (x2 : ZMod p))
          = -(((y2 : ZMod p) - (y1 : ZMod p)) * (((x2 : ZMod p) - (x1 : ZMod p)) * (inv : ZMod p))) := by ring
        _ = (y1 : ZMod p) - (y2 : ZMod p) := by rw [hinv_p, mul_one]; ring
    have hx3_p : (x3 : ZMod p) = (bls12381CurveAt p).addX (x1 : ZMod p) (x2 : ZMod p) sSlope := by
      rw [← hx3, natCast_subMod_of_dvd hq hdvd]
      unfold WeierstrassCurve.Affine.addX
      simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
      push_cast; rw [← hs_p]; ring
    have hy3_p : (y3 : ZMod p) = (bls12381CurveAt p).addY (x1 : ZMod p) (x2 : ZMod p) (y1 : ZMod p) sSlope := by
      rw [← hy3, natCast_subMod_of_dvd hq hdvd]
      push_cast
      rw [natCast_subMod_of_dvd hq hdvd]
      unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.negAddY
      rw [← hx3_p, ← hx3]
      simp only [bls12381CurveAt, zero_mul, sub_zero]
      rw [← hs_p]; ring
    have hns3 : (bls12381CurveAt p).Nonsingular (x3 : ZMod p) (y3 : ZMod p) := by
      rw [hx3_p, hy3_p]
      exact WeierstrassCurve.Affine.nonsingular_add h1 h2 (fun hxy => hxne hxy.left)
    refine ⟨hns3, ?_⟩
    rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx3_p.symm, hy3_p.symm⟩
  · cases hstep

private lemma ecMulBitsMod_sound {p q : Nat} [Fact (Nat.Prime p)]
    (hq : 0 < q) (hdvd : p ∣ q)
    (base : Nat × Nat) (P : (bls12381CurveAt p).Point)
    (hBase : ∃ h : (bls12381CurveAt p).Nonsingular (base.1 : ZMod p) (base.2 : ZMod p),
      P = .some (base.1 : ZMod p) (base.2 : ZMod p) h) :
    ∀ (bits : List Bool) (acc res : Nat × Nat) (k : Nat) (invs : List Nat),
      (∃ h : (bls12381CurveAt p).Nonsingular (acc.1 : ZMod p) (acc.2 : ZMod p),
        k • P = .some (acc.1 : ZMod p) (acc.2 : ZMod p) h) →
      ecMulBitsMod q base bits acc invs = some res →
      ∃ h : (bls12381CurveAt p).Nonsingular (res.1 : ZMod p) (res.2 : ZMod p),
        (bits.foldl (fun a b => 2 * a + if b then 1 else 0) k) • P =
          .some (res.1 : ZMod p) (res.2 : ZMod p) h
  | [], acc, res, k, [], hAcc, hRun => by
    simp only [ecMulBitsMod, Option.some.injEq] at hRun
    subst hRun
    simpa using hAcc
  | [], _, _, _, _ :: _, _, hRun => by simp [ecMulBitsMod] at hRun
  | false :: _, _, _, _, [], _, hRun => by simp [ecMulBitsMod] at hRun
  | true :: _, _, _, _, [], _, hRun => by simp [ecMulBitsMod] at hRun
  | false :: bs, acc, res, k, inv :: invs, hAcc, hRun => by
    unfold ecMulBitsMod at hRun
    cases hdbl : ecDoubleMod q acc.1 acc.2 inv with
    | none => rw [hdbl] at hRun; cases hRun
    | some acc' =>
      rw [hdbl] at hRun
      dsimp only at hRun
      have h2k : ∃ h : (bls12381CurveAt p).Nonsingular (acc'.1 : ZMod p) (acc'.2 : ZMod p),
          (2 * k) • P = .some (acc'.1 : ZMod p) (acc'.2 : ZMod p) h := by
        rw [mul_smul]
        exact ecDoubleMod_sound hq hdvd hAcc hdbl
      simpa only [List.foldl_cons, Bool.false_eq_true, ↓reduceIte, add_zero] using
        ecMulBitsMod_sound hq hdvd base P hBase bs acc' res (2 * k) invs h2k hRun
  | true :: _, _, _, _, [_], _, hRun => by simp [ecMulBitsMod] at hRun
  | true :: bs, acc, res, k, invD :: invA :: invs, hAcc, hRun => by
    unfold ecMulBitsMod at hRun
    cases hdbl : ecDoubleMod q acc.1 acc.2 invD with
    | none => rw [hdbl] at hRun; cases hRun
    | some accD =>
      rw [hdbl] at hRun
      dsimp only at hRun
      cases hadd : ecAddMod q accD.1 accD.2 base.1 base.2 invA with
      | none => rw [hadd] at hRun; cases hRun
      | some acc' =>
        rw [hadd] at hRun
        dsimp only at hRun
        have h2k : ∃ h : (bls12381CurveAt p).Nonsingular (accD.1 : ZMod p) (accD.2 : ZMod p),
            (2 * k) • P = .some (accD.1 : ZMod p) (accD.2 : ZMod p) h := by
          rw [mul_smul]
          exact ecDoubleMod_sound hq hdvd hAcc hdbl
        have h2k1 : ∃ h : (bls12381CurveAt p).Nonsingular (acc'.1 : ZMod p) (acc'.2 : ZMod p),
            (2 * k + 1) • P = .some (acc'.1 : ZMod p) (acc'.2 : ZMod p) h := by
          rw [add_smul, one_smul]
          exact ecAddMod_sound hq hdvd h2k hBase hadd
        simpa only [List.foldl_cons, ↓reduceIte] using
          ecMulBitsMod_sound hq hdvd base P hBase bs acc' res (2 * k + 1) invs h2k1 hRun

/-- For any prime `p ∣ bls12381FqModulus`, `p ≠ 2` and `p ≠ 3`. -/
lemma prime_dvd_fq_ne_two_three {p : Nat} [Fact (Nat.Prime p)] (hdvd : p ∣ bls12381FqModulus) :
    p ≠ 2 ∧ p ≠ 3 := by
  constructor
  · intro hp2; subst hp2
    have hmod : bls12381FqModulus % 2 = 1 := by decide
    have h0 : bls12381FqModulus % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega
  · intro hp3; subst hp3
    have hmod : bls12381FqModulus % 3 = 1 := by decide
    have h0 : bls12381FqModulus % 3 = 0 := Nat.mod_eq_zero_of_dvd hdvd
    omega

/-- **Generator Order Modulo Every Prime Divisor of `bls12381FqModulus`:**
For any prime `p` dividing `bls12381FqModulus`, the reduced BLS12-381 generator $G_p$ lies on
`bls12381CurveAt p`, is nonzero, and satisfies `bls12381FrModulus • G_p = 0`. -/
theorem bls12381Generator_order_at_prime_dvd_q {p : Nat} [Fact (Nat.Prime p)]
    (hdvd : p ∣ bls12381FqModulus) :
    ∃ (hG : (bls12381CurveAt p).Nonsingular (bls12381G1GenX : ZMod p) (bls12381G1GenY : ZMod p)),
      bls12381FrModulus •
        (WeierstrassCurve.Affine.Point.some (bls12381G1GenX : ZMod p) (bls12381G1GenY : ZMod p) hG) = 0 := by
  obtain ⟨hp2, hp3⟩ := prime_dvd_fq_ne_two_three hdvd
  have hGeq : ((bls12381G1GenY : ZMod p)) ^ 2 = ((bls12381G1GenX : ZMod p)) ^ 3 + 4 := by
    have hc := congrArg (fun n : Nat => (n : ZMod p)) bls12381G1Gen_onCurve_mod
    rw [natCast_mod_of_dvd hdvd, natCast_mod_of_dvd hdvd] at hc
    push_cast at hc
    linear_combination hc
  have hG : (bls12381CurveAt p).Nonsingular (bls12381G1GenX : ZMod p) (bls12381G1GenY : ZMod p) :=
    bls12381CurveAt_nonsingular_of_eq hp2 hp3 hGeq
  refine ⟨hG, ?_⟩
  set Gp : (bls12381CurveAt p).Point := .some (bls12381G1GenX : ZMod p) (bls12381G1GenY : ZMod p) hG
  have hβ : ((bls12381EndoBetaNat : ZMod p)) ^ 2 + (bls12381EndoBetaNat : ZMod p) + 1 = 0 := by
    have hc := congrArg (fun n : Nat => (n : ZMod p)) bls12381EndoBetaNat_poly_mod
    rw [natCast_mod_of_dvd hdvd] at hc
    push_cast at hc
    linear_combination hc
  have hQ1 := ecMulBitsMod_sound bls12381FqModulus_pos hdvd
    (bls12381G1GenX, bls12381G1GenY) Gp ⟨hG, rfl⟩
    bls12381SeedBits (bls12381G1GenX, bls12381G1GenY) (bls12381CertQ1X, bls12381CertQ1Y)
    1 bls12381CertInvs1 ⟨hG, by rw [one_smul]⟩ ecMulBitsMod_cert1
  rw [bls12381SeedBits_foldl] at hQ1
  have hQ2 := ecMulBitsMod_sound bls12381FqModulus_pos hdvd
    (bls12381CertQ1X, bls12381CertQ1Y) (bls12381Seed • Gp) hQ1
    bls12381SeedBits (bls12381CertQ1X, bls12381CertQ1Y)
    ((bls12381EndoBetaNat * bls12381G1GenX) % bls12381FqModulus,
     bls12381FqModulus - bls12381G1GenY)
    1 bls12381CertInvs2 (by rw [one_smul]; exact hQ1) ecMulBitsMod_cert2
  rw [bls12381SeedBits_foldl, ← mul_smul, ← sq] at hQ2
  obtain ⟨_, hQ2eq⟩ := hQ2
  have hEndoEq : (bls12381Seed ^ 2) • Gp =
      -(bls12381EndoAt p hp2 hp3 (bls12381EndoBetaNat : ZMod p) hβ Gp) := by
    rw [hQ2eq]
    dsimp only [Gp, bls12381EndoAt]
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    simp only [WeierstrassCurve.Affine.negY, bls12381CurveAt, zero_mul, sub_zero]
    constructor
    · rw [natCast_mod_of_dvd hdvd, Nat.cast_mul]
    · have hlt : bls12381G1GenY < bls12381FqModulus := by decide
      have hq0 : (bls12381FqModulus : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
      have hsum : (bls12381FqModulus - bls12381G1GenY) + bls12381G1GenY = bls12381FqModulus :=
        Nat.sub_add_cancel (Nat.le_of_lt hlt)
      have hc := congrArg (fun n : Nat => (n : ZMod p)) hsum
      rw [Nat.cast_add, hq0] at hc
      linear_combination hc
  exact order_r_of_endo_eq_at p hp2 hp3 (bls12381EndoBetaNat : ZMod p) hβ Gp hEndoEq

/-- **Generic Trivial-Bound Elliptic-Curve Primality Criterion (`prime_of_point_order_gt_two_sqrt`):**
If `q ≥ 2`, `r` is prime with `4 * q < (r - 1)^2`, and for every prime divisor `p ∣ q` there
exists a nonzero point `P` on `y^2 = x^3 + 4` over `ZMod p` with `r • P = 0`, then `q` is prime!
(Because the `r - 1` nonzero multiples of `P` map ≤ 2-to-1 into `ZMod p` via their `x`-coordinate,
forcing `r - 1 ≤ 2 * p`, contradicting `p^2 ≤ q` for a composite `q`.) -/
private theorem prime_of_point_order_gt_two_sqrt (q r : Nat) [Fact (Nat.Prime r)]
    (hq2 : 2 ≤ q) (hbound : 4 * q < (r - 1) ^ 2)
    (hstep : ∀ (p : Nat) [Fact (Nat.Prime p)], p ∣ q →
      ∃ (P : (bls12381CurveAt p).Point), P ≠ 0 ∧ r • P = 0) :
    Nat.Prime q := by
  by_contra hnot
  have hne1 : q ≠ 1 := by omega
  have hpos : 0 < q := by omega
  let p := q.minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime hne1
  have : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hdvd : p ∣ q := Nat.minFac_dvd q
  have hpsq : p * p ≤ q := by
    have := Nat.minFac_sq_le_self hpos hnot
    simpa [p, sq] using this
  obtain ⟨Gp, hGp_ne, hord⟩ := hstep p hdvd
  have hr_prime : Nat.Prime r := Fact.out
  have hsmul_mod : ∀ n : Nat, (n % r) • Gp = n • Gp := by
    intro n
    have hdiv : r * (n / r) + n % r = n := Nat.div_add_mod n r
    conv_rhs => rw [← hdiv]
    rw [add_smul, Nat.mul_comm, mul_smul, hord, nsmul_zero, zero_add]
  have hsmul_add : ∀ a b : ZMod r, a.val • Gp + b.val • Gp = (a + b).val • Gp := by
    intro a b
    rw [← add_smul, ZMod.val_add, hsmul_mod]
  have hsmul_mul : ∀ a b : ZMod r, a.val • (b.val • Gp) = (a * b).val • Gp := by
    intro a b
    rw [← mul_smul, ZMod.val_mul, hsmul_mod]
  have hinj : Function.Injective (fun k : ZMod r => k.val • Gp) := by
    intro a b hab
    dsimp only at hab
    by_contra hne
    have hdiff_ne : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hneg : (-b).val • Gp = -(b.val • Gp) := by
      apply eq_neg_of_add_eq_zero_left
      rw [hsmul_add, neg_add_cancel, ZMod.val_zero, zero_nsmul]
    have hzero : (a - b).val • Gp = 0 := by
      rw [sub_eq_add_neg, ← hsmul_add, hab, hneg, add_neg_cancel]
    have h1 : ((a - b)⁻¹ * (a - b)).val • Gp = 0 := by
      rw [← hsmul_mul, hzero, nsmul_zero]
    rw [inv_mul_cancel₀ hdiff_ne] at h1
    have : Fact (1 < r) := ⟨hr_prime.one_lt⟩
    rw [ZMod.val_one, one_nsmul] at h1
    exact hGp_ne h1
  let xCoord : (bls12381CurveAt p).Point → ZMod p
    | .zero => 0
    | .some x _ _ => x
  let S : Finset (ZMod r) := Finset.univ.erase 0
  have hScard : S.card = r - 1 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hfiber : ∀ x : ZMod p, (S.filter fun k => xCoord (k.val • Gp) = x).card ≤ 2 := by
    intro x
    by_contra hgt
    have h3 : 2 < (S.filter fun k => xCoord (k.val • Gp) = x).card := by omega
    obtain ⟨k1, hk1, k2, hk2, k3, hk3, h12, h13, h23⟩ :=
      Finset.two_lt_card.mp h3
    simp only [Finset.mem_filter, Finset.mem_erase, S] at hk1 hk2 hk3
    have hne0 : ∀ k : ZMod r, k ≠ 0 → k.val • Gp ≠ 0 := by
      intro k hk h0
      apply hk
      apply hinj
      simpa using h0
    cases hP1 : k1.val • Gp with
    | zero => exact hne0 k1 hk1.1.1 hP1
    | some x1 y1 ns1 =>
      cases hP2 : k2.val • Gp with
      | zero => exact hne0 k2 hk2.1.1 hP2
      | some x2 y2 ns2 =>
        cases hP3 : k3.val • Gp with
        | zero => exact hne0 k3 hk3.1.1 hP3
        | some x3 y3 ns3 =>
          rw [hP1] at hk1; rw [hP2] at hk2; rw [hP3] at hk3
          have hx1 : x1 = x := hk1.2
          have hx2 : x2 = x := hk2.2
          have hx3 : x3 = x := hk3.2
          have heq1 : y1 ^ 2 = x ^ 3 + 4 := by
            rw [← hx1]; exact (bls12381CurveAt_equation_iff p x1 y1).mp ns1.1
          have heq2 : y2 ^ 2 = x ^ 3 + 4 := by
            rw [← hx2]; exact (bls12381CurveAt_equation_iff p x2 y2).mp ns2.1
          have heq3 : y3 ^ 2 = x ^ 3 + 4 := by
            rw [← hx3]; exact (bls12381CurveAt_equation_iff p x3 y3).mp ns3.1
          have hy12 : y1 = y2 ∨ y1 = -y2 := by
            have h0 : (y1 - y2) * (y1 + y2) = 0 := by linear_combination heq1 - heq2
            rcases mul_eq_zero.mp h0 with h | h
            · exact Or.inl (sub_eq_zero.mp h)
            · exact Or.inr (eq_neg_of_add_eq_zero_left h)
          have hy13 : y1 = y3 ∨ y1 = -y3 := by
            have h0 : (y1 - y3) * (y1 + y3) = 0 := by linear_combination heq1 - heq3
            rcases mul_eq_zero.mp h0 with h | h
            · exact Or.inl (sub_eq_zero.mp h)
            · exact Or.inr (eq_neg_of_add_eq_zero_left h)
          rcases hy12 with rfl | h12neg
          · apply h12; apply hinj; dsimp only
            rw [hP1, hP2, WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨hx1.trans hx2.symm, rfl⟩
          · rcases hy13 with rfl | h13neg
            · apply h13; apply hinj; dsimp only
              rw [hP1, hP3, WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨hx1.trans hx3.symm, rfl⟩
            · apply h23; apply hinj; dsimp only
              rw [hP2, hP3, WeierstrassCurve.Affine.Point.some.injEq]
              exact ⟨hx2.trans hx3.symm, neg_inj.mp (h12neg.symm.trans h13neg)⟩
  have hle2p : r - 1 ≤ 2 * p := by
    have hcard_eq : S.card = ∑ x : ZMod p, (S.filter fun k => xCoord (k.val • Gp) = x).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun k : ZMod r => xCoord (k.val • Gp))
        (s := S) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    have hsum_le : (∑ x : ZMod p, (S.filter fun k => xCoord (k.val • Gp) = x).card) ≤
        ∑ _x : ZMod p, 2 :=
      Finset.sum_le_sum fun x _ => hfiber x
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hsum_le
    rw [hScard] at hcard_eq
    rw [hcard_eq, Nat.mul_comm]
    exact hsum_le
  have hsq_le : (r - 1) ^ 2 ≤ 4 * q := by
    calc (r - 1) ^ 2
        ≤ (2 * p) ^ 2 := Nat.pow_le_pow_left hle2p 2
      _ = 4 * (p * p) := by ring
      _ ≤ 4 * q := Nat.mul_le_mul_left 4 hpsq
  exact absurd hsq_le (Nat.not_le.mpr hbound)

/-- **Self-Contained Endomorphism-ECPP Primality Proof for `bls12381FqModulus`:**
Proves `Nat.Prime bls12381FqModulus` using zero `sorry`, zero `native_decide`, and zero
external axioms (only `[propext, Classical.choice, Quot.sound]`). -/
theorem bls12381FqModulus_prime : Nat.Prime bls12381FqModulus :=
  prime_of_point_order_gt_two_sqrt bls12381FqModulus bls12381FrModulus
    (by decide) four_mul_fq_lt_fr_sub_one_sq fun p _ hdvd =>
      let ⟨hG, hord⟩ := bls12381Generator_order_at_prime_dvd_q hdvd
      ⟨.some _ _ hG, WeierstrassCurve.Affine.Point.some_ne_zero _, hord⟩

instance : Fact (Nat.Prime bls12381FqModulus) := ⟨bls12381FqModulus_prime⟩

/-- The BLS12-381 base prime field $\mathbb{F}_q$. -/
abbrev BLS12381Fq : Type := ZMod bls12381FqModulus

/-! ## 3. 5×80-Bit Non-Native `BLS12381::Fq` Limb Arithmetic (`native_field.rs`) -/

section NonNativeFq

set_option exponentiation.threshold 1024

/-- Bit width $W = 80$ of each ordinary limb (`native_field.rs:15`). -/
def LIMB_BITS : Nat := 80

/-- Number of 80-bit limbs $L = 5$ representing a 381-bit `BLS12381::Fq` element
(`Bls12381::FQ_GADGET_LIMBS = 5` in `curve.rs:425`). -/
def NUM_LIMBS : Nat := 5

/-- Bit width $381 - 4 \times 80 = 61$ of the most-significant limb (`native_field.rs:51`). -/
def TOP_LIMB_BITS : Nat := 61

/-- Bit width $381 + 3 = 384$ of the biased quotient in `FqGadget::relation` (`native_field.rs:56`). -/
def QUOTIENT_BITS : Nat := 384

/-- Bit width $384 - 4 \times 80 = 64$ of the top quotient limb (`native_field.rs:66`). -/
def QUOTIENT_TOP_BITS : Nat := 64

/-- Bit width of the `"Fq range"` lookup table (`native_field.rs:17`). -/
def RANGE_BITS : Nat := 20

/-- Bit width of biased carries in `FqGadget::relation` (`native_field.rs:19`). -/
def CARRY_BITS : Nat := 89

/-- Signed carry bias $2^{88}$ (`native_field.rs:20`). -/
def CARRY_BIAS : ℤ := 2 ^ 88

/-- Limb radix $B = 2^{80}$. -/
def LIMB_RADIX : Nat := 2 ^ 80

/-- Paired-limb block radix $B^2 = 2^{160}$. -/
def BLOCK_RADIX : Nat := 2 ^ 160

/-- Five 80-bit limbs representing a non-native `BLS12381::Fq` element (`FqVar<Bls12381>`). -/
structure Bls12381FqLimbs where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  l4 : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Integer evaluation of a 5-limb `Bls12381FqLimbs` value in base $2^{80}$. -/
def evalLimbs (v : Bls12381FqLimbs) : Nat :=
  v.l0 + v.l1 * 2 ^ 80 + v.l2 * 2 ^ 160 + v.l3 * 2 ^ 240 + v.l4 * 2 ^ 320

/-- Signed integer evaluation of a 5-limb `Bls12381FqLimbs` value in base $2^{80}$. -/
def evalLimbsInt (v : Bls12381FqLimbs) : ℤ :=
  (evalLimbs v : ℤ)

/-- Limb-wise bit-width bounds enforced by `FqGadget::<Bls12381>::bound`
(`l0..l3 < 2^80`, `l4 < 2^61`). -/
def Bls12381FqLimbs.Bounded (v : Bls12381FqLimbs) : Prop :=
  v.l0 < 2 ^ 80 ∧ v.l1 < 2 ^ 80 ∧ v.l2 < 2 ^ 80 ∧ v.l3 < 2 ^ 80 ∧ v.l4 < 2 ^ 61

/-- All five limbs strictly below $2^{80}$. -/
def Bls12381FqLimbs.LimbsLtRadix (v : Bls12381FqLimbs) : Prop :=
  v.l0 < 2 ^ 80 ∧ v.l1 < 2 ^ 80 ∧ v.l2 < 2 ^ 80 ∧ v.l3 < 2 ^ 80 ∧ v.l4 < 2 ^ 80

theorem Bls12381FqLimbs.Bounded.limbsLtRadix {v : Bls12381FqLimbs} (hb : v.Bounded) :
    v.LimbsLtRadix :=
  ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, by have := hb.2.2.2.2; omega⟩

/-- Canonicality predicate: evaluated 5-limb integer strictly below `bls12381FqModulus`. -/
def Bls12381FqLimbs.Canonical (v : Bls12381FqLimbs) : Prop :=
  evalLimbs v < bls12381FqModulus

/-- Base-$2^{80}$ 5-limb decomposition of `bls12381FqModulus`. -/
def bls12381FqModulusLimbs : Bls12381FqLimbs :=
  { l0 := bls12381FqModulus % (2 ^ 80)
    l1 := (bls12381FqModulus / (2 ^ 80)) % (2 ^ 80)
    l2 := (bls12381FqModulus / (2 ^ 160)) % (2 ^ 80)
    l3 := (bls12381FqModulus / (2 ^ 240)) % (2 ^ 80)
    l4 := bls12381FqModulus / (2 ^ 320) }

/-- Base-$2^{80}$ 5-limb decomposition of `bls12381FqModulus - 1` (`native_field.rs:270`). -/
def bls12381FqModulusMinusOneLimbs : Bls12381FqLimbs :=
  { l0 := (bls12381FqModulus - 1) % (2 ^ 80)
    l1 := ((bls12381FqModulus - 1) / (2 ^ 80)) % (2 ^ 80)
    l2 := ((bls12381FqModulus - 1) / (2 ^ 160)) % (2 ^ 80)
    l3 := ((bls12381FqModulus - 1) / (2 ^ 240)) % (2 ^ 80)
    l4 := (bls12381FqModulus - 1) / (2 ^ 320) }

theorem bls12381_evalLimbs_fqModulusLimbs :
    evalLimbs bls12381FqModulusLimbs = bls12381FqModulus := by decide

theorem bls12381_evalLimbs_fqModulusMinusOneLimbs :
    evalLimbs bls12381FqModulusMinusOneLimbs = bls12381FqModulus - 1 := by decide

/-- Any `Bounded` 5-limb value has total value strictly below $2^{381}$. -/
theorem bls12381_evalLimbs_lt_two_pow_381 {v : Bls12381FqLimbs} (hb : v.Bounded) :
    evalLimbs v < 2 ^ 381 := by
  rcases hb with ⟨h0, h1, h2, h3, h4⟩
  unfold evalLimbs
  have h0' : v.l0 ≤ 2 ^ 80 - 1 := Nat.le_sub_one_of_lt h0
  have h1' : v.l1 ≤ 2 ^ 80 - 1 := Nat.le_sub_one_of_lt h1
  have h2' : v.l2 ≤ 2 ^ 80 - 1 := Nat.le_sub_one_of_lt h2
  have h3' : v.l3 ≤ 2 ^ 80 - 1 := Nat.le_sub_one_of_lt h3
  have h4' : v.l4 ≤ 2 ^ 61 - 1 := Nat.le_sub_one_of_lt h4
  calc v.l0 + v.l1 * 2 ^ 80 + v.l2 * 2 ^ 160 + v.l3 * 2 ^ 240 + v.l4 * 2 ^ 320
      ≤ (2 ^ 80 - 1) + (2 ^ 80 - 1) * 2 ^ 80 + (2 ^ 80 - 1) * 2 ^ 160 +
          (2 ^ 80 - 1) * 2 ^ 240 + (2 ^ 61 - 1) * 2 ^ 320 := by
        gcongr
    _ < 2 ^ 381 := by decide

/-- **80-Bit Limb Range Check Soundness (`bls12381_range20_limb80_bound`)**. -/
theorem bls12381_range20_limb80_bound (s0 s1 s2 s3 : Nat)
    (h0 : s0 < 2 ^ 20) (h1 : s1 < 2 ^ 20) (h2 : s2 < 2 ^ 20) (h3 : s3 < 2 ^ 20) :
    s0 + s1 * 2 ^ 20 + s2 * 2 ^ 40 + s3 * 2 ^ 60 < 2 ^ 80 := by
  omega

/-- **61-Bit Top-Limb Range Check Soundness (`bls12381_range20_topLimb61_bound`)**:
Four 20-bit sub-limbs with `s3 * 2^19 < 2^20` (so `s3 < 2^1`) pack into `< 2^61`
(`FqGadget::<Bls12381>::range_n::<4>` with `bits = 61`). -/
theorem bls12381_range20_topLimb61_bound (s0 s1 s2 s3 : Nat)
    (h0 : s0 < 2 ^ 20) (h1 : s1 < 2 ^ 20) (h2 : s2 < 2 ^ 20) (h3Scaled : s3 * 2 ^ 19 < 2 ^ 20) :
    s0 + s1 * 2 ^ 20 + s2 * 2 ^ 40 + s3 * 2 ^ 60 < 2 ^ 61 := by
  omega

/-- **64-Bit Quotient Top-Limb Range Check Soundness (`bls12381_range20_quotientTop64_bound`)**:
Four 20-bit sub-limbs with `s3 * 2^16 < 2^20` (so `s3 < 2^4`) pack into `< 2^64`. -/
theorem bls12381_range20_quotientTop64_bound (s0 s1 s2 s3 : Nat)
    (h0 : s0 < 2 ^ 20) (h1 : s1 < 2 ^ 20) (h2 : s2 < 2 ^ 20) (h3Scaled : s3 * 2 ^ 16 < 2 ^ 20) :
    s0 + s1 * 2 ^ 20 + s2 * 2 ^ 40 + s3 * 2 ^ 60 < 2 ^ 64 := by
  omega

/-- **89-Bit Biased Carry Range Check Soundness (`bls12381_range20_carry89_bound`)**. -/
theorem bls12381_range20_carry89_bound (c0 c1 c2 c3 c4 : Nat)
    (h0 : c0 < 2 ^ 20) (h1 : c1 < 2 ^ 20) (h2 : c2 < 2 ^ 20)
    (h3 : c3 < 2 ^ 20) (h4 : c4 < 2 ^ 9) :
    let c : ℤ := ((c0 + c1 * 2 ^ 20 + c2 * 2 ^ 40 + c3 * 2 ^ 60 + c4 * 2 ^ 80 : Nat) : ℤ);
    -CARRY_BIAS ≤ c - CARRY_BIAS ∧ c - CARRY_BIAS < CARRY_BIAS := by
  dsimp only; unfold CARRY_BIAS; omega

/-- Upper bound $A = 4 L B^2 + 3 B + 4 = 20 \cdot 2^{160} + 3 \cdot 2^{80} + 4$ on the
magnitude of any single degree-$k$ limb equation coefficient for $L = 5$
(`native_field.rs:668`). -/
def bls12381CoefficientBound : ℤ :=
  20 * (2 ^ 80 : ℤ) ^ 2 + 3 * (2 ^ 80 : ℤ) + 4

/-- Upper bound $(B + 1) A + (B^2 + 1) 2^{88}$ on the magnitude of any paired limb equation
for $L = 5$ (`native_field.rs:670-671`). -/
def bls12381PairedEquationBound : ℤ :=
  (2 ^ 80 + 1) * bls12381CoefficientBound + ((2 ^ 80 : ℤ) ^ 2 + 1) * CARRY_BIAS

/-- The maximum paired equation magnitude for $L = 5$ is strictly below $2^{250}$ and strictly
below half of `bls12381FrModulus` (`native_field.rs:673`). -/
theorem bls12381_pairedEquationBound_lt_fr_half :
    bls12381PairedEquationBound < 2 ^ 250 ∧
      2 * bls12381PairedEquationBound < (bls12381FrModulus : ℤ) := by
  decide

/-- Fundamental integer no-wrap lemma in `BLS12381Fr`: if $|e| < r$ and $e \equiv 0 \pmod r$,
then $e = 0$ in $\mathbb{Z}$. -/
theorem int_eq_zero_of_mod_bls12381Fr_eq_zero (e : ℤ)
    (hlo : -(bls12381FrModulus : ℤ) < e) (hhi : e < (bls12381FrModulus : ℤ))
    (hmod : e % (bls12381FrModulus : ℤ) = 0) :
    e = 0 :=
  int_eq_zero_of_dvd_of_lt (_root_.Int.dvd_of_emod_eq_zero hmod) hlo hhi

/-- **Paired-Limb No-Overflow Theorem (`bls12381_paired_limb_no_overflow`)**:
In `FqGadget::<Bls12381>::relation` (`native_field.rs:429-444`), each paired `BLS12381Fr`
constraint has integer magnitude $< 2^{250} < r / 2$, so vanishing modulo `bls12381FrModulus`
implies exact vanishing in $\mathbb{Z}$. -/
theorem bls12381_paired_limb_no_overflow
    (eqEven eqOdd carryIn carryOut : ℤ)
    (hEvenLo : -bls12381CoefficientBound ≤ eqEven) (hEvenHi : eqEven ≤ bls12381CoefficientBound)
    (hOddLo : -bls12381CoefficientBound ≤ eqOdd) (hOddHi : eqOdd ≤ bls12381CoefficientBound)
    (hInLo : -CARRY_BIAS ≤ carryIn) (hInHi : carryIn ≤ CARRY_BIAS)
    (hOutLo : -CARRY_BIAS ≤ carryOut) (hOutHi : carryOut ≤ CARRY_BIAS)
    (hModFr : (eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut) %
      (bls12381FrModulus : ℤ) = 0) :
    eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut = 0 := by
  have hlt := bls12381_pairedEquationBound_lt_fr_half.2
  have hboundLo : -bls12381PairedEquationBound ≤
      eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut := by
    unfold bls12381PairedEquationBound
    linarith
  have hboundHi : eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut ≤
      bls12381PairedEquationBound := by
    unfold bls12381PairedEquationBound
    linarith
  have hpos : 0 < bls12381PairedEquationBound := by decide
  exact int_eq_zero_of_mod_bls12381Fr_eq_zero _ (by linarith) (by linarith) hModFr

/-- **Five-Pair 10-Degree Convolution Telescoping Soundness (`bls12381_fq_relation_five_pairs_sound`)**:
Exact formalization of `for j in 0..5` in `FqGadget::<Bls12381>::relation`
(`native_field.rs:429-444`) with 10 convolution degrees `t0..t9` and 4 biased 89-bit carries
`carry0..carry3`. Telescoping $\sum_{j=0}^{4} 2^{160 j} \cdot \text{Pair}_j$ proves
`lhs = qVal * bls12381FqModulus` in $\mathbb{Z}$ and `lhs % bls12381FqModulus = 0`. -/
theorem bls12381_fq_relation_five_pairs_sound
    (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 carry0 carry1 carry2 carry3 lhs qVal : ℤ)
    (ht0Lo : -bls12381CoefficientBound ≤ t0) (ht0Hi : t0 ≤ bls12381CoefficientBound)
    (ht1Lo : -bls12381CoefficientBound ≤ t1) (ht1Hi : t1 ≤ bls12381CoefficientBound)
    (ht2Lo : -bls12381CoefficientBound ≤ t2) (ht2Hi : t2 ≤ bls12381CoefficientBound)
    (ht3Lo : -bls12381CoefficientBound ≤ t3) (ht3Hi : t3 ≤ bls12381CoefficientBound)
    (ht4Lo : -bls12381CoefficientBound ≤ t4) (ht4Hi : t4 ≤ bls12381CoefficientBound)
    (ht5Lo : -bls12381CoefficientBound ≤ t5) (ht5Hi : t5 ≤ bls12381CoefficientBound)
    (ht6Lo : -bls12381CoefficientBound ≤ t6) (ht6Hi : t6 ≤ bls12381CoefficientBound)
    (ht7Lo : -bls12381CoefficientBound ≤ t7) (ht7Hi : t7 ≤ bls12381CoefficientBound)
    (ht8Lo : -bls12381CoefficientBound ≤ t8) (ht8Hi : t8 ≤ bls12381CoefficientBound)
    (ht9Lo : -bls12381CoefficientBound ≤ t9) (ht9Hi : t9 ≤ bls12381CoefficientBound)
    (hc0Lo : -CARRY_BIAS ≤ carry0) (hc0Hi : carry0 ≤ CARRY_BIAS)
    (hc1Lo : -CARRY_BIAS ≤ carry1) (hc1Hi : carry1 ≤ CARRY_BIAS)
    (hc2Lo : -CARRY_BIAS ≤ carry2) (hc2Hi : carry2 ≤ CARRY_BIAS)
    (hc3Lo : -CARRY_BIAS ≤ carry3) (hc3Hi : carry3 ≤ CARRY_BIAS)
    (hPair0 : (t0 + 2 ^ 80 * t1 + 0 - 2 ^ 160 * carry0) % (bls12381FrModulus : ℤ) = 0)
    (hPair1 : (t2 + 2 ^ 80 * t3 + carry0 - 2 ^ 160 * carry1) % (bls12381FrModulus : ℤ) = 0)
    (hPair2 : (t4 + 2 ^ 80 * t5 + carry1 - 2 ^ 160 * carry2) % (bls12381FrModulus : ℤ) = 0)
    (hPair3 : (t6 + 2 ^ 80 * t7 + carry2 - 2 ^ 160 * carry3) % (bls12381FrModulus : ℤ) = 0)
    (hPair4 : (t8 + 2 ^ 80 * t9 + carry3 - 2 ^ 160 * 0) % (bls12381FrModulus : ℤ) = 0)
    (hDecomp :
      t0 + 2 ^ 80 * t1 + 2 ^ 160 * t2 + 2 ^ 240 * t3 + 2 ^ 320 * t4 +
        2 ^ 400 * t5 + 2 ^ 480 * t6 + 2 ^ 560 * t7 + 2 ^ 640 * t8 + 2 ^ 720 * t9 =
          lhs - qVal * (bls12381FqModulus : ℤ)) :
    lhs = qVal * (bls12381FqModulus : ℤ) ∧ lhs % (bls12381FqModulus : ℤ) = 0 := by
  have hP0 := bls12381_paired_limb_no_overflow t0 t1 0 carry0
    ht0Lo ht0Hi ht1Lo ht1Hi (by decide) (by decide) hc0Lo hc0Hi hPair0
  have hP1 := bls12381_paired_limb_no_overflow t2 t3 carry0 carry1
    ht2Lo ht2Hi ht3Lo ht3Hi hc0Lo hc0Hi hc1Lo hc1Hi hPair1
  have hP2 := bls12381_paired_limb_no_overflow t4 t5 carry1 carry2
    ht4Lo ht4Hi ht5Lo ht5Hi hc1Lo hc1Hi hc2Lo hc2Hi hPair2
  have hP3 := bls12381_paired_limb_no_overflow t6 t7 carry2 carry3
    ht6Lo ht6Hi ht7Lo ht7Hi hc2Lo hc2Hi hc3Lo hc3Hi hPair3
  have hP4 := bls12381_paired_limb_no_overflow t8 t9 carry3 0
    ht8Lo ht8Hi ht9Lo ht9Hi hc3Lo hc3Hi (by decide) (by decide) hPair4
  have hLhs : lhs = qVal * (bls12381FqModulus : ℤ) := by
    linear_combination hP0 + (2 ^ 160 : ℤ) * hP1 + (2 ^ 320 : ℤ) * hP2 +
      (2 ^ 480 : ℤ) * hP3 + (2 ^ 640 : ℤ) * hP4 - hDecomp
  refine ⟨hLhs, ?_⟩
  rw [hLhs, _root_.Int.mul_comm, _root_.Int.mul_emod_right]

/-- Modular relation predicate over `bls12381FqModulus`. -/
def Bls12381FqRelationHolds (expr : ℤ) : Prop :=
  expr % (bls12381FqModulus : ℤ) = 0

theorem bls12381_fq_add_sound (x y z : Bls12381FqLimbs)
    (hRel : Bls12381FqRelationHolds (evalLimbsInt x + evalLimbsInt y - evalLimbsInt z))
    (hCanon : z.Canonical) :
    (evalLimbs x + evalLimbs y) % bls12381FqModulus = evalLimbs z := by
  unfold Bls12381FqRelationHolds evalLimbsInt Bls12381FqLimbs.Canonical at *
  have hmod : (evalLimbs x + evalLimbs y : ℤ) % (bls12381FqModulus : ℤ) =
      (evalLimbs z : ℤ) % (bls12381FqModulus : ℤ) :=
    _root_.Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hRel
  have hz : (evalLimbs z : ℤ) % (bls12381FqModulus : ℤ) = (evalLimbs z : ℤ) :=
    _root_.Int.emod_eq_of_lt (_root_.Int.natCast_nonneg _) (_root_.Int.ofNat_lt.mpr hCanon)
  rw [hz] at hmod
  exact_mod_cast hmod

theorem bls12381_fq_sub_sound (x y z : Bls12381FqLimbs)
    (hRel : Bls12381FqRelationHolds (evalLimbsInt x - evalLimbsInt y - evalLimbsInt z))
    (hCanon : z.Canonical) :
    (evalLimbsInt x - evalLimbsInt y) % (bls12381FqModulus : ℤ) = evalLimbsInt z := by
  unfold Bls12381FqRelationHolds evalLimbsInt Bls12381FqLimbs.Canonical at *
  have hmod : ((evalLimbs x : ℤ) - (evalLimbs y : ℤ)) % (bls12381FqModulus : ℤ) =
      (evalLimbs z : ℤ) % (bls12381FqModulus : ℤ) :=
    _root_.Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hRel
  have hz : (evalLimbs z : ℤ) % (bls12381FqModulus : ℤ) = (evalLimbs z : ℤ) :=
    _root_.Int.emod_eq_of_lt (_root_.Int.natCast_nonneg _) (_root_.Int.ofNat_lt.mpr hCanon)
  exact hmod.trans hz

theorem bls12381_fq_mul_sound (x y z : Bls12381FqLimbs)
    (hRel : Bls12381FqRelationHolds (evalLimbsInt x * evalLimbsInt y - evalLimbsInt z)) :
    (evalLimbs x * evalLimbs y) % bls12381FqModulus = evalLimbs z % bls12381FqModulus := by
  unfold Bls12381FqRelationHolds evalLimbsInt at hRel
  have hmod : ((evalLimbs x : ℤ) * (evalLimbs y : ℤ)) % (bls12381FqModulus : ℤ) =
      (evalLimbs z : ℤ) % (bls12381FqModulus : ℤ) :=
    _root_.Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hRel
  exact_mod_cast hmod

theorem bls12381_fq_inv_or_zero_sound (lhs rhs inv : Bls12381FqLimbs) (flag : ℤ)
    (_hBool : flag = 0 ∨ flag = 1)
    (hRel1 : Bls12381FqRelationHolds ((evalLimbsInt lhs - evalLimbsInt rhs) * evalLimbsInt inv + flag - 1))
    (hRel2 : Bls12381FqRelationHolds ((evalLimbsInt lhs - evalLimbsInt rhs) * flag))
    (hRel3 : Bls12381FqRelationHolds (evalLimbsInt inv * flag)) :
    (flag = 1 →
      (evalLimbsInt lhs - evalLimbsInt rhs) % (bls12381FqModulus : ℤ) = 0 ∧
      evalLimbsInt inv % (bls12381FqModulus : ℤ) = 0) ∧
    (flag = 0 →
      ((evalLimbsInt lhs - evalLimbsInt rhs) * evalLimbsInt inv - 1) % (bls12381FqModulus : ℤ) = 0 ∧
      (evalLimbsInt lhs - evalLimbsInt rhs) % (bls12381FqModulus : ℤ) ≠ 0) := by
  unfold Bls12381FqRelationHolds at *
  refine ⟨?_, ?_⟩
  · intro hFlag; subst hFlag
    simp only [_root_.Int.mul_one] at hRel2 hRel3
    exact ⟨hRel2, hRel3⟩
  · intro hFlag; subst hFlag
    simp only [_root_.Int.add_zero] at hRel1
    refine ⟨hRel1, ?_⟩
    intro hDiffZero
    have hProdZero :
        ((evalLimbsInt lhs - evalLimbsInt rhs) * evalLimbsInt inv) % (bls12381FqModulus : ℤ) = 0 := by
      rw [_root_.Int.mul_emod, hDiffZero, _root_.Int.zero_mul, _root_.Int.zero_emod]
    have hEq1 : ((evalLimbsInt lhs - evalLimbsInt rhs) * evalLimbsInt inv) % (bls12381FqModulus : ℤ) =
        (1 : ℤ) % (bls12381FqModulus : ℤ) :=
      _root_.Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hRel1
    have h1 : (1 : ℤ) % (bls12381FqModulus : ℤ) = 1 :=
      _root_.Int.emod_eq_of_lt (by decide) (by decide)
    rw [hProdZero, h1] at hEq1
    exact zero_ne_one hEq1

theorem bls12381_fq_equal_sound (x y : Bls12381FqLimbs)
    (hRel : Bls12381FqRelationHolds (evalLimbsInt x - evalLimbsInt y)) :
    evalLimbs x % bls12381FqModulus = evalLimbs y % bls12381FqModulus ∧
    (x.Canonical → y.Canonical → evalLimbs x = evalLimbs y) := by
  unfold Bls12381FqRelationHolds evalLimbsInt Bls12381FqLimbs.Canonical at *
  have hmodInt : (evalLimbs x : ℤ) % (bls12381FqModulus : ℤ) =
      (evalLimbs y : ℤ) % (bls12381FqModulus : ℤ) :=
    _root_.Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr hRel
  have hmod : evalLimbs x % bls12381FqModulus = evalLimbs y % bls12381FqModulus := by
    exact_mod_cast hmodInt
  refine ⟨hmod, fun hx hy => ?_⟩
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod

/-- Single canonical-subtraction limb no-wrap lemma in `BLS12381Fr`. -/
theorem bls12381_canonical_limb_no_wrap
    (p_i v_i d_i b_in b_out : Nat)
    (hp : p_i < 2 ^ 80) (hv : v_i < 2 ^ 80) (hd : d_i < 2 ^ 80)
    (hbin : b_in = 0 ∨ b_in = 1) (hbout : b_out = 0 ∨ b_out = 1)
    (hFr : ((p_i : BLS12381Fr) - (v_i : BLS12381Fr) - (b_in : BLS12381Fr) +
      (2 ^ 80 : BLS12381Fr) * (b_out : BLS12381Fr) - (d_i : BLS12381Fr)) = 0) :
    (p_i : ℤ) - v_i - b_in + 2 ^ 80 * b_out - d_i = 0 := by
  set e : ℤ := (p_i : ℤ) - (v_i : ℤ) - (b_in : ℤ) + (2 : ℤ) ^ 80 * (b_out : ℤ) - (d_i : ℤ)
  have heFr : (e : BLS12381Fr) = 0 := by
    dsimp only [e]
    simp only [_root_.Int.cast_sub, _root_.Int.cast_add, _root_.Int.cast_mul, _root_.Int.cast_pow,
      _root_.Int.cast_natCast, _root_.Int.cast_ofNat]
    exact hFr
  have hdvd : (bls12381FrModulus : ℤ) ∣ e :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd e bls12381FrModulus).mp heFr
  have hmod : e % (bls12381FrModulus : ℤ) = 0 := _root_.Int.emod_eq_zero_of_dvd hdvd
  have hfr_gt : (2 ^ 82 : ℤ) < (bls12381FrModulus : ℤ) := by decide
  apply int_eq_zero_of_mod_bls12381Fr_eq_zero e _ _ hmod
  · rcases hbin with rfl | rfl <;> rcases hbout with rfl | rfl <;> omega
  · rcases hbin with rfl | rfl <;> rcases hbout with rfl | rfl <;> omega

/-- **5-Limb Canonical Subtraction Soundness (`bls12381_fq_canonical_lt_q_sound`)**:
Exact formalization of `FqGadget::<Bls12381>::canonical` (`native_field.rs:268-331`):
5 limb equations in `BLS12381Fr` with boolean borrows `b0..b4` and `b4 = 0` enforce
`evalLimbs v + evalLimbs d = bls12381FqModulus - 1`, hence `v.Canonical` (`evalLimbs v < q`). -/
theorem bls12381_fq_canonical_lt_q_sound
    (v d : Bls12381FqLimbs) (b0 b1 b2 b3 b4 : Nat)
    (hv : v.LimbsLtRadix) (hd : d.LimbsLtRadix)
    (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1)
    (hb2 : b2 = 0 ∨ b2 = 1) (hb3 : b3 = 0 ∨ b3 = 1) (hb4 : b4 = 0 ∨ b4 = 1)
    (hEq0 : ((bls12381FqModulusMinusOneLimbs.l0 : BLS12381Fr) - v.l0 - 0 + (2 ^ 80 : BLS12381Fr) * b0 - d.l0) = 0)
    (hEq1 : ((bls12381FqModulusMinusOneLimbs.l1 : BLS12381Fr) - v.l1 - b0 + (2 ^ 80 : BLS12381Fr) * b1 - d.l1) = 0)
    (hEq2 : ((bls12381FqModulusMinusOneLimbs.l2 : BLS12381Fr) - v.l2 - b1 + (2 ^ 80 : BLS12381Fr) * b2 - d.l2) = 0)
    (hEq3 : ((bls12381FqModulusMinusOneLimbs.l3 : BLS12381Fr) - v.l3 - b2 + (2 ^ 80 : BLS12381Fr) * b3 - d.l3) = 0)
    (hEq4 : ((bls12381FqModulusMinusOneLimbs.l4 : BLS12381Fr) - v.l4 - b3 + (2 ^ 80 : BLS12381Fr) * b4 - d.l4) = 0)
    (hFinalBorrow : b4 = 0) :
    v.Canonical := by
  have hpLimbs : bls12381FqModulusMinusOneLimbs.LimbsLtRadix :=
    ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hEq0' : ((bls12381FqModulusMinusOneLimbs.l0 : BLS12381Fr) - (v.l0 : BLS12381Fr) -
      ((0 : Nat) : BLS12381Fr) + (2 ^ 80 : BLS12381Fr) * (b0 : BLS12381Fr) - (d.l0 : BLS12381Fr)) = 0 := by
    simpa only [Nat.cast_zero] using hEq0
  have hZ0 := bls12381_canonical_limb_no_wrap bls12381FqModulusMinusOneLimbs.l0 v.l0 d.l0 0 b0
    hpLimbs.1 hv.1 hd.1 (Or.inl rfl) hb0 hEq0'
  have hZ1 := bls12381_canonical_limb_no_wrap bls12381FqModulusMinusOneLimbs.l1 v.l1 d.l1 b0 b1
    hpLimbs.2.1 hv.2.1 hd.2.1 hb0 hb1 hEq1
  have hZ2 := bls12381_canonical_limb_no_wrap bls12381FqModulusMinusOneLimbs.l2 v.l2 d.l2 b1 b2
    hpLimbs.2.2.1 hv.2.2.1 hd.2.2.1 hb1 hb2 hEq2
  have hZ3 := bls12381_canonical_limb_no_wrap bls12381FqModulusMinusOneLimbs.l3 v.l3 d.l3 b2 b3
    hpLimbs.2.2.2.1 hv.2.2.2.1 hd.2.2.2.1 hb2 hb3 hEq3
  have hZ4 := bls12381_canonical_limb_no_wrap bls12381FqModulusMinusOneLimbs.l4 v.l4 d.l4 b3 b4
    hpLimbs.2.2.2.2 hv.2.2.2.2 hd.2.2.2.2 hb3 hb4 hEq4
  have hP := bls12381_evalLimbs_fqModulusMinusOneLimbs
  have hSumInt : (evalLimbs v : ℤ) + (evalLimbs d : ℤ) = (bls12381FqModulus - 1 : Nat) := by
    rw [← hP]
    unfold evalLimbs
    push_cast
    have hb4z : (b4 : ℤ) = 0 := by exact_mod_cast hFinalBorrow
    linear_combination -hZ0 - (2 ^ 80 : ℤ) * hZ1 - (2 ^ 160 : ℤ) * hZ2 -
      (2 ^ 240 : ℤ) * hZ3 - (2 ^ 320 : ℤ) * hZ4 + (2 ^ 400 : ℤ) * hb4z
  have hSumNat : evalLimbs v + evalLimbs d = bls12381FqModulus - 1 := by
    exact_mod_cast hSumInt
  have hqPos := bls12381FqModulus_pos
  unfold Bls12381FqLimbs.Canonical
  omega

end NonNativeFq

/-! ## 4. Goldilocks-in-`BLS12381Fr` Foreign-Field Compiler & FRI Verifier Composition -/

/-- **Direct Gate Soundness over `BLS12381Fr` (`bls12381_direct_gate_sound`)**:
If $E(a,b,c) \in (-P, P)$ in $\mathbb{Z}$ and $E(a,b,c) \equiv 0 \pmod{r_{\text{BLS}}}$,
then $E(a,b,c) = 0$ in $\mathbb{Z}$ and $E(a,b,c) \equiv 0 \pmod{P}$. -/
theorem bls12381_direct_gate_sound (qm qa qb qc k a b c : ℤ)
    (hlow : -(_root_.Int.ofNat goldilocksP) < gateIntExpr qm qa qb qc k a b c)
    (hhigh : gateIntExpr qm qa qb qc k a b c < _root_.Int.ofNat goldilocksP)
    (hmodR : gateIntExpr qm qa qb qc k a b c ≡ 0 [ZMOD _root_.Int.ofNat bls12381FrModulus]) :
    gateIntExpr qm qa qb qc k a b c = 0 ∧
      gateIntExpr qm qa qb qc k a b c ≡ 0 [ZMOD _root_.Int.ofNat goldilocksP] := by
  have hPR : _root_.Int.ofNat goldilocksP < _root_.Int.ofNat bls12381FrModulus :=
    _root_.Int.ofNat_lt.mpr goldilocksP_lt_bls12381FrModulus
  have hdvd : _root_.Int.ofNat bls12381FrModulus ∣ gateIntExpr qm qa qb qc k a b c :=
    _root_.Int.modEq_zero_iff_dvd.mp hmodR
  have heq0 : gateIntExpr qm qa qb qc k a b c = 0 :=
    int_eq_zero_of_dvd_of_lt hdvd (by omega) (by omega)
  refine ⟨heq0, ?_⟩
  rw [heq0]

/-- **Quotient Gate Soundness over `BLS12381Fr` (`bls12381_quotient_gate_sound`)**:
If $0 \le E(a,b,c) + \text{offset} < r_{\text{BLS}}$, $q' < 2^{140}$,
$\text{offset} \equiv 0 \pmod{P}$, and
$E(a,b,c) + \text{offset} - P \cdot q' \equiv 0 \pmod{r_{\text{BLS}}}$,
then $E(a,b,c) + \text{offset} = P \cdot q'$ in $\mathbb{Z}$ and $E(a,b,c) \equiv 0 \pmod{P}$. -/
theorem bls12381_quotient_gate_sound (qm qa qb qc k a b c : ℤ) (offset q' : Nat)
    (hnonneg : 0 ≤ gateIntExpr qm qa qb qc k a b c + _root_.Int.ofNat offset)
    (hupper : gateIntExpr qm qa qb qc k a b c + _root_.Int.ofNat offset < _root_.Int.ofNat bls12381FrModulus)
    (hq : q' < 2 ^ 140)
    (hoffset : offset % goldilocksP = 0)
    (hmodR : gateIntExpr qm qa qb qc k a b c + _root_.Int.ofNat offset -
      _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q' ≡ 0 [ZMOD _root_.Int.ofNat bls12381FrModulus]) :
    gateIntExpr qm qa qb qc k a b c + _root_.Int.ofNat offset =
      _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q' ∧
    gateIntExpr qm qa qb qc k a b c ≡ 0 [ZMOD _root_.Int.ofNat goldilocksP] := by
  have hPq_lt : _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q' < _root_.Int.ofNat bls12381FrModulus := by
    have h1 : goldilocksP * q' < goldilocksP * 2 ^ 140 :=
      Nat.mul_lt_mul_of_pos_left hq (by decide)
    have h2 : goldilocksP * 2 ^ 140 < bls12381FrModulus := by decide
    simp only [_root_.Int.ofNat_eq_natCast]
    exact_mod_cast Nat.lt_trans h1 h2
  have hPq_nonneg : 0 ≤ _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q' := by
    simp only [_root_.Int.ofNat_eq_natCast]
    exact _root_.Int.mul_nonneg (_root_.Int.natCast_nonneg _) (_root_.Int.natCast_nonneg _)
  have hdvd : _root_.Int.ofNat bls12381FrModulus ∣
      (gateIntExpr qm qa qb qc k a b c + _root_.Int.ofNat offset -
        _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q') :=
    _root_.Int.modEq_zero_iff_dvd.mp hmodR
  have hdiff0 : gateIntExpr qm qa qb qc k a b c + _root_.Int.ofNat offset -
      _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q' = 0 :=
    int_eq_zero_of_dvd_of_lt hdvd (by omega) (by omega)
  have heq : gateIntExpr qm qa qb qc k a b c + _root_.Int.ofNat offset =
      _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q' := by omega
  refine ⟨heq, ?_⟩
  rw [_root_.Int.modEq_zero_iff_dvd]
  have hdiv_off : (goldilocksP : ℤ) ∣ _root_.Int.ofNat offset :=
    _root_.Int.ofNat_dvd.mpr (Nat.dvd_of_mod_eq_zero hoffset)
  rcases hdiv_off with ⟨m, hm⟩
  refine ⟨_root_.Int.ofNat q' - m, ?_⟩
  simp only [_root_.Int.ofNat_eq_natCast] at heq hm ⊢
  rw [mul_sub, ← hm]
  omega

theorem bls12381_universalGateExpr_bounds (qm qa qb qc k : GoldilocksF) {a b c : Nat}
    (ha : a < goldilocksP) (hb : b < goldilocksP) (hc : c < goldilocksP) :
    let E := gateIntExpr
      (signedCoeff (ZMod.val qm))
      (signedCoeff (ZMod.val qa))
      (signedCoeff (ZMod.val qb))
      (signedCoeff (ZMod.val qc))
      (signedCoeff (ZMod.val k))
      (_root_.Int.ofNat a) (_root_.Int.ofNat b) (_root_.Int.ofNat c)
    0 ≤ E + _root_.Int.ofNat universalGateOffset ∧
      E + _root_.Int.ofNat universalGateOffset < _root_.Int.ofNat bls12381FrModulus := by
  have hbn := universalGateExpr_bounds qm qa qb qc k ha hb hc
  have hlt : _root_.Int.ofNat bn254FrModulus < _root_.Int.ofNat bls12381FrModulus := by decide
  exact ⟨hbn.1, lt_trans hbn.2 hlt⟩

/-- The shared 20-bit range table `"u20"` in `BLS12381Fr`. -/
def bls12381U20Entries : List (List BLS12381Fr) :=
  List.map (fun (v : Nat) => [(v : BLS12381Fr)]) (List.range (2 ^ 20))

def bls12381U20TableSpec : TableSpec BLS12381Fr :=
  { name := "u20", width := 1, entries := bls12381U20Entries }

/-- The 12-bit canonical high-limb table `"u12"` in `BLS12381Fr`. -/
def bls12381U12Entries : List (List BLS12381Fr) :=
  List.map (fun (v : Nat) => [(v : BLS12381Fr)]) (List.range (2 ^ 12))

def bls12381U12TableSpec : TableSpec BLS12381Fr :=
  { name := "u12", width := 1, entries := bls12381U12Entries }

/-- Translate a source `GoldilocksF` lookup table to `BLS12381Fr` with `"src:"` prefix. -/
def bls12381TranslateTable (t : TableSpec GoldilocksF) : TableSpec BLS12381Fr :=
  { name := "src:" ++ t.name
    width := t.width
    entries := t.entries.map (fun row => row.map (fun v => (ZMod.val v : BLS12381Fr))) }

theorem bls12381U20Entries_mem (row : List BLS12381Fr) :
    row ∈ bls12381U20Entries ↔ ∃ v : Nat, v < 2 ^ 20 ∧ [(v : BLS12381Fr)] = row := by
  unfold bls12381U20Entries
  simp only [List.mem_map, List.mem_range]

theorem bls12381U12Entries_mem (row : List BLS12381Fr) :
    row ∈ bls12381U12Entries ↔ ∃ v : Nat, v < 2 ^ 12 ∧ [(v : BLS12381Fr)] = row := by
  unfold bls12381U12Entries
  simp only [List.mem_map, List.mem_range]

attribute [irreducible] bls12381U20Entries bls12381U12Entries

theorem bls12381_u20_lookup_val_lt (tables : List (TableSpec GoldilocksF))
    (wire : Wire) (w_fr : Wire → BLS12381Fr)
    (h : LookupConstraint.Satisfied
      (bls12381U20TableSpec :: bls12381U12TableSpec :: tables.map bls12381TranslateTable)
      { tableName := "u20", wires := [wire] } w_fr) :
    ZMod.val (w_fr wire) < 2 ^ 20 := by
  rcases h with ⟨t, ht, hname, hmem⟩
  simp only [List.mem_cons, List.mem_map] at ht
  rcases ht with rfl | rfl | ⟨srcT, _, rfl⟩
  · have hmem' : [w_fr wire] ∈ bls12381U20Entries := hmem
    rw [bls12381U20Entries_mem] at hmem'
    rcases hmem' with ⟨v, hv, heq⟩
    injection heq with hhead _
    rw [← hhead, ZMod.val_natCast, Nat.mod_eq_of_lt]
    · exact hv
    · unfold bls12381FrModulus; omega
  · exact absurd hname u12_ne_u20
  · exact absurd hname (src_prefix_ne_u20 srcT.name)

theorem bls12381_u12_lookup_val_lt (tables : List (TableSpec GoldilocksF))
    (wire : Wire) (w_fr : Wire → BLS12381Fr)
    (h : LookupConstraint.Satisfied
      (bls12381U20TableSpec :: bls12381U12TableSpec :: tables.map bls12381TranslateTable)
      { tableName := "u12", wires := [wire] } w_fr) :
    ZMod.val (w_fr wire) < 2 ^ 12 := by
  rcases h with ⟨t, ht, hname, hmem⟩
  simp only [List.mem_cons, List.mem_map] at ht
  rcases ht with rfl | rfl | ⟨srcT, _, rfl⟩
  · exact absurd hname.symm u12_ne_u20
  · have hmem' : [w_fr wire] ∈ bls12381U12Entries := hmem
    rw [bls12381U12Entries_mem] at hmem'
    rcases hmem' with ⟨v, hv, heq⟩
    injection heq with hhead _
    rw [← hhead, ZMod.val_natCast, Nat.mod_eq_of_lt]
    · exact hv
    · unfold bls12381FrModulus; omega
  · exact absurd hname (src_prefix_ne_u12 srcT.name)

theorem bls12381_val_eq_of_natCast_eq {x : BLS12381Fr} {n : Nat}
    (heq : x = (n : BLS12381Fr)) (hlt : n < bls12381FrModulus) :
    ZMod.val x = n := by
  rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

/-- The 6 degree-2 Plonkish gates in `BLS12381Fr` for the canonical Goldilocks check on wire `v`. -/
def bls12381CanonicalWireGates (v base : Nat) : List (Gate BLS12381Fr) :=
  let lo0 := base
  let lo1 := base + 1
  let hi0 := base + 2
  let hi1 := base + 3
  let lo := base + 4
  let hi := base + 5
  let inv := base + 6
  let max_hi := base + 7
  [ { a := lo0, b := lo1, c := lo, qm := 0, qa := 1, qb := (2 ^ 20 : BLS12381Fr), qc := -1, k := 0 },
    { a := hi0, b := hi1, c := hi, qm := 0, qa := 1, qb := (2 ^ 20 : BLS12381Fr), qc := -1, k := 0 },
    { a := lo, b := hi, c := v, qm := 0, qa := 1, qb := (2 ^ 32 : BLS12381Fr), qc := -1, k := 0 },
    { a := max_hi, b := max_hi, c := 0, qm := 1, qa := -1, qb := 0, qc := 0, k := 0 },
    { a := hi, b := inv, c := max_hi, qm := 1, qa := 0, qb := -(0xffffffff : BLS12381Fr), qc := 1, k := -1 },
    { a := max_hi, b := lo, c := 0, qm := 1, qa := 0, qb := 0, qc := 0, k := 0 } ]

theorem bls12381_canonicalWireGadget_sound (tables : List (TableSpec GoldilocksF))
    (v base : Nat) (w_fr : Wire → BLS12381Fr)
    (hgates : ∀ g ∈ bls12381CanonicalWireGates v base, g.Satisfied w_fr)
    (hlookups : ∀ l ∈ canonicalWireLookups base,
      l.Satisfied (bls12381U20TableSpec :: bls12381U12TableSpec :: tables.map bls12381TranslateTable) w_fr) :
    ZMod.val (w_fr v) < goldilocksP := by
  have hlo0 : ZMod.val (w_fr base) < 2 ^ 20 :=
    bls12381_u20_lookup_val_lt tables base w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hlo1 : ZMod.val (w_fr (base + 1)) < 2 ^ 12 :=
    bls12381_u12_lookup_val_lt tables (base + 1) w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hhi0 : ZMod.val (w_fr (base + 2)) < 2 ^ 20 :=
    bls12381_u20_lookup_val_lt tables (base + 2) w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hhi1 : ZMod.val (w_fr (base + 3)) < 2 ^ 12 :=
    bls12381_u12_lookup_val_lt tables (base + 3) w_fr (hlookups _ (by simp [canonicalWireLookups]))
  have hg1 := hgates
    { a := base, b := base + 1, c := base + 4,
      qm := 0, qa := 1, qb := (2 ^ 20 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381CanonicalWireGates])
  have hg2 := hgates
    { a := base + 2, b := base + 3, c := base + 5,
      qm := 0, qa := 1, qb := (2 ^ 20 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381CanonicalWireGates])
  have hg3 := hgates
    { a := base + 4, b := base + 5, c := v,
      qm := 0, qa := 1, qb := (2 ^ 32 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381CanonicalWireGates])
  have hg5 := hgates
    { a := base + 5, b := base + 6, c := base + 7,
      qm := 1, qa := 0, qb := -(0xffffffff : BLS12381Fr), qc := 1, k := -1 }
    (by simp [bls12381CanonicalWireGates])
  have hg6 := hgates
    { a := base + 7, b := base + 4, c := 0,
      qm := 1, qa := 0, qb := 0, qc := 0, k := 0 }
    (by simp [bls12381CanonicalWireGates])
  unfold Gate.Satisfied Gate.eval at hg1 hg2 hg3 hg5 hg6
  have hlo_eq : w_fr (base + 4) =
      ((ZMod.val (w_fr base) + 2 ^ 20 * ZMod.val (w_fr (base + 1)) : Nat) : BLS12381Fr) := by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; linear_combination -hg1
  have hlo_val : ZMod.val (w_fr (base + 4)) =
      ZMod.val (w_fr base) + 2 ^ 20 * ZMod.val (w_fr (base + 1)) :=
    bls12381_val_eq_of_natCast_eq hlo_eq (by unfold bls12381FrModulus; omega)
  have hhi_eq : w_fr (base + 5) =
      ((ZMod.val (w_fr (base + 2)) + 2 ^ 20 * ZMod.val (w_fr (base + 3)) : Nat) : BLS12381Fr) := by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; linear_combination -hg2
  have hhi_val : ZMod.val (w_fr (base + 5)) =
      ZMod.val (w_fr (base + 2)) + 2 ^ 20 * ZMod.val (w_fr (base + 3)) :=
    bls12381_val_eq_of_natCast_eq hhi_eq (by unfold bls12381FrModulus; omega)
  have hv_eq : w_fr v =
      ((reconstructU64FromU20U12 (ZMod.val (w_fr base)) (ZMod.val (w_fr (base + 1)))
        (ZMod.val (w_fr (base + 2))) (ZMod.val (w_fr (base + 3))) : Nat) : BLS12381Fr) := by
    unfold reconstructU64FromU20U12
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination -hg3 - hg1 - (2 ^ 32 : BLS12381Fr) * hg2
  have hv_val : ZMod.val (w_fr v) =
      reconstructU64FromU20U12 (ZMod.val (w_fr base)) (ZMod.val (w_fr (base + 1)))
        (ZMod.val (w_fr (base + 2))) (ZMod.val (w_fr (base + 3))) :=
    bls12381_val_eq_of_natCast_eq hv_eq (by unfold reconstructU64FromU20U12 bls12381FrModulus; omega)
  rw [hv_val, ← canonical_iff_lt_goldilocksP _ _ _ _ hlo0 hlo1 hhi0 hhi1]
  intro hhi_max
  have hhi_cast : w_fr (base + 5) = (0xffffffff : BLS12381Fr) := by
    rw [← ZMod.natCast_zmod_val (w_fr (base + 5)), hhi_val, hhi_max]; rfl
  have hmax1 : w_fr (base + 7) = 1 := by
    rw [hhi_cast] at hg5; linear_combination hg5
  have hlo0_fr : w_fr (base + 4) = 0 := by
    rw [hmax1] at hg6; linear_combination hg6
  rw [← hlo_val, hlo0_fr, ZMod.val_zero]

/-- The 8 degree-2 Plonkish gates in `BLS12381Fr` for a translated Goldilocks gate `g`. -/
def bls12381TranslatedGateGates (g : Gate GoldilocksF) (gbase : Nat) : List (Gate BLS12381Fr) :=
  let qm : BLS12381Fr := (signedCoeff (ZMod.val g.qm) : BLS12381Fr)
  let qa : BLS12381Fr := (signedCoeff (ZMod.val g.qa) : BLS12381Fr)
  let qb : BLS12381Fr := (signedCoeff (ZMod.val g.qb) : BLS12381Fr)
  let qc : BLS12381Fr := (signedCoeff (ZMod.val g.qc) : BLS12381Fr)
  let k : BLS12381Fr := (signedCoeff (ZMod.val g.k) : BLS12381Fr)
  let q0 := gbase
  let q1 := gbase + 1
  let q2 := gbase + 2
  let q3 := gbase + 3
  let q4 := gbase + 4
  let q5 := gbase + 5
  let q6 := gbase + 6
  let acc1 := gbase + 7
  let acc2 := gbase + 8
  let acc3 := gbase + 9
  let acc4 := gbase + 10
  let acc5 := gbase + 11
  let q_wire := gbase + 12
  let t1 := gbase + 13
  [ { a := q0, b := q1, c := acc1, qm := 0, qa := 1, qb := (2 ^ 20 : BLS12381Fr), qc := -1, k := 0 },
    { a := acc1, b := q2, c := acc2, qm := 0, qa := 1, qb := (2 ^ 40 : BLS12381Fr), qc := -1, k := 0 },
    { a := acc2, b := q3, c := acc3, qm := 0, qa := 1, qb := (2 ^ 60 : BLS12381Fr), qc := -1, k := 0 },
    { a := acc3, b := q4, c := acc4, qm := 0, qa := 1, qb := (2 ^ 80 : BLS12381Fr), qc := -1, k := 0 },
    { a := acc4, b := q5, c := acc5, qm := 0, qa := 1, qb := (2 ^ 100 : BLS12381Fr), qc := -1, k := 0 },
    { a := acc5, b := q6, c := q_wire, qm := 0, qa := 1, qb := (2 ^ 120 : BLS12381Fr), qc := -1, k := 0 },
    { a := g.a, b := g.b, c := t1,
      qm := qm, qa := qa, qb := qb, qc := -1,
      k := k + (universalGateOffset : BLS12381Fr) },
    { a := t1, b := g.c, c := q_wire,
      qm := 0, qa := 1, qb := qc, qc := -(goldilocksP : BLS12381Fr), k := 0 } ]

/-- Project a `BLS12381Fr` wire assignment to `GoldilocksF` via canonical reduction mod `goldilocksP`. -/
def bls12381ProjectGoldilocksWire (w_fr : Wire → BLS12381Fr) : Wire → GoldilocksF :=
  fun i => GoldilocksF.ofNat (BLS12381Fr.val (w_fr i) % goldilocksP)

theorem bls12381_translatedGateGadget_sound (tables : List (TableSpec GoldilocksF))
    (g : Gate GoldilocksF) (gbase : Nat) (w_fr : Wire → BLS12381Fr)
    (ha : ZMod.val (w_fr g.a) < goldilocksP)
    (hb : ZMod.val (w_fr g.b) < goldilocksP)
    (hc : ZMod.val (w_fr g.c) < goldilocksP)
    (hgates : ∀ gate ∈ bls12381TranslatedGateGates g gbase, gate.Satisfied w_fr)
    (hlookups : ∀ l ∈ translatedGateLookups gbase,
      l.Satisfied (bls12381U20TableSpec :: bls12381U12TableSpec :: tables.map bls12381TranslateTable) w_fr) :
    g.Satisfied (bls12381ProjectGoldilocksWire w_fr) := by
  have hq0 := bls12381_u20_lookup_val_lt tables gbase w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq1 := bls12381_u20_lookup_val_lt tables (gbase + 1) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq2 := bls12381_u20_lookup_val_lt tables (gbase + 2) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq3 := bls12381_u20_lookup_val_lt tables (gbase + 3) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq4 := bls12381_u20_lookup_val_lt tables (gbase + 4) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq5 := bls12381_u20_lookup_val_lt tables (gbase + 5) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hq6 := bls12381_u20_lookup_val_lt tables (gbase + 6) w_fr (hlookups _ (by simp [translatedGateLookups]))
  have hg_l1 := hgates
    { a := gbase, b := gbase + 1, c := gbase + 7, qm := 0, qa := 1, qb := (2 ^ 20 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381TranslatedGateGates])
  have hg_l2 := hgates
    { a := gbase + 7, b := gbase + 2, c := gbase + 8, qm := 0, qa := 1, qb := (2 ^ 40 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381TranslatedGateGates])
  have hg_l3 := hgates
    { a := gbase + 8, b := gbase + 3, c := gbase + 9, qm := 0, qa := 1, qb := (2 ^ 60 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381TranslatedGateGates])
  have hg_l4 := hgates
    { a := gbase + 9, b := gbase + 4, c := gbase + 10, qm := 0, qa := 1, qb := (2 ^ 80 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381TranslatedGateGates])
  have hg_l5 := hgates
    { a := gbase + 10, b := gbase + 5, c := gbase + 11, qm := 0, qa := 1, qb := (2 ^ 100 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381TranslatedGateGates])
  have hg_l6 := hgates
    { a := gbase + 11, b := gbase + 6, c := gbase + 12, qm := 0, qa := 1, qb := (2 ^ 120 : BLS12381Fr), qc := -1, k := 0 }
    (by simp [bls12381TranslatedGateGates])
  have hgA := hgates
    { a := g.a, b := g.b, c := gbase + 13,
      qm := (signedCoeff (ZMod.val g.qm) : BLS12381Fr),
      qa := (signedCoeff (ZMod.val g.qa) : BLS12381Fr),
      qb := (signedCoeff (ZMod.val g.qb) : BLS12381Fr),
      qc := -1,
      k := (signedCoeff (ZMod.val g.k) : BLS12381Fr) + (universalGateOffset : BLS12381Fr) }
    (by simp [bls12381TranslatedGateGates])
  have hgB := hgates
    { a := gbase + 13, b := g.c, c := gbase + 12,
      qm := 0, qa := 1,
      qb := (signedCoeff (ZMod.val g.qc) : BLS12381Fr),
      qc := -(goldilocksP : BLS12381Fr), k := 0 }
    (by simp [bls12381TranslatedGateGates])
  unfold Gate.Satisfied Gate.eval at hg_l1 hg_l2 hg_l3 hg_l4 hg_l5 hg_l6 hgA hgB
  let q_nat := reconstructQuotient7
    (ZMod.val (w_fr gbase)) (ZMod.val (w_fr (gbase + 1))) (ZMod.val (w_fr (gbase + 2)))
    (ZMod.val (w_fr (gbase + 3))) (ZMod.val (w_fr (gbase + 4))) (ZMod.val (w_fr (gbase + 5)))
    (ZMod.val (w_fr (gbase + 6)))
  have hq_nat_lt : q_nat < 2 ^ 140 :=
    reconstructQuotient7_lt _ _ _ _ _ _ _ hq0 hq1 hq2 hq3 hq4 hq5 hq6
  have hq_wire_eq : w_fr (gbase + 12) = (q_nat : BLS12381Fr) := by
    dsimp [q_nat, reconstructQuotient7]
    push_cast
    repeat rw [ZMod.natCast_zmod_val]
    linear_combination -(hg_l1 + hg_l2 + hg_l3 + hg_l4 + hg_l5 + hg_l6)
  let qm_i := signedCoeff (ZMod.val g.qm)
  let qa_i := signedCoeff (ZMod.val g.qa)
  let qb_i := signedCoeff (ZMod.val g.qb)
  let qc_i := signedCoeff (ZMod.val g.qc)
  let k_i := signedCoeff (ZMod.val g.k)
  let a_n := ZMod.val (w_fr g.a)
  let b_n := ZMod.val (w_fr g.b)
  let c_n := ZMod.val (w_fr g.c)
  let E := gateIntExpr qm_i qa_i qb_i qc_i k_i (_root_.Int.ofNat a_n) (_root_.Int.ofNat b_n) (_root_.Int.ofNat c_n)
  have hE_cast : ((E + _root_.Int.ofNat universalGateOffset -
      _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q_nat : ℤ) : BLS12381Fr) = 0 := by
    dsimp [E, gateIntExpr, a_n, b_n, c_n]
    push_cast
    rw [ZMod.natCast_zmod_val (w_fr g.a), ZMod.natCast_zmod_val (w_fr g.b),
        ZMod.natCast_zmod_val (w_fr g.c), ← hq_wire_eq]
    linear_combination hgA + hgB
  have hdvdR : (_root_.Int.ofNat bls12381FrModulus) ∣
      (E + _root_.Int.ofNat universalGateOffset - _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q_nat) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ bls12381FrModulus).mp hE_cast
  have hmodR : E + _root_.Int.ofNat universalGateOffset - _root_.Int.ofNat goldilocksP * _root_.Int.ofNat q_nat ≡
      0 [ZMOD _root_.Int.ofNat bls12381FrModulus] :=
    _root_.Int.modEq_zero_iff_dvd.mpr hdvdR
  have hbounds := bls12381_universalGateExpr_bounds g.qm g.qa g.qb g.qc g.k ha hb hc
  have hsound := bls12381_quotient_gate_sound qm_i qa_i qb_i qc_i k_i
    (_root_.Int.ofNat a_n) (_root_.Int.ofNat b_n) (_root_.Int.ofNat c_n)
    universalGateOffset q_nat hbounds.1 hbounds.2 hq_nat_lt universalGateOffset_mod hmodR
  have hdvdP : (_root_.Int.ofNat goldilocksP) ∣ E := _root_.Int.modEq_zero_iff_dvd.mp hsound.2
  have hE_gl : ((E : ℤ) : GoldilocksF) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd E goldilocksP).mpr hdvdP
  unfold Gate.Satisfied Gate.eval bls12381ProjectGoldilocksWire BLS12381Fr.val GoldilocksF.ofNat
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]
  dsimp [E, gateIntExpr, qm_i, qa_i, qb_i, qc_i, k_i, a_n, b_n, c_n] at hE_gl
  push_cast at hE_gl
  rw [signedCoeff_cast_goldilocks g.qm,
      signedCoeff_cast_goldilocks g.qa,
      signedCoeff_cast_goldilocks g.qb,
      signedCoeff_cast_goldilocks g.qc,
      signedCoeff_cast_goldilocks g.k] at hE_gl
  exact hE_gl

/-- **Goldilocks-to-BLS12-381 Plonkish Circuit Compiler (`bls12381ForeignCompile`)**:
Translates any `c : Plonkish.Circuit GoldilocksF` into a `Plonkish.Circuit BLS12381Fr`. -/
def bls12381ForeignCompile (c : Circuit GoldilocksF) : Circuit BLS12381Fr :=
  let refs := allReferencedWires c
  let base0 := maxWireBound c
  let wireBase (idx : Nat) : Nat := base0 + 8 * idx
  let gateStart : Nat := base0 + 8 * refs.length
  let gateBase (idx : Nat) : Nat := gateStart + 14 * idx
  let canonGates := refs.zipIdx.flatMap fun (v, idx) => bls12381CanonicalWireGates v (wireBase idx)
  let canonLookups := refs.zipIdx.flatMap fun (_, idx) => canonicalWireLookups (wireBase idx)
  let gateGates := c.gates.zipIdx.flatMap fun (g, idx) => bls12381TranslatedGateGates g (gateBase idx)
  let gateLookups := c.gates.zipIdx.flatMap fun (_, idx) => translatedGateLookups (gateBase idx)
  { numWires := gateStart + 14 * c.gates.length
    publicInputs := c.publicInputs
    gates := canonGates ++ gateGates
    tables := bls12381U20TableSpec :: bls12381U12TableSpec :: c.tables.map bls12381TranslateTable
    lookups := canonLookups ++ gateLookups ++ c.lookups.map translateLookup
    blake3Calls := c.blake3Calls }

theorem bls12381ForeignCompile_wire_canonical (c : Circuit GoldilocksF)
    (w_fr : Wire → BLS12381Fr) (hhold : (bls12381ForeignCompile c).ConstraintsHold w_fr)
    {v : Wire} (hv : v ∈ allReferencedWires c) :
    ZMod.val (w_fr v) < goldilocksP := by
  rcases List.mem_iff_getElem.mp hv with ⟨idx, hidx, hget⟩
  let base := maxWireBound c + 8 * idx
  have hmem_zip : (v, idx) ∈ (allReferencedWires c).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa [List.getElem?_eq_getElem hidx] using hget
  apply bls12381_canonicalWireGadget_sound c.tables v base w_fr
  · intro g hg
    apply hhold.1 g
    unfold bls12381ForeignCompile
    rw [List.mem_append]; left; rw [List.mem_flatMap]
    exact ⟨(v, idx), hmem_zip, hg⟩
  · intro l hl
    apply hhold.2.1 l
    unfold bls12381ForeignCompile
    rw [List.mem_append, List.mem_append]; left; left; rw [List.mem_flatMap]
    exact ⟨(v, idx), hmem_zip, hl⟩

/-- Map a list of `GoldilocksF` public inputs into `BLS12381Fr` via canonical embedding. -/
def bls12381LiftPublicInputs (pub : List GoldilocksF) : List BLS12381Fr :=
  pub.map (fun x => (ZMod.val x : BLS12381Fr))

/-- **End-to-End BLS12-381 Foreign Compiler Soundness (`bls12381_foreign_compile_sound`)**. -/
theorem bls12381_foreign_compile_sound (c : Circuit GoldilocksF)
    (pub_fr : List BLS12381Fr) (w_fr : Wire → BLS12381Fr)
    (hsat : (bls12381ForeignCompile c).Satisfies pub_fr w_fr) :
    c.Satisfies
      (pub_fr.map (fun x => GoldilocksF.ofNat (BLS12381Fr.val x % goldilocksP)))
      (bls12381ProjectGoldilocksWire w_fr) := by
  have hhold : (bls12381ForeignCompile c).ConstraintsHold w_fr := ⟨hsat.2.1, hsat.2.2.1, hsat.2.2.2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hpub := hsat.1
    change c.publicInputs.map w_fr = pub_fr at hpub
    rw [← hpub, List.map_map]
    rfl
  · intro g hg
    rcases List.mem_iff_getElem.mp hg with ⟨idx, hidx, hget⟩
    have hmem_zip : (g, idx) ∈ c.gates.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?]
      simpa [List.getElem?_eq_getElem hidx] using hget
    rcases mem_allReferencedWires_of_gate hg with ⟨hga, hgb, hgc⟩
    have ha := bls12381ForeignCompile_wire_canonical c w_fr hhold hga
    have hb := bls12381ForeignCompile_wire_canonical c w_fr hhold hgb
    have hc := bls12381ForeignCompile_wire_canonical c w_fr hhold hgc
    let gbase := (maxWireBound c + 8 * (allReferencedWires c).length) + 14 * idx
    apply bls12381_translatedGateGadget_sound c.tables g gbase w_fr ha hb hc
    · intro gate hgate
      apply hhold.1 gate
      unfold bls12381ForeignCompile
      rw [List.mem_append]; right; rw [List.mem_flatMap]
      exact ⟨(g, idx), hmem_zip, hgate⟩
    · intro l hl
      apply hhold.2.1 l
      unfold bls12381ForeignCompile
      rw [List.mem_append, List.mem_append]; left; right; rw [List.mem_flatMap]
      exact ⟨(g, idx), hmem_zip, hl⟩
  · intro l hl
    have hl_fr : (translateLookup l).Satisfied (bls12381ForeignCompile c).tables w_fr := by
      apply hhold.2.1 (translateLookup l)
      unfold bls12381ForeignCompile
      rw [List.mem_append]; right
      exact List.mem_map_of_mem hl
    rcases hl_fr with ⟨t_fr, ht_fr, hname_fr, hmem_fr⟩
    simp only [bls12381ForeignCompile, List.mem_cons, List.mem_map] at ht_fr
    rcases ht_fr with rfl | rfl | ⟨srcT, hsrcT, rfl⟩
    · exact absurd hname_fr.symm (src_prefix_ne_u20 l.tableName)
    · exact absurd hname_fr.symm (src_prefix_ne_u12 l.tableName)
    · have hname : srcT.name = l.tableName := src_prefix_inj hname_fr
      simp only [bls12381TranslateTable, translateLookup, List.mem_map] at hmem_fr
      rcases hmem_fr with ⟨srcRow, hsrcRow, hrow_eq⟩
      refine ⟨srcT, hsrcT, hname, ?_⟩
      have hproj : l.wires.map (bls12381ProjectGoldilocksWire w_fr) = srcRow := by
        have hmap := congrArg
          (List.map (fun x : BLS12381Fr => GoldilocksF.ofNat (BLS12381Fr.val x % goldilocksP)))
          hrow_eq.symm
        rw [List.map_map, List.map_map] at hmap
        simp only [Function.comp_def] at hmap
        change l.wires.map (fun i => GoldilocksF.ofNat (BLS12381Fr.val (w_fr i) % goldilocksP)) = srcRow
        rw [hmap]
        have hid : ∀ v : GoldilocksF,
            GoldilocksF.ofNat (BLS12381Fr.val (ZMod.val v : BLS12381Fr) % goldilocksP) = v := by
          intro v
          have hv_lt : ZMod.val v < bls12381FrModulus :=
            Nat.lt_trans (ZMod.val_lt v) goldilocksP_lt_bls12381FrModulus
          unfold BLS12381Fr.val GoldilocksF.ofNat
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv_lt,
              Nat.mod_eq_of_lt (ZMod.val_lt v), ZMod.natCast_zmod_val]
        calc
          List.map (fun x => GoldilocksF.ofNat (BLS12381Fr.val (ZMod.val x : BLS12381Fr) % goldilocksP)) srcRow
            = List.map id srcRow := List.map_congr_left (fun v _ => hid v)
          _ = srcRow := List.map_id srcRow
      rw [hproj]
      exact hsrcRow
  · intro b hb
    have hb_fr : b.Satisfied w_fr := hhold.2.2 b hb
    rcases hb_fr with ⟨bytes, hin, hout⟩
    refine ⟨bytes, ?_, ?_⟩
    · have hmap := congrArg
        (List.map (fun x : BLS12381Fr => GoldilocksF.ofNat (BLS12381Fr.val x % goldilocksP))) hin
      rw [List.map_map, List.map_map] at hmap
      simp only [Function.comp_def] at hmap
      change b.inputWires.map (fun i => GoldilocksF.ofNat (BLS12381Fr.val (w_fr i) % goldilocksP)) = _
      rw [hmap]
      apply List.map_congr_left
      intro u _
      have hu_p : u.toNat < goldilocksP := by have := u.toNat_lt; unfold goldilocksP; omega
      have hu_r : u.toNat < bls12381FrModulus := Nat.lt_trans hu_p goldilocksP_lt_bls12381FrModulus
      unfold BLS12381Fr.val GoldilocksF.ofNat
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu_r, Nat.mod_eq_of_lt hu_p]
    · have hmap := congrArg
        (List.map (fun x : BLS12381Fr => GoldilocksF.ofNat (BLS12381Fr.val x % goldilocksP))) hout
      rw [List.map_map, List.map_map] at hmap
      simp only [Function.comp_def] at hmap
      change b.outputWires.map (fun i => GoldilocksF.ofNat (BLS12381Fr.val (w_fr i) % goldilocksP)) = _
      rw [hmap]
      apply List.map_congr_left
      intro u _
      have hu_p : u.toNat < goldilocksP := by have := u.toNat_lt; unfold goldilocksP; omega
      have hu_r : u.toNat < bls12381FrModulus := Nat.lt_trans hu_p goldilocksP_lt_bls12381FrModulus
      unfold BLS12381Fr.val GoldilocksF.ofNat
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hu_r, Nat.mod_eq_of_lt hu_p]

/-- **Lifted Goldilocks-in-`BLS12381Fr` Foreign Compiler Soundness (`bls12381_foreign_compile_sound_lifted`)**. -/
theorem bls12381_foreign_compile_sound_lifted (c : Circuit GoldilocksF)
    (pub : List GoldilocksF) (w_fr : Wire → BLS12381Fr)
    (hsat : (bls12381ForeignCompile c).Satisfies (bls12381LiftPublicInputs pub) w_fr) :
    c.Satisfies pub (bls12381ProjectGoldilocksWire w_fr) := by
  have h := bls12381_foreign_compile_sound c (bls12381LiftPublicInputs pub) w_fr hsat
  have hpub : (bls12381LiftPublicInputs pub).map
      (fun x => GoldilocksF.ofNat (BLS12381Fr.val x % goldilocksP)) = pub := by
    unfold bls12381LiftPublicInputs
    rw [List.map_map]
    have hid : ∀ v : GoldilocksF,
        GoldilocksF.ofNat (BLS12381Fr.val (ZMod.val v : BLS12381Fr) % goldilocksP) = v := by
      intro v
      have hv_lt : ZMod.val v < bls12381FrModulus :=
        Nat.lt_trans (ZMod.val_lt v) goldilocksP_lt_bls12381FrModulus
      unfold BLS12381Fr.val GoldilocksF.ofNat
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hv_lt,
          Nat.mod_eq_of_lt (ZMod.val_lt v), ZMod.natCast_zmod_val]
    calc
      List.map (fun x => GoldilocksF.ofNat (BLS12381Fr.val (ZMod.val x : BLS12381Fr) % goldilocksP)) pub
        = List.map id pub := List.map_congr_left (fun v _ => hid v)
      _ = pub := List.map_id pub
  rwa [hpub] at h

/-- **Foreign `BLS12381Fr`-Compiled FRI Verifier Soundness (`bls12381_foreign_friVerifier_sound`)**:
Composes `bls12381_foreign_compile_sound_lifted` with existing
`Ix.Cert.Compression.FriVerifier.friVerifierCircuit_sound`: any `BLS12381Fr` wire assignment
satisfying `bls12381ForeignCompile (buildFriVerifierCircuit base layout)` on
`bls12381LiftPublicInputs pub` projects directly to a Goldilocks wire assignment satisfying
`FriVerifierSatisfied base layout pub`. -/
theorem bls12381_foreign_friVerifier_sound (base : Circuit GoldilocksF) (layout : FriVerifierLayout)
    (hlen : ∀ s ∈ layout.merkleSteps, s.2.1.length = s.2.2.1.length)
    (pub : List GoldilocksF) (w_fr : Wire → BLS12381Fr)
    (hsat : (bls12381ForeignCompile (buildFriVerifierCircuit base layout)).Satisfies
      (bls12381LiftPublicInputs pub) w_fr) :
    FriVerifierSatisfied base layout pub (bls12381ProjectGoldilocksWire w_fr) :=
  friVerifierCircuit_sound base layout hlen pub (bls12381ProjectGoldilocksWire w_fr)
    (bls12381_foreign_compile_sound_lifted (buildFriVerifierCircuit base layout) pub w_fr hsat)

end Ix.Cert.Compression.Bls12381.Field
