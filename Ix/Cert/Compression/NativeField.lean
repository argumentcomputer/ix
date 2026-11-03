import Ix.Cert.Compression.Plonkish
import Ix.Cert.Compression.Foreign

/-! # Non-Native `BN254::Fq` Limb Arithmetic Soundness (`crates/proof-compression/src/recursive/native_field.rs`)

This module formalizes and proves the soundness of the non-native `BN254::Fq` base-field
gadget implemented over `BN254::Fr` in `crates/proof-compression/src/recursive/native_field.rs`:

1. **Moduli and 80-Bit Limb Representation (`FqLimbs`, `evalLimbs`)**:
   - `bn254FqModulus`: the 254-bit BN254 base field prime $q$.
   - `bn254FrModulus`: the 254-bit BN254 scalar field prime $r$.
   - `FqLimbs`: 4 limbs `(l0, l1, l2, l3)` in base $2^{80}$, with top limb bounded by $2^{14}$.
2. **20-Bit Lookup Table Range Soundness (`range20_limb80_bound`, `range20_carry89_bound`)**:
   - Four 20-bit lookup sub-limbs pack into a strictly bounded 80-bit limb ($< 2^{80}$).
   - Five 20-bit lookup sub-limbs with top limb scaled by $2^{11}$ pack into a biased
     89-bit carry in $[-2^{88}, 2^{88})$.
3. **Paired-Limb No-Overflow & Modular Relation Soundness (`paired_limb_no_overflow`, `fq_relation_sound`)**:
   - Because each paired 80-bit limb equation with 89-bit carries has total integer
     magnitude $< 2^{249} < r / 2$, equality modulo `bn254FrModulus` implies exact integer
     equality in $\mathbb{Z}$.
   - Summing the paired limb equations telescopes all intermediate carries and yields
     exact divisibility by `bn254FqModulus`.
4. **Arithmetic & Canonicality Corollaries (`fq_add_sound`, `fq_sub_sound`, `fq_mul_sound`, `fq_inv_or_zero_sound`, `fq_canonical_lt_q_sound`)**:
   - Soundness of modular addition, subtraction, multiplication, zero-or-inverse equality
     flag (`equal_flag`), and limb-wise borrow subtraction from $q - 1$ (`FqGadget::canonical`).
-/

namespace Ix.Cert.Compression.NativeField

open Ix.Cert.Compression.Plonkish
open Ix.Cert.Compression.Foreign

/-! ## 1. BN254 Field Moduli & Gadget Constants -/

/-- The BN254 base field prime modulus $q = \lvert\mathbb{F}_q\rvert$. -/
def bn254FqModulus : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- Bit width $W = 80$ of each ordinary limb (`native_field.rs:12`). -/
def LIMB_BITS : Nat := 80

/-- Number of 80-bit limbs $L = 4$ representing a 254-bit `BN254::Fq` element (`native_field.rs:16`). -/
def NUM_LIMBS : Nat := 4

/-- Bit width $254 - 3 \times 80 = 14$ of the most-significant limb (`native_field.rs:17`). -/
def TOP_LIMB_BITS : Nat := 14

/-- Bit width of the `"Fq range"` lookup table (`native_field.rs:14`). -/
def RANGE_BITS : Nat := 20

/-- Bit width of biased carries in `FqGadget::relation` (`native_field.rs:21`). -/
def CARRY_BITS : Nat := 89

/-- Signed carry bias $2^{88}$ (`native_field.rs:22`). -/
def CARRY_BIAS : Int := 2 ^ 88

/-- Limb radix $B = 2^{80}$. -/
def LIMB_RADIX : Nat := 2 ^ 80

/-- Paired-limb block radix $B^2 = 2^{160}$. -/
def BLOCK_RADIX : Nat := 2 ^ 160

/-- Positivity of `bn254FqModulus`. -/
theorem bn254FqModulus_pos : 0 < bn254FqModulus := by decide

/-- Positivity of `bn254FrModulus`. -/
theorem bn254FrModulus_pos : 0 < bn254FrModulus := by decide

/-- `2^249` is strictly less than half of `bn254FrModulus`. -/
theorem two_pow_249_lt_bn254FrModulus_half : 2 ^ 249 * 2 < bn254FrModulus := by decide

/-! ## 2. 4-Limb Representation & Sub-Limb Range Lookup Bounds -/

/-- Four 80-bit limbs representing a non-native `BN254::Fq` element (`FqVar` in `native_field.rs:29`). -/
structure FqLimbs where
  l0 : Nat
  l1 : Nat
  l2 : Nat
  l3 : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Integer evaluation of a 4-limb `FqLimbs` value in base $2^{80}$. -/
def evalLimbs (v : FqLimbs) : Nat :=
  v.l0 + v.l1 * 2 ^ 80 + v.l2 * 2 ^ 160 + v.l3 * 2 ^ 240

/-- Signed integer evaluation of a 4-limb `FqLimbs` value in base $2^{80}$. -/
def evalLimbsInt (v : FqLimbs) : Int :=
  (evalLimbs v : Int)

/-- Limb-wise bit-width bounds enforced by `FqGadget::bound` (`native_field.rs:155-159`). -/
def FqLimbs.Bounded (v : FqLimbs) : Prop :=
  v.l0 < 2 ^ 80 ∧ v.l1 < 2 ^ 80 ∧ v.l2 < 2 ^ 80 ∧ v.l3 < 2 ^ 14

/-- Canonicality predicate: the evaluated 4-limb integer is strictly below `bn254FqModulus`. -/
def FqLimbs.Canonical (v : FqLimbs) : Prop :=
  evalLimbs v < bn254FqModulus

/-- Base-$2^{80}$ limb decomposition of `bn254FqModulus`. -/
def fqModulusLimbs : FqLimbs :=
  { l0 := bn254FqModulus % (2 ^ 80)
    l1 := (bn254FqModulus / (2 ^ 80)) % (2 ^ 80)
    l2 := (bn254FqModulus / (2 ^ 160)) % (2 ^ 80)
    l3 := bn254FqModulus / (2 ^ 240) }

/-- Base-$2^{80}$ limb decomposition of `bn254FqModulus - 1` (`native_field.rs:161`). -/
def fqModulusMinusOneLimbs : FqLimbs :=
  { l0 := (bn254FqModulus - 1) % (2 ^ 80)
    l1 := ((bn254FqModulus - 1) / (2 ^ 80)) % (2 ^ 80)
    l2 := ((bn254FqModulus - 1) / (2 ^ 160)) % (2 ^ 80)
    l3 := (bn254FqModulus - 1) / (2 ^ 240) }

/-- `fqModulusLimbs` evaluates to `bn254FqModulus`. -/
theorem evalLimbs_fqModulusLimbs : evalLimbs fqModulusLimbs = bn254FqModulus := by
  decide

/-- `fqModulusMinusOneLimbs` evaluates to `bn254FqModulus - 1`. -/
theorem evalLimbs_fqModulusMinusOneLimbs :
    evalLimbs fqModulusMinusOneLimbs = bn254FqModulus - 1 := by
  decide

/-- Any `Bounded` 4-limb value has total value strictly below $2^{254}$. -/
theorem evalLimbs_lt_two_pow_254 {v : FqLimbs} (hb : v.Bounded) :
    evalLimbs v < 2 ^ 254 := by
  rcases hb with ⟨h0, h1, h2, h3⟩
  unfold evalLimbs
  omega

/-- **80-Bit Limb Range Check Soundness (`range20_limb80_bound`)**:
If four sub-limbs `s0, s1, s2, s3` are in the $2^{20}$ `"Fq range"` lookup table
($s_i < 2^{20}$), then their packed linear combination is strictly below $2^{80}$
(`FqGadget::range_n::<4>`, `native_field.rs:91-118`). -/
theorem range20_limb80_bound
    (s0 s1 s2 s3 : Nat)
    (h0 : s0 < 2 ^ 20) (h1 : s1 < 2 ^ 20) (h2 : s2 < 2 ^ 20) (h3 : s3 < 2 ^ 20) :
    s0 + s1 * 2 ^ 20 + s2 * 2 ^ 40 + s3 * 2 ^ 60 < 2 ^ 80 := by
  omega

/-- **14-Bit Top-Limb Range Check Soundness (`range20_topLimb14_bound`)**:
If `s0 < 2^20` and its shifted value `s0 * 2^6` is also in the $2^{20}$ lookup table,
then `s0 < 2^14` (`native_field.rs:104-110`). -/
theorem range20_topLimb14_bound
    (s0 : Nat) (hScaled : s0 * 2 ^ 6 < 2 ^ 20) :
    s0 < 2 ^ 14 := by
  omega

/-- **89-Bit Biased Carry Range Check Soundness (`range20_carry89_bound`)**:
If five sub-limbs `c0..c4 < 2^20` with `c4 < 2^9` (enforced by looking up `c4 * 2^11 < 2^20`),
then the biased carry $c - 2^{88}$ lies in $[-2^{88}, 2^{88})$ (`native_field.rs:91-118, 254-256`). -/
theorem range20_carry89_bound
    (c0 c1 c2 c3 c4 : Nat)
    (h0 : c0 < 2 ^ 20) (h1 : c1 < 2 ^ 20) (h2 : c2 < 2 ^ 20)
    (h3 : c3 < 2 ^ 20) (h4 : c4 < 2 ^ 9) :
    let c : Int := ((c0 + c1 * 2 ^ 20 + c2 * 2 ^ 40 + c3 * 2 ^ 60 + c4 * 2 ^ 80 : Nat) : Int);
    -CARRY_BIAS ≤ c - CARRY_BIAS ∧ c - CARRY_BIAS < CARRY_BIAS := by
  dsimp only
  unfold CARRY_BIAS
  omega

/-! ## 3. Paired-Limb Overflow Absence (`paired_limb_no_overflow`) -/

/-- Upper bound $A = 4 L B^2 + 3 B + 4$ on the magnitude of any single degree-$k$ limb
equation coefficient before carry pairing (`native_field.rs:208, 485`). -/
def coefficientBound : Int :=
  16 * (2 ^ 80 : Int) ^ 2 + 3 * (2 ^ 80 : Int) + 4

/-- Upper bound $(B + 1) A + (B^2 + 1) 2^{88}$ on the magnitude of any paired limb equation
(`native_field.rs:209, 487-488`). -/
def pairedEquationBound : Int :=
  (2 ^ 80 + 1) * coefficientBound + ((2 ^ 80 : Int) ^ 2 + 1) * CARRY_BIAS

/-- The maximum paired equation magnitude is strictly below $2^{249}$ and strictly below
half of `bn254FrModulus` (`native_field.rs:476-490`). -/
theorem pairedEquationBound_lt_fr_half :
    pairedEquationBound < 2 ^ 249 ∧ 2 * pairedEquationBound < (bn254FrModulus : Int) := by
  decide

/-- Fundamental integer no-wrap lemma: if an integer `e` has magnitude strictly below
`bn254FrModulus` and is zero modulo `bn254FrModulus`, then `e = 0` in $\mathbb{Z}$. -/
theorem int_eq_zero_of_mod_fr_eq_zero
    (e : Int)
    (hlo : -(bn254FrModulus : Int) < e)
    (hhi : e < (bn254FrModulus : Int))
    (hmod : e % (bn254FrModulus : Int) = 0) :
    e = 0 := by
  unfold bn254FrModulus at hlo hhi hmod
  omega

/-- **Paired-Limb No-Overflow Theorem (`paired_limb_no_overflow`)**:
In `FqGadget::relation` (`native_field.rs:288-303`), each paired `BN254::Fr` constraint combines
an even limb equation `eqEven`, $2^{80}$ times an odd limb equation `eqOdd`, an incoming
biased carry `carryIn`, and $-2^{160}$ times an outgoing biased carry `carryOut`.
Because $|eqEven|, |eqOdd| \le A$ (`coefficientBound`) and $|carryIn|, |carryOut| \le 2^{88}$,
the total integer value has magnitude strictly below $2^{249} < r / 2$, so modular equality in
`BN254::Fr` implies **exact integer equality in $\mathbb{Z}$**. -/
theorem paired_limb_no_overflow
    (eqEven eqOdd carryIn carryOut : Int)
    (hEvenLo : -coefficientBound ≤ eqEven) (hEvenHi : eqEven ≤ coefficientBound)
    (hOddLo : -coefficientBound ≤ eqOdd) (hOddHi : eqOdd ≤ coefficientBound)
    (hInLo : -CARRY_BIAS ≤ carryIn) (hInHi : carryIn ≤ CARRY_BIAS)
    (hOutLo : -CARRY_BIAS ≤ carryOut) (hOutHi : carryOut ≤ CARRY_BIAS)
    (hModFr : (eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut) % (bn254FrModulus : Int) = 0) :
    eqEven + 2 ^ 80 * eqOdd + carryIn - 2 ^ 160 * carryOut = 0 := by
  unfold coefficientBound CARRY_BIAS bn254FrModulus at *
  omega

/-! ## 4. Paired-Limb Modular Relation Soundness (`fq_relation_sound`) -/

/-- **Two-Pair Limb Telescoping Soundness (`fq_relation_sound`)**:
If four 80-bit limb equations `limbEq0, limbEq1, limbEq2, limbEq3` are paired into two
`BN254::Fr` equations:
- Pair 0: `(limbEq0 + 2^80 * limbEq1 - carry1 * 2^160) % r = 0`
- Pair 1: `(limbEq2 + carry1 + 2^80 * limbEq3) % r = 0`
with bounded magnitudes (`|limbEq_j| ≤ coefficientBound`, `|carry1| ≤ 2^88`), and
the limb equations decompose `lhs - qVal * q` across the four $2^{80}$-limbs, then:
1. Both paired equations hold with exact equality in $\mathbb{Z}$,
2. Summing Pair 0 + $2^{160} \cdot$ Pair 1 telescopes `carry1` and yields
   `lhs = qVal * bn254FqModulus`, and
3. `lhs % bn254FqModulus = 0` (`lhs ≡ 0 (mod q)`). -/
theorem fq_relation_sound
    (limbEq0 limbEq1 limbEq2 limbEq3 carry1 lhs qVal : Int)
    (h0Lo : -coefficientBound ≤ limbEq0) (h0Hi : limbEq0 ≤ coefficientBound)
    (h1Lo : -coefficientBound ≤ limbEq1) (h1Hi : limbEq1 ≤ coefficientBound)
    (h2Lo : -coefficientBound ≤ limbEq2) (h2Hi : limbEq2 ≤ coefficientBound)
    (h3Lo : -coefficientBound ≤ limbEq3) (h3Hi : limbEq3 ≤ coefficientBound)
    (hCarryLo : -CARRY_BIAS ≤ carry1) (hCarryHi : carry1 ≤ CARRY_BIAS)
    (hPair0 : (limbEq0 + 2 ^ 80 * limbEq1 - 2 ^ 160 * carry1) % (bn254FrModulus : Int) = 0)
    (hPair1 : (limbEq2 + carry1 + 2 ^ 80 * limbEq3) % (bn254FrModulus : Int) = 0)
    (hDecomp :
      limbEq0 + 2 ^ 80 * limbEq1 + 2 ^ 160 * limbEq2 + 2 ^ 240 * limbEq3 =
        lhs - qVal * (bn254FqModulus : Int)) :
    lhs = qVal * (bn254FqModulus : Int) ∧ lhs % (bn254FqModulus : Int) = 0 := by
  have hP0 : limbEq0 + 2 ^ 80 * limbEq1 + 0 - 2 ^ 160 * carry1 = 0 :=
    paired_limb_no_overflow limbEq0 limbEq1 0 carry1
      h0Lo h0Hi h1Lo h1Hi (by decide) (by decide) hCarryLo hCarryHi
      (by simpa using hPair0)
  have hP1 : limbEq2 + 2 ^ 80 * limbEq3 + carry1 - 2 ^ 160 * 0 = 0 :=
    paired_limb_no_overflow limbEq2 limbEq3 carry1 0
      h2Lo h2Hi h3Lo h3Hi hCarryLo hCarryHi (by decide) (by decide)
      (by
        have hEq : limbEq2 + 2 ^ 80 * limbEq3 + carry1 - 2 ^ 160 * 0 =
            limbEq2 + carry1 + 2 ^ 80 * limbEq3 := by omega
        rw [hEq]
        exact hPair1)
  have hSum : limbEq0 + 2 ^ 80 * limbEq1 + 2 ^ 160 * limbEq2 + 2 ^ 240 * limbEq3 = 0 := by
    omega
  have hLhs : lhs = qVal * (bn254FqModulus : Int) := by
    omega
  refine ⟨hLhs, ?_⟩
  rw [hLhs, Int.mul_comm, Int.mul_emod_right]

/-- **Four-Pair Convolution Telescoping Soundness (`fq_relation_four_pairs_sound`)**:
Full 8-degree (`2 * L = 8`) paired-limb telescoping matching the loop `for j in 0..L`
in `FqGadget::relation` (`native_field.rs:288-303`) with 3 biased 89-bit carries
`carry0, carry1, carry2`:
- Pair 0 ($j=0$): `t0 + 2^80 * t1 - 2^160 * carry0 ≡ 0 (mod r)`
- Pair 1 ($j=1$): `t2 + 2^80 * t3 + carry0 - 2^160 * carry1 ≡ 0 (mod r)`
- Pair 2 ($j=2$): `t4 + 2^80 * t5 + carry1 - 2^160 * carry2 ≡ 0 (mod r)`
- Pair 3 ($j=3$): `t6 + 2^80 * t7 + carry2 ≡ 0 (mod r)`
Summing $\sum_{j=0}^{3} 2^{160 j} \cdot \text{Pair}_j$ telescopes `carry0, carry1, carry2`
and proves $\sum_{k=0}^{7} t_k 2^{80 k} = 0$ in $\mathbb{Z}$, hence `lhs ≡ 0 (mod q)`. -/
theorem fq_relation_four_pairs_sound
    (t0 t1 t2 t3 t4 t5 t6 t7 carry0 carry1 carry2 lhs qVal : Int)
    (ht0Lo : -coefficientBound ≤ t0) (ht0Hi : t0 ≤ coefficientBound)
    (ht1Lo : -coefficientBound ≤ t1) (ht1Hi : t1 ≤ coefficientBound)
    (ht2Lo : -coefficientBound ≤ t2) (ht2Hi : t2 ≤ coefficientBound)
    (ht3Lo : -coefficientBound ≤ t3) (ht3Hi : t3 ≤ coefficientBound)
    (ht4Lo : -coefficientBound ≤ t4) (ht4Hi : t4 ≤ coefficientBound)
    (ht5Lo : -coefficientBound ≤ t5) (ht5Hi : t5 ≤ coefficientBound)
    (ht6Lo : -coefficientBound ≤ t6) (ht6Hi : t6 ≤ coefficientBound)
    (ht7Lo : -coefficientBound ≤ t7) (ht7Hi : t7 ≤ coefficientBound)
    (hc0Lo : -CARRY_BIAS ≤ carry0) (hc0Hi : carry0 ≤ CARRY_BIAS)
    (hc1Lo : -CARRY_BIAS ≤ carry1) (hc1Hi : carry1 ≤ CARRY_BIAS)
    (hc2Lo : -CARRY_BIAS ≤ carry2) (hc2Hi : carry2 ≤ CARRY_BIAS)
    (hPair0 : (t0 + 2 ^ 80 * t1 + 0 - 2 ^ 160 * carry0) % (bn254FrModulus : Int) = 0)
    (hPair1 : (t2 + 2 ^ 80 * t3 + carry0 - 2 ^ 160 * carry1) % (bn254FrModulus : Int) = 0)
    (hPair2 : (t4 + 2 ^ 80 * t5 + carry1 - 2 ^ 160 * carry2) % (bn254FrModulus : Int) = 0)
    (hPair3 : (t6 + 2 ^ 80 * t7 + carry2 - 2 ^ 160 * 0) % (bn254FrModulus : Int) = 0)
    (hDecomp :
      t0 + 2 ^ 80 * t1 + 2 ^ 160 * t2 + 2 ^ 240 * t3 +
        2 ^ 320 * t4 + 2 ^ 400 * t5 + 2 ^ 480 * t6 + 2 ^ 560 * t7 =
          lhs - qVal * (bn254FqModulus : Int)) :
    lhs = qVal * (bn254FqModulus : Int) ∧ lhs % (bn254FqModulus : Int) = 0 := by
  have hP0 := paired_limb_no_overflow t0 t1 0 carry0
    ht0Lo ht0Hi ht1Lo ht1Hi (by decide) (by decide) hc0Lo hc0Hi hPair0
  have hP1 := paired_limb_no_overflow t2 t3 carry0 carry1
    ht2Lo ht2Hi ht3Lo ht3Hi hc0Lo hc0Hi hc1Lo hc1Hi hPair1
  have hP2 := paired_limb_no_overflow t4 t5 carry1 carry2
    ht4Lo ht4Hi ht5Lo ht5Hi hc1Lo hc1Hi hc2Lo hc2Hi hPair2
  have hP3 := paired_limb_no_overflow t6 t7 carry2 0
    ht6Lo ht6Hi ht7Lo ht7Hi hc2Lo hc2Hi (by decide) (by decide) hPair3
  have hLhs : lhs = qVal * (bn254FqModulus : Int) := by omega
  refine ⟨hLhs, ?_⟩
  rw [hLhs, Int.mul_comm, Int.mul_emod_right]

/-! ## 5. Arithmetic & Canonicality Corollaries -/

/-- Predicate expressing that `FqGadget::relation` holds on an integer expression `expr`:
there exists a signed quotient `qVal` witnessed by the relation advice such that
`expr = qVal * bn254FqModulus`. -/
def FqRelationHolds (expr : Int) : Prop :=
  expr % (bn254FqModulus : Int) = 0

/-- Any paired-limb witness satisfying the hypotheses of `fq_relation_sound` establishes
`FqRelationHolds lhs`. -/
theorem fqRelationHolds_of_paired_limbs
    (limbEq0 limbEq1 limbEq2 limbEq3 carry1 lhs qVal : Int)
    (h0Lo : -coefficientBound ≤ limbEq0) (h0Hi : limbEq0 ≤ coefficientBound)
    (h1Lo : -coefficientBound ≤ limbEq1) (h1Hi : limbEq1 ≤ coefficientBound)
    (h2Lo : -coefficientBound ≤ limbEq2) (h2Hi : limbEq2 ≤ coefficientBound)
    (h3Lo : -coefficientBound ≤ limbEq3) (h3Hi : limbEq3 ≤ coefficientBound)
    (hCarryLo : -CARRY_BIAS ≤ carry1) (hCarryHi : carry1 ≤ CARRY_BIAS)
    (hPair0 : (limbEq0 + 2 ^ 80 * limbEq1 - 2 ^ 160 * carry1) % (bn254FrModulus : Int) = 0)
    (hPair1 : (limbEq2 + carry1 + 2 ^ 80 * limbEq3) % (bn254FrModulus : Int) = 0)
    (hDecomp :
      limbEq0 + 2 ^ 80 * limbEq1 + 2 ^ 160 * limbEq2 + 2 ^ 240 * limbEq3 =
        lhs - qVal * (bn254FqModulus : Int)) :
    FqRelationHolds lhs :=
  (fq_relation_sound limbEq0 limbEq1 limbEq2 limbEq3 carry1 lhs qVal
    h0Lo h0Hi h1Lo h1Hi h2Lo h2Hi h3Lo h3Hi hCarryLo hCarryHi hPair0 hPair1 hDecomp).2

/-- **Non-Native `Fq` Addition Soundness (`fq_add_sound`)**:
If the linear `FqGadget::relation` $x + y - z \equiv 0 \pmod q$ holds and $z$ is canonical
($\text{evalLimbs}(z) < q$), then $(\text{evalLimbs}(x) + \text{evalLimbs}(y)) \bmod q = \text{evalLimbs}(z)$. -/
theorem fq_add_sound
    (x y z : FqLimbs)
    (hRel : FqRelationHolds (evalLimbsInt x + evalLimbsInt y - evalLimbsInt z))
    (hCanon : z.Canonical) :
    (evalLimbs x + evalLimbs y) % bn254FqModulus = evalLimbs z := by
  unfold FqRelationHolds evalLimbsInt FqLimbs.Canonical bn254FqModulus at *
  omega

/-- **Non-Native `Fq` Subtraction Soundness (`fq_sub_sound`)**:
If the linear `FqGadget::relation` $x - y - z \equiv 0 \pmod q$ holds and $z$ is canonical
($\text{evalLimbs}(z) < q$), then $(\text{evalLimbsInt}(x) - \text{evalLimbsInt}(y)) \bmod q = \text{evalLimbsInt}(z)$. -/
theorem fq_sub_sound
    (x y z : FqLimbs)
    (hRel : FqRelationHolds (evalLimbsInt x - evalLimbsInt y - evalLimbsInt z))
    (hCanon : z.Canonical) :
    (evalLimbsInt x - evalLimbsInt y) % (bn254FqModulus : Int) = evalLimbsInt z := by
  unfold FqRelationHolds evalLimbsInt FqLimbs.Canonical bn254FqModulus at *
  omega

/-- **Non-Native `Fq` Multiplication Soundness (`fq_mul_sound`)**:
If `FqGadget::mul` (`native_field.rs:305-309`) enforces $1 \cdot x \cdot y - 1 \cdot z \equiv 0 \pmod q$,
then $(\text{evalLimbs}(x) \cdot \text{evalLimbs}(y)) \bmod q = \text{evalLimbs}(z) \bmod q$,
and equals $\text{evalLimbs}(z)$ when $z$ is canonical. -/
theorem fq_mul_sound
    (x y z : FqLimbs)
    (hRel : FqRelationHolds (evalLimbsInt x * evalLimbsInt y - evalLimbsInt z)) :
    (evalLimbs x * evalLimbs y) % bn254FqModulus = evalLimbs z % bn254FqModulus := by
  unfold FqRelationHolds evalLimbsInt at hRel
  unfold bn254FqModulus at hRel ⊢
  have hCast : (evalLimbs x : Int) * (evalLimbs y : Int) = ↑(evalLimbs x * evalLimbs y) :=
    (Int.natCast_mul (evalLimbs x) (evalLimbs y)).symm
  rw [hCast] at hRel
  generalize evalLimbs x * evalLimbs y = xy at hRel ⊢
  omega

/-- **Non-Native `Fq` Inverse-or-Zero / Equality Flag Soundness (`fq_inv_or_zero_sound`)**:
In `equal_flag` (`native_curve.rs:152-168`), a boolean wire `flag ∈ {0, 1}` and witness
`inv : FqLimbs` are constrained by three `FqGadget::relation` calls:
1. $(lhs - rhs) \cdot inv + flag - 1 \equiv 0 \pmod q$
2. $(lhs - rhs) \cdot flag \equiv 0 \pmod q$
3. $inv \cdot flag \equiv 0 \pmod q$.
This theorem proves that:
- When `flag = 1`, `lhs ≡ rhs (mod q)` (and `evalLimbs lhs = evalLimbs rhs` if both are canonical)
  and `evalLimbs inv % q = 0`.
- When `flag = 0`, `((lhs - rhs) * inv) ≡ 1 (mod q)`, so `lhs ≢ rhs (mod q)`. -/
theorem fq_inv_or_zero_sound
    (lhs rhs inv : FqLimbs) (flag : Int)
    (hBool : flag = 0 ∨ flag = 1)
    (hRel1 : FqRelationHolds ((evalLimbsInt lhs - evalLimbsInt rhs) * evalLimbsInt inv + flag - 1))
    (hRel2 : FqRelationHolds ((evalLimbsInt lhs - evalLimbsInt rhs) * flag))
    (hRel3 : FqRelationHolds (evalLimbsInt inv * flag)) :
    (flag = 1 →
      (evalLimbsInt lhs - evalLimbsInt rhs) % (bn254FqModulus : Int) = 0 ∧
      evalLimbsInt inv % (bn254FqModulus : Int) = 0) ∧
    (flag = 0 →
      ((evalLimbsInt lhs - evalLimbsInt rhs) * evalLimbsInt inv - 1) % (bn254FqModulus : Int) = 0 ∧
      (evalLimbsInt lhs - evalLimbsInt rhs) % (bn254FqModulus : Int) ≠ 0) := by
  unfold FqRelationHolds at *
  refine ⟨?_, ?_⟩
  · intro hFlag
    subst hFlag
    simp only [Int.mul_one] at hRel2 hRel3
    exact ⟨hRel2, hRel3⟩
  · intro hFlag
    subst hFlag
    simp only [Int.add_zero] at hRel1
    refine ⟨hRel1, ?_⟩
    intro hDiffZero
    have hProdZero :
        ((evalLimbsInt lhs - evalLimbsInt rhs) * evalLimbsInt inv) % (bn254FqModulus : Int) = 0 := by
      rw [Int.mul_emod, hDiffZero, Int.zero_mul, Int.zero_emod]
    unfold bn254FqModulus at hRel1 hProdZero
    omega

/-- **Non-Native `Fq` Equality Soundness (`fq_equal_sound`)**:
If `FqGadget::equal` (`native_field.rs:310-312`) enforces $1 \cdot x - 1 \cdot y \equiv 0 \pmod q$,
then $\text{evalLimbs}(x) \bmod q = \text{evalLimbs}(y) \bmod q$, and if both $x$ and $y$ are
canonical ($< q$), then $\text{evalLimbs}(x) = \text{evalLimbs}(y)$. -/
theorem fq_equal_sound
    (x y : FqLimbs)
    (hRel : FqRelationHolds (evalLimbsInt x - evalLimbsInt y)) :
    evalLimbs x % bn254FqModulus = evalLimbs y % bn254FqModulus ∧
    (x.Canonical → y.Canonical → evalLimbs x = evalLimbs y) := by
  unfold FqRelationHolds evalLimbsInt FqLimbs.Canonical bn254FqModulus at *
  omega

/-- **Canonical Limb Subtraction Soundness (`fq_canonical_lt_q_sound`)**:
In `FqGadget::canonical` (`native_field.rs:160-202`), subtracting `v` limb-by-limb from
`p = fqModulusMinusOneLimbs` ($q - 1$) with 80-bit range-checked differences
`d0, d1, d2, d3 < 2^80`, boolean borrows `b0, b1, b2, b3 ∈ {0, 1}`, and final borrow
`b3 = 0` enforces:
$$(q - 1)_i - v_i - b_{i-1} + 2^{80} b_i - d_i = 0 \quad (i = 0, 1, 2, 3), \quad b_3 = 0.$$
Summing $2^{80 i}$ times these four equations telescopes the borrows $b_0, b_1, b_2$ and proves
$\text{evalLimbs}(v) + \text{evalLimbs}(d) = q - 1$, hence $\text{evalLimbs}(v) < q$ (`v.Canonical`). -/
theorem fq_canonical_lt_q_sound
    (v d : FqLimbs) (b0 b1 b2 b3 : Int)
    (hEq0 : (fqModulusMinusOneLimbs.l0 : Int) - v.l0 - 0 + 2 ^ 80 * b0 - d.l0 = 0)
    (hEq1 : (fqModulusMinusOneLimbs.l1 : Int) - v.l1 - b0 + 2 ^ 80 * b1 - d.l1 = 0)
    (hEq2 : (fqModulusMinusOneLimbs.l2 : Int) - v.l2 - b1 + 2 ^ 80 * b2 - d.l2 = 0)
    (hEq3 : (fqModulusMinusOneLimbs.l3 : Int) - v.l3 - b2 + 2 ^ 80 * b3 - d.l3 = 0)
    (hFinalBorrow : b3 = 0) :
    v.Canonical := by
  have hP := evalLimbs_fqModulusMinusOneLimbs
  unfold FqLimbs.Canonical evalLimbs fqModulusMinusOneLimbs bn254FqModulus at *
  omega

end Ix.Cert.Compression.NativeField
