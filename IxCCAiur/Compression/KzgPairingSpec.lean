import IxCCAiur.Compression.KzgWire
import IxCCAiur.Compression.PairingPure
import IxCCAiur.Compression.KzgPackedPure
import Ix.Cert.AiurCompression.StatementBinding
import Ix.Cert.AiurCompression.DeferredFold
import Ix.Cert.AiurCompression.OuterRelation
import IxCCAiur.CompressionIntrinsicsProof

/-! # Pure-Lean Mathematical Soundness of `KzgWire`, `PairingPure`, and `KzgPackedPure`

Pure functional Lean 4 soundness proofs connecting the executable single-source multi-curve
compression modules (`IxCCAiur/Compression/{KzgWire,PairingPure,KzgPackedPure}.lean`) directly
to the certification layer (`Ix.Cert.AiurCompression.{StatementBinding,DeferredFold,OuterRelation}`)
and certified multi-field compilation (`IxCC.AiurBackend.CompressionIntrinsicsProof.CompressionCert`):

1. **Non-Native `Fq`, Monus Predicates & Extension Tower ($\mathbb{F}_{q^2}, \mathbb{F}_{q^6}, \mathbb{F}_{q^{12}}$):**
   - Canonical `< q` bounds and exact `ZMod q` ring homomorphisms for `fqAddMod`, `fqSubMod`,
     `fqMulMod`, `fqNeg`, `fqNegMod`, and `fqInvMod`.
   - Exact equivalence between branchless monus error sums (`natAbsDiff`, `natLtErr`,
     `fp{2,6,12}Diff`, `fp{2,6,12}CanonErr`, `fp{2,6,12}Sum`) and equality/canonicality/zero.
   - Algebraic `CommRing` models `ZModFp2`, `ZModFp6`, `ZModFp12` proving soundness of Karatsuba
     multiplication, complex/CH-SQR2 squaring, sparse twist multiplications (`fp12MulBy034`,
     `fp12MulBy014`), tower inversion, and binary powering (`fp12Pow`).
2. **Curve Equation, Strict Infinity, Canonical Affine `u80` Codecs & BLS12-381 Bowe Subgroup Check:**
   - Exact curve equation $y^2 \equiv x^3 + b \pmod q$, strict point-at-infinity uniqueness,
     and canonical 4-limb (BN254, 18-word) and 5-limb (BLS12-381, 22-word) affine decoders bridged
     to `Ix.Cert.AiurCompression.{Bn254AffineU80Point,Bls12381AffineU80Point}`.
   - Exact soundness of inversion-free Jacobian doubling, addition, and MSB scalar multiplication
     into Mathlib's `(bls12381CurveAt bls12381FqModulus).Point`.
   - **Bowe 2019/814 prime-order `G1` subgroup soundness (`bls12381_g1Validate_prime_order`)**:
     acceptance of `PairingPure.g1Validate bls12381PairingParams P` implies canonical `< q`,
     on-curve membership, $[x^2] P = -\psi(P)$, and prime-order subgroup membership
     `bls12381FrModulus • P_aff = 0`, together with kernel-checked rejection of the concrete
     non-subgroup torsion witnesses.
3. **Optimal Ate Miller Loop & Residue-Witnessed Final Exponentiation Soundness:**
   - Exact equivalence between `millerLoop2Prepared` (on `precomputeG2Lines`) and `millerLoop2`,
     infinity preservation, and canonical output bounds.
   - Exact algebraic final-exponentiation soundness for unitary (`verifyFinalExpWitness`),
     $\mathbb{F}_{q^6}^*$-scaled (`verifyFinalExpWitnessFp6`), and BN254 fixed $d=3$ table
     (`verifyFinalExpTableBN254`) verifiers on both BN254 and BLS12-381, proving
     $f^{(q^{12}-1)/r} = 1$ in $\mathbb{F}_{q^{12}}^*$.
4. **Canonical Wire Decoding, Universal Trailing-Byte Rejection & Key-Bound Transcript Soundness:**
   - Exact canonical decoding and universal trailing-byte rejection for `IXAUCL01`, `IXAUKG01`,
     `IXPSHC02`, `IXAUSK02`, and `IXAUSP01`, plus `g1FromBytes` canonicality and injectivity.
   - Key-binding transcript soundness matching `crates/proof-compression/src/kzg/config.rs` and
     `packed_shplonk/config.rs`: `KzgPackedPure.verifyPacked` binds both `vk_digest` and every
     validated `PackedFixed` commitment point into the Fiat-Shamir transcript seed.
5. **Packed SHPLONK Opening, 4-Bit Windowed MSM & Deferred Accumulator Fold Soundness:**
   - Exact soundness of 4-bit windowed Straus `g1Msm` across both 254-bit BN254 `Fr` and
     255-bit BLS12-381 `Fr`.
   - Exact BDFG SHPLONK opening reduction equations (`verifyPacked_shplonk_sound`) and two-stage
     deferred fold composition (`stepV1` + `verifyAccumulatorV1`) bridged directly to
     `Ix.Cert.AiurCompression.{bn254_l3_deferred_fold_sound,bls12381_l3_deferred_fold_sound}`.
6. **End-to-End Composition with `CompressionIntrinsicsProof.CompressionCert`:**
   - Composes `compressionCert_assertOk_{bn254,bls12381}` and
     `compressionCert_witness_{bn254,bls12381}` with `PairingPure` and `KzgPackedPure` soundness.

Strictly pure Lean 4, total, zero `sorry`, zero `admit`, zero custom `axiom`, zero `native_decide`,
zero `bv_decide`, strictly `⊆ [propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

namespace IxCCAiur.Compression.KzgPairingSpec

open KzgWire PairingPure KzgPackedPure
open Ix.Cert.Compression.Foreign
open Ix.Cert.Compression.NativeField
open Ix.Cert.Compression.OuterRelation
open Ix.Cert.Compression.Bls12381.Field
open Ix.Cert.Compression.Bls12381.OuterRelation
open Ix.Cert.AiurCompression
open IxCC.AiurBackend.CompressionIntrinsicsProof

/-! ## Section 1: Non-Native `Fq` Modular Arithmetic, Monus Predicates & Extension Tower -/

section FqAndMonus

/-! ### 1.1 Canonical Bounds & `ZMod q` Homomorphisms for `Fq` & `Fr` Ops -/

theorem fqAddMod_lt {q : Nat} (hq : 0 < q) (a b : Nat) : fqAddMod q a b < q :=
  Nat.mod_lt _ hq

theorem fqSubMod_lt {q : Nat} (hq : 0 < q) (a b : Nat) : fqSubMod q a b < q :=
  Nat.mod_lt _ hq

theorem fqMulMod_lt {q : Nat} (hq : 0 < q) (a b : Nat) : fqMulMod q a b < q :=
  Nat.mod_lt _ hq

theorem fqNeg_lt {q : Nat} (hq : 0 < q) (a : Nat) : fqNeg q a < q :=
  Nat.mod_lt _ hq

theorem fqNegMod_lt {q : Nat} (hq : 0 < q) {a : Nat} (ha : a < q) : fqNegMod q a < q := by
  unfold fqNegMod
  split_ifs with h
  · exact hq
  · have hne : a ≠ 0 := by
      intro hz; subst hz; simp at h
    omega

theorem fqAddMod_cast (q a b : Nat) :
    ((fqAddMod q a b : Nat) : ZMod q) = (a : ZMod q) + (b : ZMod q) := by
  unfold fqAddMod
  rw [ZMod.natCast_mod, Nat.cast_add, add_comm]

theorem fqSubMod_cast {q a b : Nat} (hb : b ≤ q) :
    ((fqSubMod q a b : Nat) : ZMod q) = (a : ZMod q) - (b : ZMod q) := by
  unfold fqSubMod
  rw [ZMod.natCast_mod]
  have hle : b ≤ q + a := by omega
  rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, zero_add]

theorem fqMulMod_cast (q a b : Nat) :
    ((fqMulMod q a b : Nat) : ZMod q) = (a : ZMod q) * (b : ZMod q) := by
  unfold fqMulMod
  rw [ZMod.natCast_mod, Nat.cast_mul, mul_comm]

theorem fqNeg_cast {q a : Nat} (ha : a ≤ q) :
    ((fqNeg q a : Nat) : ZMod q) = -(a : ZMod q) := by
  unfold fqNeg
  rw [fqSubMod_cast ha, Nat.cast_zero, zero_sub]

theorem fqNegMod_cast {q a : Nat} (ha : a ≤ q) :
    ((fqNegMod q a : Nat) : ZMod q) = -(a : ZMod q) := by
  unfold fqNegMod
  by_cases h0 : a = 0
  · subst h0; simp
  · have hb : (0 == a) = false := beq_false_of_ne (Ne.symm h0)
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]

theorem fqNeg_eq_fqNegMod {q a : Nat} (ha : a < q) :
    fqNeg q a = fqNegMod q a := by
  unfold fqNeg fqSubMod fqNegMod
  by_cases h0 : a = 0
  · subst h0; simp
  · have hb : (0 == a) = false := beq_false_of_ne (Ne.symm h0)
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)

theorem fqInvMod_lt {q : Nat} [Fact (Nat.Prime q)] (hqMax : q < maxFieldModulus) (a : Nat) :
    fqInvMod q a < q := by
  have hp : Nat.Prime q := Fact.out
  have hq2 : 2 ≤ q := hp.two_le
  by_cases ha0 : a % q = 0
  · unfold fqInvMod
    have hnot2 : ¬ q < 2 := by omega
    simp [hnot2, ha0, hp.pos]
  · have hcop : Nat.gcd q a = 1 := by
      have hndvd : ¬ q ∣ a := fun hd => ha0 (Nat.mod_eq_zero_of_dvd hd)
      exact hp.coprime_iff_not_dvd.mpr hndvd
    have hchk := fqInvMod_complete_of_coprime q a hq2 hqMax hcop
    unfold fqInvMod.check at hchk
    have hnot2 : ¬ q < 2 := by omega
    have ha0b : (a % q == 0) = false := beq_false_of_ne ha0
    simp only [hnot2, ↓reduceIte, ha0b, Bool.false_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, beq_iff_eq] at hchk
    exact hchk.1.2

theorem fqInvMod_mul_cast {q : Nat} [Fact (Nat.Prime q)] (hqMax : q < maxFieldModulus)
    {a : Nat} (ha : (a : ZMod q) ≠ 0) :
    (a : ZMod q) * ((fqInvMod q a : Nat) : ZMod q) = 1 := by
  have hp : Nat.Prime q := Fact.out
  have hq2 : 2 ≤ q := hp.two_le
  have ha0 : a % q ≠ 0 := by
    intro hm
    apply ha
    rw [← ZMod.natCast_mod, hm, Nat.cast_zero]
  have hcop : Nat.gcd q a = 1 :=
    hp.coprime_iff_not_dvd.mpr fun hd => ha0 (Nat.mod_eq_zero_of_dvd hd)
  have hchk := fqInvMod_complete_of_coprime q a hq2 hqMax hcop
  unfold fqInvMod.check at hchk
  have hnot2 : ¬ q < 2 := by omega
  have ha0b : (a % q == 0) = false := beq_false_of_ne ha0
  simp only [hnot2, ↓reduceIte, ha0b, Bool.false_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hchk
  have hmul : ((a * fqInvMod q a : Nat) : ZMod q) = ((1 : Nat) : ZMod q) := by
    rw [← ZMod.natCast_mod, hchk.2]
  simpa [Nat.cast_mul] using hmul

theorem fqInvMod_cast_eq_inv {q : Nat} [Fact (Nat.Prime q)] (hqMax : q < maxFieldModulus)
    (a : Nat) :
    ((fqInvMod q a : Nat) : ZMod q) = (a : ZMod q)⁻¹ := by
  by_cases ha : (a : ZMod q) = 0
  · have hmod : a % q = 0 := by
      have hdvd : q ∣ a := (ZMod.natCast_eq_zero_iff a q).mp ha
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hq2 : ¬ q < 2 := by have := (Fact.out : Nat.Prime q).two_le; omega
    unfold fqInvMod
    simp [hq2, hmod, ha]
  · have hmul := fqInvMod_mul_cast hqMax ha
    exact (inv_eq_of_mul_eq_one_right hmul).symm

theorem frAdd_lt {p : Nat} (hp : 0 < p) (a b : Nat) : frAdd p a b < p := Nat.mod_lt _ hp
theorem frSub_lt {p : Nat} (hp : 0 < p) (a b : Nat) : frSub p a b < p := Nat.mod_lt _ hp
theorem frMul_lt {p : Nat} (hp : 0 < p) (a b : Nat) : frMul p a b < p := Nat.mod_lt _ hp

theorem frAdd_cast (p a b : Nat) :
    ((frAdd p a b : Nat) : ZMod p) = (a : ZMod p) + (b : ZMod p) := by
  unfold frAdd; rw [ZMod.natCast_mod, Nat.cast_add]

theorem frSub_cast {p a b : Nat} (hb : b ≤ p) :
    ((frSub p a b : Nat) : ZMod p) = (a : ZMod p) - (b : ZMod p) := by
  unfold frSub
  rw [ZMod.natCast_mod]
  have hle : b ≤ a + p := by omega
  rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero]

theorem frMul_cast (p a b : Nat) :
    ((frMul p a b : Nat) : ZMod p) = (a : ZMod p) * (b : ZMod p) := by
  unfold frMul; rw [ZMod.natCast_mod, Nat.cast_mul]

theorem frNeg_cast {p a : Nat} (ha : a ≤ p) :
    ((frNeg p a : Nat) : ZMod p) = -(a : ZMod p) := by
  unfold frNeg
  by_cases h0 : a = 0
  · subst h0; simp
  · have hb : (a == 0) = false := beq_false_of_ne h0
    rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]

theorem frIsZero_eq_one_iff (a : Nat) : frIsZero a = 1 ↔ a = 0 := by
  unfold frIsZero; by_cases h : a = 0 <;> simp [h]

theorem frIsZero_eq_zero_iff (a : Nat) : frIsZero a = 0 ↔ a ≠ 0 := by
  unfold frIsZero; by_cases h : a = 0 <;> simp [h]

theorem frEq_eq_one_iff (a b : Nat) : frEq a b = 1 ↔ a = b := by
  unfold frEq; by_cases h : a = b <;> simp [h]

/-! ### 1.2 Branchless Monus Predicates & Flat Error Sums -/

theorem natAbsDiff_eq_zero_iff (a b : Nat) : natAbsDiff a b = 0 ↔ a = b := by
  unfold natAbsDiff; omega

theorem natLtErr_eq_zero_iff (a bound : Nat) : natLtErr a bound = 0 ↔ a < bound := by
  unfold natLtErr; omega

theorem fp2Sum_eq_zero_iff (a : Fp2) : fp2Sum a = 0 ↔ a = fp2Zero := by
  cases a; unfold fp2Sum fp2Zero; simp only [Fp2.mk.injEq]; omega

theorem fp2IsZero_iff (a : Fp2) : fp2IsZero a = true ↔ a = fp2Zero := by
  unfold fp2IsZero; simp [fp2Sum_eq_zero_iff]

theorem fp2IsOne_iff (a : Fp2) : fp2IsOne a = true ↔ a = fp2One := by
  cases a; unfold fp2IsOne fp2One natAbsDiff; simp only [beq_iff_eq, Fp2.mk.injEq]; omega

theorem fp2Diff_eq_zero_iff (a b : Fp2) : fp2Diff a b = 0 ↔ a = b := by
  cases a; cases b; unfold fp2Diff natAbsDiff; simp only [Fp2.mk.injEq]; omega

theorem fp2Eq_iff (a b : Fp2) : fp2Eq a b = true ↔ a = b := by
  unfold fp2Eq; simp [fp2Diff_eq_zero_iff]

theorem fp2CanonErr_eq_zero_iff (q : Nat) (a : Fp2) :
    fp2CanonErr q a = 0 ↔ a.c0 < q ∧ a.c1 < q := by
  cases a; unfold fp2CanonErr natLtErr; dsimp only; omega

theorem fp2Canonical_iff (q : Nat) (a : Fp2) :
    fp2Canonical q a = true ↔ a.c0 < q ∧ a.c1 < q := by
  unfold fp2Canonical; simp [fp2CanonErr_eq_zero_iff]

theorem fp6Sum_eq_zero_iff (a : Fp6) : fp6Sum a = 0 ↔ a = fp6Zero := by
  cases a with
  | mk c0 c1 c2 =>
    unfold fp6Sum fp6Zero
    simp only [Fp6.mk.injEq]
    constructor
    · intro h
      have h0 : fp2Sum c0 = 0 := by omega
      have h1 : fp2Sum c1 = 0 := by omega
      have h2 : fp2Sum c2 = 0 := by omega
      exact ⟨(fp2Sum_eq_zero_iff c0).mp h0, (fp2Sum_eq_zero_iff c1).mp h1,
        (fp2Sum_eq_zero_iff c2).mp h2⟩
    · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem fp6IsZero_iff (a : Fp6) : fp6IsZero a = true ↔ a = fp6Zero := by
  unfold fp6IsZero; simp [fp6Sum_eq_zero_iff]

theorem fp6Diff_eq_zero_iff (a b : Fp6) : fp6Diff a b = 0 ↔ a = b := by
  cases a with
  | mk a0 a1 a2 =>
    cases b with
    | mk b0 b1 b2 =>
      unfold fp6Diff
      simp only [Fp6.mk.injEq]
      constructor
      · intro h
        exact ⟨(fp2Diff_eq_zero_iff a0 b0).mp (by omega),
          (fp2Diff_eq_zero_iff a1 b1).mp (by omega),
          (fp2Diff_eq_zero_iff a2 b2).mp (by omega)⟩
      · rintro ⟨rfl, rfl, rfl⟩
        simp [(fp2Diff_eq_zero_iff _ _).mpr rfl]

theorem fp6Eq_iff (a b : Fp6) : fp6Eq a b = true ↔ a = b := by
  unfold fp6Eq; simp [fp6Diff_eq_zero_iff]

theorem fp6CanonErr_eq_zero_iff (q : Nat) (a : Fp6) :
    fp6CanonErr q a = 0 ↔
      fp2Canonical q a.c0 = true ∧ fp2Canonical q a.c1 = true ∧ fp2Canonical q a.c2 = true := by
  cases a with
  | mk c0 c1 c2 =>
    unfold fp6CanonErr fp2Canonical
    simp only [beq_iff_eq]
    omega

theorem fp6Canonical_iff (q : Nat) (a : Fp6) :
    fp6Canonical q a = true ↔
      fp2Canonical q a.c0 = true ∧ fp2Canonical q a.c1 = true ∧ fp2Canonical q a.c2 = true := by
  unfold fp6Canonical; simp [fp6CanonErr_eq_zero_iff]

theorem fp12Sum_eq_zero_iff (a : Fp12) : fp12Sum a = 0 ↔ a = fp12Zero := by
  cases a with
  | mk c0 c1 =>
    unfold fp12Sum fp12Zero
    simp only [Fp12.mk.injEq]
    constructor
    · intro h
      exact ⟨(fp6Sum_eq_zero_iff c0).mp (by omega), (fp6Sum_eq_zero_iff c1).mp (by omega)⟩
    · rintro ⟨rfl, rfl⟩; rfl

theorem fp12IsZero_iff (a : Fp12) : fp12IsZero a = true ↔ a = fp12Zero := by
  unfold fp12IsZero; simp [fp12Sum_eq_zero_iff]

theorem fp12Diff_eq_zero_iff (a b : Fp12) : fp12Diff a b = 0 ↔ a = b := by
  cases a with
  | mk a0 a1 =>
    cases b with
    | mk b0 b1 =>
      unfold fp12Diff
      simp only [Fp12.mk.injEq]
      constructor
      · intro h
        exact ⟨(fp6Diff_eq_zero_iff a0 b0).mp (by omega),
          (fp6Diff_eq_zero_iff a1 b1).mp (by omega)⟩
      · rintro ⟨rfl, rfl⟩
        simp [(fp6Diff_eq_zero_iff _ _).mpr rfl]

theorem fp12Eq_iff (a b : Fp12) : fp12Eq a b = true ↔ a = b := by
  unfold fp12Eq; simp [fp12Diff_eq_zero_iff]

theorem fp12CanonErr_eq_zero_iff (q : Nat) (a : Fp12) :
    fp12CanonErr q a = 0 ↔ fp6Canonical q a.c0 = true ∧ fp6Canonical q a.c1 = true := by
  cases a with
  | mk c0 c1 =>
    unfold fp12CanonErr fp6Canonical
    simp only [beq_iff_eq]
    omega

theorem fp12Canonical_iff (q : Nat) (a : Fp12) :
    fp12Canonical q a = true ↔ fp6Canonical q a.c0 = true ∧ fp6Canonical q a.c1 = true := by
  unfold fp12Canonical; simp [fp12CanonErr_eq_zero_iff]

/-! ### 1.3 Algebraic Ring Models `ZModFp2`, `ZModFp6`, `ZModFp12` & Tower Soundness -/

/-- Exact quadratic extension ring `ZMod q[u] / (u² + 1)`. -/
@[ext]
structure ZModFp2 (q : Nat) where
  c0 : ZMod q
  c1 : ZMod q
  deriving DecidableEq

namespace ZModFp2

def zero (q : Nat) : ZModFp2 q := ⟨0, 0⟩
def one (q : Nat) : ZModFp2 q := ⟨1, 0⟩
def add {q : Nat} (a b : ZModFp2 q) : ZModFp2 q := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
def sub {q : Nat} (a b : ZModFp2 q) : ZModFp2 q := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
def neg {q : Nat} (a : ZModFp2 q) : ZModFp2 q := ⟨-a.c0, -a.c1⟩
def conj {q : Nat} (a : ZModFp2 q) : ZModFp2 q := ⟨a.c0, -a.c1⟩
def mul {q : Nat} (a b : ZModFp2 q) : ZModFp2 q :=
  ⟨a.c0 * b.c0 - a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩
def xi (q xi0 : Nat) : ZModFp2 q := ⟨(xi0 : ZMod q), 1⟩

instance (q : Nat) : Zero (ZModFp2 q) := ⟨zero q⟩
instance (q : Nat) : One (ZModFp2 q) := ⟨one q⟩
instance (q : Nat) : Add (ZModFp2 q) := ⟨add⟩
instance (q : Nat) : Sub (ZModFp2 q) := ⟨sub⟩
instance (q : Nat) : Neg (ZModFp2 q) := ⟨neg⟩
instance (q : Nat) : Mul (ZModFp2 q) := ⟨mul⟩

@[simp] theorem zero_c0 (q : Nat) : (0 : ZModFp2 q).c0 = 0 := rfl
@[simp] theorem zero_c1 (q : Nat) : (0 : ZModFp2 q).c1 = 0 := rfl
@[simp] theorem one_c0 (q : Nat) : (1 : ZModFp2 q).c0 = 1 := rfl
@[simp] theorem one_c1 (q : Nat) : (1 : ZModFp2 q).c1 = 0 := rfl
@[simp] theorem add_c0 {q : Nat} (a b : ZModFp2 q) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 {q : Nat} (a b : ZModFp2 q) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 {q : Nat} (a b : ZModFp2 q) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 {q : Nat} (a b : ZModFp2 q) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 {q : Nat} (a : ZModFp2 q) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 {q : Nat} (a : ZModFp2 q) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 {q : Nat} (a b : ZModFp2 q) : (a * b).c0 = a.c0 * b.c0 - a.c1 * b.c1 := rfl
@[simp] theorem mul_c1 {q : Nat} (a b : ZModFp2 q) : (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

instance (q : Nat) : CommRing (ZModFp2 q) where
  add_assoc a b c := by apply ZModFp2.ext <;> simp [add_assoc]
  zero_add a := by apply ZModFp2.ext <;> simp
  add_zero a := by apply ZModFp2.ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by apply ZModFp2.ext <;> simp [add_comm]
  zsmul := zsmulRec
  neg_add_cancel a := by apply ZModFp2.ext <;> simp
  sub_eq_add_neg a b := by apply ZModFp2.ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by apply ZModFp2.ext <;> simp <;> ring
  one_mul a := by apply ZModFp2.ext <;> simp
  mul_one a := by apply ZModFp2.ext <;> simp
  left_distrib a b c := by apply ZModFp2.ext <;> simp <;> ring
  right_distrib a b c := by apply ZModFp2.ext <;> simp <;> ring
  zero_mul a := by apply ZModFp2.ext <;> simp
  mul_zero a := by apply ZModFp2.ext <;> simp
  mul_comm a b := by apply ZModFp2.ext <;> simp <;> ring

end ZModFp2

/-- Canonical projection from executable `Fp2` to `ZModFp2 q`. -/
def fp2ToZMod (q : Nat) (a : Fp2) : ZModFp2 q :=
  ⟨(a.c0 : ZMod q), (a.c1 : ZMod q)⟩

theorem fp2ToZMod_inj {q : Nat} [NeZero q] {a b : Fp2}
    (ha : fp2Canonical q a = true) (hb : fp2Canonical q b = true)
    (heq : fp2ToZMod q a = fp2ToZMod q b) : a = b := by
  rw [fp2Canonical_iff] at ha hb
  have h0 := congrArg (fun x : ZModFp2 q => x.c0.val) heq
  have h1 := congrArg (fun x : ZModFp2 q => x.c1.val) heq
  simp only [fp2ToZMod, ZMod.val_natCast_of_lt ha.1, ZMod.val_natCast_of_lt ha.2,
    ZMod.val_natCast_of_lt hb.1, ZMod.val_natCast_of_lt hb.2] at h0 h1
  cases a; cases b; simp_all

theorem fp2Add_canonical {q : Nat} (hq : 0 < q) (a b : Fp2) :
    fp2Canonical q (fp2Add q a b) = true := by
  rw [fp2Canonical_iff]; exact ⟨fqAddMod_lt hq _ _, fqAddMod_lt hq _ _⟩

theorem fp2Sub_canonical {q : Nat} (hq : 0 < q) (a b : Fp2) :
    fp2Canonical q (fp2Sub q a b) = true := by
  rw [fp2Canonical_iff]; exact ⟨fqSubMod_lt hq _ _, fqSubMod_lt hq _ _⟩

theorem fp2Neg_canonical {q : Nat} (hq : 0 < q) (a : Fp2) :
    fp2Canonical q (fp2Neg q a) = true := by
  rw [fp2Canonical_iff]; exact ⟨fqNeg_lt hq _, fqNeg_lt hq _⟩

theorem fp2Conj_canonical {q : Nat} (hq : 0 < q) {a : Fp2} (ha : fp2Canonical q a = true) :
    fp2Canonical q (fp2Conj q a) = true := by
  rw [fp2Canonical_iff] at ha ⊢; exact ⟨ha.1, fqNeg_lt hq _⟩

theorem fp2MulByFq_canonical {q : Nat} (hq : 0 < q) (a : Fp2) (s : Nat) :
    fp2Canonical q (fp2MulByFq q a s) = true := by
  rw [fp2Canonical_iff]; exact ⟨fqMulMod_lt hq _ _, fqMulMod_lt hq _ _⟩

theorem fp2Mul_canonical {q : Nat} (hq : 0 < q) (a b : Fp2) :
    fp2Canonical q (fp2Mul q a b) = true := by
  rw [fp2Canonical_iff]; exact ⟨fqSubMod_lt hq _ _, fqSubMod_lt hq _ _⟩

theorem fp2Sqr_canonical {q : Nat} (hq : 0 < q) (a : Fp2) :
    fp2Canonical q (fp2Sqr q a) = true := by
  rw [fp2Canonical_iff]; exact ⟨fqMulMod_lt hq _ _, fqAddMod_lt hq _ _⟩

theorem fp2MulByNonResidue_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp2) :
    fp2Canonical q (fp2MulByNonResidue q xi0 a) = true := by
  rw [fp2Canonical_iff]; exact ⟨fqSubMod_lt hq _ _, fqAddMod_lt hq _ _⟩

theorem fp2ToZMod_zero (q : Nat) : fp2ToZMod q fp2Zero = 0 := by
  apply ZModFp2.ext <;> simp [fp2ToZMod, fp2Zero]

theorem fp2ToZMod_one (q : Nat) : fp2ToZMod q fp2One = 1 := by
  apply ZModFp2.ext <;> simp [fp2ToZMod, fp2One]

theorem fp2Add_hom (q : Nat) (a b : Fp2) :
    fp2ToZMod q (fp2Add q a b) = fp2ToZMod q a + fp2ToZMod q b := by
  apply ZModFp2.ext <;> simp [fp2ToZMod, fp2Add, fqAddMod_cast]

theorem fp2Sub_hom {q : Nat} {a b : Fp2} (hb : fp2Canonical q b = true) :
    fp2ToZMod q (fp2Sub q a b) = fp2ToZMod q a - fp2ToZMod q b := by
  rw [fp2Canonical_iff] at hb
  apply ZModFp2.ext
  · exact fqSubMod_cast (Nat.le_of_lt hb.1)
  · exact fqSubMod_cast (Nat.le_of_lt hb.2)

theorem fp2Neg_hom {q : Nat} {a : Fp2} (ha : fp2Canonical q a = true) :
    fp2ToZMod q (fp2Neg q a) = -fp2ToZMod q a := by
  rw [fp2Canonical_iff] at ha
  apply ZModFp2.ext
  · exact fqNeg_cast (Nat.le_of_lt ha.1)
  · exact fqNeg_cast (Nat.le_of_lt ha.2)

theorem fp2Conj_hom {q : Nat} {a : Fp2} (ha : fp2Canonical q a = true) :
    fp2ToZMod q (fp2Conj q a) = ZModFp2.conj (fp2ToZMod q a) := by
  rw [fp2Canonical_iff] at ha
  apply ZModFp2.ext
  · rfl
  · exact fqNeg_cast (Nat.le_of_lt ha.2)

theorem fp2MulByFq_hom (q : Nat) (a : Fp2) (s : Nat) :
    fp2ToZMod q (fp2MulByFq q a s) = fp2ToZMod q a * ⟨(s : ZMod q), 0⟩ := by
  apply ZModFp2.ext <;> simp [fp2ToZMod, fp2MulByFq, fqMulMod_cast]

/-- Exact soundness of Karatsuba `fp2Mul` against schoolbook multiplication in `ZMod q[u]/(u²+1)`. -/
theorem fp2Mul_hom {q : Nat} (hq : 0 < q) (a b : Fp2) :
    fp2ToZMod q (fp2Mul q a b) = fp2ToZMod q a * fp2ToZMod q b := by
  have hv0 : fqMulMod q a.c0 b.c0 ≤ q := Nat.le_of_lt (fqMulMod_lt hq _ _)
  have hv1 : fqMulMod q a.c1 b.c1 ≤ q := Nat.le_of_lt (fqMulMod_lt hq _ _)
  ext
  · show ((fqSubMod q (fqMulMod q a.c0 b.c0) (fqMulMod q a.c1 b.c1) : Nat) : ZMod q) = _
    rw [fqSubMod_cast hv1, fqMulMod_cast, fqMulMod_cast]
    rfl
  · show ((fqSubMod q (fqSubMod q (fqMulMod q (fqAddMod q a.c0 a.c1) (fqAddMod q b.c0 b.c1))
        (fqMulMod q a.c0 b.c0)) (fqMulMod q a.c1 b.c1) : Nat) : ZMod q) = _
    rw [fqSubMod_cast hv1, fqSubMod_cast hv0, fqMulMod_cast, fqAddMod_cast, fqAddMod_cast,
      fqMulMod_cast, fqMulMod_cast]
    show ((a.c0 : ZMod q) + a.c1) * ((b.c0 : ZMod q) + b.c1) - a.c0 * b.c0 - a.c1 * b.c1 =
      a.c0 * b.c1 + a.c1 * b.c0
    ring

/-- Exact soundness of complex squaring `fp2Sqr` against `a * a` in `ZModFp2 q`. -/
theorem fp2Sqr_hom {q : Nat} {a : Fp2} (ha : fp2Canonical q a = true) :
    fp2ToZMod q (fp2Sqr q a) = fp2ToZMod q a * fp2ToZMod q a := by
  rw [fp2Canonical_iff] at ha
  ext
  · show ((fqMulMod q (fqAddMod q a.c0 a.c1) (fqSubMod q a.c0 a.c1) : Nat) : ZMod q) = _
    rw [fqMulMod_cast, fqAddMod_cast, fqSubMod_cast (Nat.le_of_lt ha.2)]
    show ((a.c0 : ZMod q) + a.c1) * ((a.c0 : ZMod q) - a.c1) = a.c0 * a.c0 - a.c1 * a.c1
    ring
  · show ((fqAddMod q (fqMulMod q a.c0 a.c1) (fqMulMod q a.c0 a.c1) : Nat) : ZMod q) = _
    rw [fqAddMod_cast, fqMulMod_cast]
    show (a.c0 : ZMod q) * a.c1 + a.c0 * a.c1 = a.c0 * a.c1 + a.c1 * a.c0
    ring

/-- Exact soundness of `fp2MulByNonResidue` against multiplication by `ξ = xi0 + u`. -/
theorem fp2MulByNonResidue_hom {q : Nat} (xi0 : Nat) {a : Fp2} (ha : fp2Canonical q a = true) :
    fp2ToZMod q (fp2MulByNonResidue q xi0 a) = fp2ToZMod q a * ZModFp2.xi q xi0 := by
  rw [fp2Canonical_iff] at ha
  ext
  · show ((fqSubMod q (fqMulMod q a.c0 xi0) a.c1 : Nat) : ZMod q) = _
    rw [fqSubMod_cast (Nat.le_of_lt ha.2), fqMulMod_cast]
    show (a.c0 : ZMod q) * xi0 - a.c1 = a.c0 * xi0 - a.c1 * 1
    ring
  · show ((fqAddMod q a.c0 (fqMulMod q a.c1 xi0) : Nat) : ZMod q) = _
    rw [fqAddMod_cast, fqMulMod_cast]
    show (a.c0 : ZMod q) + a.c1 * xi0 = a.c0 * 1 + a.c1 * xi0
    ring

/-- Soundness of `fp2Inv`: whenever the $\mathbb{F}_{q^2}$ norm $a_0^2 + a_1^2 \neq 0 \pmod q$
for prime $q < 2^{384}$, `a * fp2Inv q a = 1` in `ZModFp2 q`. -/
theorem fp2Inv_sound {q : Nat} [Fact (Nat.Prime q)] (hqMax : q < maxFieldModulus)
    (a : Fp2) (hnorm : (a.c0 : ZMod q) ^ 2 + (a.c1 : ZMod q) ^ 2 ≠ 0) :
    fp2ToZMod q a * fp2ToZMod q (fp2Inv q a) = 1 := by
  have hq : 0 < q := (Fact.out : Nat.Prime q).pos
  have hnormCast :
      ((fqAddMod q (fqMulMod q a.c0 a.c0) (fqMulMod q a.c1 a.c1) : Nat) : ZMod q) =
        (a.c0 : ZMod q) ^ 2 + (a.c1 : ZMod q) ^ 2 := by
    rw [fqAddMod_cast, fqMulMod_cast, fqMulMod_cast]; ring
  have hnormNe : ((fqAddMod q (fqMulMod q a.c0 a.c0) (fqMulMod q a.c1 a.c1) : Nat) : ZMod q) ≠ 0 := by
    rwa [hnormCast]
  have hinv := fqInvMod_mul_cast hqMax hnormNe
  rw [hnormCast] at hinv
  have hm1 : fqMulMod q a.c1 (fqInvMod q (fqAddMod q (fqMulMod q a.c0 a.c0) (fqMulMod q a.c1 a.c1))) ≤ q :=
    Nat.le_of_lt (fqMulMod_lt hq _ _)
  set invN : ZMod q :=
    ((fqInvMod q (fqAddMod q (fqMulMod q a.c0 a.c0) (fqMulMod q a.c1 a.c1)) : Nat) : ZMod q)
  ext
  · show (a.c0 : ZMod q) * ((fqMulMod q a.c0 _ : Nat) : ZMod q) -
        (a.c1 : ZMod q) * ((fqNeg q (fqMulMod q a.c1 _) : Nat) : ZMod q) = 1
    rw [fqMulMod_cast, fqNeg_cast hm1, fqMulMod_cast]
    linear_combination hinv
  · show (a.c0 : ZMod q) * ((fqNeg q (fqMulMod q a.c1 _) : Nat) : ZMod q) +
        (a.c1 : ZMod q) * ((fqMulMod q a.c0 _ : Nat) : ZMod q) = 0
    rw [fqMulMod_cast, fqNeg_cast hm1, fqMulMod_cast]
    ring

/-- Exact cubic extension ring `ZModFp2 q[v] / (v³ - ξ)`. -/
@[ext]
structure ZModFp6 (q xi0 : Nat) where
  c0 : ZModFp2 q
  c1 : ZModFp2 q
  c2 : ZModFp2 q
  deriving DecidableEq

namespace ZModFp6

def zero (q xi0 : Nat) : ZModFp6 q xi0 := ⟨0, 0, 0⟩
def one (q xi0 : Nat) : ZModFp6 q xi0 := ⟨1, 0, 0⟩
def add {q xi0 : Nat} (a b : ZModFp6 q xi0) : ZModFp6 q xi0 :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2⟩
def sub {q xi0 : Nat} (a b : ZModFp6 q xi0) : ZModFp6 q xi0 :=
  ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2⟩
def neg {q xi0 : Nat} (a : ZModFp6 q xi0) : ZModFp6 q xi0 :=
  ⟨-a.c0, -a.c1, -a.c2⟩
def mulV {q xi0 : Nat} (a : ZModFp6 q xi0) : ZModFp6 q xi0 :=
  ⟨a.c2 * ZModFp2.xi q xi0, a.c0, a.c1⟩
def mul {q xi0 : Nat} (a b : ZModFp6 q xi0) : ZModFp6 q xi0 :=
  ⟨a.c0 * b.c0 + (a.c1 * b.c2 + a.c2 * b.c1) * ZModFp2.xi q xi0,
   a.c0 * b.c1 + a.c1 * b.c0 + a.c2 * b.c2 * ZModFp2.xi q xi0,
   a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0⟩

instance (q xi0 : Nat) : Zero (ZModFp6 q xi0) := ⟨zero q xi0⟩
instance (q xi0 : Nat) : One (ZModFp6 q xi0) := ⟨one q xi0⟩
instance (q xi0 : Nat) : Add (ZModFp6 q xi0) := ⟨add⟩
instance (q xi0 : Nat) : Sub (ZModFp6 q xi0) := ⟨sub⟩
instance (q xi0 : Nat) : Neg (ZModFp6 q xi0) := ⟨neg⟩
instance (q xi0 : Nat) : Mul (ZModFp6 q xi0) := ⟨mul⟩

@[simp] theorem zero_c0 (q xi0 : Nat) : (0 : ZModFp6 q xi0).c0 = 0 := rfl
@[simp] theorem zero_c1 (q xi0 : Nat) : (0 : ZModFp6 q xi0).c1 = 0 := rfl
@[simp] theorem zero_c2 (q xi0 : Nat) : (0 : ZModFp6 q xi0).c2 = 0 := rfl
@[simp] theorem one_c0 (q xi0 : Nat) : (1 : ZModFp6 q xi0).c0 = 1 := rfl
@[simp] theorem one_c1 (q xi0 : Nat) : (1 : ZModFp6 q xi0).c1 = 0 := rfl
@[simp] theorem one_c2 (q xi0 : Nat) : (1 : ZModFp6 q xi0).c2 = 0 := rfl
@[simp] theorem add_c0 {q xi0 : Nat} (a b : ZModFp6 q xi0) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 {q xi0 : Nat} (a b : ZModFp6 q xi0) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 {q xi0 : Nat} (a b : ZModFp6 q xi0) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem sub_c0 {q xi0 : Nat} (a b : ZModFp6 q xi0) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 {q xi0 : Nat} (a b : ZModFp6 q xi0) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 {q xi0 : Nat} (a b : ZModFp6 q xi0) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem neg_c0 {q xi0 : Nat} (a : ZModFp6 q xi0) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 {q xi0 : Nat} (a : ZModFp6 q xi0) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 {q xi0 : Nat} (a : ZModFp6 q xi0) : (-a).c2 = -a.c2 := rfl
@[simp] theorem mul_c0 {q xi0 : Nat} (a b : ZModFp6 q xi0) :
    (a * b).c0 = a.c0 * b.c0 + (a.c1 * b.c2 + a.c2 * b.c1) * ZModFp2.xi q xi0 := rfl
@[simp] theorem mul_c1 {q xi0 : Nat} (a b : ZModFp6 q xi0) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 + a.c2 * b.c2 * ZModFp2.xi q xi0 := rfl
@[simp] theorem mul_c2 {q xi0 : Nat} (a b : ZModFp6 q xi0) :
    (a * b).c2 = a.c0 * b.c2 + a.c1 * b.c1 + a.c2 * b.c0 := rfl

instance (q xi0 : Nat) : CommRing (ZModFp6 q xi0) where
  add_assoc a b c := by apply ZModFp6.ext <;> simp [add_assoc]
  zero_add a := by apply ZModFp6.ext <;> simp
  add_zero a := by apply ZModFp6.ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by apply ZModFp6.ext <;> simp [add_comm]
  zsmul := zsmulRec
  neg_add_cancel a := by apply ZModFp6.ext <;> simp
  sub_eq_add_neg a b := by apply ZModFp6.ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by apply ZModFp6.ext <;> simp <;> ring
  one_mul a := by apply ZModFp6.ext <;> simp
  mul_one a := by apply ZModFp6.ext <;> simp
  left_distrib a b c := by apply ZModFp6.ext <;> simp <;> ring
  right_distrib a b c := by apply ZModFp6.ext <;> simp <;> ring
  zero_mul a := by apply ZModFp6.ext <;> simp
  mul_zero a := by apply ZModFp6.ext <;> simp
  mul_comm a b := by apply ZModFp6.ext <;> simp <;> ring

theorem mulV_eq_mul {q xi0 : Nat} (a : ZModFp6 q xi0) :
    mulV a = a * (⟨0, 1, 0⟩ : ZModFp6 q xi0) := by
  apply ZModFp6.ext <;> simp [mulV]

end ZModFp6

/-- Canonical projection from executable `Fp6` to `ZModFp6 q xi0`. -/
def fp6ToZMod (q xi0 : Nat) (a : Fp6) : ZModFp6 q xi0 :=
  ⟨fp2ToZMod q a.c0, fp2ToZMod q a.c1, fp2ToZMod q a.c2⟩

theorem fp6ToZMod_inj {q xi0 : Nat} [NeZero q] {a b : Fp6}
    (ha : fp6Canonical q a = true) (hb : fp6Canonical q b = true)
    (heq : fp6ToZMod q xi0 a = fp6ToZMod q xi0 b) : a = b := by
  rw [fp6Canonical_iff] at ha hb
  have h0 : fp2ToZMod q a.c0 = fp2ToZMod q b.c0 := congrArg ZModFp6.c0 heq
  have h1 : fp2ToZMod q a.c1 = fp2ToZMod q b.c1 := congrArg ZModFp6.c1 heq
  have h2 : fp2ToZMod q a.c2 = fp2ToZMod q b.c2 := congrArg ZModFp6.c2 heq
  cases a; cases b
  simp only [Fp6.mk.injEq]
  exact ⟨fp2ToZMod_inj ha.1 hb.1 h0, fp2ToZMod_inj ha.2.1 hb.2.1 h1, fp2ToZMod_inj ha.2.2 hb.2.2 h2⟩

theorem fp6Add_canonical {q : Nat} (hq : 0 < q) (a b : Fp6) :
    fp6Canonical q (fp6Add q a b) = true := by
  rw [fp6Canonical_iff]; exact ⟨fp2Add_canonical hq _ _, fp2Add_canonical hq _ _, fp2Add_canonical hq _ _⟩

theorem fp6Sub_canonical {q : Nat} (hq : 0 < q) (a b : Fp6) :
    fp6Canonical q (fp6Sub q a b) = true := by
  rw [fp6Canonical_iff]; exact ⟨fp2Sub_canonical hq _ _, fp2Sub_canonical hq _ _, fp2Sub_canonical hq _ _⟩

theorem fp6Neg_canonical {q : Nat} (hq : 0 < q) (a : Fp6) :
    fp6Canonical q (fp6Neg q a) = true := by
  rw [fp6Canonical_iff]; exact ⟨fp2Neg_canonical hq _, fp2Neg_canonical hq _, fp2Neg_canonical hq _⟩

theorem fp6MulByNonResidue_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) {a : Fp6}
    (ha : fp6Canonical q a = true) :
    fp6Canonical q (fp6MulByNonResidue q xi0 a) = true := by
  rw [fp6Canonical_iff] at ha ⊢
  exact ⟨fp2MulByNonResidue_canonical hq xi0 _, ha.1, ha.2.1⟩

theorem fp6MulByFp2_canonical {q : Nat} (hq : 0 < q) (a : Fp6) (s : Fp2) :
    fp6Canonical q (fp6MulByFp2 q a s) = true := by
  rw [fp6Canonical_iff]; exact ⟨fp2Mul_canonical hq _ _, fp2Mul_canonical hq _ _, fp2Mul_canonical hq _ _⟩

theorem fp6Mul_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (a b : Fp6) :
    fp6Canonical q (fp6Mul q xi0 a b) = true := by
  rw [fp6Canonical_iff]; exact ⟨fp2Add_canonical hq _ _, fp2Add_canonical hq _ _, fp2Add_canonical hq _ _⟩

theorem fp6Sqr_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp6) :
    fp6Canonical q (fp6Sqr q xi0 a) = true := by
  rw [fp6Canonical_iff]; exact ⟨fp2Add_canonical hq _ _, fp2Add_canonical hq _ _, fp2Sub_canonical hq _ _⟩

theorem fp6MulBy01_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp6) (b0 b1 : Fp2) :
    fp6Canonical q (fp6MulBy01 q xi0 a b0 b1) = true := by
  rw [fp6Canonical_iff]; exact ⟨fp2Add_canonical hq _ _, fp2Sub_canonical hq _ _, fp2Add_canonical hq _ _⟩

theorem fp6MulBy1_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp6) (b1 : Fp2) :
    fp6Canonical q (fp6MulBy1 q xi0 a b1) = true := by
  rw [fp6Canonical_iff]
  exact ⟨fp2MulByNonResidue_canonical hq xi0 _, fp2Mul_canonical hq _ _, fp2Mul_canonical hq _ _⟩

theorem fp6FrobOdd_canonical {q : Nat} (hq : 0 < q) (k1 k2 : Fp2) {a : Fp6}
    (ha : fp6Canonical q a = true) :
    fp6Canonical q (fp6FrobOdd q k1 k2 a) = true := by
  rw [fp6Canonical_iff] at ha ⊢
  exact ⟨fp2Conj_canonical hq ha.1, fp2Mul_canonical hq _ _, fp2Mul_canonical hq _ _⟩

theorem fp6FrobEven_canonical {q : Nat} (hq : 0 < q) (k1 k2 : Fp2) {a : Fp6}
    (ha : fp6Canonical q a = true) :
    fp6Canonical q (fp6FrobEven q k1 k2 a) = true := by
  rw [fp6Canonical_iff] at ha ⊢
  exact ⟨ha.1, fp2Mul_canonical hq _ _, fp2Mul_canonical hq _ _⟩

theorem fp6ToZMod_zero (q xi0 : Nat) : fp6ToZMod q xi0 fp6Zero = 0 := by
  apply ZModFp6.ext <;> exact fp2ToZMod_zero q

theorem fp6ToZMod_one (q xi0 : Nat) : fp6ToZMod q xi0 fp6One = 1 := by
  apply ZModFp6.ext
  · exact fp2ToZMod_one q
  · exact fp2ToZMod_zero q
  · exact fp2ToZMod_zero q

theorem fp6Add_hom (q xi0 : Nat) (a b : Fp6) :
    fp6ToZMod q xi0 (fp6Add q a b) = fp6ToZMod q xi0 a + fp6ToZMod q xi0 b := by
  apply ZModFp6.ext <;> exact fp2Add_hom q _ _

theorem fp6Sub_hom {q xi0 : Nat} {a b : Fp6} (hb : fp6Canonical q b = true) :
    fp6ToZMod q xi0 (fp6Sub q a b) = fp6ToZMod q xi0 a - fp6ToZMod q xi0 b := by
  rw [fp6Canonical_iff] at hb
  apply ZModFp6.ext
  · exact fp2Sub_hom hb.1
  · exact fp2Sub_hom hb.2.1
  · exact fp2Sub_hom hb.2.2

theorem fp6Neg_hom {q xi0 : Nat} {a : Fp6} (ha : fp6Canonical q a = true) :
    fp6ToZMod q xi0 (fp6Neg q a) = -fp6ToZMod q xi0 a := by
  rw [fp6Canonical_iff] at ha
  apply ZModFp6.ext
  · exact fp2Neg_hom ha.1
  · exact fp2Neg_hom ha.2.1
  · exact fp2Neg_hom ha.2.2

theorem fp6MulByNonResidue_hom {q : Nat} (xi0 : Nat) {a : Fp6} (ha : fp6Canonical q a = true) :
    fp6ToZMod q xi0 (fp6MulByNonResidue q xi0 a) = ZModFp6.mulV (fp6ToZMod q xi0 a) := by
  rw [fp6Canonical_iff] at ha
  apply ZModFp6.ext
  · exact fp2MulByNonResidue_hom xi0 ha.2.2
  · rfl
  · rfl

theorem fp6MulByFp2_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp6) (s : Fp2) :
    fp6ToZMod q xi0 (fp6MulByFp2 q a s) =
      fp6ToZMod q xi0 a * ⟨fp2ToZMod q s, 0, 0⟩ := by
  apply ZModFp6.ext <;> simp [fp6ToZMod, fp6MulByFp2, fp2Mul_hom hq]

/-- Exact soundness of Karatsuba `fp6Mul` in `ZModFp2 q[v] / (v³ - ξ)`. -/
theorem fp6Mul_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (a b : Fp6) :
    fp6ToZMod q xi0 (fp6Mul q xi0 a b) = fp6ToZMod q xi0 a * fp6ToZMod q xi0 b := by
  have hc := fun x y => fp2Mul_canonical hq x y
  have hsc := fun x y => fp2Sub_canonical hq x y
  apply ZModFp6.ext
  · simp only [fp6ToZMod, fp6Mul, fp2Add_hom, fp2MulByNonResidue_hom xi0 (hsc _ _),
      fp2Sub_hom (hc _ _), fp2Mul_hom hq, ZModFp6.mul_c0]
    ring
  · simp only [fp6ToZMod, fp6Mul, fp2Add_hom, fp2MulByNonResidue_hom xi0 (hc _ _),
      fp2Sub_hom (hc _ _), fp2Mul_hom hq, ZModFp6.mul_c1]
    ring
  · simp only [fp6ToZMod, fp6Mul, fp2Add_hom,
      fp2Sub_hom (hc _ _), fp2Mul_hom hq, ZModFp6.mul_c2]
    ring

/-- Exact soundness of CH-SQR2 squaring `fp6Sqr` against `a * a` in `ZModFp6 q xi0`. -/
theorem fp6Sqr_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) {a : Fp6} (ha : fp6Canonical q a = true) :
    fp6ToZMod q xi0 (fp6Sqr q xi0 a) = fp6ToZMod q xi0 a * fp6ToZMod q xi0 a := by
  rw [fp6Canonical_iff] at ha
  have hsc := fp2Sqr_canonical hq
  have hac := fp2Add_canonical hq
  apply ZModFp6.ext
  · simp only [fp6ToZMod, fp6Sqr, fp2Add_hom, fp2MulByNonResidue_hom xi0 (hac _ _),
      fp2Sqr_hom ha.1, fp2Mul_hom hq, ZModFp6.mul_c0]
    ring
  · simp only [fp6ToZMod, fp6Sqr, fp2Add_hom, fp2MulByNonResidue_hom xi0 (hsc _),
      fp2Sqr_hom ha.2.2, fp2Mul_hom hq, ZModFp6.mul_c1]
    ring
  · simp only [fp6ToZMod, fp6Sqr, fp2Sub_hom (hsc _), fp2Add_hom,
      fp2Sqr_hom ha.1, fp2Sqr_hom ha.2.2, fp2Sqr_hom (hac _ _), fp2Sub_hom ha.2.1,
      fp2Mul_hom hq, ZModFp6.mul_c2]
    ring

/-- Exact soundness of sparse `fp6MulBy01` against dense `ZModFp6` multiplication by `b0 + b1*v`. -/
theorem fp6MulBy01_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp6) (b0 b1 : Fp2) :
    fp6ToZMod q xi0 (fp6MulBy01 q xi0 a b0 b1) =
      fp6ToZMod q xi0 a * ⟨fp2ToZMod q b0, fp2ToZMod q b1, 0⟩ := by
  have hmc := fp2Mul_canonical hq
  have hsc := fp2Sub_canonical hq
  apply ZModFp6.ext
  · simp only [fp6ToZMod, fp6MulBy01, fp2Add_hom, fp2MulByNonResidue_hom xi0 (hsc _ _),
      fp2Sub_hom (hmc _ _), fp2Mul_hom hq, ZModFp6.mul_c0]
    ring
  · simp only [fp6ToZMod, fp6MulBy01, fp2Sub_hom (hmc _ _), fp2Add_hom, fp2Mul_hom hq,
      ZModFp6.mul_c1]
    ring
  · simp only [fp6ToZMod, fp6MulBy01, fp2Add_hom, fp2Sub_hom (hmc _ _), fp2Mul_hom hq,
      ZModFp6.mul_c2]
    ring

/-- Exact soundness of sparse `fp6MulBy1` against dense `ZModFp6` multiplication by `b1*v`. -/
theorem fp6MulBy1_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp6) (b1 : Fp2) :
    fp6ToZMod q xi0 (fp6MulBy1 q xi0 a b1) =
      fp6ToZMod q xi0 a * ⟨0, fp2ToZMod q b1, 0⟩ := by
  have hmc := fp2Mul_canonical hq
  apply ZModFp6.ext
  · simp only [fp6ToZMod, fp6MulBy1, fp2MulByNonResidue_hom xi0 (hmc _ _), fp2Mul_hom hq,
      ZModFp6.mul_c0]
    ring
  · simp only [fp6ToZMod, fp6MulBy1, fp2Mul_hom hq, ZModFp6.mul_c1]
    ring
  · simp only [fp6ToZMod, fp6MulBy1, fp2Mul_hom hq, ZModFp6.mul_c2]
    ring

/-- Exact quadratic extension ring `ZModFp6 q xi0[w] / (w² - v)` (degree-12 pairing tower). -/
@[ext]
structure ZModFp12 (q xi0 : Nat) where
  c0 : ZModFp6 q xi0
  c1 : ZModFp6 q xi0
  deriving DecidableEq

namespace ZModFp12

def zero (q xi0 : Nat) : ZModFp12 q xi0 := ⟨0, 0⟩
def one (q xi0 : Nat) : ZModFp12 q xi0 := ⟨1, 0⟩
def add {q xi0 : Nat} (a b : ZModFp12 q xi0) : ZModFp12 q xi0 := ⟨a.c0 + b.c0, a.c1 + b.c1⟩
def sub {q xi0 : Nat} (a b : ZModFp12 q xi0) : ZModFp12 q xi0 := ⟨a.c0 - b.c0, a.c1 - b.c1⟩
def neg {q xi0 : Nat} (a : ZModFp12 q xi0) : ZModFp12 q xi0 := ⟨-a.c0, -a.c1⟩
def conj {q xi0 : Nat} (a : ZModFp12 q xi0) : ZModFp12 q xi0 := ⟨a.c0, -a.c1⟩
def ofFp6 {q xi0 : Nat} (s : ZModFp6 q xi0) : ZModFp12 q xi0 := ⟨s, 0⟩
def mul {q xi0 : Nat} (a b : ZModFp12 q xi0) : ZModFp12 q xi0 :=
  ⟨a.c0 * b.c0 + ZModFp6.mulV (a.c1 * b.c1), a.c0 * b.c1 + a.c1 * b.c0⟩

instance (q xi0 : Nat) : Zero (ZModFp12 q xi0) := ⟨zero q xi0⟩
instance (q xi0 : Nat) : One (ZModFp12 q xi0) := ⟨one q xi0⟩
instance (q xi0 : Nat) : Add (ZModFp12 q xi0) := ⟨add⟩
instance (q xi0 : Nat) : Sub (ZModFp12 q xi0) := ⟨sub⟩
instance (q xi0 : Nat) : Neg (ZModFp12 q xi0) := ⟨neg⟩
instance (q xi0 : Nat) : Mul (ZModFp12 q xi0) := ⟨mul⟩

@[simp] theorem zero_c0 (q xi0 : Nat) : (0 : ZModFp12 q xi0).c0 = 0 := rfl
@[simp] theorem zero_c1 (q xi0 : Nat) : (0 : ZModFp12 q xi0).c1 = 0 := rfl
@[simp] theorem one_c0 (q xi0 : Nat) : (1 : ZModFp12 q xi0).c0 = 1 := rfl
@[simp] theorem one_c1 (q xi0 : Nat) : (1 : ZModFp12 q xi0).c1 = 0 := rfl
@[simp] theorem add_c0 {q xi0 : Nat} (a b : ZModFp12 q xi0) : (a + b).c0 = a.c0 + b.c0 := rfl
@[simp] theorem add_c1 {q xi0 : Nat} (a b : ZModFp12 q xi0) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem sub_c0 {q xi0 : Nat} (a b : ZModFp12 q xi0) : (a - b).c0 = a.c0 - b.c0 := rfl
@[simp] theorem sub_c1 {q xi0 : Nat} (a b : ZModFp12 q xi0) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem neg_c0 {q xi0 : Nat} (a : ZModFp12 q xi0) : (-a).c0 = -a.c0 := rfl
@[simp] theorem neg_c1 {q xi0 : Nat} (a : ZModFp12 q xi0) : (-a).c1 = -a.c1 := rfl
@[simp] theorem mul_c0 {q xi0 : Nat} (a b : ZModFp12 q xi0) :
    (a * b).c0 = a.c0 * b.c0 + ZModFp6.mulV (a.c1 * b.c1) := rfl
@[simp] theorem mul_c1 {q xi0 : Nat} (a b : ZModFp12 q xi0) :
    (a * b).c1 = a.c0 * b.c1 + a.c1 * b.c0 := rfl

instance (q xi0 : Nat) : CommRing (ZModFp12 q xi0) where
  add_assoc a b c := by apply ZModFp12.ext <;> simp [add_assoc]
  zero_add a := by apply ZModFp12.ext <;> simp
  add_zero a := by apply ZModFp12.ext <;> simp
  nsmul := nsmulRec
  add_comm a b := by apply ZModFp12.ext <;> simp [add_comm]
  zsmul := zsmulRec
  neg_add_cancel a := by apply ZModFp12.ext <;> simp
  sub_eq_add_neg a b := by apply ZModFp12.ext <;> simp [sub_eq_add_neg]
  mul_assoc a b c := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul] <;> ring
  one_mul a := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul]
  mul_one a := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul]
  left_distrib a b c := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul] <;> ring
  right_distrib a b c := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul] <;> ring
  zero_mul a := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul]
  mul_zero a := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul]
  mul_comm a b := by apply ZModFp12.ext <;> simp [ZModFp6.mulV_eq_mul] <;> ring

end ZModFp12

/-- Canonical projection from executable `Fp12` to `ZModFp12 q xi0`. -/
def fp12ToZMod (q xi0 : Nat) (a : Fp12) : ZModFp12 q xi0 :=
  ⟨fp6ToZMod q xi0 a.c0, fp6ToZMod q xi0 a.c1⟩

theorem fp12ToZMod_inj {q xi0 : Nat} [NeZero q] {a b : Fp12}
    (ha : fp12Canonical q a = true) (hb : fp12Canonical q b = true)
    (heq : fp12ToZMod q xi0 a = fp12ToZMod q xi0 b) : a = b := by
  rw [fp12Canonical_iff] at ha hb
  cases a; cases b
  simp only [Fp12.mk.injEq]
  exact ⟨fp6ToZMod_inj ha.1 hb.1 (congrArg ZModFp12.c0 heq),
    fp6ToZMod_inj ha.2 hb.2 (congrArg ZModFp12.c1 heq)⟩

theorem fp12Zero_canonical {q : Nat} (hq : 0 < q) : fp12Canonical q fp12Zero = true := by
  simp [fp12Canonical_iff, fp6Canonical_iff, fp2Canonical_iff, fp12Zero, fp6Zero, fp2Zero, hq]

theorem fp12One_canonical {q : Nat} (hq : 1 < q) : fp12Canonical q fp12One = true := by
  simp [fp12Canonical_iff, fp6Canonical_iff, fp2Canonical_iff, fp12One, fp6One, fp6Zero,
    fp2One, fp2Zero, hq, (by omega : 0 < q)]

theorem fp12OfFp6_canonical {q : Nat} (hq : 0 < q) {s : Fp6} (hs : fp6Canonical q s = true) :
    fp12Canonical q (fp12OfFp6 s) = true := by
  rw [fp12Canonical_iff]
  refine ⟨hs, ?_⟩
  simp [fp12OfFp6, fp6Canonical_iff, fp2Canonical_iff, fp6Zero, fp2Zero, hq]

theorem fp12Conj_canonical {q : Nat} (hq : 0 < q) {a : Fp12} (ha : fp12Canonical q a = true) :
    fp12Canonical q (fp12Conj q a) = true := by
  rw [fp12Canonical_iff] at ha ⊢; exact ⟨ha.1, fp6Neg_canonical hq _⟩

theorem fp12Mul_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (a b : Fp12) :
    fp12Canonical q (fp12Mul q xi0 a b) = true := by
  rw [fp12Canonical_iff]; exact ⟨fp6Add_canonical hq _ _, fp6Sub_canonical hq _ _⟩

theorem fp12Sqr_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (a : Fp12) :
    fp12Canonical q (fp12Sqr q xi0 a) = true := by
  rw [fp12Canonical_iff]; exact ⟨fp6Sub_canonical hq _ _, fp6Add_canonical hq _ _⟩

theorem fp12MulBy034_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (f : Fp12) (c0 c3 c4 : Fp2) :
    fp12Canonical q (fp12MulBy034 q xi0 f c0 c3 c4) = true := by
  rw [fp12Canonical_iff]; exact ⟨fp6Add_canonical hq _ _, fp6Sub_canonical hq _ _⟩

theorem fp12MulBy014_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) (f : Fp12) (c0 c1 c4 : Fp2) :
    fp12Canonical q (fp12MulBy014 q xi0 f c0 c1 c4) = true := by
  rw [fp12Canonical_iff]; exact ⟨fp6Add_canonical hq _ _, fp6Sub_canonical hq _ _⟩

theorem fp12FrobOdd_canonical {q : Nat} (hq : 0 < q) (k1 k2 w1 : Fp2) {a : Fp12}
    (ha : fp12Canonical q a = true) :
    fp12Canonical q (fp12FrobOdd q k1 k2 w1 a) = true := by
  rw [fp12Canonical_iff] at ha ⊢
  exact ⟨fp6FrobOdd_canonical hq k1 k2 ha.1, fp6MulByFp2_canonical hq _ _⟩

theorem fp12FrobEven_canonical {q : Nat} (hq : 0 < q) (k1 k2 w1 : Fp2) {a : Fp12}
    (ha : fp12Canonical q a = true) :
    fp12Canonical q (fp12FrobEven q k1 k2 w1 a) = true := by
  rw [fp12Canonical_iff] at ha ⊢
  exact ⟨fp6FrobEven_canonical hq k1 k2 ha.1, fp6MulByFp2_canonical hq _ _⟩

theorem fp12ToZMod_zero (q xi0 : Nat) : fp12ToZMod q xi0 fp12Zero = 0 := by
  apply ZModFp12.ext <;> exact fp6ToZMod_zero q xi0

theorem fp12ToZMod_one (q xi0 : Nat) : fp12ToZMod q xi0 fp12One = 1 := by
  apply ZModFp12.ext
  · exact fp6ToZMod_one q xi0
  · exact fp6ToZMod_zero q xi0

theorem fp12OfFp6_hom (q xi0 : Nat) (s : Fp6) :
    fp12ToZMod q xi0 (fp12OfFp6 s) = ZModFp12.ofFp6 (fp6ToZMod q xi0 s) := by
  apply ZModFp12.ext
  · rfl
  · exact fp6ToZMod_zero q xi0

theorem fp12Add_hom (q xi0 : Nat) (a b : Fp12) :
    fp12ToZMod q xi0 (fp12Add q a b) = fp12ToZMod q xi0 a + fp12ToZMod q xi0 b := by
  apply ZModFp12.ext <;> exact fp6Add_hom q xi0 _ _

theorem fp12Sub_hom {q xi0 : Nat} {a b : Fp12} (hb : fp12Canonical q b = true) :
    fp12ToZMod q xi0 (fp12Sub q a b) = fp12ToZMod q xi0 a - fp12ToZMod q xi0 b := by
  rw [fp12Canonical_iff] at hb
  apply ZModFp12.ext
  · exact fp6Sub_hom hb.1
  · exact fp6Sub_hom hb.2

theorem fp12Conj_hom {q xi0 : Nat} {a : Fp12} (ha : fp12Canonical q a = true) :
    fp12ToZMod q xi0 (fp12Conj q a) = ZModFp12.conj (fp12ToZMod q xi0 a) := by
  rw [fp12Canonical_iff] at ha
  apply ZModFp12.ext
  · rfl
  · exact fp6Neg_hom ha.2

/-- Exact soundness of Karatsuba `fp12Mul` in `ZModFp6 q xi0[w] / (w² - v)`. -/
theorem fp12Mul_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (a b : Fp12) :
    fp12ToZMod q xi0 (fp12Mul q xi0 a b) = fp12ToZMod q xi0 a * fp12ToZMod q xi0 b := by
  have hmc := fp6Mul_canonical hq xi0
  apply ZModFp12.ext
  · simp only [fp12ToZMod, fp12Mul, fp6Add_hom, fp6MulByNonResidue_hom xi0 (hmc _ _),
      fp6Mul_hom hq xi0, ZModFp12.mul_c0]
  · simp only [fp12ToZMod, fp12Mul, fp6Sub_hom (hmc _ _), fp6Add_hom,
      fp6Mul_hom hq xi0, ZModFp12.mul_c1]
    ring

/-- Exact soundness of complex squaring `fp12Sqr` against `a * a` in `ZModFp12 q xi0`. -/
theorem fp12Sqr_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) {a : Fp12} (ha : fp12Canonical q a = true) :
    fp12ToZMod q xi0 (fp12Sqr q xi0 a) = fp12ToZMod q xi0 a * fp12ToZMod q xi0 a := by
  rw [fp12Canonical_iff] at ha
  have hmc := fp6Mul_canonical hq xi0
  have hvc : ∀ x : Fp6, fp6Canonical q x = true → fp6Canonical q (fp6MulByNonResidue q xi0 x) = true :=
    fun _ hx => fp6MulByNonResidue_canonical hq xi0 hx
  apply ZModFp12.ext
  · simp only [fp12ToZMod, fp12Sqr, fp6Sub_hom (hvc _ (hmc _ _)), fp6Sub_hom (hmc _ _),
      fp6Mul_hom hq xi0, fp6Add_hom, fp6MulByNonResidue_hom xi0 ha.2,
      fp6MulByNonResidue_hom xi0 (hmc _ _), ZModFp12.mul_c0, ZModFp6.mulV_eq_mul]
    ring
  · simp only [fp12ToZMod, fp12Sqr, fp6Add_hom, fp6Mul_hom hq xi0, ZModFp12.mul_c1]
    ring

/-- Exact soundness of D-type sparse line multiplication `fp12MulBy034` (BN254). -/
theorem fp12MulBy034_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (f : Fp12) (c0 c3 c4 : Fp2) :
    fp12ToZMod q xi0 (fp12MulBy034 q xi0 f c0 c3 c4) =
      fp12ToZMod q xi0 f *
        ⟨⟨fp2ToZMod q c0, 0, 0⟩, ⟨fp2ToZMod q c3, fp2ToZMod q c4, 0⟩⟩ := by
  have h01 := fp6MulBy01_canonical hq xi0
  have hac := fp6Add_canonical hq
  apply ZModFp12.ext
  · simp only [fp12ToZMod, fp12MulBy034, fp6Add_hom, fp6MulByNonResidue_hom xi0 (h01 _ _ _),
      fp6MulByFp2_hom hq xi0, fp6MulBy01_hom hq xi0, ZModFp12.mul_c0]
    ring
  · simp only [fp12ToZMod, fp12MulBy034, fp6Sub_hom (hac _ _), fp6Add_hom,
      fp6MulBy01_hom hq xi0, fp6MulByFp2_hom hq xi0, fp2Add_hom, ZModFp12.mul_c1]
    have hsplit :
        (⟨fp2ToZMod q c0 + fp2ToZMod q c3, fp2ToZMod q c4, 0⟩ : ZModFp6 q xi0) =
          ⟨fp2ToZMod q c0, 0, 0⟩ + ⟨fp2ToZMod q c3, fp2ToZMod q c4, 0⟩ := by
      apply ZModFp6.ext <;> simp
    rw [hsplit]
    ring

/-- Exact soundness of M-type sparse line multiplication `fp12MulBy014` (BLS12-381). -/
theorem fp12MulBy014_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (f : Fp12) (c0 c1 c4 : Fp2) :
    fp12ToZMod q xi0 (fp12MulBy014 q xi0 f c0 c1 c4) =
      fp12ToZMod q xi0 f *
        ⟨⟨fp2ToZMod q c0, fp2ToZMod q c1, 0⟩, ⟨0, fp2ToZMod q c4, 0⟩⟩ := by
  have h01 := fp6MulBy01_canonical hq xi0
  have h1 := fp6MulBy1_canonical hq xi0
  apply ZModFp12.ext
  · simp only [fp12ToZMod, fp12MulBy014, fp6Add_hom, fp6MulByNonResidue_hom xi0 (h1 _ _),
      fp6MulBy01_hom hq xi0, fp6MulBy1_hom hq xi0, ZModFp12.mul_c0]
    ring
  · simp only [fp12ToZMod, fp12MulBy014, fp6Sub_hom (h1 _ _), fp6Sub_hom (h01 _ _ _),
      fp6Add_hom, fp6MulBy01_hom hq xi0, fp6MulBy1_hom hq xi0, fp2Add_hom, ZModFp12.mul_c1]
    have hsplit :
        (⟨fp2ToZMod q c0, fp2ToZMod q c1 + fp2ToZMod q c4, 0⟩ : ZModFp6 q xi0) =
          ⟨fp2ToZMod q c0, fp2ToZMod q c1, 0⟩ + ⟨0, fp2ToZMod q c4, 0⟩ := by
      apply ZModFp6.ext <;> simp
    rw [hsplit]
    ring

theorem fp12PowFuel_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat) :
    ∀ fuel base exp acc,
      fp12Canonical q base = true →
      fp12Canonical q acc = true →
      fp12Canonical q (fp12PowFuel q xi0 fuel base exp acc) = true
  | 0, _, _, _, _, hacc => hacc
  | fuel + 1, base, 0, acc, _, hacc => hacc
  | fuel + 1, base, exp + 1, acc, _, hacc => by
    unfold fp12PowFuel
    dsimp only
    apply fp12PowFuel_canonical hq xi0 fuel
    · exact fp12Sqr_canonical hq xi0 base
    · unfold fp12CondMul
      cases (exp + 1) % 2 with
      | zero => exact hacc
      | succ _ => exact fp12Mul_canonical hq xi0 acc base

/-- Exact soundness of structural binary exponentiation `fp12PowFuel` in `ZModFp12 q xi0`. -/
theorem fp12PowFuel_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) :
    ∀ fuel base exp acc,
      exp < 2 ^ fuel →
      fp12Canonical q base = true →
      fp12ToZMod q xi0 (fp12PowFuel q xi0 fuel base exp acc) =
        fp12ToZMod q xi0 acc * (fp12ToZMod q xi0 base) ^ exp
  | 0, base, exp, acc, hlt, _ => by
    have h0 : exp = 0 := by omega
    subst h0; simp [fp12PowFuel]
  | fuel + 1, base, 0, acc, _, _ => by
    simp [fp12PowFuel]
  | fuel + 1, base, exp + 1, acc, hlt, hbase => by
    have hstep : fp12PowFuel q xi0 (fuel + 1) base (exp + 1) acc =
        fp12PowFuel q xi0 fuel (fp12Sqr q xi0 base) ((exp + 1) / 2)
          (fp12CondMul q xi0 ((exp + 1) % 2) acc base) := rfl
    rw [hstep]
    have hdiv : (exp + 1) / 2 < 2 ^ fuel := by
      have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      omega
    rw [fp12PowFuel_hom hq xi0 fuel _ _ _ hdiv (fp12Sqr_canonical hq xi0 base),
      fp12Sqr_hom hq xi0 hbase]
    have hmod_cases : (exp + 1) % 2 = 0 ∨ (exp + 1) % 2 = 1 := by omega
    rcases hmod_cases with hm | hm
    · rw [hm]
      simp only [fp12CondMul]
      have hexp : exp + 1 = 2 * ((exp + 1) / 2) := by omega
      conv_rhs => rw [hexp, pow_mul, sq]
    · rw [hm]
      simp only [fp12CondMul, fp12Mul_hom hq xi0]
      have hexp : exp + 1 = 2 * ((exp + 1) / 2) + 1 := by omega
      conv_rhs => rw [hexp, pow_succ, pow_mul, sq]
      ring

/-- Exact soundness of `fp12Pow q xi0 bits base exp` whenever `exp < 2 ^ bits` and `base` is canonical. -/
theorem fp12Pow_hom {q : Nat} (hq : 0 < q) (xi0 bits : Nat) {base : Fp12} {exp : Nat}
    (hlt : exp < 2 ^ bits) (hbase : fp12Canonical q base = true) :
    fp12ToZMod q xi0 (fp12Pow q xi0 bits base exp) = (fp12ToZMod q xi0 base) ^ exp := by
  unfold fp12Pow
  rw [fp12PowFuel_hom hq xi0 bits base exp fp12One hlt hbase, fp12ToZMod_one, one_mul]

end FqAndMonus

/-! ## Section 2: Curve Equation, Strict Infinity, Affine `u80` Codecs & BLS12-381 Bowe Subgroup Soundness -/

section CurveAndSubgroup

/-! ### 2.1 Curve Equation & Strict Infinity Rules -/

theorem g1OnCurve_iff {c : CurveParams} (P : G1Point) :
    g1OnCurve c P = true ↔
      P = g1Inf ∨
        (P.isInf = 0 ∧ P.x < c.fqMod ∧ P.y < c.fqMod ∧
          (P.y * P.y) % c.fqMod = (P.x * P.x * P.x + c.curveB) % c.fqMod) := by
  unfold g1OnCurve g1Inf
  cases P with
  | mk px py pinf =>
    dsimp only
    by_cases h1 : pinf = 1
    · subst h1
      simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq, G1Point.mk.injEq, and_true]
      constructor
      · intro h
        by_cases hx : px = 0
        · simp [hx] at h; exact Or.inl ⟨hx, h⟩
        · simp [hx] at h
      · rintro (⟨rfl, rfl⟩ | ⟨h0, _⟩)
        · simp
        · omega
    · have h1b : (pinf == 1) = false := beq_false_of_ne h1
      rw [h1b]
      simp only [Bool.false_eq_true, ↓reduceIte, G1Point.mk.injEq]
      by_cases h0 : pinf = 0
      · subst h0
        simp only [beq_self_eq_true, ↓reduceIte, true_and]
        have hrhs :
            (c.curveB % c.fqMod + (px * ((px * px) % c.fqMod)) % c.fqMod) % c.fqMod =
              (px * px * px + c.curveB) % c.fqMod := by
          rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, Nat.mul_mod px, Nat.mod_mod,
            ← Nat.mul_mod, Nat.add_comm, ← Nat.add_mod, Nat.mul_comm px (px * px)]
        constructor
        · intro h
          right
          split_ifs at h with hx hy
          · simp only [beq_iff_eq] at h
            unfold fqMulMod fqAddMod at h
            exact ⟨hx, hy, h.trans hrhs⟩
        · rintro (⟨_, _, h01⟩ | ⟨hx, hy, heq⟩)
          · omega
          · simp only [hx, hy, ↓reduceIte, beq_iff_eq]
            unfold fqMulMod fqAddMod
            exact heq.trans hrhs.symm
      · have h0b : (pinf == 0) = false := beq_false_of_ne h0
        rw [h0b]
        simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_or]
        exact ⟨fun h => h1 h.2.2, fun h => h0 h.1⟩

theorem g1Validate_iff {p : PairingParams} (P : G1Point) :
    g1Validate p P = true ↔
      P = g1Inf ∨
        (P.isInf = 0 ∧ P.x < p.curve.fqMod ∧ P.y < p.curve.fqMod ∧ (P.x ≠ 0 ∨ P.y ≠ 0) ∧
          (P.y * P.y) % p.curve.fqMod = (P.x * P.x * P.x + p.curve.curveB) % p.curve.fqMod ∧
          g1InSubgroup p P = true) := by
  unfold g1Validate g1Inf
  cases P with
  | mk px py pinf =>
    dsimp only
    by_cases h1 : pinf = 1
    · subst h1
      simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq, G1Point.mk.injEq, and_true]
      constructor
      · intro h; exact Or.inl ⟨by omega, by omega⟩
      · rintro (⟨rfl, rfl⟩ | ⟨h0, _⟩)
        · rfl
        · omega
    · have h1b : (pinf == 1) = false := beq_false_of_ne h1
      rw [h1b]
      simp only [Bool.false_eq_true, ↓reduceIte, G1Point.mk.injEq]
      by_cases h0 : pinf = 0
      · subst h0
        simp only [beq_self_eq_true, ↓reduceIte, true_and]
        have hlt : (natLtErr px p.curve.fqMod + natLtErr py p.curve.fqMod == 0) = true ↔
            px < p.curve.fqMod ∧ py < p.curve.fqMod := by
          simp only [beq_iff_eq, natLtErr]; omega
        by_cases hcan : natLtErr px p.curve.fqMod + natLtErr py p.curve.fqMod == 0
        · have ⟨hx, hy⟩ := hlt.mp hcan
          simp only [hcan, ↓reduceIte]
          by_cases hzero : px + py = 0
          · have hzb : (px + py == 0) = true := beq_iff_eq.mpr hzero
            simp only [hzb, ↓reduceIte, Bool.false_eq_true, false_iff, not_or]
            refine ⟨fun h => by omega, fun h => by rcases h.2.2.1 with hne | hne <;> omega⟩
          · have hzb : (px + py == 0) = false := beq_false_of_ne hzero
            simp only [hzb, Bool.false_eq_true, ↓reduceIte]
            have hcurveEq :
                (fqMulMod p.curve.fqMod py py ==
                  fqAddMod p.curve.fqMod
                    (fqMulMod p.curve.fqMod (fqMulMod p.curve.fqMod px px) px)
                    (p.curve.curveB % p.curve.fqMod)) = true ↔
                (py * py) % p.curve.fqMod = (px * px * px + p.curve.curveB) % p.curve.fqMod := by
              simp only [beq_iff_eq]
              unfold fqMulMod fqAddMod
              have hrhs :
                  (p.curve.curveB % p.curve.fqMod + (px * ((px * px) % p.curve.fqMod)) % p.curve.fqMod) %
                    p.curve.fqMod = (px * px * px + p.curve.curveB) % p.curve.fqMod := by
                rw [Nat.add_mod, Nat.mod_mod, Nat.mod_mod, Nat.mul_mod px, Nat.mod_mod,
                  ← Nat.mul_mod, Nat.add_comm, ← Nat.add_mod, Nat.mul_comm px (px * px)]
              rw [hrhs]
            by_cases hc : fqMulMod p.curve.fqMod py py ==
                fqAddMod p.curve.fqMod
                  (fqMulMod p.curve.fqMod (fqMulMod p.curve.fqMod px px) px)
                  (p.curve.curveB % p.curve.fqMod)
            · simp only [hc, ↓reduceIte]
              constructor
              · intro hsub
                exact Or.inr ⟨hx, hy, by omega, hcurveEq.mp hc, hsub⟩
              · rintro (⟨_, _, h01⟩ | ⟨_, _, _, _, hsub⟩)
                · omega
                · exact hsub
            · simp only [hc, Bool.false_eq_true, ↓reduceIte, false_iff, not_or]
              refine ⟨fun h => by omega, fun h => ?_⟩
              have := hcurveEq.mpr h.2.2.2.1
              rw [this] at hc; exact absurd rfl hc
        · simp only [hcan, Bool.false_eq_true, ↓reduceIte, false_iff, not_or]
          refine ⟨fun h => by omega, fun h => ?_⟩
          have := hlt.mpr ⟨h.1, h.2.1⟩
          rw [this] at hcan; exact absurd rfl hcan
      · have h0b : (pinf == 0) = false := beq_false_of_ne h0
        rw [h0b]
        simp only [Bool.false_eq_true, ↓reduceIte, false_iff, not_or]
        exact ⟨fun h => h1 h.2.2, fun h => h0 h.1⟩

/-- Strict rejection of malformed point-at-infinity flags and degenerate coordinates in `g1Validate`. -/
theorem g1Validate_rejects_malformed_infinity (p : PairingParams) (x y inf : Nat) :
    (inf ≠ 0 → inf ≠ 1 → g1Validate p { x, y, isInf := inf } = false) ∧
    ((x ≠ 0 ∨ y ≠ 0) → g1Validate p { x, y, isInf := 1 } = false) ∧
    g1Validate p { x := 0, y := 0, isInf := 0 } = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro h0 h1
    unfold g1Validate
    have hb1 : (inf == 1) = false := beq_false_of_ne h1
    have hb0 : (inf == 0) = false := beq_false_of_ne h0
    simp [hb1, hb0]
  · intro hne
    unfold g1Validate
    simp only [beq_self_eq_true, ↓reduceIte, beq_eq_false_iff_ne]
    rcases hne with hx | hy <;> omega
  · unfold g1Validate
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Nat.add_zero]
    split_ifs <;> rfl

/-! ### 2.2 Canonical Affine `u80` Limb Decoders & Bridge to `Ix.Cert.AiurCompression` -/

theorem decodeLimb4Canonical_sound {r topBound q : Nat} {v : Limb4}
    (h : (decodeLimb4Canonical r topBound q v).ok = 1) :
    v.l0 < r ∧ v.l1 < r ∧ v.l2 < r ∧ v.l3 < topBound ∧
    (decodeLimb4Canonical r topBound q v).val =
      v.l0 + r * (v.l1 + r * (v.l2 + r * v.l3)) ∧
    (decodeLimb4Canonical r topBound q v).val < q := by
  unfold decodeLimb4Canonical at h ⊢
  dsimp only at h ⊢
  split_ifs at h with herr hlt
  have herr' := herr
  simp only [beq_iff_eq, Nat.add_eq_zero_iff, natLtErr_eq_zero_iff] at herr'
  obtain ⟨⟨⟨hl0, hl1⟩, hl2⟩, hl3⟩ := herr'
  refine ⟨hl0, hl1, hl2, hl3, ?_, ?_⟩
  · simp only [herr, hlt, ↓reduceIte]
  · simp only [herr, hlt, ↓reduceIte]

theorem decodeLimb5Canonical_sound {r topBound q : Nat} {v : Limb5}
    (h : (decodeLimb5Canonical r topBound q v).ok = 1) :
    v.l0 < r ∧ v.l1 < r ∧ v.l2 < r ∧ v.l3 < r ∧ v.l4 < topBound ∧
    (decodeLimb5Canonical r topBound q v).val =
      v.l0 + r * (v.l1 + r * (v.l2 + r * (v.l3 + r * v.l4))) ∧
    (decodeLimb5Canonical r topBound q v).val < q := by
  unfold decodeLimb5Canonical at h ⊢
  dsimp only at h ⊢
  split_ifs at h with herr hlt
  have herr' := herr
  simp only [beq_iff_eq, Nat.add_eq_zero_iff, natLtErr_eq_zero_iff] at herr'
  obtain ⟨⟨⟨⟨hl0, hl1⟩, hl2⟩, hl3⟩, hl4⟩ := herr'
  refine ⟨hl0, hl1, hl2, hl3, hl4, ?_, ?_⟩
  · simp only [herr, hlt, ↓reduceIte]
  · simp only [herr, hlt, ↓reduceIte]

private theorem limb4_recompose_2pow80 (l0 l1 l2 l3 : Nat) :
    l0 + 2 ^ 80 * (l1 + 2 ^ 80 * (l2 + 2 ^ 80 * l3)) =
      l0 + 2 ^ 80 * l1 + 2 ^ 160 * l2 + 2 ^ 240 * l3 := by
  have h160 : (2 ^ 80 : Nat) ^ 2 = 2 ^ 160 :=
    (Nat.pow_mul 2 80 2).symm.trans (congrArg (2 ^ ·) (by decide : 80 * 2 = 160))
  have h240 : (2 ^ 80 : Nat) ^ 3 = 2 ^ 240 :=
    (Nat.pow_mul 2 80 3).symm.trans (congrArg (2 ^ ·) (by decide : 80 * 3 = 240))
  rw [← h160, ← h240]
  generalize (2 ^ 80 : Nat) = R
  ring

private theorem limb5_recompose_2pow80 (l0 l1 l2 l3 l4 : Nat) :
    l0 + 2 ^ 80 * (l1 + 2 ^ 80 * (l2 + 2 ^ 80 * (l3 + 2 ^ 80 * l4))) =
      l0 + 2 ^ 80 * l1 + 2 ^ 160 * l2 + 2 ^ 240 * l3 + 2 ^ 320 * l4 := by
  have h160 : (2 ^ 80 : Nat) ^ 2 = 2 ^ 160 := by
    have hm : 80 * 2 = 160 := rfl; rw [← hm, Nat.pow_mul]
  have h240 : (2 ^ 80 : Nat) ^ 3 = 2 ^ 240 := by
    have hm : 80 * 3 = 240 := rfl; rw [← hm, Nat.pow_mul]
  have h320 : (2 ^ 80 : Nat) ^ 4 = 2 ^ 320 := by
    have hm : 80 * 4 = 320 := rfl; rw [← hm, Nat.pow_mul]
  rw [← h160, ← h240, ← h320]
  generalize (2 ^ 80 : Nat) = R
  ring

private theorem radix80_eq_pow : radix80 = 2 ^ 80 := by decide

/-- Soundness of `decodeAffineG1BN254` on production BN254:
extracts canonical `4 × u80/u14` limb bounds, exact recomposed coordinates `< bn254FqModulus`,
`g1Validate`, AND a canonical `Ix.Cert.AiurCompression.Bn254AffineU80Point` matching `pt`! -/
theorem decodeAffineG1BN254_sound {pt : AffineG1BN254}
    (h : (decodeAffineG1BN254 bn254PairingParams pt).ok = 1) :
    let d := decodeAffineG1BN254 bn254PairingParams pt
    pt.x.l0 < 2 ^ 80 ∧ pt.x.l1 < 2 ^ 80 ∧ pt.x.l2 < 2 ^ 80 ∧ pt.x.l3 < 2 ^ 14 ∧
    pt.y.l0 < 2 ^ 80 ∧ pt.y.l1 < 2 ^ 80 ∧ pt.y.l2 < 2 ^ 80 ∧ pt.y.l3 < 2 ^ 14 ∧
    d.point.x = ofLimb4 pt.x ∧ d.point.y = ofLimb4 pt.y ∧ d.point.isInf = pt.isInf ∧
    g1Validate bn254PairingParams d.point = true ∧
    ∃ u : Bn254AffineU80Point,
      u.x.toNat = d.point.x ∧ u.y.toNat = d.point.y ∧
      (if u.infinity then 1 else 0) = d.point.isInf ∧
      u.words = [pt.x.l0, pt.x.l1, pt.x.l2, pt.x.l3, pt.y.l0, pt.y.l1, pt.y.l2, pt.y.l3, pt.isInf] := by
  have hDecDef : decodeAffineG1BN254 bn254PairingParams pt =
      if (natLtErr pt.x.l0 radix80 + natLtErr pt.x.l1 radix80 + natLtErr pt.x.l2 radix80 +
          natLtErr pt.x.l3 16384 + natLtErr pt.y.l0 radix80 + natLtErr pt.y.l1 radix80 +
          natLtErr pt.y.l2 radix80 + natLtErr pt.y.l3 16384 == 0) = true then
        if g1Validate bn254PairingParams { x := ofLimb4 pt.x, y := ofLimb4 pt.y, isInf := pt.isInf } = true then
          { ok := 1, point := { x := ofLimb4 pt.x, y := ofLimb4 pt.y, isInf := pt.isInf } }
        else { ok := 0, point := g1Inf }
      else { ok := 0, point := g1Inf } := rfl
  rw [hDecDef] at h ⊢
  split_ifs at h with herr hval
  have hOut :
      (if (natLtErr pt.x.l0 radix80 + natLtErr pt.x.l1 radix80 + natLtErr pt.x.l2 radix80 +
            natLtErr pt.x.l3 16384 + natLtErr pt.y.l0 radix80 + natLtErr pt.y.l1 radix80 +
            natLtErr pt.y.l2 radix80 + natLtErr pt.y.l3 16384 == 0) = true then
        if g1Validate bn254PairingParams { x := ofLimb4 pt.x, y := ofLimb4 pt.y, isInf := pt.isInf } = true then
          ({ ok := 1, point := { x := ofLimb4 pt.x, y := ofLimb4 pt.y, isInf := pt.isInf } } : DecodeG1Result)
        else { ok := 0, point := g1Inf }
      else { ok := 0, point := g1Inf }) =
      { ok := 1, point := { x := ofLimb4 pt.x, y := ofLimb4 pt.y, isInf := pt.isInf } } := by
    simp only [herr, hval, ↓reduceIte]
  dsimp only
  rw [hOut]
  dsimp only
  have herr' := herr
  simp only [beq_iff_eq, Nat.add_eq_zero_iff, natLtErr_eq_zero_iff] at herr'
  obtain ⟨⟨⟨⟨⟨⟨⟨hx0, hx1⟩, hx2⟩, hx3⟩, hy0⟩, hy1⟩, hy2⟩, hy3⟩ := herr'
  have htb : (16384 : Nat) = 2 ^ 14 := by decide
  rw [radix80_eq_pow] at hx0 hx1 hx2 hy0 hy1 hy2
  rw [htb] at hx3 hy3
  have hEqX : ofLimb4 pt.x = pt.x.l0 + 2 ^ 80 * pt.x.l1 + 2 ^ 160 * pt.x.l2 + 2 ^ 240 * pt.x.l3 := by
    unfold ofLimb4; rw [radix80_eq_pow]; exact limb4_recompose_2pow80 pt.x.l0 pt.x.l1 pt.x.l2 pt.x.l3
  have hEqY : ofLimb4 pt.y = pt.y.l0 + 2 ^ 80 * pt.y.l1 + 2 ^ 160 * pt.y.l2 + 2 ^ 240 * pt.y.l3 := by
    unfold ofLimb4; rw [radix80_eq_pow]; exact limb4_recompose_2pow80 pt.y.l0 pt.y.l1 pt.y.l2 pt.y.l3
  have hgv := (g1Validate_iff _).mp hval
  have hxr : pt.x.l0 + 2 ^ 80 * pt.x.l1 + 2 ^ 160 * pt.x.l2 + 2 ^ 240 * pt.x.l3 < bn254FqModulus := by
    rw [← hEqX]
    rcases hgv with hinf | ⟨_, hltX, _⟩
    · have h0 : ofLimb4 pt.x = 0 := congrArg G1Point.x hinf
      rw [h0]; exact bn254FqModulus_pos
    · exact hltX
  have hyr : pt.y.l0 + 2 ^ 80 * pt.y.l1 + 2 ^ 160 * pt.y.l2 + 2 ^ 240 * pt.y.l3 < bn254FqModulus := by
    rw [← hEqY]
    rcases hgv with hinf | ⟨_, _, hltY, _⟩
    · have h0 : ofLimb4 pt.y = 0 := congrArg G1Point.y hinf
      rw [h0]; exact bn254FqModulus_pos
    · exact hltY
  refine ⟨hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, rfl, rfl, rfl, hval, ?_⟩
  let xc : Bn254AffineU80Coord := ⟨pt.x.l0, pt.x.l1, pt.x.l2, pt.x.l3, hx0, hx1, hx2, hx3, hxr⟩
  let yc : Bn254AffineU80Coord := ⟨pt.y.l0, pt.y.l1, pt.y.l2, pt.y.l3, hy0, hy1, hy2, hy3, hyr⟩
  rcases hgv with hinf | ⟨hpinf0, _, _, hnz, _, _⟩
  · have hxZero : xc.toNat = 0 := by
      change pt.x.l0 + 2 ^ 80 * pt.x.l1 + 2 ^ 160 * pt.x.l2 + 2 ^ 240 * pt.x.l3 = 0
      rw [← hEqX]; exact congrArg G1Point.x hinf
    have hyZero : yc.toNat = 0 := by
      change pt.y.l0 + 2 ^ 80 * pt.y.l1 + 2 ^ 160 * pt.y.l2 + 2 ^ 240 * pt.y.l3 = 0
      rw [← hEqY]; exact congrArg G1Point.y hinf
    have hpinf1 : pt.isInf = 1 := congrArg G1Point.isInf hinf
    refine ⟨⟨xc, yc, true, ⟨fun _ => ⟨hxZero, hyZero⟩, fun _ => rfl⟩⟩, ?_, ?_, ?_, ?_⟩
    · exact hEqX.symm
    · exact hEqY.symm
    · simp [hpinf1]
    · simp [Bn254AffineU80Point.words, xc, yc, hpinf1]
  · have hpinf0' : pt.isInf = 0 := hpinf0
    have hNotZero : ¬ (xc.toNat = 0 ∧ yc.toNat = 0) := by
      rintro ⟨hx0', hy0'⟩
      rcases hnz with hnx | hny
      · exact hnx (hEqX.trans hx0')
      · exact hny (hEqY.trans hy0')
    refine ⟨⟨xc, yc, false, ⟨fun hc => absurd hc (by decide), fun hz => absurd hz hNotZero⟩⟩,
      ?_, ?_, ?_, ?_⟩
    · exact hEqX.symm
    · exact hEqY.symm
    · simp [hpinf0']
    · simp [Bn254AffineU80Point.words, xc, yc, hpinf0']

/-- Soundness of `decodeAffineG1BLS12381` on production BLS12-381:
extracts canonical `5 × u80/u61` limb bounds, exact recomposed coordinates `< bls12381FqModulus`,
`g1Validate` (including Bowe prime-order subgroup check), AND a canonical
`Ix.Cert.AiurCompression.Bls12381AffineU80Point` matching `pt`! -/
theorem decodeAffineG1BLS12381_sound {pt : AffineG1BLS12381}
    (h : (decodeAffineG1BLS12381 bls12381PairingParams pt).ok = 1) :
    let d := decodeAffineG1BLS12381 bls12381PairingParams pt
    pt.x.l0 < 2 ^ 80 ∧ pt.x.l1 < 2 ^ 80 ∧ pt.x.l2 < 2 ^ 80 ∧ pt.x.l3 < 2 ^ 80 ∧ pt.x.l4 < 2 ^ 61 ∧
    pt.y.l0 < 2 ^ 80 ∧ pt.y.l1 < 2 ^ 80 ∧ pt.y.l2 < 2 ^ 80 ∧ pt.y.l3 < 2 ^ 80 ∧ pt.y.l4 < 2 ^ 61 ∧
    d.point.x = ofLimb5 pt.x ∧ d.point.y = ofLimb5 pt.y ∧ d.point.isInf = pt.isInf ∧
    g1Validate bls12381PairingParams d.point = true ∧
    ∃ u : Bls12381AffineU80Point,
      u.x.toNat = d.point.x ∧ u.y.toNat = d.point.y ∧
      (if u.infinity then 1 else 0) = d.point.isInf ∧
      u.words = [pt.x.l0, pt.x.l1, pt.x.l2, pt.x.l3, pt.x.l4,
                 pt.y.l0, pt.y.l1, pt.y.l2, pt.y.l3, pt.y.l4, pt.isInf] := by
  have hDecDef : decodeAffineG1BLS12381 bls12381PairingParams pt =
      if (natLtErr pt.x.l0 radix80 + natLtErr pt.x.l1 radix80 + natLtErr pt.x.l2 radix80 +
          natLtErr pt.x.l3 radix80 + natLtErr pt.x.l4 2305843009213693952 +
          natLtErr pt.y.l0 radix80 + natLtErr pt.y.l1 radix80 + natLtErr pt.y.l2 radix80 +
          natLtErr pt.y.l3 radix80 + natLtErr pt.y.l4 2305843009213693952 == 0) = true then
        if g1Validate bls12381PairingParams { x := ofLimb5 pt.x, y := ofLimb5 pt.y, isInf := pt.isInf } = true then
          { ok := 1, point := { x := ofLimb5 pt.x, y := ofLimb5 pt.y, isInf := pt.isInf } }
        else { ok := 0, point := g1Inf }
      else { ok := 0, point := g1Inf } := rfl
  rw [hDecDef] at h ⊢
  split_ifs at h with herr hval
  have hOut :
      (if (natLtErr pt.x.l0 radix80 + natLtErr pt.x.l1 radix80 + natLtErr pt.x.l2 radix80 +
            natLtErr pt.x.l3 radix80 + natLtErr pt.x.l4 2305843009213693952 +
            natLtErr pt.y.l0 radix80 + natLtErr pt.y.l1 radix80 + natLtErr pt.y.l2 radix80 +
            natLtErr pt.y.l3 radix80 + natLtErr pt.y.l4 2305843009213693952 == 0) = true then
        if g1Validate bls12381PairingParams { x := ofLimb5 pt.x, y := ofLimb5 pt.y, isInf := pt.isInf } = true then
          ({ ok := 1, point := { x := ofLimb5 pt.x, y := ofLimb5 pt.y, isInf := pt.isInf } } : DecodeG1Result)
        else { ok := 0, point := g1Inf }
      else { ok := 0, point := g1Inf }) =
      { ok := 1, point := { x := ofLimb5 pt.x, y := ofLimb5 pt.y, isInf := pt.isInf } } := by
    simp only [herr, hval, ↓reduceIte]
  dsimp only
  rw [hOut]
  dsimp only
  have herr' := herr
  simp only [beq_iff_eq, Nat.add_eq_zero_iff, natLtErr_eq_zero_iff] at herr'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hx0, hx1⟩, hx2⟩, hx3⟩, hx4⟩, hy0⟩, hy1⟩, hy2⟩, hy3⟩, hy4⟩ := herr'
  have htb : (2305843009213693952 : Nat) = 2 ^ 61 := by decide
  rw [radix80_eq_pow] at hx0 hx1 hx2 hx3 hy0 hy1 hy2 hy3
  rw [htb] at hx4 hy4
  have hEqX : ofLimb5 pt.x =
      pt.x.l0 + 2 ^ 80 * pt.x.l1 + 2 ^ 160 * pt.x.l2 + 2 ^ 240 * pt.x.l3 + 2 ^ 320 * pt.x.l4 := by
    unfold ofLimb5; rw [radix80_eq_pow]
    exact limb5_recompose_2pow80 pt.x.l0 pt.x.l1 pt.x.l2 pt.x.l3 pt.x.l4
  have hEqY : ofLimb5 pt.y =
      pt.y.l0 + 2 ^ 80 * pt.y.l1 + 2 ^ 160 * pt.y.l2 + 2 ^ 240 * pt.y.l3 + 2 ^ 320 * pt.y.l4 := by
    unfold ofLimb5; rw [radix80_eq_pow]
    exact limb5_recompose_2pow80 pt.y.l0 pt.y.l1 pt.y.l2 pt.y.l3 pt.y.l4
  have hgv := (g1Validate_iff _).mp hval
  have hxr : pt.x.l0 + 2 ^ 80 * pt.x.l1 + 2 ^ 160 * pt.x.l2 + 2 ^ 240 * pt.x.l3 + 2 ^ 320 * pt.x.l4 <
      bls12381FqModulus := by
    rw [← hEqX]
    rcases hgv with hinf | ⟨_, hltX, _⟩
    · have h0 : ofLimb5 pt.x = 0 := congrArg G1Point.x hinf
      rw [h0]; exact bls12381FqModulus_pos
    · exact hltX
  have hyr : pt.y.l0 + 2 ^ 80 * pt.y.l1 + 2 ^ 160 * pt.y.l2 + 2 ^ 240 * pt.y.l3 + 2 ^ 320 * pt.y.l4 <
      bls12381FqModulus := by
    rw [← hEqY]
    rcases hgv with hinf | ⟨_, _, hltY, _⟩
    · have h0 : ofLimb5 pt.y = 0 := congrArg G1Point.y hinf
      rw [h0]; exact bls12381FqModulus_pos
    · exact hltY
  refine ⟨hx0, hx1, hx2, hx3, hx4, hy0, hy1, hy2, hy3, hy4, rfl, rfl, rfl, hval, ?_⟩
  let xc : Bls12381AffineU80Coord := ⟨pt.x.l0, pt.x.l1, pt.x.l2, pt.x.l3, pt.x.l4, hx0, hx1, hx2, hx3, hx4, hxr⟩
  let yc : Bls12381AffineU80Coord := ⟨pt.y.l0, pt.y.l1, pt.y.l2, pt.y.l3, pt.y.l4, hy0, hy1, hy2, hy3, hy4, hyr⟩
  rcases hgv with hinf | ⟨hpinf0, _, _, hnz, _, _⟩
  · have hxZero : xc.toNat = 0 := by
      change pt.x.l0 + 2 ^ 80 * pt.x.l1 + 2 ^ 160 * pt.x.l2 + 2 ^ 240 * pt.x.l3 + 2 ^ 320 * pt.x.l4 = 0
      rw [← hEqX]; exact congrArg G1Point.x hinf
    have hyZero : yc.toNat = 0 := by
      change pt.y.l0 + 2 ^ 80 * pt.y.l1 + 2 ^ 160 * pt.y.l2 + 2 ^ 240 * pt.y.l3 + 2 ^ 320 * pt.y.l4 = 0
      rw [← hEqY]; exact congrArg G1Point.y hinf
    have hpinf1 : pt.isInf = 1 := congrArg G1Point.isInf hinf
    refine ⟨⟨xc, yc, true, ⟨fun _ => ⟨hxZero, hyZero⟩, fun _ => rfl⟩⟩, ?_, ?_, ?_, ?_⟩
    · exact hEqX.symm
    · exact hEqY.symm
    · simp [hpinf1]
    · simp [Bls12381AffineU80Point.words, xc, yc, hpinf1]
  · have hpinf0' : pt.isInf = 0 := hpinf0
    have hNotZero : ¬ (xc.toNat = 0 ∧ yc.toNat = 0) := by
      rintro ⟨hx0', hy0'⟩
      rcases hnz with hnx | hny
      · exact hnx (hEqX.trans hx0')
      · exact hny (hEqY.trans hy0')
    refine ⟨⟨xc, yc, false, ⟨fun hc => absurd hc (by decide), fun hz => absurd hz hNotZero⟩⟩,
      ?_, ?_, ?_, ?_⟩
    · exact hEqX.symm
    · exact hEqY.symm
    · simp [hpinf0']
    · simp [Bls12381AffineU80Point.words, xc, yc, hpinf0']

theorem fListLen_append (a b : FList) : fListLen (fListAppend a b) = fListLen a + fListLen b := by
  induction a with
  | nil => simp [fListAppend, fListLen]
  | cons h t ih => simp [fListAppend, fListLen, ih]; omega

theorem fListLen_toLimbsGeneric (r n x : Nat) : fListLen (toLimbsGeneric r n x) = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [toLimbsGeneric, fListLen, ih]

theorem encodeAffinePairWords_len (c : CurveParams) (A B : G1Point) :
    fListLen (encodeAffinePairWords c A B) = 4 * c.fqLimbCount + 2 := by
  unfold encodeAffinePairWords encodeAffinePointWords
  simp [fListLen_append, fListLen_toLimbsGeneric, fListLen]
  omega

theorem encodeAffinePairWords_len_bn254 (A B : G1Point) :
    fListLen (encodeAffinePairWords bn254CurveParams A B) = 18 :=
  encodeAffinePairWords_len bn254CurveParams A B

theorem encodeAffinePairWords_len_bls12381 (A B : G1Point) :
    fListLen (encodeAffinePairWords bls12381CurveParams A B) = 22 :=
  encodeAffinePairWords_len bls12381CurveParams A B

/-! ### 2.3 BLS12-381 Jacobian Arithmetic & Bowe 2019/814 Prime-Order `G1` Subgroup Soundness -/

private theorem bls12381Fq_ne_two : bls12381FqModulus ≠ 2 := by decide
private theorem bls12381Fq_ne_three : bls12381FqModulus ≠ 3 := by decide
private theorem bls12381Fq_pos : 0 < bls12381FqModulus := bls12381FqModulus_pos

private theorem bls12381EndoBeta_poly :
    ((bls12381EndoBetaNat : ZMod bls12381FqModulus) ^ 2 +
      (bls12381EndoBetaNat : ZMod bls12381FqModulus) + 1) = 0 := by
  have h := bls12381EndoBetaNat_poly_mod
  have hcast : ((bls12381EndoBetaNat * bls12381EndoBetaNat + bls12381EndoBetaNat + 1 : Nat) :
      ZMod bls12381FqModulus) = 0 := by
    rw [← ZMod.natCast_mod, h, Nat.cast_zero]
  simpa [sq, Nat.cast_add, Nat.cast_mul] using hcast

/-- Canonical Jacobian point invariant on BLS12-381 $E(\mathbb{F}_q) : y^2 = x^3 + 4$:
all three coordinates are `< q`, and whenever `z ≠ 0`, $Y^2 = X^3 + 4 Z^6$ in $\mathbb{F}_q$. -/
def G1JacOnBls (R : G1Jac) : Prop :=
  R.x < bls12381FqModulus ∧
  R.y < bls12381FqModulus ∧
  R.z < bls12381FqModulus ∧
  (R.z ≠ 0 →
    (R.y : ZMod bls12381FqModulus) ^ 2 =
      (R.x : ZMod bls12381FqModulus) ^ 3 + 4 * (R.z : ZMod bls12381FqModulus) ^ 6)

/-- Interpret a valid BLS12-381 Jacobian point `(X : Y : Z)` as an affine curve point
`(X/Z², Y/Z³)` in Mathlib's `(bls12381CurveAt bls12381FqModulus).Point`. -/
noncomputable def g1JacToBlsPoint (R : G1Jac) (hR : G1JacOnBls R) :
    (bls12381CurveAt bls12381FqModulus).Point :=
  if hz : R.z = 0 then 0
  else
    let z : ZMod bls12381FqModulus := (R.z : ZMod bls12381FqModulus)
    let x : ZMod bls12381FqModulus := (R.x : ZMod bls12381FqModulus) / z ^ 2
    let y : ZMod bls12381FqModulus := (R.y : ZMod bls12381FqModulus) / z ^ 3
    have hzNe : z ≠ 0 := by
      intro h0
      have hv := congrArg ZMod.val h0
      rw [ZMod.val_natCast_of_lt hR.2.2.1, ZMod.val_zero] at hv
      exact hz hv
    .some x y (bls12381CurveAt_nonsingular_of_eq bls12381Fq_ne_two bls12381Fq_ne_three (by
      have heq := hR.2.2.2 hz
      dsimp only [x, y]
      have hz6 : z ^ 6 ≠ 0 := pow_ne_zero 6 hzNe
      field_simp [hzNe]
      linear_combination heq))

private lemma zmod_bls_cast_eq_zero_iff {a : Nat} (ha : a < bls12381FqModulus) :
    (a : ZMod bls12381FqModulus) = 0 ↔ a = 0 := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_zero] at hv
  · rintro rfl; simp

/-- Soundness of branchless Jacobian doubling `g1JacDouble` on BLS12-381:
preserves `G1JacOnBls` and computes exact curve doubling `2 • P = P + P` in
`(bls12381CurveAt bls12381FqModulus).Point`. -/
theorem g1JacDouble_bls_sound (R : G1Jac) (hR : G1JacOnBls R) :
    ∃ hD : G1JacOnBls (g1JacDouble bls12381FqModulus R),
      g1JacToBlsPoint (g1JacDouble bls12381FqModulus R) hD =
        g1JacToBlsPoint R hR + g1JacToBlsPoint R hR := by
  have hq : 0 < bls12381FqModulus := bls12381Fq_pos
  have h2ne : (2 : ZMod bls12381FqModulus) ≠ 0 := zmod_two_ne_zero bls12381Fq_ne_two
  set X : ZMod bls12381FqModulus := (R.x : ZMod bls12381FqModulus)
  set Y : ZMod bls12381FqModulus := (R.y : ZMod bls12381FqModulus)
  set Z : ZMod bls12381FqModulus := (R.z : ZMod bls12381FqModulus)
  have hx3_lt : (g1JacDouble bls12381FqModulus R).x < bls12381FqModulus := fqSubMod_lt hq _ _
  have hy3_lt : (g1JacDouble bls12381FqModulus R).y < bls12381FqModulus := fqSubMod_lt hq _ _
  have hz3_lt : (g1JacDouble bls12381FqModulus R).z < bls12381FqModulus := fqAddMod_lt hq _ _
  have hx3_cast : ((g1JacDouble bls12381FqModulus R).x : ZMod bls12381FqModulus) =
      9 * X ^ 4 - 8 * X * Y ^ 2 := by
    unfold g1JacDouble
    dsimp only
    simp only [fqSubMod_cast (Nat.le_of_lt (fqAddMod_lt hq _ _)),
      fqSubMod_cast (Nat.le_of_lt (fqMulMod_lt hq _ _)),
      fqAddMod_cast, fqMulMod_cast]
    ring
  have hy3_cast : ((g1JacDouble bls12381FqModulus R).y : ZMod bls12381FqModulus) =
      3 * X ^ 2 * (4 * X * Y ^ 2 - (9 * X ^ 4 - 8 * X * Y ^ 2)) - 8 * Y ^ 4 := by
    unfold g1JacDouble
    dsimp only
    simp only [fqSubMod_cast (Nat.le_of_lt (fqAddMod_lt hq _ _)),
      fqSubMod_cast (Nat.le_of_lt (fqMulMod_lt hq _ _)),
      fqSubMod_cast (Nat.le_of_lt (fqSubMod_lt hq _ _)),
      fqAddMod_cast, fqMulMod_cast]
    ring
  have hz3_cast : ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) = 2 * Y * Z := by
    unfold g1JacDouble
    dsimp only
    simp only [fqAddMod_cast, fqMulMod_cast]
    ring
  by_cases hz : R.z = 0
  · have hZ0 : Z = 0 := by simp [Z, hz]
    have hz3Zero : (g1JacDouble bls12381FqModulus R).z = 0 :=
      (zmod_bls_cast_eq_zero_iff hz3_lt).mp (by rw [hz3_cast, hZ0, mul_zero])
    have hD : G1JacOnBls (g1JacDouble bls12381FqModulus R) :=
      ⟨hx3_lt, hy3_lt, hz3_lt, fun h => absurd hz3Zero h⟩
    refine ⟨hD, ?_⟩
    simp [g1JacToBlsPoint, hz, hz3Zero]
  · have hZNe : Z ≠ 0 := mt (zmod_bls_cast_eq_zero_iff hR.2.2.1).mp hz
    by_cases hy : R.y = 0
    · have hY0 : Y = 0 := by simp [Y, hy]
      have hz3Zero : (g1JacDouble bls12381FqModulus R).z = 0 :=
        (zmod_bls_cast_eq_zero_iff hz3_lt).mp (by rw [hz3_cast, hY0]; ring)
      have hD : G1JacOnBls (g1JacDouble bls12381FqModulus R) :=
        ⟨hx3_lt, hy3_lt, hz3_lt, fun h => absurd hz3Zero h⟩
      refine ⟨hD, ?_⟩
      simp only [g1JacToBlsPoint, hz, hz3Zero, ↓reduceDIte]
      have hyEqNeg : (Y / Z ^ 3 : ZMod bls12381FqModulus) =
          (bls12381CurveAt bls12381FqModulus).negY (X / Z ^ 2) (Y / Z ^ 3) := by
        simp [WeierstrassCurve.Affine.negY, bls12381CurveAt, hY0]
      exact (WeierstrassCurve.Affine.Point.add_of_Y_eq rfl hyEqNeg).symm
    · have hYNe : Y ≠ 0 := mt (zmod_bls_cast_eq_zero_iff hR.2.1).mp hy
      have hz3ZNe : ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ≠ 0 := by
        rw [hz3_cast]; exact mul_ne_zero (mul_ne_zero h2ne hYNe) hZNe
      have hz3Ne : (g1JacDouble bls12381FqModulus R).z ≠ 0 :=
        mt (zmod_bls_cast_eq_zero_iff hz3_lt).mpr hz3ZNe
      have hcurve : Y ^ 2 = X ^ 3 + 4 * Z ^ 6 := hR.2.2.2 hz
      have hns : (bls12381CurveAt bls12381FqModulus).Nonsingular (X / Z ^ 2) (Y / Z ^ 3) :=
        bls12381CurveAt_nonsingular_of_eq bls12381Fq_ne_two bls12381Fq_ne_three (by
          field_simp [hZNe]; linear_combination hcurve)
      have hyNeNeg : (Y / Z ^ 3 : ZMod bls12381FqModulus) ≠
          (bls12381CurveAt bls12381FqModulus).negY (X / Z ^ 2) (Y / Z ^ 3) := by
        simp only [WeierstrassCurve.Affine.negY, bls12381CurveAt, zero_mul, sub_zero]
        intro hyn
        have h2y : (2 : ZMod bls12381FqModulus) * (Y / Z ^ 3) = 0 := by linear_combination hyn
        exact mul_ne_zero h2ne (div_ne_zero hYNe (pow_ne_zero 3 hZNe)) h2y
      have hs : (bls12381CurveAt bls12381FqModulus).slope
          (X / Z ^ 2) (X / Z ^ 2) (Y / Z ^ 3) (Y / Z ^ 3) = (3 * X ^ 2) / (2 * Y * Z) := by
        rw [WeierstrassCurve.Affine.slope]
        have hyNeNeg' : Y / Z ^ 3 ≠ -(Y / Z ^ 3) := by
          simpa [WeierstrassCurve.Affine.negY, bls12381CurveAt] using hyNeNeg
        simp only [↓reduceIte, bls12381CurveAt, WeierstrassCurve.Affine.negY,
          zero_mul, add_zero, sub_zero, hyNeNeg', sub_neg_eq_add]
        have hden : (Y / Z ^ 3 + Y / Z ^ 3 : ZMod bls12381FqModulus) ≠ 0 := by
          have : (Y / Z ^ 3 + Y / Z ^ 3 : ZMod bls12381FqModulus) = 2 * Y / Z ^ 3 := by ring
          rw [this]; exact div_ne_zero (mul_ne_zero h2ne hYNe) (pow_ne_zero 3 hZNe)
        rw [div_eq_div_iff hden (mul_ne_zero (mul_ne_zero h2ne hYNe) hZNe)]
        field_simp [hZNe]; ring
      have h2YZ : (2 : ZMod bls12381FqModulus) * Y * Z ≠ 0 :=
        mul_ne_zero (mul_ne_zero h2ne hYNe) hZNe
      have hxEq : ((g1JacDouble bls12381FqModulus R).x : ZMod bls12381FqModulus) /
            ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 2 =
          (bls12381CurveAt bls12381FqModulus).addX (X / Z ^ 2) (X / Z ^ 2)
            ((bls12381CurveAt bls12381FqModulus).slope
              (X / Z ^ 2) (X / Z ^ 2) (Y / Z ^ 3) (Y / Z ^ 3)) := by
        rw [hx3_cast, hz3_cast, hs]
        unfold WeierstrassCurve.Affine.addX
        simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
        field_simp [h2YZ, hZNe]
        ring
      have hyEq : ((g1JacDouble bls12381FqModulus R).y : ZMod bls12381FqModulus) /
            ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 3 =
          (bls12381CurveAt bls12381FqModulus).addY (X / Z ^ 2) (X / Z ^ 2) (Y / Z ^ 3)
            ((bls12381CurveAt bls12381FqModulus).slope
              (X / Z ^ 2) (X / Z ^ 2) (Y / Z ^ 3) (Y / Z ^ 3)) := by
        rw [hy3_cast, hz3_cast, hs]
        unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
          WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX
        simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
        field_simp [h2YZ, hZNe]
        ring
      have hnsAdd := WeierstrassCurve.Affine.nonsingular_add hns hns (fun h => hyNeNeg h.2)
      have heqAdd :
          ((g1JacDouble bls12381FqModulus R).y : ZMod bls12381FqModulus) ^ 2 =
            ((g1JacDouble bls12381FqModulus R).x : ZMod bls12381FqModulus) ^ 3 +
              4 * ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6 := by
        have haff := (bls12381CurveAt_equation_iff bls12381FqModulus _ _).mp hnsAdd.1
        rw [← hxEq, ← hyEq] at haff
        have hz6 : ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6 ≠ 0 :=
          pow_ne_zero 6 hz3ZNe
        have h1 : (((g1JacDouble bls12381FqModulus R).y : ZMod bls12381FqModulus) /
              ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 3) ^ 2 *
            ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6 =
            ((g1JacDouble bls12381FqModulus R).y : ZMod bls12381FqModulus) ^ 2 := by
          rw [div_pow, show (((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 3) ^ 2 =
              ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6 by ring,
            div_mul_cancel₀ _ hz6]
        have h2 : ((((g1JacDouble bls12381FqModulus R).x : ZMod bls12381FqModulus) /
              ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 2) ^ 3 + 4) *
            ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6 =
            ((g1JacDouble bls12381FqModulus R).x : ZMod bls12381FqModulus) ^ 3 +
              4 * ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6 := by
          rw [add_mul, div_pow, show (((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 2) ^ 3 =
              ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6 by ring,
            div_mul_cancel₀ _ hz6]
        have := congrArg (· * ((g1JacDouble bls12381FqModulus R).z : ZMod bls12381FqModulus) ^ 6) haff
        rwa [h1, h2] at this
      have hD : G1JacOnBls (g1JacDouble bls12381FqModulus R) :=
        ⟨hx3_lt, hy3_lt, hz3_lt, fun _ => heqAdd⟩
      refine ⟨hD, ?_⟩
      simp only [g1JacToBlsPoint, hz, hz3Ne, ↓reduceDIte]
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyNeNeg]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hxEq, hyEq⟩

/-- Soundness of complete Jacobian addition `g1JacAdd` on BLS12-381:
preserves `G1JacOnBls` and computes exact curve addition `P₁ + P₂` in
`(bls12381CurveAt bls12381FqModulus).Point`. -/
theorem g1JacAdd_bls_sound (R1 R2 : G1Jac) (hR1 : G1JacOnBls R1) (hR2 : G1JacOnBls R2) :
    ∃ hA : G1JacOnBls (g1JacAdd bls12381FqModulus R1 R2),
      g1JacToBlsPoint (g1JacAdd bls12381FqModulus R1 R2) hA =
        g1JacToBlsPoint R1 hR1 + g1JacToBlsPoint R2 hR2 := by
  have hq : 0 < bls12381FqModulus := bls12381Fq_pos
  set q := bls12381FqModulus
  have : Fact (Nat.Prime q) := inferInstanceAs (Fact (Nat.Prime bls12381FqModulus))
  by_cases hz1 : R1.z = 0
  · have hAdd : g1JacAdd q R1 R2 = R2 := by
      unfold g1JacAdd; simp [hz1]
    rw [hAdd]
    refine ⟨hR2, ?_⟩
    simp [g1JacToBlsPoint, hz1]
  · by_cases hz2 : R2.z = 0
    · have hAdd : g1JacAdd q R1 R2 = R1 := by
        unfold g1JacAdd; simp [beq_false_of_ne hz1, hz2]
      rw [hAdd]
      refine ⟨hR1, ?_⟩
      simp [g1JacToBlsPoint, hz2]
    · set X1 : ZMod q := (R1.x : ZMod q)
      set Y1 : ZMod q := (R1.y : ZMod q)
      set Z1 : ZMod q := (R1.z : ZMod q)
      set X2 : ZMod q := (R2.x : ZMod q)
      set Y2 : ZMod q := (R2.y : ZMod q)
      set Z2 : ZMod q := (R2.z : ZMod q)
      have hZ1Ne : Z1 ≠ 0 := mt (zmod_bls_cast_eq_zero_iff hR1.2.2.1).mp hz1
      have hZ2Ne : Z2 ≠ 0 := mt (zmod_bls_cast_eq_zero_iff hR2.2.2.1).mp hz2
      have hc1 : Y1 ^ 2 = X1 ^ 3 + 4 * Z1 ^ 6 := hR1.2.2.2 hz1
      have hc2 : Y2 ^ 2 = X2 ^ 3 + 4 * Z2 ^ 6 := hR2.2.2.2 hz2
      set hNat := fqSubMod q (fqMulMod q R2.x (fqMulMod q R1.z R1.z))
        (fqMulMod q R1.x (fqMulMod q R2.z R2.z))
      set rNat := fqSubMod q (fqMulMod q R2.y (fqMulMod q R1.z (fqMulMod q R1.z R1.z)))
        (fqMulMod q R1.y (fqMulMod q R2.z (fqMulMod q R2.z R2.z)))
      have hh_lt : hNat < q := fqSubMod_lt hq _ _
      have hr_lt : rNat < q := fqSubMod_lt hq _ _
      have hh_cast : (hNat : ZMod q) = X2 * Z1 ^ 2 - X1 * Z2 ^ 2 := by
        dsimp only [hNat]
        rw [fqSubMod_cast (Nat.le_of_lt (fqMulMod_lt hq _ _)),
          fqMulMod_cast, fqMulMod_cast, fqMulMod_cast, fqMulMod_cast]
        ring
      have hr_cast : (rNat : ZMod q) = Y2 * Z1 ^ 3 - Y1 * Z2 ^ 3 := by
        dsimp only [rNat]
        rw [fqSubMod_cast (Nat.le_of_lt (fqMulMod_lt hq _ _)),
          fqMulMod_cast, fqMulMod_cast, fqMulMod_cast, fqMulMod_cast,
          fqMulMod_cast, fqMulMod_cast]
        ring
      by_cases hh0 : hNat = 0
      · have hxEq : X1 / Z1 ^ 2 = X2 / Z2 ^ 2 := by
          have hz : X2 * Z1 ^ 2 - X1 * Z2 ^ 2 = 0 := by
            rw [← hh_cast, hh0, Nat.cast_zero]
          rw [div_eq_div_iff (pow_ne_zero 2 hZ1Ne) (pow_ne_zero 2 hZ2Ne)]
          linear_combination -hz
        by_cases hr0 : rNat = 0
        · have hAdd : g1JacAdd q R1 R2 = g1JacDouble q R1 := by
            unfold g1JacAdd
            simp only [beq_false_of_ne hz1, beq_false_of_ne hz2, Bool.false_eq_true, ↓reduceIte]
            change (if (hNat == 0) = true then if (rNat == 0) = true then g1JacDouble q R1 else g1JacInf else _) = _
            simp [hh0, hr0]
          rw [hAdd]
          have hyEq : Y1 / Z1 ^ 3 = Y2 / Z2 ^ 3 := by
            have hz : Y2 * Z1 ^ 3 - Y1 * Z2 ^ 3 = 0 := by
              rw [← hr_cast, hr0, Nat.cast_zero]
            rw [div_eq_div_iff (pow_ne_zero 3 hZ1Ne) (pow_ne_zero 3 hZ2Ne)]
            linear_combination -hz
          have hPeq : g1JacToBlsPoint R1 hR1 = g1JacToBlsPoint R2 hR2 := by
            simp only [g1JacToBlsPoint, hz1, hz2, ↓reduceDIte, WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨hxEq, hyEq⟩
          rw [← hPeq]
          exact g1JacDouble_bls_sound R1 hR1
        · have hAdd : g1JacAdd q R1 R2 = g1JacInf := by
            unfold g1JacAdd
            simp only [beq_false_of_ne hz1, beq_false_of_ne hz2, Bool.false_eq_true, ↓reduceIte]
            change (if (hNat == 0) = true then if (rNat == 0) = true then g1JacDouble q R1 else g1JacInf else _) = _
            simp [hh0, beq_false_of_ne hr0]
          rw [hAdd]
          have hInfOn : G1JacOnBls g1JacInf :=
            ⟨by decide, by decide, by decide, fun h => absurd rfl h⟩
          refine ⟨hInfOn, ?_⟩
          have hyNe : Y1 / Z1 ^ 3 ≠ Y2 / Z2 ^ 3 := by
            intro heq
            have hrz : (rNat : ZMod q) = 0 := by
              rw [hr_cast]
              have hmul : Y1 * Z2 ^ 3 = Y2 * Z1 ^ 3 :=
                (div_eq_div_iff (pow_ne_zero 3 hZ1Ne) (pow_ne_zero 3 hZ2Ne)).mp heq
              linear_combination -hmul
            exact hr0 ((zmod_bls_cast_eq_zero_iff hr_lt).mp hrz)
          have hySqEq : (Y1 / Z1 ^ 3) ^ 2 = (Y2 / Z2 ^ 3) ^ 2 := by
            have h1 : (Y1 / Z1 ^ 3) ^ 2 = (X1 / Z1 ^ 2) ^ 3 + 4 := by
              field_simp [hZ1Ne]; linear_combination hc1
            have h2 : (Y2 / Z2 ^ 3) ^ 2 = (X2 / Z2 ^ 2) ^ 3 + 4 := by
              field_simp [hZ2Ne]; linear_combination hc2
            rw [h1, h2, hxEq]
          have hyNeg : Y1 / Z1 ^ 3 = (bls12381CurveAt q).negY (X2 / Z2 ^ 2) (Y2 / Z2 ^ 3) := by
            simp only [WeierstrassCurve.Affine.negY, bls12381CurveAt, zero_mul, sub_zero]
            have hfac : (Y1 / Z1 ^ 3 - Y2 / Z2 ^ 3) * (Y1 / Z1 ^ 3 + Y2 / Z2 ^ 3) = 0 := by
              linear_combination hySqEq
            rcases mul_eq_zero.mp hfac with hsub | hadd
            · exact absurd (sub_eq_zero.mp hsub) hyNe
            · exact eq_neg_of_add_eq_zero_left hadd
          simp only [g1JacToBlsPoint, g1JacInf, ↓reduceDIte, hz1, hz2]
          exact (WeierstrassCurve.Affine.Point.add_of_Y_eq hxEq hyNeg).symm
      · set H : ZMod q := (hNat : ZMod q)
        set Rr : ZMod q := (rNat : ZMod q)
        set U1 : ZMod q := X1 * Z2 ^ 2
        set S1 : ZMod q := Y1 * Z2 ^ 3
        have hHNe : H ≠ 0 := mt (zmod_bls_cast_eq_zero_iff hh_lt).mp hh0
        have hxNe : X1 / Z1 ^ 2 ≠ X2 / Z2 ^ 2 := by
          intro heq
          have hmul : X1 * Z2 ^ 2 = X2 * Z1 ^ 2 :=
            (div_eq_div_iff (pow_ne_zero 2 hZ1Ne) (pow_ne_zero 2 hZ2Ne)).mp heq
          exact hHNe (by rw [hh_cast]; linear_combination -hmul)
        set res : G1Jac :=
          { x := fqSubMod q (fqSubMod q (fqMulMod q rNat rNat) (fqMulMod q hNat (fqMulMod q hNat hNat)))
              (fqAddMod q (fqMulMod q (fqMulMod q R1.x (fqMulMod q R2.z R2.z)) (fqMulMod q hNat hNat))
                (fqMulMod q (fqMulMod q R1.x (fqMulMod q R2.z R2.z)) (fqMulMod q hNat hNat)))
            y := fqSubMod q
              (fqMulMod q rNat (fqSubMod q
                (fqMulMod q (fqMulMod q R1.x (fqMulMod q R2.z R2.z)) (fqMulMod q hNat hNat))
                (fqSubMod q (fqSubMod q (fqMulMod q rNat rNat) (fqMulMod q hNat (fqMulMod q hNat hNat)))
                  (fqAddMod q (fqMulMod q (fqMulMod q R1.x (fqMulMod q R2.z R2.z)) (fqMulMod q hNat hNat))
                    (fqMulMod q (fqMulMod q R1.x (fqMulMod q R2.z R2.z)) (fqMulMod q hNat hNat))))))
              (fqMulMod q (fqMulMod q R1.y (fqMulMod q R2.z (fqMulMod q R2.z R2.z)))
                (fqMulMod q hNat (fqMulMod q hNat hNat)))
            z := fqMulMod q (fqMulMod q R1.z R2.z) hNat }
        have hAdd : g1JacAdd q R1 R2 = res := by
          unfold g1JacAdd
          simp only [beq_false_of_ne hz1, beq_false_of_ne hz2, Bool.false_eq_true, ↓reduceIte]
          change (if (hNat == 0) = true then _ else res) = res
          simp [beq_false_of_ne hh0]
        rw [hAdd]
        have hx3_lt : res.x < q := fqSubMod_lt hq _ _
        have hy3_lt : res.y < q := fqSubMod_lt hq _ _
        have hz3_lt : res.z < q := fqMulMod_lt hq _ _
        have hx3_cast : (res.x : ZMod q) = Rr ^ 2 - H ^ 3 - 2 * U1 * H ^ 2 := by
          dsimp only [res]
          simp only [fqSubMod_cast (Nat.le_of_lt (fqAddMod_lt hq _ _)),
            fqSubMod_cast (Nat.le_of_lt (fqMulMod_lt hq _ _)),
            fqAddMod_cast, fqMulMod_cast]
          dsimp only [U1, H, Rr, X1, Z2]
          ring
        have hy3_cast : (res.y : ZMod q) =
            Rr * (U1 * H ^ 2 - (Rr ^ 2 - H ^ 3 - 2 * U1 * H ^ 2)) - S1 * H ^ 3 := by
          dsimp only [res]
          simp only [fqSubMod_cast (Nat.le_of_lt (fqAddMod_lt hq _ _)),
            fqSubMod_cast (Nat.le_of_lt (fqMulMod_lt hq _ _)),
            fqSubMod_cast (Nat.le_of_lt (fqSubMod_lt hq _ _)),
            fqAddMod_cast, fqMulMod_cast]
          dsimp only [U1, S1, H, Rr, X1, Y1, Z2]
          ring
        have hz3_cast : (res.z : ZMod q) = Z1 * Z2 * H := by
          dsimp only [res]
          simp only [fqMulMod_cast]
          rfl
        have hz3ZNe : (res.z : ZMod q) ≠ 0 := by
          rw [hz3_cast]; exact mul_ne_zero (mul_ne_zero hZ1Ne hZ2Ne) hHNe
        have hz3Ne : res.z ≠ 0 := mt (zmod_bls_cast_eq_zero_iff hz3_lt).mpr hz3ZNe
        have hns1 : (bls12381CurveAt q).Nonsingular (X1 / Z1 ^ 2) (Y1 / Z1 ^ 3) :=
          bls12381CurveAt_nonsingular_of_eq bls12381Fq_ne_two bls12381Fq_ne_three (by
            field_simp [hZ1Ne]; linear_combination hc1)
        have hns2 : (bls12381CurveAt q).Nonsingular (X2 / Z2 ^ 2) (Y2 / Z2 ^ 3) :=
          bls12381CurveAt_nonsingular_of_eq bls12381Fq_ne_two bls12381Fq_ne_three (by
            field_simp [hZ2Ne]; linear_combination hc2)
        have hs : (bls12381CurveAt q).slope (X1 / Z1 ^ 2) (X2 / Z2 ^ 2) (Y1 / Z1 ^ 3) (Y2 / Z2 ^ 3) =
            Rr / (Z1 * Z2 * H) := by
          rw [WeierstrassCurve.Affine.slope]
          simp only [hxNe, ↓reduceIte]
          have hdxNe : X1 / Z1 ^ 2 - X2 / Z2 ^ 2 ≠ 0 := sub_ne_zero.mpr hxNe
          rw [div_eq_div_iff hdxNe (mul_ne_zero (mul_ne_zero hZ1Ne hZ2Ne) hHNe)]
          have h1 : (Y1 / Z1 ^ 3 - Y2 / Z2 ^ 3) * (Z1 * Z2 * H) = -Rr * H / (Z1 ^ 2 * Z2 ^ 2) := by
            rw [hr_cast]; field_simp [hZ1Ne, hZ2Ne]; ring
          have h2 : Rr * (X1 / Z1 ^ 2 - X2 / Z2 ^ 2) = -Rr * H / (Z1 ^ 2 * Z2 ^ 2) := by
            rw [hh_cast]; field_simp [hZ1Ne, hZ2Ne]; ring
          rw [h1, h2]
        have hZ12H : Z1 * Z2 * H ≠ 0 := mul_ne_zero (mul_ne_zero hZ1Ne hZ2Ne) hHNe
        have hxEq : (res.x : ZMod q) / (res.z : ZMod q) ^ 2 =
            (bls12381CurveAt q).addX (X1 / Z1 ^ 2) (X2 / Z2 ^ 2)
              ((bls12381CurveAt q).slope (X1 / Z1 ^ 2) (X2 / Z2 ^ 2) (Y1 / Z1 ^ 3) (Y2 / Z2 ^ 3)) := by
          rw [hx3_cast, hz3_cast, hs]
          unfold WeierstrassCurve.Affine.addX
          simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
          have hX2 : X2 * Z1 ^ 2 = U1 + H := by rw [hh_cast]; dsimp only [U1]; ring
          field_simp [hZ12H, hZ1Ne, hZ2Ne]
          dsimp only [U1] at hX2 ⊢
          linear_combination H ^ 2 * hX2
        have hyEq : (res.y : ZMod q) / (res.z : ZMod q) ^ 3 =
            (bls12381CurveAt q).addY (X1 / Z1 ^ 2) (X2 / Z2 ^ 2) (Y1 / Z1 ^ 3)
              ((bls12381CurveAt q).slope (X1 / Z1 ^ 2) (X2 / Z2 ^ 2) (Y1 / Z1 ^ 3) (Y2 / Z2 ^ 3)) := by
          rw [hy3_cast, hz3_cast, hs]
          unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
            WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX
          simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]
          have hX2 : X2 * Z1 ^ 2 = U1 + H := by rw [hh_cast]; dsimp only [U1]; ring
          field_simp [hZ12H, hZ1Ne, hZ2Ne]
          dsimp only [U1, S1] at hX2 ⊢
          linear_combination -Rr * H ^ 2 * hX2
        have hnsAdd := WeierstrassCurve.Affine.nonsingular_add hns1 hns2 (fun h => hxNe h.1)
        have heqAdd : (res.y : ZMod q) ^ 2 = (res.x : ZMod q) ^ 3 + 4 * (res.z : ZMod q) ^ 6 := by
          have haff := (bls12381CurveAt_equation_iff q _ _).mp hnsAdd.1
          rw [← hxEq, ← hyEq] at haff
          have hz6 : (res.z : ZMod q) ^ 6 ≠ 0 := pow_ne_zero 6 hz3ZNe
          have h1 : ((res.y : ZMod q) / (res.z : ZMod q) ^ 3) ^ 2 * (res.z : ZMod q) ^ 6 =
              (res.y : ZMod q) ^ 2 := by
            rw [div_pow, show ((res.z : ZMod q) ^ 3) ^ 2 = (res.z : ZMod q) ^ 6 by ring,
              div_mul_cancel₀ _ hz6]
          have h2 : (((res.x : ZMod q) / (res.z : ZMod q) ^ 2) ^ 3 + 4) * (res.z : ZMod q) ^ 6 =
              (res.x : ZMod q) ^ 3 + 4 * (res.z : ZMod q) ^ 6 := by
            rw [add_mul, div_pow, show ((res.z : ZMod q) ^ 2) ^ 3 = (res.z : ZMod q) ^ 6 by ring,
              div_mul_cancel₀ _ hz6]
          have := congrArg (· * (res.z : ZMod q) ^ 6) haff
          rwa [h1, h2] at this
        have hA : G1JacOnBls res := ⟨hx3_lt, hy3_lt, hz3_lt, fun _ => heqAdd⟩
        refine ⟨hA, ?_⟩
        simp only [g1JacToBlsPoint, hz1, hz2, hz3Ne, ↓reduceDIte]
        rw [WeierstrassCurve.Affine.Point.add_of_X_ne hxNe]
        simp only [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨hxEq, hyEq⟩

/-- Structural induction soundness for MSB-to-LSB Jacobian scalar multiplication `g1JacScalarMulMsb`
on BLS12-381: after `n` steps with `bitMask = 2^n / 2`, the output represents
`2^n • acc + (k % 2^n) • base` in `(bls12381CurveAt bls12381FqModulus).Point`. -/
theorem g1JacScalarMulMsb_bls_sound (k : Nat) :
    ∀ (n : Nat) (base acc : G1Jac) (hB : G1JacOnBls base) (hA : G1JacOnBls acc),
      ∃ hOut : G1JacOnBls (g1JacScalarMulMsb bls12381FqModulus k n (2 ^ n / 2) base acc),
        g1JacToBlsPoint (g1JacScalarMulMsb bls12381FqModulus k n (2 ^ n / 2) base acc) hOut =
          (2 ^ n) • g1JacToBlsPoint acc hA + (k % 2 ^ n) • g1JacToBlsPoint base hB
  | 0, base, acc, hB, hA => by
    refine ⟨hA, ?_⟩
    simp [g1JacScalarMulMsb, Nat.mod_one]
  | n + 1, base, acc, hB, hA => by
    unfold g1JacScalarMulMsb
    have hmask : 2 ^ (n + 1) / 2 = 2 ^ n := by
      rw [Nat.pow_succ]; exact Nat.mul_div_cancel _ (by decide)
    rw [hmask]
    obtain ⟨hDbl, hDblEq⟩ := g1JacDouble_bls_sound acc hA
    have hbit_decomp : k % 2 ^ (n + 1) = 2 ^ n * ((k / 2 ^ n) % 2) + k % 2 ^ n := by
      have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      have h1 := Nat.div_add_mod k (2 ^ n)
      have h2 := Nat.div_add_mod (k / 2 ^ n) 2
      have h3 : k % (2 ^ n * 2) = 2 ^ n * ((k / 2 ^ n) % 2) + k % 2 ^ n := by
        have hlt : 2 ^ n * ((k / 2 ^ n) % 2) + k % 2 ^ n < 2 ^ n * 2 := by
          have hm1 : k % 2 ^ n < 2 ^ n := Nat.mod_lt k hpos
          have hm2 : (k / 2 ^ n) % 2 < 2 := Nat.mod_lt _ (by decide)
          rcases (by omega : (k / 2 ^ n) % 2 = 0 ∨ (k / 2 ^ n) % 2 = 1) with h0 | h0 <;>
            simp [h0] <;> omega
        have heq : k = (2 ^ n * 2) * (k / 2 ^ n / 2) + (2 ^ n * ((k / 2 ^ n) % 2) + k % 2 ^ n) := by
          calc k = 2 ^ n * (k / 2 ^ n) + k % 2 ^ n := h1.symm
            _ = 2 ^ n * (2 * (k / 2 ^ n / 2) + (k / 2 ^ n) % 2) + k % 2 ^ n := by rw [h2]
            _ = (2 ^ n * 2) * (k / 2 ^ n / 2) + (2 ^ n * ((k / 2 ^ n) % 2) + k % 2 ^ n) := by ring
        conv_lhs => rw [heq]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rwa [hpow]
    by_cases hbit : (k / 2 ^ n) % 2 = 1
    · simp only [hbit, beq_self_eq_true, ↓reduceIte]
      obtain ⟨hAdd, hAddEq⟩ := g1JacAdd_bls_sound _ base hDbl hB
      obtain ⟨hOut, hOutEq⟩ := g1JacScalarMulMsb_bls_sound k n base _ hB hAdd
      refine ⟨hOut, ?_⟩
      rw [hOutEq, hAddEq, hDblEq, hbit_decomp, hbit, Nat.mul_one]
      simp only [nsmul_add, add_nsmul]
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; ring
      rw [h2, add_nsmul]
      abel
    · have hbit0 : (k / 2 ^ n) % 2 = 0 := by omega
      have hbitb : ((k / 2 ^ n) % 2 == 1) = false := beq_false_of_ne hbit
      simp only [hbitb, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hOut, hOutEq⟩ := g1JacScalarMulMsb_bls_sound k n base _ hB hDbl
      refine ⟨hOut, ?_⟩
      rw [hOutEq, hDblEq, hbit_decomp, hbit0, Nat.mul_zero, Nat.zero_add]
      simp only [nsmul_add]
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; ring
      rw [h2, add_nsmul]

/-- **Bowe 2019/814 Prime-Order `G1` Subgroup Check Soundness (`bls12381_g1Validate_prime_order`):**
Whenever `PairingPure.g1Validate bls12381PairingParams P = true`,
1. `P` is either canonical infinity `{ x := 0, y := 0, isInf := 1 }` or a canonical finite
   on-curve point (`P.x < q`, `P.y < q`, `(P.x, P.y) ≠ (0, 0)`, `y² ≡ x³ + 4 (mod q)`),
2. Its curve point `P_aff : (bls12381CurveAt bls12381FqModulus).Point` satisfies the exact
   Bowe endomorphism subgroup identity `(bls12381Seed ^ 2) • P_aff = -ψ(P_aff)`, and
3. Unconditionally, `bls12381FrModulus • P_aff = 0` (`P_aff ∈ E(𝔽_q)[r]`). -/
theorem bls12381_g1Validate_prime_order {P : G1Point}
    (h : g1Validate bls12381PairingParams P = true) :
    (P = g1Inf ∨
      (P.isInf = 0 ∧ P.x < bls12381FqModulus ∧ P.y < bls12381FqModulus ∧
        (P.x ≠ 0 ∨ P.y ≠ 0) ∧
        (P.y * P.y) % bls12381FqModulus = (P.x * P.x * P.x + 4) % bls12381FqModulus)) ∧
    ∃ P_aff : (bls12381CurveAt bls12381FqModulus).Point,
      (P = g1Inf → P_aff = 0) ∧
      (P.isInf = 0 →
        ∃ hns, P_aff = .some (P.x : ZMod bls12381FqModulus) (P.y : ZMod bls12381FqModulus) hns) ∧
      (bls12381Seed ^ 2) • P_aff =
        -(bls12381EndoAt bls12381FqModulus bls12381Fq_ne_two bls12381Fq_ne_three
            (bls12381EndoBetaNat : ZMod bls12381FqModulus) bls12381EndoBeta_poly P_aff) ∧
      bls12381FrModulus • P_aff = 0 := by
  have hgv := (g1Validate_iff P).mp h
  rcases hgv with rfl | ⟨hinf0, hxlt, hylt, hnz, hcurve, hsub⟩
  · refine ⟨Or.inl rfl, 0, fun _ => rfl, fun h0 => by simp [g1Inf] at h0, ?_, ?_⟩
    · simp [bls12381EndoAt]
    · simp
  · have hqEq : bls12381PairingParams.curve.fqMod = bls12381FqModulus := rfl
    have hbEq : bls12381PairingParams.curve.curveB = 4 := rfl
    rw [hqEq] at hxlt hylt hcurve
    rw [hbEq] at hcurve
    refine ⟨Or.inr ⟨hinf0, hxlt, hylt, hnz, hcurve⟩, ?_⟩
    have hcurveZ : (P.y : ZMod bls12381FqModulus) ^ 2 = (P.x : ZMod bls12381FqModulus) ^ 3 + 4 := by
      have hcast : ((P.y * P.y : Nat) : ZMod bls12381FqModulus) =
          ((P.x * P.x * P.x + 4 : Nat) : ZMod bls12381FqModulus) := by
        rw [← ZMod.natCast_mod, hcurve, ZMod.natCast_mod]
      simpa [pow_two, pow_succ, Nat.cast_mul, Nat.cast_add, mul_assoc] using hcast
    have hns : (bls12381CurveAt bls12381FqModulus).Nonsingular
        (P.x : ZMod bls12381FqModulus) (P.y : ZMod bls12381FqModulus) :=
      bls12381CurveAt_nonsingular_of_eq bls12381Fq_ne_two bls12381Fq_ne_three hcurveZ
    let P_aff : (bls12381CurveAt bls12381FqModulus).Point :=
      .some (P.x : ZMod bls12381FqModulus) (P.y : ZMod bls12381FqModulus) hns
    have h1lt : 1 < bls12381FqModulus := by decide
    have hPJac : G1JacOnBls { x := P.x, y := P.y, z := 1 } :=
      ⟨hxlt, hylt, h1lt, fun _ => by simpa using hcurveZ⟩
    have hPJacEq : g1JacToBlsPoint { x := P.x, y := P.y, z := 1 } hPJac = P_aff := by
      simp [g1JacToBlsPoint, P_aff]
    unfold g1InSubgroup at hsub
    have hisBn : bls12381PairingParams.isBn = 0 := rfl
    have hloopBits : bls12381PairingParams.loopBits - 1 = 63 := rfl
    have hloopTop : bls12381PairingParams.loopTopPow2 / 2 = 2 ^ 63 / 2 := by decide
    have hloopExp : bls12381PairingParams.loopExp = bls12381Seed := rfl
    have hbetaEq : bls12381PairingParams.g1EndoBeta = bls12381EndoBetaNat := rfl
    have hseedSplit : 2 ^ 63 + bls12381Seed % 2 ^ 63 = bls12381Seed := by decide
    rw [hinf0, hisBn, hqEq, hloopExp, hloopBits, hloopTop, hbetaEq] at hsub
    simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte] at hsub
    set xP := g1JacScalarMulMsb bls12381FqModulus bls12381Seed 63 (2 ^ 63 / 2)
      { x := P.x, y := P.y, z := 1 } { x := P.x, y := P.y, z := 1 }
    set x2P := g1JacScalarMulMsb bls12381FqModulus bls12381Seed 63 (2 ^ 63 / 2) xP xP
    obtain ⟨hxPOn, hxPEq⟩ :=
      g1JacScalarMulMsb_bls_sound bls12381Seed 63 _ _ hPJac hPJac
    obtain ⟨hx2POn, hx2PEq⟩ :=
      g1JacScalarMulMsb_bls_sound bls12381Seed 63 xP xP hxPOn hxPOn
    have hxP_aff : g1JacToBlsPoint xP hxPOn = bls12381Seed • P_aff := by
      rw [hxPEq, hPJacEq, ← add_smul, hseedSplit]
    have hx2P_aff : g1JacToBlsPoint x2P hx2POn = (bls12381Seed ^ 2) • P_aff := by
      rw [hx2PEq, ← add_smul, hseedSplit, hxP_aff, smul_smul, ← sq]
    split_ifs at hsub with hz0
    have hx2PzNe : x2P.z ≠ 0 := by
      intro h0; rw [h0] at hz0; simp at hz0
    simp only [beq_iff_eq, Nat.add_eq_zero_iff] at hsub
    have hxEqNat : x2P.x =
        fqMulMod bls12381FqModulus (fqMulMod bls12381FqModulus bls12381EndoBetaNat P.x)
          (fqMulMod bls12381FqModulus x2P.z x2P.z) :=
      (natAbsDiff_eq_zero_iff _ _).mp hsub.1
    have hyEqNat : x2P.y =
        fqMulMod bls12381FqModulus (fqNeg bls12381FqModulus P.y)
          (fqMulMod bls12381FqModulus (fqMulMod bls12381FqModulus x2P.z x2P.z) x2P.z) :=
      (natAbsDiff_eq_zero_iff _ _).mp hsub.2
    have hZNe : (x2P.z : ZMod bls12381FqModulus) ≠ 0 :=
      mt (zmod_bls_cast_eq_zero_iff hx2POn.2.2.1).mp hx2PzNe
    have hXCast : (x2P.x : ZMod bls12381FqModulus) / (x2P.z : ZMod bls12381FqModulus) ^ 2 =
        (bls12381EndoBetaNat : ZMod bls12381FqModulus) * (P.x : ZMod bls12381FqModulus) := by
      rw [hxEqNat, fqMulMod_cast, fqMulMod_cast, fqMulMod_cast]
      field_simp [hZNe]
    have hYCast : (x2P.y : ZMod bls12381FqModulus) / (x2P.z : ZMod bls12381FqModulus) ^ 3 =
        -(P.y : ZMod bls12381FqModulus) := by
      rw [hyEqNat, fqMulMod_cast, fqNeg_cast (Nat.le_of_lt hylt), fqMulMod_cast, fqMulMod_cast]
      field_simp [hZNe]
    have hEndo : (bls12381Seed ^ 2) • P_aff =
        -(bls12381EndoAt bls12381FqModulus bls12381Fq_ne_two bls12381Fq_ne_three
            (bls12381EndoBetaNat : ZMod bls12381FqModulus) bls12381EndoBeta_poly P_aff) := by
      rw [← hx2P_aff]
      unfold g1JacToBlsPoint
      simp only [hx2PzNe, ↓reduceDIte]
      dsimp only [P_aff, bls12381EndoAt]
      rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
      simp only [WeierstrassCurve.Affine.negY, bls12381CurveAt, zero_mul, sub_zero]
      exact ⟨hXCast, hYCast⟩
    have hOrder := order_r_of_endo_eq_at bls12381FqModulus bls12381Fq_ne_two bls12381Fq_ne_three
      (bls12381EndoBetaNat : ZMod bls12381FqModulus) bls12381EndoBeta_poly P_aff hEndo
    exact ⟨P_aff, fun hinf => by rw [hinf] at hinf0; simp [g1Inf] at hinf0,
      fun _ => ⟨hns, rfl⟩, hEndo, hOrder⟩

/-! ### 2.4 Concrete BLS12-381 Cofactor & 3-Torsion Negative Controls -/

/-- Exact non-subgroup torsion witness from `PairingPure.lean` & `KzgWire.lean`:
lies on $E(\mathbb{F}_q) : y^2 = x^3 + 4$ yet outside the prime-order subgroup $E(\mathbb{F}_q)[r]$. -/
def bls12381TorsionWitness : G1Point :=
  { x := 4
    y := 1630892974828014537729259858097113969650871260980656934049590190201941782487224876496582135785777461178964897591404
    isInf := 0 }

/-- Elementary 3-torsion witness `(0, 2)` on BLS12-381 $E(\mathbb{F}_q) : y^2 = x^3 + 4$. -/
def bls12381ThreeTorsionZeroTwo : G1Point :=
  { x := 0, y := 2, isInf := 0 }

/-- Concrete 3-torsion witness on the small BLS12 circuit curve ($q = 727, r = 241, h_1 = 3$). -/
def bls12381CircuitTorsionWitness : G1Point :=
  { x := 1, y := 673, isInf := 0 }

set_option maxRecDepth 20000 in
/-- Kernel-verified rejection of the concrete BLS12-381 torsion witness from `PairingPure.lean`
and `KzgWire.lean` across `g1InSubgroup`, `g1Validate`, `g1SubgroupCheck`, `g1ValidPoint`, and
`pairingCheckAffineBLS12381`. -/
theorem bls12381_torsion_witness_rejected :
    g1OnCurve bls12381CurveParams bls12381TorsionWitness = true ∧
    g1InSubgroup bls12381PairingParams bls12381TorsionWitness = false ∧
    g1Validate bls12381PairingParams bls12381TorsionWitness = false ∧
    g1SubgroupCheck bls12381CurveParams bls12381TorsionWitness = false ∧
    g1ValidPoint bls12381CurveParams bls12381TorsionWitness = false ∧
    pairingCheckAffineBLS12381 bls12381PairingParams
      (encodeAffinePairBLS12381 radix80 bls12381TorsionWitness
        (g1Neg bls12381CurveParams bls12381TorsionWitness))
      bls12381PairingParams.g2Gen bls12381PairingParams.g2Gen fp12One = 0 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Algebraic rejection of the 3-torsion point `(0, 2)` on BLS12-381 $y^2 = x^3 + 4$:
proved directly from `bls12381_g1Validate_prime_order` (since `[3](0,2) = O` and `r ≡ 1 (mod 3)`,
so `[r](0,2) = (0,2) ≠ O`). -/
theorem bls12381_threeTorsion_zero_two_rejected :
    g1OnCurve bls12381CurveParams bls12381ThreeTorsionZeroTwo = true ∧
    g1Validate bls12381PairingParams bls12381ThreeTorsionZeroTwo = false := by
  refine ⟨by decide, ?_⟩
  cases h : g1Validate bls12381PairingParams bls12381ThreeTorsionZeroTwo with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨_, P_aff, _, hfin, _, hr⟩ := bls12381_g1Validate_prime_order h
    obtain ⟨hns, hPeq⟩ := hfin rfl
    have h2ne : (2 : ZMod bls12381FqModulus) ≠ 0 := zmod_two_ne_zero bls12381Fq_ne_two
    have hyNeNeg : (2 : ZMod bls12381FqModulus) ≠ (bls12381CurveAt bls12381FqModulus).negY 0 2 := by
      simp only [WeierstrassCurve.Affine.negY, bls12381CurveAt, zero_mul, sub_zero]
      intro hyn
      have h4 : (2 : ZMod bls12381FqModulus) * 2 = 0 := by linear_combination hyn
      exact mul_ne_zero h2ne h2ne h4
    have h2P : P_aff + P_aff = -P_aff := by
      rw [hPeq]
      simp only [bls12381ThreeTorsionZeroTwo, Nat.cast_zero, Nat.cast_ofNat]
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hyNeNeg,
        WeierstrassCurve.Affine.Point.neg_some]
      simp only [WeierstrassCurve.Affine.Point.some.injEq]
      have hs0 : (bls12381CurveAt bls12381FqModulus).slope 0 0 2 2 = 0 := by
        rw [WeierstrassCurve.Affine.slope]
        simp [WeierstrassCurve.Affine.negY, bls12381CurveAt]
      constructor
      · rw [hs0]; unfold WeierstrassCurve.Affine.addX
        simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]; ring
      · rw [hs0]; unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY
          WeierstrassCurve.Affine.negAddY WeierstrassCurve.Affine.addX
        simp only [bls12381CurveAt, zero_mul, add_zero, sub_zero]; ring
    have h3P : (3 : Nat) • P_aff = 0 := by
      change (2 + 1) • P_aff = 0
      rw [add_smul, two_smul, one_smul, h2P, neg_add_cancel]
    have hrmod : bls12381FrModulus = (bls12381FrModulus / 3) * 3 + 1 := by decide
    rw [hrmod, add_smul, mul_smul, h3P, nsmul_zero, zero_add, one_smul] at hr
    rw [hPeq] at hr
    cases hr

/-- Kernel-verified rejection of the 3-torsion witness on the small BLS12 circuit curve ($h_1 = 3$). -/
theorem bls12381_circuit_torsion_rejected :
    g1OnCurve bls12381CircuitPairingParams.curve bls12381CircuitTorsionWitness = true ∧
    g1InSubgroup bls12381CircuitPairingParams bls12381CircuitTorsionWitness = false ∧
    g1Validate bls12381CircuitPairingParams bls12381CircuitTorsionWitness = false := by
  refine ⟨by decide, by decide, by decide⟩

end CurveAndSubgroup

/-! ## Section 3: Optimal Ate Miller Loop & Residue-Witnessed Final Exponentiation Soundness -/

section MillerLoopAndFinalExp

/-! ### 3.1 Miller Loop Canonicality, Infinity Identity & Prepared-Line Equivalence -/

theorem fp12Sqr_one {q : Nat} (hq : 1 < q) (xi0 : Nat) :
    fp12Sqr q xi0 fp12One = fp12One := by
  have hqPos : 0 < q := by omega
  have : NeZero q := ⟨by omega⟩
  apply fp12ToZMod_inj (xi0 := xi0) (fp12Sqr_canonical hqPos xi0 fp12One) (fp12One_canonical hq)
  rw [fp12Sqr_hom hqPos xi0 (fp12One_canonical hq), fp12ToZMod_one, one_mul]

theorem fp12Conj_one {q : Nat} : fp12Conj q fp12One = fp12One := by
  simp [fp12Conj, fp12One, fp6Neg, fp6Zero, fp2Neg, fp2Zero, fqNeg, fqSubMod]

theorem evalLine_canonical {q : Nat} (hq : 0 < q) (xi0 isBn : Nat) {f : Fp12}
    (hf : fp12Canonical q f = true) (coeff : EllCoeff) (P : G1Point) :
    fp12Canonical q (evalLine q xi0 isBn f coeff P) = true := by
  unfold evalLine
  split_ifs
  · exact hf
  · exact fp12MulBy034_canonical hq xi0 _ _ _ _
  · exact fp12MulBy014_canonical hq xi0 _ _ _ _

theorem doubleAndEval_canonical {q : Nat} (hq : 0 < q) (xi0 twoInv isBn qIsInf : Nat)
    (bTwist : Fp2) (P : G1Point) (T : G2Proj) {f : Fp12} (hf : fp12Canonical q f = true) :
    fp12Canonical q (doubleAndEval q xi0 twoInv isBn qIsInf bTwist P T f).f = true := by
  unfold doubleAndEval
  split_ifs
  · exact evalLine_canonical hq xi0 isBn hf _ P
  · exact hf
  · exact hf

theorem addAndEval_canonical {q : Nat} (hq : 0 < q) (xi0 isBn : Nat)
    (P : G1Point) (Q : G2Point) (T : G2Proj) {f : Fp12} (hf : fp12Canonical q f = true) :
    fp12Canonical q (addAndEval q xi0 isBn P Q T f).f = true := by
  unfold addAndEval
  split_ifs
  · exact evalLine_canonical hq xi0 isBn hf _ P
  · exact hf
  · exact hf

theorem applyBnFrobLines_canonical {q : Nat} (hq : 0 < q) (xi0 : Nat)
    (twistQX twistQY : Fp2) {f : Fp12} (hf : fp12Canonical q f = true)
    (T : G2Proj) (P : G1Point) (Q : G2Point) :
    fp12Canonical q (applyBnFrobLines q xi0 twistQX twistQY f T P Q) = true := by
  unfold applyBnFrobLines
  split_ifs
  · exact evalLine_canonical hq xi0 1 (evalLine_canonical hq xi0 1 hf _ P) _ P
  · exact hf
  · exact hf

theorem millerLoop2Walk_canonical (p : PairingParams) (hq : 0 < p.curve.fqMod)
    (P0 P1 : G1Point) (Q0 negQ0 Q1 negQ1 : G2Point) :
    ∀ (digits : BitList) (st : MillerState),
      fp12Canonical p.curve.fqMod st.f = true →
      fp12Canonical p.curve.fqMod (millerLoop2Walk p digits P0 P1 Q0 negQ0 Q1 negQ1 st).f = true
  | .nil, st, hf => hf
  | .cons digit rest, st, _ => by
    unfold millerLoop2Walk
    dsimp only
    have hf0 := fp12Sqr_canonical hq p.xi0 st.f
    have ho0 := doubleAndEval_canonical hq p.xi0 p.twoInv p.isBn Q0.isInf p.bTwist P0 st.t0 hf0
    have ho1 := doubleAndEval_canonical hq p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 ho0
    split_ifs
    · exact millerLoop2Walk_canonical p hq P0 P1 Q0 negQ0 Q1 negQ1 rest _
        (addAndEval_canonical hq p.xi0 p.isBn P1 Q1 _ (addAndEval_canonical hq p.xi0 p.isBn P0 Q0 _ ho1))
    · exact millerLoop2Walk_canonical p hq P0 P1 Q0 negQ0 Q1 negQ1 rest _
        (addAndEval_canonical hq p.xi0 p.isBn P1 negQ1 _ (addAndEval_canonical hq p.xi0 p.isBn P0 negQ0 _ ho1))
    · exact millerLoop2Walk_canonical p hq P0 P1 Q0 negQ0 Q1 negQ1 rest _ ho1

theorem millerLoop2FinishBn_canonical (p : PairingParams) (hq : 0 < p.curve.fqMod)
    (P0 P1 : G1Point) (Q0 Q1 : G2Point) (t0 t1 : G2Proj) {f : Fp12}
    (hf : fp12Canonical p.curve.fqMod f = true) :
    fp12Canonical p.curve.fqMod (millerLoop2FinishBn p P0 P1 Q0 Q1 t0 t1 f) = true := by
  unfold millerLoop2FinishBn
  split_ifs
  · exact applyBnFrobLines_canonical hq p.xi0 _ _ (applyBnFrobLines_canonical hq p.xi0 _ _ hf t0 P0 Q0) t1 P1 Q1
  · exact hf

theorem millerLoop2Finalize_canonical (p : PairingParams) (hq : 0 < p.curve.fqMod)
    (P0 P1 : G1Point) (Q0 Q1 : G2Point) {st : MillerState}
    (hf : fp12Canonical p.curve.fqMod st.f = true) :
    fp12Canonical p.curve.fqMod (millerLoop2Finalize p P0 P1 Q0 Q1 st) = true := by
  unfold millerLoop2Finalize
  split_ifs
  · exact millerLoop2FinishBn_canonical p hq P0 P1 Q0 Q1 st.t0 st.t1 (fp12Conj_canonical hq hf)
  · exact millerLoop2FinishBn_canonical p hq P0 P1 Q0 Q1 st.t0 st.t1 hf

/-- `millerLoop2` always returns a canonical `Fp12` element (`< q` in all 12 coordinates). -/
theorem millerLoop2_canonical (p : PairingParams) (hq : 1 < p.curve.fqMod) (digits : BitList)
    (P0 : G1Point) (Q0 : G2Point) (P1 : G1Point) (Q1 : G2Point) :
    fp12Canonical p.curve.fqMod (millerLoop2 p digits P0 Q0 P1 Q1) = true := by
  have hqPos : 0 < p.curve.fqMod := by omega
  unfold millerLoop2
  exact millerLoop2Finalize_canonical p hqPos P0 P1 Q0 Q1
    (millerLoop2Walk_canonical p hqPos P0 P1 Q0 _ Q1 _ digits _ (fp12One_canonical hq))

theorem millerLoop2BinaryWalk_canonical (p : PairingParams) (hq : 0 < p.curve.fqMod)
    (P0 P1 : G1Point) (Q0 Q1 : G2Point) :
    ∀ (fuel bitMask : Nat) (st : MillerState),
      fp12Canonical p.curve.fqMod st.f = true →
      fp12Canonical p.curve.fqMod (millerLoop2BinaryWalk p fuel bitMask P0 P1 Q0 Q1 st).f = true
  | 0, _, st, hf => hf
  | fuel + 1, bitMask, st, _ => by
    unfold millerLoop2BinaryWalk
    dsimp only
    have hf0 := fp12Sqr_canonical hq p.xi0 st.f
    have ho0 := doubleAndEval_canonical hq p.xi0 p.twoInv p.isBn Q0.isInf p.bTwist P0 st.t0 hf0
    have ho1 := doubleAndEval_canonical hq p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 ho0
    split_ifs
    · exact millerLoop2BinaryWalk_canonical p hq P0 P1 Q0 Q1 fuel (bitMask / 2) _
        (addAndEval_canonical hq p.xi0 p.isBn P1 Q1 _ (addAndEval_canonical hq p.xi0 p.isBn P0 Q0 _ ho1))
    · exact millerLoop2BinaryWalk_canonical p hq P0 P1 Q0 Q1 fuel (bitMask / 2) _ ho1

/-- `millerLoop2Binary` always returns a canonical `Fp12` element (`< q` in all 12 coordinates). -/
theorem millerLoop2Binary_canonical (p : PairingParams) (hq : 1 < p.curve.fqMod)
    (P0 : G1Point) (Q0 : G2Point) (P1 : G1Point) (Q1 : G2Point) :
    fp12Canonical p.curve.fqMod (millerLoop2Binary p P0 Q0 P1 Q1) = true := by
  have hqPos : 0 < p.curve.fqMod := by omega
  unfold millerLoop2Binary
  exact millerLoop2Finalize_canonical p hqPos P0 P1 Q0 Q1
    (millerLoop2BinaryWalk_canonical p hqPos P0 P1 Q0 Q1 _ _ _ (fp12One_canonical hq))

private theorem millerLoop2Walk_inf_inf (p : PairingParams) (hq : 1 < p.curve.fqMod)
    (Q0 negQ0 Q1 negQ1 : G2Point) :
    ∀ (digits : BitList) (t0 t1 : G2Proj),
      (millerLoop2Walk p digits g1Inf g1Inf Q0 negQ0 Q1 negQ1 { f := fp12One, t0, t1 }).f = fp12One
  | .nil, _, _ => rfl
  | .cons digit rest, t0, t1 => by
    unfold millerLoop2Walk
    dsimp only
    rw [fp12Sqr_one hq p.xi0]
    have hD0 : doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q0.isInf p.bTwist g1Inf t0 fp12One =
        { f := fp12One, t := t0 } := by simp [doubleAndEval, g1Inf]
    have hD1 : doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist g1Inf t1 fp12One =
        { f := fp12One, t := t1 } := by simp [doubleAndEval, g1Inf]
    have hA : ∀ Q T, addAndEval p.curve.fqMod p.xi0 p.isBn g1Inf Q T fp12One =
        { f := fp12One, t := T } := fun Q T => by simp [addAndEval, g1Inf]
    rw [hD0, hD1]
    split_ifs
    · rw [hA Q0 t0, hA Q1 t1]; exact millerLoop2Walk_inf_inf p hq Q0 negQ0 Q1 negQ1 rest t0 t1
    · rw [hA negQ0 t0, hA negQ1 t1]; exact millerLoop2Walk_inf_inf p hq Q0 negQ0 Q1 negQ1 rest t0 t1
    · exact millerLoop2Walk_inf_inf p hq Q0 negQ0 Q1 negQ1 rest t0 t1

/-- Optimal Ate Miller loop identity at infinity: `millerLoop2 p digits O Q0 O Q1 = 1`. -/
theorem millerLoop2_inf_inf (p : PairingParams) (hq : 1 < p.curve.fqMod) (digits : BitList)
    (Q0 Q1 : G2Point) :
    millerLoop2 p digits g1Inf Q0 g1Inf Q1 = fp12One := by
  unfold millerLoop2 millerLoop2Finalize millerLoop2FinishBn
  dsimp only
  have hf := millerLoop2Walk_inf_inf p hq Q0 (g2Neg p.curve.fqMod Q0) Q1 (g2Neg p.curve.fqMod Q1)
    digits { x := Q0.x, y := Q0.y, z := fp2One } { x := Q1.x, y := Q1.y, z := fp2One }
  rw [hf, fp12Conj_one]
  split_ifs <;> simp [applyBnFrobLines, g1Inf]

private theorem millerLoop2BinaryWalk_inf_inf (p : PairingParams) (hq : 1 < p.curve.fqMod)
    (Q0 Q1 : G2Point) :
    ∀ (fuel bitMask : Nat) (t0 t1 : G2Proj),
      (millerLoop2BinaryWalk p fuel bitMask g1Inf g1Inf Q0 Q1 { f := fp12One, t0, t1 }).f = fp12One
  | 0, _, _, _ => rfl
  | fuel + 1, bitMask, t0, t1 => by
    unfold millerLoop2BinaryWalk
    dsimp only
    rw [fp12Sqr_one hq p.xi0]
    have hD0 : doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q0.isInf p.bTwist g1Inf t0 fp12One =
        { f := fp12One, t := t0 } := by simp [doubleAndEval, g1Inf]
    have hD1 : doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist g1Inf t1 fp12One =
        { f := fp12One, t := t1 } := by simp [doubleAndEval, g1Inf]
    have hA : ∀ Q T, addAndEval p.curve.fqMod p.xi0 p.isBn g1Inf Q T fp12One =
        { f := fp12One, t := T } := fun Q T => by simp [addAndEval, g1Inf]
    rw [hD0, hD1]
    split_ifs
    · rw [hA Q0 t0, hA Q1 t1]; exact millerLoop2BinaryWalk_inf_inf p hq Q0 Q1 fuel (bitMask / 2) t0 t1
    · exact millerLoop2BinaryWalk_inf_inf p hq Q0 Q1 fuel (bitMask / 2) t0 t1

/-- Binary optimal Ate Miller loop identity at infinity: `millerLoop2Binary p O Q0 O Q1 = 1`. -/
theorem millerLoop2Binary_inf_inf (p : PairingParams) (hq : 1 < p.curve.fqMod)
    (Q0 Q1 : G2Point) :
    millerLoop2Binary p g1Inf Q0 g1Inf Q1 = fp12One := by
  unfold millerLoop2Binary millerLoop2Finalize millerLoop2FinishBn
  dsimp only
  have hf := millerLoop2BinaryWalk_inf_inf p hq Q0 Q1 (p.loopBits - 1) (p.loopTopPow2 / 2)
    { x := Q0.x, y := Q0.y, z := fp2One } { x := Q1.x, y := Q1.y, z := fp2One }
  rw [hf, fp12Conj_one]
  split_ifs <;> simp [applyBnFrobLines, g1Inf]

private def PrepSync (p : PairingParams) (digits : BitList) (P : G1Point) (Q negQ : G2Point)
    (t : G2Proj) (ls : EllCoeffList) : Prop :=
  P.isInf = 1 ∨
  (Q.isInf = 1 ∧ negQ.isInf = 1 ∧ ls = .nil) ∨
  (Q.isInf = 0 ∧ negQ.isInf = 0 ∧ ls = precomputeG2Walk p digits Q negQ t)

private lemma evalPoppedLine_inf (q xi0 isBn : Nat) (f : Fp12) (lp : LinePop)
    {P : G1Point} (hP : P.isInf = 1) :
    evalPoppedLine q xi0 isBn f lp P = f := by
  unfold evalPoppedLine evalLine
  split_ifs <;> simp [hP] at *

private lemma millerLoop2PreparedWalk_sync (p : PairingParams)
    (P0 P1 : G1Point) (Q0 negQ0 Q1 negQ1 : G2Point)
    (hP0 : P0.isInf ≤ 1) (hP1 : P1.isInf ≤ 1) :
    ∀ (digits : BitList) (st : MillerState) (pst : PrepMillerState),
      pst.f = st.f →
      PrepSync p digits P0 Q0 negQ0 st.t0 pst.l0 →
      PrepSync p digits P1 Q1 negQ1 st.t1 pst.l1 →
      let st' := millerLoop2Walk p digits P0 P1 Q0 negQ0 Q1 negQ1 st
      let pst' := millerLoop2PreparedWalk p digits P0 P1 pst
      pst'.f = st'.f ∧
      PrepSync p .nil P0 Q0 negQ0 st'.t0 pst'.l0 ∧
      PrepSync p .nil P1 Q1 negQ1 st'.t1 pst'.l1
  | .nil, st, pst, hf, hs0, hs1 => ⟨hf, hs0, hs1⟩
  | .cons digit rest, st, pst, hf, hs0, hs1 => by
    unfold millerLoop2Walk millerLoop2PreparedWalk
    dsimp only
    rw [hf]
    have hstep :
        ∀ (P : G1Point) (hP : P.isInf ≤ 1) (Q negQ : G2Point) (t : G2Proj) (ls : EllCoeffList)
          (fIn : Fp12),
          PrepSync p (.cons digit rest) P Q negQ t ls →
          let o := doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q.isInf p.bTwist P t fIn
          let pd := popLine ls
          evalPoppedLine p.curve.fqMod p.xi0 p.isBn fIn pd P = o.f ∧
          (digit = 1 →
            let a := addAndEval p.curve.fqMod p.xi0 p.isBn P Q o.t o.f
            let pa := popLine pd.rest
            (∀ f2, evalPoppedLine p.curve.fqMod p.xi0 p.isBn f2 pa P =
              (addAndEval p.curve.fqMod p.xi0 p.isBn P Q o.t f2).f) ∧
            PrepSync p rest P Q negQ a.t pa.rest) ∧
          (digit = 2 →
            let a := addAndEval p.curve.fqMod p.xi0 p.isBn P negQ o.t o.f
            let pa := popLine pd.rest
            (∀ f2, evalPoppedLine p.curve.fqMod p.xi0 p.isBn f2 pa P =
              (addAndEval p.curve.fqMod p.xi0 p.isBn P negQ o.t f2).f) ∧
            PrepSync p rest P Q negQ a.t pa.rest) ∧
          (digit ≠ 1 → digit ≠ 2 →
            PrepSync p rest P Q negQ o.t pd.rest) := by
      intro P hP Q negQ t ls fIn hsync
      rcases hsync with hP1' | ⟨hQ1', hnegQ1', hls⟩ | ⟨hQ0', hnegQ0', hls⟩
      · refine ⟨?_, fun _ => ⟨fun f2 => ?_, Or.inl hP1'⟩,
          fun _ => ⟨fun f2 => ?_, Or.inl hP1'⟩, fun _ _ => Or.inl hP1'⟩
        · rw [evalPoppedLine_inf _ _ _ _ _ hP1']; simp [doubleAndEval, hP1']
        · rw [evalPoppedLine_inf _ _ _ _ _ hP1']; simp [addAndEval, hP1']
        · rw [evalPoppedLine_inf _ _ _ _ _ hP1']; simp [addAndEval, hP1']
      · subst hls
        refine ⟨?_, fun _ => ⟨fun f2 => ?_, Or.inr (Or.inl ⟨hQ1', hnegQ1', rfl⟩)⟩,
          fun _ => ⟨fun f2 => ?_, Or.inr (Or.inl ⟨hQ1', hnegQ1', rfl⟩)⟩,
          fun _ _ => Or.inr (Or.inl ⟨hQ1', hnegQ1', rfl⟩)⟩
        · simp [doubleAndEval, popLine, evalPoppedLine, hQ1']
        · simp [addAndEval, popLine, evalPoppedLine, hQ1']
        · simp [addAndEval, popLine, evalPoppedLine, hnegQ1']
      · subst hls
        rcases (by omega : P.isInf = 0 ∨ P.isInf = 1) with hP0' | hP1'
        · refine ⟨?_, fun hd1 => ?_, fun hd2 => ?_, fun hd1 hd2 => ?_⟩
          · simp only [precomputeG2Walk, doubleAndEval, hP0', hQ0', beq_self_eq_true, ↓reduceIte]
            split_ifs <;> rfl
          · simp only [precomputeG2Walk, hd1, beq_self_eq_true, ↓reduceIte, popLine,
              doubleAndEval, addAndEval, hP0', hQ0', evalPoppedLine]
            exact ⟨fun _ => trivial, Or.inr (Or.inr ⟨hQ0', hnegQ0', rfl⟩)⟩
          · simp only [precomputeG2Walk, hd2, Nat.reduceBEq, beq_self_eq_true,
              Bool.false_eq_true, ↓reduceIte, popLine,
              doubleAndEval, addAndEval, hP0', hQ0', hnegQ0', evalPoppedLine]
            exact ⟨fun _ => trivial, Or.inr (Or.inr ⟨hQ0', hnegQ0', rfl⟩)⟩
          · simp only [precomputeG2Walk, beq_false_of_ne hd1, beq_false_of_ne hd2,
              Bool.false_eq_true, ↓reduceIte, popLine, doubleAndEval, hP0', hQ0', beq_self_eq_true]
            exact Or.inr (Or.inr ⟨hQ0', hnegQ0', rfl⟩)
        · refine ⟨?_, fun _ => ⟨fun f2 => ?_, Or.inl hP1'⟩,
            fun _ => ⟨fun f2 => ?_, Or.inl hP1'⟩, fun _ _ => Or.inl hP1'⟩
          · rw [evalPoppedLine_inf _ _ _ _ _ hP1']; simp [doubleAndEval, hP1']
          · rw [evalPoppedLine_inf _ _ _ _ _ hP1']; simp [addAndEval, hP1']
          · rw [evalPoppedLine_inf _ _ _ _ _ hP1']; simp [addAndEval, hP1']
    set f0 := fp12Sqr p.curve.fqMod p.xi0 st.f
    have h0 := hstep P0 hP0 Q0 negQ0 st.t0 pst.l0 f0 hs0
    set o0 := doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q0.isInf p.bTwist P0 st.t0 f0
    have h1 := hstep P1 hP1 Q1 negQ1 st.t1 pst.l1 o0.f hs1
    rw [h0.1, h1.1]
    by_cases hd1 : digit = 1
    · simp only [hd1, beq_self_eq_true, Bool.true_or, ↓reduceIte]
      obtain ⟨ha0f, ha0s⟩ := h0.2.1 hd1
      obtain ⟨ha1f, ha1s⟩ := h1.2.1 hd1
      have hsync0 : PrepSync p rest P0 Q0 negQ0
          (addAndEval p.curve.fqMod p.xi0 p.isBn P0 Q0 o0.t
            (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f).t
          (popLine (popLine pst.l0).rest).rest := by
        have htEq : (addAndEval p.curve.fqMod p.xi0 p.isBn P0 Q0 o0.t
            (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f).t =
            (addAndEval p.curve.fqMod p.xi0 p.isBn P0 Q0 o0.t o0.f).t := by
          unfold addAndEval; split_ifs <;> rfl
        rw [htEq]; exact ha0s
      have hsync1 : PrepSync p rest P1 Q1 negQ1
          (addAndEval p.curve.fqMod p.xi0 p.isBn P1 Q1
            (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).t
            (addAndEval p.curve.fqMod p.xi0 p.isBn P0 Q0 o0.t
              (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f).f).t
          (popLine (popLine pst.l1).rest).rest := by
        have htEq : ∀ fA fB,
            (addAndEval p.curve.fqMod p.xi0 p.isBn P1 Q1
              (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).t fA).t =
            (addAndEval p.curve.fqMod p.xi0 p.isBn P1 Q1
              (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).t fB).t := by
          intro fA fB; unfold addAndEval; split_ifs <;> rfl
        rw [htEq _ (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f]
        exact ha1s
      exact millerLoop2PreparedWalk_sync p P0 P1 Q0 negQ0 Q1 negQ1 hP0 hP1 rest _ _
        (by rw [ha0f, ha1f]) hsync0 hsync1
    · by_cases hd2 : digit = 2
      · simp only [hd2, Nat.reduceBEq, beq_self_eq_true, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨ha0f, ha0s⟩ := h0.2.2.1 hd2
        obtain ⟨ha1f, ha1s⟩ := h1.2.2.1 hd2
        have hsync0 : PrepSync p rest P0 Q0 negQ0
            (addAndEval p.curve.fqMod p.xi0 p.isBn P0 negQ0 o0.t
              (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f).t
            (popLine (popLine pst.l0).rest).rest := by
          have htEq : (addAndEval p.curve.fqMod p.xi0 p.isBn P0 negQ0 o0.t
              (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f).t =
              (addAndEval p.curve.fqMod p.xi0 p.isBn P0 negQ0 o0.t o0.f).t := by
            unfold addAndEval; split_ifs <;> rfl
          rw [htEq]; exact ha0s
        have hsync1 : PrepSync p rest P1 Q1 negQ1
            (addAndEval p.curve.fqMod p.xi0 p.isBn P1 negQ1
              (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).t
              (addAndEval p.curve.fqMod p.xi0 p.isBn P0 negQ0 o0.t
                (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f).f).t
            (popLine (popLine pst.l1).rest).rest := by
          have htEq : ∀ fA fB,
              (addAndEval p.curve.fqMod p.xi0 p.isBn P1 negQ1
                (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).t fA).t =
              (addAndEval p.curve.fqMod p.xi0 p.isBn P1 negQ1
                (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).t fB).t := by
            intro fA fB; unfold addAndEval; split_ifs <;> rfl
          rw [htEq _ (doubleAndEval p.curve.fqMod p.xi0 p.twoInv p.isBn Q1.isInf p.bTwist P1 st.t1 o0.f).f]
          exact ha1s
        exact millerLoop2PreparedWalk_sync p P0 P1 Q0 negQ0 Q1 negQ1 hP0 hP1 rest _ _
          (by rw [ha0f, ha1f]) hsync0 hsync1
      · simp only [beq_false_of_ne hd1, beq_false_of_ne hd2, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        exact millerLoop2PreparedWalk_sync p P0 P1 Q0 negQ0 Q1 negQ1 hP0 hP1 rest _ _
          rfl (h0.2.2.2 hd1 hd2) (h1.2.2.2 hd1 hd2)

/-- **Exact Equivalence of Precomputed-Line and On-the-Fly Optimal Ate Miller Loops
(`millerLoop2Prepared_eq_millerLoop2`):**
For every `PairingParams`, signed/binary `digits`, and canonical `isInf ≤ 1` points
`(P0, Q0, P1, Q1)`, `millerLoop2Prepared` on `precomputeG2Lines` produces the **bit-for-bit
identical `Fp12` element** as `millerLoop2`. -/
theorem millerLoop2Prepared_eq_millerLoop2 (p : PairingParams) (digits : BitList)
    (P0 : G1Point) (Q0 : G2Point) (P1 : G1Point) (Q1 : G2Point)
    (hP0 : P0.isInf ≤ 1) (hP1 : P1.isInf ≤ 1) (hQ0 : Q0.isInf ≤ 1) (hQ1 : Q1.isInf ≤ 1) :
    millerLoop2Prepared p digits P0 (precomputeG2Lines p digits Q0)
      P1 (precomputeG2Lines p digits Q1) =
    millerLoop2 p digits P0 Q0 P1 Q1 := by
  have hInitSync : ∀ (P : G1Point) (Q : G2Point), Q.isInf ≤ 1 →
      PrepSync p digits P Q (g2Neg p.curve.fqMod Q)
        { x := Q.x, y := Q.y, z := fp2One } (precomputeG2Lines p digits Q) := by
    intro P Q hQ
    rcases (by omega : Q.isInf = 0 ∨ Q.isInf = 1) with hQ0' | hQ1'
    · refine Or.inr (Or.inr ⟨hQ0', ?_, ?_⟩)
      · simp [g2Neg, hQ0']
      · simp [precomputeG2Lines, hQ0']
    · refine Or.inr (Or.inl ⟨hQ1', ?_, ?_⟩)
      · simp [g2Neg, g2Inf, hQ1']
      · simp [precomputeG2Lines, hQ1']
  unfold millerLoop2Prepared millerLoop2 millerLoop2Finalize millerLoop2FinishBn
  dsimp only
  obtain ⟨hfEq, hs0, hs1⟩ := millerLoop2PreparedWalk_sync p P0 P1
    Q0 (g2Neg p.curve.fqMod Q0) Q1 (g2Neg p.curve.fqMod Q1) hP0 hP1 digits
    { f := fp12One, t0 := { x := Q0.x, y := Q0.y, z := fp2One }, t1 := { x := Q1.x, y := Q1.y, z := fp2One } }
    { f := fp12One, l0 := precomputeG2Lines p digits Q0, l1 := precomputeG2Lines p digits Q1 }
    rfl (hInitSync P0 Q0 hQ0) (hInitSync P1 Q1 hQ1)
  rw [hfEq]
  have hBnPair : ∀ (fIn : Fp12) (P : G1Point) (hP : P.isInf ≤ 1) (Q negQ : G2Point)
      (t : G2Proj) (ls : EllCoeffList),
      p.isBn = 1 →
      PrepSync p .nil P Q negQ t ls →
      evalPoppedLine p.curve.fqMod p.xi0 1
        (evalPoppedLine p.curve.fqMod p.xi0 1 fIn (popLine ls) P) (popLine (popLine ls).rest) P =
      applyBnFrobLines p.curve.fqMod p.xi0 p.twistMulByQX p.twistMulByQY fIn t P Q := by
    intro fIn P hP Q negQ t ls hBn hsync
    rcases hsync with hP1' | ⟨hQ1', _, hls⟩ | ⟨hQ0', _, hls⟩
    · rw [evalPoppedLine_inf _ _ _ _ _ hP1', evalPoppedLine_inf _ _ _ _ _ hP1']
      simp [applyBnFrobLines, hP1']
    · subst hls
      simp [popLine, evalPoppedLine, applyBnFrobLines, hQ1']
    · subst hls
      rcases (by omega : P.isInf = 0 ∨ P.isInf = 1) with hP0' | hP1'
      · simp [precomputeG2Walk, hBn, popLine, evalPoppedLine, applyBnFrobLines, hP0', hQ0']
      · rw [evalPoppedLine_inf _ _ _ _ _ hP1', evalPoppedLine_inf _ _ _ _ _ hP1']
        simp [applyBnFrobLines, hP1']
  by_cases hBn : p.isBn = 1
  · simp only [hBn, beq_self_eq_true, ↓reduceIte]
    split_ifs <;> rw [hBnPair _ P0 hP0 _ _ _ _ hBn hs0, hBnPair _ P1 hP1 _ _ _ _ hBn hs1]
  · simp only [beq_false_of_ne hBn, Bool.false_eq_true, ↓reduceIte]

/-! ### 3.2 Field-Theoretic Tower Frobenius Soundness (For Any Field `K` & `φ : ZModFp12 →+* K`) -/

@[simp] theorem ZModFp6.mulV_c0 {q xi0 : Nat} (a : ZModFp6 q xi0) :
    (ZModFp6.mulV a).c0 = a.c2 * ZModFp2.xi q xi0 := rfl
@[simp] theorem ZModFp6.mulV_c1 {q xi0 : Nat} (a : ZModFp6 q xi0) :
    (ZModFp6.mulV a).c1 = a.c0 := rfl
@[simp] theorem ZModFp6.mulV_c2 {q xi0 : Nat} (a : ZModFp6 q xi0) :
    (ZModFp6.mulV a).c2 = a.c1 := rfl
@[simp] theorem ZModFp6.mulV_zero (q xi0 : Nat) :
    ZModFp6.mulV (0 : ZModFp6 q xi0) = 0 := by
  apply ZModFp6.ext <;> simp

/-- Ring embedding `ZMod q →+* ZModFp2 q`. -/
def zmodToFp2 (q : Nat) : ZMod q →+* ZModFp2 q where
  toFun x := ⟨x, 0⟩
  map_one' := rfl
  map_mul' a b := by apply ZModFp2.ext <;> simp
  map_zero' := rfl
  map_add' a b := by apply ZModFp2.ext <;> simp

/-- Ring embedding `ZModFp2 q →+* ZModFp6 q xi0`. -/
def zmodFp2ToFp6 (q xi0 : Nat) : ZModFp2 q →+* ZModFp6 q xi0 where
  toFun x := ⟨x, 0, 0⟩
  map_one' := rfl
  map_mul' a b := by apply ZModFp6.ext <;> simp
  map_zero' := rfl
  map_add' a b := by apply ZModFp6.ext <;> simp

/-- Ring embedding `ZModFp6 q xi0 →+* ZModFp12 q xi0`. -/
def zmodFp6ToFp12 (q xi0 : Nat) : ZModFp6 q xi0 →+* ZModFp12 q xi0 where
  toFun x := ⟨x, 0⟩
  map_one' := rfl
  map_mul' a b := by apply ZModFp12.ext <;> simp
  map_zero' := rfl
  map_add' a b := by apply ZModFp12.ext <;> simp

/-- Ring embedding `ZModFp2 q →+* ZModFp12 q xi0`. -/
def zmodFp2ToFp12 (q xi0 : Nat) : ZModFp2 q →+* ZModFp12 q xi0 :=
  (zmodFp6ToFp12 q xi0).comp (zmodFp2ToFp6 q xi0)

/-- Ring embedding `ZMod q →+* ZModFp12 q xi0`. -/
def zmodToFp12 (q xi0 : Nat) : ZMod q →+* ZModFp12 q xi0 :=
  (zmodFp2ToFp12 q xi0).comp (zmodToFp2 q)

@[simp] theorem zmodFp6ToFp12_c0 {q xi0 : Nat} (x : ZModFp6 q xi0) :
    (zmodFp6ToFp12 q xi0 x).c0 = x := rfl
@[simp] theorem zmodFp6ToFp12_c1 {q xi0 : Nat} (x : ZModFp6 q xi0) :
    (zmodFp6ToFp12 q xi0 x).c1 = 0 := rfl
@[simp] theorem zmodFp2ToFp12_c0 {q xi0 : Nat} (x : ZModFp2 q) :
    (zmodFp2ToFp12 q xi0 x).c0 = ⟨x, 0, 0⟩ := rfl
@[simp] theorem zmodFp2ToFp12_c1 {q xi0 : Nat} (x : ZModFp2 q) :
    (zmodFp2ToFp12 q xi0 x).c1 = 0 := rfl
@[simp] theorem zmodToFp12_c0 {q xi0 : Nat} (x : ZMod q) :
    (zmodToFp12 q xi0 x).c0 = ⟨⟨x, 0⟩, 0, 0⟩ := rfl
@[simp] theorem zmodToFp12_c1 {q xi0 : Nat} (x : ZMod q) :
    (zmodToFp12 q xi0 x).c1 = 0 := rfl

/-- Any field `K` receiving a ring homomorphism `φ : ZModFp12 q xi0 →+* K` for prime `q`
automatically has characteristic `q`. -/
theorem charP_of_fp12Hom {q xi0 : Nat} [Fact (Nat.Prime q)] {K : Type*} [Field K]
    (φ : ZModFp12 q xi0 →+* K) : CharP K q := by
  let ψ : ZMod q →+* K := φ.comp (zmodToFp12 q xi0)
  refine ⟨fun n => ?_⟩
  constructor
  · intro hn
    by_contra hndvd
    have hnz : (n : ZMod q) ≠ 0 := by
      intro h0
      exact hndvd ((ZMod.natCast_eq_zero_iff n q).mp h0)
    have hinv : (n : ZMod q) * (n : ZMod q)⁻¹ = 1 := mul_inv_cancel₀ hnz
    have h1 : ψ ((n : ZMod q) * (n : ZMod q)⁻¹) = ψ 1 := congrArg ψ hinv
    rw [map_mul, map_one, map_natCast, hn, zero_mul] at h1
    exact zero_ne_one h1
  · intro hdvd
    have h0 : (n : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff n q).mpr hdvd
    have hmap : ψ (n : ZMod q) = 0 := by rw [h0, map_zero]
    rwa [map_natCast] at hmap

namespace ZModFp12

/-- Quadratic tower generator `u ∈ ZModFp12 q xi0` (`u² = -1`). -/
def u12 (q xi0 : Nat) : ZModFp12 q xi0 := zmodFp2ToFp12 q xi0 ⟨0, 1⟩

/-- Cubic tower generator `v ∈ ZModFp12 q xi0` (`v³ = ξ = xi0 + u`). -/
def v12 (q xi0 : Nat) : ZModFp12 q xi0 := zmodFp6ToFp12 q xi0 ⟨0, 1, 0⟩

/-- Sextic/twelfth tower generator `w ∈ ZModFp12 q xi0` (`w² = v`, `w⁶ = ξ`). -/
def w12 (q xi0 : Nat) : ZModFp12 q xi0 := ⟨0, 1⟩

@[simp] theorem u12_c0 (q xi0 : Nat) : (u12 q xi0).c0 = ⟨⟨0, 1⟩, 0, 0⟩ := rfl
@[simp] theorem u12_c1 (q xi0 : Nat) : (u12 q xi0).c1 = 0 := rfl
@[simp] theorem v12_c0 (q xi0 : Nat) : (v12 q xi0).c0 = ⟨0, 1, 0⟩ := rfl
@[simp] theorem v12_c1 (q xi0 : Nat) : (v12 q xi0).c1 = 0 := rfl
@[simp] theorem w12_c0 (q xi0 : Nat) : (w12 q xi0).c0 = 0 := rfl
@[simp] theorem w12_c1 (q xi0 : Nat) : (w12 q xi0).c1 = 1 := rfl

theorem u12_sq (q xi0 : Nat) : (u12 q xi0) ^ 2 = -1 := by
  rw [sq]; apply ZModFp12.ext <;> apply ZModFp6.ext <;> apply ZModFp2.ext <;> simp

theorem w12_sq (q xi0 : Nat) : (w12 q xi0) ^ 2 = v12 q xi0 := by
  rw [sq]; apply ZModFp12.ext <;> apply ZModFp6.ext <;> apply ZModFp2.ext <;> simp

theorem v12_cube (q xi0 : Nat) : (v12 q xi0) ^ 3 = zmodFp2ToFp12 q xi0 (ZModFp2.xi q xi0) := by
  rw [show (3 : Nat) = 2 + 1 from rfl, pow_succ, sq]
  apply ZModFp12.ext <;> apply ZModFp6.ext <;> apply ZModFp2.ext <;> simp [ZModFp2.xi]

theorem w12_pow_six (q xi0 : Nat) : (w12 q xi0) ^ 6 = zmodFp2ToFp12 q xi0 (ZModFp2.xi q xi0) := by
  rw [show (6 : Nat) = 2 * 3 from rfl, pow_mul, w12_sq, v12_cube]

theorem decomp_fp2 (q xi0 : Nat) (x : ZModFp2 q) :
    zmodFp2ToFp12 q xi0 x = zmodToFp12 q xi0 x.c0 + zmodToFp12 q xi0 x.c1 * u12 q xi0 := by
  apply ZModFp12.ext <;> apply ZModFp6.ext <;> apply ZModFp2.ext <;> simp

theorem decomp_fp6 (q xi0 : Nat) (x : ZModFp6 q xi0) :
    zmodFp6ToFp12 q xi0 x =
      zmodFp2ToFp12 q xi0 x.c0 +
      zmodFp2ToFp12 q xi0 x.c1 * v12 q xi0 +
      zmodFp2ToFp12 q xi0 x.c2 * (v12 q xi0) ^ 2 := by
  rw [sq]
  apply ZModFp12.ext <;> apply ZModFp6.ext <;> apply ZModFp2.ext <;> simp

theorem decomp_fp12 (q xi0 : Nat) (a : ZModFp12 q xi0) :
    a = zmodFp6ToFp12 q xi0 a.c0 + zmodFp6ToFp12 q xi0 a.c1 * w12 q xi0 := by
  apply ZModFp12.ext <;> apply ZModFp6.ext <;> apply ZModFp2.ext <;> simp

end ZModFp12

/-- Executable structural binary powering in `Fp2` for kernel Frobenius verification. -/
def fp2PowFuel (q : Nat) : Nat → Fp2 → Nat → Fp2 → Fp2
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
    match exp with
    | 0 => acc
    | _ =>
      let nextAcc := if exp % 2 == 1 then fp2Mul q acc base else acc
      fp2PowFuel q fuel (fp2Sqr q base) (exp / 2) nextAcc
termination_by structural fuel => fuel

def fp2Pow (q bits : Nat) (base : Fp2) (exp : Nat) : Fp2 :=
  fp2PowFuel q bits base exp fp2One

theorem fp2PowFuel_hom {q : Nat} (hq : 0 < q) :
    ∀ fuel base exp acc,
      exp < 2 ^ fuel →
      fp2Canonical q base = true →
      fp2ToZMod q (fp2PowFuel q fuel base exp acc) =
        fp2ToZMod q acc * (fp2ToZMod q base) ^ exp
  | 0, base, exp, acc, hlt, _ => by
    have h0 : exp = 0 := by omega
    subst h0; simp [fp2PowFuel]
  | fuel + 1, base, 0, acc, _, _ => by
    simp [fp2PowFuel]
  | fuel + 1, base, exp + 1, acc, hlt, hbase => by
    have hstep : fp2PowFuel q (fuel + 1) base (exp + 1) acc =
        fp2PowFuel q fuel (fp2Sqr q base) ((exp + 1) / 2)
          (if (exp + 1) % 2 == 1 then fp2Mul q acc base else acc) := rfl
    rw [hstep]
    have hdiv : (exp + 1) / 2 < 2 ^ fuel := by
      have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      omega
    rw [fp2PowFuel_hom hq fuel _ _ _ hdiv (fp2Sqr_canonical hq base), fp2Sqr_hom hbase]
    have hmod_cases : (exp + 1) % 2 = 0 ∨ (exp + 1) % 2 = 1 := by omega
    rcases hmod_cases with hm | hm
    · rw [hm]
      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
      have hexp : exp + 1 = 2 * ((exp + 1) / 2) := by omega
      conv_rhs => rw [hexp, pow_mul, sq]
    · rw [hm]
      simp only [beq_self_eq_true, ↓reduceIte, fp2Mul_hom hq]
      have hexp : exp + 1 = 2 * ((exp + 1) / 2) + 1 := by omega
      conv_rhs => rw [hexp, pow_succ, pow_mul, sq]
      ring

theorem fp2Pow_hom {q : Nat} (hq : 0 < q) (bits : Nat) {base : Fp2} {exp : Nat}
    (hlt : exp < 2 ^ bits) (hbase : fp2Canonical q base = true) :
    fp2ToZMod q (fp2Pow q bits base exp) = (fp2ToZMod q base) ^ exp := by
  unfold fp2Pow
  rw [fp2PowFuel_hom hq bits base exp fp2One hlt hbase, fp2ToZMod_one, one_mul]

/-- Exact algebraic validity conditions on a curve's Frobenius constants in `PairingParams`. -/
structure FrobConstantsValid (p : PairingParams) : Prop where
  q_mod_4 : p.curve.fqMod % 4 = 3
  q_mod_6 : p.curve.fqMod % 6 = 1
  w1_1_eq : fp2ToZMod p.curve.fqMod p.frob12C1_1 = (ZModFp2.xi p.curve.fqMod p.xi0) ^ ((p.curve.fqMod - 1) / 6)
  c1_1_eq : fp2ToZMod p.curve.fqMod p.frob6C1_1 = (fp2ToZMod p.curve.fqMod p.frob12C1_1) ^ 2
  c2_1_eq : fp2ToZMod p.curve.fqMod p.frob6C2_1 = (fp2ToZMod p.curve.fqMod p.frob6C1_1) ^ 2
  c1_2_eq : fp2ToZMod p.curve.fqMod p.frob6C1_2 =
    (fp2ToZMod p.curve.fqMod p.frob6C1_1).conj * fp2ToZMod p.curve.fqMod p.frob6C1_1
  c2_2_eq : fp2ToZMod p.curve.fqMod p.frob6C2_2 =
    (fp2ToZMod p.curve.fqMod p.frob6C2_1).conj * fp2ToZMod p.curve.fqMod p.frob6C2_1
  w1_2_eq : fp2ToZMod p.curve.fqMod p.frob12C1_2 =
    (fp2ToZMod p.curve.fqMod p.frob12C1_1).conj * fp2ToZMod p.curve.fqMod p.frob12C1_1
  c1_3_eq : fp2ToZMod p.curve.fqMod p.frob6C1_3 =
    (fp2ToZMod p.curve.fqMod p.frob6C1_2).conj * fp2ToZMod p.curve.fqMod p.frob6C1_1
  c2_3_eq : fp2ToZMod p.curve.fqMod p.frob6C2_3 =
    (fp2ToZMod p.curve.fqMod p.frob6C2_2).conj * fp2ToZMod p.curve.fqMod p.frob6C2_1
  w1_3_eq : fp2ToZMod p.curve.fqMod p.frob12C1_3 =
    (fp2ToZMod p.curve.fqMod p.frob12C1_2).conj * fp2ToZMod p.curve.fqMod p.frob12C1_1
  c1_6_eq : (fp2ToZMod p.curve.fqMod p.frob6C1_3).conj * fp2ToZMod p.curve.fqMod p.frob6C1_3 = 1
  c2_6_eq : (fp2ToZMod p.curve.fqMod p.frob6C2_3).conj * fp2ToZMod p.curve.fqMod p.frob6C2_3 = 1
  w1_6_eq : (fp2ToZMod p.curve.fqMod p.frob12C1_3).conj * fp2ToZMod p.curve.fqMod p.frob12C1_3 = -1

private theorem fp12FrobOdd_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (k1 k2 w1 : Fp2)
    {a : Fp12} (ha : fp12Canonical q a = true) :
    fp12ToZMod q xi0 (fp12FrobOdd q k1 k2 w1 a) =
      (zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c0.c0).conj +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c0.c1).conj *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k1) * ZModFp12.v12 q xi0) +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c0.c2).conj *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k2) * (ZModFp12.v12 q xi0) ^ 2)) +
      (zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c1.c0).conj +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c1.c1).conj *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k1) * ZModFp12.v12 q xi0) +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c1.c2).conj *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k2) * (ZModFp12.v12 q xi0) ^ 2)) *
        (zmodFp2ToFp12 q xi0 (fp2ToZMod q w1) * ZModFp12.w12 q xi0) := by
  rw [fp12Canonical_iff, fp6Canonical_iff, fp6Canonical_iff] at ha
  have hc00 := fp2Conj_hom ha.1.1
  have hc01 := fp2Conj_hom ha.1.2.1
  have hc02 := fp2Conj_hom ha.1.2.2
  have hc10 := fp2Conj_hom ha.2.1
  have hc11 := fp2Conj_hom ha.2.2.1
  have hc12 := fp2Conj_hom ha.2.2.2
  rw [sq]
  apply ZModFp12.ext <;> apply ZModFp6.ext <;>
    simp [fp12FrobOdd, fp6FrobOdd, fp6MulByFp2, fp12ToZMod, fp6ToZMod,
      fp2Mul_hom hq, hc00, hc01, hc02, hc10, hc11, hc12]

private theorem fp12FrobEven_hom {q : Nat} (hq : 0 < q) (xi0 : Nat) (k1 k2 w1 : Fp2) (a : Fp12) :
    fp12ToZMod q xi0 (fp12FrobEven q k1 k2 w1 a) =
      (zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c0.c0) +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c0.c1) *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k1) * ZModFp12.v12 q xi0) +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c0.c2) *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k2) * (ZModFp12.v12 q xi0) ^ 2)) +
      (zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c1.c0) +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c1.c1) *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k1) * ZModFp12.v12 q xi0) +
       zmodFp2ToFp12 q xi0 (fp2ToZMod q a.c1.c2) *
         (zmodFp2ToFp12 q xi0 (fp2ToZMod q k2) * (ZModFp12.v12 q xi0) ^ 2)) *
        (zmodFp2ToFp12 q xi0 (fp2ToZMod q w1) * ZModFp12.w12 q xi0) := by
  rw [sq]
  apply ZModFp12.ext <;> apply ZModFp6.ext <;>
    simp [fp12FrobEven, fp6FrobEven, fp6MulByFp2, fp12ToZMod, fp6ToZMod,
      fp2Mul_hom hq]

/-- **Frobenius Field Soundness (`fp12Frob_field_sound`):**
For ANY `PairingParams` satisfying `FrobConstantsValid p` with prime `q = p.curve.fqMod`,
ANY field `K`, and ANY ring homomorphism `φ : ZModFp12 q p.xi0 →+* K`:
1. `φ (fp12Frob1 p a) = (φ a) ^ q`,
2. `φ (fp12Frob2 p a) = (φ a) ^ (q ^ 2)`,
3. `φ (fp12Frob3 p a) = (φ a) ^ (q ^ 3)`,
4. `φ (fp12Conj q a) = (φ a) ^ (q ^ 6)`,
5. `(φ a) ^ (q ^ 12) = φ a`,
6. `(φ (fp12OfFp6 s)) ^ (q ^ 6) = φ (fp12OfFp6 s)`. -/
theorem fp12Frob_field_sound {p : PairingParams} [Fact (Nat.Prime p.curve.fqMod)]
    (hv : FrobConstantsValid p) {K : Type*} [Field K]
    (φ : ZModFp12 p.curve.fqMod p.xi0 →+* K) :
    (∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob1 p a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ p.curve.fqMod) ∧
    (∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob2 p a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 2)) ∧
    (∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob3 p a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 3)) ∧
    (∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Conj p.curve.fqMod a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 6)) ∧
    (∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 12) =
        φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ∧
    (∀ s : Fp6, fp6Canonical p.curve.fqMod s = true →
      (φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12OfFp6 s))) ^ (p.curve.fqMod ^ 6) =
        φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12OfFp6 s))) := by
  have : CharP K p.curve.fqMod := charP_of_fp12Hom φ
  have hqPos : 0 < p.curve.fqMod := (Fact.out : Nat.Prime p.curve.fqMod).pos
  have hqAdd : ∀ x y : K, (x + y) ^ p.curve.fqMod = x ^ p.curve.fqMod + y ^ p.curve.fqMod :=
    fun x y => add_pow_char x y p.curve.fqMod
  have hFqPow : ∀ x : ZMod p.curve.fqMod,
      (φ (zmodToFp12 p.curve.fqMod p.xi0 x)) ^ p.curve.fqMod =
        φ (zmodToFp12 p.curve.fqMod p.xi0 x) := by
    intro x
    rw [← map_pow, ← map_pow, ZMod.pow_card]
  have hUPow : (φ (ZModFp12.u12 p.curve.fqMod p.xi0)) ^ p.curve.fqMod =
      -(φ (ZModFp12.u12 p.curve.fqMod p.xi0)) := by
    have hq4 : p.curve.fqMod = 2 * (2 * (p.curve.fqMod / 4) + 1) + 1 := by
      have := hv.q_mod_4; omega
    have hstep : (φ (ZModFp12.u12 p.curve.fqMod p.xi0)) ^ p.curve.fqMod =
        (φ (ZModFp12.u12 p.curve.fqMod p.xi0)) ^ (2 * (2 * (p.curve.fqMod / 4) + 1) + 1) :=
      congrArg (_ ^ ·) hq4
    rw [hstep, pow_succ, pow_mul, ← map_pow, ZModFp12.u12_sq, map_neg, map_one,
      Odd.neg_one_pow ⟨p.curve.fqMod / 4, rfl⟩]
    ring
  have hFp2Pow : ∀ x : ZModFp2 p.curve.fqMod,
      (φ (zmodFp2ToFp12 p.curve.fqMod p.xi0 x)) ^ p.curve.fqMod =
        φ (zmodFp2ToFp12 p.curve.fqMod p.xi0 x.conj) := by
    intro x
    rw [ZModFp12.decomp_fp2, map_add, map_mul, hqAdd, mul_pow, hFqPow, hFqPow, hUPow]
    rw [ZModFp12.decomp_fp2]
    simp only [ZModFp2.conj, map_add, map_mul, map_neg]
    ring
  have hWPow : (φ (ZModFp12.w12 p.curve.fqMod p.xi0)) ^ p.curve.fqMod =
      φ (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod p.frob12C1_1)) *
        φ (ZModFp12.w12 p.curve.fqMod p.xi0) := by
    have hq6 : p.curve.fqMod = 6 * ((p.curve.fqMod - 1) / 6) + 1 := by
      have := hv.q_mod_6; omega
    have hstep : (φ (ZModFp12.w12 p.curve.fqMod p.xi0)) ^ p.curve.fqMod =
        (φ (ZModFp12.w12 p.curve.fqMod p.xi0)) ^ (6 * ((p.curve.fqMod - 1) / 6) + 1) :=
      congrArg (_ ^ ·) hq6
    rw [hstep, pow_succ, pow_mul, ← map_pow, ZModFp12.w12_pow_six, ← map_pow, ← map_pow, ← hv.w1_1_eq]
  have hVPow : (φ (ZModFp12.v12 p.curve.fqMod p.xi0)) ^ p.curve.fqMod =
      φ (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod p.frob6C1_1)) *
        φ (ZModFp12.v12 p.curve.fqMod p.xi0) := by
    rw [← ZModFp12.w12_sq, map_pow, ← pow_mul, Nat.mul_comm 2, pow_mul, hWPow,
      mul_pow, ← map_pow, ← map_pow, ← hv.c1_1_eq, ← map_pow, ZModFp12.w12_sq]
  have hV2Pow : (φ ((ZModFp12.v12 p.curve.fqMod p.xi0) ^ 2)) ^ p.curve.fqMod =
      φ (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod p.frob6C2_1)) *
        φ ((ZModFp12.v12 p.curve.fqMod p.xi0) ^ 2) := by
    rw [map_pow, ← pow_mul, Nat.mul_comm 2, pow_mul, hVPow,
      mul_pow, ← map_pow, ← map_pow, ← hv.c2_1_eq, ← map_pow]
  have hFrob1 : ∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob1 p a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ p.curve.fqMod := by
    intro a ha
    unfold fp12Frob1
    rw [fp12FrobOdd_hom hqPos p.xi0 _ _ _ ha]
    conv_rhs =>
      rw [ZModFp12.decomp_fp12 p.curve.fqMod p.xi0 (fp12ToZMod p.curve.fqMod p.xi0 a),
        ZModFp12.decomp_fp6 p.curve.fqMod p.xi0 (fp12ToZMod p.curve.fqMod p.xi0 a).c0,
        ZModFp12.decomp_fp6 p.curve.fqMod p.xi0 (fp12ToZMod p.curve.fqMod p.xi0 a).c1]
    simp only [fp12ToZMod, fp6ToZMod, map_add, map_mul, hqAdd, mul_pow,
      hFp2Pow, hVPow, hV2Pow, hWPow]
  have hFrob2 : ∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob2 p a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 2) := by
    intro a ha
    have ha1 : fp12Canonical p.curve.fqMod (fp12Frob1 p a) = true :=
      fp12FrobOdd_canonical hqPos _ _ _ ha
    have hcomp : fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob2 p a) =
        fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob1 p (fp12Frob1 p a)) := by
      have ha1' : fp12Canonical p.curve.fqMod
          (fp12FrobOdd p.curve.fqMod p.frob6C1_1 p.frob6C2_1 p.frob12C1_1 a) = true := ha1
      unfold fp12Frob2 fp12Frob1
      rw [fp12FrobEven_hom hqPos p.xi0 _ _ _ a, fp12FrobOdd_hom hqPos p.xi0 _ _ _ ha1']
      have hconj_mul : ∀ x y : ZModFp2 p.curve.fqMod, (x * y).conj = x.conj * y.conj := by
        intro x y; (apply ZModFp2.ext <;> simp [ZModFp2.conj]); ring
      have hconj_conj : ∀ x : ZModFp2 p.curve.fqMod, x.conj.conj = x := by
        intro x; apply ZModFp2.ext <;> simp [ZModFp2.conj]
      rw [fp12Canonical_iff, fp6Canonical_iff, fp6Canonical_iff] at ha
      simp only [fp12FrobOdd, fp6FrobOdd, fp6MulByFp2, fp2Mul_hom hqPos,
        fp2Conj_hom ha.1.1, fp2Conj_hom ha.1.2.1, fp2Conj_hom ha.1.2.2,
        fp2Conj_hom ha.2.1, fp2Conj_hom ha.2.2.1, fp2Conj_hom ha.2.2.2,
        hconj_mul, hconj_conj, hv.c1_2_eq, hv.c2_2_eq, hv.w1_2_eq, map_mul]
      ring
    rw [hcomp, hFrob1 _ ha1, hFrob1 a ha, ← pow_mul, sq]
  have hFrob3 : ∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob3 p a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 3) := by
    intro a ha
    have ha2 : fp12Canonical p.curve.fqMod (fp12Frob2 p a) = true :=
      fp12FrobEven_canonical hqPos _ _ _ ha
    have hcomp : fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob3 p a) =
        fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob1 p (fp12Frob2 p a)) := by
      have ha2' : fp12Canonical p.curve.fqMod
          (fp12FrobEven p.curve.fqMod p.frob6C1_2 p.frob6C2_2 p.frob12C1_2 a) = true := ha2
      unfold fp12Frob3 fp12Frob1 fp12Frob2
      rw [fp12FrobOdd_hom hqPos p.xi0 _ _ _ ha, fp12FrobOdd_hom hqPos p.xi0 _ _ _ ha2']
      have hconj_mul : ∀ x y : ZModFp2 p.curve.fqMod, (x * y).conj = x.conj * y.conj := by
        intro x y; (apply ZModFp2.ext <;> simp [ZModFp2.conj]); ring
      simp only [fp12FrobEven, fp6FrobEven, fp6MulByFp2, fp2Mul_hom hqPos,
        hconj_mul, hv.c1_3_eq, hv.c2_3_eq, hv.w1_3_eq, map_mul]
      ring
    rw [hcomp, hFrob1 _ ha2, hFrob2 a ha, ← pow_mul,
      show p.curve.fqMod ^ 2 * p.curve.fqMod = p.curve.fqMod ^ 3 by ring]
  have hConj : ∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Conj p.curve.fqMod a)) =
        (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 6) := by
    intro a ha
    have ha3 : fp12Canonical p.curve.fqMod (fp12Frob3 p a) = true :=
      fp12FrobOdd_canonical hqPos _ _ _ ha
    have hcomp : fp12ToZMod p.curve.fqMod p.xi0 (fp12Conj p.curve.fqMod a) =
        fp12ToZMod p.curve.fqMod p.xi0 (fp12Frob3 p (fp12Frob3 p a)) := by
      have ha3' : fp12Canonical p.curve.fqMod
          (fp12FrobOdd p.curve.fqMod p.frob6C1_3 p.frob6C2_3 p.frob12C1_3 a) = true := ha3
      unfold fp12Frob3
      rw [fp12Conj_hom ha, fp12FrobOdd_hom hqPos p.xi0 _ _ _ ha3']
      have hconj_mul : ∀ x y : ZModFp2 p.curve.fqMod, (x * y).conj = x.conj * y.conj := by
        intro x y; (apply ZModFp2.ext <;> simp [ZModFp2.conj]); ring
      have hconj_conj : ∀ x : ZModFp2 p.curve.fqMod, x.conj.conj = x := by
        intro x; apply ZModFp2.ext <;> simp [ZModFp2.conj]
      rw [fp12Canonical_iff, fp6Canonical_iff, fp6Canonical_iff] at ha
      simp only [fp12FrobOdd, fp6FrobOdd, fp6MulByFp2, fp2Mul_hom hqPos,
        fp2Conj_hom ha.1.1, fp2Conj_hom ha.1.2.1, fp2Conj_hom ha.1.2.2,
        fp2Conj_hom ha.2.1, fp2Conj_hom ha.2.2.1, fp2Conj_hom ha.2.2.2,
        hconj_mul, hconj_conj]
      have hK1 : zmodFp2ToFp12 p.curve.fqMod p.xi0
          ((fp2ToZMod p.curve.fqMod p.frob6C1_3).conj * fp2ToZMod p.curve.fqMod p.frob6C1_3) = 1 := by
        rw [hv.c1_6_eq, map_one]
      have hK2 : zmodFp2ToFp12 p.curve.fqMod p.xi0
          ((fp2ToZMod p.curve.fqMod p.frob6C2_3).conj * fp2ToZMod p.curve.fqMod p.frob6C2_3) = 1 := by
        rw [hv.c2_6_eq, map_one]
      have hW1 : zmodFp2ToFp12 p.curve.fqMod p.xi0
          ((fp2ToZMod p.curve.fqMod p.frob12C1_3).conj * fp2ToZMod p.curve.fqMod p.frob12C1_3) = -1 := by
        rw [hv.w1_6_eq, map_neg, map_one]
      rw [map_mul] at hK1 hK2 hW1
      simp only [map_mul]
      have hdecomp : ZModFp12.conj (fp12ToZMod p.curve.fqMod p.xi0 a) =
          (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c0.c0) +
           zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c0.c1) *
             ZModFp12.v12 p.curve.fqMod p.xi0 +
           zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c0.c2) *
             (ZModFp12.v12 p.curve.fqMod p.xi0) ^ 2) -
          (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c1.c0) +
           zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c1.c1) *
             ZModFp12.v12 p.curve.fqMod p.xi0 +
           zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c1.c2) *
             (ZModFp12.v12 p.curve.fqMod p.xi0) ^ 2) * ZModFp12.w12 p.curve.fqMod p.xi0 := by
        rw [sq]
        apply ZModFp12.ext <;> apply ZModFp6.ext <;>
          simp [ZModFp12.conj, fp12ToZMod, fp6ToZMod]
      rw [hdecomp]
      linear_combination
        -(zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c0.c1) *
            ZModFp12.v12 p.curve.fqMod p.xi0) * hK1 -
        (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c0.c2) *
            (ZModFp12.v12 p.curve.fqMod p.xi0) ^ 2) * hK2 -
        (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c1.c0) *
            ZModFp12.w12 p.curve.fqMod p.xi0) * hW1 -
        (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c1.c1) *
            ZModFp12.v12 p.curve.fqMod p.xi0 * ZModFp12.w12 p.curve.fqMod p.xi0) *
          (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod p.frob12C1_3).conj *
            zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod p.frob12C1_3) * hK1 + hW1) -
        (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod a.c1.c2) *
            (ZModFp12.v12 p.curve.fqMod p.xi0) ^ 2 * ZModFp12.w12 p.curve.fqMod p.xi0) *
          (zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod p.frob12C1_3).conj *
            zmodFp2ToFp12 p.curve.fqMod p.xi0 (fp2ToZMod p.curve.fqMod p.frob12C1_3) * hK2 + hW1)
    rw [hcomp, hFrob3 _ ha3, hFrob3 a ha, ← pow_mul,
      show p.curve.fqMod ^ 3 * p.curve.fqMod ^ 3 = p.curve.fqMod ^ 6 by ring]
  have hPow12 : ∀ a : Fp12, fp12Canonical p.curve.fqMod a = true →
      (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 12) =
        φ (fp12ToZMod p.curve.fqMod p.xi0 a) := by
    intro a ha
    have hconj2 : fp12ToZMod p.curve.fqMod p.xi0 (fp12Conj p.curve.fqMod (fp12Conj p.curve.fqMod a)) =
        fp12ToZMod p.curve.fqMod p.xi0 a := by
      rw [fp12Conj_hom (fp12Conj_canonical hqPos ha), fp12Conj_hom ha]
      apply ZModFp12.ext <;> simp [ZModFp12.conj]
    calc (φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 12)
        = ((φ (fp12ToZMod p.curve.fqMod p.xi0 a)) ^ (p.curve.fqMod ^ 6)) ^ (p.curve.fqMod ^ 6) := by
            rw [← pow_mul, show p.curve.fqMod ^ 6 * p.curve.fqMod ^ 6 = p.curve.fqMod ^ 12 by ring]
      _ = (φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Conj p.curve.fqMod a))) ^ (p.curve.fqMod ^ 6) := by
            rw [hConj a ha]
      _ = φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12Conj p.curve.fqMod (fp12Conj p.curve.fqMod a))) := by
            rw [← hConj _ (fp12Conj_canonical hqPos ha)]
      _ = φ (fp12ToZMod p.curve.fqMod p.xi0 a) := by rw [hconj2]
  have hFp6Fixed : ∀ s : Fp6, fp6Canonical p.curve.fqMod s = true →
      (φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12OfFp6 s))) ^ (p.curve.fqMod ^ 6) =
        φ (fp12ToZMod p.curve.fqMod p.xi0 (fp12OfFp6 s)) := by
    intro s hs
    have hconjSelf : fp12Conj p.curve.fqMod (fp12OfFp6 s) = fp12OfFp6 s := by
      simp [fp12Conj, fp12OfFp6, fp6Neg, fp6Zero, fp2Neg, fp2Zero, fqNeg, fqSubMod]
    rw [← hConj (fp12OfFp6 s) (fp12OfFp6_canonical hqPos hs), hconjSelf]
  exact ⟨hFrob1, hFrob2, hFrob3, hConj, hPow12, hFp6Fixed⟩

set_option maxRecDepth 20000 in
/-- Kernel-verified Frobenius constant validity for production 254-bit BN254. -/
theorem bn254_frobConstantsValid : FrobConstantsValid bn254PairingParams := by
  have hqPos : 0 < bn254Fp := bn254FqModulus_pos
  have hxiCan : fp2Canonical bn254Fp { c0 := 9, c1 := 1 } = true := by decide
  have hexpLt : (bn254Fp - 1) / 6 < 2 ^ 256 := by decide
  have hw1Exec : fp2Pow bn254Fp 256 { c0 := 9, c1 := 1 } ((bn254Fp - 1) / 6) =
      bn254PairingParams.frob12C1_1 := by decide
  have hc11Exec : fp2Sqr bn254Fp bn254PairingParams.frob12C1_1 = bn254PairingParams.frob6C1_1 := by decide
  have hc21Exec : fp2Sqr bn254Fp bn254PairingParams.frob6C1_1 = bn254PairingParams.frob6C2_1 := by decide
  have hc12Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob6C1_1)
      bn254PairingParams.frob6C1_1 = bn254PairingParams.frob6C1_2 := by decide
  have hc22Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob6C2_1)
      bn254PairingParams.frob6C2_1 = bn254PairingParams.frob6C2_2 := by decide
  have hw12Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob12C1_1)
      bn254PairingParams.frob12C1_1 = bn254PairingParams.frob12C1_2 := by decide
  have hc13Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob6C1_2)
      bn254PairingParams.frob6C1_1 = bn254PairingParams.frob6C1_3 := by decide
  have hc23Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob6C2_2)
      bn254PairingParams.frob6C2_1 = bn254PairingParams.frob6C2_3 := by decide
  have hw13Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob12C1_2)
      bn254PairingParams.frob12C1_1 = bn254PairingParams.frob12C1_3 := by decide
  have hc16Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob6C1_3)
      bn254PairingParams.frob6C1_3 = fp2One := by decide
  have hc26Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob6C2_3)
      bn254PairingParams.frob6C2_3 = fp2One := by decide
  have hw16Exec : fp2Mul bn254Fp (fp2Conj bn254Fp bn254PairingParams.frob12C1_3)
      bn254PairingParams.frob12C1_3 = fp2Neg bn254Fp fp2One := by decide
  refine
    { q_mod_4 := by decide
      q_mod_6 := by decide
      w1_1_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hw1Exec.symm
        rw [fp2Pow_hom hqPos 256 hexpLt hxiCan] at h
        exact h
      c1_1_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc11Exec.symm
        rw [fp2Sqr_hom (by decide), ← sq] at h; exact h
      c2_1_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc21Exec.symm
        rw [fp2Sqr_hom (by decide), ← sq] at h; exact h
      c1_2_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc12Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c2_2_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc22Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      w1_2_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hw12Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c1_3_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc13Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c2_3_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc23Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      w1_3_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hw13Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c1_6_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc16Exec
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide), fp2ToZMod_one] at h; exact h
      c2_6_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hc26Exec
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide), fp2ToZMod_one] at h; exact h
      w1_6_eq := by
        have h := congrArg (fp2ToZMod bn254Fp) hw16Exec
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide), fp2Neg_hom (by decide), fp2ToZMod_one] at h
        exact h }

set_option maxRecDepth 20000 in
set_option exponentiation.threshold 512 in
/-- Kernel-verified Frobenius constant validity for production 381-bit BLS12-381. -/
theorem bls12381_frobConstantsValid : FrobConstantsValid bls12381PairingParams := by
  have hqPos : 0 < bls12381Fp := bls12381FqModulus_pos
  have hxiCan : fp2Canonical bls12381Fp { c0 := 1, c1 := 1 } = true := by decide
  have hexpLt : (bls12381Fp - 1) / 6 < 2 ^ 384 := by decide
  have hw1Exec : fp2Pow bls12381Fp 384 { c0 := 1, c1 := 1 } ((bls12381Fp - 1) / 6) =
      bls12381PairingParams.frob12C1_1 := by decide
  have hc11Exec : fp2Sqr bls12381Fp bls12381PairingParams.frob12C1_1 = bls12381PairingParams.frob6C1_1 := by decide
  have hc21Exec : fp2Sqr bls12381Fp bls12381PairingParams.frob6C1_1 = bls12381PairingParams.frob6C2_1 := by decide
  have hc12Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob6C1_1)
      bls12381PairingParams.frob6C1_1 = bls12381PairingParams.frob6C1_2 := by decide
  have hc22Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob6C2_1)
      bls12381PairingParams.frob6C2_1 = bls12381PairingParams.frob6C2_2 := by decide
  have hw12Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob12C1_1)
      bls12381PairingParams.frob12C1_1 = bls12381PairingParams.frob12C1_2 := by decide
  have hc13Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob6C1_2)
      bls12381PairingParams.frob6C1_1 = bls12381PairingParams.frob6C1_3 := by decide
  have hc23Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob6C2_2)
      bls12381PairingParams.frob6C2_1 = bls12381PairingParams.frob6C2_3 := by decide
  have hw13Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob12C1_2)
      bls12381PairingParams.frob12C1_1 = bls12381PairingParams.frob12C1_3 := by decide
  have hc16Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob6C1_3)
      bls12381PairingParams.frob6C1_3 = fp2One := by decide
  have hc26Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob6C2_3)
      bls12381PairingParams.frob6C2_3 = fp2One := by decide
  have hw16Exec : fp2Mul bls12381Fp (fp2Conj bls12381Fp bls12381PairingParams.frob12C1_3)
      bls12381PairingParams.frob12C1_3 = fp2Neg bls12381Fp fp2One := by decide
  refine
    { q_mod_4 := by decide
      q_mod_6 := by decide
      w1_1_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hw1Exec.symm
        rw [fp2Pow_hom hqPos 384 hexpLt hxiCan] at h
        exact h
      c1_1_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc11Exec.symm
        rw [fp2Sqr_hom (by decide), ← sq] at h; exact h
      c2_1_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc21Exec.symm
        rw [fp2Sqr_hom (by decide), ← sq] at h; exact h
      c1_2_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc12Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c2_2_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc22Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      w1_2_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hw12Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c1_3_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc13Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c2_3_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc23Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      w1_3_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hw13Exec.symm
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide)] at h; exact h
      c1_6_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc16Exec
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide), fp2ToZMod_one] at h; exact h
      c2_6_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hc26Exec
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide), fp2ToZMod_one] at h; exact h
      w1_6_eq := by
        have h := congrArg (fp2ToZMod bls12381Fp) hw16Exec
        rw [fp2Mul_hom hqPos, fp2Conj_hom (by decide), fp2Neg_hom (by decide), fp2ToZMod_one] at h
        exact h }

/-! ### 3.3 Number-Theoretic Divisibility Certificates & Residue-Witnessed Final Exponentiation Soundness -/

private theorem field_eq_one_of_pow_coprime {K : Type*} [Field K] {x : K} (hx : x ≠ 0)
    {m n : Nat} (hm : x ^ m = 1) (hn : x ^ n = 1) (hcop : Nat.Coprime m n) : x = 1 := by
  let u : Kˣ := Units.mk0 x hx
  have hum : u ^ m = 1 := Units.ext (by simpa [u] using hm)
  have hun : u ^ n = 1 := Units.ext (by simpa [u] using hn)
  have hd1 : orderOf u ∣ m := orderOf_dvd_of_pow_eq_one hum
  have hd2 : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one hun
  have hd : orderOf u ∣ Nat.gcd m n := Nat.dvd_gcd hd1 hd2
  rw [hcop.gcd_eq_one] at hd
  have hu1 : u = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  exact congrArg Units.val hu1

private theorem pow12_sub_one_eq_mul (q : Nat) (hq : 1 ≤ q) :
    q ^ 12 - 1 = (q ^ 6 - 1) * (q ^ 6 + 1) := by
  have h1 : 1 ≤ q ^ 6 := Nat.one_le_pow 6 q hq
  have h12 : q ^ 12 = q ^ 6 * q ^ 6 := by ring
  rw [h12]
  zify [h1, (show 1 ≤ q ^ 6 * q ^ 6 by nlinarith)]
  ring

private theorem coprime_pow6_sub_one_of_dvd_pow6_add_one {q r : Nat}
    (hrPrime : Nat.Prime r) (hrGt2 : 2 < r) (hq : 1 ≤ q) (hdvd : r ∣ q ^ 6 + 1) :
    Nat.Coprime (q ^ 6 - 1) r := by
  rw [Nat.coprime_comm]
  refine hrPrime.coprime_iff_not_dvd.mpr ?_
  intro hdvdSub
  have h1 : 1 ≤ q ^ 6 := Nat.one_le_pow 6 q hq
  have hdiff : (q ^ 6 + 1) - (q ^ 6 - 1) = 2 := by omega
  have hd2 : r ∣ 2 := hdiff ▸ Nat.dvd_sub hdvd hdvdSub
  have hle : r ≤ 2 := Nat.le_of_dvd (by decide) hd2
  omega

/-- BN254 embedding-degree divisibility: `bn254Fr ∣ bn254Fp ^ 6 + 1` (and `bn254Fr ∣ bn254Fp ^ 12 - 1`). -/
theorem bn254Fr_dvd_fp6_add_one : bn254Fr ∣ bn254Fp ^ 6 + 1 := by
  have hmod : ((bn254Fp % bn254Fr) ^ 6 + 1) % bn254Fr = 0 := by decide
  have hcast : ((bn254Fp ^ 6 + 1 : Nat) : ZMod bn254Fr) = 0 := by
    have h1 : (((bn254Fp % bn254Fr) ^ 6 + 1 : Nat) : ZMod bn254Fr) = 0 := by
      rw [← ZMod.natCast_mod, hmod, Nat.cast_zero]
    simpa [Nat.cast_add, Nat.cast_pow, ZMod.natCast_mod] using h1
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

theorem bn254Fr_dvd_fp12_sub_one : bn254Fr ∣ bn254Fp ^ 12 - 1 := by
  rw [pow12_sub_one_eq_mul bn254Fp (by decide)]
  exact dvd_mul_of_dvd_right bn254Fr_dvd_fp6_add_one _

theorem bn254_coprime_fp6_sub_one_fr : Nat.Coprime (bn254Fp ^ 6 - 1) bn254Fr :=
  coprime_pow6_sub_one_of_dvd_pow6_add_one
    (Fact.out : Nat.Prime bn254FrModulus) (by decide) (by decide) bn254Fr_dvd_fp6_add_one

/-- BN254 hard-part exponent identity: `r ∣ (6x + 2 + q - q² + q³)`. -/
theorem bn254_lambda_dvd :
    ∃ k : Nat,
      bn254PairingParams.loopExp + bn254Fp + bn254Fp ^ 3 = bn254Fp ^ 2 + bn254Fr * k := by
  have hqGe : bn254Fp ^ 2 ≤ bn254Fp ^ 3 := by
    have h1 : 1 ≤ bn254Fp := by decide
    have : bn254Fp ^ 2 * 1 ≤ bn254Fp ^ 2 * bn254Fp := Nat.mul_le_mul_left _ h1
    simpa [pow_succ] using this
  have hmod :
      ((bn254PairingParams.loopExp % bn254Fr) + (bn254Fp % bn254Fr) +
        (bn254Fp % bn254Fr) ^ 3) % bn254Fr =
      ((bn254Fp % bn254Fr) ^ 2) % bn254Fr := by decide
  have hcast :
      (((bn254PairingParams.loopExp + bn254Fp + bn254Fp ^ 3 - bn254Fp ^ 2 : Nat)) : ZMod bn254Fr) = 0 := by
    have hsub : bn254Fp ^ 2 ≤ bn254PairingParams.loopExp + bn254Fp + bn254Fp ^ 3 := by omega
    rw [Nat.cast_sub hsub, sub_eq_zero]
    have h1 : (((bn254PairingParams.loopExp % bn254Fr + bn254Fp % bn254Fr +
        (bn254Fp % bn254Fr) ^ 3 : Nat)) : ZMod bn254Fr) =
        ((((bn254Fp % bn254Fr) ^ 2 : Nat)) : ZMod bn254Fr) := by
      rw [← ZMod.natCast_mod, hmod, ZMod.natCast_mod]
    simpa [Nat.cast_add, Nat.cast_pow, ZMod.natCast_mod] using h1
  obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  exact ⟨k, by omega⟩

/-- Every entry `w_k` (`k ∈ {0, 1, 2}`) in the compile-time BN254 residue table is canonical,
nonzero, lies in `Fp6*`, and satisfies `w_k ^ 27 = 1` in `ZModFp6 bn254Fp 9`. -/
theorem bn254ResidueTable_spec :
    (fp6Canonical bn254Fp bn254ResidueW0 = true ∧ bn254ResidueW0 ≠ fp6Zero ∧
      (fp6ToZMod bn254Fp 9 bn254ResidueW0) ^ 27 = 1) ∧
    (fp6Canonical bn254Fp bn254ResidueW1 = true ∧ bn254ResidueW1 ≠ fp6Zero ∧
      (fp6ToZMod bn254Fp 9 bn254ResidueW1) ^ 27 = 1) ∧
    (fp6Canonical bn254Fp bn254ResidueW2 = true ∧ bn254ResidueW2 ≠ fp6Zero ∧
      (fp6ToZMod bn254Fp 9 bn254ResidueW2) ^ 27 = 1) := by
  have hqPos : 0 < bn254Fp := bn254FqModulus_pos
  have hPow27 : ∀ w : Fp6,
      fp6Mul bn254Fp 9 (fp6Mul bn254Fp 9 (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))
        (fp6Mul bn254Fp 9 (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))
          (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))))
        (fp6Mul bn254Fp 9
          (fp6Mul bn254Fp 9 (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))
            (fp6Mul bn254Fp 9 (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))
              (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))))
          (fp6Mul bn254Fp 9 (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))
            (fp6Mul bn254Fp 9 (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))
              (fp6Mul bn254Fp 9 w (fp6Mul bn254Fp 9 w w))))) = fp6One →
      (fp6ToZMod bn254Fp 9 w) ^ 27 = 1 := by
    intro w heq
    have h := congrArg (fp6ToZMod bn254Fp 9) heq
    simp only [fp6Mul_hom hqPos 9, fp6ToZMod_one] at h
    convert h using 1; ring
  refine ⟨⟨by decide, by decide, hPow27 bn254ResidueW0 (by decide)⟩,
          ⟨by decide, by decide, hPow27 bn254ResidueW1 (by decide)⟩,
          ⟨by decide, by decide, hPow27 bn254ResidueW2 (by decide)⟩⟩

/-- BLS12-381 embedding-degree divisibility: `bls12381Fr ∣ bls12381Fp ^ 6 + 1`. -/
theorem bls12381Fr_dvd_fp6_add_one : bls12381Fr ∣ bls12381Fp ^ 6 + 1 := by
  have hmod : ((bls12381Fp % bls12381Fr) ^ 6 + 1) % bls12381Fr = 0 := by decide
  have hcast : ((bls12381Fp ^ 6 + 1 : Nat) : ZMod bls12381Fr) = 0 := by
    have h1 : (((bls12381Fp % bls12381Fr) ^ 6 + 1 : Nat) : ZMod bls12381Fr) = 0 := by
      rw [← ZMod.natCast_mod, hmod, Nat.cast_zero]
    simpa [Nat.cast_add, Nat.cast_pow, ZMod.natCast_mod] using h1
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

theorem bls12381Fr_dvd_fp12_sub_one : bls12381Fr ∣ bls12381Fp ^ 12 - 1 := by
  rw [pow12_sub_one_eq_mul bls12381Fp (by decide)]
  exact dvd_mul_of_dvd_right bls12381Fr_dvd_fp6_add_one _

theorem bls12381_coprime_fp6_sub_one_fr : Nat.Coprime (bls12381Fp ^ 6 - 1) bls12381Fr :=
  coprime_pow6_sub_one_of_dvd_pow6_add_one
    (Fact.out : Nat.Prime bls12381FrModulus) (by decide) (by decide) bls12381Fr_dvd_fp6_add_one

/-- BLS12-381 hard-part exponent identity: `q + |x| = h₁ * r` (`bls12381G1_order_identity`). -/
theorem bls12381_lambda_eq :
    bls12381Fp + bls12381PairingParams.loopExp = bls12381G1Cofactor * bls12381Fr :=
  bls12381G1_order_identity.symm

/-- **BN254 Unitary Final Exponentiation Witness Soundness (`verifyFinalExpWitness_bn254_sound`):**
When `verifyFinalExpWitness bn254PairingParams f c = 1` on canonical `f`:
1. `f ≠ 0`, `c` is canonical (`< q` in all 12 coordinates), and `c ≠ 0`;
2. `conj(f) · c^{q²} = f · c^{6x+2} · c^q · c^{q³}` holds identically in `ZModFp12 bn254Fp 9`;
3. For ANY field `K` and ANY ring hom `φ : ZModFp12 bn254Fp 9 →+* K` with `φ f ≠ 0` and `φ c ≠ 0`,
   the exact final exponentiation equation holds: `(φ f) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1`! -/
theorem verifyFinalExpWitness_bn254_sound {f c : Fp12}
    (hfCan : fp12Canonical bn254Fp f = true)
    (h : verifyFinalExpWitness bn254PairingParams f c = 1) :
    f ≠ fp12Zero ∧
    fp12Canonical bn254Fp c = true ∧
    c ≠ fp12Zero ∧
    ZModFp12.conj (fp12ToZMod bn254Fp 9 f) *
        fp12ToZMod bn254Fp 9 (fp12Frob2 bn254PairingParams c) =
      fp12ToZMod bn254Fp 9 f *
        ((fp12ToZMod bn254Fp 9 c) ^ bn254PairingParams.loopExp *
          (fp12ToZMod bn254Fp 9 (fp12Frob1 bn254PairingParams c) *
            fp12ToZMod bn254Fp 9 (fp12Frob3 bn254PairingParams c))) ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bn254Fp 9 →+* K),
      φ (fp12ToZMod bn254Fp 9 f) ≠ 0 →
      φ (fp12ToZMod bn254Fp 9 c) ≠ 0 →
      (φ (fp12ToZMod bn254Fp 9 f)) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1 := by
  have hqPos : 0 < bn254Fp := bn254FqModulus_pos
  unfold verifyFinalExpWitness at h
  dsimp only at h
  have hisBn : bn254PairingParams.isBn = 1 := rfl
  have hloopLt : bn254PairingParams.loopExp < 2 ^ bn254PairingParams.loopBits := by decide
  rw [hisBn] at h
  simp only [beq_self_eq_true, ↓reduceIte] at h
  split_ifs at h with hf0 hcCan hc0 heq
  have hfNe : f ≠ fp12Zero := fun hz => hf0 ((fp12IsZero_iff f).mpr hz)
  have hcNe : c ≠ fp12Zero := fun hz => hc0 ((fp12IsZero_iff c).mpr hz)
  have heqFp12 := (fp12Eq_iff _ _).mp heq
  have hRingEq :
      ZModFp12.conj (fp12ToZMod bn254Fp 9 f) *
        fp12ToZMod bn254Fp 9 (fp12Frob2 bn254PairingParams c) =
      fp12ToZMod bn254Fp 9 f *
        ((fp12ToZMod bn254Fp 9 c) ^ bn254PairingParams.loopExp *
          (fp12ToZMod bn254Fp 9 (fp12Frob1 bn254PairingParams c) *
            fp12ToZMod bn254Fp 9 (fp12Frob3 bn254PairingParams c))) := by
    have heq' :
        fp12Mul bn254Fp 9 (fp12Conj bn254Fp f) (fp12Frob2 bn254PairingParams c) =
        fp12Mul bn254Fp 9 f
          (fp12Mul bn254Fp 9 (fp12Pow bn254Fp 9 bn254PairingParams.loopBits c bn254PairingParams.loopExp)
            (fp12Mul bn254Fp 9 (fp12Frob1 bn254PairingParams c) (fp12Frob3 bn254PairingParams c))) :=
      heqFp12
    have hz := congrArg (fp12ToZMod bn254Fp 9) heq'
    rw [fp12Mul_hom hqPos 9, fp12Mul_hom hqPos 9, fp12Mul_hom hqPos 9, fp12Mul_hom hqPos 9,
      fp12Conj_hom hfCan, fp12Pow_hom hqPos 9 _ hloopLt hcCan] at hz
    exact hz
  refine ⟨hfNe, hcCan, hcNe, hRingEq, ?_⟩
  intro K _ φ hφf hφc
  have : Fact (Nat.Prime bn254PairingParams.curve.fqMod) :=
    inferInstanceAs (Fact (Nat.Prime bn254FqModulus))
  obtain ⟨hF1, hF2, hF3, hConj, hPow12, _⟩ := fp12Frob_field_sound bn254_frobConstantsValid φ
  set F := φ (fp12ToZMod bn254Fp 9 f)
  set C := φ (fp12ToZMod bn254Fp 9 c)
  have hEqK : F ^ (bn254Fp ^ 6) * C ^ (bn254Fp ^ 2) =
      F * (C ^ bn254PairingParams.loopExp * (C ^ bn254Fp * C ^ (bn254Fp ^ 3))) := by
    have hmap := congrArg φ hRingEq
    simp only [map_mul, map_pow] at hmap
    have hConj' : φ (fp12ToZMod bn254Fp 9 (fp12Conj bn254Fp f)) = F ^ (bn254Fp ^ 6) := hConj f hfCan
    have hF1' : φ (fp12ToZMod bn254Fp 9 (fp12Frob1 bn254PairingParams c)) = C ^ bn254Fp := hF1 c hcCan
    have hF2' : φ (fp12ToZMod bn254Fp 9 (fp12Frob2 bn254PairingParams c)) = C ^ (bn254Fp ^ 2) := hF2 c hcCan
    have hF3' : φ (fp12ToZMod bn254Fp 9 (fp12Frob3 bn254PairingParams c)) = C ^ (bn254Fp ^ 3) := hF3 c hcCan
    rw [← fp12Conj_hom hfCan, hConj', hF2', hF1', hF3'] at hmap
    exact hmap
  obtain ⟨k, hk⟩ := bn254_lambda_dvd
  have hCpow : C ^ bn254PairingParams.loopExp * (C ^ bn254Fp * C ^ (bn254Fp ^ 3)) =
      C ^ (bn254Fp ^ 2) * C ^ (bn254Fr * k) := by
    rw [← pow_add, ← pow_add, ← add_assoc, hk, pow_add]
  rw [hCpow] at hEqK
  have hC2Ne : C ^ (bn254Fp ^ 2) ≠ 0 := pow_ne_zero _ hφc
  have hEq1 : F ^ (bn254Fp ^ 6) = F * C ^ (bn254Fr * k) := by
    apply mul_right_cancel₀ hC2Ne
    linear_combination hEqK
  have h1q6 : 1 ≤ bn254Fp ^ 6 := Nat.one_le_pow 6 bn254Fp (by decide)
  have hFsub : F ^ (bn254Fp ^ 6 - 1) = C ^ (bn254Fr * k) := by
    apply mul_left_cancel₀ hφf
    rw [← pow_succ', Nat.sub_add_cancel h1q6, hEq1]
  have h1q12 : 1 ≤ bn254Fp ^ 12 := Nat.one_le_pow 12 bn254Fp (by decide)
  have hF12 : F ^ (bn254Fp ^ 12 - 1) = 1 := by
    apply mul_left_cancel₀ hφf
    rw [← pow_succ', Nat.sub_add_cancel h1q12, mul_one]
    exact hPow12 f hfCan
  have hC12 : C ^ (bn254Fp ^ 12 - 1) = 1 := by
    apply mul_left_cancel₀ hφc
    rw [← pow_succ', Nat.sub_add_cancel h1q12, mul_one]
    exact hPow12 c hcCan
  set E := (bn254Fp ^ 12 - 1) / bn254Fr
  have hrE : bn254Fr * E = bn254Fp ^ 12 - 1 := Nat.mul_div_cancel' bn254Fr_dvd_fp12_sub_one
  have hgR : (F ^ E) ^ bn254Fr = 1 := by
    rw [← pow_mul, Nat.mul_comm E bn254Fr, hrE, hF12]
  have hgQ6 : (F ^ E) ^ (bn254Fp ^ 6 - 1) = 1 := by
    rw [← pow_mul, Nat.mul_comm E, pow_mul, hFsub, ← pow_mul,
      show bn254Fr * k * E = (bn254Fr * E) * k by ring, hrE, pow_mul, hC12, one_pow]
  exact field_eq_one_of_pow_coprime (pow_ne_zero E hφf) hgQ6 hgR bn254_coprime_fp6_sub_one_fr

/-- **BN254 $\mathbb{F}_{q^6}^*$-Scaled Final Exponentiation Witness Soundness
(`verifyFinalExpWitnessFp6_bn254_sound`):**
When `verifyFinalExpWitnessFp6 bn254PairingParams f c s = 1` on canonical `f`:
1. `f ≠ 0`, `c` is canonical & nonzero, `s` is canonical & nonzero;
2. `f · s · c^{q²} = c^{6x+2} · c^q · c^{q³}` in `ZModFp12 bn254Fp 9`;
3. For ANY field `K` and ANY ring hom `φ : ZModFp12 bn254Fp 9 →+* K` with
   `φ f ≠ 0`, `φ c ≠ 0`, `φ (fp12OfFp6 s) ≠ 0`, `(φ f) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1`! -/
theorem verifyFinalExpWitnessFp6_bn254_sound {f c : Fp12} {s : Fp6}
    (h : verifyFinalExpWitnessFp6 bn254PairingParams f c s = 1) :
    f ≠ fp12Zero ∧
    fp12Canonical bn254Fp c = true ∧
    c ≠ fp12Zero ∧
    fp6Canonical bn254Fp s = true ∧
    s ≠ fp6Zero ∧
    fp12ToZMod bn254Fp 9 f * ZModFp12.ofFp6 (fp6ToZMod bn254Fp 9 s) *
        fp12ToZMod bn254Fp 9 (fp12Frob2 bn254PairingParams c) =
      (fp12ToZMod bn254Fp 9 c) ^ bn254PairingParams.loopExp *
        (fp12ToZMod bn254Fp 9 (fp12Frob1 bn254PairingParams c) *
          fp12ToZMod bn254Fp 9 (fp12Frob3 bn254PairingParams c)) ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bn254Fp 9 →+* K),
      φ (fp12ToZMod bn254Fp 9 f) ≠ 0 →
      φ (fp12ToZMod bn254Fp 9 c) ≠ 0 →
      φ (fp12ToZMod bn254Fp 9 (fp12OfFp6 s)) ≠ 0 →
      (φ (fp12ToZMod bn254Fp 9 f)) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1 := by
  have hqPos : 0 < bn254Fp := bn254FqModulus_pos
  unfold verifyFinalExpWitnessFp6 at h
  dsimp only at h
  have hisBn : bn254PairingParams.isBn = 1 := rfl
  have hloopLt : bn254PairingParams.loopExp < 2 ^ bn254PairingParams.loopBits := by decide
  rw [hisBn] at h
  simp only [beq_self_eq_true, ↓reduceIte] at h
  split_ifs at h with hf0 hcCan hc0 hsCan hs0 heq
  have hfNe : f ≠ fp12Zero := fun hz => hf0 ((fp12IsZero_iff f).mpr hz)
  have hcNe : c ≠ fp12Zero := fun hz => hc0 ((fp12IsZero_iff c).mpr hz)
  have hsNe : s ≠ fp6Zero := fun hz => hs0 ((fp6IsZero_iff s).mpr hz)
  have heqFp12 := (fp12Eq_iff _ _).mp heq
  have hRingEq :
      fp12ToZMod bn254Fp 9 f * ZModFp12.ofFp6 (fp6ToZMod bn254Fp 9 s) *
        fp12ToZMod bn254Fp 9 (fp12Frob2 bn254PairingParams c) =
      (fp12ToZMod bn254Fp 9 c) ^ bn254PairingParams.loopExp *
        (fp12ToZMod bn254Fp 9 (fp12Frob1 bn254PairingParams c) *
          fp12ToZMod bn254Fp 9 (fp12Frob3 bn254PairingParams c)) := by
    have heq' :
        fp12Mul bn254Fp 9 (fp12Mul bn254Fp 9 f (fp12OfFp6 s)) (fp12Frob2 bn254PairingParams c) =
        fp12Mul bn254Fp 9 (fp12Pow bn254Fp 9 bn254PairingParams.loopBits c bn254PairingParams.loopExp)
          (fp12Mul bn254Fp 9 (fp12Frob1 bn254PairingParams c) (fp12Frob3 bn254PairingParams c)) :=
      heqFp12
    have hz := congrArg (fp12ToZMod bn254Fp 9) heq'
    rw [fp12Mul_hom hqPos 9, fp12Mul_hom hqPos 9, fp12Mul_hom hqPos 9, fp12Mul_hom hqPos 9,
      fp12OfFp6_hom, fp12Pow_hom hqPos 9 _ hloopLt hcCan] at hz
    exact hz
  refine ⟨hfNe, hcCan, hcNe, hsCan, hsNe, hRingEq, ?_⟩
  intro K _ φ _ hφc hφs
  have : Fact (Nat.Prime bn254PairingParams.curve.fqMod) :=
    inferInstanceAs (Fact (Nat.Prime bn254FqModulus))
  obtain ⟨hF1, hF2, hF3, _, hPow12, hFp6Fixed⟩ := fp12Frob_field_sound bn254_frobConstantsValid φ
  set F := φ (fp12ToZMod bn254Fp 9 f)
  set C := φ (fp12ToZMod bn254Fp 9 c)
  set S := φ (fp12ToZMod bn254Fp 9 (fp12OfFp6 s))
  have hEqK : F * S * C ^ (bn254Fp ^ 2) =
      C ^ bn254PairingParams.loopExp * (C ^ bn254Fp * C ^ (bn254Fp ^ 3)) := by
    have hmap := congrArg φ hRingEq
    simp only [map_mul, map_pow] at hmap
    have hF1' : φ (fp12ToZMod bn254Fp 9 (fp12Frob1 bn254PairingParams c)) = C ^ bn254Fp := hF1 c hcCan
    have hF2' : φ (fp12ToZMod bn254Fp 9 (fp12Frob2 bn254PairingParams c)) = C ^ (bn254Fp ^ 2) := hF2 c hcCan
    have hF3' : φ (fp12ToZMod bn254Fp 9 (fp12Frob3 bn254PairingParams c)) = C ^ (bn254Fp ^ 3) := hF3 c hcCan
    rw [← fp12OfFp6_hom bn254Fp 9 s, hF2', hF1', hF3'] at hmap
    exact hmap
  obtain ⟨k, hk⟩ := bn254_lambda_dvd
  have hCpow : C ^ bn254PairingParams.loopExp * (C ^ bn254Fp * C ^ (bn254Fp ^ 3)) =
      C ^ (bn254Fp ^ 2) * C ^ (bn254Fr * k) := by
    rw [← pow_add, ← pow_add, ← add_assoc, hk, pow_add]
  rw [hCpow] at hEqK
  have hFS : F * S = C ^ (bn254Fr * k) := by
    apply mul_right_cancel₀ (pow_ne_zero (bn254Fp ^ 2) hφc)
    linear_combination hEqK
  have h1q6 : 1 ≤ bn254Fp ^ 6 := Nat.one_le_pow 6 bn254Fp (by decide)
  have h1q12 : 1 ≤ bn254Fp ^ 12 := Nat.one_le_pow 12 bn254Fp (by decide)
  have hS6 : S ^ (bn254Fp ^ 6 - 1) = 1 := by
    apply mul_left_cancel₀ hφs
    rw [← pow_succ', Nat.sub_add_cancel h1q6, mul_one]
    exact hFp6Fixed s hsCan
  have hC12 : C ^ (bn254Fp ^ 12 - 1) = 1 := by
    apply mul_left_cancel₀ hφc
    rw [← pow_succ', Nat.sub_add_cancel h1q12, mul_one]
    exact hPow12 c hcCan
  set E := (bn254Fp ^ 12 - 1) / bn254Fr
  have hrE : bn254Fr * E = bn254Fp ^ 12 - 1 := Nat.mul_div_cancel' bn254Fr_dvd_fp12_sub_one
  have hEfac : E = (bn254Fp ^ 6 - 1) * ((bn254Fp ^ 6 + 1) / bn254Fr) := by
    dsimp only [E]
    rw [pow12_sub_one_eq_mul bn254Fp (by decide), Nat.mul_div_assoc _ bn254Fr_dvd_fp6_add_one]
  have hSE : S ^ E = 1 := by rw [hEfac, pow_mul, hS6, one_pow]
  have hFSE : (F * S) ^ E = 1 := by
    rw [hFS, ← pow_mul, show bn254Fr * k * E = (bn254Fr * E) * k by ring, hrE, pow_mul, hC12, one_pow]
  rw [mul_pow, hSE, mul_one] at hFSE
  exact hFSE

/-- **BN254 Fixed `d = 3` Residue-Table Final Exponentiation Soundness
(`verifyFinalExpTableBN254_sound`):**
When `verifyFinalExpTableBN254 f c wIdx = 1` on canonical `f`:
`wIdx < 3`, the selected residue `w ∈ {W0, W1, W2} ⊂ Fp6*` has `w ^ 27 = 1`, satisfies
`f · w · c^{q²} = c^{6x+2} · c^q · c^{q³}`, and `(φ f) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1`
in ANY field `K` receiving `φ : ZModFp12 bn254Fp 9 →+* K` with `φ f ≠ 0`, `φ c ≠ 0`!
(Note: `φ (fp12OfFp6 w) ≠ 0` is AUTOMATIC because `w ^ 27 = 1` in `ZModFp6`!) -/
theorem verifyFinalExpTableBN254_sound.{u} {f c : Fp12} {wIdx : Nat}
    (h : verifyFinalExpTableBN254 f c wIdx = 1) :
    wIdx < 3 ∧
    f ≠ fp12Zero ∧
    fp12Canonical bn254Fp c = true ∧
    c ≠ fp12Zero ∧
    ∃ w : Fp6,
      ((wIdx = 0 ∧ w = bn254ResidueW0) ∨
       (wIdx = 1 ∧ w = bn254ResidueW1) ∨
       (wIdx = 2 ∧ w = bn254ResidueW2)) ∧
      (fp6ToZMod bn254Fp 9 w) ^ 27 = 1 ∧
      fp12ToZMod bn254Fp 9 f * ZModFp12.ofFp6 (fp6ToZMod bn254Fp 9 w) *
          fp12ToZMod bn254Fp 9 (fp12Frob2 bn254PairingParams c) =
        (fp12ToZMod bn254Fp 9 c) ^ bn254PairingParams.loopExp *
          (fp12ToZMod bn254Fp 9 (fp12Frob1 bn254PairingParams c) *
            fp12ToZMod bn254Fp 9 (fp12Frob3 bn254PairingParams c)) ∧
      ∀ {K : Type u} [Field K] (φ : ZModFp12 bn254Fp 9 →+* K),
        φ (fp12ToZMod bn254Fp 9 f) ≠ 0 →
        φ (fp12ToZMod bn254Fp 9 c) ≠ 0 →
        (φ (fp12ToZMod bn254Fp 9 f)) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1 := by
  have hNzOfPow27 : ∀ {w : Fp6} {K : Type u} [Field K] (φ : ZModFp12 bn254Fp 9 →+* K),
      (fp6ToZMod bn254Fp 9 w) ^ 27 = 1 →
      φ (fp12ToZMod bn254Fp 9 (fp12OfFp6 w)) ≠ 0 := by
    intro w K _ φ hw27 h0
    have hpow : (φ (fp12ToZMod bn254Fp 9 (fp12OfFp6 w))) ^ 27 = 1 := by
      rw [fp12OfFp6_hom]
      change (φ (zmodFp6ToFp12 bn254Fp 9 (fp6ToZMod bn254Fp 9 w))) ^ 27 = 1
      rw [← map_pow, ← map_pow, hw27, map_one, map_one]
    rw [h0, zero_pow (by decide)] at hpow
    exact zero_ne_one hpow
  unfold verifyFinalExpTableBN254 at h
  split_ifs at h with h0 h1 h2
  · have hw0 : wIdx = 0 := beq_iff_eq.mp h0
    obtain ⟨hfNe, hcCan, hcNe, _, _, hEq, hFinal⟩ := verifyFinalExpWitnessFp6_bn254_sound h
    have hw27 := bn254ResidueTable_spec.1.2.2
    exact ⟨by omega, hfNe, hcCan, hcNe, bn254ResidueW0, Or.inl ⟨hw0, rfl⟩, hw27, hEq,
      fun φ hφf hφc => hFinal φ hφf hφc (hNzOfPow27 φ hw27)⟩
  · have hw1 : wIdx = 1 := beq_iff_eq.mp h1
    obtain ⟨hfNe, hcCan, hcNe, _, _, hEq, hFinal⟩ := verifyFinalExpWitnessFp6_bn254_sound h
    have hw27 := bn254ResidueTable_spec.2.1.2.2
    exact ⟨by omega, hfNe, hcCan, hcNe, bn254ResidueW1, Or.inr (Or.inl ⟨hw1, rfl⟩), hw27, hEq,
      fun φ hφf hφc => hFinal φ hφf hφc (hNzOfPow27 φ hw27)⟩
  · have hw2 : wIdx = 2 := beq_iff_eq.mp h2
    obtain ⟨hfNe, hcCan, hcNe, _, _, hEq, hFinal⟩ := verifyFinalExpWitnessFp6_bn254_sound h
    have hw27 := bn254ResidueTable_spec.2.2.2.2
    exact ⟨by omega, hfNe, hcCan, hcNe, bn254ResidueW2, Or.inr (Or.inr ⟨hw2, rfl⟩), hw27, hEq,
      fun φ hφf hφc => hFinal φ hφf hφc (hNzOfPow27 φ hw27)⟩

/-- **BLS12-381 Unitary Final Exponentiation Witness Soundness (`verifyFinalExpWitness_bls12381_sound`):**
When `verifyFinalExpWitness bls12381PairingParams f c = 1` on canonical `f`:
1. `f ≠ 0`, `c` is canonical (`< q` in all 12 coordinates), and `c ≠ 0`;
2. `conj(f) = f · c^q · c^{|x|}` holds identically in `ZModFp12 bls12381Fp 1`;
3. For ANY field `K` and ANY ring hom `φ : ZModFp12 bls12381Fp 1 →+* K` with `φ f ≠ 0` and `φ c ≠ 0`,
   the exact final exponentiation equation holds: `(φ f) ^ ((bls12381Fp ^ 12 - 1) / bls12381Fr) = 1`! -/
theorem verifyFinalExpWitness_bls12381_sound {f c : Fp12}
    (hfCan : fp12Canonical bls12381Fp f = true)
    (h : verifyFinalExpWitness bls12381PairingParams f c = 1) :
    f ≠ fp12Zero ∧
    fp12Canonical bls12381Fp c = true ∧
    c ≠ fp12Zero ∧
    ZModFp12.conj (fp12ToZMod bls12381Fp 1 f) =
      fp12ToZMod bls12381Fp 1 f *
        (fp12ToZMod bls12381Fp 1 (fp12Frob1 bls12381PairingParams c) *
          (fp12ToZMod bls12381Fp 1 c) ^ bls12381PairingParams.loopExp) ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bls12381Fp 1 →+* K),
      φ (fp12ToZMod bls12381Fp 1 f) ≠ 0 →
      φ (fp12ToZMod bls12381Fp 1 c) ≠ 0 →
      (φ (fp12ToZMod bls12381Fp 1 f)) ^ ((bls12381Fp ^ 12 - 1) / bls12381Fr) = 1 := by
  have hqPos : 0 < bls12381Fp := bls12381FqModulus_pos
  unfold verifyFinalExpWitness at h
  dsimp only at h
  have hisBn : bls12381PairingParams.isBn = 0 := rfl
  have hisNeg : bls12381PairingParams.isNegSeed = 1 := rfl
  have hloopLt : bls12381PairingParams.loopExp < 2 ^ bls12381PairingParams.loopBits := by decide
  rw [hisBn, hisNeg] at h
  simp only [Nat.reduceBEq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at h
  split_ifs at h with hf0 hcCan hc0 heq
  have hfNe : f ≠ fp12Zero := fun hz => hf0 ((fp12IsZero_iff f).mpr hz)
  have hcNe : c ≠ fp12Zero := fun hz => hc0 ((fp12IsZero_iff c).mpr hz)
  have heqFp12 := (fp12Eq_iff _ _).mp heq
  have hRingEq :
      ZModFp12.conj (fp12ToZMod bls12381Fp 1 f) =
      fp12ToZMod bls12381Fp 1 f *
        (fp12ToZMod bls12381Fp 1 (fp12Frob1 bls12381PairingParams c) *
          (fp12ToZMod bls12381Fp 1 c) ^ bls12381PairingParams.loopExp) := by
    have heq' :
        fp12Conj bls12381Fp f =
        fp12Mul bls12381Fp 1 f
          (fp12Mul bls12381Fp 1 (fp12Frob1 bls12381PairingParams c)
            (fp12Pow bls12381Fp 1 bls12381PairingParams.loopBits c bls12381PairingParams.loopExp)) :=
      heqFp12
    have hz := congrArg (fp12ToZMod bls12381Fp 1) heq'
    rw [fp12Mul_hom hqPos 1, fp12Mul_hom hqPos 1, fp12Conj_hom hfCan,
      fp12Pow_hom hqPos 1 _ hloopLt hcCan] at hz
    exact hz
  refine ⟨hfNe, hcCan, hcNe, hRingEq, ?_⟩
  intro K _ φ hφf hφc
  have : Fact (Nat.Prime bls12381PairingParams.curve.fqMod) :=
    inferInstanceAs (Fact (Nat.Prime bls12381FqModulus))
  obtain ⟨hF1, _, _, hConj, hPow12, _⟩ := fp12Frob_field_sound bls12381_frobConstantsValid φ
  set F := φ (fp12ToZMod bls12381Fp 1 f)
  set C := φ (fp12ToZMod bls12381Fp 1 c)
  have hEqK : F ^ (bls12381Fp ^ 6) = F * (C ^ bls12381Fp * C ^ bls12381PairingParams.loopExp) := by
    have hmap := congrArg φ hRingEq
    simp only [map_mul, map_pow] at hmap
    have hConj' : φ (fp12ToZMod bls12381Fp 1 (fp12Conj bls12381Fp f)) = F ^ (bls12381Fp ^ 6) := hConj f hfCan
    have hF1' : φ (fp12ToZMod bls12381Fp 1 (fp12Frob1 bls12381PairingParams c)) = C ^ bls12381Fp := hF1 c hcCan
    rw [← fp12Conj_hom hfCan, hConj', hF1'] at hmap
    exact hmap
  rw [← pow_add, bls12381_lambda_eq] at hEqK
  have h1q6 : 1 ≤ bls12381Fp ^ 6 := Nat.one_le_pow 6 bls12381Fp (by decide)
  have h1q12 : 1 ≤ bls12381Fp ^ 12 := Nat.one_le_pow 12 bls12381Fp (by decide)
  have hFsub : F ^ (bls12381Fp ^ 6 - 1) = C ^ (bls12381G1Cofactor * bls12381Fr) := by
    apply mul_left_cancel₀ hφf
    rw [← pow_succ', Nat.sub_add_cancel h1q6, hEqK]
  have hF12 : F ^ (bls12381Fp ^ 12 - 1) = 1 := by
    apply mul_left_cancel₀ hφf
    rw [← pow_succ', Nat.sub_add_cancel h1q12, mul_one]
    exact hPow12 f hfCan
  have hC12 : C ^ (bls12381Fp ^ 12 - 1) = 1 := by
    apply mul_left_cancel₀ hφc
    rw [← pow_succ', Nat.sub_add_cancel h1q12, mul_one]
    exact hPow12 c hcCan
  set E := (bls12381Fp ^ 12 - 1) / bls12381Fr
  have hrE : bls12381Fr * E = bls12381Fp ^ 12 - 1 := Nat.mul_div_cancel' bls12381Fr_dvd_fp12_sub_one
  have hgR : (F ^ E) ^ bls12381Fr = 1 := by
    rw [← pow_mul, Nat.mul_comm E bls12381Fr, hrE, hF12]
  have hgQ6 : (F ^ E) ^ (bls12381Fp ^ 6 - 1) = 1 := by
    rw [← pow_mul, Nat.mul_comm E, pow_mul, hFsub, ← pow_mul,
      show bls12381G1Cofactor * bls12381Fr * E = (bls12381Fr * E) * bls12381G1Cofactor by ring,
      hrE, pow_mul, hC12, one_pow]
  exact field_eq_one_of_pow_coprime (pow_ne_zero E hφf) hgQ6 hgR bls12381_coprime_fp6_sub_one_fr

/-- **BLS12-381 $\mathbb{F}_{q^6}^*$-Scaled Final Exponentiation Witness Soundness
(`verifyFinalExpWitnessFp6_bls12381_sound`):**
When `verifyFinalExpWitnessFp6 bls12381PairingParams f c s = 1` on canonical `f`,
`f · s = c^q · c^{|x|}` and `(φ f) ^ ((bls12381Fp ^ 12 - 1) / bls12381Fr) = 1`! -/
theorem verifyFinalExpWitnessFp6_bls12381_sound {f c : Fp12} {s : Fp6}
    (h : verifyFinalExpWitnessFp6 bls12381PairingParams f c s = 1) :
    f ≠ fp12Zero ∧
    fp12Canonical bls12381Fp c = true ∧
    c ≠ fp12Zero ∧
    fp6Canonical bls12381Fp s = true ∧
    s ≠ fp6Zero ∧
    fp12ToZMod bls12381Fp 1 f * ZModFp12.ofFp6 (fp6ToZMod bls12381Fp 1 s) =
      fp12ToZMod bls12381Fp 1 (fp12Frob1 bls12381PairingParams c) *
        (fp12ToZMod bls12381Fp 1 c) ^ bls12381PairingParams.loopExp ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bls12381Fp 1 →+* K),
      φ (fp12ToZMod bls12381Fp 1 f) ≠ 0 →
      φ (fp12ToZMod bls12381Fp 1 c) ≠ 0 →
      φ (fp12ToZMod bls12381Fp 1 (fp12OfFp6 s)) ≠ 0 →
      (φ (fp12ToZMod bls12381Fp 1 f)) ^ ((bls12381Fp ^ 12 - 1) / bls12381Fr) = 1 := by
  have hqPos : 0 < bls12381Fp := bls12381FqModulus_pos
  unfold verifyFinalExpWitnessFp6 at h
  dsimp only at h
  have hisBn : bls12381PairingParams.isBn = 0 := rfl
  have hisNeg : bls12381PairingParams.isNegSeed = 1 := rfl
  have hloopLt : bls12381PairingParams.loopExp < 2 ^ bls12381PairingParams.loopBits := by decide
  rw [hisBn, hisNeg] at h
  simp only [Nat.reduceBEq, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte] at h
  split_ifs at h with hf0 hcCan hc0 hsCan hs0 heq
  have hfNe : f ≠ fp12Zero := fun hz => hf0 ((fp12IsZero_iff f).mpr hz)
  have hcNe : c ≠ fp12Zero := fun hz => hc0 ((fp12IsZero_iff c).mpr hz)
  have hsNe : s ≠ fp6Zero := fun hz => hs0 ((fp6IsZero_iff s).mpr hz)
  have heqFp12 := (fp12Eq_iff _ _).mp heq
  have hRingEq :
      fp12ToZMod bls12381Fp 1 f * ZModFp12.ofFp6 (fp6ToZMod bls12381Fp 1 s) =
      fp12ToZMod bls12381Fp 1 (fp12Frob1 bls12381PairingParams c) *
        (fp12ToZMod bls12381Fp 1 c) ^ bls12381PairingParams.loopExp := by
    have heq' :
        fp12Mul bls12381Fp 1 f (fp12OfFp6 s) =
        fp12Mul bls12381Fp 1 (fp12Frob1 bls12381PairingParams c)
          (fp12Pow bls12381Fp 1 bls12381PairingParams.loopBits c bls12381PairingParams.loopExp) :=
      heqFp12
    have hz := congrArg (fp12ToZMod bls12381Fp 1) heq'
    rw [fp12Mul_hom hqPos 1, fp12Mul_hom hqPos 1, fp12OfFp6_hom,
      fp12Pow_hom hqPos 1 _ hloopLt hcCan] at hz
    exact hz
  refine ⟨hfNe, hcCan, hcNe, hsCan, hsNe, hRingEq, ?_⟩
  intro K _ φ _ hφc hφs
  have : Fact (Nat.Prime bls12381PairingParams.curve.fqMod) :=
    inferInstanceAs (Fact (Nat.Prime bls12381FqModulus))
  obtain ⟨hF1, _, _, _, hPow12, hFp6Fixed⟩ := fp12Frob_field_sound bls12381_frobConstantsValid φ
  set F := φ (fp12ToZMod bls12381Fp 1 f)
  set C := φ (fp12ToZMod bls12381Fp 1 c)
  set S := φ (fp12ToZMod bls12381Fp 1 (fp12OfFp6 s))
  have hFS : F * S = C ^ (bls12381G1Cofactor * bls12381Fr) := by
    have hmap := congrArg φ hRingEq
    simp only [map_mul, map_pow] at hmap
    have hF1' : φ (fp12ToZMod bls12381Fp 1 (fp12Frob1 bls12381PairingParams c)) = C ^ bls12381Fp := hF1 c hcCan
    rw [← fp12OfFp6_hom bls12381Fp 1 s, hF1', ← pow_add, bls12381_lambda_eq] at hmap
    exact hmap
  have h1q6 : 1 ≤ bls12381Fp ^ 6 := Nat.one_le_pow 6 bls12381Fp (by decide)
  have h1q12 : 1 ≤ bls12381Fp ^ 12 := Nat.one_le_pow 12 bls12381Fp (by decide)
  have hS6 : S ^ (bls12381Fp ^ 6 - 1) = 1 := by
    apply mul_left_cancel₀ hφs
    rw [← pow_succ', Nat.sub_add_cancel h1q6, mul_one]
    exact hFp6Fixed s hsCan
  have hC12 : C ^ (bls12381Fp ^ 12 - 1) = 1 := by
    apply mul_left_cancel₀ hφc
    rw [← pow_succ', Nat.sub_add_cancel h1q12, mul_one]
    exact hPow12 c hcCan
  set E := (bls12381Fp ^ 12 - 1) / bls12381Fr
  have hrE : bls12381Fr * E = bls12381Fp ^ 12 - 1 := Nat.mul_div_cancel' bls12381Fr_dvd_fp12_sub_one
  have hEfac : E = (bls12381Fp ^ 6 - 1) * ((bls12381Fp ^ 6 + 1) / bls12381Fr) := by
    dsimp only [E]
    rw [pow12_sub_one_eq_mul bls12381Fp (by decide), Nat.mul_div_assoc _ bls12381Fr_dvd_fp6_add_one]
  have hSE : S ^ E = 1 := by rw [hEfac, pow_mul, hS6, one_pow]
  have hFSE : (F * S) ^ E = 1 := by
    rw [hFS, ← pow_mul,
      show bls12381G1Cofactor * bls12381Fr * E = (bls12381Fr * E) * bls12381G1Cofactor by ring,
      hrE, pow_mul, hC12, one_pow]
  rw [mul_pow, hSE, mul_one] at hFSE
  exact hFSE

/-! ### 3.4 Full 18-Word BN254 & 22-Word BLS12-381 `PairingCheck` Soundness Theorems -/

/-- **Full BN254 18-Word Affine `PairingCheck` Soundness (`pairingCheckAffineBN254_sound`):**
When `pairingCheckAffineBN254 bn254PairingParams digits pair Q0 Q1 c = 1`:
1. Both `pair.a` and `pair.b` decode to canonical `4 × u80/u14` `Bn254AffineU80Point`s satisfying
   strict infinity and BN254 curve equations (`y² ≡ x³ + 3 (mod q)`, `x, y < q`);
2. The Miller loop output `f = millerLoop2 bn254PairingParams digits d0.point Q0 d1.point Q1`
   is canonical and nonzero, `c` is canonical and nonzero, and for ANY field `K` and ring hom
   `φ : ZModFp12 bn254Fp 9 →+* K` with `φ f ≠ 0` and `φ c ≠ 0`,
   `(φ f) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1`! -/
theorem pairingCheckAffineBN254_sound {digits : BitList} {pair : AffinePairBN254}
    {Q0 Q1 : G2Point} {c : Fp12}
    (h : pairingCheckAffineBN254 bn254PairingParams digits pair Q0 Q1 c = 1) :
    let d0 := decodeAffineG1BN254 bn254PairingParams pair.a
    let d1 := decodeAffineG1BN254 bn254PairingParams pair.b
    let f := millerLoop2 bn254PairingParams digits d0.point Q0 d1.point Q1
    d0.ok = 1 ∧ d1.ok = 1 ∧
    g1Validate bn254PairingParams d0.point = true ∧
    g1Validate bn254PairingParams d1.point = true ∧
    (∃ u0 : Bn254AffineU80Point, u0.x.toNat = d0.point.x ∧ u0.y.toNat = d0.point.y ∧
      (if u0.infinity then 1 else 0) = d0.point.isInf) ∧
    (∃ u1 : Bn254AffineU80Point, u1.x.toNat = d1.point.x ∧ u1.y.toNat = d1.point.y ∧
      (if u1.infinity then 1 else 0) = d1.point.isInf) ∧
    fp12Canonical bn254Fp f = true ∧ f ≠ fp12Zero ∧
    fp12Canonical bn254Fp c = true ∧ c ≠ fp12Zero ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bn254Fp 9 →+* K),
      φ (fp12ToZMod bn254Fp 9 f) ≠ 0 →
      φ (fp12ToZMod bn254Fp 9 c) ≠ 0 →
      (φ (fp12ToZMod bn254Fp 9 f)) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1 := by
  unfold pairingCheckAffineBN254 at h
  dsimp only at h ⊢
  split_ifs at h with hd0 hd1
  have hd0Eq : (decodeAffineG1BN254 bn254PairingParams pair.a).ok = 1 := beq_iff_eq.mp hd0
  have hd1Eq : (decodeAffineG1BN254 bn254PairingParams pair.b).ok = 1 := beq_iff_eq.mp hd1
  have hs0 := decodeAffineG1BN254_sound hd0Eq
  have hs1 := decodeAffineG1BN254_sound hd1Eq
  have hfCan : fp12Canonical bn254Fp
      (millerLoop2 bn254PairingParams digits
        (decodeAffineG1BN254 bn254PairingParams pair.a).point Q0
        (decodeAffineG1BN254 bn254PairingParams pair.b).point Q1) = true :=
    millerLoop2_canonical bn254PairingParams (by decide) digits _ Q0 _ Q1
  obtain ⟨hfNe, hcCan, hcNe, _, hFinal⟩ := verifyFinalExpWitness_bn254_sound hfCan h
  obtain ⟨u0, hu0x, hu0y, hu0i, _⟩ := hs0.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨u1, hu1x, hu1y, hu1i, _⟩ := hs1.2.2.2.2.2.2.2.2.2.2.2.2
  exact ⟨hd0Eq, hd1Eq, hs0.2.2.2.2.2.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.2.2.2.1,
    ⟨u0, hu0x, hu0y, hu0i⟩, ⟨u1, hu1x, hu1y, hu1i⟩, hfCan, hfNe, hcCan, hcNe, hFinal⟩

/-- **Full BN254 18-Word Fixed-Table (`d = 3`) `PairingCheck` Soundness
(`pairingCheckAffineTableBN254_sound`):**
Composes canonical `4 × u80/u14` affine decoding, `bn254AteLoopDigits` optimal Ate Miller loop,
and `verifyFinalExpTableBN254` (`wIdx < 3`, `w ^ 27 = 1`, `(φ f) ^ ((q¹² - 1) / r) = 1`). -/
theorem pairingCheckAffineTableBN254_sound {pair : AffinePairBN254}
    {Q0 Q1 : G2Point} {c : Fp12} {wIdx : Nat}
    (h : pairingCheckAffineTableBN254 pair Q0 Q1 c wIdx = 1) :
    let d0 := decodeAffineG1BN254 bn254PairingParams pair.a
    let d1 := decodeAffineG1BN254 bn254PairingParams pair.b
    let f := millerLoop2 bn254PairingParams bn254AteLoopDigits d0.point Q0 d1.point Q1
    d0.ok = 1 ∧ d1.ok = 1 ∧
    g1Validate bn254PairingParams d0.point = true ∧
    g1Validate bn254PairingParams d1.point = true ∧
    wIdx < 3 ∧
    fp12Canonical bn254Fp f = true ∧ f ≠ fp12Zero ∧
    fp12Canonical bn254Fp c = true ∧ c ≠ fp12Zero ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bn254Fp 9 →+* K),
      φ (fp12ToZMod bn254Fp 9 f) ≠ 0 →
      φ (fp12ToZMod bn254Fp 9 c) ≠ 0 →
      (φ (fp12ToZMod bn254Fp 9 f)) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1 := by
  unfold pairingCheckAffineTableBN254 at h
  dsimp only at h ⊢
  split_ifs at h with hd0 hd1
  have hd0Eq : (decodeAffineG1BN254 bn254PairingParams pair.a).ok = 1 := beq_iff_eq.mp hd0
  have hd1Eq : (decodeAffineG1BN254 bn254PairingParams pair.b).ok = 1 := beq_iff_eq.mp hd1
  have hs0 := decodeAffineG1BN254_sound hd0Eq
  have hs1 := decodeAffineG1BN254_sound hd1Eq
  have hfCan : fp12Canonical bn254Fp
      (millerLoop2 bn254PairingParams bn254AteLoopDigits
        (decodeAffineG1BN254 bn254PairingParams pair.a).point Q0
        (decodeAffineG1BN254 bn254PairingParams pair.b).point Q1) = true :=
    millerLoop2_canonical bn254PairingParams (by decide) bn254AteLoopDigits _ Q0 _ Q1
  obtain ⟨hwLt, hfNe, hcCan, hcNe, _, _, _, _, hFinal⟩ := verifyFinalExpTableBN254_sound h
  exact ⟨hd0Eq, hd1Eq, hs0.2.2.2.2.2.2.2.2.2.2.2.1, hs1.2.2.2.2.2.2.2.2.2.2.2.1,
    hwLt, hfCan, hfNe, hcCan, hcNe, hFinal⟩

/-- **Full BLS12-381 22-Word Affine `PairingCheck` Soundness (`pairingCheckAffineBLS12381_sound`):**
When `pairingCheckAffineBLS12381 bls12381PairingParams pair Q0 Q1 c = 1`:
1. Both `pair.a` and `pair.b` decode to canonical `5 × u80/u61` `Bls12381AffineU80Point`s;
2. BOTH decoded points satisfy Bowe's endomorphism criterion `[x²]P = -ψ(P)` AND lie strictly
   in the prime-order subgroup `bls12381FrModulus • P_aff = 0` (rejecting all cofactor torsion);
3. The Miller loop output `f = millerLoop2Binary bls12381PairingParams d0.point Q0 d1.point Q1`
   is canonical and nonzero, `c` is canonical and nonzero, and for ANY field `K` and ring hom
   `φ : ZModFp12 bls12381Fp 1 →+* K` with `φ f ≠ 0` and `φ c ≠ 0`,
   `(φ f) ^ ((bls12381Fp ^ 12 - 1) / bls12381Fr) = 1`! -/
theorem pairingCheckAffineBLS12381_sound {pair : AffinePairBLS12381}
    {Q0 Q1 : G2Point} {c : Fp12}
    (h : pairingCheckAffineBLS12381 bls12381PairingParams pair Q0 Q1 c = 1) :
    let d0 := decodeAffineG1BLS12381 bls12381PairingParams pair.a
    let d1 := decodeAffineG1BLS12381 bls12381PairingParams pair.b
    let f := millerLoop2Binary bls12381PairingParams d0.point Q0 d1.point Q1
    d0.ok = 1 ∧ d1.ok = 1 ∧
    (∃ u0 : Bls12381AffineU80Point, u0.x.toNat = d0.point.x ∧ u0.y.toNat = d0.point.y ∧
      (if u0.infinity then 1 else 0) = d0.point.isInf) ∧
    (∃ u1 : Bls12381AffineU80Point, u1.x.toNat = d1.point.x ∧ u1.y.toNat = d1.point.y ∧
      (if u1.infinity then 1 else 0) = d1.point.isInf) ∧
    (∃ P0_aff : (bls12381CurveAt bls12381FqModulus).Point,
      (d0.point = g1Inf → P0_aff = 0) ∧
      (d0.point.isInf = 0 →
        ∃ hns, P0_aff = .some (d0.point.x : ZMod bls12381FqModulus)
          (d0.point.y : ZMod bls12381FqModulus) hns) ∧
      bls12381FrModulus • P0_aff = 0) ∧
    (∃ P1_aff : (bls12381CurveAt bls12381FqModulus).Point,
      (d1.point = g1Inf → P1_aff = 0) ∧
      (d1.point.isInf = 0 →
        ∃ hns, P1_aff = .some (d1.point.x : ZMod bls12381FqModulus)
          (d1.point.y : ZMod bls12381FqModulus) hns) ∧
      bls12381FrModulus • P1_aff = 0) ∧
    fp12Canonical bls12381Fp f = true ∧ f ≠ fp12Zero ∧
    fp12Canonical bls12381Fp c = true ∧ c ≠ fp12Zero ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bls12381Fp 1 →+* K),
      φ (fp12ToZMod bls12381Fp 1 f) ≠ 0 →
      φ (fp12ToZMod bls12381Fp 1 c) ≠ 0 →
      (φ (fp12ToZMod bls12381Fp 1 f)) ^ ((bls12381Fp ^ 12 - 1) / bls12381Fr) = 1 := by
  unfold pairingCheckAffineBLS12381 at h
  dsimp only at h ⊢
  split_ifs at h with hd0 hd1
  have hd0Eq : (decodeAffineG1BLS12381 bls12381PairingParams pair.a).ok = 1 := beq_iff_eq.mp hd0
  have hd1Eq : (decodeAffineG1BLS12381 bls12381PairingParams pair.b).ok = 1 := beq_iff_eq.mp hd1
  have hs0 := decodeAffineG1BLS12381_sound hd0Eq
  have hs1 := decodeAffineG1BLS12381_sound hd1Eq
  have hval0 := hs0.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hval1 := hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨u0, hu0x, hu0y, hu0i, _⟩ := hs0.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨u1, hu1x, hu1y, hu1i, _⟩ := hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨_, P0_aff, h0inf, h0fin, _, h0ord⟩ := bls12381_g1Validate_prime_order hval0
  obtain ⟨_, P1_aff, h1inf, h1fin, _, h1ord⟩ := bls12381_g1Validate_prime_order hval1
  have hfCan : fp12Canonical bls12381Fp
      (millerLoop2Binary bls12381PairingParams
        (decodeAffineG1BLS12381 bls12381PairingParams pair.a).point Q0
        (decodeAffineG1BLS12381 bls12381PairingParams pair.b).point Q1) = true :=
    millerLoop2Binary_canonical bls12381PairingParams (by decide) _ Q0 _ Q1
  obtain ⟨hfNe, hcCan, hcNe, _, hFinal⟩ := verifyFinalExpWitness_bls12381_sound hfCan h
  exact ⟨hd0Eq, hd1Eq, ⟨u0, hu0x, hu0y, hu0i⟩, ⟨u1, hu1x, hu1y, hu1i⟩,
    ⟨P0_aff, h0inf, h0fin, h0ord⟩, ⟨P1_aff, h1inf, h1fin, h1ord⟩,
    hfCan, hfNe, hcCan, hcNe, hFinal⟩

end MillerLoopAndFinalExp

/-! ## Section 4: Canonical Wire Decoding, Universal Trailing-Byte Rejection & Key-Bound Transcript Soundness -/

section WireAndKeyBinding

/-! ### 4.1 `ByteList` Algebra, Little-Endian Codecs & `List UInt8` Bridge -/

/-- Convert a `KzgWire.ByteList` into `List UInt8` (matching `Ix.Cert.AiurCompression`). -/
def byteListToUInt8List : ByteList → List UInt8
  | .nil => []
  | .cons b rest => UInt8.ofNat b :: byteListToUInt8List rest

/-- Convert `List UInt8` into a canonical `KzgWire.ByteList`. -/
def uint8ListToByteList : List UInt8 → ByteList
  | [] => .nil
  | b :: rest => .cons b.toNat (uint8ListToByteList rest)

@[simp] theorem byteAppend_nil_left (bs : ByteList) : byteAppend .nil bs = bs := rfl

@[simp] theorem byteAppend_nil_right : ∀ bs : ByteList, byteAppend bs .nil = bs
  | .nil => rfl
  | .cons b rest => by simp [byteAppend, byteAppend_nil_right rest]

theorem byteAppend_assoc : ∀ a b c : ByteList,
    byteAppend (byteAppend a b) c = byteAppend a (byteAppend b c)
  | .nil, _, _ => rfl
  | .cons h t, b, c => by simp [byteAppend, byteAppend_assoc t b c]

@[simp] theorem byteLen_nil : byteLen .nil = 0 := rfl
@[simp] theorem byteLen_cons (b : Nat) (t : ByteList) : byteLen (.cons b t) = byteLen t + 1 := rfl

@[simp] theorem byteLen_append : ∀ a b : ByteList,
    byteLen (byteAppend a b) = byteLen a + byteLen b
  | .nil, b => by simp [byteAppend]
  | .cons _ t, b => by simp [byteAppend, byteLen_append t b]; omega

theorem byteAppend_inj_left : ∀ {a b₁ b₂ : ByteList},
    byteAppend a b₁ = byteAppend a b₂ → b₁ = b₂
  | .nil, _, _, h => h
  | .cons _ _, _, _, h => byteAppend_inj_left (ByteList.cons.inj h).2

theorem byteAppend_inj_of_len : ∀ {a₁ a₂ b₁ b₂ : ByteList},
    byteLen a₁ = byteLen a₂ →
    byteAppend a₁ b₁ = byteAppend a₂ b₂ →
    a₁ = a₂ ∧ b₁ = b₂
  | .nil, .nil, _, _, _, h => ⟨rfl, h⟩
  | .nil, .cons _ _, _, _, hlen, _ => by simp at hlen
  | .cons _ _, .nil, _, _, hlen, _ => by simp at hlen
  | .cons x xs, .cons y ys, b₁, b₂, hlen, h => by
    have hxy : x = y := (ByteList.cons.inj h).1
    have htl := byteAppend_inj_of_len (by simp at hlen; omega) (ByteList.cons.inj h).2
    exact ⟨by rw [hxy, htl.1], htl.2⟩

theorem byteListEq_eq_one_iff : ∀ a b : ByteList, byteListEq a b = 1 ↔ a = b
  | .nil, .nil => by simp [byteListEq]
  | .nil, .cons _ _ => by simp [byteListEq]
  | .cons _ _, .nil => by simp [byteListEq]
  | .cons x xs, .cons y ys => by
    unfold byteListEq
    by_cases hxy : x = y
    · subst hxy
      simp only [beq_self_eq_true, ↓reduceIte, byteListEq_eq_one_iff xs ys, ByteList.cons.injEq,
        true_and]
    · simp [beq_false_of_ne hxy, hxy]

theorem checkFinish_eq_one_iff (bs : ByteList) : checkFinish bs = 1 ↔ bs = .nil := by
  cases bs <;> simp [checkFinish]

theorem bytesCanonical_append : ∀ a b : ByteList,
    bytesCanonical (byteAppend a b) = 1 ↔ bytesCanonical a = 1 ∧ bytesCanonical b = 1
  | .nil, b => by simp [byteAppend, bytesCanonical]
  | .cons x xs, b => by
    simp only [byteAppend, bytesCanonical]
    split_ifs with hx
    · exact bytesCanonical_append xs b
    · simp

theorem bytesCanonical_cons_iff (b : Nat) (rest : ByteList) :
    bytesCanonical (.cons b rest) = 1 ↔ b < 256 ∧ bytesCanonical rest = 1 := by
  change (if b < 256 then bytesCanonical rest else 0) = 1 ↔ _
  split_ifs with hb
  · simp [hb]
  · simp [hb]

@[simp] theorem byteLen_natToLeBytes : ∀ n x : Nat, byteLen (natToLeBytes n x) = n
  | 0, _ => rfl
  | n + 1, x => by simp [natToLeBytes, byteLen_natToLeBytes n]

theorem bytesCanonical_natToLeBytes : ∀ n x : Nat, bytesCanonical (natToLeBytes n x) = 1
  | 0, _ => rfl
  | n + 1, x => by
    rw [natToLeBytes, bytesCanonical_cons_iff]
    exact ⟨Nat.mod_lt x (by decide), bytesCanonical_natToLeBytes n (x / 256)⟩

theorem leBytesToNat_natToLeBytes : ∀ n x : Nat,
    leBytesToNat (natToLeBytes n x) = x % 256 ^ n
  | 0, x => by simp [natToLeBytes, leBytesToNat, Nat.mod_one]
  | n + 1, x => by
    simp only [natToLeBytes, leBytesToNat, leBytesToNat_natToLeBytes n (x / 256), Nat.pow_succ']
    have h1 : x = 256 * (x / 256) + x % 256 := by omega
    have h2 : x / 256 = 256 ^ n * ((x / 256) / 256 ^ n) + (x / 256) % 256 ^ n :=
      (Nat.div_add_mod (x / 256) (256 ^ n)).symm
    have hlt : x % 256 + 256 * ((x / 256) % 256 ^ n) < 256 * 256 ^ n := by
      have ha : x % 256 < 256 := Nat.mod_lt x (by decide)
      have hb : (x / 256) % 256 ^ n < 256 ^ n := Nat.mod_lt _ (Nat.pow_pos (by decide))
      have hle : (x / 256) % 256 ^ n + 1 ≤ 256 ^ n := hb
      have hmul := Nat.mul_le_mul_left 256 hle
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have heq : x = (256 * 256 ^ n) * ((x / 256) / 256 ^ n) +
        (x % 256 + 256 * ((x / 256) % 256 ^ n)) := by
      calc x = 256 * (x / 256) + x % 256 := h1
        _ = 256 * (256 ^ n * ((x / 256) / 256 ^ n) + (x / 256) % 256 ^ n) + x % 256 := by
              rw [← h2]
        _ = (256 * 256 ^ n) * ((x / 256) / 256 ^ n) + (x % 256 + 256 * ((x / 256) % 256 ^ n)) := by
              ring
    conv_rhs => rw [heq]
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

theorem leBytesToNat_lt : ∀ {bs : ByteList},
    bytesCanonical bs = 1 → leBytesToNat bs < 256 ^ byteLen bs
  | .nil, _ => by simp [leBytesToNat]
  | .cons b rest, hcan => by
    rw [bytesCanonical_cons_iff] at hcan
    have htl := leBytesToNat_lt hcan.2
    simp only [leBytesToNat, byteLen_cons, Nat.pow_succ']
    have hle : leBytesToNat rest + 1 ≤ 256 ^ byteLen rest := htl
    have hmul := Nat.mul_le_mul_left 256 hle
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega

theorem natToLeBytes_leBytesToNat : ∀ {bs : ByteList},
    bytesCanonical bs = 1 → natToLeBytes (byteLen bs) (leBytesToNat bs) = bs
  | .nil, _ => rfl
  | .cons b rest, hcan => by
    rw [bytesCanonical_cons_iff] at hcan
    simp only [byteLen_cons, natToLeBytes, leBytesToNat]
    have hmod : (b + 256 * leBytesToNat rest) % 256 = b := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcan.1]
    have hdiv : (b + 256 * leBytesToNat rest) / 256 = leBytesToNat rest := by
      rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hcan.1, Nat.zero_add]
    rw [hmod, hdiv, natToLeBytes_leBytesToNat hcan.2]

theorem natToLeBytes_inj {n a b : Nat} (ha : a < 256 ^ n) (hb : b < 256 ^ n)
    (h : natToLeBytes n a = natToLeBytes n b) : a = b := by
  have heq := congrArg leBytesToNat h
  rw [leBytesToNat_natToLeBytes, leBytesToNat_natToLeBytes,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at heq
  exact heq

@[simp] theorem byteListToUInt8List_append : ∀ a b : ByteList,
    byteListToUInt8List (byteAppend a b) = byteListToUInt8List a ++ byteListToUInt8List b
  | .nil, _ => rfl
  | .cons h t, b => by simp [byteAppend, byteListToUInt8List, byteListToUInt8List_append t b]

@[simp] theorem byteListToUInt8List_length : ∀ bs : ByteList,
    (byteListToUInt8List bs).length = byteLen bs
  | .nil => rfl
  | .cons _ t => by simp [byteListToUInt8List, byteListToUInt8List_length t]

theorem byteListToUInt8List_uint8ListToByteList : ∀ bs : List UInt8,
    byteListToUInt8List (uint8ListToByteList bs) = bs
  | [] => rfl
  | b :: rest => by simp [uint8ListToByteList, byteListToUInt8List,
      byteListToUInt8List_uint8ListToByteList rest]

theorem uint8ListToByteList_canonical : ∀ bs : List UInt8,
    bytesCanonical (uint8ListToByteList bs) = 1
  | [] => rfl
  | b :: rest => by
    rw [uint8ListToByteList, bytesCanonical_cons_iff]
    exact ⟨b.toNat_lt, uint8ListToByteList_canonical rest⟩

theorem byteListToUInt8List_inj : ∀ {a b : ByteList},
    bytesCanonical a = 1 → bytesCanonical b = 1 →
    byteListToUInt8List a = byteListToUInt8List b → a = b
  | .nil, .nil, _, _, _ => rfl
  | .nil, .cons _ _, _, _, h => by simp [byteListToUInt8List] at h
  | .cons _ _, .nil, _, _, h => by simp [byteListToUInt8List] at h
  | .cons x xs, .cons y ys, ha, hb, h => by
    rw [bytesCanonical_cons_iff] at ha hb
    simp only [byteListToUInt8List, List.cons.injEq] at h
    have hxEq : x = y := by
      have h1 := congrArg UInt8.toNat h.1
      simp only [UInt8.toNat_ofNat', Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] at h1
      exact h1
    rw [hxEq, byteListToUInt8List_inj ha.2 hb.2 h.2]

theorem byteListToUInt8List_encodeU32 (v : Nat) :
    byteListToUInt8List (encodeU32 v) = encodeU32LE v := by
  change [UInt8.ofNat (v % 256),
          UInt8.ofNat ((v / 256) % 256),
          UInt8.ofNat (((v / 256) / 256) % 256),
          UInt8.ofNat ((((v / 256) / 256) / 256) % 256)] =
         [UInt8.ofNat (v % 256),
          UInt8.ofNat ((v / 256) % 256),
          UInt8.ofNat ((v / 65536) % 256),
          UInt8.ofNat ((v / 16777216) % 256)]
  simp only [Nat.div_div_eq_div_mul]

theorem digestWordsEq_eq_one_iff (a b : DigestWords) :
    digestWordsEq a b = 1 ↔ a = b := by
  cases a; cases b
  unfold digestWordsEq
  simp only [DigestWords.mk.injEq]
  split_ifs with h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · constructor
    · intro h0; exact absurd h0 (by decide)
    · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simp at h

theorem digestWordsCanonical_eq_one_iff (d : DigestWords) :
    digestWordsCanonical d = 1 ↔
      d.d0 < 2 ^ 32 ∧ d.d1 < 2 ^ 32 ∧ d.d2 < 2 ^ 32 ∧ d.d3 < 2 ^ 32 ∧
      d.d4 < 2 ^ 32 ∧ d.d5 < 2 ^ 32 ∧ d.d6 < 2 ^ 32 ∧ d.d7 < 2 ^ 32 := by
  unfold digestWordsCanonical
  dsimp only
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · constructor
    · intro h0; exact absurd h0 (by decide)
    · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
      exfalso; apply h
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

@[simp] theorem digestWordsToBytes_len (d : DigestWords) :
    byteLen (digestWordsToBytes d) = 32 := by
  simp [digestWordsToBytes]

theorem digestWordsToBytes_canonical (d : DigestWords) :
    bytesCanonical (digestWordsToBytes d) = 1 := by
  simp [digestWordsToBytes, bytesCanonical_append, bytesCanonical_natToLeBytes]

theorem digestWordsToBytes_inj {a b : DigestWords}
    (ha : digestWordsCanonical a = 1) (hb : digestWordsCanonical b = 1)
    (heq : digestWordsToBytes a = digestWordsToBytes b) : a = b := by
  rw [digestWordsCanonical_eq_one_iff] at ha hb
  unfold digestWordsToBytes at heq
  obtain ⟨e0, r1⟩ := byteAppend_inj_of_len (by simp) heq
  obtain ⟨e1, r2⟩ := byteAppend_inj_of_len (by simp) r1
  obtain ⟨e2, r3⟩ := byteAppend_inj_of_len (by simp) r2
  obtain ⟨e3, r4⟩ := byteAppend_inj_of_len (by simp) r3
  obtain ⟨e4, r5⟩ := byteAppend_inj_of_len (by simp) r4
  obtain ⟨e5, r6⟩ := byteAppend_inj_of_len (by simp) r5
  obtain ⟨e6, e7⟩ := byteAppend_inj_of_len (by simp) r6
  have h256 : 256 ^ 4 = 2 ^ 32 := by decide
  cases a; cases b
  simp only [DigestWords.mk.injEq]
  exact ⟨natToLeBytes_inj (h256 ▸ ha.1) (h256 ▸ hb.1) e0,
    natToLeBytes_inj (h256 ▸ ha.2.1) (h256 ▸ hb.2.1) e1,
    natToLeBytes_inj (h256 ▸ ha.2.2.1) (h256 ▸ hb.2.2.1) e2,
    natToLeBytes_inj (h256 ▸ ha.2.2.2.1) (h256 ▸ hb.2.2.2.1) e3,
    natToLeBytes_inj (h256 ▸ ha.2.2.2.2.1) (h256 ▸ hb.2.2.2.2.1) e4,
    natToLeBytes_inj (h256 ▸ ha.2.2.2.2.2.1) (h256 ▸ hb.2.2.2.2.2.1) e5,
    natToLeBytes_inj (h256 ▸ ha.2.2.2.2.2.2.1) (h256 ▸ hb.2.2.2.2.2.2.1) e6,
    natToLeBytes_inj (h256 ▸ ha.2.2.2.2.2.2.2) (h256 ▸ hb.2.2.2.2.2.2.2) e7⟩

@[simp] theorem digest32ToBytes_len (d : Digest32) :
    byteLen (digest32ToBytes d) = 32 :=
  digestWordsToBytes_len _

theorem digest32ToWords_canonical (d : Digest32) :
    digestWordsCanonical (digest32ToWords d) = 1 := by
  rw [digestWordsCanonical_eq_one_iff]
  exact ⟨d.w0.toNat_lt, d.w1.toNat_lt, d.w2.toNat_lt, d.w3.toNat_lt,
    d.w4.toNat_lt, d.w5.toNat_lt, d.w6.toNat_lt, d.w7.toNat_lt⟩

theorem digest32ToBytes_inj {a b : Digest32}
    (heq : digest32ToBytes a = digest32ToBytes b) : a = b := by
  have hw := digestWordsToBytes_inj (digest32ToWords_canonical a) (digest32ToWords_canonical b) heq
  cases a; cases b
  simp only [digest32ToWords, DigestWords.mk.injEq] at hw
  simp only [Digest32.mk.injEq]
  exact ⟨UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.1),
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.2.1),
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.2.2.1),
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.2.2.2.1),
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.2.2.2.2.1),
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.2.2.2.2.2.1),
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.2.2.2.2.2.2.1),
    UInt32.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hw.2.2.2.2.2.2.2)⟩

/-- Exact characterization of `byteListEndsWith`: returns `1` iff `bs = byteAppend pre suffix`
for some prefix `pre`. -/
theorem byteListEndsWith_eq_one_iff (bs suffix : ByteList) :
    byteListEndsWith bs suffix = 1 ↔ ∃ pre : ByteList, bs = byteAppend pre suffix := by
  induction bs with
  | nil =>
    cases suffix with
    | nil =>
      refine ⟨fun _ => ⟨.nil, rfl⟩, fun _ => rfl⟩
    | cons _ _ =>
      unfold byteListEndsWith
      simp only [byteLen_nil, byteLen_cons, Nat.zero_lt_succ, ↓reduceIte, zero_ne_one, false_iff]
      rintro ⟨pre, h⟩
      cases pre <;> simp [byteAppend] at h
  | cons b rest ih =>
    by_cases hle : byteLen suffix ≤ byteLen rest
    · have hstep : byteListEndsWith (.cons b rest) suffix = byteListEndsWith rest suffix := by
        unfold byteListEndsWith
        have h1 : ¬ (byteLen (.cons b rest) < byteLen suffix) := by simp; omega
        have h2 : ¬ (byteLen rest < byteLen suffix) := by omega
        have hsub : byteLen (.cons b rest) - byteLen suffix = (byteLen rest - byteLen suffix) + 1 := by
          simp only [byteLen_cons]; omega
        simp only [h1, h2, ↓reduceIte, hsub]
        rfl
      rw [hstep, ih]
      constructor
      · rintro ⟨pre, rfl⟩
        exact ⟨.cons b pre, rfl⟩
      · rintro ⟨pre, h⟩
        cases pre with
        | nil =>
          simp only [byteAppend] at h
          have hlen := congrArg byteLen h
          simp at hlen; omega
        | cons b' pre' =>
          simp only [byteAppend, ByteList.cons.injEq] at h
          exact ⟨pre', h.2⟩
    · by_cases heq : byteLen (.cons b rest) = byteLen suffix
      · have hstep : byteListEndsWith (.cons b rest) suffix = byteListEq (.cons b rest) suffix := by
          unfold byteListEndsWith
          have h1 : ¬ (byteLen (.cons b rest) < byteLen suffix) := by omega
          have hsub : byteLen (.cons b rest) - byteLen suffix = 0 := by omega
          simp only [h1, ↓reduceIte, hsub]
          rfl
        rw [hstep, byteListEq_eq_one_iff]
        constructor
        · intro h; exact ⟨.nil, h⟩
        · rintro ⟨pre, h⟩
          have hlen := congrArg byteLen h
          simp only [byteLen_append] at hlen
          have hpre0 : byteLen pre = 0 := by omega
          cases pre with
          | nil => exact h
          | cons _ _ => simp at hpre0
      · have hlt : byteLen (.cons b rest) < byteLen suffix := by simp at heq ⊢; omega
        unfold byteListEndsWith
        simp only [hlt, ↓reduceIte, zero_ne_one, false_iff]
        rintro ⟨pre, h⟩
        have hlen := congrArg byteLen h
        simp only [byteLen_append] at hlen
        omega

/-! ### 4.2 Canonical `g1OnCurve`, `g1ValidPoint`, `g1ToBytes` Injectivity & `g1FromBytes` Soundness -/

/-- Exact curve semantics of `KzgWire.g1OnCurve c P = true`:
strict infinity (`P = g1Inf`) OR finite canonical coordinates (`x < q`, `y < q`) satisfying
`y² = x³ + b` in `ZMod c.fqMod`. -/
theorem g1OnCurve_sound {c : CurveParams} {P : G1Point} (h : g1OnCurve c P = true) :
    P = g1Inf ∨
    (P.isInf = 0 ∧ P.x < c.fqMod ∧ P.y < c.fqMod ∧
      ((P.y : ZMod c.fqMod) ^ 2 = (P.x : ZMod c.fqMod) ^ 3 + (c.curveB : ZMod c.fqMod))) := by
  unfold g1OnCurve at h
  dsimp only at h
  split_ifs at h with hinf hx0 hinf0 hxLt hyLt
  · left
    cases P
    simp only [g1Inf, G1Point.mk.injEq]
    exact ⟨beq_iff_eq.mp hx0, beq_iff_eq.mp h, beq_iff_eq.mp hinf⟩
  · right
    have hEq := beq_iff_eq.mp h
    have hZ := congrArg (fun n : Nat => (n : ZMod c.fqMod)) hEq
    rw [fqMulMod_cast, fqAddMod_cast, fqMulMod_cast, fqMulMod_cast, ZMod.natCast_mod] at hZ
    refine ⟨beq_iff_eq.mp hinf0, hxLt, hyLt, ?_⟩
    linear_combination hZ

theorem g1ValidPoint_sound {c : CurveParams} {P : G1Point} (h : g1ValidPoint c P = true) :
    g1OnCurve c P = true ∧ g1SubgroupCheck c P = true ∧
    (P = g1Inf ∨
      (P.isInf = 0 ∧ P.x < c.fqMod ∧ P.y < c.fqMod ∧
        ((P.y : ZMod c.fqMod) ^ 2 = (P.x : ZMod c.fqMod) ^ 3 + (c.curveB : ZMod c.fqMod)))) := by
  unfold g1ValidPoint at h
  rw [Bool.and_eq_true] at h
  exact ⟨h.1, h.2, g1OnCurve_sound h.1⟩

private theorem addLastByteFlag_natToLeBytes_inj :
    ∀ (n : Nat) {x₁ x₂ f₁ f₂ : Nat},
      0 < n →
      x₁ < 64 * 256 ^ (n - 1) → x₂ < 64 * 256 ^ (n - 1) →
      f₁ < 4 → f₂ < 4 →
      addLastByteFlag (64 * f₁) (natToLeBytes n x₁) =
        addLastByteFlag (64 * f₂) (natToLeBytes n x₂) →
      x₁ = x₂ ∧ f₁ = f₂
  | 0, _, _, _, _, hpos, _, _, _, _, _ => by omega
  | 1, x₁, x₂, f₁, f₂, _, hx₁, hx₂, _, _, h => by
    simp only [Nat.sub_self, pow_zero, Nat.mul_one] at hx₁ hx₂
    simp only [natToLeBytes, addLastByteFlag, ByteList.cons.injEq, and_true,
      Nat.mod_eq_of_lt (show x₁ < 256 by omega), Nat.mod_eq_of_lt (show x₂ < 256 by omega)] at h
    exact ⟨by omega, by omega⟩
  | n + 2, x₁, x₂, f₁, f₂, _, hx₁, hx₂, hf₁, hf₂, h => by
    have hstep : ∀ x f,
        addLastByteFlag (64 * f) (natToLeBytes (n + 2) x) =
          .cons (x % 256) (addLastByteFlag (64 * f) (natToLeBytes (n + 1) (x / 256))) := by
      intro x f
      simp only [natToLeBytes, addLastByteFlag]
    rw [hstep, hstep, ByteList.cons.injEq] at h
    have hpow : 64 * 256 ^ (n + 1) = 256 * (64 * 256 ^ n) := by rw [Nat.pow_succ']; ring
    have hsub : n + 2 - 1 = n + 1 := by omega
    rw [hsub] at hx₁ hx₂
    have hd₁ : x₁ / 256 < 64 * 256 ^ n := by rw [hpow] at hx₁; omega
    have hd₂ : x₂ / 256 < 64 * 256 ^ n := by rw [hpow] at hx₂; omega
    obtain ⟨hdiv, hf⟩ := addLastByteFlag_natToLeBytes_inj (n + 1) (by omega) hd₁ hd₂ hf₁ hf₂ h.2
    exact ⟨by omega, hf⟩

/-- **Strict Injectivity of `g1ToBytes` on Canonical On-Curve `G1` Points (`g1ToBytes_inj`):**
For any curve with prime `q > 2` fitting in `8 * g1ByteLen - 2` bits (covering both BN254
`bn254Fp ≤ 64 * 256^31 = 2^254` and BLS12-381 `bls12381Fp ≤ 64 * 256^47 = 2^382`),
two canonical on-curve points with identical compressed `SWFlags` bytes are equal. -/
theorem g1ToBytes_inj {c : CurveParams} [Fact (Nat.Prime c.fqMod)]
    (hq2 : 2 < c.fqMod) (hlen : 0 < c.g1ByteLen)
    (hqBound : c.fqMod ≤ 64 * 256 ^ (c.g1ByteLen - 1))
    {P Q : G1Point} (hP : g1OnCurve c P = true) (hQ : g1OnCurve c Q = true)
    (heq : g1ToBytes c P = g1ToBytes c Q) : P = Q := by
  have hqOdd : c.fqMod % 2 = 1 := by
    rcases (Fact.out : Nat.Prime c.fqMod).eq_two_or_odd with h2 | hodd
    · omega
    · exact hodd
  have hP' := g1OnCurve_sound hP
  have hQ' := g1OnCurve_sound hQ
  have hPx : P.x < 64 * 256 ^ (c.g1ByteLen - 1) := by
    rcases hP' with rfl | ⟨_, hx, _, _⟩
    · simp only [g1Inf]; exact Nat.lt_of_lt_of_le (by omega) hqBound
    · exact Nat.lt_of_lt_of_le hx hqBound
  have hQx : Q.x < 64 * 256 ^ (c.g1ByteLen - 1) := by
    rcases hQ' with rfl | ⟨_, hx, _, _⟩
    · simp only [g1Inf]; exact Nat.lt_of_lt_of_le (by omega) hqBound
    · exact Nat.lt_of_lt_of_le hx hqBound
  have hPinfLe : P.isInf ≤ 1 := by
    rcases hP' with rfl | ⟨h0, _, _, _⟩
    · decide
    · omega
  have hQinfLe : Q.isInf ≤ 1 := by
    rcases hQ' with rfl | ⟨h0, _, _, _⟩
    · decide
    · omega
  have hysLe : ∀ y, g1YSign c y ≤ 1 := by intro y; unfold g1YSign; split_ifs <;> omega
  unfold g1ToBytes at heq
  have hflagEq : ∀ P : G1Point, 64 * P.isInf + 128 * g1YSign c P.y = 64 * (P.isInf + 2 * g1YSign c P.y) := by
    intro R; ring
  rw [hflagEq P, hflagEq Q] at heq
  obtain ⟨hxEq, hfEq⟩ := addLastByteFlag_natToLeBytes_inj c.g1ByteLen hlen hPx hQx
    (by have := hysLe P.y; omega) (by have := hysLe Q.y; omega) heq
  have hinfEq : P.isInf = Q.isInf := by omega
  have hysEq : g1YSign c P.y = g1YSign c Q.y := by omega
  rcases hP' with rfl | ⟨hPi0, hPxLt, hPyLt, hPeq⟩
  · rcases hQ' with rfl | ⟨hQi0, _, _, _⟩
    · rfl
    · simp [g1Inf] at hinfEq; omega
  · rcases hQ' with rfl | ⟨hQi0, hQxLt, hQyLt, hQeq⟩
    · simp [g1Inf] at hinfEq; omega
    · have hySq : (P.y : ZMod c.fqMod) ^ 2 = (Q.y : ZMod c.fqMod) ^ 2 := by
        rw [hPeq, hQeq, hxEq]
      have hfac : ((P.y : ZMod c.fqMod) - (Q.y : ZMod c.fqMod)) *
          ((P.y : ZMod c.fqMod) + (Q.y : ZMod c.fqMod)) = 0 := by linear_combination hySq
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · have hyZ : (P.y : ZMod c.fqMod) = (Q.y : ZMod c.fqMod) := sub_eq_zero.mp hsub
        have hyEq : P.y = Q.y := by
          have hv := congrArg ZMod.val hyZ
          rwa [ZMod.val_natCast_of_lt hPyLt, ZMod.val_natCast_of_lt hQyLt] at hv
        cases P; cases Q; simp only [G1Point.mk.injEq] at *; exact ⟨hxEq, hyEq, hinfEq⟩
      · have hsumCast : ((P.y + Q.y : Nat) : ZMod c.fqMod) = 0 := by push_cast; exact hadd
        have hdvd : c.fqMod ∣ P.y + Q.y := (ZMod.natCast_eq_zero_iff _ _).mp hsumCast
        rcases hdvd with ⟨k, hk⟩
        have hkCases : k = 0 ∨ k = 1 := by
          have : c.fqMod * k < c.fqMod * 2 := by omega
          have hkLt : k < 2 := Nat.lt_of_mul_lt_mul_left this
          omega
        rcases hkCases with rfl | rfl
        · have hyEq : P.y = Q.y := by omega
          cases P; cases Q; simp only [G1Point.mk.injEq] at *; exact ⟨hxEq, hyEq, hinfEq⟩
        · exfalso
          have hsumQ : P.y + Q.y = c.fqMod := by omega
          unfold g1YSign at hysEq
          split_ifs at hysEq with h1 h2 <;> omega

/-- **Canonical Compressed `G1` Wire Decoding Soundness (`g1FromBytes_sound`):**
When `(g1FromBytes c bs).ok = 1`:
1. `byteLen bs = c.g1ByteLen` and `bytesCanonical bs = 1`;
2. The decoded point satisfies `g1ValidPoint c pt = true` (canonical `< fqMod`, strict infinity,
   on-curve equation $y^2 \equiv x^3 + b \pmod q$, and prime-order subgroup check);
3. For every finite decoded point (`pt.isInf = 0`), exact canonical round-trip `g1ToBytes c pt = bs`! -/
theorem g1FromBytes_sound {c : CurveParams} {bs : ByteList}
    (h : (g1FromBytes c bs).ok = 1) :
    let pt := (g1FromBytes c bs).point
    byteLen bs = c.g1ByteLen ∧
    bytesCanonical bs = 1 ∧
    g1ValidPoint c pt = true ∧
    (pt.isInf = 0 → g1ToBytes c pt = bs) := by
  unfold g1FromBytes at h ⊢
  dsimp only at h ⊢
  by_cases hlen : (byteLen bs == c.g1ByteLen) = true
  swap; · simp [hlen] at h
  simp only [hlen, ↓reduceIte] at h ⊢
  by_cases hcan : (bytesCanonical bs == 1) = true
  swap; · simp [hcan] at h
  simp only [hcan, ↓reduceIte] at h ⊢
  have hlenEq : byteLen bs = c.g1ByteLen := beq_iff_eq.mp hlen
  have hcanEq : bytesCanonical bs = 1 := beq_iff_eq.mp hcan
  split_ifs at h with hinf hx hys hxLt hySign hval hrt
  · simp only [hinf, hx, hys, ↓reduceIte]
    exact ⟨hlenEq, hcanEq, by simp [g1ValidPoint, g1OnCurve, g1SubgroupCheck, g1Inf],
      fun h0 => absurd h0 (by decide)⟩
  · have hrtEq : g1ToBytes c _ = bs := (byteListEq_eq_one_iff _ _).mp (beq_iff_eq.mp hrt)
    simp only [hinf, hxLt, hySign, hval, hrt, ↓reduceIte]
    exact ⟨hlenEq, hcanEq, hval, fun _ => hrtEq⟩
  · rename_i hval' hrt'
    have hrtEq : g1ToBytes c _ = bs := (byteListEq_eq_one_iff _ _).mp (beq_iff_eq.mp hrt')
    simp only [hinf, hxLt, hySign, Bool.false_eq_true, ↓reduceIte, hval', hrt']
    exact ⟨hlenEq, hcanEq, trivial, fun _ => hrtEq⟩

/-- **Canonical Compressed `G1` Injectivity on Finite Points (`g1FromBytes_injective_finite`):**
No two distinct byte strings can decode to the same finite `G1Point` under `g1FromBytes`. -/
theorem g1FromBytes_injective_finite {c : CurveParams} {bs₁ bs₂ : ByteList}
    (h₁ : (g1FromBytes c bs₁).ok = 1) (h₂ : (g1FromBytes c bs₂).ok = 1)
    (hfin : (g1FromBytes c bs₁).point.isInf = 0)
    (hpt : (g1FromBytes c bs₁).point = (g1FromBytes c bs₂).point) :
    bs₁ = bs₂ := by
  have hs₁ := g1FromBytes_sound h₁
  have hs₂ := g1FromBytes_sound h₂
  rw [← hs₁.2.2.2 hfin, ← hs₂.2.2.2 (hpt ▸ hfin), hpt]

/-- Concrete BLS12-381 torsion witness `bls12381TorsionWitness` (`x = 4`) is on the curve
`y² = x³ + 4` but rejected by `KzgWire.g1SubgroupCheck`, `g1ValidPoint`, and `g1FromBytes`. -/
theorem kzgWire_bls12381_torsion_rejected :
    g1OnCurve bls12381CurveParams bls12381TorsionWitness = true ∧
    g1SubgroupCheck bls12381CurveParams bls12381TorsionWitness = false ∧
    g1ValidPoint bls12381CurveParams bls12381TorsionWitness = false ∧
    (g1FromBytes bls12381CurveParams (g1ToBytes bls12381CurveParams bls12381TorsionWitness)).ok = 0 := by
  have hrej := bls12381_torsion_witness_rejected
  refine ⟨hrej.1, hrej.2.2.2.1, hrej.2.2.2.2.1, ?_⟩
  cases hok : (g1FromBytes bls12381CurveParams
      (g1ToBytes bls12381CurveParams bls12381TorsionWitness)).ok with
  | zero => rfl
  | succ k =>
    exfalso
    have hok1 : (g1FromBytes bls12381CurveParams
        (g1ToBytes bls12381CurveParams bls12381TorsionWitness)).ok = 1 := by
      have h01 : ∀ c bs, (g1FromBytes c bs).ok = 0 ∨ (g1FromBytes c bs).ok = 1 := by
        intro c bs; unfold g1FromBytes; dsimp only; split_ifs <;> simp
      rcases h01 bls12381CurveParams (g1ToBytes bls12381CurveParams bls12381TorsionWitness) with h0 | h1
      · omega
      · exact h1
    have hs := g1FromBytes_sound hok1
    set pt := (g1FromBytes bls12381CurveParams
      (g1ToBytes bls12381CurveParams bls12381TorsionWitness)).point
    have hptInf0 : pt.isInf = 0 := by
      rcases g1OnCurve_sound (g1ValidPoint_sound hs.2.2.1).1 with hinf | hfin
      · exfalso
        have hok' := hok1
        have hpt' : (g1FromBytes bls12381CurveParams
            (g1ToBytes bls12381CurveParams bls12381TorsionWitness)).point = g1Inf := hinf
        unfold g1FromBytes at hok' hpt'
        dsimp only at hok' hpt'
        by_cases hlen : (byteLen (g1ToBytes bls12381CurveParams bls12381TorsionWitness) ==
            bls12381CurveParams.g1ByteLen) = true
        swap; · simp [hlen] at hok'
        simp only [hlen, ↓reduceIte] at hok' hpt'
        by_cases hcan : (bytesCanonical (g1ToBytes bls12381CurveParams bls12381TorsionWitness) == 1) = true
        swap; · simp [hcan] at hok'
        simp only [hcan, ↓reduceIte] at hok' hpt'
        split_ifs at hok' hpt' with hinfFlag
        · exact absurd hinfFlag (by decide)
        · simp [g1Inf] at hpt'
        · simp [g1Inf] at hpt'
      · exact hfin.1
    have hrt := hs.2.2.2 hptInf0
    have hptEq : pt = bls12381TorsionWitness := by
      have : Fact (Nat.Prime bls12381CurveParams.fqMod) :=
        inferInstanceAs (Fact (Nat.Prime bls12381FqModulus))
      exact g1ToBytes_inj (by decide) (by decide) (by decide)
        (g1ValidPoint_sound hs.2.2.1).1 hrej.1 hrt
    have hval := hs.2.2.1
    rw [hptEq, hrej.2.2.2.2.1] at hval
    exact Bool.false_ne_true hval

/-! ### 4.3 Streaming Prefix-Preservation & Universal Trailing-Byte Rejection (All 5 Formats) -/

private theorem readU8_append {bs extra : ByteList} {r : ParseNat}
    (hr : readU8 bs = r) (h : r.ok = 1) :
    readU8 (byteAppend bs extra) =
      { ok := 1, val := r.val, rest := byteAppend r.rest extra } := by
  subst hr
  cases bs with
  | nil => simp [readU8] at h
  | cons b rest =>
    unfold readU8 at h ⊢
    dsimp only at h ⊢
    split_ifs at h with hb
    simp [byteAppend, hb]

private theorem readU32_append {bs extra : ByteList} {r : ParseNat}
    (hr : readU32 bs = r) (h : r.ok = 1) :
    readU32 (byteAppend bs extra) =
      { ok := 1, val := r.val, rest := byteAppend r.rest extra } := by
  subst hr
  match bs with
  | .cons b0 (.cons b1 (.cons b2 (.cons b3 rest))) =>
    unfold readU32 at h ⊢
    dsimp only at h ⊢
    split_ifs at h with hb
    simp [byteAppend, hb]
  | .nil | .cons _ .nil | .cons _ (.cons _ .nil) | .cons _ (.cons _ (.cons _ .nil)) =>
    simp [readU32] at h

private theorem readBytes_append : ∀ (n : Nat) {bs extra : ByteList} {r : ParseBytes},
    readBytes bs n = r → r.ok = 1 →
    readBytes (byteAppend bs extra) n =
      { ok := 1, bytes := r.bytes, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, .nil, _, _, hr, h => by subst hr; simp [readBytes] at h
  | n + 1, .cons b rest, extra, r, hr, h => by
    subst hr
    unfold readBytes at h ⊢
    dsimp only at h ⊢
    set sub := readBytes rest n with hsub_def
    split_ifs at h with hb hsub
    have ih := readBytes_append n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [byteAppend, hb, ↓reduceIte, ih, beq_self_eq_true, hsub]

private theorem readBytes_sound : ∀ (n : Nat) {bs : ByteList},
    (readBytes bs n).ok = 1 →
    byteLen (readBytes bs n).bytes = n ∧
    bytesCanonical (readBytes bs n).bytes = 1 ∧
    bs = byteAppend (readBytes bs n).bytes (readBytes bs n).rest
  | 0, bs, _ => by simp [readBytes, bytesCanonical]
  | n + 1, .nil, h => by simp [readBytes] at h
  | n + 1, .cons b rest, h => by
    unfold readBytes at h ⊢
    dsimp only at h ⊢
    split_ifs at h with hb hsub
    have hsubEq : (readBytes rest n).ok = 1 := beq_iff_eq.mp hsub
    obtain ⟨hlen, hcan, happ⟩ := readBytes_sound n hsubEq
    simp only [hb, hsub, ↓reduceIte, byteLen_cons, hlen, bytesCanonical_cons_iff, hcan,
      byteAppend, true_and]
    exact congrArg (ByteList.cons b) happ

private theorem readBlob_append {bs extra : ByteList} {r : ParseBytes}
    (hr : readBlob bs = r) (h : r.ok = 1) :
    readBlob (byteAppend bs extra) =
      { ok := 1, bytes := r.bytes, rest := byteAppend r.rest extra } := by
  subst hr
  unfold readBlob at h ⊢
  set n := readU32 bs with hn_def
  dsimp only at h ⊢
  split_ifs at h with hn
  have hu := readU32_append (extra := extra) hn_def.symm (beq_iff_eq.mp hn)
  have hb := readBytes_append n.val (extra := extra) rfl h
  simp only [hu, hn, beq_self_eq_true, ↓reduceIte, hb]

private theorem checkMagic_append {bs expected extra : ByteList} {r : ParseBytes}
    (hr : checkMagic bs expected = r) (h : r.ok = 1) :
    checkMagic (byteAppend bs extra) expected =
      { ok := 1, bytes := r.bytes, rest := byteAppend r.rest extra } := by
  subst hr
  unfold checkMagic at h ⊢
  set rb := readBytes bs 8 with hrb_def
  dsimp only at h ⊢
  split_ifs at h with hrb heq
  have hb := readBytes_append 8 (extra := extra) hrb_def.symm (beq_iff_eq.mp hrb)
  simp only [hb, hrb, beq_self_eq_true, ↓reduceIte, heq]

private theorem readScalar_append {c : CurveParams} {bs extra : ByteList} {r : ParseNat}
    (hr : readScalar c bs = r) (h : r.ok = 1) :
    readScalar c (byteAppend bs extra) =
      { ok := 1, val := r.val, rest := byteAppend r.rest extra } := by
  subst hr
  unfold readScalar at h ⊢
  set rb := readBytes bs 32 with hrb_def
  dsimp only at h ⊢
  split_ifs at h with hrb hlt
  have hb := readBytes_append 32 (extra := extra) hrb_def.symm (beq_iff_eq.mp hrb)
  simp only [hb, hrb, beq_self_eq_true, ↓reduceIte, hlt]

private theorem readScalars_append (c : CurveParams) : ∀ (n : Nat) {bs extra : ByteList} {r : ParseFList},
    readScalars c bs n = r → r.ok = 1 →
    readScalars c (byteAppend bs extra) n =
      { ok := 1, vals := r.vals, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readScalars at h ⊢
    dsimp only at h ⊢
    set hd := readScalar c bs with hhd_def
    set sub := readScalars c hd.rest n with hsub_def
    split_ifs at h with hhd hsub
    have h1 := readScalar_append (extra := extra) hhd_def.symm (beq_iff_eq.mp hhd)
    have h2 := readScalars_append c n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [h1, hhd, beq_self_eq_true, ↓reduceIte, h2, hsub]

private theorem readTags_append : ∀ (n : Nat) {bs extra : ByteList} {r : ParseFList},
    readTags bs n = r → r.ok = 1 →
    readTags (byteAppend bs extra) n =
      { ok := 1, vals := r.vals, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readTags at h ⊢
    dsimp only at h ⊢
    set hd := readU8 bs with hhd_def
    set sub := readTags hd.rest n with hsub_def
    split_ifs at h with hhd hsub
    have h1 := readU8_append (extra := extra) hhd_def.symm (beq_iff_eq.mp hhd)
    have h2 := readTags_append n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [h1, hhd, beq_self_eq_true, ↓reduceIte, h2, hsub]

private theorem readU32List_append : ∀ (n : Nat) {bs extra : ByteList} {r : ParseFList},
    readU32List bs n = r → r.ok = 1 →
    readU32List (byteAppend bs extra) n =
      { ok := 1, vals := r.vals, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readU32List at h ⊢
    dsimp only at h ⊢
    set hd := readU32 bs with hhd_def
    set sub := readU32List hd.rest n with hsub_def
    split_ifs at h with hhd hsub
    have h1 := readU32_append (extra := extra) hhd_def.symm (beq_iff_eq.mp hhd)
    have h2 := readU32List_append n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [h1, hhd, beq_self_eq_true, ↓reduceIte, h2, hsub]

private theorem readIds_append (bound : Nat) : ∀ (n : Nat) {bs extra : ByteList} {r : ParseFList},
    readIds bs bound n = r → r.ok = 1 →
    readIds (byteAppend bs extra) bound n =
      { ok := 1, vals := r.vals, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readIds at h ⊢
    dsimp only at h ⊢
    set hd := readU32 bs with hhd_def
    set sub := readIds hd.rest bound n with hsub_def
    split_ifs at h with hhd hsub
    have hhd' := hhd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hhd'
    have h1 := readU32_append (extra := extra) hhd_def.symm hhd'.1
    have h2 := readIds_append bound n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [h1, hhd'.1, hhd'.2, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte, h2, hsub]

private theorem readPoint_append {c : CurveParams} {bs extra : ByteList} {r : ParsePoint}
    (hr : readPoint c bs = r) (h : r.ok = 1) :
    readPoint c (byteAppend bs extra) =
      { ok := 1, point := r.point, rest := byteAppend r.rest extra } := by
  subst hr
  unfold readPoint at h ⊢
  dsimp only at h ⊢
  set rb := readBytes bs c.g1ByteLen with hrb_def
  split_ifs at h with hrb hp
  have h1 := readBytes_append c.g1ByteLen (extra := extra) hrb_def.symm (beq_iff_eq.mp hrb)
  simp only [h1, hrb, beq_self_eq_true, ↓reduceIte, hp]

private theorem readPoints_append (c : CurveParams) : ∀ (n : Nat) {bs extra : ByteList} {r : ParsePointList},
    readPoints c bs n = r → r.ok = 1 →
    readPoints c (byteAppend bs extra) n =
      { ok := 1, points := r.points, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readPoints at h ⊢
    dsimp only at h ⊢
    set hd := readPoint c bs with hhd_def
    set sub := readPoints c hd.rest n with hsub_def
    split_ifs at h with hhd hsub
    have h1 := readPoint_append (extra := extra) hhd_def.symm (beq_iff_eq.mp hhd)
    have h2 := readPoints_append c n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [h1, hhd, beq_self_eq_true, ↓reduceIte, h2, hsub]

private theorem readDigestWords_append {bs extra : ByteList} {r : ParseDigestWords}
    (hr : readDigestWords bs = r) (h : r.ok = 1) :
    readDigestWords (byteAppend bs extra) =
      { ok := 1, digest := r.digest, rest := byteAppend r.rest extra } := by
  subst hr
  unfold readDigestWords at h ⊢
  dsimp only at h ⊢
  set r0 := readU32 bs with hr0
  set r1 := readU32 r0.rest with hr1
  set r2 := readU32 r1.rest with hr2
  set r3 := readU32 r2.rest with hr3
  set r4 := readU32 r3.rest with hr4
  set r5 := readU32 r4.rest with hr5
  set r6 := readU32 r5.rest with hr6
  set r7 := readU32 r6.rest with hr7
  split_ifs at h with hall
  have hall' := hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall'
  rcases hall' with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  have e0 := readU32_append (extra := extra) hr0.symm h0
  have e1 := readU32_append (extra := extra) hr1.symm h1
  have e2 := readU32_append (extra := extra) hr2.symm h2
  have e3 := readU32_append (extra := extra) hr3.symm h3
  have e4 := readU32_append (extra := extra) hr4.symm h4
  have e5 := readU32_append (extra := extra) hr5.symm h5
  have e6 := readU32_append (extra := extra) hr6.symm h6
  have e7 := readU32_append (extra := extra) hr7.symm h7
  simp only [e0, e1, e2, e3, e4, e5, e6, e7, hall, beq_self_eq_true, Bool.and_self, ↓reduceIte]

private theorem readScalarRows_append (c : CurveParams) :
    ∀ (n : Nat) {bs extra : ByteList} {r : ParseFListList},
      readScalarRows c bs n = r → r.ok = 1 →
      readScalarRows c (byteAppend bs extra) n =
        { ok := 1, rows := r.rows, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readScalarRows at h ⊢
    dsimp only at h ⊢
    set w := readU32 bs with hw_def
    set row := readScalars c w.rest w.val with hrow_def
    set sub := readScalarRows c row.rest n with hsub_def
    split_ifs at h with hw hrow hsub
    have e1 := readU32_append (extra := extra) hw_def.symm (beq_iff_eq.mp hw)
    have e2 := readScalars_append c w.val (extra := extra) hrow_def.symm (beq_iff_eq.mp hrow)
    have e3 := readScalarRows_append c n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [e1, e2, e3, hw, hrow, hsub, beq_self_eq_true, ↓reduceIte]

private theorem readOpeningMatrices_append (c : CurveParams) :
    ∀ (n : Nat) {bs extra : ByteList} {r : ParseFList3},
      readOpeningMatrices c bs n = r → r.ok = 1 →
      readOpeningMatrices c (byteAppend bs extra) n =
        { ok := 1, mats := r.mats, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readOpeningMatrices at h ⊢
    dsimp only at h ⊢
    set w := readU32 bs with hw_def
    set rows := readScalarRows c w.rest w.val with hrows_def
    set sub := readOpeningMatrices c rows.rest n with hsub_def
    split_ifs at h with hw hrows hsub
    have e1 := readU32_append (extra := extra) hw_def.symm (beq_iff_eq.mp hw)
    have e2 := readScalarRows_append c w.val (extra := extra) hrows_def.symm (beq_iff_eq.mp hrows)
    have e3 := readOpeningMatrices_append c n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    simp only [e1, e2, e3, hw, hrows, hsub, beq_self_eq_true, ↓reduceIte]

private theorem readOpenings_append {c : CurveParams} {bs extra : ByteList} {r : ParseFList3}
    (hr : readOpenings c bs = r) (h : r.ok = 1) :
    readOpenings c (byteAppend bs extra) =
      { ok := 1, mats := r.mats, rest := byteAppend r.rest extra } := by
  subst hr
  unfold readOpenings at h ⊢
  dsimp only at h ⊢
  set n := readU32 bs with hn_def
  split_ifs at h with hn
  have e1 := readU32_append (extra := extra) hn_def.symm (beq_iff_eq.mp hn)
  have e2 := readOpeningMatrices_append c n.val (extra := extra) rfl h
  simp only [e1, hn, beq_self_eq_true, ↓reduceIte, e2]

private theorem readPackedShapes_append (c : CurveParams) :
    ∀ (n : Nat) {bs extra : ByteList} {r : ParseShapeList},
      readPackedShapes c bs n = r → r.ok = 1 →
      readPackedShapes c (byteAppend bs extra) n =
        { ok := 1, shapes := r.shapes, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readPackedShapes at h ⊢
    dsimp only at h ⊢
    set lg := readU8 bs with hlg_def
    set wd := readU32 lg.rest with hwd_def
    set nx := readU8 wd.rest with hnx_def
    set sub := readPackedShapes c nx.rest n with hsub_def
    split_ifs at h with hcond hsub
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcond'
    rcases hcond' with ⟨⟨⟨⟨⟨hlg, hwd⟩, hnx⟩, hlgLe⟩, hwdNe⟩, hnxLe⟩
    have e1 := readU8_append (extra := extra) hlg_def.symm hlg
    have e2 := readU32_append (extra := extra) hwd_def.symm hwd
    have e3 := readU8_append (extra := extra) hnx_def.symm hnx
    have e4 := readPackedShapes_append c n (extra := extra) hsub_def.symm (beq_iff_eq.mp hsub)
    have hwdNeB : (wd.val != 0) = true := bne_iff_ne.mpr hwdNe
    simp only [e1, e2, e3, e4, hlg, hwd, hnx, hlgLe, hwdNeB, hnxLe, hsub,
      beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]

private theorem readU8_ok_one_of_ne_zero {bs : ByteList} (h : ¬ ((readU8 bs).ok == 0) = true) :
    (readU8 bs).ok = 1 := by
  cases bs with
  | nil => simp [readU8] at h
  | cons b rest =>
    unfold readU8 at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ <;> simp at h ⊢

private theorem readNode_append {c : CurveParams} {bs extra : ByteList} {idx : Nat}
    {s : CircuitShape} {r : ParseNode} (hr : readNode c bs idx s = r) (h : r.ok = 1) :
    readNode c (byteAppend bs extra) idx s =
      { ok := 1, node := r.node, mainNext := r.mainNext, fixedNext := r.fixedNext,
        rest := byteAppend r.rest extra } := by
  subst hr
  unfold readNode at h ⊢
  dsimp only at h ⊢
  set t := readU8 bs with ht_def
  by_cases ht0 : (t.ok == 0) = true
  · simp [ht0] at h
  simp only [ht0, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have htOk : t.ok = 1 := readU8_ok_one_of_ne_zero ht0
  have et := readU8_append (extra := extra) ht_def.symm htOk
  simp only [et, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  rcases htVal : t.val with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [htVal] at h ⊢
  · -- tag 0: const
    set v := readScalar c t.rest with hv_def
    by_cases hv : (v.ok == 1) = true; swap; · simp [hv] at h
    have ev := readScalar_append (extra := extra) hv_def.symm (beq_iff_eq.mp hv)
    simp only [ev, hv, beq_self_eq_true, ↓reduceIte]
  · -- tag 1: var
    set src := readU8 t.rest with hsrc_def
    set off := readU8 src.rest with hoff_def
    set col := readU32 off.rest with hcol_def
    by_cases hcond : (src.ok == 1 && off.ok == 1 && col.ok == 1 && decide (off.val ≤ 1)) = true
    swap; · simp [hcond] at h
    simp only [hcond, ↓reduceIte] at h ⊢
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond'
    rcases hcond' with ⟨⟨⟨hsrc, hoff⟩, hcol⟩, hoffLe⟩
    have e1 := readU8_append (extra := extra) hsrc_def.symm hsrc
    have e2 := readU8_append (extra := extra) hoff_def.symm hoff
    have e3 := readU32_append (extra := extra) hcol_def.symm hcol
    simp only [e1, e2, e3, hoffLe, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
    rcases hsrcV : src.val with _ | _ | _ | _ <;> simp only [hsrcV] at h ⊢
    · split_ifs at h with hlt; simp [hlt]
    · split_ifs at h with hlt; simp [hlt]
    · split_ifs at h with hlt; simp [hlt]
    · simp at h
  · -- tag 2: pub
    set i := readU32 t.rest with hi_def
    by_cases hcond : (i.ok == 1 && decide (i.val < 4)) = true; swap; · simp [hcond] at h
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond'
    have ei := readU32_append (extra := extra) hi_def.symm hcond'.1
    simp only [ei, hcond'.1, hcond'.2, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
  · -- tag 6: add
    set a := readU32 t.rest with ha_def
    set b := readU32 a.rest with hb_def
    by_cases hcond : (a.ok == 1 && b.ok == 1 && decide (a.val < idx) && decide (b.val < idx)) = true
    swap; · simp [hcond] at h
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond'
    rcases hcond' with ⟨⟨⟨ha, hb⟩, haLt⟩, hbLt⟩
    have ea := readU32_append (extra := extra) ha_def.symm ha
    have eb := readU32_append (extra := extra) hb_def.symm hb
    simp only [ea, eb, ha, hb, haLt, hbLt, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
  · -- tag 7: sub
    set a := readU32 t.rest with ha_def
    set b := readU32 a.rest with hb_def
    by_cases hcond : (a.ok == 1 && b.ok == 1 && decide (a.val < idx) && decide (b.val < idx)) = true
    swap; · simp [hcond] at h
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond'
    rcases hcond' with ⟨⟨⟨ha, hb⟩, haLt⟩, hbLt⟩
    have ea := readU32_append (extra := extra) ha_def.symm ha
    have eb := readU32_append (extra := extra) hb_def.symm hb
    simp only [ea, eb, ha, hb, haLt, hbLt, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
  · -- tag 8: mul
    set a := readU32 t.rest with ha_def
    set b := readU32 a.rest with hb_def
    by_cases hcond : (a.ok == 1 && b.ok == 1 && decide (a.val < idx) && decide (b.val < idx)) = true
    swap; · simp [hcond] at h
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond'
    rcases hcond' with ⟨⟨⟨ha, hb⟩, haLt⟩, hbLt⟩
    have ea := readU32_append (extra := extra) ha_def.symm ha
    have eb := readU32_append (extra := extra) hb_def.symm hb
    simp only [ea, eb, ha, hb, haLt, hbLt, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
  · -- tag 9: neg
    set a := readU32 t.rest with ha_def
    by_cases hcond : (a.ok == 1 && decide (a.val < idx)) = true; swap; · simp [hcond] at h
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond'
    have ea := readU32_append (extra := extra) ha_def.symm hcond'.1
    simp only [ea, hcond'.1, hcond'.2, beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]
  · simp at h

private theorem readNodes_append (c : CurveParams) (s : CircuitShape) :
    ∀ (n idx : Nat) {bs extra : ByteList} {r : ParseNodeList},
      readNodes c bs idx s n = r → r.ok = 1 →
      readNodes c (byteAppend bs extra) idx s n =
        { ok := 1, nodes := r.nodes, mainNext := r.mainNext, fixedNext := r.fixedNext,
          rest := byteAppend r.rest extra }
  | 0, _, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, idx, bs, extra, r, hr, h => by
    subst hr
    unfold readNodes at h ⊢
    dsimp only at h ⊢
    set hd := readNode c bs idx s with hhd_def
    set tl := readNodes c hd.rest (idx + 1) s n with htl_def
    by_cases hhd : (hd.ok == 1) = true; swap; · simp [hhd] at h
    simp only [hhd, ↓reduceIte] at h ⊢
    by_cases htl : (tl.ok == 1) = true; swap; · simp [htl] at h
    simp only [htl, ↓reduceIte] at h ⊢
    have e1 := readNode_append (extra := extra) hhd_def.symm (beq_iff_eq.mp hhd)
    have e2 := readNodes_append c s n (idx + 1) (extra := extra) htl_def.symm (beq_iff_eq.mp htl)
    simp only [e1, e2, beq_self_eq_true, ↓reduceIte]

private theorem readLookups_append (bound : Nat) :
    ∀ (n : Nat) {bs extra : ByteList} {r : ParseLookupList},
      readLookups bs bound n = r → r.ok = 1 →
      readLookups (byteAppend bs extra) bound n =
        { ok := 1, lookups := r.lookups, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    unfold readLookups at h ⊢
    dsimp only at h ⊢
    set mult := readU32 bs with hm_def
    set wd := readU32 mult.rest with hw_def
    set args := readIds wd.rest bound wd.val with hargs_def
    set tl := readLookups args.rest bound n with htl_def
    split_ifs at h with hcond hargs htl
    have hcond' := hcond
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond'
    rcases hcond' with ⟨⟨hm, hw⟩, hmLt⟩
    have e1 := readU32_append (extra := extra) hm_def.symm hm
    have e2 := readU32_append (extra := extra) hw_def.symm hw
    have e3 := readIds_append bound wd.val (extra := extra) hargs_def.symm (beq_iff_eq.mp hargs)
    have e4 := readLookups_append bound n (extra := extra) htl_def.symm (beq_iff_eq.mp htl)
    simp only [e1, e2, e3, e4, hm, hw, hmLt, hargs, htl,
      beq_self_eq_true, decide_true, Bool.and_self, ↓reduceIte]

private theorem ite_circuit_ok {p : Prop} [Decidable p] {t : ParseCircuitList}
    (h : (if p then t else { ok := 0, circuits := .nil, rest := .nil }).ok = 1) :
    p ∧ t.ok = 1 := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte] at h; exact ⟨hp, h⟩
  · simp only [hp, ↓reduceIte] at h; exact absurd h (by decide)

private theorem readPackedCircuits_unfold_step (c : CurveParams) (bs : ByteList)
    (budget n : Nat) (cp r0 r1 r2 r3 r4 r5 r6 r7 nc rc lc : ParseNat)
    (ns : ParseNodeList) (rts : ParseFList) (lks : ParseLookupList) (tl : ParseCircuitList)
    (hcp : readU32 bs = cp)
    (hr0 : readU32 cp.rest = r0) (hr1 : readU32 r0.rest = r1)
    (hr2 : readU32 r1.rest = r2) (hr3 : readU32 r2.rest = r3)
    (hr4 : readU32 r3.rest = r4) (hr5 : readU32 r4.rest = r5)
    (hr6 : readU32 r5.rest = r6) (hr7 : readU32 r6.rest = r7)
    (hnc : readU32 r7.rest = nc)
    (hns : readNodes c nc.rest 0
      { m0 := r0.val, m1 := r1.val, m2 := r2.val, m3 := r3.val
        m4 := r4.val, m5 := r5.val, m6 := r6.val, m7 := r7.val } nc.val = ns)
    (hrc : readU32 ns.rest = rc)
    (hrts : readIds rc.rest nc.val rc.val = rts)
    (hlc : readU32 rts.rest = lc)
    (hlks : readLookups lc.rest nc.val lc.val = lks)
    (htl : readPackedCircuits c lks.rest budget n = tl) :
    readPackedCircuits c bs budget (n + 1) =
      let sh : CircuitShape :=
        { m0 := r0.val, m1 := r1.val, m2 := r2.val, m3 := r3.val
          m4 := r4.val, m5 := r5.val, m6 := r6.val, m7 := r7.val }
      let fixedZeroOk := (sh.m2 == 0) == (sh.m3 == 0)
      let fixedHeightOk := sh.m2 == 0 || isSupportedPower sh.m2 1 c.maxLog == 1
      let grps0 := groupCount lc.val sh.m6
      let grps := if grps0 == 0 then 1 else grps0
      if cp.ok == 1 && cp.val != 0 &&
          r0.ok == 1 && r1.ok == 1 && r2.ok == 1 && r3.ok == 1 &&
          r4.ok == 1 && r5.ok == 1 && r6.ok == 1 && r7.ok == 1 then
        if 0 < sh.m6 && sh.m6 < 9 && sh.m1 < budget + 2 &&
            sh.m7 == quotientDegreeFuel sh.m1 1 32 && fixedZeroOk && fixedHeightOk then
          if nc.ok == 1 then
            if ns.ok == 1 then
              if rc.ok == 1 then
                if rts.ok == 1 then
                  if lc.ok == 1 then
                    if lks.ok == 1 then
                      if sh.m5 == grps && sh.m0 == rc.val + grps then
                        let circ : Circuit :=
                          { shape := sh, nodes := ns.nodes, roots := rts.vals, lookups := lks.lookups
                            mainNext := ns.mainNext, fixedNext := ns.fixedNext }
                        if tl.ok == 1 then
                          { ok := 1, circuits := copiesOfCircuit circ tl.circuits cp.val, rest := tl.rest }
                        else { ok := 0, circuits := .nil, rest := .nil }
                      else { ok := 0, circuits := .nil, rest := .nil }
                    else { ok := 0, circuits := .nil, rest := .nil }
                  else { ok := 0, circuits := .nil, rest := .nil }
                else { ok := 0, circuits := .nil, rest := .nil }
              else { ok := 0, circuits := .nil, rest := .nil }
            else { ok := 0, circuits := .nil, rest := .nil }
          else { ok := 0, circuits := .nil, rest := .nil }
        else { ok := 0, circuits := .nil, rest := .nil }
      else { ok := 0, circuits := .nil, rest := .nil } := by
  rcases hcp with rfl; rcases hr0 with rfl; rcases hr1 with rfl; rcases hr2 with rfl
  rcases hr3 with rfl; rcases hr4 with rfl; rcases hr5 with rfl; rcases hr6 with rfl
  rcases hr7 with rfl; rcases hnc with rfl; rcases hns with rfl; rcases hrc with rfl
  rcases hrts with rfl; rcases hlc with rfl; rcases hlks with rfl; rcases htl with rfl
  rfl

private theorem readPackedCircuits_append (c : CurveParams) (budget : Nat) :
    ∀ (n : Nat) {bs extra : ByteList} {r : ParseCircuitList},
      readPackedCircuits c bs budget n = r → r.ok = 1 →
      readPackedCircuits c (byteAppend bs extra) budget n =
        { ok := 1, circuits := r.circuits, rest := byteAppend r.rest extra }
  | 0, _, _, _, hr, _ => by subst hr; rfl
  | n + 1, bs, extra, r, hr, h => by
    subst hr
    generalize hcp : readU32 bs = cp
    generalize hr0 : readU32 cp.rest = r0
    generalize hr1 : readU32 r0.rest = r1
    generalize hr2 : readU32 r1.rest = r2
    generalize hr3 : readU32 r2.rest = r3
    generalize hr4 : readU32 r3.rest = r4
    generalize hr5 : readU32 r4.rest = r5
    generalize hr6 : readU32 r5.rest = r6
    generalize hr7 : readU32 r6.rest = r7
    let sh : CircuitShape :=
      { m0 := r0.val, m1 := r1.val, m2 := r2.val, m3 := r3.val
        m4 := r4.val, m5 := r5.val, m6 := r6.val, m7 := r7.val }
    generalize hnc : readU32 r7.rest = nc
    generalize hns : readNodes c nc.rest 0 sh nc.val = ns
    generalize hrc : readU32 ns.rest = rc
    generalize hrts : readIds rc.rest nc.val rc.val = rts
    generalize hlc : readU32 rts.rest = lc
    generalize hlks : readLookups lc.rest nc.val lc.val = lks
    generalize htl : readPackedCircuits c lks.rest budget n = tl
    have hL := readPackedCircuits_unfold_step c bs budget n cp r0 r1 r2 r3 r4 r5 r6 r7
      nc rc lc ns rts lks tl hcp hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7 hnc hns hrc hrts hlc hlks htl
    rw [hL] at h
    dsimp only at h
    obtain ⟨hhdr, h⟩ := ite_circuit_ok h
    obtain ⟨hshape, h⟩ := ite_circuit_ok h
    obtain ⟨hncOk, h⟩ := ite_circuit_ok h
    obtain ⟨hnsOk, h⟩ := ite_circuit_ok h
    obtain ⟨hrcOk, h⟩ := ite_circuit_ok h
    obtain ⟨hrtsOk, h⟩ := ite_circuit_ok h
    obtain ⟨hlcOk, h⟩ := ite_circuit_ok h
    obtain ⟨hlksOk, h⟩ := ite_circuit_ok h
    obtain ⟨hgrps, h⟩ := ite_circuit_ok h
    obtain ⟨htlOk, _⟩ := ite_circuit_ok h
    have hL_val : readPackedCircuits c bs budget (n + 1) =
        { ok := 1
          circuits := copiesOfCircuit
            { shape := sh, nodes := ns.nodes, roots := rts.vals, lookups := lks.lookups
              mainNext := ns.mainNext, fixedNext := ns.fixedNext } tl.circuits cp.val
          rest := tl.rest } := by
      rw [hL]
      dsimp only
      simp only [hhdr, hshape, hncOk, hnsOk, hrcOk, hrtsOk, hlcOk, hlksOk, hgrps, htlOk, ↓reduceIte]
      rfl
    rw [hL_val]
    have hhdr' := hhdr
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hhdr'
    rcases hhdr' with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hcp1, hcpNe⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
    have ecp := readU32_append (extra := extra) hcp hcp1
    have e0 := readU32_append (extra := extra) hr0 h0
    have e1 := readU32_append (extra := extra) hr1 h1
    have e2 := readU32_append (extra := extra) hr2 h2
    have e3 := readU32_append (extra := extra) hr3 h3
    have e4 := readU32_append (extra := extra) hr4 h4
    have e5 := readU32_append (extra := extra) hr5 h5
    have e6 := readU32_append (extra := extra) hr6 h6
    have e7 := readU32_append (extra := extra) hr7 h7
    have enc := readU32_append (extra := extra) hnc (beq_iff_eq.mp hncOk)
    have ens := readNodes_append c sh nc.val 0 (extra := extra) hns (beq_iff_eq.mp hnsOk)
    have erc := readU32_append (extra := extra) hrc (beq_iff_eq.mp hrcOk)
    have erts := readIds_append nc.val rc.val (extra := extra) hrts (beq_iff_eq.mp hrtsOk)
    have elc := readU32_append (extra := extra) hlc (beq_iff_eq.mp hlcOk)
    have elks := readLookups_append nc.val lc.val (extra := extra) hlks (beq_iff_eq.mp hlksOk)
    have etl := readPackedCircuits_append c budget n (extra := extra) htl (beq_iff_eq.mp htlOk)
    have hR := readPackedCircuits_unfold_step c (byteAppend bs extra) budget n _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ ecp e0 e1 e2 e3 e4 e5 e6 e7 enc ens erc erts elc elks etl
    rw [hR]
    dsimp only
    have hcpNeB : (cp.val != 0) = true := bne_iff_ne.mpr hcpNe
    simp only [hcpNeB, hshape, hgrps, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl

private theorem readPackedWitness_append {c : CurveParams} {bs extra : ByteList} {r : ParseWitness}
    (hr : readPackedWitness c bs = r) (h : r.ok = 1) :
    readPackedWitness c (byteAppend bs extra) =
      { ok := 1, witness := r.witness, rest := byteAppend r.rest extra } := by
  subst hr
  unfold readPackedWitness at h ⊢
  set rb := readBytes bs c.g1ByteLen with hrb_def
  dsimp only at h ⊢
  split_ifs at h with hrb hp
  have e1 := readBytes_append c.g1ByteLen (extra := extra) hrb_def.symm (beq_iff_eq.mp hrb)
  simp only [e1, hrb, beq_self_eq_true, ↓reduceIte, hp]

/-- **Universal Trailing-Byte Rejection for `IXAUCL01` (`readClaims_rejects_trailing`):**
Appending ANY non-empty byte suffix to ANY valid `IXAUCL01` claims payload is rejected (`ok = 0`). -/
theorem readClaims_rejects_trailing {c : CurveParams} {bs tail : ByteList} {b : Nat}
    (h : (readClaims c bs).ok = 1) :
    (readClaims c (byteAppend bs (.cons b tail))).ok = 0 := by
  unfold readClaims at h ⊢
  set m := checkMagic bs magicClaims with hm_def
  set cnt := readU32 m.rest with hcnt_def
  set rows := readScalarRows c cnt.rest cnt.val with hrows_def
  dsimp only at h ⊢
  split_ifs at h with hm hcnt hrows
  simp only [Bool.and_eq_true, beq_iff_eq] at hrows
  have hrestNil : rows.rest = .nil := (checkFinish_eq_one_iff _).mp hrows.2
  have e1 := checkMagic_append (extra := .cons b tail) hm_def.symm (beq_iff_eq.mp hm)
  have e2 := readU32_append (extra := .cons b tail) hcnt_def.symm (beq_iff_eq.mp hcnt)
  have e3 := readScalarRows_append c cnt.val (extra := .cons b tail) hrows_def.symm hrows.1
  simp only [e1, e2, e3, hrestNil, byteAppend, checkFinish,
    beq_self_eq_true, Nat.reduceBEq, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- **Universal Trailing-Byte Rejection for `IXAUKG01` (`readChainPolicy_rejects_trailing`):**
Appending ANY non-empty byte suffix to ANY valid `IXAUKG01` policy payload is rejected (`ok = 0`). -/
theorem readChainPolicy_rejects_trailing {bs tail : ByteList} {b : Nat}
    (h : (readChainPolicy bs).ok = 1) :
    (readChainPolicy (byteAppend bs (.cons b tail))).ok = 0 := by
  unfold readChainPolicy at h ⊢
  set m := checkMagic bs magicChainPolicy with hm_def
  set anc := readBytes m.rest 128 with hanc_def
  set gd := readDigestWords anc.rest with hgd_def
  set ge := readU32 gd.rest with hge_def
  set bd := readDigestWords ge.rest with hbd_def
  set be := readU32 bd.rest with hbe_def
  dsimp only at h ⊢
  split_ifs at h with hm hanc hgd hge hbd hbe
  simp only [Bool.and_eq_true, beq_iff_eq] at hbe
  have hrestNil : be.rest = .nil := (checkFinish_eq_one_iff _).mp hbe.2
  have e1 := checkMagic_append (extra := .cons b tail) hm_def.symm (beq_iff_eq.mp hm)
  have e2 := readBytes_append 128 (extra := .cons b tail) hanc_def.symm (beq_iff_eq.mp hanc)
  have e3 := readDigestWords_append (extra := .cons b tail) hgd_def.symm (beq_iff_eq.mp hgd)
  have e4 := readU32_append (extra := .cons b tail) hge_def.symm (beq_iff_eq.mp hge)
  have e5 := readDigestWords_append (extra := .cons b tail) hbd_def.symm (beq_iff_eq.mp hbd)
  have e6 := readU32_append (extra := .cons b tail) hbe_def.symm hbe.1
  simp only [e1, e2, e3, e4, e5, e6, hrestNil, byteAppend, checkFinish,
    beq_self_eq_true, Nat.reduceBEq, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- **Universal Trailing-Byte Rejection for `IXPSHC02` (`readPackedCommitment_rejects_trailing`):**
Appending ANY non-empty byte suffix to ANY valid `IXPSHC02` commitment is rejected (`ok = 0`). -/
theorem readPackedCommitment_rejects_trailing {c : CurveParams} {bs tail : ByteList} {b : Nat}
    (h : (readPackedCommitment c bs).ok = 1) :
    (readPackedCommitment c (byteAppend bs (.cons b tail))).ok = 0 := by
  unfold readPackedCommitment at h ⊢
  set m := checkMagic bs magicPackedComm with hm_def
  set sc := readU32 m.rest with hsc_def
  set sh := readPackedShapes c sc.rest sc.val with hsh_def
  set pc := readU32 sh.rest with hpc_def
  set pts := readPoints c pc.rest pc.val with hpts_def
  dsimp only at h ⊢
  split_ifs at h with hm hsc hsh hpc hpts
  simp only [Bool.and_eq_true, beq_iff_eq] at hpts
  have hrestNil : pts.rest = .nil := (checkFinish_eq_one_iff _).mp hpts.2
  have e1 := checkMagic_append (extra := .cons b tail) hm_def.symm (beq_iff_eq.mp hm)
  have e2 := readU32_append (extra := .cons b tail) hsc_def.symm (beq_iff_eq.mp hsc)
  have e3 := readPackedShapes_append c sc.val (extra := .cons b tail) hsh_def.symm (beq_iff_eq.mp hsh)
  have e4 := readU32_append (extra := .cons b tail) hpc_def.symm (beq_iff_eq.mp hpc)
  have e5 := readPoints_append c pc.val (extra := .cons b tail) hpts_def.symm hpts.1
  simp only [e1, e2, e3, e4, e5, hrestNil, byteAppend, checkFinish,
    beq_self_eq_true, Nat.reduceBEq, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

private theorem readPackedFixed_rejects_trailing {c : CurveParams} {bs tail : ByteList}
    {numCircuits b : Nat} (h : (readPackedFixed c bs numCircuits).ok = 1) :
    (readPackedFixed c (byteAppend bs (.cons b tail)) numCircuits).ok = 0 := by
  unfold readPackedFixed at h ⊢
  dsimp only at h ⊢
  set t := readU8 bs with ht_def
  by_cases ht0 : (t.ok == 0) = true
  · simp [ht0] at h
  simp only [ht0, Bool.false_eq_true, ↓reduceIte] at h
  have htOk : t.ok = 1 := readU8_ok_one_of_ne_zero ht0
  have et := readU8_append (extra := .cons b tail) ht_def.symm htOk
  simp only [et, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  rcases htVal : t.val with _ | _ | _ | _ <;> simp only [htVal] at h ⊢
  · -- tag 0: .none
    by_cases hfin : (checkFinish t.rest == 1) = true; swap; · simp [hfin] at h
    have hnil := (checkFinish_eq_one_iff _).mp (beq_iff_eq.mp hfin)
    simp [hnil, checkFinish]
  · -- tag 1: .some
    set bl := readBlob t.rest with hbl_def
    by_cases hblob : (bl.ok == 1 && checkFinish bl.rest == 1) = true; swap; · simp [hblob] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hblob
    have hnil := (checkFinish_eq_one_iff _).mp hblob.2
    have eb := readBlob_append (extra := .cons b tail) hbl_def.symm hblob.1
    simp [eb, hnil, checkFinish]
  · -- tag 2: .shared
    set bl := readBlob t.rest with hbl_def
    set cm := readPackedCommitment c bl.bytes
    set sc := readU32 bl.rest with hsc_def
    set sl := readU32List sc.rest sc.val with hsl_def
    by_cases hblob : (bl.ok == 1) = true; swap; · simp [hblob] at h
    simp only [hblob, ↓reduceIte] at h
    by_cases hcmsc : (cm.ok == 1 && sc.ok == 1 && sc.val == numCircuits) = true
    swap; · simp [hcmsc] at h
    simp only [hcmsc, ↓reduceIte] at h
    by_cases hsl : (sl.ok == 1 && checkFinish sl.rest == 1) = true; swap; · simp [hsl] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hcmsc hsl
    have hnil := (checkFinish_eq_one_iff _).mp hsl.2
    have eb := readBlob_append (extra := .cons b tail) hbl_def.symm (beq_iff_eq.mp hblob)
    have esc := readU32_append (extra := .cons b tail) hsc_def.symm hcmsc.1.2
    have esl := readU32List_append sc.val (extra := .cons b tail) hsl_def.symm hsl.1
    have hcm1 : (readPackedCommitment c bl.bytes).ok = 1 := hcmsc.1.1
    rw [eb, esc, esl, hnil]
    simp only [hcm1, hcmsc.2, byteAppend, checkFinish,
      beq_self_eq_true, Nat.reduceBEq, Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- **Universal Trailing-Byte Rejection for `IXAUSK02` (`readPackedKey_rejects_trailing`):**
Appending ANY non-empty byte suffix to ANY valid `IXAUSK02` packed verifying key (across all
three `PackedFixed` modes `.none`, `.some`, `.shared`) is rejected (`ok = 0`). -/
theorem readPackedKey_rejects_trailing {c : CurveParams} {bs tail : ByteList} {b : Nat}
    (h : (readPackedKey c bs).ok = 1) :
    (readPackedKey c (byteAppend bs (.cons b tail))).ok = 0 := by
  unfold readPackedKey at h ⊢
  dsimp only at h ⊢
  set m := checkMagic bs magicPackedKey with hm_def
  set sd := readBlob m.rest with hsd_def
  set ml := readU32 sd.rest with hml_def
  set bg := readU32 ml.rest with hbg_def
  set gen := readPoint c bg.rest with hgen_def
  set anc := readBytes gen.rest 128 with hanc_def
  set cnt := readU32 anc.rest with hcnt_def
  set cs := readPackedCircuits c cnt.rest bg.val cnt.val with hcs_def
  set fx := readPackedFixed c cs.rest (circuitListLen cs.circuits)
  split_ifs at h with hm hhdr hgen hcs hfx
  have hhdr' := hhdr
  have hgen' := hgen
  have hfx' := hfx
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hhdr' hgen' hfx'
  rcases hhdr' with ⟨⟨⟨⟨⟨hsd, hml⟩, hbg⟩, hml0⟩, hmlLe⟩, hbgPow⟩
  rcases hgen' with ⟨⟨⟨hgp, hanc⟩, hcnt⟩, hcntNe⟩
  have em := checkMagic_append (extra := .cons b tail) hm_def.symm (beq_iff_eq.mp hm)
  have esd := readBlob_append (extra := .cons b tail) hsd_def.symm hsd
  have eml := readU32_append (extra := .cons b tail) hml_def.symm hml
  have ebg := readU32_append (extra := .cons b tail) hbg_def.symm hbg
  have egp := readPoint_append (extra := .cons b tail) hgen_def.symm hgp
  have eanc := readBytes_append 128 (extra := .cons b tail) hanc_def.symm hanc
  have ecnt := readU32_append (extra := .cons b tail) hcnt_def.symm hcnt
  have ecs := readPackedCircuits_append c bg.val cnt.val (extra := .cons b tail) hcs_def.symm (beq_iff_eq.mp hcs)
  have efx := readPackedFixed_rejects_trailing (b := b) (tail := tail) hfx'.1
  have hcntNeB : (cnt.val != 0) = true := bne_iff_ne.mpr hcntNe
  simp only [em, esd, eml, ebg, hml0, hmlLe, hbgPow, egp, eanc, ecnt, hcntNeB, ecs, efx,
    beq_self_eq_true, decide_true, Nat.reduceBEq, Bool.and_self, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

/-- **Universal Trailing-Byte Rejection for `IXAUSP01` (`readPackedProof_rejects_trailing`):**
Appending ANY non-empty byte suffix to ANY valid `IXAUSP01` packed SHPLONK proof is rejected (`ok = 0`). -/
theorem readPackedProof_rejects_trailing {c : CurveParams} {bs tail : ByteList} {b : Nat}
    (h : (readPackedProof c bs).ok = 1) :
    (readPackedProof c (byteAppend bs (.cons b tail))).ok = 0 := by
  unfold readPackedProof at h ⊢
  dsimp only at h ⊢
  set m := checkMagic bs magicPackedProof with hm_def
  set ac := readU32 m.rest with hac_def
  set act := readTags ac.rest ac.val with hact_def
  set lc := readU32 act.rest with hlc_def
  set lgs := readTags lc.rest lc.val with hlgs_def
  set mb := readBlob lgs.rest with hmb_def
  set sb := readBlob mb.rest with hsb_def
  set qb := readBlob sb.rest with hqb_def
  set mainC := readPackedCommitment c mb.bytes
  set stage2C := readPackedCommitment c sb.bytes
  set quotC := readPackedCommitment c qb.bytes
  set accCnt := readU32 qb.rest with haccC_def
  set accs := readScalars c accCnt.rest accCnt.val with haccs_def
  set mo := readOpenings c accs.rest with hmo_def
  set so := readOpenings c mo.rest with hso_def
  set qo := readOpenings c so.rest with hqo_def
  set ftag := readU8 qo.rest with hftag_def
  by_cases hm : (m.ok == 1) = true; swap; · simp [hm] at h
  simp only [hm, ↓reduceIte] at h
  by_cases hp1 : (ac.ok == 1 && act.ok == 1 && lc.ok == 1 && lgs.ok == 1 &&
      mb.ok == 1 && sb.ok == 1 && qb.ok == 1) = true
  swap; · simp [hp1] at h
  simp only [hp1, ↓reduceIte] at h
  by_cases hp2 : (mainC.ok == 1 && stage2C.ok == 1 && quotC.ok == 1 &&
      accCnt.ok == 1 && accs.ok == 1 && mo.ok == 1 && so.ok == 1 &&
      qo.ok == 1 && ftag.ok == 1) = true
  swap; · simp [hp2] at h
  simp only [hp2, ↓reduceIte] at h
  have hp1' := hp1
  have hp2' := hp2
  simp only [Bool.and_eq_true, beq_iff_eq] at hp1' hp2'
  rcases hp1' with ⟨⟨⟨⟨⟨⟨hac, hact⟩, hlc⟩, hlgs⟩, hmb⟩, hsb⟩, hqb⟩
  rcases hp2' with ⟨⟨⟨⟨⟨⟨⟨⟨hmc, hsc⟩, hqc⟩, haccC⟩, haccs⟩, hmo⟩, hso⟩, hqo⟩, hftag⟩
  have em := checkMagic_append (extra := .cons b tail) hm_def.symm (beq_iff_eq.mp hm)
  have eac := readU32_append (extra := .cons b tail) hac_def.symm hac
  have eact := readTags_append ac.val (extra := .cons b tail) hact_def.symm hact
  have elc := readU32_append (extra := .cons b tail) hlc_def.symm hlc
  have elgs := readTags_append lc.val (extra := .cons b tail) hlgs_def.symm hlgs
  have emb := readBlob_append (extra := .cons b tail) hmb_def.symm hmb
  have esb := readBlob_append (extra := .cons b tail) hsb_def.symm hsb
  have eqb := readBlob_append (extra := .cons b tail) hqb_def.symm hqb
  have eaccC := readU32_append (extra := .cons b tail) haccC_def.symm haccC
  have eaccs := readScalars_append c accCnt.val (extra := .cons b tail) haccs_def.symm haccs
  have emo := readOpenings_append (extra := .cons b tail) hmo_def.symm hmo
  have eso := readOpenings_append (extra := .cons b tail) hso_def.symm hso
  have eqo := readOpenings_append (extra := .cons b tail) hqo_def.symm hqo
  have eftag := readU8_append (extra := .cons b tail) hftag_def.symm hftag
  have hmc' : (readPackedCommitment c mb.bytes).ok = 1 := hmc
  have hsc' : (readPackedCommitment c sb.bytes).ok = 1 := hsc
  have hqc' : (readPackedCommitment c qb.bytes).ok = 1 := hqc
  simp only [em, eac, eact, elc, elgs, emb, esb, eqb, hmc', hsc', hqc',
    eaccC, eaccs, emo, eso, eqo, eftag, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  rcases hfv : ftag.val with _ | _ | _ <;> simp only [hfv, beq_self_eq_true, ↓reduceIte] at h ⊢
  · -- ftag = 0
    set ec := readU32 ftag.rest with hec_def
    set ex := readScalars c ec.rest ec.val with hex_def
    set w1 := readPackedWitness c ex.rest with hw1_def
    set w2 := readPackedWitness c w1.rest with hw2_def
    by_cases hp3 : (ec.ok == 1 && ex.ok == 1 && w1.ok == 1 && w2.ok == 1 && checkFinish w2.rest == 1) = true
    swap; · simp [hp3] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp3
    rcases hp3 with ⟨⟨⟨⟨hec, hex⟩, hw1⟩, hw2⟩, hfin⟩
    have hnil : w2.rest = .nil := (checkFinish_eq_one_iff _).mp hfin
    have eec := readU32_append (extra := .cons b tail) hec_def.symm hec
    have eex := readScalars_append c ec.val (extra := .cons b tail) hex_def.symm hex
    have ew1 := readPackedWitness_append (extra := .cons b tail) hw1_def.symm hw1
    have ew2 := readPackedWitness_append (extra := .cons b tail) hw2_def.symm hw2
    simp only [eec, eex, ew1, ew2, hnil, byteAppend, checkFinish,
      beq_self_eq_true, Nat.reduceBEq, Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · -- ftag = 1
    set foR := readOpenings c ftag.rest with hfo_def
    set ec := readU32 foR.rest with hec_def
    set ex := readScalars c ec.rest ec.val with hex_def
    set w1 := readPackedWitness c ex.rest with hw1_def
    set w2 := readPackedWitness c w1.rest with hw2_def
    by_cases hfo : (foR.ok == 1) = true; swap; · simp [hfo] at h
    simp only [hfo, ↓reduceIte] at h
    by_cases hp3 : (ec.ok == 1 && ex.ok == 1 && w1.ok == 1 && w2.ok == 1 && checkFinish w2.rest == 1) = true
    swap; · simp [hp3] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at hp3
    rcases hp3 with ⟨⟨⟨⟨hec, hex⟩, hw1⟩, hw2⟩, hfin⟩
    have hnil : w2.rest = .nil := (checkFinish_eq_one_iff _).mp hfin
    have efo := readOpenings_append (extra := .cons b tail) hfo_def.symm (beq_iff_eq.mp hfo)
    have eec := readU32_append (extra := .cons b tail) hec_def.symm hec
    have eex := readScalars_append c ec.val (extra := .cons b tail) hex_def.symm hex
    have ew1 := readPackedWitness_append (extra := .cons b tail) hw1_def.symm hw1
    have ew2 := readPackedWitness_append (extra := .cons b tail) hw2_def.symm hw2
    simp only [efo, eec, eex, ew1, ew2, hnil, byteAppend, checkFinish,
      beq_self_eq_true, Nat.reduceBEq, Bool.and_self, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · simp at h

/-! ### 4.4 Canonical Decoding Soundness & `ChainPolicy ↔ Ix.Cert.AiurCompression.PackedPolicy` Bridge -/

/-- Convert a `KzgWire.ChainPolicy` into `Ix.Cert.AiurCompression.PackedPolicy`. -/
def chainPolicyToCert (pol : ChainPolicy) : PackedPolicy where
  anchors := byteListToUInt8List pol.anchors
  glKeyDigest := byteListToUInt8List (digestWordsToBytes pol.glDigest)
  glEntry := pol.glEntry
  narrowKeyDigest := byteListToUInt8List (digestWordsToBytes pol.bnDigest)
  narrowEntry := pol.bnEntry

private theorem readU32_sound {bs : ByteList} (h : (readU32 bs).ok = 1) :
    (readU32 bs).val < 2 ^ 32 ∧
    bs = byteAppend (encodeU32 (readU32 bs).val) (readU32 bs).rest := by
  match bs with
  | .cons b0 (.cons b1 (.cons b2 (.cons b3 rest))) =>
    unfold readU32 at h ⊢
    dsimp only at h ⊢
    split_ifs at h with hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    rcases hb with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
    refine ⟨by simp only [h0, h1, h2, h3, decide_true, Bool.and_self, ↓reduceIte]; omega, ?_⟩
    simp only [h0, h1, h2, h3, decide_true, Bool.and_self, ↓reduceIte, encodeU32, natToLeBytes,
      byteAppend, ByteList.cons.injEq, and_true]
    exact ⟨by omega, by omega, by omega, by omega⟩
  | .nil | .cons _ .nil | .cons _ (.cons _ .nil) | .cons _ (.cons _ (.cons _ .nil)) =>
    simp [readU32] at h

private theorem readDigestWords_sound {bs : ByteList} (h : (readDigestWords bs).ok = 1) :
    digestWordsCanonical (readDigestWords bs).digest = 1 ∧
    bs = byteAppend (digestWordsToBytes (readDigestWords bs).digest) (readDigestWords bs).rest := by
  unfold readDigestWords at h ⊢
  dsimp only at h ⊢
  set r0 := readU32 bs
  set r1 := readU32 r0.rest
  set r2 := readU32 r1.rest
  set r3 := readU32 r2.rest
  set r4 := readU32 r3.rest
  set r5 := readU32 r4.rest
  set r6 := readU32 r5.rest
  set r7 := readU32 r6.rest
  split_ifs at h with hall
  have hall' := hall
  simp only [Bool.and_eq_true, beq_iff_eq] at hall'
  rcases hall' with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  obtain ⟨lt0, eq0⟩ := readU32_sound h0
  obtain ⟨lt1, eq1⟩ := readU32_sound h1
  obtain ⟨lt2, eq2⟩ := readU32_sound h2
  obtain ⟨lt3, eq3⟩ := readU32_sound h3
  obtain ⟨lt4, eq4⟩ := readU32_sound h4
  obtain ⟨lt5, eq5⟩ := readU32_sound h5
  obtain ⟨lt6, eq6⟩ := readU32_sound h6
  obtain ⟨lt7, eq7⟩ := readU32_sound h7
  simp only [hall, ↓reduceIte]
  refine ⟨(digestWordsCanonical_eq_one_iff _).mpr ⟨lt0, lt1, lt2, lt3, lt4, lt5, lt6, lt7⟩, ?_⟩
  unfold digestWordsToBytes
  conv_lhs => rw [eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  simp only [byteAppend_assoc, encodeU32]
  rfl

/-- **Canonical `IXAUKG01` Chain Policy Soundness & `PackedPolicy` Bridge (`readChainPolicy_sound`):**
When `(readChainPolicy bs).ok = 1`:
1. `byteLen bs = 208` and `bytesCanonical bs = 1`;
2. Every field of `pol := (readChainPolicy bs).policy` is canonical (`128`-byte anchors,
   canonical `u32` digests & entries);
3. Exact canonical wire round-trip `encodeChainPolicy pol = bs`;
4. Exact correspondence with `Ix.Cert.AiurCompression.PackedPolicy`:
   `(chainPolicyToCert pol).WellFormed` AND `(chainPolicyToCert pol).encode = byteListToUInt8List bs`! -/
theorem readChainPolicy_sound {bs : ByteList} (h : (readChainPolicy bs).ok = 1) :
    let pol := (readChainPolicy bs).policy
    byteLen bs = 208 ∧
    bytesCanonical bs = 1 ∧
    byteLen pol.anchors = 128 ∧
    bytesCanonical pol.anchors = 1 ∧
    digestWordsCanonical pol.glDigest = 1 ∧
    pol.glEntry < 2 ^ 32 ∧
    digestWordsCanonical pol.bnDigest = 1 ∧
    pol.bnEntry < 2 ^ 32 ∧
    encodeChainPolicy pol = bs ∧
    (chainPolicyToCert pol).WellFormed ∧
    (chainPolicyToCert pol).encode = byteListToUInt8List bs := by
  unfold readChainPolicy at h ⊢
  dsimp only at h ⊢
  set m := checkMagic bs magicChainPolicy
  set anc := readBytes m.rest 128
  set gd := readDigestWords anc.rest
  set ge := readU32 gd.rest
  set bd := readDigestWords ge.rest
  set be := readU32 bd.rest
  split_ifs at h with hm hanc hgd hge hbd hbe
  have hbe' := hbe
  simp only [Bool.and_eq_true, beq_iff_eq] at hbe'
  have hmEq := beq_iff_eq.mp hm
  have hancEq := beq_iff_eq.mp hanc
  have hgdEq := beq_iff_eq.mp hgd
  have hgeEq := beq_iff_eq.mp hge
  have hbdEq := beq_iff_eq.mp hbd
  have hnil : be.rest = .nil := (checkFinish_eq_one_iff _).mp hbe'.2
  have hmDecomp : bs = byteAppend magicChainPolicy m.rest := by
    have hm1 : (checkMagic bs magicChainPolicy).ok = 1 := hmEq
    change bs = byteAppend magicChainPolicy (checkMagic bs magicChainPolicy).rest
    unfold checkMagic at hm1 ⊢
    dsimp only at hm1 ⊢
    split_ifs at hm1 with hr heq
    have hrEq := beq_iff_eq.mp hr
    have heq' := (byteListEq_eq_one_iff _ _).mp (beq_iff_eq.mp heq)
    have hs := (readBytes_sound 8 hrEq).2.2
    simp only [hr, heq, ↓reduceIte]
    rwa [heq'] at hs
  obtain ⟨hancLen, hancCan, hancDecomp⟩ := readBytes_sound 128 hancEq
  obtain ⟨hgdCan, hgdDecomp⟩ := readDigestWords_sound hgdEq
  obtain ⟨hgeLt, hgeDecomp⟩ := readU32_sound hgeEq
  obtain ⟨hbdCan, hbdDecomp⟩ := readDigestWords_sound hbdEq
  obtain ⟨hbeLt, hbeDecomp⟩ := readU32_sound hbe'.1
  simp only [hm, hanc, hgd, hge, hbd, hbe, ↓reduceIte]
  set pol : ChainPolicy :=
    { anchors := anc.bytes, glDigest := gd.digest, glEntry := ge.val
      bnDigest := bd.digest, bnEntry := be.val }
  have hrt : encodeChainPolicy pol = bs := by
    unfold encodeChainPolicy
    conv_rhs => rw [hmDecomp, hancDecomp, hgdDecomp, hgeDecomp, hbdDecomp, hbeDecomp, hnil,
      byteAppend_nil_right]
  have hmagLen : byteLen magicChainPolicy = 8 := rfl
  have hmagCan : bytesCanonical magicChainPolicy = 1 := rfl
  have hancLen' : byteLen anc.bytes = 128 := hancLen
  have hancCan' : bytesCanonical anc.bytes = 1 := hancCan
  have hlenBs : byteLen bs = 208 := by
    rw [← hrt]
    unfold encodeChainPolicy
    simp only [pol, byteLen_append, hmagLen, hancLen', digestWordsToBytes_len, encodeU32,
      byteLen_natToLeBytes]
  have hcanBs : bytesCanonical bs = 1 := by
    rw [← hrt]
    unfold encodeChainPolicy
    simp only [pol, bytesCanonical_append, hmagCan, hancCan', digestWordsToBytes_canonical,
      encodeU32, bytesCanonical_natToLeBytes, and_true]
  have hwf : (chainPolicyToCert pol).WellFormed :=
    ⟨by simp [chainPolicyToCert, pol, hancLen'], by simp [chainPolicyToCert], hgeLt,
      by simp [chainPolicyToCert], hbeLt⟩
  have hcertEnc : (chainPolicyToCert pol).encode = byteListToUInt8List bs := by
    rw [← hrt]
    unfold PackedPolicy.encode chainPolicyToCert encodeChainPolicy
    simp only [byteListToUInt8List_append, byteListToUInt8List_encodeU32, List.append_assoc]
    have hmag : packedPolicyMagic = byteListToUInt8List magicChainPolicy := by decide
    rw [hmag]
  exact ⟨hlenBs, hcanBs, hancLen, hancCan, hgdCan, hgeLt, hbdCan, hbeLt, hrt, hwf, hcertEnc⟩

private theorem readPoint_valid {c : CurveParams} {bs : ByteList}
    (h : (readPoint c bs).ok = 1) : g1ValidPoint c (readPoint c bs).point = true := by
  unfold readPoint at h ⊢
  dsimp only at h ⊢
  set r := readBytes bs c.g1ByteLen
  split_ifs at h with hr hp
  have hpEq := beq_iff_eq.mp hp
  simp only [hr, hp, ↓reduceIte]
  exact (g1FromBytes_sound hpEq).2.2.1

private theorem readPoints_valid (c : CurveParams) :
    ∀ (n : Nat) {bs : ByteList},
      (readPoints c bs n).ok = 1 → g1PointListValid c (readPoints c bs n).points = true
  | 0, _, _ => rfl
  | n + 1, bs, h => by
    unfold readPoints at h ⊢
    dsimp only at h ⊢
    set r := readPoint c bs
    set sub := readPoints c r.rest n
    split_ifs at h with hr hsub
    have hrEq := beq_iff_eq.mp hr
    have hsubEq := beq_iff_eq.mp hsub
    simp only [hr, hsub, ↓reduceIte, g1PointListValid, Bool.and_eq_true]
    exact ⟨readPoint_valid hrEq, readPoints_valid c n hsubEq⟩

private theorem readPackedWitness_valid {c : CurveParams} {bs : ByteList}
    (h : (readPackedWitness c bs).ok = 1) :
    let w := (readPackedWitness c bs).witness
    g1ValidPoint c w.point = true ∧
    byteLen w.rawBytes = c.g1ByteLen ∧
    bytesCanonical w.rawBytes = 1 ∧
    (g1FromBytes c w.rawBytes).ok = 1 ∧
    (g1FromBytes c w.rawBytes).point = w.point ∧
    (w.point.isInf = 0 → w.rawBytes = g1ToBytes c w.point) := by
  unfold readPackedWitness at h ⊢
  dsimp only at h ⊢
  set r := readBytes bs c.g1ByteLen
  split_ifs at h with hr hp
  have hpEq := beq_iff_eq.mp hp
  have hs := g1FromBytes_sound hpEq
  simp only [hr, hp, ↓reduceIte]
  exact ⟨hs.2.2.1, hs.1, hs.2.1, hpEq, trivial, fun h0 => (hs.2.2.2 h0).symm⟩

/-- **Canonical `IXPSHC02` Packed Commitment Soundness (`readPackedCommitment_sound`):**
Every accepted `IXPSHC02` commitment preserves verbatim wire bytes and validates every decoded
`G1` point via `g1ValidPoint` (canonical `< fqMod`, on-curve, and BLS12-381 subgroup checked). -/
theorem readPackedCommitment_sound {c : CurveParams} {raw : ByteList}
    (h : (readPackedCommitment c raw).ok = 1) :
    (readPackedCommitment c raw).comm.rawBytes = raw ∧
    g1PointListValid c (readPackedCommitment c raw).comm.points = true := by
  unfold readPackedCommitment at h ⊢
  dsimp only at h ⊢
  set m := checkMagic raw magicPackedComm
  set sc := readU32 m.rest
  set sh := readPackedShapes c sc.rest sc.val
  set pc := readU32 sh.rest
  set pts := readPoints c pc.rest pc.val
  split_ifs at h with hm hsc hsh hpc hpts
  have hpts' := hpts
  simp only [Bool.and_eq_true, beq_iff_eq] at hpts'
  simp only [hm, hsc, hsh, hpc, hpts, ↓reduceIte]
  exact ⟨trivial, readPoints_valid c pc.val hpts'.1⟩

/-- **Canonical `IXAUSK02` Packed Key Soundness (`readPackedKey_sound`):**
Every accepted `IXAUSK02` packed verifying key satisfies:
1. Valid domain bound `0 < key.maxLog ≤ c.maxLog`;
2. Canonical 128-byte anchors;
3. Validated generator (`g1ValidPoint c key.generator = true`) AND validated preprocessed
   commitment points (`fixedPointsValid c key.fixed = true`, enforcing on-curve + BLS12-381
   prime-order subgroup membership on all fixed commitments);
4. Canonical key-binding transcript seed (`∃ baseSeed, key.seed = bindPackedSeed c baseSeed key.circuits key.fixed`)! -/
theorem readPackedKey_sound {c : CurveParams} {bs : ByteList}
    (h : (readPackedKey c bs).ok = 1) :
    let key := (readPackedKey c bs).key
    0 < key.maxLog ∧ key.maxLog ≤ c.maxLog ∧
    byteLen key.anchors = 128 ∧ bytesCanonical key.anchors = 1 ∧
    g1ValidPoint c key.generator = true ∧
    fixedPointsValid c key.fixed = true ∧
    seedBindsPackedKey c key.seed key.circuits key.fixed = 1 ∧
    ∃ baseSeed : ByteList, key.seed = bindPackedSeed c baseSeed key.circuits key.fixed := by
  unfold readPackedKey at h ⊢
  dsimp only at h ⊢
  set m := checkMagic bs magicPackedKey
  set sd := readBlob m.rest
  set ml := readU32 sd.rest
  set bg := readU32 ml.rest
  set gen := readPoint c bg.rest
  set anc := readBytes gen.rest 128
  set cnt := readU32 anc.rest
  set cs := readPackedCircuits c cnt.rest bg.val cnt.val
  set fx := readPackedFixed c cs.rest (circuitListLen cs.circuits)
  split_ifs at h with hm hhdr hgen hcs hfx
  have hhdr' := hhdr
  have hgen' := hgen
  have hfx' := hfx
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hhdr' hgen' hfx'
  rcases hhdr' with ⟨⟨⟨⟨⟨_, _⟩, _⟩, hml0⟩, hmlLe⟩, _⟩
  rcases hgen' with ⟨⟨⟨hgp, hanc⟩, _⟩, _⟩
  have hancS := readBytes_sound 128 hanc
  have hgpV := readPoint_valid hgp
  have hfxV : fixedPointsValid c fx.fixed = true := by
    have hfxOk : fx.ok = 1 := hfx'.1
    change fixedPointsValid c (readPackedFixed c cs.rest (circuitListLen cs.circuits)).fixed = true
    change (readPackedFixed c cs.rest (circuitListLen cs.circuits)).ok = 1 at hfxOk
    unfold readPackedFixed at hfxOk ⊢
    dsimp only at hfxOk ⊢
    set t := readU8 cs.rest
    by_cases ht0 : (t.ok == 0) = true
    · simp [ht0] at hfxOk
    simp only [ht0, Bool.false_eq_true, ↓reduceIte] at hfxOk ⊢
    rcases htV : t.val with _ | _ | _ | _ <;> simp only [htV] at hfxOk ⊢
    · split_ifs at hfxOk with hfin
      simp only [hfin, ↓reduceIte, fixedPointsValid]
    · set bl := readBlob t.rest
      split_ifs at hfxOk with hbl hcm
      simp only [hbl, hcm, ↓reduceIte, fixedPointsValid]
      exact (readPackedCommitment_sound (beq_iff_eq.mp hcm)).2
    · set bl := readBlob t.rest
      set cm := readPackedCommitment c bl.bytes
      set sc := readU32 bl.rest
      set sl := readU32List sc.rest sc.val
      split_ifs at hfxOk with hbl hcmsc hsl
      simp only [Bool.and_eq_true, beq_iff_eq] at hcmsc
      simp only [hbl, hcmsc.1.1, hcmsc.1.2, hcmsc.2, hsl, beq_self_eq_true, Bool.and_self,
        ↓reduceIte, fixedPointsValid]
      exact (readPackedCommitment_sound hcmsc.1.1).2
    · simp at hfxOk
  simp only [hm, hhdr, hgen, hcs, hfx, ↓reduceIte]
  exact ⟨hml0, hmlLe, hancS.1, hancS.2.1, hgpV, hfxV, hfx'.2,
    (byteListEndsWith_eq_one_iff _ _).mp hfx'.2⟩

/-- **Canonical `IXAUSP01` Packed Proof Soundness (`readPackedProof_sound`):**
Every accepted `IXAUSP01` proof validates every `G1` commitment point (`main`, `stage2`,
`quotient`) and both opening witnesses (`w1`, `w2`) via `g1ValidPoint`, with verbatim
canonical compressed witness bytes matching `g1FromBytes` (and `g1ToBytes` on finite points). -/
theorem readPackedProof_sound {c : CurveParams} {bs : ByteList}
    (h : (readPackedProof c bs).ok = 1) :
    let proof := (readPackedProof c bs).proof
    g1PointListValid c proof.main.points = true ∧
    g1PointListValid c proof.stage2.points = true ∧
    g1PointListValid c proof.quotient.points = true ∧
    g1ValidPoint c proof.w1.point = true ∧
    g1ValidPoint c proof.w2.point = true ∧
    (proof.w1.point.isInf = 0 → proof.w1.rawBytes = g1ToBytes c proof.w1.point) ∧
    (proof.w2.point.isInf = 0 → proof.w2.rawBytes = g1ToBytes c proof.w2.point) := by
  unfold readPackedProof at h ⊢
  dsimp only at h ⊢
  set m := checkMagic bs magicPackedProof
  set ac := readU32 m.rest
  set act := readTags ac.rest ac.val
  set lc := readU32 act.rest
  set lgs := readTags lc.rest lc.val
  set mb := readBlob lgs.rest
  set sb := readBlob mb.rest
  set qb := readBlob sb.rest
  set mainC := readPackedCommitment c mb.bytes
  set stage2C := readPackedCommitment c sb.bytes
  set quotC := readPackedCommitment c qb.bytes
  set accCnt := readU32 qb.rest
  set accs := readScalars c accCnt.rest accCnt.val
  set mo := readOpenings c accs.rest
  set so := readOpenings c mo.rest
  set qo := readOpenings c so.rest
  set ftag := readU8 qo.rest
  by_cases hm : (m.ok == 1) = true; swap; · simp [hm] at h
  simp only [hm, ↓reduceIte] at h ⊢
  by_cases hp1 : (ac.ok == 1 && act.ok == 1 && lc.ok == 1 && lgs.ok == 1 &&
      mb.ok == 1 && sb.ok == 1 && qb.ok == 1) = true
  swap; · simp [hp1] at h
  simp only [hp1, ↓reduceIte] at h ⊢
  by_cases hp2 : (mainC.ok == 1 && stage2C.ok == 1 && quotC.ok == 1 &&
      accCnt.ok == 1 && accs.ok == 1 && mo.ok == 1 && so.ok == 1 &&
      qo.ok == 1 && ftag.ok == 1) = true
  swap; · simp [hp2] at h
  simp only [hp2, ↓reduceIte] at h ⊢
  have hp2' := hp2
  simp only [Bool.and_eq_true, beq_iff_eq] at hp2'
  rcases hp2' with ⟨⟨⟨⟨⟨⟨⟨⟨hmc, hsc⟩, hqc⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  have hmcV := (readPackedCommitment_sound hmc).2
  have hscV := (readPackedCommitment_sound hsc).2
  have hqcV := (readPackedCommitment_sound hqc).2
  rcases hfv : ftag.val with _ | _ | _ <;> simp only [hfv, beq_self_eq_true, ↓reduceIte] at h ⊢
  · set ec := readU32 ftag.rest
    set ex := readScalars c ec.rest ec.val
    set w1 := readPackedWitness c ex.rest
    set w2 := readPackedWitness c w1.rest
    split_ifs at h with hp3
    have hp3' := hp3
    simp only [Bool.and_eq_true, beq_iff_eq] at hp3'
    rcases hp3' with ⟨⟨⟨⟨_, _⟩, hw1⟩, hw2⟩, _⟩
    have hw1V := readPackedWitness_valid hw1
    have hw2V := readPackedWitness_valid hw2
    simp only [hp3, ↓reduceIte]
    exact ⟨hmcV, hscV, hqcV, hw1V.1, hw2V.1, hw1V.2.2.2.2.2, hw2V.2.2.2.2.2⟩
  · set foR := readOpenings c ftag.rest
    set ec := readU32 foR.rest
    set ex := readScalars c ec.rest ec.val
    set w1 := readPackedWitness c ex.rest
    set w2 := readPackedWitness c w1.rest
    split_ifs at h with hfo hp3
    have hp3' := hp3
    simp only [Bool.and_eq_true, beq_iff_eq] at hp3'
    rcases hp3' with ⟨⟨⟨⟨_, _⟩, hw1⟩, hw2⟩, _⟩
    have hw1V := readPackedWitness_valid hw1
    have hw2V := readPackedWitness_valid hw2
    simp only [hfo, hp3, ↓reduceIte]
    exact ⟨hmcV, hscV, hqcV, hw1V.1, hw2V.1, hw1V.2.2.2.2.2, hw2V.2.2.2.2.2⟩
  · simp at h

/-! ### 4.5 Domain-Separator Parity & Key-Bound Fiat-Shamir Transcript Soundness -/

/-- Pure ASCII byte encoding of a string literal (kernel-reducible without `@[extern]` `ByteArray`). -/
def asciiBytes (s : String) : List UInt8 :=
  s.toList.map fun ch => UInt8.ofNat ch.toNat

/-- Exact ASCII domain-separator parity matching Rust `crates/proof-compression/src/kzg/config.rs`,
`packed_shplonk/config.rs`, and `Ix.Cert.AiurCompression.foldTranscriptDomain`. -/
theorem domainSeparators_exact_ascii :
    byteListToUInt8List v6VkDomainBytes = asciiBytes "multi-stark/v6/vk" ∧
    byteListToUInt8List packedSystemKeyDomainBytes =
      asciiBytes "ix/packed-shplonk/system-key/v1" ++ [0] ∧
    byteListToUInt8List kzgKeySeedDomainBytes =
      asciiBytes "ix/aiur/kzg-key/v1" ++ [0] ∧
    byteListToUInt8List packedShplonkSeedTagBytes =
      asciiBytes "ix/multi-stark/packed-shplonk/v1" ++ [0] ∧
    byteListToUInt8List openDomainBytes =
      asciiBytes "ix/kzg/packed-shplonk-pcs/open/v1" ++ [0] ∧
    byteListToUInt8List batchDomainBytes =
      asciiBytes "ix/kzg/packed-shplonk/v1" ++ [0] ∧
    byteListToUInt8List foldDomainBytes = foldTranscriptDomain := by
  decide

/-- Exact characterization of `seedBindsPackedKey`: holds iff `seed` ends with the canonical
`packedKeySeedSuffix` binding `computePackedKeyDigest` (`"ix/aiur/kzg-key/v1\0" ‖ keyDigest ‖
"ix/multi-stark/packed-shplonk/v1\0"`). -/
theorem seedBindsPackedKey_iff (c : CurveParams) (seed : ByteList)
    (circuits : CircuitList) (fixed : PackedFixed) :
    seedBindsPackedKey c seed circuits fixed = 1 ↔
      ∃ baseSeed : ByteList, seed = bindPackedSeed c baseSeed circuits fixed :=
  byteListEndsWith_eq_one_iff seed (packedKeySeedSuffix c circuits fixed)

/-- Explicit BLAKE3 collision predicate on `KzgWire.ByteList`. -/
def KzgBlake3Collision (a b : ByteList) : Prop :=
  a ≠ b ∧ blake3Hash a = blake3Hash b

/-- Exact injectivity of `packedKeySeedSuffix` in the packed key digest. -/
theorem packedKeySeedSuffix_injective {c : CurveParams}
    {cs₁ cs₂ : CircuitList} {fx₁ fx₂ : PackedFixed}
    (h : packedKeySeedSuffix c cs₁ fx₁ = packedKeySeedSuffix c cs₂ fx₂) :
    computePackedKeyDigest c cs₁ fx₁ = computePackedKeyDigest c cs₂ fx₂ := by
  unfold packedKeySeedSuffix at h
  have h1 := byteAppend_inj_left h
  have h2 := (byteAppend_inj_of_len (by simp) h1).1
  exact digest32ToBytes_inj h2

private theorem blake3Hash_eq_prefix_binds (dom p₁ p₂ t₁ t₂ : ByteList)
    (hlen : byteLen p₁ = byteLen p₂)
    (h : blake3Hash (byteAppend dom (byteAppend p₁ t₁)) =
      blake3Hash (byteAppend dom (byteAppend p₂ t₂))) :
    (∃ pre₁ pre₂ : ByteList, KzgBlake3Collision pre₁ pre₂) ∨
    (p₁ = p₂ ∧ byteAppend dom (byteAppend p₁ t₁) = byteAppend dom (byteAppend p₂ t₂)) := by
  by_cases hpre : byteAppend dom (byteAppend p₁ t₁) = byteAppend dom (byteAppend p₂ t₂)
  · exact Or.inr ⟨(byteAppend_inj_of_len hlen (byteAppend_inj_left hpre)).1, hpre⟩
  · exact Or.inl ⟨_, _, hpre, h⟩

/-- **Key-Digest Binding Soundness (`computePackedKeyDigest_binds_vk_and_fixed`):**
Equal `computePackedKeyDigest` values EITHER exhibit a concrete BLAKE3 collision on the
domain-separated `"ix/packed-shplonk/system-key/v1\0" ‖ vkDigest ‖ preprocessedPart` preimages,
OR force exact equality of `computeVkDigest cs₁ = computeVkDigest cs₂` AND the entire
preprocessed commitment/slot byte serialization! -/
theorem computePackedKeyDigest_binds_vk_and_fixed (c : CurveParams)
    (cs₁ cs₂ : CircuitList) (fx₁ fx₂ : PackedFixed)
    (hdig : computePackedKeyDigest c cs₁ fx₁ = computePackedKeyDigest c cs₂ fx₂) :
    (∃ pre₁ pre₂ : ByteList, KzgBlake3Collision pre₁ pre₂) ∨
    (computeVkDigest cs₁ = computeVkDigest cs₂ ∧
      packedKeySeedSuffix c cs₁ fx₁ = packedKeySeedSuffix c cs₂ fx₂) := by
  have hdig' := hdig
  unfold computePackedKeyDigest at hdig'
  dsimp only at hdig'
  rcases blake3Hash_eq_prefix_binds _ _ _ _ _ (by simp) hdig' with hcol | ⟨hvkBytes, _⟩
  · exact Or.inl hcol
  · refine Or.inr ⟨digest32ToBytes_inj hvkBytes, ?_⟩
    unfold packedKeySeedSuffix
    rw [hdig]

/-- Helper lemma: `observeKey` preserves the initial `zeroBytes32 ‖ key.seed` prefix (carrying
the canonical key-binding suffix) AND appends `fx.rawBytes` verbatim for `.some`/`.shared` keys. -/
theorem observeKey_structure (seed : ByteList) (circuits : CircuitList) (active : FList)
    (fixed : PackedFixed) :
    (∃ rest : ByteList,
      (observeKey seed circuits active fixed).buf =
        byteAppend (byteAppend zeroBytes32 seed) rest) ∧
    (∀ fx, fixed = .some fx →
      ∃ pre : ByteList, (observeKey seed circuits active fixed).buf = byteAppend pre fx.rawBytes) ∧
    (∀ fx slots, fixed = .shared fx slots →
      ∃ pre : ByteList, (observeKey seed circuits active fixed).buf = byteAppend pre fx.rawBytes) := by
  have hobsFields : ∀ tr vs, ∃ suf, (transcriptObserveFields tr vs).buf = byteAppend tr.buf suf := by
    intro tr vs
    induction vs generalizing tr with
    | nil => exact ⟨.nil, by simp [transcriptObserveFields]⟩
    | cons v tl ih =>
      obtain ⟨suf, hsuf⟩ := ih (transcriptObserveField tr v)
      exact ⟨byteAppend (natToLeBytes 32 v) suf, by
        simpa [transcriptObserveFields, transcriptObserveField, transcriptObserveBytes,
          byteAppend_assoc] using hsuf⟩
  have hobsShapes : ∀ tr cs, ∃ suf, (observeCircuitShapes tr cs).buf = byteAppend tr.buf suf := by
    intro tr cs
    induction cs generalizing tr with
    | nil => exact ⟨.nil, by simp [observeCircuitShapes]⟩
    | cons circ tl ih =>
      let s := circ.shape
      let tr7 :=
        transcriptObserveField
          (transcriptObserveField
            (transcriptObserveField
              (transcriptObserveField
                (transcriptObserveField
                  (transcriptObserveField
                    (transcriptObserveField tr s.m0) s.m1) s.m2) s.m3) s.m4) s.m5) s.m6
      obtain ⟨suf, hsuf⟩ := ih tr7
      refine ⟨byteAppend (natToLeBytes 32 s.m0)
        (byteAppend (natToLeBytes 32 s.m1)
        (byteAppend (natToLeBytes 32 s.m2)
        (byteAppend (natToLeBytes 32 s.m3)
        (byteAppend (natToLeBytes 32 s.m4)
        (byteAppend (natToLeBytes 32 s.m5)
        (byteAppend (natToLeBytes 32 s.m6) suf)))))), ?_⟩
      simpa [observeCircuitShapes, tr7, s, transcriptObserveField, transcriptObserveBytes,
        byteAppend_assoc] using hsuf
  refine ⟨?_, ?_, ?_⟩
  · unfold observeKey
    obtain ⟨s1, hs1⟩ := hobsShapes (transcriptObserveField (transcriptStart seed) (circuitListLen circuits)) circuits
    cases fixed with
    | none =>
      obtain ⟨s2, hs2⟩ := hobsFields (observeCircuitShapes (transcriptObserveField (transcriptStart seed) (circuitListLen circuits)) circuits) active
      refine ⟨byteAppend (natToLeBytes 32 (circuitListLen circuits)) (byteAppend s1 s2), ?_⟩
      rw [hs2, hs1]
      simp [transcriptObserveField, transcriptObserveBytes, transcriptStart, byteAppend_assoc]
    | some fx =>
      obtain ⟨s2, hs2⟩ := hobsFields (observeCircuitShapes (transcriptObserveField (transcriptStart seed) (circuitListLen circuits)) circuits) active
      refine ⟨byteAppend (natToLeBytes 32 (circuitListLen circuits))
        (byteAppend s1 (byteAppend s2 fx.rawBytes)), ?_⟩
      simp only [transcriptObserveBytes]
      rw [hs2, hs1]
      simp [transcriptObserveField, transcriptObserveBytes, transcriptStart, byteAppend_assoc]
    | shared fx slots =>
      obtain ⟨s2, hs2⟩ := hobsFields (observeCircuitShapes (transcriptObserveField (transcriptStart seed) (circuitListLen circuits)) circuits) slots
      obtain ⟨s3, hs3⟩ := hobsFields (transcriptObserveFields (observeCircuitShapes (transcriptObserveField (transcriptStart seed) (circuitListLen circuits)) circuits) slots) active
      refine ⟨byteAppend (natToLeBytes 32 (circuitListLen circuits))
        (byteAppend s1 (byteAppend s2 (byteAppend s3 fx.rawBytes))), ?_⟩
      simp only [transcriptObserveBytes]
      rw [hs3, hs2, hs1]
      simp [transcriptObserveField, transcriptObserveBytes, transcriptStart, byteAppend_assoc]
  · intro fx hfx; subst hfx
    exact ⟨_, rfl⟩
  · intro fx slots hfx; subst hfx
    exact ⟨_, rfl⟩

private theorem byteListEndsWith_zero_or_one (bs suf : ByteList) :
    byteListEndsWith bs suf = 0 ∨ byteListEndsWith bs suf = 1 := by
  have hle : ∀ a b, byteListEq a b = 0 ∨ byteListEq a b = 1 := by
    intro a; induction a with
    | nil => intro b; cases b <;> simp [byteListEq]
    | cons x xs ih =>
      intro b; cases b with
      | nil => simp [byteListEq]
      | cons y ys =>
        unfold byteListEq; split_ifs
        · exact ih ys
        · exact Or.inl rfl
  unfold byteListEndsWith
  dsimp only
  split_ifs
  · exact Or.inl rfl
  · exact hle _ _

/-- **Key-Binding Transcript Soundness of `KzgPackedPure.verifyPacked` (`verifyPacked_key_binding_sound`):**
Whenever `(verifyPacked c key proof claims).ok = 1`:
1. `key.seed` is bound to `(key.circuits, key.fixed)` via `bindPackedSeed` (embedding
   `"ix/aiur/kzg-key/v1\0" ‖ computePackedKeyDigest c key.circuits key.fixed ‖
    "ix/multi-stark/packed-shplonk/v1\0"` into the Fiat-Shamir transcript seed, matching
   Rust `KzgConfig::with_key_digest` and `bind_packed_system_key`);
2. `key.generator` and EVERY preprocessed commitment point in `key.fixed` pass `g1ValidPoint`
   (canonical `< fqMod`, on-curve, and BLS12-381 prime-order subgroup checked);
3. EVERY proof commitment point (`main`, `stage2`, `quotient`) and BOTH SHPLONK witnesses
   (`w1`, `w2`) pass `g1ValidPoint`;
4. The initial Fiat-Shamir transcript `(observeKey key.seed key.circuits proof.active key.fixed).buf`
   absorbs BOTH the bound key-digest seed prefix AND `fx.rawBytes` verbatim (for `.some`/`.shared` keys). -/
theorem verifyPacked_key_binding_sound {c : CurveParams} {key : PackedKey}
    {proof : PackedProof} {claims : FListList}
    (h : (verifyPacked c key proof claims).ok = 1) :
    seedBindsPackedKey c key.seed key.circuits key.fixed = 1 ∧
    (∃ baseSeed : ByteList, key.seed = bindPackedSeed c baseSeed key.circuits key.fixed) ∧
    g1ValidPoint c key.generator = true ∧
    fixedPointsValid c key.fixed = true ∧
    g1PointListValid c proof.main.points = true ∧
    g1PointListValid c proof.stage2.points = true ∧
    g1PointListValid c proof.quotient.points = true ∧
    g1ValidPoint c proof.w1.point = true ∧
    g1ValidPoint c proof.w2.point = true ∧
    (∃ baseSeed rest : ByteList,
      (observeKey key.seed key.circuits proof.active key.fixed).buf =
        byteAppend (byteAppend zeroBytes32 (bindPackedSeed c baseSeed key.circuits key.fixed)) rest) ∧
    (∀ fx, key.fixed = .some fx →
      ∃ pre : ByteList,
        (observeKey key.seed key.circuits proof.active key.fixed).buf = byteAppend pre fx.rawBytes) ∧
    (∀ fx slots, key.fixed = .shared fx slots →
      ∃ pre : ByteList,
        (observeKey key.seed key.circuits proof.active key.fixed).buf = byteAppend pre fx.rawBytes) := by
  unfold verifyPacked at h
  dsimp only at h
  by_cases hseed : (seedBindsPackedKey c key.seed key.circuits key.fixed == 0) = true
  · simp [hseed] at h
  simp only [hseed] at h
  by_cases hpts : (!g1ValidPoint c key.generator || !fixedPointsValid c key.fixed ||
      !g1PointListValid c proof.main.points || !g1PointListValid c proof.stage2.points ||
      !g1PointListValid c proof.quotient.points || !g1ValidPoint c proof.w1.point ||
      !g1ValidPoint c proof.w2.point) = true
  · simp [hpts] at h
  have hseed1 : seedBindsPackedKey c key.seed key.circuits key.fixed = 1 := by
    rcases byteListEndsWith_zero_or_one key.seed (packedKeySeedSuffix c key.circuits key.fixed) with h0 | h1
    · exact absurd (beq_iff_eq.mpr h0) hseed
    · exact h1
  obtain ⟨baseSeed, hbase⟩ := (seedBindsPackedKey_iff c key.seed key.circuits key.fixed).mp hseed1
  simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hpts
  rcases hpts with ⟨⟨⟨⟨⟨⟨hgen, hfix⟩, hmain⟩, hs2⟩, hquot⟩, hw1⟩, hw2⟩
  obtain ⟨⟨rest, hrest⟩, hsome, hshared⟩ := observeKey_structure key.seed key.circuits proof.active key.fixed
  exact ⟨hseed1, ⟨baseSeed, hbase⟩, hgen, hfix, hmain, hs2, hquot, hw1, hw2,
    ⟨baseSeed, rest, by rw [← hbase]; exact hrest⟩, hsome, hshared⟩

/-- Constructive negative control: any key whose seed does not carry the canonical
`packedKeySeedSuffix` is unconditionally rejected by `verifyPacked`. -/
theorem verifyPacked_rejects_unbound_seed {c : CurveParams} {key : PackedKey}
    {proof : PackedProof} {claims : FListList}
    (hunbound : seedBindsPackedKey c key.seed key.circuits key.fixed = 0) :
    (verifyPacked c key proof claims).ok = 0 := by
  unfold verifyPacked
  simp [hunbound]

/-- Constructive negative control: any key with an invalid or non-subgroup preprocessed
commitment point is unconditionally rejected by `verifyPacked`. -/
theorem verifyPacked_rejects_invalid_fixed {c : CurveParams} {key : PackedKey}
    {proof : PackedProof} {claims : FListList}
    (hbad : fixedPointsValid c key.fixed = false) :
    (verifyPacked c key proof claims).ok = 0 := by
  unfold verifyPacked
  dsimp only
  by_cases h1 : (seedBindsPackedKey c key.seed key.circuits key.fixed == 0) = true
  · simp [h1]
  · simp [h1, hbad]

/-- Constructive negative control: inserting the BLS12-381 on-curve torsion point (`x = 4`)
into a `PackedFixed` commitment or SHPLONK witness is unconditionally rejected by `verifyPacked`. -/
theorem verifyPacked_rejects_bls12381_torsion {key : PackedKey} {proof : PackedProof}
    {claims : FListList} :
    (∀ comm, key.fixed = .some comm → ∀ pts, comm.points = .cons bls12381TorsionWitness pts →
      (verifyPacked bls12381CurveParams key proof claims).ok = 0) ∧
    (proof.w1.point = bls12381TorsionWitness →
      (verifyPacked bls12381CurveParams key proof claims).ok = 0) ∧
    (proof.w2.point = bls12381TorsionWitness →
      (verifyPacked bls12381CurveParams key proof claims).ok = 0) := by
  have hPbad : g1ValidPoint bls12381CurveParams bls12381TorsionWitness = false :=
    kzgWire_bls12381_torsion_rejected.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · intro comm hfx pts hpts
    apply verifyPacked_rejects_invalid_fixed
    simp [fixedPointsValid, hfx, hpts, g1PointListValid, hPbad]
  · intro hw1
    unfold verifyPacked; dsimp only
    by_cases h1 : (seedBindsPackedKey bls12381CurveParams key.seed key.circuits key.fixed == 0) = true
    · simp [h1]
    · simp [h1, hw1, hPbad]
  · intro hw2
    unfold verifyPacked; dsimp only
    by_cases h1 : (seedBindsPackedKey bls12381CurveParams key.seed key.circuits key.fixed == 0) = true
    · simp [h1]
    · simp [h1, hw2, hPbad]

end WireAndKeyBinding

/-! ## Section 5: 4-Bit Windowed MSM, Packed SHPLONK Opening & Two-Stage Deferred Fold Soundness -/

section ShplonkAndDeferredFold

/-! ### 5.1 Abstract `G1GroupModel` & 4-Bit Windowed Straus MSM Soundness (`g1Msm_sound`) -/

/-- Exact algebraic group model of `KzgWire`'s `G1Point` arithmetic (`g1Inf`, `g1Neg`, `g1Double`,
`g1Add`) over an additive commutative group `G` (instantiated below by `BilinearPairing.G1` for
BN254 and `Bls12381BilinearPairing.G1` for BLS12-381). -/
structure G1GroupModel (c : CurveParams) (G : Type*) [AddCommGroup G] where
  Valid : G1Point → Prop
  toG : G1Point → G
  valid_inf : Valid g1Inf
  toG_inf : toG g1Inf = 0
  valid_neg : ∀ {P}, Valid P → Valid (g1Neg c P)
  toG_neg : ∀ {P}, Valid P → toG (g1Neg c P) = -toG P
  valid_double : ∀ {P}, Valid P → Valid (g1Double c P)
  toG_double : ∀ {P}, Valid P → toG (g1Double c P) = toG P + toG P
  valid_add : ∀ {P Q}, Valid P → Valid Q → Valid (g1Add c P Q)
  toG_add : ∀ {P Q}, Valid P → Valid Q → toG (g1Add c P Q) = toG P + toG Q

/-- All points in a `G1PointList` satisfy `M.Valid`. -/
def g1PointListAllValid {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) : G1PointList → Prop
  | .nil => True
  | .cons p rest => M.Valid p ∧ g1PointListAllValid M rest

/-- All term points in a `G1TermList` satisfy `M.Valid`. -/
def g1TermListAllValid {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) : G1TermList → Prop
  | .nil => True
  | .cons t rest => M.Valid t.point ∧ g1TermListAllValid M rest

/-- Exact group sum of a `G1PointList` under `M`. -/
def g1PointListSum {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) : G1PointList → G
  | .nil => 0
  | .cons p rest => M.toG p + g1PointListSum M rest

/-- Exact multi-scalar linear combination `∑ (t.scalar % c.frMod) • M.toG t.point` under `M`. -/
def g1TermSum {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) : G1TermList → G
  | .nil => 0
  | .cons t rest => (t.scalar % c.frMod) • M.toG t.point + g1TermSum M rest

/-- Validity invariant on a 4-bit windowed `MsmPreparedList`: every 16-entry table contains valid
points with `table[d] = d • table[1]` for every `0 ≤ d < 16`. -/
private def msmPreparedValid {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) : MsmPreparedList → Prop
  | .nil => True
  | .cons t rest =>
    (∀ d < 16, M.Valid (g1PointListGet t.table d) ∧
      M.toG (g1PointListGet t.table d) = d • M.toG (g1PointListGet t.table 1)) ∧
    msmPreparedValid M rest

/-- Remaining scalar bound `∀ t ∈ prep, t.rem < bound`. -/
private def msmPreparedRemLt (bound : Nat) : MsmPreparedList → Prop
  | .nil => True
  | .cons t rest => t.rem < bound ∧ msmPreparedRemLt bound rest

/-- Remaining weighted sum `∑ t.rem • M.toG (table[1])`. -/
private def msmPreparedSum {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) : MsmPreparedList → G
  | .nil => 0
  | .cons t rest => t.rem • M.toG (g1PointListGet t.table 1) + msmPreparedSum M rest

private theorem g1WindowTableAux_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) {P : G1Point} (hP : M.Valid P) :
    ∀ (n k : Nat) (cur : G1Point),
      M.Valid cur → M.toG cur = k • M.toG P →
      ∀ d < n, M.Valid (g1PointListGet (g1WindowTableAux c P cur n) d) ∧
        M.toG (g1PointListGet (g1WindowTableAux c P cur n) d) = (k + d) • M.toG P
  | 0, _, _, _, _, d, hd => absurd hd (Nat.not_lt_zero d)
  | n + 1, k, cur, hcur, hcurG, d, hd => by
    cases d with
    | zero =>
      simp only [g1WindowTableAux, g1PointListGet, Nat.add_zero]
      exact ⟨hcur, hcurG⟩
    | succ d' =>
      simp only [g1WindowTableAux, g1PointListGet]
      have hnextV : M.Valid (g1Add c cur P) := M.valid_add hcur hP
      have hnextG : M.toG (g1Add c cur P) = (k + 1) • M.toG P := by
        rw [M.toG_add hcur hP, hcurG, add_nsmul, one_nsmul]
      have ih := g1WindowTableAux_sound M hP n (k + 1) (g1Add c cur P) hnextV hnextG
        d' (Nat.lt_of_succ_lt_succ hd)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem g1WindowTable_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) {P : G1Point} (hP : M.Valid P) :
    ∀ d < 16, M.Valid (g1PointListGet (g1WindowTable c P) d) ∧
      M.toG (g1PointListGet (g1WindowTable c P) d) = d • M.toG P := by
  intro d hd
  have h := g1WindowTableAux_sound M hP 16 0 g1Inf M.valid_inf (by rw [M.toG_inf, zero_nsmul]) d hd
  unfold g1WindowTable
  simpa using h

private theorem g1MsmPrepare_sound_pos {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) (hfrPos : 0 < c.frMod) (hfr : c.frMod < 2 ^ 256) :
    ∀ {terms : G1TermList}, g1TermListAllValid M terms →
      msmPreparedValid M (g1MsmPrepare c terms) ∧
      msmPreparedRemLt (16 ^ 64) (g1MsmPrepare c terms) ∧
      msmPreparedSum M (g1MsmPrepare c terms) = g1TermSum M terms
  | .nil, _ => ⟨trivial, trivial, rfl⟩
  | .cons t rest, ⟨htV, hrestV⟩ => by
    obtain ⟨hV, hLt, hSum⟩ := g1MsmPrepare_sound_pos M hfrPos hfr hrestV
    have htab := g1WindowTable_sound M htV
    have h1 : M.toG (g1PointListGet (g1WindowTable c t.point) 1) = M.toG t.point := by
      simpa using (htab 1 (by decide)).2
    have hremLt : t.scalar % c.frMod < 16 ^ 64 := by
      have hmodLt : t.scalar % c.frMod < c.frMod := Nat.mod_lt _ hfrPos
      have hpow : (2 : Nat) ^ 256 = 16 ^ 64 := by decide
      omega
    refine ⟨⟨fun d hd => ?_, hV⟩, ⟨hremLt, hLt⟩, ?_⟩
    · refine ⟨(htab d hd).1, ?_⟩
      rw [(htab d hd).2, h1]
    · simp only [g1MsmPrepare, msmPreparedSum, g1TermSum, h1, hSum]

private theorem g1AddPoints_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) :
    ∀ (pts : G1PointList) (acc : G1Point),
      g1PointListAllValid M pts → M.Valid acc →
      M.Valid (g1AddPoints c pts acc) ∧
      M.toG (g1AddPoints c pts acc) = M.toG acc + g1PointListSum M pts
  | .nil, acc, _, hacc => ⟨hacc, by simp [g1AddPoints, g1PointListSum]⟩
  | .cons p rest, acc, ⟨hp, hrest⟩, hacc => by
    have hacc' : M.Valid (g1Add c acc p) := M.valid_add hacc hp
    obtain ⟨hv, hg⟩ := g1AddPoints_sound M rest (g1Add c acc p) hrest hacc'
    refine ⟨hv, ?_⟩
    simp only [g1AddPoints, g1PointListSum]
    rw [hg, M.toG_add hacc hp, add_assoc]

private theorem g1Double4_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) {P : G1Point} (hP : M.Valid P) :
    M.Valid (g1Double4 c P) ∧ M.toG (g1Double4 c P) = 16 • M.toG P := by
  have h1 := M.valid_double hP
  have h2 := M.valid_double h1
  have h3 := M.valid_double h2
  have h4 := M.valid_double h3
  refine ⟨h4, ?_⟩
  unfold g1Double4
  rw [M.toG_double h3, M.toG_double h2, M.toG_double h1, M.toG_double hP]
  have h16 : (16 : Nat) • M.toG P =
      (((M.toG P + M.toG P) + (M.toG P + M.toG P)) +
       ((M.toG P + M.toG P) + (M.toG P + M.toG P))) +
      (((M.toG P + M.toG P) + (M.toG P + M.toG P)) +
       ((M.toG P + M.toG P) + (M.toG P + M.toG P))) := by
    simp only [show (16 : Nat) = 8 + 8 from rfl, show (8 : Nat) = 4 + 4 from rfl,
      show (4 : Nat) = 2 + 2 from rfl, show (2 : Nat) = 1 + 1 from rfl, add_nsmul, one_nsmul]
  exact h16.symm

private theorem g1MsmSplit_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) (n : Nat) :
    ∀ {prep : MsmPreparedList},
      msmPreparedValid M prep → msmPreparedRemLt (16 ^ (n + 1)) prep →
      msmPreparedValid M (g1MsmSplit prep).next ∧
      msmPreparedRemLt (16 ^ n) (g1MsmSplit prep).next ∧
      g1PointListAllValid M (g1MsmSplit prep).selected ∧
      16 • msmPreparedSum M (g1MsmSplit prep).next + g1PointListSum M (g1MsmSplit prep).selected =
        msmPreparedSum M prep
  | .nil, _, _ => ⟨trivial, trivial, trivial, by simp [g1MsmSplit, msmPreparedSum, g1PointListSum]⟩
  | .cons t rest, ⟨htV, hrestV⟩, ⟨htLt, hrestLt⟩ => by
    obtain ⟨hnV, hnLt, hsV, hsum⟩ := g1MsmSplit_sound M n hrestV hrestLt
    have hqLt : t.rem / 16 < 16 ^ n := by
      have hpow : 16 ^ (n + 1) = 16 ^ n * 16 := Nat.pow_succ _ _
      rw [hpow] at htLt
      exact Nat.div_lt_of_lt_mul (by omega)
    have hdLt : t.rem % 16 < 16 := Nat.mod_lt _ (by decide)
    have hdivMod : 16 * (t.rem / 16) + t.rem % 16 = t.rem := Nat.div_add_mod t.rem 16
    unfold g1MsmSplit
    dsimp only
    by_cases hd0 : (t.rem % 16 == 0) = true
    · have hdEq0 : t.rem % 16 = 0 := beq_iff_eq.mp hd0
      simp only [hd0, ↓reduceIte]
      refine ⟨⟨htV, hnV⟩, ⟨hqLt, hnLt⟩, hsV, ?_⟩
      simp only [msmPreparedSum]
      rw [smul_add, ← mul_nsmul, add_assoc, hsum]
      have hremEq : t.rem / 16 * 16 = t.rem := by omega
      rw [hremEq]
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hptV, hptG⟩ := htV (t.rem % 16) hdLt
      refine ⟨⟨htV, hnV⟩, ⟨hqLt, hnLt⟩, ⟨hptV, hsV⟩, ?_⟩
      simp only [msmPreparedSum, g1PointListSum]
      rw [smul_add, ← mul_nsmul, hptG]
      calc (t.rem / 16 * 16) • M.toG (g1PointListGet t.table 1) +
            16 • msmPreparedSum M (g1MsmSplit rest).next +
            ((t.rem % 16) • M.toG (g1PointListGet t.table 1) +
              g1PointListSum M (g1MsmSplit rest).selected)
          = ((t.rem / 16 * 16) • M.toG (g1PointListGet t.table 1) +
              (t.rem % 16) • M.toG (g1PointListGet t.table 1)) +
            (16 • msmPreparedSum M (g1MsmSplit rest).next +
              g1PointListSum M (g1MsmSplit rest).selected) := by abel
        _ = (t.rem / 16 * 16 + t.rem % 16) • M.toG (g1PointListGet t.table 1) +
              msmPreparedSum M rest := by rw [← add_nsmul, hsum]
        _ = t.rem • M.toG (g1PointListGet t.table 1) + msmPreparedSum M rest := by
            rw [Nat.mul_comm (t.rem / 16) 16, hdivMod]

private theorem msmPreparedSum_zero_of_lt_one {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) :
    ∀ {prep : MsmPreparedList}, msmPreparedRemLt 1 prep → msmPreparedSum M prep = 0
  | .nil, _ => rfl
  | .cons t rest, ⟨htLt, hrestLt⟩ => by
    have h0 : t.rem = 0 := by omega
    simp only [msmPreparedSum, h0, zero_nsmul, zero_add]
    exact msmPreparedSum_zero_of_lt_one M hrestLt

private theorem g1MsmWindows_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) :
    ∀ (n : Nat) (prep : MsmPreparedList) (acc : G1Point),
      msmPreparedValid M prep → msmPreparedRemLt (16 ^ n) prep → M.Valid acc →
      M.Valid (g1MsmWindows c n prep acc) ∧
      M.toG (g1MsmWindows c n prep acc) = (16 ^ n) • M.toG acc + msmPreparedSum M prep
  | 0, prep, acc, _, hlt, hacc => by
    simp only [g1MsmWindows, Nat.pow_zero, one_nsmul]
    rw [msmPreparedSum_zero_of_lt_one M hlt, add_zero]
    exact ⟨hacc, rfl⟩
  | n + 1, prep, acc, hV, hlt, hacc => by
    unfold g1MsmWindows
    dsimp only
    obtain ⟨hnV, hnLt, hsV, hsplitSum⟩ := g1MsmSplit_sound M n hV hlt
    obtain ⟨hhiV, hhiG⟩ := g1MsmWindows_sound M n (g1MsmSplit prep).next acc hnV hnLt hacc
    obtain ⟨hdV, hdG⟩ := g1Double4_sound M hhiV
    obtain ⟨haddV, haddG⟩ := g1AddPoints_sound M (g1MsmSplit prep).selected
      (g1Double4 c (g1MsmWindows c n (g1MsmSplit prep).next acc)) hsV hdV
    refine ⟨haddV, ?_⟩
    rw [haddG, hdG, hhiG, smul_add, ← mul_nsmul, add_assoc, hsplitSum]
    have hpow : 16 ^ n * 16 = 16 ^ (n + 1) := (Nat.pow_succ 16 n).symm
    rw [hpow]

/-- **4-Bit Windowed Straus MSM Soundness (`g1Msm_sound`):**
For ANY curve with `0 < c.frMod < 2^256` (covering both BN254 `Fr` and BLS12-381 `Fr`) and ANY
group model `M : G1GroupModel c G`, whenever every term point satisfies `M.Valid`, the 64-window
MSM `g1Msm c terms` returns a valid point evaluating to the exact multi-scalar linear combination
`∑ (t.scalar % c.frMod) • M.toG t.point`. -/
theorem g1Msm_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) (hfrPos : 0 < c.frMod) (hfrLt : c.frMod < 2 ^ 256)
    {terms : G1TermList} (hvalid : g1TermListAllValid M terms) :
    M.Valid (g1Msm c terms) ∧ M.toG (g1Msm c terms) = g1TermSum M terms := by
  unfold g1Msm
  obtain ⟨hV, hLt, hSum⟩ := g1MsmPrepare_sound_pos M hfrPos hfrLt hvalid
  obtain ⟨hwV, hwG⟩ := g1MsmWindows_sound M 64 (g1MsmPrepare c terms) g1Inf hV hLt M.valid_inf
  refine ⟨hwV, ?_⟩
  rw [hwG, M.toG_inf, smul_zero, zero_add, hSum]

/-- Singleton-MSM specialization used by `KzgPackedPure.foldAccumulator`:
`g1Msm c (.cons { point := P, scalar := w } .nil)` evaluates to `(w % c.frMod) • M.toG P`. -/
theorem g1Msm_singleton_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) (hfrPos : 0 < c.frMod) (hfrLt : c.frMod < 2 ^ 256)
    {P : G1Point} (hP : M.Valid P) (w : Nat) :
    M.Valid (g1Msm c (.cons { point := P, scalar := w } .nil)) ∧
    M.toG (g1Msm c (.cons { point := P, scalar := w } .nil)) = (w % c.frMod) • M.toG P := by
  have h := g1Msm_sound M hfrPos hfrLt (terms := .cons { point := P, scalar := w } .nil) ⟨hP, trivial⟩
  simpa [g1TermSum] using h

theorem bn254CurveParams_frMod_bounds :
    0 < bn254CurveParams.frMod ∧ bn254CurveParams.frMod < 2 ^ 256 := by decide

theorem bls12381CurveParams_frMod_bounds :
    0 < bls12381CurveParams.frMod ∧ bls12381CurveParams.frMod < 2 ^ 256 := by decide

/-! ### 5.2 Packed SHPLONK Weighing & Opening Reduction Soundness (`verifyPacked_shplonk_sound`) -/

/-- Exact right-to-left Horner polynomial evaluation in `ZMod p`. -/
def hornerEval (p : Nat) : FList → ZMod p → ZMod p
  | .nil, _ => 0
  | .cons c rest, x => (c : ZMod p) + x * hornerEval p rest x

theorem polynomial_cast (p : Nat) (coeffs : FList) (z : Nat) :
    ((polynomial p coeffs z : Nat) : ZMod p) = hornerEval p coeffs (z : ZMod p) := by
  induction coeffs with
  | nil => simp [polynomial, hornerEval]
  | cons v rest ih =>
    simp only [polynomial, hornerEval, frAdd_cast, frMul_cast, ih]

private theorem frPowU32Fuel_cast (p : Nat) :
    ∀ (fuel base exp acc : Nat), exp < 2 ^ fuel →
      ((frPowU32Fuel p fuel base exp acc : Nat) : ZMod p) =
        (acc : ZMod p) * (base : ZMod p) ^ exp
  | 0, _, exp, acc, hlt => by
    have h0 : exp = 0 := by omega
    subst h0
    simp [frPowU32Fuel]
  | fuel + 1, base, exp, acc, hlt => by
    cases exp with
    | zero => simp [frPowU32Fuel]
    | succ e =>
      unfold frPowU32Fuel
      dsimp only
      have hhalf : (e + 1) / 2 < 2 ^ fuel := by
        have hpow : 2 ^ (fuel + 1) = 2 ^ fuel * 2 := Nat.pow_succ _ _
        omega
      have ih := frPowU32Fuel_cast p fuel (frMul p base base) ((e + 1) / 2)
        (if (e + 1) % 2 == 1 then frMul p acc base else acc) hhalf
      change ((frPowU32Fuel p fuel (frMul p base base) ((e + 1) / 2)
        (if (e + 1) % 2 == 1 then frMul p acc base else acc) : Nat) : ZMod p) = _
      rw [ih, frMul_cast]
      have hsq : ((base : ZMod p) * (base : ZMod p)) ^ ((e + 1) / 2) =
          (base : ZMod p) ^ (2 * ((e + 1) / 2)) := by
        rw [← sq, ← pow_mul]
      rw [hsq]
      by_cases hodd : ((e + 1) % 2 == 1) = true
      · have hmod : (e + 1) % 2 = 1 := beq_iff_eq.mp hodd
        have hdecomp : 2 * ((e + 1) / 2) + 1 = e + 1 := by omega
        simp only [hodd, ↓reduceIte, frMul_cast]
        rw [mul_assoc, ← pow_succ', show 2 * ((e + 1) / 2) + 1 = e + 1 from hdecomp]
      · have hmod : (e + 1) % 2 = 0 := by
          have hne : (e + 1) % 2 ≠ 1 := fun h => hodd (beq_iff_eq.mpr h)
          omega
        have hdecomp : 2 * ((e + 1) / 2) = e + 1 := by omega
        simp only [hodd, Bool.false_eq_true, ↓reduceIte, hdecomp]

/-- Exact soundness of `KzgPackedPure.frPowU32`: for any `exp < 2^32`,
`(frPowU32 p base exp : ZMod p) = (base : ZMod p) ^ exp`. -/
theorem frPowU32_sound (p base exp : Nat) (hexp : exp < 2 ^ 32) :
    ((frPowU32 p base exp : Nat) : ZMod p) = (base : ZMod p) ^ exp := by
  unfold frPowU32
  simpa using frPowU32Fuel_cast p 32 base exp 1 hexp

/-- **Single-Pack BDFG SHPLONK Weighing Soundness (`weighSinglePack_sound`):**
When `(weighSinglePack c log needNext current next z zeta power).1 = 1` (with `c.frMod` prime,
canonical `zeta < c.frMod`, and pack width `w = fListLen current < 2^32`):
1. The vanishing polynomial `Z_S(z)` is strictly non-zero in `ZMod c.frMod`:
   - for `needNext = 0`: `(z : ZMod p)^w ≠ (zeta : ZMod p)`,
   - for `needNext ≠ 0`: `(z : ZMod p)^w ≠ (zeta : ZMod p)` AND
     `(z : ZMod p)^w ≠ (zeta : ZMod p) * (twoAdicGen c log : ZMod p)`;
2. The constant-term contribution satisfies
   `(cTerm : ZMod p) = (weight : ZMod p) * (remainder : ZMod p)`, with `here = hornerEval p current z`
   and (when `needNext ≠ 0`) `nxtEval = hornerEval p next z`! -/
theorem weighSinglePack_sound {c : CurveParams} [Fact (Nat.Prime c.frMod)]
    {log needNext z zeta power : Nat} {current next : FList}
    (hzeta : zeta < c.frMod) (hw : fListLen current < 2 ^ 32)
    (h : (weighSinglePack c log needNext current next z zeta power).1 = 1) :
    let p := c.frMod
    let r := weighSinglePack c log needNext current next z zeta power
    (needNext = 0 →
      (z : ZMod p) ^ (fListLen current) ≠ (zeta : ZMod p) ∧
      ((r.2.2 : Nat) : ZMod p) = ((r.2.1 : Nat) : ZMod p) * hornerEval p current (z : ZMod p)) ∧
    (needNext ≠ 0 →
      (z : ZMod p) ^ (fListLen current) ≠ (zeta : ZMod p) ∧
      (z : ZMod p) ^ (fListLen current) ≠ (zeta : ZMod p) * (twoAdicGen c log : ZMod p)) := by
  have hpPos : 0 < c.frMod := (Fact.out : Nat.Prime c.frMod).pos
  have hyCast : ((frPowU32 c.frMod z (fListLen current) : Nat) : ZMod c.frMod) =
      (z : ZMod c.frMod) ^ (fListLen current) := frPowU32_sound c.frMod z (fListLen current) hw
  refine ⟨?_, ?_⟩
  · intro hnn0
    subst hnn0
    unfold weighSinglePack at h ⊢
    dsimp only at h ⊢
    simp only [beq_self_eq_true, ↓reduceIte] at h ⊢
    by_cases hzv : (frIsZero (frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta) == 1) = true
    · simp [hzv] at h
    simp only [hzv, Bool.false_eq_true, ↓reduceIte]
    have hvanNe : frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta ≠ 0 := by
      intro hz
      exact hzv (beq_iff_eq.mpr ((frIsZero_eq_one_iff _).mpr hz))
    have hvanLt : frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta < c.frMod :=
      frSub_lt hpPos _ _
    have hvanZ : ((frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta : Nat) : ZMod c.frMod) ≠ 0 := by
      intro hz
      have hdvd : c.frMod ∣ frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta :=
        (ZMod.natCast_eq_zero_iff _ _).mp hz
      exact hvanNe (Nat.eq_zero_of_dvd_of_lt hdvd hvanLt)
    rw [frSub_cast (Nat.le_of_lt hzeta), hyCast, sub_ne_zero] at hvanZ
    refine ⟨hvanZ, ?_⟩
    rw [frMul_cast, polynomial_cast]
  · intro hnnNe
    have hnnB : (needNext == 0) = false := beq_false_of_ne hnnNe
    unfold weighSinglePack at h
    dsimp only at h
    simp only [hnnB, Bool.false_eq_true, ↓reduceIte] at h
    by_cases hzv :
        (frIsZero (frMul c.frMod
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta)
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current))
            (frMul c.frMod zeta (twoAdicGen c log)))) == 1) = true
    · simp [hzv] at h
    have hvanNe :
        frMul c.frMod
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta)
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current))
            (frMul c.frMod zeta (twoAdicGen c log))) ≠ 0 := by
      intro hz
      exact hzv (beq_iff_eq.mpr ((frIsZero_eq_one_iff _).mpr hz))
    have hvanLt :
        frMul c.frMod
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta)
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current))
            (frMul c.frMod zeta (twoAdicGen c log))) < c.frMod := frMul_lt hpPos _ _
    have hvanZ :
        ((frMul c.frMod
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current)) zeta)
          (frSub c.frMod (frPowU32 c.frMod z (fListLen current))
            (frMul c.frMod zeta (twoAdicGen c log))) : Nat) : ZMod c.frMod) ≠ 0 := by
      intro hz
      have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hz
      exact hvanNe (Nat.eq_zero_of_dvd_of_lt hdvd hvanLt)
    have hafterLt : frMul c.frMod zeta (twoAdicGen c log) < c.frMod := frMul_lt hpPos _ _
    rw [frMul_cast, frSub_cast (Nat.le_of_lt hzeta), frSub_cast (Nat.le_of_lt hafterLt),
      frMul_cast, hyCast] at hvanZ
    have hne1 : (z : ZMod c.frMod) ^ fListLen current - (zeta : ZMod c.frMod) ≠ 0 :=
      left_ne_zero_of_mul hvanZ
    have hne2 : (z : ZMod c.frMod) ^ fListLen current -
        (zeta : ZMod c.frMod) * (twoAdicGen c log : ZMod c.frMod) ≠ 0 :=
      right_ne_zero_of_mul hvanZ
    exact ⟨sub_ne_zero.mp hne1, sub_ne_zero.mp hne2⟩

/-! #### `g1ValidPoint` Propagation Across `buildPcsRounds → roundPacks → weighPacks → reducePcs` -/

private def packGroupsValid (c : CurveParams) : PackGroupList → Prop
  | .nil => True
  | .cons g rest => g1ValidPoint c g.point = true ∧ packGroupsValid c rest

private def shplonkPacksValid (c : CurveParams) : ShplonkPackList → Prop
  | .nil => True
  | .cons pk rest => g1ValidPoint c pk.point = true ∧ shplonkPacksValid c rest

private def pcsRoundsValid (c : CurveParams) : PcsRoundList → Prop
  | .nil => True
  | .cons rd rest => g1PointListValid c rd.comm.points = true ∧ pcsRoundsValid c rest

private def g1TermsValidPoint (c : CurveParams) : G1TermList → Prop
  | .nil => True
  | .cons t rest => g1ValidPoint c t.point = true ∧ g1TermsValidPoint c rest

private theorem packGroupsValid_append {c : CurveParams} :
    ∀ {a b : PackGroupList}, packGroupsValid c a → packGroupsValid c b →
      packGroupsValid c (packGroupAppend a b)
  | .nil, _, _, hb => hb
  | .cons _ _, _, ⟨ha, hat⟩, hb => ⟨ha, packGroupsValid_append hat hb⟩

private theorem shplonkPacksValid_append {c : CurveParams} :
    ∀ {a b : ShplonkPackList}, shplonkPacksValid c a → shplonkPacksValid c b →
      shplonkPacksValid c (shplonkPackAppend a b)
  | .nil, _, _, hb => hb
  | .cons _ _, _, ⟨ha, hat⟩, hb => ⟨ha, shplonkPacksValid_append hat hb⟩

private theorem groupsAtLogFuel_valid (c : CurveParams) :
    ∀ (fuel : Nat) (cols : PackColList) (pts : G1PointList) (log cap : Nat),
      g1PointListValid c pts = true →
      (groupsAtLogFuel cols pts log cap fuel).1 = 1 →
      packGroupsValid c (groupsAtLogFuel cols pts log cap fuel).2.1 ∧
      g1PointListValid c (groupsAtLogFuel cols pts log cap fuel).2.2 = true
  | 0, .nil, pts, _, _, hpts, _ => ⟨trivial, hpts⟩
  | 0, .cons _ _, _, _, _, _, h => by simp [groupsAtLogFuel] at h
  | fuel + 1, .nil, pts, _, _, hpts, _ => ⟨trivial, hpts⟩
  | fuel + 1, .cons col restC, .nil, _, _, _, h => by simp [groupsAtLogFuel] at h
  | fuel + 1, .cons col restC, .cons pt restPts, log, cap, hpts, h => by
    simp only [g1PointListValid, Bool.and_eq_true] at hpts
    unfold groupsAtLogFuel at h ⊢
    dsimp only at h ⊢
    split_ifs at h with hsub
    have hsubEq : (groupsAtLogFuel (splitPackCols (.cons col restC) cap).2 restPts log cap fuel).1 = 1 :=
      beq_iff_eq.mp hsub
    obtain ⟨hg, hrem⟩ := groupsAtLogFuel_valid c fuel _ restPts log cap hpts.2 hsubEq
    simp only [hsub, ↓reduceIte]
    exact ⟨⟨hpts.1, hg⟩, hrem⟩

private theorem walkGroupsFuel_valid (c : CurveParams) :
    ∀ (fuel : Nat) (mats : RoundMatrixList) (shapes : MatrixShapeList) (pts : G1PointList)
      (log maxLog : Nat),
      g1PointListValid c pts = true →
      (walkGroupsFuel mats shapes pts log maxLog fuel).1 = 1 →
      packGroupsValid c (walkGroupsFuel mats shapes pts log maxLog fuel).2
  | 0, _, _, _, _, _, _, h => by simp [walkGroupsFuel] at h
  | fuel + 1, mats, shapes, pts, log, maxLog, hpts, h => by
    unfold walkGroupsFuel at h ⊢
    dsimp only at h ⊢
    set cap := power2Nat (maxLog - log)
    set cN := columnsAt mats shapes log 1
    set cC := columnsAt mats shapes log 0
    by_cases hcol : (cN.1 == 0 || cC.1 == 0) = true
    · simp [hcol] at h
    simp only [hcol, Bool.false_eq_true, ↓reduceIte] at h ⊢
    set g1 := groupsAtLogFuel cN.2 pts log cap (packColLen cN.2 + 1)
    set g2 := groupsAtLogFuel cC.2 g1.2.2 log cap (packColLen cC.2 + 1)
    by_cases hgrp : (g1.1 == 0 || g2.1 == 0) = true
    · simp [hgrp] at h
    simp only [hgrp, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hg1Ok : g1.1 = 1 := by
      have h01 : ∀ fuel' cols' pts' log' cap',
          (groupsAtLogFuel cols' pts' log' cap' fuel').1 = 0 ∨
          (groupsAtLogFuel cols' pts' log' cap' fuel').1 = 1 := by
        intro f'; induction f' with
        | zero => intro cs ps _ _; cases cs <;> simp [groupsAtLogFuel]
        | succ f' ih =>
          intro cs ps lg cp; cases cs with
          | nil => exact Or.inr rfl
          | cons _ _ =>
            cases ps with
            | nil => exact Or.inl rfl
            | cons _ _ =>
              unfold groupsAtLogFuel; dsimp only; split_ifs <;> simp
      rcases h01 (packColLen cN.2 + 1) cN.2 pts log cap with h0 | h1
      · exfalso; exact hgrp (by simp [g1, h0])
      · exact h1
    have hg2Ok : g2.1 = 1 := by
      have h01 : ∀ fuel' cols' pts' log' cap',
          (groupsAtLogFuel cols' pts' log' cap' fuel').1 = 0 ∨
          (groupsAtLogFuel cols' pts' log' cap' fuel').1 = 1 := by
        intro f'; induction f' with
        | zero => intro cs ps _ _; cases cs <;> simp [groupsAtLogFuel]
        | succ f' ih =>
          intro cs ps lg cp; cases cs with
          | nil => exact Or.inr rfl
          | cons _ _ =>
            cases ps with
            | nil => exact Or.inl rfl
            | cons _ _ =>
              unfold groupsAtLogFuel; dsimp only; split_ifs <;> simp
      rcases h01 (packColLen cC.2 + 1) cC.2 g1.2.2 log cap with h0 | h1
      · exfalso; exact hgrp (by simp [g2, h0])
      · exact h1
    obtain ⟨hv1, hpts1⟩ := groupsAtLogFuel_valid c (packColLen cN.2 + 1) cN.2 pts log cap hpts hg1Ok
    obtain ⟨hv2, hpts2⟩ := groupsAtLogFuel_valid c (packColLen cC.2 + 1) cC.2 g1.2.2 log cap hpts1 hg2Ok
    have hhd : packGroupsValid c (packGroupAppend g1.2.1 g2.2.1) := packGroupsValid_append hv1 hv2
    by_cases hlast : (log == maxLog) = true
    · simp only [hlast, ↓reduceIte] at h ⊢
      cases hrem : g2.2.2 with
      | nil => exact hhd
      | cons _ _ => simp [hrem] at h
    · simp only [hlast, Bool.false_eq_true, ↓reduceIte] at h ⊢
      split_ifs at h with htl
      simp only [htl, ↓reduceIte]
      exact packGroupsValid_append hhd
        (walkGroupsFuel_valid c fuel mats shapes g2.2.2 (log + 1) maxLog hpts2 (beq_iff_eq.mp htl))

private theorem groupPacks_valid (c : CurveParams) :
    ∀ (tr : KzgTranscript) (groups : PackGroupList) (extras : FList),
      packGroupsValid c groups →
      (groupPacks tr groups extras).ok = 1 →
      shplonkPacksValid c (groupPacks tr groups extras).packs
  | _, .nil, _, _, _ => trivial
  | tr, .cons grp rest, extras, ⟨hgV, hrestV⟩, h => by
    unfold groupPacks at h ⊢
    dsimp only at h ⊢
    set needNext := if packHasNext grp.cols == 1 && grp.log != 0 then 1 else 0
    set ev := extractPackValues grp.cols extras needNext
    by_cases hev : (ev.ok == 0) = true
    · simp [hev] at h
    simp only [hev, Bool.false_eq_true, ↓reduceIte] at h ⊢
    split_ifs at h with hsub
    simp only [hsub, ↓reduceIte]
    exact ⟨hgV, groupPacks_valid c _ rest ev.restExtras hrestV (beq_iff_eq.mp hsub)⟩

private theorem roundPacks_valid (c : CurveParams) :
    ∀ (tr : KzgTranscript) (rounds : PcsRoundList) (extras : FList) (maxLog : Nat),
      pcsRoundsValid c rounds →
      (roundPacks tr rounds extras maxLog).ok = 1 →
      shplonkPacksValid c (roundPacks tr rounds extras maxLog).packs
  | _, .nil, .nil, _, _, _ => trivial
  | _, .nil, .cons _ _, _, _, h => by simp [roundPacks] at h
  | tr, .cons rd rest, extras, maxLog, ⟨hrdV, hrestV⟩, h => by
    unfold roundPacks at h ⊢
    dsimp only at h ⊢
    set wg := walkGroupsFuel rd.matrices rd.comm.shapes rd.comm.points 0 maxLog (maxLog + 1)
    by_cases hwg : (wg.1 == 0) = true
    · simp [hwg] at h
    simp only [hwg, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hwg1 : wg.1 = 1 := by
      have h01 : ∀ fuel' ms' sh' ps' lg' ml',
          (walkGroupsFuel ms' sh' ps' lg' ml' fuel').1 = 0 ∨
          (walkGroupsFuel ms' sh' ps' lg' ml' fuel').1 = 1 := by
        intro f'; induction f' with
        | zero => intro _ _ _ _ _; exact Or.inl rfl
        | succ f' ih =>
          intro ms' sh' ps' lg' ml'
          unfold walkGroupsFuel; dsimp only
          by_cases h1 : ((columnsAt ms' sh' lg' 1).1 == 0 || (columnsAt ms' sh' lg' 0).1 == 0) = true
          · simp [h1]
          simp only [h1, Bool.false_eq_true, ↓reduceIte]
          by_cases h2 : ((groupsAtLogFuel (columnsAt ms' sh' lg' 1).2 ps' lg' (power2Nat (ml' - lg'))
              (packColLen (columnsAt ms' sh' lg' 1).2 + 1)).1 == 0 ||
              (groupsAtLogFuel (columnsAt ms' sh' lg' 0).2
                (groupsAtLogFuel (columnsAt ms' sh' lg' 1).2 ps' lg' (power2Nat (ml' - lg'))
                  (packColLen (columnsAt ms' sh' lg' 1).2 + 1)).2.2 lg' (power2Nat (ml' - lg'))
                (packColLen (columnsAt ms' sh' lg' 0).2 + 1)).1 == 0) = true
          · simp [h2]
          simp only [h2, Bool.false_eq_true, ↓reduceIte]
          by_cases h3 : (lg' == ml') = true
          · simp only [h3, ↓reduceIte]
            cases (groupsAtLogFuel (columnsAt ms' sh' lg' 0).2
              (groupsAtLogFuel (columnsAt ms' sh' lg' 1).2 ps' lg' (power2Nat (ml' - lg'))
                (packColLen (columnsAt ms' sh' lg' 1).2 + 1)).2.2 lg' (power2Nat (ml' - lg'))
              (packColLen (columnsAt ms' sh' lg' 0).2 + 1)).2.2 <;> simp
          · simp only [h3, Bool.false_eq_true, ↓reduceIte]
            split_ifs <;> simp
      rcases h01 (maxLog + 1) rd.matrices rd.comm.shapes rd.comm.points 0 maxLog with h0 | h1
      · exfalso; exact hwg (by simp [wg, h0])
      · exact h1
    have hgrpsV : packGroupsValid c wg.2 := walkGroupsFuel_valid c (maxLog + 1) _ _ _ 0 maxLog hrdV hwg1
    set gp := groupPacks tr wg.2 extras
    by_cases hgp : (gp.ok == 0) = true
    · simp [hgp] at h
    simp only [hgp, Bool.false_eq_true, ↓reduceIte] at h ⊢
    have hgp1 : gp.ok = 1 := by
      have h01 : ∀ tr' gs' ex', (groupPacks tr' gs' ex').ok = 0 ∨ (groupPacks tr' gs' ex').ok = 1 := by
        intro tr' gs'; induction gs' generalizing tr' with
        | nil => intro _; exact Or.inr rfl
        | cons _ _ ih =>
          intro ex'; unfold groupPacks; dsimp only; split_ifs <;> simp
      rcases h01 tr wg.2 extras with h0 | h1
      · exfalso; exact hgp (by simp [gp, h0])
      · exact h1
    have hgpV : shplonkPacksValid c gp.packs := groupPacks_valid c tr wg.2 extras hgrpsV hgp1
    split_ifs at h with hsub
    simp only [hsub, ↓reduceIte]
    exact shplonkPacksValid_append hgpV
      (roundPacks_valid c gp.transcript rest gp.restExtras maxLog hrestV (beq_iff_eq.mp hsub))

private theorem buildPcsRounds_valid {c : CurveParams} (frames : PackedFrameList)
    {main stage2 quotient : PackedCommitment} {fixed : PackedFixed}
    (hm : g1PointListValid c main.points = true)
    (hs : g1PointListValid c stage2.points = true)
    (hq : g1PointListValid c quotient.points = true)
    (hf : fixedPointsValid c fixed = true) :
    pcsRoundsValid c (buildPcsRounds frames main stage2 quotient fixed) := by
  unfold buildPcsRounds
  cases fixed with
  | none => exact ⟨hm, hs, hq, trivial⟩
  | some fx => exact ⟨hm, hs, hq, hf, trivial⟩
  | shared fx slots => exact ⟨hm, hs, hq, hf, trivial⟩

private theorem weighPacks_valid (c : CurveParams) :
    ∀ (packs : ShplonkPackList) (gamma z zeta power constant : Nat) (terms : G1TermList),
      shplonkPacksValid c packs → g1TermsValidPoint c terms →
      (weighPacks c packs gamma z zeta power constant terms).ok = 1 →
      g1TermsValidPoint c (weighPacks c packs gamma z zeta power constant terms).terms
  | .nil, _, _, _, _, _, terms, _, hterms, _ => hterms
  | .cons pk rest, gamma, z, zeta, power, constant, terms, ⟨hpkV, hrestV⟩, hterms, h => by
    unfold weighPacks at h ⊢
    dsimp only at h ⊢
    by_cases hok : ((weighSinglePack c pk.log pk.needNext pk.current pk.next z zeta power).1 == 0) = true
    · simp [hok] at h
    simp only [hok, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact weighPacks_valid c rest gamma z zeta _ _ _ hrestV ⟨hpkV, hterms⟩ h

private theorem g1TermListAllValid_of_validPoint {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) (hvalid : ∀ P, g1ValidPoint c P = true → M.Valid P) :
    ∀ {terms : G1TermList}, g1TermsValidPoint c terms → g1TermListAllValid M terms
  | .nil, _ => trivial
  | .cons _ _, ⟨ht, hrest⟩ => ⟨hvalid _ ht, g1TermListAllValid_of_validPoint M hvalid hrest⟩

/-- **Packed SHPLONK Opening Reduction Soundness (`reducePcs_shplonk_sound`):**
When `(reducePcs c tr rounds extras w1 w2 zeta generator maxLog).ok = 1` over any group model `M`
validating `g1ValidPoint` points (with `0 < c.frMod < 2^256`):
1. Both deferred pairing outputs `(res.a, res.b)` satisfy `M.Valid`;
2. Every MSM term point in `wg.terms` passes `g1ValidPoint`;
3. `(M.toG res.a, M.toG res.b)` satisfies the exact BDFG SHPLONK deferred accumulator equations:
   - `M.toG res.a = (frNeg c.frMod wg.constant % c.frMod) • M.toG generator + (z % c.frMod) • M.toG w2.point + g1TermSum M wg.terms - M.toG w1.point`
   - `M.toG res.b = -M.toG w2.point`! -/
theorem reducePcs_shplonk_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) (hvalid : ∀ P, g1ValidPoint c P = true → M.Valid P)
    (hfrPos : 0 < c.frMod) (hfrLt : c.frMod < 2 ^ 256)
    {tr : KzgTranscript} {rounds : PcsRoundList} {extras : FList}
    {w1 w2 : PackedWitness} {zeta : Nat} {generator : G1Point} {maxLog : Nat}
    (hrounds : pcsRoundsValid c rounds)
    (hgen : g1ValidPoint c generator = true)
    (hw1 : g1ValidPoint c w1.point = true)
    (hw2 : g1ValidPoint c w2.point = true)
    (h : (reducePcs c tr rounds extras w1 w2 zeta generator maxLog).ok = 1) :
    let res := reducePcs c tr rounds extras w1 w2 zeta generator maxLog
    M.Valid res.a ∧ M.Valid res.b ∧
    ∃ (wg : WeighResult) (z : Nat),
      wg.ok = 1 ∧
      g1TermsValidPoint c wg.terms ∧
      M.toG res.a =
        (frNeg c.frMod wg.constant % c.frMod) • M.toG generator +
        (z % c.frMod) • M.toG w2.point +
        g1TermSum M wg.terms - M.toG w1.point ∧
      M.toG res.b = -M.toG w2.point := by
  unfold reducePcs at h ⊢
  dsimp only at h ⊢
  set tr1 := transcriptObserveBytes tr openDomainBytes
  set tr2 := transcriptObserveU64 tr1 (pcsRoundLen rounds)
  set tr3 := observeRounds c tr2 rounds zeta
  set rp := roundPacks tr3 rounds extras maxLog
  by_cases hrp : (rp.ok == 0) = true
  · simp [hrp] at h
  simp only [hrp, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have hrp1 : rp.ok = 1 := by
    have h01 : ∀ tr' rds' ex' ml', (roundPacks tr' rds' ex' ml').ok = 0 ∨ (roundPacks tr' rds' ex' ml').ok = 1 := by
      intro tr' rds'; induction rds' generalizing tr' with
      | nil => intro ex' _; cases ex' <;> simp [roundPacks]
      | cons _ _ ih => intro ex' ml'; unfold roundPacks; dsimp only; split_ifs <;> simp
    rcases h01 tr3 rounds extras maxLog with h0 | h1
    · exfalso; exact hrp (by simp [rp, h0])
    · exact h1
  have hpacksV : shplonkPacksValid c rp.packs := roundPacks_valid c tr3 rounds extras maxLog hrounds hrp1
  set tr4 := transcriptObserveBytes rp.transcript batchDomainBytes
  set sGamma := transcriptSampleFr c tr4
  set tr5 := transcriptObserveBytes sGamma.transcript w1.rawBytes
  set sZ := transcriptSampleFr c tr5
  set tr6 := transcriptObserveBytes sZ.transcript w2.rawBytes
  set wg := weighPacks c rp.packs sGamma.challenge sZ.challenge zeta 1 0 .nil
  by_cases hwg : (wg.ok == 0) = true
  · simp [hwg] at h
  simp only [hwg, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have hwg1 : wg.ok = 1 := by
    have h01 : ∀ pks' gm' zz' zt' pw' cn' tms',
        (weighPacks c pks' gm' zz' zt' pw' cn' tms').ok = 0 ∨
        (weighPacks c pks' gm' zz' zt' pw' cn' tms').ok = 1 := by
      intro pks'; induction pks' with
      | nil => intro _ _ _ _ _ _; exact Or.inr rfl
      | cons _ _ ih =>
        intro gm' zz' zt' pw' cn' tms'
        unfold weighPacks; dsimp only
        split_ifs
        · exact Or.inl rfl
        · exact ih _ _ _ _ _ _
    rcases h01 rp.packs sGamma.challenge sZ.challenge zeta 1 0 .nil with h0 | h1
    · exfalso; exact hwg (by simp [wg, h0])
    · exact h1
  have hwgTermsV : g1TermsValidPoint c wg.terms :=
    weighPacks_valid c rp.packs sGamma.challenge sZ.challenge zeta 1 0 .nil hpacksV trivial hwg1
  have hallTermsV : g1TermListAllValid M
      (.cons { point := generator, scalar := frNeg c.frMod wg.constant }
        (.cons { point := w2.point, scalar := sZ.challenge } wg.terms)) :=
    ⟨hvalid _ hgen, hvalid _ hw2, g1TermListAllValid_of_validPoint M hvalid hwgTermsV⟩
  obtain ⟨hmsmV, hmsmG⟩ := g1Msm_sound M hfrPos hfrLt hallTermsV
  have hnegW1V : M.Valid (g1Neg c w1.point) := M.valid_neg (hvalid _ hw1)
  have haV : M.Valid (g1Add c (g1Msm c (.cons { point := generator, scalar := frNeg c.frMod wg.constant }
      (.cons { point := w2.point, scalar := sZ.challenge } wg.terms))) (g1Neg c w1.point)) :=
    M.valid_add hmsmV hnegW1V
  have hbV : M.Valid (g1Neg c w2.point) := M.valid_neg (hvalid _ hw2)
  refine ⟨haV, hbV, wg, sZ.challenge, hwg1, hwgTermsV, ?_, ?_⟩
  · rw [M.toG_add hmsmV hnegW1V, hmsmG, M.toG_neg (hvalid _ hw1)]
    simp only [g1TermSum]
    abel
  · exact M.toG_neg (hvalid _ hw2)

/-- **Full `KzgPackedPure.verifyPacked` SHPLONK Opening & Key-Binding Soundness
(`verifyPacked_shplonk_sound`):**
Whenever `(verifyPacked c key proof claims).ok = 1` (for any curve with `0 < c.frMod < 2^256` and
any group model `M : G1GroupModel c G` validating `g1ValidPoint` points):
1. Both key-binding (`seedBindsPackedKey = 1`) and full `G1` point validation (generator, fixed
   commitments, proof commitments, witnesses) hold;
2. Both deferred pairing outputs `(vr.a, vr.b)` satisfy `M.Valid`;
3. `(M.toG vr.a, M.toG vr.b)` equals the exact BDFG SHPLONK deferred pairing accumulator:
   - `M.toG vr.a = (-wg.constant) • G + z • W₂ + ∑ w_i • C_i - W₁`,
   - `M.toG vr.b = -W₂`,
   so in any bilinear pairing `e(vr.a, [1]₂) · e(vr.b, [τ]₂) = 1` holds iff
   `e(∑ w_i • C_i - wg.constant • G + z • W₂ - W₁, [1]₂) = e(W₂, [τ]₂)`! -/
theorem verifyPacked_shplonk_sound {c : CurveParams} {G : Type*} [AddCommGroup G]
    (M : G1GroupModel c G) (hvalid : ∀ P, g1ValidPoint c P = true → M.Valid P)
    (hfrPos : 0 < c.frMod) (hfrLt : c.frMod < 2 ^ 256)
    {key : PackedKey} {proof : PackedProof} {claims : FListList}
    (h : (verifyPacked c key proof claims).ok = 1) :
    let vr := verifyPacked c key proof claims
    seedBindsPackedKey c key.seed key.circuits key.fixed = 1 ∧
    M.Valid vr.a ∧ M.Valid vr.b ∧
    ∃ (wg : WeighResult) (z : Nat),
      wg.ok = 1 ∧
      g1TermsValidPoint c wg.terms ∧
      M.toG vr.a =
        (frNeg c.frMod wg.constant % c.frMod) • M.toG key.generator +
        (z % c.frMod) • M.toG proof.w2.point +
        g1TermSum M wg.terms - M.toG proof.w1.point ∧
      M.toG vr.b = -M.toG proof.w2.point := by
  have hkb := verifyPacked_key_binding_sound h
  obtain ⟨hseed1, _, hgen, hfix, hmain, hs2, hquot, hw1, hw2, _, _, _⟩ := hkb
  unfold verifyPacked at h ⊢
  dsimp only at h ⊢
  have hseedNe0 : (seedBindsPackedKey c key.seed key.circuits key.fixed == 0) = false := by
    rw [hseed1]; rfl
  have hptsOk : (!g1ValidPoint c key.generator || !fixedPointsValid c key.fixed ||
      !g1PointListValid c proof.main.points || !g1PointListValid c proof.stage2.points ||
      !g1PointListValid c proof.quotient.points || !g1ValidPoint c proof.w1.point ||
      !g1ValidPoint c proof.w2.point) = false := by
    simp [hgen, hfix, hmain, hs2, hquot, hw1, hw2]
  simp only [hseedNe0, hptsOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set bf := buildFrames c key proof
  by_cases hbf : (bf.ok == 0) = true; · simp [hbf] at h
  simp only [hbf, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set tr0 := observeKey key.seed key.circuits proof.active key.fixed
  set tr1 := transcriptObserveBytes tr0 proof.main.rawBytes
  set tr2 := transcriptObserveFields tr1 proof.logs
  set tr3 := transcriptObserveClaims tr2 claims
  set sBeta := transcriptSampleFr c tr3
  set tr4 := transcriptObserveField sBeta.transcript sBeta.challenge
  set sGamma := transcriptSampleFr c tr4
  set tr5 := transcriptObserveField sGamma.transcript sGamma.challenge
  set initial := claimsAccumulator c.frMod claims sBeta.challenge sGamma.challenge
  set tr6 := transcriptObserveBytes tr5 proof.stage2.rawBytes
  set tr7 := transcriptObserveFields tr6 proof.accumulators
  set sAlpha := transcriptSampleFr c tr7
  set tr8 := transcriptObserveBytes sAlpha.transcript proof.quotient.rawBytes
  set sZeta := transcriptSampleFr c tr8
  by_cases hzeta : (frIsZero sZeta.challenge == 1) = true; · simp [hzeta] at h
  simp only [hzeta, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set framesOk := verifyFrames c bf.frames
    sBeta.challenge sGamma.challenge sAlpha.challenge sZeta.challenge initial
  by_cases hfrOk : (framesOk == 0) = true; · simp [hfrOk] at h
  simp only [hfrOk, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have hrounds := buildPcsRounds_valid bf.frames hmain hs2 hquot hfix
  obtain ⟨haV, hbV, hshplonk⟩ :=
    reducePcs_shplonk_sound M hvalid hfrPos hfrLt hrounds hgen hw1 hw2 h
  exact ⟨hseed1, haV, hbV, hshplonk⟩

/-! ### 5.3 Statement Limbs, Canonical Affine `u80` Words, Fold & Two-Stage `DeferredFold` Bridge -/

/-- Convert a `DigestWords` into an 8-element `List Nat`. -/
def digestWordsToList (d : DigestWords) : List Nat :=
  [d.d0, d.d1, d.d2, d.d3, d.d4, d.d5, d.d6, d.d7]

/-- Convert an `FList` into a `List Nat`. -/
def fListToList : FList → List Nat
  | .nil => []
  | .cons h t => h :: fListToList t

theorem fListToList_append (a b : FList) :
    fListToList (fListAppend a b) = fListToList a ++ fListToList b := by
  induction a with
  | nil => rfl
  | cons h t ih => simp [fListAppend, fListToList, ih]

theorem fListToList_length (xs : FList) : (fListToList xs).length = fListLen xs := by
  induction xs with
  | nil => rfl
  | cons _ t ih => simp [fListToList, fListLen, ih]

private theorem natToLeBytes_add : ∀ (m n x : Nat),
    natToLeBytes (m + n) x = byteAppend (natToLeBytes m x) (natToLeBytes n (x / 256 ^ m))
  | 0, n, x => by simp [natToLeBytes]
  | m + 1, n, x => by
    rw [Nat.succ_add]
    simp only [natToLeBytes, byteAppend]
    rw [natToLeBytes_add m n (x / 256), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

private theorem readU32_natToLeBytes_4 (x : Nat) (rest : ByteList) :
    readU32 (byteAppend (natToLeBytes 4 x) rest) =
      { ok := 1, val := x % 2 ^ 32, rest := rest } := by
  have h0 : x % 256 < 256 := Nat.mod_lt _ (by decide)
  have h1 : x / 256 % 256 < 256 := Nat.mod_lt _ (by decide)
  have h2 : x / 256 / 256 % 256 < 256 := Nat.mod_lt _ (by decide)
  have h3 : x / 256 / 256 / 256 % 256 < 256 := Nat.mod_lt _ (by decide)
  have hd2 : x / 256 / 256 = x / 65536 := Nat.div_div_eq_div_mul x 256 256
  have hd3 : x / 256 / 256 / 256 = x / 16777216 := by
    rw [hd2, Nat.div_div_eq_div_mul]
  simp only [natToLeBytes, byteAppend, readU32, h0, h1, h2, h3, decide_true, Bool.and_self,
    ↓reduceIte, ParseNat.mk.injEq, true_and, and_true]
  rw [hd3, hd2]
  omega

/-- **Exact Bridge (`statementFromLimbs_eq_unpack`):**
`KzgPackedPure.statementFromLimbs low high` accepts iff `low < 2^128 ∧ high < 2^128`, producing
canonical `u32` words identical to `Ix.Cert.AiurCompression.unpackLimbsToU32Words low high`! -/
theorem statementFromLimbs_eq_unpack {low high : Nat}
    (h : (statementFromLimbs low high).1 = 1) :
    low < 2 ^ 128 ∧ high < 2 ^ 128 ∧
    digestWordsCanonical (statementFromLimbs low high).2 = 1 ∧
    digestWordsToList (statementFromLimbs low high).2 = unpackLimbsToU32Words low high := by
  unfold statementFromLimbs at h ⊢
  dsimp only at h ⊢
  by_cases hlt : (decide (low < radix128) && decide (high < radix128)) = true
  swap; · simp [hlt] at h
  simp only [hlt, ↓reduceIte]
  have hlt' := hlt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt'
  have hrad : radix128 = 2 ^ 128 := by decide
  rw [hrad] at hlt'
  have hsplit : ∀ x : Nat,
      natToLeBytes 16 x =
        byteAppend (natToLeBytes 4 x)
        (byteAppend (natToLeBytes 4 (x / 2 ^ 32))
        (byteAppend (natToLeBytes 4 (x / 2 ^ 64))
          (natToLeBytes 4 (x / 2 ^ 96)))) := by
    intro x
    have h1 := natToLeBytes_add 4 12 x
    have h2 := natToLeBytes_add 4 8 (x / 2 ^ 32)
    have h3 := natToLeBytes_add 4 4 (x / 2 ^ 64)
    have p4 : (256 : Nat) ^ 4 = 2 ^ 32 := by decide
    rw [p4] at h1 h2 h3
    rw [h1, h2, Nat.div_div_eq_div_mul, show (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 from by decide,
      h3, Nat.div_div_eq_div_mul, show (2 : Nat) ^ 64 * 2 ^ 32 = 2 ^ 96 from by decide]
  have hrd : readDigestWords (byteAppend (natToLeBytes 16 low) (natToLeBytes 16 high)) =
      { ok := 1
        digest :=
          { d0 := low % 2 ^ 32, d1 := (low / 2 ^ 32) % 2 ^ 32
            d2 := (low / 2 ^ 64) % 2 ^ 32, d3 := (low / 2 ^ 96) % 2 ^ 32
            d4 := high % 2 ^ 32, d5 := (high / 2 ^ 32) % 2 ^ 32
            d6 := (high / 2 ^ 64) % 2 ^ 32, d7 := (high / 2 ^ 96) % 2 ^ 32 }
        rest := .nil } := by
    rw [hsplit low, hsplit high]
    unfold readDigestWords
    simp only [byteAppend_assoc]
    have hnil : natToLeBytes 4 (high / 2 ^ 96) = byteAppend (natToLeBytes 4 (high / 2 ^ 96)) .nil := by
      rw [byteAppend_nil_right]
    rw [hnil]
    simp only [readU32_natToLeBytes_4, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  rw [hrd]
  refine ⟨hlt'.1, hlt'.2, ?_, rfl⟩
  exact (digestWordsCanonical_eq_one_iff _).mpr
    ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide),
     Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩

/-! #### Canonical Affine `u80` Point & Pair Word Encoding Soundness (`18` BN254 / `22` BLS12-381) -/

private theorem ofLimbsGeneric_toLimbsGeneric (r : Nat) (hr : 0 < r) :
    ∀ (n x : Nat), x < r ^ n → ofLimbsGeneric r (toLimbsGeneric r n x) = x
  | 0, x, hx => by
    have h0 : x = 0 := by simp at hx; omega
    subst h0; rfl
  | n + 1, x, hx => by
    simp only [toLimbsGeneric, ofLimbsGeneric]
    have hdivLt : x / r < r ^ n := by
      have hpow : r ^ (n + 1) = r ^ n * r := Nat.pow_succ _ _
      rw [hpow, Nat.mul_comm] at hx
      exact Nat.div_lt_of_lt_mul hx
    rw [ofLimbsGeneric_toLimbsGeneric r hr n (x / r) hdivLt, Nat.mod_add_div]

private theorem fListTake_append_left : ∀ (a b : FList), fListTake (fListAppend a b) (fListLen a) = a
  | .nil, _ => rfl
  | .cons h t, b => by
    simp only [fListAppend, fListLen, fListTake]
    rw [fListTake_append_left t b]

private theorem fListDrop_append_left : ∀ (a b : FList), fListDrop (fListAppend a b) (fListLen a) = b
  | .nil, _ => rfl
  | .cons _ t, b => by
    simp only [fListAppend, fListLen, fListDrop]
    exact fListDrop_append_left t b

theorem decodeAffinePointWords_encodeAffinePointWords {c : CurveParams}
    (hr : 0 < c.limbRadix) {P : G1Point}
    (hx : P.x < c.limbRadix ^ c.fqLimbCount) (hy : P.y < c.limbRadix ^ c.fqLimbCount) :
    decodeAffinePointWords c (encodeAffinePointWords c P) = P := by
  unfold decodeAffinePointWords encodeAffinePointWords
  dsimp only
  have hlenX : fListLen (toLimbsGeneric c.limbRadix c.fqLimbCount P.x) = c.fqLimbCount :=
    fListLen_toLimbsGeneric c.limbRadix c.fqLimbCount P.x
  have hlenY : fListLen (toLimbsGeneric c.limbRadix c.fqLimbCount P.y) = c.fqLimbCount :=
    fListLen_toLimbsGeneric c.limbRadix c.fqLimbCount P.y
  have htx := hlenX ▸ fListTake_append_left (toLimbsGeneric c.limbRadix c.fqLimbCount P.x)
    (fListAppend (toLimbsGeneric c.limbRadix c.fqLimbCount P.y) (.cons P.isInf .nil))
  have hdx := hlenX ▸ fListDrop_append_left (toLimbsGeneric c.limbRadix c.fqLimbCount P.x)
    (fListAppend (toLimbsGeneric c.limbRadix c.fqLimbCount P.y) (.cons P.isInf .nil))
  have hty := hlenY ▸ fListTake_append_left (toLimbsGeneric c.limbRadix c.fqLimbCount P.y)
    (.cons P.isInf .nil)
  have hdy := hlenY ▸ fListDrop_append_left (toLimbsGeneric c.limbRadix c.fqLimbCount P.y)
    (.cons P.isInf .nil)
  rw [htx, hdx, hty, hdy]
  rw [ofLimbsGeneric_toLimbsGeneric c.limbRadix hr c.fqLimbCount P.x hx,
      ofLimbsGeneric_toLimbsGeneric c.limbRadix hr c.fqLimbCount P.y hy]

set_option exponentiation.threshold 512 in
/-- **BN254 Canonical 18-Word `affine-u80-v1` Soundness & `DeferredFold` Bridge
(`encodeAffinePairWords_bn254_sound`):**
For any validated BN254 pair `(A, B)`:
1. `fListLen (encodeAffinePairWords bn254CurveParams A B) = 18` (`= aiurTerminalOutputsBN254`);
2. Both `A` and `B` have canonical `< bn254FqModulus` coordinates and strict `isInf = 1 ↔ x = 0 ∧ y = 0`;
3. Exact `decodeAffinePointWords` round-trip recovers `(A, B)`;
4. Exact correspondence with `Ix.Cert.AiurCompression.decodeBn254AffineU80PointWords` on the 9+9
   `BN254Fr` output words! -/
theorem encodeAffinePairWords_bn254_sound {A B : G1Point}
    (hA : g1ValidPoint bn254CurveParams A = true)
    (hB : g1ValidPoint bn254CurveParams B = true) :
    let ws := encodeAffinePairWords bn254CurveParams A B
    fListLen ws = aiurTerminalOutputsBN254 ∧
    A.x < bn254FqModulus ∧ A.y < bn254FqModulus ∧
    B.x < bn254FqModulus ∧ B.y < bn254FqModulus ∧
    decodeAffinePointWords bn254CurveParams (fListTake ws 9) = A ∧
    decodeAffinePointWords bn254CurveParams (fListDrop ws 9) = B ∧
    (∃ pA pB : Bn254AffineU80Point,
      pA.x.toNat = A.x ∧ pA.y.toNat = A.y ∧ (if pA.infinity then 1 else 0) = A.isInf ∧
      pB.x.toNat = B.x ∧ pB.y.toNat = B.y ∧ (if pB.infinity then 1 else 0) = B.isInf ∧
      fListToList ws = pA.words ++ pB.words ∧
      decodeBn254AffineU80PointWords (pA.fieldWords) = some pA ∧
      decodeBn254AffineU80PointWords (pB.fieldWords) = some pB) := by
  have hmkPt : ∀ P : G1Point, g1ValidPoint bn254CurveParams P = true →
      P.x < bn254FqModulus ∧ P.y < bn254FqModulus ∧
      ∃ p : Bn254AffineU80Point,
        p.x.toNat = P.x ∧ p.y.toNat = P.y ∧ (if p.infinity then 1 else 0) = P.isInf ∧
        fListToList (encodeAffinePointWords bn254CurveParams P) = p.words ∧
        decodeBn254AffineU80PointWords p.fieldWords = some p := by
    intro P hP
    have hon := (g1ValidPoint_sound hP).1
    have hcurve := g1OnCurve_sound hon
    have hxLt : P.x < bn254FqModulus := by
      rcases hcurve with rfl | ⟨_, hx, _, _⟩
      · exact bn254FqModulus_pos
      · exact hx
    have hyLt : P.y < bn254FqModulus := by
      rcases hcurve with rfl | ⟨_, _, hy, _⟩
      · exact bn254FqModulus_pos
      · exact hy
    have hrad : radix80 = 2 ^ 80 := radix80_eq_pow
    have hqLt : bn254FqModulus < 2 ^ 254 := by decide
    have mkCoord : ∀ v : Nat, v < bn254FqModulus →
        ∃ c : Bn254AffineU80Coord,
          c.toNat = v ∧
          fListToList (toLimbsGeneric radix80 4 v) = [c.w0, c.w1, c.w2, c.w3] := by
      intro v hv
      have hw0 : v % 2 ^ 80 < 2 ^ 80 := Nat.mod_lt _ (by decide)
      have hw1 : v / 2 ^ 80 % 2 ^ 80 < 2 ^ 80 := Nat.mod_lt _ (by decide)
      have hw2 : v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 < 2 ^ 80 := Nat.mod_lt _ (by decide)
      have hw3 : v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 < 2 ^ 14 := by
        have hq : v < 2 ^ 254 := lt_trans hv hqLt
        have hdiv : v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 = v / 2 ^ 240 := by
          rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
          congr 1
        rw [hdiv]
        have hlt14 : v / 2 ^ 240 < 2 ^ 14 := by
          have : 2 ^ 254 = 2 ^ 240 * 2 ^ 14 := by decide
          rw [this] at hq
          exact Nat.div_lt_of_lt_mul (by omega)
        rw [Nat.mod_eq_of_lt (lt_trans hlt14 (by decide : 2 ^ 14 < 2 ^ 80))]
        exact hlt14
      have hrecomp : v % 2 ^ 80 + 2 ^ 80 * (v / 2 ^ 80 % 2 ^ 80) +
          2 ^ 160 * (v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80) +
          2 ^ 240 * (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80) = v := by
        have hlt254 : v < 2 ^ 254 := lt_trans hv hqLt
        have hlt320 : v < 2 ^ 320 :=
          lt_trans hlt254 (Nat.pow_lt_pow_right (by decide) (by decide))
        have hof := ofLimbsGeneric_toLimbsGeneric (2 ^ 80) (by decide) 4 v (by
          rw [← Nat.pow_mul]; exact hlt320)
        simp only [toLimbsGeneric, ofLimbsGeneric] at hof
        have hmul := limb4_recompose_2pow80 (v % 2 ^ 80) (v / 2 ^ 80 % 2 ^ 80)
          (v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80) (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80)
        have : v % 2 ^ 80 + 2 ^ 80 * (v / 2 ^ 80 % 2 ^ 80 + 2 ^ 80 *
            (v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 + 2 ^ 80 * (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80))) = v := by
          simpa using hof
        omega
      refine ⟨⟨v % 2 ^ 80, v / 2 ^ 80 % 2 ^ 80, v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80,
          v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80, hw0, hw1, hw2, hw3, by omega⟩, hrecomp, ?_⟩
      simp only [toLimbsGeneric, fListToList, hrad]
    obtain ⟨xc, hxcN, hxcL⟩ := mkCoord P.x hxLt
    obtain ⟨yc, hycN, hycL⟩ := mkCoord P.y hyLt
    have hdecCoord : ∀ c : Bn254AffineU80Coord,
        decodeBn254AffineU80Coord (c.w0 : BN254Fr) (c.w1 : BN254Fr) (c.w2 : BN254Fr) (c.w3 : BN254Fr) =
          some c := by
      intro c
      have h80 : 2 ^ 80 < bn254FrModulus := by decide
      have h14 : 2 ^ 14 < bn254FrModulus := by decide
      have v0 : ((c.w0 : BN254Fr)).val = c.w0 := ZMod.val_natCast_of_lt (lt_trans c.h0 h80)
      have v1 : ((c.w1 : BN254Fr)).val = c.w1 := ZMod.val_natCast_of_lt (lt_trans c.h1 h80)
      have v2 : ((c.w2 : BN254Fr)).val = c.w2 := ZMod.val_natCast_of_lt (lt_trans c.h2 h80)
      have v3 : ((c.w3 : BN254Fr)).val = c.w3 := ZMod.val_natCast_of_lt (lt_trans c.h3 h14)
      unfold decodeBn254AffineU80Coord
      simp only [v0, v1, v2, v3, c.h0, c.h1, c.h2, c.h3, c.hRange, ↓reduceDIte]
    rcases hcurve with hinf | ⟨hinf0, _, _, heq⟩
    · subst hinf
      have hxz : xc.toNat = 0 := hxcN
      have hyz : yc.toNat = 0 := hycN
      let p : Bn254AffineU80Point := ⟨xc, yc, true, ⟨fun _ => ⟨hxz, hyz⟩, fun _ => rfl⟩⟩
      refine ⟨hxLt, hyLt, p, hxcN, hycN, rfl, ?_, ?_⟩
      · unfold encodeAffinePointWords
        simp only [fListToList_append, fListToList, Bn254AffineU80Point.words, p, ↓reduceIte,
          bn254CurveParams, hxcL, hycL, List.cons_append, List.nil_append]
        rfl
      · have h1 : (1 : BN254Fr).val = 1 := ZMod.val_one bn254FrModulus
        have hfw : p.fieldWords = [(xc.w0 : BN254Fr), (xc.w1 : BN254Fr), (xc.w2 : BN254Fr),
            (xc.w3 : BN254Fr), (yc.w0 : BN254Fr), (yc.w1 : BN254Fr), (yc.w2 : BN254Fr),
            (yc.w3 : BN254Fr), 1] := rfl
        rw [hfw]
        simp only [decodeBn254AffineU80PointWords, hdecCoord, h1, ↓reduceDIte, hxz, hyz, and_self, p]
    · have hnz : ¬ (xc.toNat = 0 ∧ yc.toNat = 0) := by
        rintro ⟨hx0, hy0⟩
        rw [hxcN] at hx0
        rw [hycN] at hy0
        rw [hx0, hy0] at heq
        simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
          zero_add] at heq
        have h3ne0 : ((bn254CurveParams.curveB : Nat) : ZMod bn254CurveParams.fqMod) ≠ 0 := by
          intro hz
          have hdvd : bn254CurveParams.fqMod ∣ bn254CurveParams.curveB :=
            (ZMod.natCast_eq_zero_iff _ _).mp hz
          have hlt : bn254CurveParams.curveB < bn254CurveParams.fqMod := by decide
          have h0 : bn254CurveParams.curveB = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
          exact absurd h0 (by decide)
        exact h3ne0 heq.symm
      let p : Bn254AffineU80Point :=
        ⟨xc, yc, false, ⟨fun h => absurd h (by decide), fun hz => absurd hz hnz⟩⟩
      refine ⟨hxLt, hyLt, p, hxcN, hycN, by simp [p, hinf0], ?_, ?_⟩
      · unfold encodeAffinePointWords
        simp only [fListToList_append, fListToList, Bn254AffineU80Point.words, p, Bool.false_eq_true,
          ↓reduceIte, bn254CurveParams, hxcL, hycL, hinf0, List.cons_append, List.nil_append]
      · have h0 : (0 : BN254Fr).val = 0 := ZMod.val_zero
        have hfw : p.fieldWords = [(xc.w0 : BN254Fr), (xc.w1 : BN254Fr), (xc.w2 : BN254Fr),
            (xc.w3 : BN254Fr), (yc.w0 : BN254Fr), (yc.w1 : BN254Fr), (yc.w2 : BN254Fr),
            (yc.w3 : BN254Fr), 0] := rfl
        rw [hfw]
        simp only [decodeBn254AffineU80PointWords, hdecCoord, h0, zero_ne_one, ↓reduceDIte, hnz,
          not_false_eq_true, p]
  obtain ⟨hAx, hAy, pA, hpAx, hpAy, hpAi, hpAw, hpAd⟩ := hmkPt A hA
  obtain ⟨hBx, hBy, pB, hpBx, hpBy, hpBi, hpBw, hpBd⟩ := hmkPt B hB
  have hpow : bn254CurveParams.limbRadix ^ bn254CurveParams.fqLimbCount = 2 ^ 320 := by
    change radix80 ^ 4 = 2 ^ 320
    rw [radix80_eq_pow, ← Nat.pow_mul]
  have hq320 : bn254FqModulus < 2 ^ 320 :=
    lt_trans (by decide : bn254FqModulus < 2 ^ 254) (Nat.pow_lt_pow_right (by decide) (by decide))
  have hlenA : fListLen (encodeAffinePointWords bn254CurveParams A) = 9 := by
    unfold encodeAffinePointWords
    simp [fListLen_append, fListLen_toLimbsGeneric, fListLen, bn254CurveParams]
  refine ⟨encodeAffinePairWords_len_bn254 A B, hAx, hAy, hBx, hBy, ?_, ?_,
    pA, pB, hpAx, hpAy, hpAi, hpBx, hpBy, hpBi, ?_, hpAd, hpBd⟩
  · unfold encodeAffinePairWords
    rw [← hlenA, fListTake_append_left]
    exact decodeAffinePointWords_encodeAffinePointWords (by decide)
      (by rw [hpow]; exact lt_trans hAx hq320) (by rw [hpow]; exact lt_trans hAy hq320)
  · unfold encodeAffinePairWords
    rw [← hlenA, fListDrop_append_left]
    exact decodeAffinePointWords_encodeAffinePointWords (by decide)
      (by rw [hpow]; exact lt_trans hBx hq320) (by rw [hpow]; exact lt_trans hBy hq320)
  · unfold encodeAffinePairWords
    rw [fListToList_append, hpAw, hpBw]

set_option exponentiation.threshold 512 in
/-- **BLS12-381 Canonical 22-Word `5 × u80/u61` Affine Soundness & `DeferredFold` Bridge
(`encodeAffinePairWords_bls12381_sound`):**
For any validated BLS12-381 pair `(A, B)`:
1. `fListLen (encodeAffinePairWords bls12381CurveParams A B) = 22`;
2. Both `A` and `B` have canonical `< bls12381FqModulus` coordinates, strict `isInf = 1 ↔ x = 0 ∧ y = 0`,
   and prime-order subgroup membership (`bls12381_g1Validate_prime_order`);
3. Exact `decodeAffinePointWords` round-trip recovers `(A, B)`;
4. Exact correspondence with `Ix.Cert.AiurCompression.Bls12381AffineU80Point` (`5 × u80/u61`)! -/
theorem encodeAffinePairWords_bls12381_sound {A B : G1Point}
    (hA : g1ValidPoint bls12381CurveParams A = true)
    (hB : g1ValidPoint bls12381CurveParams B = true) :
    let ws := encodeAffinePairWords bls12381CurveParams A B
    fListLen ws = 22 ∧
    A.x < bls12381FqModulus ∧ A.y < bls12381FqModulus ∧
    B.x < bls12381FqModulus ∧ B.y < bls12381FqModulus ∧
    decodeAffinePointWords bls12381CurveParams (fListTake ws 11) = A ∧
    decodeAffinePointWords bls12381CurveParams (fListDrop ws 11) = B ∧
    (∃ pA pB : Bls12381AffineU80Point,
      pA.x.toNat = A.x ∧ pA.y.toNat = A.y ∧ (if pA.infinity then 1 else 0) = A.isInf ∧
      pB.x.toNat = B.x ∧ pB.y.toNat = B.y ∧ (if pB.infinity then 1 else 0) = B.isInf ∧
      fListToList ws = pA.words ++ pB.words) := by
  have hmkPt : ∀ P : G1Point, g1ValidPoint bls12381CurveParams P = true →
      P.x < bls12381FqModulus ∧ P.y < bls12381FqModulus ∧
      ∃ p : Bls12381AffineU80Point,
        p.x.toNat = P.x ∧ p.y.toNat = P.y ∧ (if p.infinity then 1 else 0) = P.isInf ∧
        fListToList (encodeAffinePointWords bls12381CurveParams P) = p.words := by
    intro P hP
    have hon := (g1ValidPoint_sound hP).1
    have hcurve := g1OnCurve_sound hon
    have hxLt : P.x < bls12381FqModulus := by
      rcases hcurve with rfl | ⟨_, hx, _, _⟩
      · exact bls12381FqModulus_pos
      · exact hx
    have hyLt : P.y < bls12381FqModulus := by
      rcases hcurve with rfl | ⟨_, _, hy, _⟩
      · exact bls12381FqModulus_pos
      · exact hy
    have hrad : radix80 = 2 ^ 80 := radix80_eq_pow
    have hqLt : bls12381FqModulus < 2 ^ 381 := by
      have h381 : (2 : Nat) ^ 381 = 2 ^ 256 * 2 ^ 125 := by rw [← Nat.pow_add]
      rw [h381]; decide
    have mkCoord : ∀ v : Nat, v < bls12381FqModulus →
        ∃ c : Bls12381AffineU80Coord,
          c.toNat = v ∧
          fListToList (toLimbsGeneric radix80 5 v) = [c.w0, c.w1, c.w2, c.w3, c.w4] := by
      intro v hv
      have hw0 : v % 2 ^ 80 < 2 ^ 80 := Nat.mod_lt _ (by decide)
      have hw1 : v / 2 ^ 80 % 2 ^ 80 < 2 ^ 80 := Nat.mod_lt _ (by decide)
      have hw2 : v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 < 2 ^ 80 := Nat.mod_lt _ (by decide)
      have hw3 : v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 < 2 ^ 80 := Nat.mod_lt _ (by decide)
      have hw4 : v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 < 2 ^ 61 := by
        have hq : v < 2 ^ 381 := lt_trans hv hqLt
        have hdiv : v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 = v / 2 ^ 320 := by
          rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
            ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
        rw [hdiv]
        have hlt61 : v / 2 ^ 320 < 2 ^ 61 := by
          have : (2 : Nat) ^ 381 = 2 ^ 320 * 2 ^ 61 := by rw [← Nat.pow_add]
          rw [this] at hq
          exact Nat.div_lt_of_lt_mul (by omega)
        rw [Nat.mod_eq_of_lt (lt_trans hlt61 (by decide : 2 ^ 61 < 2 ^ 80))]
        exact hlt61
      have hrecomp : v % 2 ^ 80 + 2 ^ 80 * (v / 2 ^ 80 % 2 ^ 80) +
          2 ^ 160 * (v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80) +
          2 ^ 240 * (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80) +
          2 ^ 320 * (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80) = v := by
        have hlt381 : v < 2 ^ 381 := lt_trans hv hqLt
        have hlt400 : v < 2 ^ 400 :=
          lt_trans hlt381 (Nat.pow_lt_pow_right (by decide) (by decide))
        have hof := ofLimbsGeneric_toLimbsGeneric (2 ^ 80) (by decide) 5 v (by
          rw [← Nat.pow_mul]; exact hlt400)
        simp only [toLimbsGeneric, ofLimbsGeneric] at hof
        have hmul := limb5_recompose_2pow80 (v % 2 ^ 80) (v / 2 ^ 80 % 2 ^ 80)
          (v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80) (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80)
          (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80)
        have : v % 2 ^ 80 + 2 ^ 80 * (v / 2 ^ 80 % 2 ^ 80 + 2 ^ 80 *
            (v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 + 2 ^ 80 * (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80 +
              2 ^ 80 * (v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80)))) = v := by
          simpa using hof
        omega
      refine ⟨⟨v % 2 ^ 80, v / 2 ^ 80 % 2 ^ 80, v / 2 ^ 80 / 2 ^ 80 % 2 ^ 80,
          v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80,
          v / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 / 2 ^ 80 % 2 ^ 80,
          hw0, hw1, hw2, hw3, hw4, by omega⟩, hrecomp, ?_⟩
      simp only [toLimbsGeneric, fListToList, hrad]
    obtain ⟨xc, hxcN, hxcL⟩ := mkCoord P.x hxLt
    obtain ⟨yc, hycN, hycL⟩ := mkCoord P.y hyLt
    rcases hcurve with hinf | ⟨hinf0, _, _, heq⟩
    · subst hinf
      have hxz : xc.toNat = 0 := hxcN
      have hyz : yc.toNat = 0 := hycN
      let p : Bls12381AffineU80Point := ⟨xc, yc, true, ⟨fun _ => ⟨hxz, hyz⟩, fun _ => rfl⟩⟩
      refine ⟨hxLt, hyLt, p, hxcN, hycN, rfl, ?_⟩
      unfold encodeAffinePointWords
      simp only [fListToList_append, fListToList, Bls12381AffineU80Point.words, p, ↓reduceIte,
        bls12381CurveParams, hxcL, hycL, List.cons_append, List.nil_append]
      rfl
    · have hnz : ¬ (xc.toNat = 0 ∧ yc.toNat = 0) := by
        rintro ⟨hx0, hy0⟩
        rw [hxcN] at hx0
        rw [hycN] at hy0
        rw [hx0, hy0] at heq
        simp only [Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
          zero_add] at heq
        have h4ne0 : ((bls12381CurveParams.curveB : Nat) : ZMod bls12381CurveParams.fqMod) ≠ 0 := by
          intro hz
          have hdvd : bls12381CurveParams.fqMod ∣ bls12381CurveParams.curveB :=
            (ZMod.natCast_eq_zero_iff _ _).mp hz
          have hlt : bls12381CurveParams.curveB < bls12381CurveParams.fqMod := by decide
          have h0 : bls12381CurveParams.curveB = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
          exact absurd h0 (by decide)
        exact h4ne0 heq.symm
      let p : Bls12381AffineU80Point :=
        ⟨xc, yc, false, ⟨fun h => absurd h (by decide), fun hz => absurd hz hnz⟩⟩
      refine ⟨hxLt, hyLt, p, hxcN, hycN, by simp [p, hinf0], ?_⟩
      unfold encodeAffinePointWords
      simp only [fListToList_append, fListToList, Bls12381AffineU80Point.words, p, Bool.false_eq_true,
        ↓reduceIte, bls12381CurveParams, hxcL, hycL, hinf0, List.cons_append, List.nil_append]
  obtain ⟨hAx, hAy, pA, hpAx, hpAy, hpAi, hpAw⟩ := hmkPt A hA
  obtain ⟨hBx, hBy, pB, hpBx, hpBy, hpBi, hpBw⟩ := hmkPt B hB
  have hpow : bls12381CurveParams.limbRadix ^ bls12381CurveParams.fqLimbCount = 2 ^ 400 := by
    change radix80 ^ 5 = 2 ^ 400
    rw [radix80_eq_pow, ← Nat.pow_mul]
  have hq400 : bls12381FqModulus < 2 ^ 400 := by
    have h381 : bls12381FqModulus < 2 ^ 381 := by
      have h381' : (2 : Nat) ^ 381 = 2 ^ 256 * 2 ^ 125 := by rw [← Nat.pow_add]
      rw [h381']; decide
    exact lt_trans h381 (Nat.pow_lt_pow_right (by decide) (by decide))
  have hlenA : fListLen (encodeAffinePointWords bls12381CurveParams A) = 11 := by
    unfold encodeAffinePointWords
    simp [fListLen_append, fListLen_toLimbsGeneric, fListLen, bls12381CurveParams]
  refine ⟨encodeAffinePairWords_len_bls12381 A B, hAx, hAy, hBx, hBy, ?_, ?_,
    pA, pB, hpAx, hpAy, hpAi, hpBx, hpBy, hpBi, ?_⟩
  · unfold encodeAffinePairWords
    rw [← hlenA, fListTake_append_left]
    exact decodeAffinePointWords_encodeAffinePointWords (by decide)
      (by rw [hpow]; exact lt_trans hAx hq400) (by rw [hpow]; exact lt_trans hAy hq400)
  · unfold encodeAffinePairWords
    rw [← hlenA, fListDrop_append_left]
    exact decodeAffinePointWords_encodeAffinePointWords (by decide)
      (by rw [hpow]; exact lt_trans hBx hq400) (by rw [hpow]; exact lt_trans hBy hq400)
  · unfold encodeAffinePairWords
    rw [fListToList_append, hpAw, hpBw]

/-! #### Deferred Accumulator Fold & Two-Stage Pipeline (`stepV1` + `verifyAccumulatorV1` → `DeferredFold`) -/

/-- Curve-group model specializing `G1GroupModel` to `Ix.Cert.Compression.OuterRelation.BilinearPairing`
on BN254 (`bn254CurveParams`). -/
structure BN254G1Model (bp : BilinearPairing) extends G1GroupModel bn254CurveParams bp.G1 where
  valid_of_g1Valid : ∀ P, g1ValidPoint bn254CurveParams P = true → Valid P
  g1Valid_of_valid : ∀ P, Valid P → g1ValidPoint bn254CurveParams P = true
  smul_eq : ∀ (ρ : BN254Fr) (P : bp.G1), ρ.val • P = bp.smul ρ P

/-- Curve-group model specializing `G1GroupModel` to `Bls12381BilinearPairing` on BLS12-381
(`bls12381CurveParams`), certifying that every validated point lies in `bp.InPrimeSubgroupG1`. -/
structure BLS12381G1Model (bp : Bls12381BilinearPairing)
    extends G1GroupModel bls12381CurveParams bp.G1 where
  valid_of_g1Valid : ∀ P, g1ValidPoint bls12381CurveParams P = true → Valid P
  g1Valid_of_valid : ∀ P, Valid P → g1ValidPoint bls12381CurveParams P = true
  inSubgroup_of_valid : ∀ {P}, Valid P → bp.InPrimeSubgroupG1 (toG P)
  smul_eq : ∀ (ρ : BLS12381Fr) {P : bp.G1}, bp.InPrimeSubgroupG1 P → ρ.val • P = bp.smul ρ P

private theorem transcriptSampleFr_lt (c : CurveParams) (hfr : 0 < c.frMod) (tr : KzgTranscript) :
    (transcriptSampleFr c tr).challenge < c.frMod := by
  unfold transcriptSampleFr
  exact Nat.mod_lt _ hfr

private theorem foldWeight_sound {c : CurveParams} (hfr : 0 < c.frMod)
    {tr : KzgTranscript} {polDig stmtDig keyDig : DigestWords} {stage : Nat}
    {prevA prevB curA curB : G1Point}
    (h : (foldWeight c tr polDig stmtDig stage keyDig prevA prevB curA curB).1 = 1) :
    let w := (foldWeight c tr polDig stmtDig stage keyDig prevA prevB curA curB).2
    0 < w ∧ w < c.frMod := by
  unfold foldWeight at h ⊢
  dsimp only at h ⊢
  set payload :=
    byteAppend foldDomainBytes
      (byteAppend (digestWordsToBytes polDig)
      (byteAppend (digestWordsToBytes stmtDig)
      (byteAppend (encodeU32 stage)
      (byteAppend (digestWordsToBytes keyDig)
      (byteAppend (g1ToBytes c prevA)
      (byteAppend (g1ToBytes c prevB)
      (byteAppend (g1ToBytes c curA) (g1ToBytes c curB))))))))
  set s := transcriptSampleFr c (transcriptObserveBytes tr payload)
  by_cases hz : (frIsZero s.challenge == 1) = true
  · simp [hz] at h
  simp only [hz, Bool.false_eq_true, ↓reduceIte]
  have hne : s.challenge ≠ 0 := by
    intro h0; exact hz (beq_iff_eq.mpr ((frIsZero_eq_one_iff _).mpr h0))
  exact ⟨Nat.pos_of_ne_zero hne, transcriptSampleFr_lt c hfr _⟩

/-- **BN254 Deferred Accumulator Fold Soundness (`foldAccumulator_sound_bn254`):**
When `KzgPackedPure.foldAccumulator bn254CurveParams` accepts on valid points, the output pair
`(a, b)` is valid (`M.Valid` & `g1ValidPoint`), the squeezed fold weight `w` satisfies
`0 < w < bn254FrModulus`, and `(M.toG a, M.toG b)` equals `Ix.Cert.AiurCompression.bn254FoldStep`! -/
theorem foldAccumulator_sound_bn254 {bp : BilinearPairing} (M : BN254G1Model bp)
    {tr : KzgTranscript} {polDig stmtDig keyDig : DigestWords} {stage : Nat}
    {prevA prevB curA curB : G1Point}
    (hpA : M.Valid prevA) (hpB : M.Valid prevB) (hcA : M.Valid curA) (hcB : M.Valid curB)
    (h : (foldAccumulator bn254CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB).1 = 1) :
    let res := foldAccumulator bn254CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB
    let w := (foldWeight bn254CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB).2
    0 < w ∧ w < bn254FrModulus ∧
    M.Valid res.2.1 ∧ M.Valid res.2.2 ∧
    (M.toG res.2.1, M.toG res.2.2) =
      bn254FoldStep bp (w : BN254Fr) (M.toG prevA, M.toG prevB) (M.toG curA, M.toG curB) := by
  have ⟨hfrPos, hfrLt⟩ := bn254CurveParams_frMod_bounds
  unfold foldAccumulator at h ⊢
  dsimp only at h ⊢
  set fw := foldWeight bn254CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB
  by_cases hfw : (fw.1 == 0) = true
  · simp [hfw] at h
  simp only [hfw, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have hfw1 : fw.1 = 1 := by
    have h01 : fw.1 = 0 ∨ fw.1 = 1 := by
      unfold fw foldWeight; dsimp only; split_ifs <;> simp
    rcases h01 with h0 | h1
    · exfalso; exact hfw (beq_iff_eq.mpr h0)
    · exact h1
  obtain ⟨hwPos, hwLt⟩ := foldWeight_sound hfrPos hfw1
  have hwLt' : fw.2 < bn254FrModulus := hwLt
  obtain ⟨hmA, hmAG⟩ := g1Msm_singleton_sound M.toG1GroupModel hfrPos hfrLt hpA fw.2
  obtain ⟨hmB, hmBG⟩ := g1Msm_singleton_sound M.toG1GroupModel hfrPos hfrLt hpB fw.2
  have haV : M.Valid (g1Add bn254CurveParams curA (g1Msm bn254CurveParams (.cons { point := prevA, scalar := fw.2 } .nil))) :=
    M.valid_add hcA hmA
  have hbV : M.Valid (g1Add bn254CurveParams curB (g1Msm bn254CurveParams (.cons { point := prevB, scalar := fw.2 } .nil))) :=
    M.valid_add hcB hmB
  have hmodEq : fw.2 % bn254CurveParams.frMod = ((fw.2 : BN254Fr)).val :=
    (Nat.mod_eq_of_lt hwLt').trans (ZMod.val_natCast_of_lt hwLt').symm
  refine ⟨hwPos, hwLt', haV, hbV, ?_⟩
  unfold bn254FoldStep
  ext1
  · rw [M.toG_add hcA hmA, hmAG, hmodEq, M.smul_eq]
  · rw [M.toG_add hcB hmB, hmBG, hmodEq, M.smul_eq]

/-- **BLS12-381 Subgroup-Enforced Deferred Accumulator Fold Soundness
(`foldAccumulator_sound_bls12381`):**
When `KzgPackedPure.foldAccumulator bls12381CurveParams` accepts on valid subgroup points, the
output pair `(a, b)` stays in `BlsPairInSubgroup bp`, the squeezed fold weight `w` satisfies
`0 < w < bls12381FrModulus`, and `(M.toG a, M.toG b)` equals `Ix.Cert.AiurCompression.bls12381FoldStep`! -/
theorem foldAccumulator_sound_bls12381 {bp : Bls12381BilinearPairing} (M : BLS12381G1Model bp)
    {tr : KzgTranscript} {polDig stmtDig keyDig : DigestWords} {stage : Nat}
    {prevA prevB curA curB : G1Point}
    (hpA : M.Valid prevA) (hpB : M.Valid prevB) (hcA : M.Valid curA) (hcB : M.Valid curB)
    (h : (foldAccumulator bls12381CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB).1 = 1) :
    let res := foldAccumulator bls12381CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB
    let w := (foldWeight bls12381CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB).2
    0 < w ∧ w < bls12381FrModulus ∧
    M.Valid res.2.1 ∧ M.Valid res.2.2 ∧
    BlsPairInSubgroup bp (M.toG res.2.1, M.toG res.2.2) ∧
    (M.toG res.2.1, M.toG res.2.2) =
      bls12381FoldStep bp (w : BLS12381Fr) (M.toG prevA, M.toG prevB) (M.toG curA, M.toG curB) := by
  have ⟨hfrPos, hfrLt⟩ := bls12381CurveParams_frMod_bounds
  unfold foldAccumulator at h ⊢
  dsimp only at h ⊢
  set fw := foldWeight bls12381CurveParams tr polDig stmtDig stage keyDig prevA prevB curA curB
  by_cases hfw : (fw.1 == 0) = true
  · simp [hfw] at h
  simp only [hfw, Bool.false_eq_true, ↓reduceIte] at h ⊢
  have hfw1 : fw.1 = 1 := by
    have h01 : fw.1 = 0 ∨ fw.1 = 1 := by
      unfold fw foldWeight; dsimp only; split_ifs <;> simp
    rcases h01 with h0 | h1
    · exfalso; exact hfw (beq_iff_eq.mpr h0)
    · exact h1
  obtain ⟨hwPos, hwLt⟩ := foldWeight_sound hfrPos hfw1
  have hwLt' : fw.2 < bls12381FrModulus := hwLt
  obtain ⟨hmA, hmAG⟩ := g1Msm_singleton_sound M.toG1GroupModel hfrPos hfrLt hpA fw.2
  obtain ⟨hmB, hmBG⟩ := g1Msm_singleton_sound M.toG1GroupModel hfrPos hfrLt hpB fw.2
  have haV : M.Valid (g1Add bls12381CurveParams curA (g1Msm bls12381CurveParams (.cons { point := prevA, scalar := fw.2 } .nil))) :=
    M.valid_add hcA hmA
  have hbV : M.Valid (g1Add bls12381CurveParams curB (g1Msm bls12381CurveParams (.cons { point := prevB, scalar := fw.2 } .nil))) :=
    M.valid_add hcB hmB
  have hmodEq : fw.2 % bls12381CurveParams.frMod = ((fw.2 : BLS12381Fr)).val :=
    (Nat.mod_eq_of_lt hwLt').trans (ZMod.val_natCast_of_lt hwLt').symm
  refine ⟨hwPos, hwLt', haV, hbV, ⟨M.inSubgroup_of_valid haV, M.inSubgroup_of_valid hbV⟩, ?_⟩
  unfold bls12381FoldStep
  ext1
  · rw [M.toG_add hcA hmA, hmAG, hmodEq, M.smul_eq _ (M.inSubgroup_of_valid hpA)]
  · rw [M.toG_add hcB hmB, hmBG, hmodEq, M.smul_eq _ (M.inSubgroup_of_valid hpB)]

private theorem unpackAccumulatorChunks_valid {c : CurveParams} {xs : FList}
    (h : (unpackAccumulatorChunks c xs).1 = 1) :
    g1ValidPoint c (unpackAccumulatorChunks c xs).2.1 = true ∧
    g1ValidPoint c (unpackAccumulatorChunks c xs).2.2 = true := by
  unfold unpackAccumulatorChunks at h ⊢
  by_cases h32 : (c.g1ByteLen == 32) = true
  · simp only [h32, ↓reduceIte] at h ⊢
    match xs with
    | .cons c0 (.cons c1 (.cons c2 (.cons c3 .nil))) =>
      unfold unpackAccumulator4 at h ⊢
      dsimp only at h ⊢
      split_ifs at h with hlt hok
      simp only [Bool.and_eq_true, beq_iff_eq] at hok
      simp only [hlt, hok.1, hok.2, beq_self_eq_true, Bool.and_self, ↓reduceIte]
      exact ⟨(g1FromBytes_sound hok.1).2.2.1, (g1FromBytes_sound hok.2).2.2.1⟩
    | .nil | .cons _ .nil | .cons _ (.cons _ .nil) | .cons _ (.cons _ (.cons _ .nil))
    | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))) => simp at h
  · simp only [h32, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h48 : (c.g1ByteLen == 48) = true
    · simp only [h48, ↓reduceIte] at h ⊢
      match xs with
      | .cons c0 (.cons c1 (.cons c2 (.cons c3 (.cons c4 (.cons c5 .nil))))) =>
        unfold unpackAccumulator6 at h ⊢
        dsimp only at h ⊢
        split_ifs at h with hlt hok
        simp only [Bool.and_eq_true, beq_iff_eq] at hok
        simp only [hlt, hok.1, hok.2, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        exact ⟨(g1FromBytes_sound hok.1).2.2.1, (g1FromBytes_sound hok.2).2.2.1⟩
      | .nil | .cons _ .nil | .cons _ (.cons _ .nil) | .cons _ (.cons _ (.cons _ .nil))
      | .cons _ (.cons _ (.cons _ (.cons _ .nil))) | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ .nil))))
      | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))))) => simp at h
    · simp only [h48, Bool.false_eq_true, ↓reduceIte] at h ⊢
      match xs with
      | .cons a (.cons b .nil) =>
        dsimp only at h ⊢
        split_ifs at h with hok
        simp only [Bool.and_eq_true, beq_iff_eq] at hok
        simp only [hok.1, hok.2, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        exact ⟨(g1FromBytes_sound hok.1).2.2.1, (g1FromBytes_sound hok.2).2.2.1⟩
      | .nil | .cons _ .nil | .cons _ (.cons _ (.cons _ _)) => simp at h

private theorem checkPredecessorStage1_sound {pol : ChainPolicy} {statement : DigestWords}
    {claims : FListList} (h : (checkPredecessorStage1 pol statement claims).1 = 1) :
    (checkPredecessorStage1 pol statement claims).2 = (g1Inf, g1Inf) := by
  unfold checkPredecessorStage1 at h ⊢
  match claims with
  | .cons (.cons tag (.cons entry rest0)) .nil =>
    dsimp only at h ⊢
    by_cases hte : (tag == 1 && entry == pol.glEntry) = true
    swap; · simp [hte] at h
    simp only [hte, ↓reduceIte] at h ⊢
    cases hokR : (takeDigest8 rest0).1 with
    | zero => simp [hokR] at h
    | succ kR =>
      cases kR with
      | succ _ => simp [hokR] at h
      | zero =>
        cases hokS : (takeDigest8 (takeDigest8 rest0).2.2).1 with
        | zero => simp [hokR, hokS] at h
        | succ kS =>
          cases kS with
          | succ _ => simp [hokR, hokS] at h
          | zero =>
            cases hrem : (takeDigest8 (takeDigest8 rest0).2.2).2.2 with
            | cons _ _ => simp [hokR, hokS, hrem] at h
            | nil =>
              simp only [hokR, hokS, hrem] at h ⊢
              split_ifs at h with heq
              simp only [heq, ↓reduceIte]
  | .nil | .cons .nil .nil | .cons (.cons _ .nil) .nil | .cons _ (.cons _ _) =>
    simp at h

private theorem checkPredecessorNarrow_sound {c : CurveParams} {vals : FList}
    {policyDigest statement : DigestWords} {stage : Nat}
    (h : (checkPredecessorNarrow c vals policyDigest stage statement).1 = 1) :
    let prev := checkPredecessorNarrow c vals policyDigest stage statement
    g1ValidPoint c prev.2.1 = true ∧ g1ValidPoint c prev.2.2 = true := by
  unfold checkPredecessorNarrow at h ⊢
  dsimp only at h ⊢
  by_cases hp : ((takeDigest8 vals).1 == 0 || digestWordsEq (takeDigest8 vals).2.1 policyDigest == 0) = true
  · simp [hp] at h
  simp only [hp, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases hr1 : (takeDigest8 vals).2.2 with
  | nil => simp [hr1] at h
  | cons prevStage rest2 =>
    simp only [hr1] at h ⊢
    by_cases hst : (prevStage + 1 != stage) = true
    · simp [hst] at h
    simp only [hst, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases hs : ((takeDigest8 rest2).1 == 0 || digestWordsEq (takeDigest8 rest2).2.1 statement == 0) = true
    · simp [hs] at h
    simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact unpackAccumulatorChunks_valid h

private theorem ite_proof_ok_01 {p : Prop} [Decidable p] {a b : ParseProof}
    (ha : a.ok = 0 ∨ a.ok = 1) (hb : b.ok = 0 ∨ b.ok = 1) :
    (if p then a else b).ok = 0 ∨ (if p then a else b).ok = 1 := by
  split_ifs <;> assumption

private theorem ite_verify_ok_01 {p : Prop} [Decidable p] {a b : DeferredVerifyResult}
    (ha : a.ok = 0 ∨ a.ok = 1) (hb : b.ok = 0 ∨ b.ok = 1) :
    (if p then a else b).ok = 0 ∨ (if p then a else b).ok = 1 := by
  split_ifs <;> assumption

private theorem readPackedProof_ok_01 (c : CurveParams) (bs : ByteList) :
    (readPackedProof c bs).ok = 0 ∨ (readPackedProof c bs).ok = 1 := by
  unfold readPackedProof; dsimp only
  set m := checkMagic bs magicPackedProof
  set ac := readU32 m.rest
  set act := readTags ac.rest ac.val
  set lc := readU32 act.rest
  set lgs := readTags lc.rest lc.val
  set mb := readBlob lgs.rest
  set sb := readBlob mb.rest
  set qb := readBlob sb.rest
  set mainC := readPackedCommitment c mb.bytes
  set stage2C := readPackedCommitment c sb.bytes
  set quotC := readPackedCommitment c qb.bytes
  set accCnt := readU32 qb.rest
  set accs := readScalars c accCnt.rest accCnt.val
  set mo := readOpenings c accs.rest
  set so := readOpenings c mo.rest
  set qo := readOpenings c so.rest
  set ftag := readU8 qo.rest
  apply ite_proof_ok_01; swap; · exact Or.inl rfl
  apply ite_proof_ok_01; swap; · exact Or.inl rfl
  apply ite_proof_ok_01; swap; · exact Or.inl rfl
  rcases ftag.val with _ | _ | _ <;> simp only [beq_self_eq_true, ↓reduceIte]
  · split_ifs <;> simp
  · split_ifs <;> simp
  · simp

private theorem verifyPacked_ok_01 (c : CurveParams) (key : PackedKey) (proof : PackedProof)
    (claims : FListList) :
    (verifyPacked c key proof claims).ok = 0 ∨ (verifyPacked c key proof claims).ok = 1 := by
  unfold verifyPacked
  apply ite_verify_ok_01 (Or.inl rfl)
  apply ite_verify_ok_01 (Or.inl rfl)
  apply ite_verify_ok_01 (Or.inl rfl)
  apply ite_verify_ok_01 (Or.inl rfl)
  apply ite_verify_ok_01 (Or.inl rfl)
  unfold reducePcs
  apply ite_verify_ok_01 (Or.inl rfl)
  exact ite_verify_ok_01 (Or.inl rfl) (Or.inr rfl)

/-- **Stage-1 `CompressNarrowFixed.stepV1` Full Soundness (`stepV1_sound`):**
Whenever `(stepV1 c key keyDigest policyDigest stage statement policyBytes claimsBytes proofBytes).ok = 1`:
1. `stage = 1`, `policyDigest` and `statement` are canonical;
2. `blake3HashWords policyBytes = policyDigest` and `readChainPolicy policyBytes` succeeds (`IXAUKG01`);
3. `keyDigest = policy.glDigest` and `policy.anchors = key.anchors`;
4. `readClaims c claimsBytes` and `readPackedProof c proofBytes` both succeed;
5. `verifyPacked c key proof claims` succeeds (key-bound + SHPLONK);
6. `foldAccumulator` folds `(vr.a, vr.b)` with `(g1Inf, g1Inf)` to produce `(res.a, res.b)`. -/
theorem stepV1_sound {c : CurveParams} {key : PackedKey}
    {keyDigest policyDigest statement : DigestWords} {stage : Nat}
    {policyBytes claimsBytes proofBytes : ByteList}
    (h : (stepV1 c key keyDigest policyDigest stage statement policyBytes claimsBytes proofBytes).ok = 1) :
    let res := stepV1 c key keyDigest policyDigest stage statement policyBytes claimsBytes proofBytes
    let pp := readChainPolicy policyBytes
    let pc := readClaims c claimsBytes
    let pr := readPackedProof c proofBytes
    let vr := verifyPacked c key pr.proof pc.claims
    stage = 1 ∧
    digestWordsCanonical policyDigest = 1 ∧
    digestWordsCanonical statement = 1 ∧
    blake3HashWords policyBytes = policyDigest ∧
    pp.ok = 1 ∧
    keyDigest = pp.policy.glDigest ∧
    pp.policy.anchors = key.anchors ∧
    pc.ok = 1 ∧
    pr.ok = 1 ∧
    vr.ok = 1 ∧
    (foldAccumulator c vr.transcript policyDigest statement stage keyDigest g1Inf g1Inf vr.a vr.b).1 = 1 ∧
    (res.a, res.b) =
      (foldAccumulator c vr.transcript policyDigest statement stage keyDigest g1Inf g1Inf vr.a vr.b).2 := by
  have hdEq01 : ∀ a b, digestWordsEq a b = 0 ∨ digestWordsEq a b = 1 := by
    intro a b; unfold digestWordsEq; split_ifs <;> simp
  have hdCan01 : ∀ d, digestWordsCanonical d = 0 ∨ digestWordsCanonical d = 1 := by
    intro d; unfold digestWordsCanonical; dsimp only; split_ifs <;> simp
  have hbl01 : ∀ a b, byteListEq a b = 0 ∨ byteListEq a b = 1 := by
    intro a; induction a with
    | nil => intro b; cases b <;> simp [byteListEq]
    | cons _ _ ih => intro b; cases b with | nil => simp [byteListEq] | cons _ _ => unfold byteListEq; split_ifs; exact ih _; exact Or.inl rfl
  unfold stepV1 at h ⊢
  dsimp only at h ⊢
  by_cases h1 : (digestWordsCanonical policyDigest == 0 || digestWordsCanonical statement == 0 || stage != 1) = true
  · simp [h1] at h
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h2 : (digestWordsEq (blake3HashWords policyBytes) policyDigest == 0) = true
  · simp [h2] at h
  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set pp := readChainPolicy policyBytes
  by_cases h3 : (pp.ok == 0) = true; · simp [h3] at h
  simp only [h3, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h4 : (digestWordsEq keyDigest pp.policy.glDigest == 0) = true; · simp [h4] at h
  simp only [h4, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h5 : (byteListEq pp.policy.anchors key.anchors == 0) = true; · simp [h5] at h
  simp only [h5, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set pc := readClaims c claimsBytes
  by_cases h6 : (pc.ok == 0) = true; · simp [h6] at h
  simp only [h6, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set prev := checkPredecessorStage1 pp.policy statement pc.claims
  by_cases h7 : (prev.1 == 0) = true; · simp [h7] at h
  simp only [h7, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set pr := readPackedProof c proofBytes
  by_cases h8 : (pr.ok == 0) = true; · simp [h8] at h
  simp only [h8, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set vr := verifyPacked c key pr.proof pc.claims
  by_cases h9 : (vr.ok == 0) = true; · simp [h9] at h
  simp only [h9, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set fd := foldAccumulator c vr.transcript policyDigest statement stage keyDigest prev.2.1 prev.2.2 vr.a vr.b
  by_cases h10 : (fd.1 == 0) = true; · simp [h10] at h
  simp only [h10, Bool.false_eq_true, ↓reduceIte] at h ⊢
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, not_or, not_not] at h1
  have hpolCan : digestWordsCanonical policyDigest = 1 :=
    (hdCan01 policyDigest).resolve_left h1.1.1
  have hstCan : digestWordsCanonical statement = 1 :=
    (hdCan01 statement).resolve_left h1.1.2
  have hpolHash : blake3HashWords policyBytes = policyDigest :=
    (digestWordsEq_eq_one_iff _ _).mp ((hdEq01 _ _).resolve_left (fun h0 => h2 (beq_iff_eq.mpr h0)))
  have hppOk : pp.ok = 1 := by
    have h01 : pp.ok = 0 ∨ pp.ok = 1 := by unfold pp readChainPolicy; dsimp only; split_ifs <;> simp
    exact h01.resolve_left (fun h0 => h3 (beq_iff_eq.mpr h0))
  have hkdEq : keyDigest = pp.policy.glDigest :=
    (digestWordsEq_eq_one_iff _ _).mp ((hdEq01 _ _).resolve_left (fun h0 => h4 (beq_iff_eq.mpr h0)))
  have hancEq : pp.policy.anchors = key.anchors :=
    (byteListEq_eq_one_iff _ _).mp ((hbl01 _ _).resolve_left (fun h0 => h5 (beq_iff_eq.mpr h0)))
  have hpcOk : pc.ok = 1 := by
    have h01 : pc.ok = 0 ∨ pc.ok = 1 := by unfold pc readClaims; dsimp only; split_ifs <;> simp
    exact h01.resolve_left (fun h0 => h6 (beq_iff_eq.mpr h0))
  have hprevOk : prev.1 = 1 := by
    have h01 : prev.1 = 0 ∨ prev.1 = 1 := by
      unfold prev checkPredecessorStage1
      cases pc.claims with
      | nil => exact Or.inl rfl
      | cons c0 rest =>
        cases rest with
        | cons _ _ => exact Or.inl rfl
        | nil =>
          cases c0 with
          | nil => exact Or.inl rfl
          | cons t1 r1 =>
            cases r1 with
            | nil => exact Or.inl rfl
            | cons e1 r2 =>
              dsimp only
              by_cases hte : (t1 == 1 && e1 == pp.policy.glEntry) = true
              · simp only [hte, ↓reduceIte]
                cases (takeDigest8 r2).1 with
                | zero => exact Or.inl rfl
                | succ k => cases k with | succ _ => exact Or.inl rfl | zero =>
                  cases (takeDigest8 (takeDigest8 r2).2.2).1 with
                  | zero => exact Or.inl rfl
                  | succ k2 => cases k2 with | succ _ => exact Or.inl rfl | zero =>
                    cases (takeDigest8 (takeDigest8 r2).2.2).2.2 with
                    | cons _ _ => exact Or.inl rfl
                    | nil => split_ifs <;> simp
              · simp only [hte, Bool.false_eq_true, ↓reduceIte]; exact Or.inl trivial
    exact h01.resolve_left (fun h0 => h7 (beq_iff_eq.mpr h0))
  have hprevInf : prev.2 = (g1Inf, g1Inf) := checkPredecessorStage1_sound hprevOk
  have hprevA : prev.2.1 = g1Inf := congrArg Prod.fst hprevInf
  have hprevB : prev.2.2 = g1Inf := congrArg Prod.snd hprevInf
  have hprOk : pr.ok = 1 :=
    (readPackedProof_ok_01 c proofBytes).resolve_left (fun h0 => h8 (beq_iff_eq.mpr h0))
  have hvrOk : vr.ok = 1 :=
    (verifyPacked_ok_01 c key pr.proof pc.claims).resolve_left (fun h0 => h9 (beq_iff_eq.mpr h0))
  have hfdOk : fd.1 = 1 := by
    have h01 : fd.1 = 0 ∨ fd.1 = 1 := by unfold fd foldAccumulator; dsimp only; split_ifs <;> simp
    exact h01.resolve_left (fun h0 => h10 (beq_iff_eq.mpr h0))
  have hfdOk' : (foldAccumulator c vr.transcript policyDigest statement stage keyDigest g1Inf g1Inf vr.a vr.b).1 = 1 := by
    have hfdEq : fd = foldAccumulator c vr.transcript policyDigest statement stage keyDigest g1Inf g1Inf vr.a vr.b := by
      change foldAccumulator c vr.transcript policyDigest statement stage keyDigest prev.2.1 prev.2.2 vr.a vr.b = _
      rw [hprevA, hprevB]
    rwa [← hfdEq]
  refine ⟨h1.2, hpolCan, hstCan, hpolHash, hppOk, hkdEq, hancEq, hpcOk, hprOk, hvrOk, hfdOk', ?_⟩
  change (fd.2.1, fd.2.2) = _
  have hfdEq : fd = foldAccumulator c vr.transcript policyDigest statement stage keyDigest g1Inf g1Inf vr.a vr.b := by
    change foldAccumulator c vr.transcript policyDigest statement stage keyDigest prev.2.1 prev.2.2 vr.a vr.b = _
    rw [hprevA, hprevB]
  rw [hfdEq]

/-- **Stage-2 Terminal `CompressFinalNarrow.verifyAccumulatorV1` Full Soundness
(`verifyAccumulatorV1_sound`):**
Whenever `(verifyAccumulatorV1 c cfg key stmtLow stmtHigh policyBytes claimsBytes proofBytes).ok = 1`:
1. `stmtLow < 2^128`, `stmtHigh < 2^128`, `digestWordsToList stmt = unpackLimbsToU32Words stmtLow stmtHigh`;
2. `2 ≤ cfg.stage`, `blake3HashWords policyBytes = cfg.policyDigest`, `readChainPolicy` accepts;
3. `policy.anchors = key.anchors` AND `policy.anchors = cfg.expectedAnchors`;
4. `readClaims`, `extractNarrowClaimValues`, `checkPredecessorNarrow` accept, unpacking valid
   `(prevA, prevB)` with `g1ValidPoint c prevA = true ∧ g1ValidPoint c prevB = true`;
5. `readPackedProof` and `verifyPacked` accept;
6. `foldAccumulator` accepts, yielding `(res.a, res.b)` AND `res.affineWords = encodeAffinePairWords c res.a res.b`! -/
theorem verifyAccumulatorV1_sound {c : CurveParams} {cfg : FinalConfig} {key : PackedKey}
    {stmtLow stmtHigh : Nat} {policyBytes claimsBytes proofBytes : ByteList}
    (h : (verifyAccumulatorV1 c cfg key stmtLow stmtHigh policyBytes claimsBytes proofBytes).ok = 1) :
    let res := verifyAccumulatorV1 c cfg key stmtLow stmtHigh policyBytes claimsBytes proofBytes
    let stmt := (statementFromLimbs stmtLow stmtHigh).2
    let pp := readChainPolicy policyBytes
    let pc := readClaims c claimsBytes
    let fv := extractNarrowClaimValues pc.claims cfg.headers
    let prev := checkPredecessorNarrow c fv.2 cfg.policyDigest cfg.stage stmt
    let pr := readPackedProof c proofBytes
    let vr := verifyPacked c key pr.proof pc.claims
    stmtLow < 2 ^ 128 ∧ stmtHigh < 2 ^ 128 ∧
    digestWordsToList stmt = unpackLimbsToU32Words stmtLow stmtHigh ∧
    2 ≤ cfg.stage ∧
    blake3HashWords policyBytes = cfg.policyDigest ∧
    pp.ok = 1 ∧
    pp.policy.anchors = key.anchors ∧
    pp.policy.anchors = cfg.expectedAnchors ∧
    pc.ok = 1 ∧
    g1ValidPoint c prev.2.1 = true ∧ g1ValidPoint c prev.2.2 = true ∧
    pr.ok = 1 ∧
    vr.ok = 1 ∧
    (foldAccumulator c vr.transcript cfg.policyDigest stmt cfg.stage cfg.keyDigest
      prev.2.1 prev.2.2 vr.a vr.b).1 = 1 ∧
    (res.a, res.b) =
      (foldAccumulator c vr.transcript cfg.policyDigest stmt cfg.stage cfg.keyDigest
        prev.2.1 prev.2.2 vr.a vr.b).2 ∧
    res.affineWords = encodeAffinePairWords c res.a res.b := by
  have hdEq01 : ∀ a b, digestWordsEq a b = 0 ∨ digestWordsEq a b = 1 := by
    intro a b; unfold digestWordsEq; split_ifs <;> simp
  have hbl01 : ∀ a b, byteListEq a b = 0 ∨ byteListEq a b = 1 := by
    intro a; induction a with
    | nil => intro b; cases b <;> simp [byteListEq]
    | cons _ _ ih => intro b; cases b with | nil => simp [byteListEq] | cons _ _ => unfold byteListEq; split_ifs; exact ih _; exact Or.inl rfl
  unfold verifyAccumulatorV1 at h ⊢
  dsimp only at h ⊢
  set st := statementFromLimbs stmtLow stmtHigh
  by_cases h1 : (st.1 == 0 || decide (cfg.stage < 2)) = true
  · simp only [h1, ↓reduceIte] at h; exact absurd h (by decide)
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h2 : (digestWordsEq (blake3HashWords policyBytes) cfg.policyDigest == 0) = true
  · simp [h2] at h
  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set pp := readChainPolicy policyBytes
  by_cases h3 : (pp.ok == 0) = true; · simp [h3] at h
  simp only [h3, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h3b : (digestWordsEq cfg.keyDigest pp.policy.bnDigest == 0) = true; · simp [h3b] at h
  simp only [h3b, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h4 : (byteListEq pp.policy.anchors key.anchors == 0) = true; · simp [h4] at h
  simp only [h4, Bool.false_eq_true, ↓reduceIte] at h ⊢
  by_cases h5 : (byteListEq pp.policy.anchors cfg.expectedAnchors == 0) = true; · simp [h5] at h
  simp only [h5, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set pc := readClaims c claimsBytes
  by_cases h6 : (pc.ok == 0) = true; · simp [h6] at h
  simp only [h6, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set fv := extractNarrowClaimValues pc.claims cfg.headers
  by_cases h7 : (fv.1 == 0) = true; · simp [h7] at h
  simp only [h7, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set prev := checkPredecessorNarrow c fv.2 cfg.policyDigest cfg.stage st.2
  by_cases h8 : (prev.1 == 0) = true; · simp [h8] at h
  simp only [h8, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set pr := readPackedProof c proofBytes
  by_cases h9 : (pr.ok == 0) = true; · simp [h9] at h
  simp only [h9, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set vr := verifyPacked c key pr.proof pc.claims
  by_cases h10 : (vr.ok == 0) = true; · simp [h10] at h
  simp only [h10, Bool.false_eq_true, ↓reduceIte] at h ⊢
  set fd := foldAccumulator c vr.transcript cfg.policyDigest st.2 cfg.stage cfg.keyDigest
    prev.2.1 prev.2.2 vr.a vr.b
  by_cases h11 : (fd.1 == 0) = true; · simp [h11] at h
  simp only [h11, Bool.false_eq_true, ↓reduceIte] at h ⊢
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or] at h1
  have hstOk : st.1 = 1 := by
    have h01 : st.1 = 0 ∨ st.1 = 1 := by
      unfold st statementFromLimbs; dsimp only; split_ifs
      · unfold readDigestWords; dsimp only; split_ifs <;> simp
      · exact Or.inl rfl
    exact h01.resolve_left h1.1
  obtain ⟨hlowLt, hhighLt, _, hunpack⟩ := statementFromLimbs_eq_unpack hstOk
  have hstageGe : 2 ≤ cfg.stage := Nat.le_of_not_lt h1.2
  have hpolHash : blake3HashWords policyBytes = cfg.policyDigest :=
    (digestWordsEq_eq_one_iff _ _).mp ((hdEq01 _ _).resolve_left (fun h0 => h2 (beq_iff_eq.mpr h0)))
  have hppOk : pp.ok = 1 := by
    have h01 : pp.ok = 0 ∨ pp.ok = 1 := by unfold pp readChainPolicy; dsimp only; split_ifs <;> simp
    exact h01.resolve_left (fun h0 => h3 (beq_iff_eq.mpr h0))
  have hancK : pp.policy.anchors = key.anchors :=
    (byteListEq_eq_one_iff _ _).mp ((hbl01 _ _).resolve_left (fun h0 => h4 (beq_iff_eq.mpr h0)))
  have hancE : pp.policy.anchors = cfg.expectedAnchors :=
    (byteListEq_eq_one_iff _ _).mp ((hbl01 _ _).resolve_left (fun h0 => h5 (beq_iff_eq.mpr h0)))
  have hpcOk : pc.ok = 1 := by
    have h01 : pc.ok = 0 ∨ pc.ok = 1 := by unfold pc readClaims; dsimp only; split_ifs <;> simp
    exact h01.resolve_left (fun h0 => h6 (beq_iff_eq.mpr h0))
  have hprevOk : prev.1 = 1 := by
    have hunp01 : ∀ xs, (unpackAccumulatorChunks c xs).1 = 0 ∨ (unpackAccumulatorChunks c xs).1 = 1 := by
      intro xs; unfold unpackAccumulatorChunks
      split_ifs
      · match xs with
        | .cons _ (.cons _ (.cons _ (.cons _ .nil))) =>
          unfold unpackAccumulator4; dsimp only; split_ifs <;> simp
        | .nil | .cons _ .nil | .cons _ (.cons _ .nil) | .cons _ (.cons _ (.cons _ .nil))
        | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))) => exact Or.inl rfl
      · match xs with
        | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ .nil))))) =>
          unfold unpackAccumulator6; dsimp only; split_ifs <;> simp
        | .nil | .cons _ .nil | .cons _ (.cons _ .nil) | .cons _ (.cons _ (.cons _ .nil))
        | .cons _ (.cons _ (.cons _ (.cons _ .nil))) | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ .nil))))
        | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))))) => exact Or.inl rfl
      · match xs with
        | .cons _ (.cons _ .nil) => dsimp only; split_ifs <;> simp
        | .nil | .cons _ .nil | .cons _ (.cons _ (.cons _ _)) => exact Or.inl rfl
    have h01 : prev.1 = 0 ∨ prev.1 = 1 := by
      unfold prev checkPredecessorNarrow; dsimp only
      by_cases a : ((takeDigest8 fv.2).1 == 0 || digestWordsEq (takeDigest8 fv.2).2.1 cfg.policyDigest == 0) = true
      · simp [a]
      · simp only [a, Bool.false_eq_true, ↓reduceIte]
        cases (takeDigest8 fv.2).2.2 with
        | nil => exact Or.inl rfl
        | cons ps r2 =>
          by_cases b : (ps + 1 != cfg.stage) = true
          · simp [b]
          · simp only [b, Bool.false_eq_true, ↓reduceIte]
            by_cases d : ((takeDigest8 r2).1 == 0 || digestWordsEq (takeDigest8 r2).2.1 st.2 == 0) = true
            · simp [d]
            · simp only [d, Bool.false_eq_true, ↓reduceIte]
              exact hunp01 _
    exact h01.resolve_left (fun h0 => h8 (beq_iff_eq.mpr h0))
  obtain ⟨hpAV, hpBV⟩ := checkPredecessorNarrow_sound hprevOk
  have hprOk : pr.ok = 1 :=
    (readPackedProof_ok_01 c proofBytes).resolve_left (fun h0 => h9 (beq_iff_eq.mpr h0))
  have hvrOk : vr.ok = 1 :=
    (verifyPacked_ok_01 c key pr.proof pc.claims).resolve_left (fun h0 => h10 (beq_iff_eq.mpr h0))
  have hfdOk : fd.1 = 1 := by
    have h01 : fd.1 = 0 ∨ fd.1 = 1 := by unfold fd foldAccumulator; dsimp only; split_ifs <;> simp
    exact h01.resolve_left (fun h0 => h11 (beq_iff_eq.mpr h0))
  exact ⟨hlowLt, hhighLt, hunpack, hstageGe, hpolHash, hppOk, hancK, hancE, hpcOk,
    hpAV, hpBV, hprOk, hvrOk, hfdOk, trivial, trivial⟩

/-- **Stage-2 Terminal `CompressFinalNarrow.verifyAccumulatorV1` Predecessor-Key Policy Binding
(`verifyAccumulatorV1_bnDigest_eq`):**
Whenever `(verifyAccumulatorV1 c cfg key stmtLow stmtHigh policyBytes claimsBytes proofBytes).ok = 1`,
the verified predecessor key digest `cfg.keyDigest` equals the authorized `bnDigest` carried in the
authenticated chain policy `readChainPolicy policyBytes` (matching `CompressFinalNarrow.lean`'s
`assert_eq!(key_digest, bn_key)` check). -/
theorem verifyAccumulatorV1_bnDigest_eq {c : CurveParams} {cfg : FinalConfig} {key : PackedKey}
    {stmtLow stmtHigh : Nat} {policyBytes claimsBytes proofBytes : ByteList}
    (h : (verifyAccumulatorV1 c cfg key stmtLow stmtHigh policyBytes claimsBytes proofBytes).ok = 1) :
    cfg.keyDigest = (readChainPolicy policyBytes).policy.bnDigest := by
  have hdEq01 : ∀ a b, digestWordsEq a b = 0 ∨ digestWordsEq a b = 1 := by
    intro a b; unfold digestWordsEq; split_ifs <;> simp
  unfold verifyAccumulatorV1 at h
  dsimp only at h
  by_cases h1 : ((statementFromLimbs stmtLow stmtHigh).1 == 0 || decide (cfg.stage < 2)) = true
  · simp only [h1, ↓reduceIte] at h; exact absurd h (by decide)
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h2 : (digestWordsEq (blake3HashWords policyBytes) cfg.policyDigest == 0) = true
  · simp [h2] at h
  simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h3 : ((readChainPolicy policyBytes).ok == 0) = true
  · simp [h3] at h
  simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h3b : (digestWordsEq cfg.keyDigest (readChainPolicy policyBytes).policy.bnDigest == 0) = true
  · simp [h3b] at h
  exact (digestWordsEq_eq_one_iff _ _).mp ((hdEq01 _ _).resolve_left (fun h0 => h3b (beq_iff_eq.mpr h0)))

/-- **Two-Stage BN254 `KzgPackedPure` → `Ix.Cert.AiurCompression.DeferredFold` Headline Theorem
(`twoStage_kzgPacked_deferred_fold_sound_bn254`):**
Composes Stage 1 (`CompressNarrowFixed.stepV1`), Stage 2 (`CompressFinalNarrow.verifyAccumulatorV1`
carrying Stage 1's accumulator `(res₁.a, res₁.b)`), and terminal BN254 pairing acceptance
`bn254DeferredVal bp anchors (M.toG res₂.a, M.toG res₂.b) = 1` directly into
`Ix.Cert.AiurCompression.bn254_l3_deferred_fold_sound`:
1. Both stages' `IXAUKG01` policy, `IXAUSP01` proofs, and key-bound `verifyPacked` checks succeed;
2. The terminal 18-word `affine-u80-v1` output `res₂.affineWords` encodes canonical `< bn254FqModulus`
   coordinates matching `decodeBn254AffineU80PointWords`;
3. EITHER BOTH Stage 1's SHPLONK deferred pair `cur₁` AND Stage 2's SHPLONK deferred pair `cur₂`
   pass their individual pairing checks (`= 1`), OR Stage 2's fold challenge `w₂` fell into the
   algebraic bad-challenge set of size `≤ 1` out of `bn254FrModulus` (`≤ 2^{-253}`)! -/
theorem twoStage_kzgPacked_deferred_fold_sound_bn254 {bp : BilinearPairing}
    (M : BN254G1Model bp) (anchors : bp.G2 × bp.G2)
    -- Stage 1 inputs
    {key₁ : PackedKey} {keyDig₁ polDig stmt₁ : DigestWords} {stage₁ : Nat}
    {polBytes₁ claimsBytes₁ proofBytes₁ : ByteList}
    (h1 : (stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁).ok = 1)
    -- Stage 2 inputs
    {cfg : FinalConfig} {key₂ : PackedKey} {stmtLow stmtHigh : Nat}
    {polBytes₂ claimsBytes₂ proofBytes₂ : ByteList}
    (h2 : (verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂).ok = 1)
    -- Accumulator carry link: Stage 2 unpacked Stage 1's folded accumulator
    (hCarry :
      let res₁ := stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁
      let stmt₂ := (statementFromLimbs stmtLow stmtHigh).2
      let fv := extractNarrowClaimValues (readClaims bn254CurveParams claimsBytes₂).claims cfg.headers
      let prev := checkPredecessorNarrow bn254CurveParams fv.2 cfg.policyDigest cfg.stage stmt₂
      prev.2 = (res₁.a, res₁.b))
    -- Terminal two-pair BN254 pairing check acceptance
    (hTerm :
      let res₂ := verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂
      bn254DeferredVal bp anchors (M.toG res₂.a, M.toG res₂.b) = 1) :
    let res₁ := stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁
    let res₂ := verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂
    let vr₁ := verifyPacked bn254CurveParams key₁
      (readPackedProof bn254CurveParams proofBytes₁).proof
      (readClaims bn254CurveParams claimsBytes₁).claims
    let vr₂ := verifyPacked bn254CurveParams key₂
      (readPackedProof bn254CurveParams proofBytes₂).proof
      (readClaims bn254CurveParams claimsBytes₂).claims
    let cur₁ : bp.G1 × bp.G1 := (M.toG vr₁.a, M.toG vr₁.b)
    let cur₂ : bp.G1 × bp.G1 := (M.toG vr₂.a, M.toG vr₂.b)
    fListLen res₂.affineWords = aiurTerminalOutputsBN254 ∧
    res₂.a.x < bn254FqModulus ∧ res₂.a.y < bn254FqModulus ∧
    res₂.b.x < bn254FqModulus ∧ res₂.b.y < bn254FqModulus ∧
    seedBindsPackedKey bn254CurveParams key₁.seed key₁.circuits key₁.fixed = 1 ∧
    seedBindsPackedKey bn254CurveParams key₂.seed key₂.circuits key₂.fixed = 1 ∧
    ∃ w₁ w₂ : BN254Fr,
      (M.toG res₁.a, M.toG res₁.b) = bn254FoldStep bp w₁ (0, 0) cur₁ ∧
      (M.toG res₂.a, M.toG res₂.b) = bn254FoldStep bp w₂ (bn254FoldStep bp w₁ (0, 0) cur₁) cur₂ ∧
      ((bn254DeferredVal bp anchors cur₁ = 1 ∧ bn254DeferredVal bp anchors cur₂ = 1) ∨
        (bn254DeferredVal bp anchors
          (bn254FoldStep bp w₂ (bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 ∧
          (Finset.univ.filter fun w' : BN254Fr =>
            bn254DeferredVal bp anchors
              (bn254FoldStep bp w' (bn254FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1).card ≤ 1)) := by
  have ⟨hfrPos, hfrLt⟩ := bn254CurveParams_frMod_bounds
  obtain ⟨_, _, _, _, _, _, _, _, _, hvr1Ok, hfd1Ok, hres1Eq⟩ := stepV1_sound h1
  obtain ⟨_, _, _, _, _, _, _, _, _, hpAV, hpBV, _, hvr2Ok, hfd2Ok, hres2Eq, haff2Eq⟩ :=
    verifyAccumulatorV1_sound h2
  obtain ⟨hkb1, hvr1aV, hvr1bV, _⟩ :=
    verifyPacked_shplonk_sound M.toG1GroupModel M.valid_of_g1Valid hfrPos hfrLt hvr1Ok
  obtain ⟨hkb2, hvr2aV, hvr2bV, _⟩ :=
    verifyPacked_shplonk_sound M.toG1GroupModel M.valid_of_g1Valid hfrPos hfrLt hvr2Ok
  obtain ⟨_, _, hfd1aV, hfd1bV, hfd1Step⟩ :=
    foldAccumulator_sound_bn254 M M.valid_inf M.valid_inf hvr1aV hvr1bV hfd1Ok
  obtain ⟨_, _, hfd2aV, hfd2bV, hfd2Step⟩ :=
    foldAccumulator_sound_bn254 M (M.valid_of_g1Valid _ hpAV) (M.valid_of_g1Valid _ hpBV)
      hvr2aV hvr2bV hfd2Ok
  have ha1Eq : (stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁).a =
      (foldAccumulator bn254CurveParams _ polDig stmt₁ stage₁ keyDig₁ g1Inf g1Inf _ _).2.1 :=
    congrArg Prod.fst hres1Eq
  have hb1Eq : (stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁).b =
      (foldAccumulator bn254CurveParams _ polDig stmt₁ stage₁ keyDig₁ g1Inf g1Inf _ _).2.2 :=
    congrArg Prod.snd hres1Eq
  have ha2Eq : (verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂).a =
      (foldAccumulator bn254CurveParams _ cfg.policyDigest _ cfg.stage cfg.keyDigest _ _ _ _).2.1 :=
    congrArg Prod.fst hres2Eq
  have hb2Eq : (verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂).b =
      (foldAccumulator bn254CurveParams _ cfg.policyDigest _ cfg.stage cfg.keyDigest _ _ _ _).2.2 :=
    congrArg Prod.snd hres2Eq
  have hres2aV : g1ValidPoint bn254CurveParams
      (verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).a = true := by
    rw [ha2Eq]; exact M.g1Valid_of_valid _ hfd2aV
  have hres2bV : g1ValidPoint bn254CurveParams
      (verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).b = true := by
    rw [hb2Eq]; exact M.g1Valid_of_valid _ hfd2bV
  have haffS := encodeAffinePairWords_bn254_sound hres2aV hres2bV
  set vr₁ := verifyPacked bn254CurveParams key₁
    (readPackedProof bn254CurveParams proofBytes₁).proof
    (readClaims bn254CurveParams claimsBytes₁).claims
  set vr₂ := verifyPacked bn254CurveParams key₂
    (readPackedProof bn254CurveParams proofBytes₂).proof
    (readClaims bn254CurveParams claimsBytes₂).claims
  set stmt₂ := (statementFromLimbs stmtLow stmtHigh).2
  set prev₂ := checkPredecessorNarrow bn254CurveParams
    (extractNarrowClaimValues (readClaims bn254CurveParams claimsBytes₂).claims cfg.headers).2
    cfg.policyDigest cfg.stage stmt₂
  set w₁ : BN254Fr :=
    ((foldWeight bn254CurveParams vr₁.transcript polDig stmt₁ stage₁ keyDig₁
      g1Inf g1Inf vr₁.a vr₁.b).2 : BN254Fr)
  set w₂ : BN254Fr :=
    ((foldWeight bn254CurveParams vr₂.transcript cfg.policyDigest stmt₂ cfg.stage cfg.keyDigest
      prev₂.2.1 prev₂.2.2 vr₂.a vr₂.b).2 : BN254Fr)
  have hstep1 :
      (M.toG (stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).a,
       M.toG (stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).b) =
      bn254FoldStep bp w₁ (0, 0) (M.toG vr₁.a, M.toG vr₁.b) := by
    rw [ha1Eq, hb1Eq, hfd1Step, M.toG_inf]
  have hprevA : prev₂.2.1 =
      (stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).a := congrArg Prod.fst hCarry
  have hprevB : prev₂.2.2 =
      (stepV1 bn254CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).b := congrArg Prod.snd hCarry
  have hstep2 :
      (M.toG (verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).a,
       M.toG (verifyAccumulatorV1 bn254CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).b) =
      bn254FoldStep bp w₂ (bn254FoldStep bp w₁ (0, 0) (M.toG vr₁.a, M.toG vr₁.b))
        (M.toG vr₂.a, M.toG vr₂.b) := by
    rw [ha2Eq, hb2Eq, hfd2Step, hprevA, hprevB, hstep1]
  have hTerm' : bn254DeferredVal bp anchors
      (bn254FoldStep bp w₂ (bn254FoldStep bp w₁ (0, 0) (M.toG vr₁.a, M.toG vr₁.b))
        (M.toG vr₂.a, M.toG vr₂.b)) = 1 := by
    rw [← hstep2]; exact hTerm
  refine ⟨by rw [haff2Eq]; exact haffS.1, haffS.2.1, haffS.2.2.1, haffS.2.2.2.1, haffS.2.2.2.2.1,
    hkb1, hkb2, w₁, w₂, hstep1, hstep2,
    bn254_l3_deferred_fold_sound bp anchors w₁ w₂
      (M.toG vr₁.a, M.toG vr₁.b) (M.toG vr₂.a, M.toG vr₂.b) hTerm'⟩

/-- **Two-Stage BLS12-381 Subgroup-Enforced `KzgPackedPure` → `DeferredFold` Headline Theorem
(`twoStage_kzgPacked_deferred_fold_sound_bls12381`):**
Composes Stage 1 (`stepV1`), Stage 2 (`verifyAccumulatorV1`), Bowe-subgroup-enforced `G1` validation,
and terminal BLS12-381 pairing acceptance directly into
`Ix.Cert.AiurCompression.bls12381_l3_deferred_fold_sound`! -/
theorem twoStage_kzgPacked_deferred_fold_sound_bls12381 {bp : Bls12381BilinearPairing}
    (M : BLS12381G1Model bp) (anchors : bp.G2 × bp.G2)
    {key₁ : PackedKey} {keyDig₁ polDig stmt₁ : DigestWords} {stage₁ : Nat}
    {polBytes₁ claimsBytes₁ proofBytes₁ : ByteList}
    (h1 : (stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁).ok = 1)
    {cfg : FinalConfig} {key₂ : PackedKey} {stmtLow stmtHigh : Nat}
    {polBytes₂ claimsBytes₂ proofBytes₂ : ByteList}
    (h2 : (verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂).ok = 1)
    (hCarry :
      let res₁ := stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁
      let stmt₂ := (statementFromLimbs stmtLow stmtHigh).2
      let fv := extractNarrowClaimValues (readClaims bls12381CurveParams claimsBytes₂).claims cfg.headers
      let prev := checkPredecessorNarrow bls12381CurveParams fv.2 cfg.policyDigest cfg.stage stmt₂
      prev.2 = (res₁.a, res₁.b))
    (hTerm :
      let res₂ := verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂
      bls12381DeferredVal bp anchors (M.toG res₂.a, M.toG res₂.b) = 1) :
    let res₁ := stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁
    let res₂ := verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂
    let vr₁ := verifyPacked bls12381CurveParams key₁
      (readPackedProof bls12381CurveParams proofBytes₁).proof
      (readClaims bls12381CurveParams claimsBytes₁).claims
    let vr₂ := verifyPacked bls12381CurveParams key₂
      (readPackedProof bls12381CurveParams proofBytes₂).proof
      (readClaims bls12381CurveParams claimsBytes₂).claims
    let cur₁ : bp.G1 × bp.G1 := (M.toG vr₁.a, M.toG vr₁.b)
    let cur₂ : bp.G1 × bp.G1 := (M.toG vr₂.a, M.toG vr₂.b)
    fListLen res₂.affineWords = 22 ∧
    res₂.a.x < bls12381FqModulus ∧ res₂.a.y < bls12381FqModulus ∧
    res₂.b.x < bls12381FqModulus ∧ res₂.b.y < bls12381FqModulus ∧
    BlsPairInSubgroup bp (M.toG res₂.a, M.toG res₂.b) ∧
    seedBindsPackedKey bls12381CurveParams key₁.seed key₁.circuits key₁.fixed = 1 ∧
    seedBindsPackedKey bls12381CurveParams key₂.seed key₂.circuits key₂.fixed = 1 ∧
    ∃ w₁ w₂ : BLS12381Fr,
      (M.toG res₁.a, M.toG res₁.b) = bls12381FoldStep bp w₁ (0, 0) cur₁ ∧
      (M.toG res₂.a, M.toG res₂.b) = bls12381FoldStep bp w₂ (bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂ ∧
      ((bls12381DeferredVal bp anchors cur₁ = 1 ∧ bls12381DeferredVal bp anchors cur₂ = 1) ∨
        (bls12381DeferredVal bp anchors
          (bls12381FoldStep bp w₂ (bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1 ∧
          (Finset.univ.filter fun w' : BLS12381Fr =>
            bls12381DeferredVal bp anchors
              (bls12381FoldStep bp w' (bls12381FoldStep bp w₁ (0, 0) cur₁) cur₂) = 1).card ≤ 1)) := by
  have ⟨hfrPos, hfrLt⟩ := bls12381CurveParams_frMod_bounds
  obtain ⟨_, _, _, _, _, _, _, _, _, hvr1Ok, hfd1Ok, hres1Eq⟩ := stepV1_sound h1
  obtain ⟨_, _, _, _, _, _, _, _, _, hpAV, hpBV, _, hvr2Ok, hfd2Ok, hres2Eq, haff2Eq⟩ :=
    verifyAccumulatorV1_sound h2
  obtain ⟨hkb1, hvr1aV, hvr1bV, _⟩ :=
    verifyPacked_shplonk_sound M.toG1GroupModel M.valid_of_g1Valid hfrPos hfrLt hvr1Ok
  obtain ⟨hkb2, hvr2aV, hvr2bV, _⟩ :=
    verifyPacked_shplonk_sound M.toG1GroupModel M.valid_of_g1Valid hfrPos hfrLt hvr2Ok
  obtain ⟨_, _, hfd1aV, hfd1bV, _, hfd1Step⟩ :=
    foldAccumulator_sound_bls12381 M M.valid_inf M.valid_inf hvr1aV hvr1bV hfd1Ok
  obtain ⟨_, _, hfd2aV, hfd2bV, hsub2, hfd2Step⟩ :=
    foldAccumulator_sound_bls12381 M (M.valid_of_g1Valid _ hpAV) (M.valid_of_g1Valid _ hpBV)
      hvr2aV hvr2bV hfd2Ok
  have ha1Eq : (stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁).a =
      (foldAccumulator bls12381CurveParams _ polDig stmt₁ stage₁ keyDig₁ g1Inf g1Inf _ _).2.1 :=
    congrArg Prod.fst hres1Eq
  have hb1Eq : (stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
      polBytes₁ claimsBytes₁ proofBytes₁).b =
      (foldAccumulator bls12381CurveParams _ polDig stmt₁ stage₁ keyDig₁ g1Inf g1Inf _ _).2.2 :=
    congrArg Prod.snd hres1Eq
  have ha2Eq : (verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂).a =
      (foldAccumulator bls12381CurveParams _ cfg.policyDigest _ cfg.stage cfg.keyDigest _ _ _ _).2.1 :=
    congrArg Prod.fst hres2Eq
  have hb2Eq : (verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
      polBytes₂ claimsBytes₂ proofBytes₂).b =
      (foldAccumulator bls12381CurveParams _ cfg.policyDigest _ cfg.stage cfg.keyDigest _ _ _ _).2.2 :=
    congrArg Prod.snd hres2Eq
  have hres2aV : g1ValidPoint bls12381CurveParams
      (verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).a = true := by
    rw [ha2Eq]; exact M.g1Valid_of_valid _ hfd2aV
  have hres2bV : g1ValidPoint bls12381CurveParams
      (verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).b = true := by
    rw [hb2Eq]; exact M.g1Valid_of_valid _ hfd2bV
  have haffS := encodeAffinePairWords_bls12381_sound hres2aV hres2bV
  set vr₁ := verifyPacked bls12381CurveParams key₁
    (readPackedProof bls12381CurveParams proofBytes₁).proof
    (readClaims bls12381CurveParams claimsBytes₁).claims
  set vr₂ := verifyPacked bls12381CurveParams key₂
    (readPackedProof bls12381CurveParams proofBytes₂).proof
    (readClaims bls12381CurveParams claimsBytes₂).claims
  set stmt₂ := (statementFromLimbs stmtLow stmtHigh).2
  set prev₂ := checkPredecessorNarrow bls12381CurveParams
    (extractNarrowClaimValues (readClaims bls12381CurveParams claimsBytes₂).claims cfg.headers).2
    cfg.policyDigest cfg.stage stmt₂
  set w₁ : BLS12381Fr :=
    ((foldWeight bls12381CurveParams vr₁.transcript polDig stmt₁ stage₁ keyDig₁
      g1Inf g1Inf vr₁.a vr₁.b).2 : BLS12381Fr)
  set w₂ : BLS12381Fr :=
    ((foldWeight bls12381CurveParams vr₂.transcript cfg.policyDigest stmt₂ cfg.stage cfg.keyDigest
      prev₂.2.1 prev₂.2.2 vr₂.a vr₂.b).2 : BLS12381Fr)
  have hstep1 :
      (M.toG (stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).a,
       M.toG (stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).b) =
      bls12381FoldStep bp w₁ (0, 0) (M.toG vr₁.a, M.toG vr₁.b) := by
    rw [ha1Eq, hb1Eq, hfd1Step, M.toG_inf]
  have hprevA : prev₂.2.1 =
      (stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).a := congrArg Prod.fst hCarry
  have hprevB : prev₂.2.2 =
      (stepV1 bls12381CurveParams key₁ keyDig₁ polDig stage₁ stmt₁
        polBytes₁ claimsBytes₁ proofBytes₁).b := congrArg Prod.snd hCarry
  have hstep2 :
      (M.toG (verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).a,
       M.toG (verifyAccumulatorV1 bls12381CurveParams cfg key₂ stmtLow stmtHigh
        polBytes₂ claimsBytes₂ proofBytes₂).b) =
      bls12381FoldStep bp w₂ (bls12381FoldStep bp w₁ (0, 0) (M.toG vr₁.a, M.toG vr₁.b))
        (M.toG vr₂.a, M.toG vr₂.b) := by
    rw [ha2Eq, hb2Eq, hfd2Step, hprevA, hprevB, hstep1]
  have hTerm' : bls12381DeferredVal bp anchors
      (bls12381FoldStep bp w₂ (bls12381FoldStep bp w₁ (0, 0) (M.toG vr₁.a, M.toG vr₁.b))
        (M.toG vr₂.a, M.toG vr₂.b)) = 1 := by
    rw [← hstep2]; exact hTerm
  have hcur1Sub : BlsPairInSubgroup bp (M.toG vr₁.a, M.toG vr₁.b) :=
    ⟨M.inSubgroup_of_valid hvr1aV, M.inSubgroup_of_valid hvr1bV⟩
  have hcur2Sub : BlsPairInSubgroup bp (M.toG vr₂.a, M.toG vr₂.b) :=
    ⟨M.inSubgroup_of_valid hvr2aV, M.inSubgroup_of_valid hvr2bV⟩
  have hl3 := bls12381_l3_deferred_fold_sound bp anchors w₁ w₂ hcur1Sub hcur2Sub hTerm'
  refine ⟨by rw [haff2Eq]; exact haffS.1, haffS.2.1, haffS.2.2.1, haffS.2.2.2.1, haffS.2.2.2.2.1,
    by rw [ha2Eq, hb2Eq]; exact hsub2, hkb1, hkb2, w₁, w₂, hstep1, hstep2, hl3.2⟩

end ShplonkAndDeferredFold

/-! ## Section 6: End-to-End Composition with `CompressionIntrinsicsProof.CompressionCert` & `Ix.Cert.AiurCompression` -/

section CompressionCertBridge

open IxCC
open IxCC.AiurBackend.Schedule (CircuitSchedule)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.TypedRep (Rep)
open IxCC.AiurBackend.TypedLower (LoweredProgram)
open IxCC.AiurBackend.TypedWorld (checkTypedWorld)
open IxCC.AiurBackend.Progress (checkShape)
open IxCC.AiurBackend.CompressionIntrinsics (CompressionConfig)
open IxCC.AiurBackend.Lower (hasDoubleColon qualified qualifyExprF entryName)
open IxCC.AiurBackend.Gadgets (WorldHasFn)
open IxCC.AiurBackend.WitnessIO
  (isValidByteList ByteStreamRel StarkIOWorld KzgIOWorld
   WitnessChannelKind witnessVarName witnessWrapperBody)

/-- **BN254 End-to-End `CompressionCert` → `PairingPure.pairingCheckAffineTableBN254` Soundness
(`compressionCert_pairingCheck_bn254_sound`):**
Composes certified multi-field compilation (`compressionCert_assertOk_bn254`) with
`pairingCheckAffineTableBN254_sound`: any accepted BN254 Aiur trace for an `--assert-ok` pairing
check entrypoint semantically linked to `pairingCheckAffineTableBN254` certifies canonical
`4 × u80/u14` affine decoding, curve membership, `wIdx < 3`, and `(φ f)^((q¹² - 1) / r) = 1`
in every field `K`! -/
theorem compressionCert_pairingCheck_bn254_sound
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BN254.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source Aiur.Library.Field.BN254.F}
    (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List Aiur.Library.Field.BN254.F}
    {rom : Aiur.WidthROM Aiur.Library.Field.BN254.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BN254.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BN254.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BN254.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BN254.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true)
    {pair : AffinePairBN254} {Q0 Q1 : G2Point} {resWit : Fp12} {wIdx : Nat}
    (hSem : (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1)) →
      pairingCheckAffineTableBN254 pair Q0 Q1 resWit wIdx = 1) :
    let d0 := decodeAffineG1BN254 bn254PairingParams pair.a
    let d1 := decodeAffineG1BN254 bn254PairingParams pair.b
    let ml := millerLoop2 bn254PairingParams bn254AteLoopDigits d0.point Q0 d1.point Q1
    d0.ok = 1 ∧ d1.ok = 1 ∧
    g1Validate bn254PairingParams d0.point = true ∧
    g1Validate bn254PairingParams d1.point = true ∧
    wIdx < 3 ∧
    fp12Canonical bn254Fp ml = true ∧ ml ≠ fp12Zero ∧
    fp12Canonical bn254Fp resWit = true ∧ resWit ≠ fp12Zero ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bn254Fp 9 →+* K),
      φ (fp12ToZMod bn254Fp 9 ml) ≠ 0 →
      φ (fp12ToZMod bn254Fp 9 resWit) ≠ 0 →
      (φ (fp12ToZMod bn254Fp 9 ml)) ^ ((bn254Fp ^ 12 - 1) / bn254Fr) = 1 :=
  pairingCheckAffineTableBN254_sound
    (hSem (compressionCert_assertOk_bn254 hf cert hAssert hexp hret hfn hwOrig bridge
      valid signed rooted outside bound checked arguments decoded hcov hshape))

/-- **BLS12-381 End-to-End `CompressionCert` → `PairingPure.pairingCheckAffineBLS12381` Soundness
(`compressionCert_pairingCheck_bls12381_sound`):**
Composes `compressionCert_assertOk_bls12381` with `pairingCheckAffineBLS12381_sound`: any accepted
BLS12-381 Aiur trace for an `--assert-ok` pairing check entrypoint certifies canonical `5 × u80/u61`
affine decoding, **Bowe 2019/814 prime-order `G1` subgroup membership (`bls12381FrModulus • P = 0`)**
on both points, and `(φ f)^((q¹² - 1) / r) = 1` in every field `K`! -/
theorem compressionCert_pairingCheck_bls12381_sound
    {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : CircuitSchedule}
    {lp : LoweredProgram} {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BLS12381.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} {g : Fir.FunId}
    (cert : CompressionCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {sOrig : Aiur.Generic.Source Aiur.Library.Field.BLS12381.F}
    (hwOrig : checkTypedWorld sOrig lp = true)
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions sOrig.world)
    {as : List Aiur.Library.Field.BLS12381.F}
    {rom : Aiur.WidthROM Aiur.Library.Field.BLS12381.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BLS12381.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BLS12381.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true)
    {pair : AffinePairBLS12381} {Q0 Q1 : G2Point} {resWit : Fp12}
    (hSem : (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat 1)) →
      pairingCheckAffineBLS12381 bls12381PairingParams pair Q0 Q1 resWit = 1) :
    let d0 := decodeAffineG1BLS12381 bls12381PairingParams pair.a
    let d1 := decodeAffineG1BLS12381 bls12381PairingParams pair.b
    let ml := millerLoop2Binary bls12381PairingParams d0.point Q0 d1.point Q1
    d0.ok = 1 ∧ d1.ok = 1 ∧
    (∃ u0 : Bls12381AffineU80Point, u0.x.toNat = d0.point.x ∧ u0.y.toNat = d0.point.y ∧
      (if u0.infinity then 1 else 0) = d0.point.isInf) ∧
    (∃ u1 : Bls12381AffineU80Point, u1.x.toNat = d1.point.x ∧ u1.y.toNat = d1.point.y ∧
      (if u1.infinity then 1 else 0) = d1.point.isInf) ∧
    (∃ P0_aff : (bls12381CurveAt bls12381FqModulus).Point,
      (d0.point = g1Inf → P0_aff = 0) ∧
      (d0.point.isInf = 0 →
        ∃ hns, P0_aff = .some (d0.point.x : ZMod bls12381FqModulus)
          (d0.point.y : ZMod bls12381FqModulus) hns) ∧
      bls12381FrModulus • P0_aff = 0) ∧
    (∃ P1_aff : (bls12381CurveAt bls12381FqModulus).Point,
      (d1.point = g1Inf → P1_aff = 0) ∧
      (d1.point.isInf = 0 →
        ∃ hns, P1_aff = .some (d1.point.x : ZMod bls12381FqModulus)
          (d1.point.y : ZMod bls12381FqModulus) hns) ∧
      bls12381FrModulus • P1_aff = 0) ∧
    fp12Canonical bls12381Fp ml = true ∧ ml ≠ fp12Zero ∧
    fp12Canonical bls12381Fp resWit = true ∧ resWit ≠ fp12Zero ∧
    ∀ {K : Type*} [Field K] (φ : ZModFp12 bls12381Fp 1 →+* K),
      φ (fp12ToZMod bls12381Fp 1 ml) ≠ 0 →
      φ (fp12ToZMod bls12381Fp 1 resWit) ≠ 0 →
      (φ (fp12ToZMod bls12381Fp 1 ml)) ^ ((bls12381Fp ^ 12 - 1) / bls12381Fr) = 1 :=
  pairingCheckAffineBLS12381_sound
    (hSem (compressionCert_assertOk_bls12381 hf cert hAssert hexp hret hfn hwOrig bridge
      valid signed rooted outside bound checked arguments decoded hcov hshape))

/-- **BN254 End-to-End `CompressionCert` → `KzgPackedPure` + `DeferredFold` Soundness
(`compressionCert_kzgPacked_bn254_sound`):**
Composes `compressionCert_witness_bn254` (existential 3-channel witness ingress) with
`verifyAccumulatorV1_sound`, `readChainPolicy_sound` (`PackedPolicy`), `verifyPacked_shplonk_sound`,
`encodeAffinePairWords_bn254_sound` (18-word `affine-u80-v1`), `foldAccumulator_sound_bn254`, and
`Ix.Cert.AiurCompression.bn254_foldStep_sound`! -/
theorem compressionCert_kzgPacked_bn254_sound
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BN254.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World Aiur.Library.Field.BN254.F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BN254.F (witnessWrapperBody pubParams channels checkFnName false)))
    {bp : BilinearPairing} (M : BN254G1Model bp) (anchors : bp.G2 × bp.G2)
    {finalCfg : FinalConfig} {key : PackedKey} {stmtLow stmtHigh : Nat}
    {pub : List (SourceValue Aiur.Library.Field.BN254.F)}
    (hSpec : ∀ (pubArgs : List (SourceValue Aiur.Library.Field.BN254.F))
      (h1 h2 : Heap Aiur.Library.Field.BN254.F)
      (wPtrs : List (SourceValue Aiur.Library.Field.BN254.F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      pubArgs = pub →
      ∃ polB claimsB proofB : List UInt8,
        ws = [polB, claimsB, proofB] ∧
        (verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh
          (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).ok = 1 ∧
        bn254DeferredVal bp anchors
          (M.toG (verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh
            (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).a,
           M.toG (verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh
            (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).b) = 1)
    {rom : Aiur.WidthROM Aiur.Library.Field.BN254.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BN254.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BN254.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BN254.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BN254.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ polB claimsB proofB : List UInt8,
      let polBL := uint8ListToByteList polB
      let claimsBL := uint8ListToByteList claimsB
      let proofBL := uint8ListToByteList proofB
      let res := verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh polBL claimsBL proofBL
      let pp := readChainPolicy polBL
      let pc := readClaims bn254CurveParams claimsBL
      let fv := extractNarrowClaimValues pc.claims finalCfg.headers
      let prev := checkPredecessorNarrow bn254CurveParams fv.2 finalCfg.policyDigest finalCfg.stage
        (statementFromLimbs stmtLow stmtHigh).2
      let vr := verifyPacked bn254CurveParams key (readPackedProof bn254CurveParams proofBL).proof pc.claims
      stmtLow < 2 ^ 128 ∧ stmtHigh < 2 ^ 128 ∧
      digestWordsToList (statementFromLimbs stmtLow stmtHigh).2 = unpackLimbsToU32Words stmtLow stmtHigh ∧
      (chainPolicyToCert pp.policy).WellFormed ∧
      (chainPolicyToCert pp.policy).encode = polB ∧
      seedBindsPackedKey bn254CurveParams key.seed key.circuits key.fixed = 1 ∧
      fListLen res.affineWords = aiurTerminalOutputsBN254 ∧
      res.a.x < bn254FqModulus ∧ res.a.y < bn254FqModulus ∧
      res.b.x < bn254FqModulus ∧ res.b.y < bn254FqModulus ∧
      ∃ w : BN254Fr,
        (M.toG res.a, M.toG res.b) =
          bn254FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b) ∧
        ((bn254DeferredVal bp anchors (M.toG vr.a, M.toG vr.b) = 1 ∧
          bn254DeferredVal bp anchors (M.toG prev.2.1, M.toG prev.2.2) = 1) ∨
         (bn254DeferredVal bp anchors
            (bn254FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b)) = 1 ∧
          (Finset.univ.filter fun w' : BN254Fr =>
            bn254DeferredVal bp anchors
              (bn254FoldStep bp w' (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b)) = 1).card ≤ 1)) := by
  obtain ⟨ws, _, _, hres⟩ :=
    compressionCert_witness_bn254 cert hAssert hsio hkio bridge hchkQual hnd hwrap
      (Spec := fun pubArgs ws => pubArgs = pub →
        ∃ polB claimsB proofB : List UInt8,
          ws = [polB, claimsB, proofB] ∧
          (verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh
            (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).ok = 1 ∧
          bn254DeferredVal bp anchors
            (M.toG (verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh
              (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).a,
             M.toG (verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh
              (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).b) = 1)
      hSpec valid signed rooted outside bound checked arguments decoded
  obtain ⟨polB, claimsB, proofB, _, hAcc, hTerm⟩ := hres rfl
  set polBL := uint8ListToByteList polB
  set claimsBL := uint8ListToByteList claimsB
  set proofBL := uint8ListToByteList proofB
  set res := verifyAccumulatorV1 bn254CurveParams finalCfg key stmtLow stmtHigh polBL claimsBL proofBL
  set stmt := (statementFromLimbs stmtLow stmtHigh).2
  set pc := readClaims bn254CurveParams claimsBL
  set fv := extractNarrowClaimValues pc.claims finalCfg.headers
  set prev := checkPredecessorNarrow bn254CurveParams fv.2 finalCfg.policyDigest finalCfg.stage stmt
  set vr := verifyPacked bn254CurveParams key (readPackedProof bn254CurveParams proofBL).proof pc.claims
  have ⟨hfrPos, hfrLt⟩ := bn254CurveParams_frMod_bounds
  obtain ⟨hlowLt, hhighLt, hunpack, _, _, hppOk, _, _, _, hpAV, hpBV, _, hvrOk, hfdOk, hpairEq, haffEq⟩ :=
    verifyAccumulatorV1_sound hAcc
  have hpolS := readChainPolicy_sound hppOk
  have hpolEnc : (chainPolicyToCert (readChainPolicy polBL).policy).encode = polB := by
    rw [hpolS.2.2.2.2.2.2.2.2.2.2]
    exact byteListToUInt8List_uint8ListToByteList polB
  obtain ⟨hkb, hvraV, hvrbV, _⟩ :=
    verifyPacked_shplonk_sound M.toG1GroupModel M.valid_of_g1Valid hfrPos hfrLt hvrOk
  obtain ⟨_, _, hfdaV, hfdbV, hfdStep⟩ :=
    foldAccumulator_sound_bn254 M (M.valid_of_g1Valid _ hpAV) (M.valid_of_g1Valid _ hpBV)
      hvraV hvrbV hfdOk
  have haEq : res.a =
      (foldAccumulator bn254CurveParams vr.transcript finalCfg.policyDigest stmt finalCfg.stage finalCfg.keyDigest
        prev.2.1 prev.2.2 vr.a vr.b).2.1 :=
    congrArg Prod.fst hpairEq
  have hbEq : res.b =
      (foldAccumulator bn254CurveParams vr.transcript finalCfg.policyDigest stmt finalCfg.stage finalCfg.keyDigest
        prev.2.1 prev.2.2 vr.a vr.b).2.2 :=
    congrArg Prod.snd hpairEq
  have haffS := encodeAffinePairWords_bn254_sound (A := res.a) (B := res.b)
    (by rw [haEq]; exact M.g1Valid_of_valid _ hfdaV)
    (by rw [hbEq]; exact M.g1Valid_of_valid _ hfdbV)
  set w : BN254Fr :=
    ((foldWeight bn254CurveParams vr.transcript finalCfg.policyDigest stmt finalCfg.stage finalCfg.keyDigest
      prev.2.1 prev.2.2 vr.a vr.b).2 : BN254Fr)
  have hstepEq :
      (M.toG res.a, M.toG res.b) =
      bn254FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b) := by
    rw [haEq, hbEq, hfdStep]
  have hTerm' : bn254DeferredVal bp anchors
      (bn254FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b)) = 1 := by
    rw [← hstepEq]; exact hTerm
  exact ⟨polB, claimsB, proofB, hlowLt, hhighLt, hunpack, hpolS.2.2.2.2.2.2.2.2.2.1, hpolEnc,
    hkb, by rw [haffEq]; exact haffS.1, haffS.2.1, haffS.2.2.1, haffS.2.2.2.1, haffS.2.2.2.2.1,
    w, hstepEq, bn254_foldStep_sound bp anchors w (M.toG prev.2.1, M.toG prev.2.2)
      (M.toG vr.a, M.toG vr.b) hTerm'⟩

/-- **BLS12-381 End-to-End Subgroup-Enforced `CompressionCert` → `KzgPackedPure` + `DeferredFold` Soundness
(`compressionCert_kzgPacked_bls12381_sound`):**
Composes `compressionCert_witness_bls12381` with `verifyAccumulatorV1_sound`, `readChainPolicy_sound`,
`verifyPacked_shplonk_sound`, `encodeAffinePairWords_bls12381_sound` (22-word `5 × u80/u61`),
`foldAccumulator_sound_bls12381`, `BlsPairInSubgroup`, and `Ix.Cert.AiurCompression.bls12381_foldStep_sound`! -/
theorem compressionCert_kzgPacked_bls12381_sound
    {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : CircuitSchedule} {lp : LoweredProgram}
    {compCfg : CompressionConfig} {lpComp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program Aiur.Library.Field.BLS12381.F}
    {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat}
    (cert : CompressionCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp)
      (compCfg := compCfg) (lpComp := lpComp) prepared i)
    (hAssert : cert.aliasSpec.assertOk = true)
    (hsio : StarkIOWorld prepared.environment.source.world)
    (hkio : KzgIOWorld prepared.environment.source.world)
    {wOrig : World Aiur.Library.Field.BLS12381.F}
    (bridge : CompressionLowerBridge prepared.environment.source.world compCfg
      lp.program.functions wOrig)
    {checkFnName : String} {pubParams : List String}
    {channels : List (WitnessChannelKind × Nat)}
    (hchkQual : hasDoubleColon checkFnName.toList = true)
    (hnd : (pubParams ++ (List.range channels.length).map witnessVarName).Nodup)
    (hwrap : WorldHasFn prepared.environment.source.world (qualified (entryName i)) pubParams
      (qualifyExprF Aiur.Library.Field.BLS12381.F (witnessWrapperBody pubParams channels checkFnName false)))
    {bp : Bls12381BilinearPairing} (M : BLS12381G1Model bp) (anchors : bp.G2 × bp.G2)
    {finalCfg : FinalConfig} {key : PackedKey} {stmtLow stmtHigh : Nat}
    {pub : List (SourceValue Aiur.Library.Field.BLS12381.F)}
    (hSpec : ∀ (pubArgs : List (SourceValue Aiur.Library.Field.BLS12381.F))
      (h1 h2 : Heap Aiur.Library.Field.BLS12381.F)
      (wPtrs : List (SourceValue Aiur.Library.Field.BLS12381.F)) (ws : List (List UInt8)),
      List.Forall₂ (ByteStreamRel h1) ws wPtrs →
      EvalFn wOrig checkFnName (pubArgs ++ wPtrs) h1 (.field 1) h2 →
      pubArgs = pub →
      ∃ polB claimsB proofB : List UInt8,
        ws = [polB, claimsB, proofB] ∧
        (verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh
          (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).ok = 1 ∧
        bls12381DeferredVal bp anchors
          (M.toG (verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh
            (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).a,
           M.toG (verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh
            (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).b) = 1)
    {rom : Aiur.WidthROM Aiur.Library.Field.BLS12381.F} (valid : rom.Valid)
    {wires : List (Aiur.WireValue Aiur.Library.Field.BLS12381.F)}
    {output : Aiur.WireValue Aiur.Library.Field.BLS12381.F}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.Field.BLS12381.F}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.Field.BLS12381.F)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues pub))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.tuple [])) :
    ∃ polB claimsB proofB : List UInt8,
      let polBL := uint8ListToByteList polB
      let claimsBL := uint8ListToByteList claimsB
      let proofBL := uint8ListToByteList proofB
      let res := verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh polBL claimsBL proofBL
      let pp := readChainPolicy polBL
      let pc := readClaims bls12381CurveParams claimsBL
      let fv := extractNarrowClaimValues pc.claims finalCfg.headers
      let prev := checkPredecessorNarrow bls12381CurveParams fv.2 finalCfg.policyDigest finalCfg.stage
        (statementFromLimbs stmtLow stmtHigh).2
      let vr := verifyPacked bls12381CurveParams key (readPackedProof bls12381CurveParams proofBL).proof pc.claims
      stmtLow < 2 ^ 128 ∧ stmtHigh < 2 ^ 128 ∧
      digestWordsToList (statementFromLimbs stmtLow stmtHigh).2 = unpackLimbsToU32Words stmtLow stmtHigh ∧
      (chainPolicyToCert pp.policy).WellFormed ∧
      (chainPolicyToCert pp.policy).encode = polB ∧
      seedBindsPackedKey bls12381CurveParams key.seed key.circuits key.fixed = 1 ∧
      fListLen res.affineWords = 22 ∧
      res.a.x < bls12381FqModulus ∧ res.a.y < bls12381FqModulus ∧
      res.b.x < bls12381FqModulus ∧ res.b.y < bls12381FqModulus ∧
      BlsPairInSubgroup bp (M.toG res.a, M.toG res.b) ∧
      ∃ w : BLS12381Fr,
        (M.toG res.a, M.toG res.b) =
          bls12381FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b) ∧
        ((bls12381DeferredVal bp anchors (M.toG vr.a, M.toG vr.b) = 1 ∧
          bls12381DeferredVal bp anchors (M.toG prev.2.1, M.toG prev.2.2) = 1) ∨
         (bls12381DeferredVal bp anchors
            (bls12381FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b)) = 1 ∧
          (Finset.univ.filter fun w' : BLS12381Fr =>
            bls12381DeferredVal bp anchors
              (bls12381FoldStep bp w' (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b)) = 1).card ≤ 1)) := by
  obtain ⟨ws, _, _, hres⟩ :=
    compressionCert_witness_bls12381 cert hAssert hsio hkio bridge hchkQual hnd hwrap
      (Spec := fun pubArgs ws => pubArgs = pub →
        ∃ polB claimsB proofB : List UInt8,
          ws = [polB, claimsB, proofB] ∧
          (verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh
            (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).ok = 1 ∧
          bls12381DeferredVal bp anchors
            (M.toG (verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh
              (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).a,
             M.toG (verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh
              (uint8ListToByteList polB) (uint8ListToByteList claimsB) (uint8ListToByteList proofB)).b) = 1)
      hSpec valid signed rooted outside bound checked arguments decoded
  obtain ⟨polB, claimsB, proofB, _, hAcc, hTerm⟩ := hres rfl
  set polBL := uint8ListToByteList polB
  set claimsBL := uint8ListToByteList claimsB
  set proofBL := uint8ListToByteList proofB
  set res := verifyAccumulatorV1 bls12381CurveParams finalCfg key stmtLow stmtHigh polBL claimsBL proofBL
  set stmt := (statementFromLimbs stmtLow stmtHigh).2
  set pc := readClaims bls12381CurveParams claimsBL
  set fv := extractNarrowClaimValues pc.claims finalCfg.headers
  set prev := checkPredecessorNarrow bls12381CurveParams fv.2 finalCfg.policyDigest finalCfg.stage stmt
  set vr := verifyPacked bls12381CurveParams key (readPackedProof bls12381CurveParams proofBL).proof pc.claims
  have ⟨hfrPos, hfrLt⟩ := bls12381CurveParams_frMod_bounds
  obtain ⟨hlowLt, hhighLt, hunpack, _, _, hppOk, _, _, _, hpAV, hpBV, _, hvrOk, hfdOk, hpairEq, haffEq⟩ :=
    verifyAccumulatorV1_sound hAcc
  have hpolS := readChainPolicy_sound hppOk
  have hpolEnc : (chainPolicyToCert (readChainPolicy polBL).policy).encode = polB := by
    rw [hpolS.2.2.2.2.2.2.2.2.2.2]
    exact byteListToUInt8List_uint8ListToByteList polB
  obtain ⟨hkb, hvraV, hvrbV, _⟩ :=
    verifyPacked_shplonk_sound M.toG1GroupModel M.valid_of_g1Valid hfrPos hfrLt hvrOk
  obtain ⟨_, _, hfdaV, hfdbV, hsubOut, hfdStep⟩ :=
    foldAccumulator_sound_bls12381 M (M.valid_of_g1Valid _ hpAV) (M.valid_of_g1Valid _ hpBV)
      hvraV hvrbV hfdOk
  have haEq : res.a =
      (foldAccumulator bls12381CurveParams vr.transcript finalCfg.policyDigest stmt finalCfg.stage finalCfg.keyDigest
        prev.2.1 prev.2.2 vr.a vr.b).2.1 :=
    congrArg Prod.fst hpairEq
  have hbEq : res.b =
      (foldAccumulator bls12381CurveParams vr.transcript finalCfg.policyDigest stmt finalCfg.stage finalCfg.keyDigest
        prev.2.1 prev.2.2 vr.a vr.b).2.2 :=
    congrArg Prod.snd hpairEq
  have haffS := encodeAffinePairWords_bls12381_sound (A := res.a) (B := res.b)
    (by rw [haEq]; exact M.g1Valid_of_valid _ hfdaV)
    (by rw [hbEq]; exact M.g1Valid_of_valid _ hfdbV)
  set w : BLS12381Fr :=
    ((foldWeight bls12381CurveParams vr.transcript finalCfg.policyDigest stmt finalCfg.stage finalCfg.keyDigest
      prev.2.1 prev.2.2 vr.a vr.b).2 : BLS12381Fr)
  have hstepEq :
      (M.toG res.a, M.toG res.b) =
      bls12381FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b) := by
    rw [haEq, hbEq, hfdStep]
  have hTerm' : bls12381DeferredVal bp anchors
      (bls12381FoldStep bp w (M.toG prev.2.1, M.toG prev.2.2) (M.toG vr.a, M.toG vr.b)) = 1 := by
    rw [← hstepEq]; exact hTerm
  have hprevSub : BlsPairInSubgroup bp (M.toG prev.2.1, M.toG prev.2.2) :=
    ⟨M.inSubgroup_of_valid (M.valid_of_g1Valid _ hpAV), M.inSubgroup_of_valid (M.valid_of_g1Valid _ hpBV)⟩
  have hcurSub : BlsPairInSubgroup bp (M.toG vr.a, M.toG vr.b) :=
    ⟨M.inSubgroup_of_valid hvraV, M.inSubgroup_of_valid hvrbV⟩
  have hfold := bls12381_foldStep_sound bp anchors w hprevSub hcurSub hTerm'
  exact ⟨polB, claimsB, proofB, hlowLt, hhighLt, hunpack, hpolS.2.2.2.2.2.2.2.2.2.1, hpolEnc,
    hkb, by rw [haffEq]; exact haffS.1, haffS.2.1, haffS.2.2.1, haffS.2.2.2.1, haffS.2.2.2.2.1,
    by rw [haEq, hbEq]; exact hsubOut, w, hstepEq, hfold.2⟩

end CompressionCertBridge

/-! ## Section 7: Axiom Fences (`⊆ [propext, Classical.choice, Quot.sound]`)

Every headline theorem across Sections 1–6 is machine-fenced below with
`#guard_msgs (whitespace := lax) in #print axioms`, certifying that ZERO `sorry`,
`admit`, custom `axiom`, `native_decide` (`Lean.ofReduceBool`), or `bv_decide`
dependencies appear anywhere in the proof graph. -/

section AxiomFences

-- Section 1: Base-field (`Fq`), scalar-field (`Fr`), and tower (`Fq2`/`Fq6`/`Fq12`) arithmetic
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fqAddMod_lt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fqAddMod_lt
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fqSubMod_lt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fqSubMod_lt
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fqMulMod_lt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms fqMulMod_lt
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fqInvMod_cast_eq_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fqInvMod_cast_eq_inv
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fp2Mul_hom' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp2Mul_hom
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fp2Inv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp2Inv_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fp6Mul_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp6Mul_hom
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fp12Mul_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp12Mul_hom
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fp12Pow_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp12Pow_hom

-- Section 2: Curve equation, strict infinity, affine `u80` codecs, BLS12-381 Bowe subgroup & torsion rejection
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1OnCurve_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1OnCurve_iff
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1Validate_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1Validate_iff
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1Validate_rejects_malformed_infinity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1Validate_rejects_malformed_infinity
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.decodeAffineG1BN254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeAffineG1BN254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.decodeAffineG1BLS12381_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeAffineG1BLS12381_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.bls12381_g1Validate_prime_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bls12381_g1Validate_prime_order
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.bls12381_torsion_witness_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms bls12381_torsion_witness_rejected
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.bls12381_threeTorsion_zero_two_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bls12381_threeTorsion_zero_two_rejected
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.bls12381_circuit_torsion_rejected' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms bls12381_circuit_torsion_rejected

-- Section 3: Miller loop, Frobenius, residue-witnessed final exponentiation, and 2-pairing checks
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.millerLoop2Prepared_eq_millerLoop2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms millerLoop2Prepared_eq_millerLoop2
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.fp12Frob_field_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fp12Frob_field_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyFinalExpWitness_bn254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyFinalExpWitness_bn254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyFinalExpWitnessFp6_bn254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyFinalExpWitnessFp6_bn254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyFinalExpTableBN254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyFinalExpTableBN254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyFinalExpWitness_bls12381_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyFinalExpWitness_bls12381_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyFinalExpWitnessFp6_bls12381_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyFinalExpWitnessFp6_bls12381_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.pairingCheckAffineBN254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairingCheckAffineBN254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.pairingCheckAffineTableBN254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairingCheckAffineTableBN254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.pairingCheckAffineBLS12381_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairingCheckAffineBLS12381_sound

-- Section 4: Canonical wire decoding, trailing-byte rejection, and key-bound transcript soundness
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1OnCurve_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1OnCurve_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1ValidPoint_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1ValidPoint_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1ToBytes_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1ToBytes_inj
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1FromBytes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1FromBytes_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1FromBytes_injective_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1FromBytes_injective_finite
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.kzgWire_bls12381_torsion_rejected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms kzgWire_bls12381_torsion_rejected
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readClaims_rejects_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readClaims_rejects_trailing
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readChainPolicy_rejects_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readChainPolicy_rejects_trailing
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readPackedCommitment_rejects_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPackedCommitment_rejects_trailing
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readPackedKey_rejects_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPackedKey_rejects_trailing
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readPackedProof_rejects_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPackedProof_rejects_trailing
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readChainPolicy_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readChainPolicy_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readPackedCommitment_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPackedCommitment_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readPackedKey_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPackedKey_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.readPackedProof_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms readPackedProof_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.domainSeparators_exact_ascii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms domainSeparators_exact_ascii
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.seedBindsPackedKey_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms seedBindsPackedKey_iff
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.packedKeySeedSuffix_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packedKeySeedSuffix_injective
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.computePackedKeyDigest_binds_vk_and_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms computePackedKeyDigest_binds_vk_and_fixed
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.observeKey_structure' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms observeKey_structure
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyPacked_key_binding_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyPacked_key_binding_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyPacked_rejects_unbound_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyPacked_rejects_unbound_seed
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyPacked_rejects_invalid_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyPacked_rejects_invalid_fixed
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyPacked_rejects_bls12381_torsion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyPacked_rejects_bls12381_torsion

-- Section 5: SHPLONK MSM, opening reduction, affine `u80` pair words, and two-stage `DeferredFold` bridge
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.g1Msm_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms g1Msm_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.frPowU32_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms frPowU32_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.weighSinglePack_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weighSinglePack_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.reducePcs_shplonk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reducePcs_shplonk_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyPacked_shplonk_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyPacked_shplonk_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.statementFromLimbs_eq_unpack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms statementFromLimbs_eq_unpack
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.decodeAffinePointWords_encodeAffinePointWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeAffinePointWords_encodeAffinePointWords
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.encodeAffinePairWords_bn254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodeAffinePairWords_bn254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.encodeAffinePairWords_bls12381_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodeAffinePairWords_bls12381_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.foldAccumulator_sound_bn254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldAccumulator_sound_bn254
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.foldAccumulator_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms foldAccumulator_sound_bls12381
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.stepV1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stepV1_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyAccumulatorV1_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAccumulatorV1_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.verifyAccumulatorV1_bnDigest_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms verifyAccumulatorV1_bnDigest_eq
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.twoStage_kzgPacked_deferred_fold_sound_bn254' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoStage_kzgPacked_deferred_fold_sound_bn254
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.twoStage_kzgPacked_deferred_fold_sound_bls12381' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms twoStage_kzgPacked_deferred_fold_sound_bls12381

-- Section 6: End-to-end `CompressionIntrinsicsProof.CompressionCert` composition
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.compressionCert_pairingCheck_bn254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compressionCert_pairingCheck_bn254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.compressionCert_pairingCheck_bls12381_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compressionCert_pairingCheck_bls12381_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.compressionCert_kzgPacked_bn254_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compressionCert_kzgPacked_bn254_sound
/-- info: 'IxCCAiur.Compression.KzgPairingSpec.compressionCert_kzgPacked_bls12381_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compressionCert_kzgPacked_bls12381_sound

end AxiomFences

end IxCCAiur.Compression.KzgPairingSpec

