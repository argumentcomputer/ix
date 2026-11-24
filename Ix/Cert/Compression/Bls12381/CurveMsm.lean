import Ix.Cert.Compression.Bls12381.Field

/-! # Non-Native `BLS12381::G1` Curve, Mandatory Subgroup Check & 4-Bit Straus MSM Soundness

This module formalizes and proves the soundness of the BLS12-381 $G_1$ affine curve gadget
(`crates/proof-compression/src/recursive/native_curve.rs`), the **mandatory $G_1$ prime-order
subgroup check** (`Affine::subgroup_check`, absent on cofactor-1 BN254), and the 64-round
4-bit windowed Straus multi-scalar multiplication gadget (`native_msm.rs`):

1. **BLS12-381 $G_1$ Short Weierstrass Curve & `PointInput` (`BLS12381G1`, `bls12381_pointInput_sound`)**:
   - Models $E(\mathbb{F}_q) : y^2 \equiv x^3 + 4 \pmod q$ over 5×80-bit `Bls12381FqLimbs`.
2. **Incomplete Affine Addition, Doubling & Complete Addition**:
   - `bls12381_affine_add_sound`, `bls12381_affine_double_sound`, `bls12381_add_complete_sound`.
3. **64-Round 4-Bit Windowed Straus MSM with Non-Exceptional Offset**:
   - `bls12381_straus_loop_invariant`, `bls12381_msm_sound`,
     `bls12381_msm_shifted_correction_sound`.
4. **Concrete Mathlib `WeierstrassCurve.Affine` Instantiation (`bls12381Curve`, `bls12381G1`)**:
   - Discharges `hGroupAdd`, `hGroupDbl`, and `hOpp` unconditionally via
     `bls12381_affineAddSpec_eq`, `bls12381_affineDoubleSpec_eq`, and
     `bls12381_sameX_neY_imp_neg`.
5. **Mandatory BLS12-381 $G_1$ Prime-Order Subgroup Check & Constructive Negative Control**:
   - Because BLS12-381 $G_1$ has non-trivial cofactor $h_1 = (u+1)^2 / 3$ (`3 ∣ h_1`),
     membership on $y^2 = x^3 + 4$ does **not** imply membership in the prime-order subgroup
     $G_1 = E(\mathbb{F}_q)[r]$.
   - Proves soundness of the GLV endomorphism check `[u^2] P = -φ(P)`
     (`bls12381_endoSubgroupCheck_sound`, `bls12381_affineSubgroupSpec_sound`),
     proves `bls12381Generator_inPrimeSubgroup` unconditionally, proves subgroup closure under
     `0`, `add`, `neg`, `smul`, and `bls12381MsmEval` (`bls12381_msm_inPrimeSubgroup`),
     and exhibits the elementary 3-torsion point `T = (0, 2)` on $y^2 = x^3 + 4$ which is
     canonical and on-curve yet fails `InPrimeSubgroup` and `EndoSubgroupChecked`
     (`bls12381_torsionPoint_not_inPrimeSubgroup`, `bls12381_torsionPoint_fails_endoCheck`).
-/

namespace Ix.Cert.Compression.Bls12381.CurveMsm

open Ix.Cert.Compression.Bls12381.Field

set_option exponentiation.threshold 512

/-! ## 1. BLS12-381 $G_1$ Short Weierstrass Curve & `PointInput` -/

/-- Non-native affine coordinates $(x, y)$ represented as pairs of 5-limb `Bls12381FqLimbs`. -/
structure Bls12381AffineCoords where
  x : Bls12381FqLimbs
  y : Bls12381FqLimbs
  deriving DecidableEq, Repr, Inhabited

/-- The BLS12-381 $G_1$ curve equation $y^2 \equiv x^3 + 4 \pmod q$. -/
def Bls12381OnCurve (p : Bls12381AffineCoords) : Prop :=
  (evalLimbsInt p.x * evalLimbsInt p.x * evalLimbsInt p.x + 4 -
    evalLimbsInt p.y * evalLimbsInt p.y) % (bls12381FqModulus : ℤ) = 0

/-- Both coordinates of `p` are canonical ($< q$). -/
def Bls12381AffineCoords.Canonical (p : Bls12381AffineCoords) : Prop :=
  p.x.Canonical ∧ p.y.Canonical

/-- Wire representation of a possibly-infinite BLS12-381 $G_1$ point. -/
structure Bls12381PointInputCoords where
  point : Bls12381AffineCoords
  infinity : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Abstract abelian group and curve interface `BLS12381G1` over $\mathbb{F}_q$
($y^2 = x^3 + 4 \pmod q$). -/
structure BLS12381G1 where
  Point : Type
  zero : Point
  add : Point → Point → Point
  neg : Point → Point
  smul : Nat → Point → Point
  generator : Point
  fromAffine : Bls12381AffineCoords → Point
  add_assoc : ∀ a b c : Point, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : Point, add a b = add b a
  zero_add : ∀ a : Point, add zero a = a
  add_zero : ∀ a : Point, add a zero = a
  add_neg_cancel : ∀ a : Point, add a (neg a) = zero
  neg_add_cancel : ∀ a : Point, add (neg a) a = zero
  smul_zero : ∀ a : Point, smul 0 a = zero
  smul_zero_point : ∀ n : Nat, smul n zero = zero
  smul_one : ∀ a : Point, smul 1 a = a
  smul_add : ∀ (m n : Nat) (a : Point), smul (m + n) a = add (smul m a) (smul n a)
  smul_distrib : ∀ (n : Nat) (a b : Point), smul n (add a b) = add (smul n a) (smul n b)
  smul_smul : ∀ (m n : Nat) (a : Point), smul m (smul n a) = smul (m * n) a

instance (G : BLS12381G1) : Std.Associative G.add := ⟨G.add_assoc⟩
instance (G : BLS12381G1) : Std.Commutative G.add := ⟨G.add_comm⟩

/-- Interpretation of a `Bls12381PointInputCoords` in `G : BLS12381G1`. -/
def Bls12381PointInputCoords.eval (G : BLS12381G1) (p : Bls12381PointInputCoords) : G.Point :=
  if p.infinity = 1 then G.zero else G.fromAffine p.point

/-- **Prime-order subgroup membership predicate (`BLS12381G1.InPrimeSubgroup`):**
$P \in E(\mathbb{F}_q)[r] \iff [r] P = \mathcal{O}$. -/
def BLS12381G1.InPrimeSubgroup (G : BLS12381G1) (P : G.Point) : Prop :=
  G.smul bls12381FrModulus P = G.zero

/-- **`PointInput` Unpacking & On-Curve Soundness (`bls12381_pointInput_sound`)**. -/
theorem bls12381_pointInput_sound
    (p : Bls12381PointInputCoords) (xx : Bls12381FqLimbs)
    (hBool : p.infinity = 0 ∨ p.infinity = 1)
    (hCanonX : p.point.x.Canonical)
    (hCanonY : p.point.y.Canonical)
    (hZeroX : p.infinity = 1 → p.point.x = ⟨0, 0, 0, 0, 0⟩)
    (hZeroY : p.infinity = 1 → p.point.y = ⟨0, 0, 0, 0, 0⟩)
    (hMulXX : p.infinity = 0 →
      Bls12381FqRelationHolds (evalLimbsInt p.point.x * evalLimbsInt p.point.x - evalLimbsInt xx))
    (hCurveRel : p.infinity = 0 →
      Bls12381FqRelationHolds (evalLimbsInt xx * evalLimbsInt p.point.x -
        evalLimbsInt p.point.y * evalLimbsInt p.point.y + 4)) :
    (p.infinity = 0 ∨ p.infinity = 1) ∧
    (p.infinity = 0 → p.point.Canonical ∧ Bls12381OnCurve p.point) ∧
    (p.infinity = 1 → evalLimbs p.point.x = 0 ∧ evalLimbs p.point.y = 0) := by
  refine ⟨hBool, ?_, ?_⟩
  · intro hNotInf
    refine ⟨⟨hCanonX, hCanonY⟩, ?_⟩
    have hM := hMulXX hNotInf
    have hC := hCurveRel hNotInf
    unfold Bls12381FqRelationHolds Bls12381OnCurve at *
    have hSub :
        evalLimbsInt p.point.x * evalLimbsInt p.point.x * evalLimbsInt p.point.x + 4 -
          evalLimbsInt p.point.y * evalLimbsInt p.point.y =
        (evalLimbsInt p.point.x * evalLimbsInt p.point.x - evalLimbsInt xx) * evalLimbsInt p.point.x +
        (evalLimbsInt xx * evalLimbsInt p.point.x -
          evalLimbsInt p.point.y * evalLimbsInt p.point.y + 4) := by ring
    rw [hSub, _root_.Int.add_emod, _root_.Int.mul_emod, hM, _root_.Int.zero_mul,
      _root_.Int.zero_emod, _root_.Int.zero_add, hC, _root_.Int.zero_emod]
  · intro hInf
    rw [hZeroX hInf, hZeroY hInf]
    unfold evalLimbs
    simp

/-! ## 2. Incomplete Affine Addition, Doubling & Complete Addition Soundness -/

/-- Specification of the affine chord addition equations modulo `bls12381FqModulus`. -/
def Bls12381AffineAddSpec (p1 p2 p3 : Bls12381AffineCoords) (slope : Bls12381FqLimbs) : Prop :=
  (evalLimbsInt p2.x - evalLimbsInt p1.x) % (bls12381FqModulus : ℤ) ≠ 0 ∧
  (evalLimbsInt slope * (evalLimbsInt p2.x - evalLimbsInt p1.x) -
    (evalLimbsInt p2.y - evalLimbsInt p1.y)) % (bls12381FqModulus : ℤ) = 0 ∧
  (evalLimbsInt p3.x + evalLimbsInt p1.x + evalLimbsInt p2.x -
    evalLimbsInt slope * evalLimbsInt slope) % (bls12381FqModulus : ℤ) = 0 ∧
  (evalLimbsInt p3.y + evalLimbsInt p1.y -
    evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bls12381FqModulus : ℤ) = 0

/-- Specification of the affine tangent doubling equations modulo `bls12381FqModulus`. -/
def Bls12381AffineDoubleSpec (p1 p3 : Bls12381AffineCoords) (slope : Bls12381FqLimbs) : Prop :=
  (2 * evalLimbsInt p1.y * evalLimbsInt slope -
    3 * evalLimbsInt p1.x * evalLimbsInt p1.x) % (bls12381FqModulus : ℤ) = 0 ∧
  (evalLimbsInt p3.x + 2 * evalLimbsInt p1.x -
    evalLimbsInt slope * evalLimbsInt slope) % (bls12381FqModulus : ℤ) = 0 ∧
  (evalLimbsInt p3.y + evalLimbsInt p1.y -
    evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bls12381FqModulus : ℤ) = 0

private lemma emod_neg_zero {a m : ℤ} (h : a % m = 0) : (-a) % m = 0 := by
  rw [← _root_.Int.dvd_iff_emod_eq_zero] at h ⊢
  exact dvd_neg.mpr h

/-- **Incomplete Affine Addition Soundness (`bls12381_affine_add_sound`)**. -/
theorem bls12381_affine_add_sound
    (G : BLS12381G1)
    (p1 p2 p3 : Bls12381AffineCoords) (inv slope : Bls12381FqLimbs)
    (hInv : Bls12381FqRelationHolds (evalLimbsInt p2.x * evalLimbsInt inv - evalLimbsInt p1.x * evalLimbsInt inv - 1))
    (hSlope : Bls12381FqRelationHolds (evalLimbsInt slope * evalLimbsInt p2.x - evalLimbsInt slope * evalLimbsInt p1.x -
      evalLimbsInt p2.y + evalLimbsInt p1.y))
    (hSumX : Bls12381FqRelationHolds (evalLimbsInt slope * evalLimbsInt slope -
      evalLimbsInt p1.x - evalLimbsInt p2.x - evalLimbsInt p3.x))
    (hSumY : Bls12381FqRelationHolds (evalLimbsInt slope * evalLimbsInt p1.x -
      evalLimbsInt slope * evalLimbsInt p3.x - evalLimbsInt p1.y - evalLimbsInt p3.y))
    (hGroupAdd : Bls12381AffineAddSpec p1 p2 p3 slope →
      G.fromAffine p3 = G.add (G.fromAffine p1) (G.fromAffine p2)) :
    Bls12381AffineAddSpec p1 p2 p3 slope ∧
    G.fromAffine p3 = G.add (G.fromAffine p1) (G.fromAffine p2) := by
  unfold Bls12381FqRelationHolds at *
  have hFactorInv :
      evalLimbsInt p2.x * evalLimbsInt inv - evalLimbsInt p1.x * evalLimbsInt inv - 1 =
      (evalLimbsInt p2.x - evalLimbsInt p1.x) * evalLimbsInt inv + 0 - 1 := by ring
  have hNonZero : (evalLimbsInt p2.x - evalLimbsInt p1.x) % (bls12381FqModulus : ℤ) ≠ 0 := by
    have hInvZero := bls12381_fq_inv_or_zero_sound p2.x p1.x inv 0 (Or.inl rfl)
      (by unfold Bls12381FqRelationHolds; rw [← hFactorInv]; exact hInv)
      (by unfold Bls12381FqRelationHolds; simp)
      (by unfold Bls12381FqRelationHolds; simp)
    exact (hInvZero.2 rfl).2
  have hSpecSlope :
      (evalLimbsInt slope * (evalLimbsInt p2.x - evalLimbsInt p1.x) -
        (evalLimbsInt p2.y - evalLimbsInt p1.y)) % (bls12381FqModulus : ℤ) = 0 := by
    have hEq :
        evalLimbsInt slope * (evalLimbsInt p2.x - evalLimbsInt p1.x) -
          (evalLimbsInt p2.y - evalLimbsInt p1.y) =
        evalLimbsInt slope * evalLimbsInt p2.x - evalLimbsInt slope * evalLimbsInt p1.x -
          evalLimbsInt p2.y + evalLimbsInt p1.y := by ring
    rw [hEq]; exact hSlope
  have hSpecX :
      (evalLimbsInt p3.x + evalLimbsInt p1.x + evalLimbsInt p2.x -
        evalLimbsInt slope * evalLimbsInt slope) % (bls12381FqModulus : ℤ) = 0 := by
    have hEq :
        evalLimbsInt p3.x + evalLimbsInt p1.x + evalLimbsInt p2.x -
          evalLimbsInt slope * evalLimbsInt slope =
        -(evalLimbsInt slope * evalLimbsInt slope -
          evalLimbsInt p1.x - evalLimbsInt p2.x - evalLimbsInt p3.x) := by ring
    rw [hEq]; exact emod_neg_zero hSumX
  have hSpecY :
      (evalLimbsInt p3.y + evalLimbsInt p1.y -
        evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bls12381FqModulus : ℤ) = 0 := by
    have hEq :
        evalLimbsInt p3.y + evalLimbsInt p1.y -
          evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x) =
        -(evalLimbsInt slope * evalLimbsInt p1.x -
          evalLimbsInt slope * evalLimbsInt p3.x - evalLimbsInt p1.y - evalLimbsInt p3.y) := by ring
    rw [hEq]; exact emod_neg_zero hSumY
  have hSpec : Bls12381AffineAddSpec p1 p2 p3 slope := ⟨hNonZero, hSpecSlope, hSpecX, hSpecY⟩
  exact ⟨hSpec, hGroupAdd hSpec⟩

/-- **Incomplete Affine Doubling Soundness (`bls12381_affine_double_sound`)**. -/
theorem bls12381_affine_double_sound
    (G : BLS12381G1)
    (p1 p3 : Bls12381AffineCoords) (slope : Bls12381FqLimbs)
    (hSlope : Bls12381FqRelationHolds (2 * evalLimbsInt p1.y * evalLimbsInt slope -
      3 * evalLimbsInt p1.x * evalLimbsInt p1.x))
    (hDblX : Bls12381FqRelationHolds (evalLimbsInt slope * evalLimbsInt slope -
      2 * evalLimbsInt p1.x - evalLimbsInt p3.x))
    (hDblY : Bls12381FqRelationHolds (evalLimbsInt slope * evalLimbsInt p1.x -
      evalLimbsInt slope * evalLimbsInt p3.x - evalLimbsInt p1.y - evalLimbsInt p3.y))
    (hGroupDbl : Bls12381AffineDoubleSpec p1 p3 slope →
      G.fromAffine p3 = G.smul 2 (G.fromAffine p1)) :
    Bls12381AffineDoubleSpec p1 p3 slope ∧
    G.fromAffine p3 = G.smul 2 (G.fromAffine p1) ∧
    G.fromAffine p3 = G.add (G.fromAffine p1) (G.fromAffine p1) := by
  unfold Bls12381FqRelationHolds at *
  have hSpecX :
      (evalLimbsInt p3.x + 2 * evalLimbsInt p1.x -
        evalLimbsInt slope * evalLimbsInt slope) % (bls12381FqModulus : ℤ) = 0 := by
    have hEq :
        evalLimbsInt p3.x + 2 * evalLimbsInt p1.x - evalLimbsInt slope * evalLimbsInt slope =
        -(evalLimbsInt slope * evalLimbsInt slope - 2 * evalLimbsInt p1.x - evalLimbsInt p3.x) := by
      ring
    rw [hEq]; exact emod_neg_zero hDblX
  have hSpecY :
      (evalLimbsInt p3.y + evalLimbsInt p1.y -
        evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bls12381FqModulus : ℤ) = 0 := by
    have hEq :
        evalLimbsInt p3.y + evalLimbsInt p1.y -
          evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x) =
        -(evalLimbsInt slope * evalLimbsInt p1.x -
          evalLimbsInt slope * evalLimbsInt p3.x - evalLimbsInt p1.y - evalLimbsInt p3.y) := by ring
    rw [hEq]; exact emod_neg_zero hDblY
  have hSpec : Bls12381AffineDoubleSpec p1 p3 slope := ⟨hSlope, hSpecX, hSpecY⟩
  have hSmul2 := hGroupDbl hSpec
  have hAdd : G.smul 2 (G.fromAffine p1) = G.add (G.fromAffine p1) (G.fromAffine p1) := by
    have h11 : (2 : Nat) = 1 + 1 := rfl
    rw [h11, G.smul_add, G.smul_one]
  exact ⟨hSpec, hSmul2, hSmul2.trans hAdd⟩

/-- **Complete Affine Addition Soundness (`bls12381_add_complete_sound`)**. -/
theorem bls12381_add_complete_sound
    (G : BLS12381G1)
    (p1 p2 ordinary doubled : Bls12381AffineCoords)
    (sameX sameY : Bool)
    (hOrd : sameX = false → G.fromAffine ordinary = G.add (G.fromAffine p1) (G.fromAffine p2))
    (hDbl : sameX = true → sameY = true →
      G.fromAffine doubled = G.add (G.fromAffine p1) (G.fromAffine p2))
    (hOpp : sameX = true → sameY = false →
      G.fromAffine p2 = G.neg (G.fromAffine p1)) :
    let outPoint :=
      if sameX then
        (if sameY then doubled else ⟨⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩⟩)
      else ordinary
    let outInf := if sameX && !sameY then 1 else 0
    Bls12381PointInputCoords.eval G ⟨outPoint, outInf⟩ =
      G.add (G.fromAffine p1) (G.fromAffine p2) := by
  dsimp only [Bls12381PointInputCoords.eval]
  cases hX : sameX
  · simp [hOrd hX]
  · cases hY : sameY
    · simp [hOpp hX hY, G.add_neg_cancel]
    · simp [hDbl hX hY]

/-! ## 3. 64-Round 4-Bit Windowed Straus MSM (`native_msm.rs`) -/

/-- Multi-scalar multiplication evaluation $\bigoplus_{i=0}^{n-1} [s_i] P_i$ over `G : BLS12381G1`. -/
def bls12381MsmEval (G : BLS12381G1) : List Nat → List G.Point → G.Point
  | [], _ => G.zero
  | _, [] => G.zero
  | s :: ss, p :: ps => G.add (G.smul s p) (bls12381MsmEval G ss ps)

/-- One round of the 4-bit Straus loop (`native_msm.rs:333`): four doublings followed by adding
$\bigoplus_i [\text{win}_i] P_i$. -/
def bls12381StrausStep (G : BLS12381G1) (points : List G.Point)
    (acc : G.Point) (winRow : List Nat) : G.Point :=
  G.add (G.smul 16 acc) (bls12381MsmEval G winRow points)

/-- Execution of `rounds` starting at non-exceptional offset `h : G.Point`. -/
def bls12381StrausLoop (G : BLS12381G1) (points : List G.Point)
    (h : G.Point) (rounds : List (List Nat)) : G.Point :=
  rounds.foldl (bls12381StrausStep G points) h

/-- Accumulating 4-bit window rows into full scalar values (64 windows cover 256 bits > 255-bit `Fr`). -/
def bls12381FoldWindowRows (numBases : Nat) (rounds : List (List Nat)) : List Nat :=
  rounds.foldl (fun acc row => List.zipWith (fun s w => 16 * s + w) acc row)
    (List.replicate numBases 0)

theorem bls12381FrModulus_lt_sixteen_pow_64 :
    bls12381FrModulus < 16 ^ 64 := by decide

theorem bls12381MsmEval_horner_step (G : BLS12381G1) :
    ∀ (scalars winRow : List Nat) (points : List G.Point),
      scalars.length = points.length →
      winRow.length = points.length →
      bls12381MsmEval G (List.zipWith (fun s w => 16 * s + w) scalars winRow) points =
        G.add (G.smul 16 (bls12381MsmEval G scalars points)) (bls12381MsmEval G winRow points)
  | [], [], [], _, _ => by
    simp [bls12381MsmEval, G.smul_zero_point, G.add_zero]
  | s :: ss, w :: ws, p :: ps, hs, hw => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hs hw
    simp only [List.zipWith_cons_cons, bls12381MsmEval]
    rw [bls12381MsmEval_horner_step G ss ws ps hs hw]
    rw [G.smul_add, ← G.smul_smul 16 s p, G.smul_distrib]
    ac_rfl
  | [], _ :: _, _ :: _, hs, _ => by cases hs
  | _ :: _, [], _ :: _, _, hw => by cases hw
  | _ :: _, _ :: _, [], hs, _ => by cases hs
  | [], [], _ :: _, hs, _ => by cases hs
  | [], _ :: _, [], _, hw => by cases hw
  | _ :: _, [], [], hs, _ => by cases hs

theorem bls12381MsmEval_replicate_zero (G : BLS12381G1) :
    ∀ (points : List G.Point),
      bls12381MsmEval G (List.replicate points.length 0) points = G.zero
  | [] => rfl
  | p :: ps => by
    simp only [List.length_cons, List.replicate_succ, bls12381MsmEval, G.smul_zero, G.zero_add]
    exact bls12381MsmEval_replicate_zero G ps

/-- **Straus Window Loop Invariant (`bls12381_straus_loop_invariant`)**. -/
theorem bls12381_straus_loop_invariant
    (G : BLS12381G1) (points : List G.Point) (h : G.Point)
    (rounds : List (List Nat))
    (hRows : ∀ row ∈ rounds, row.length = points.length) :
    bls12381StrausLoop G points h rounds =
      G.add (G.smul (16 ^ rounds.length) h)
        (bls12381MsmEval G (bls12381FoldWindowRows points.length rounds) points) := by
  unfold bls12381StrausLoop bls12381FoldWindowRows
  have hGen :
      ∀ (accScalar : List Nat) (accPoint : G.Point) (k : Nat) (rem : List (List Nat)),
        accScalar.length = points.length →
        (∀ row ∈ rem, row.length = points.length) →
        accPoint = G.add (G.smul (16 ^ k) h) (bls12381MsmEval G accScalar points) →
        rem.foldl (bls12381StrausStep G points) accPoint =
          G.add (G.smul (16 ^ (k + rem.length)) h)
            (bls12381MsmEval G
              (rem.foldl (fun a r => List.zipWith (fun s w => 16 * s + w) a r) accScalar) points) := by
    intro accScalar accPoint k rem
    induction rem generalizing accScalar accPoint k with
    | nil =>
      intro _ _ hAcc
      simp [hAcc]
    | cons row rest ih =>
      intro hAccLen hRemRows hAcc
      simp only [List.foldl_cons, List.length_cons]
      have hRowLen : row.length = points.length := hRemRows row (List.Mem.head _)
      have hNextLen : (List.zipWith (fun s w => 16 * s + w) accScalar row).length = points.length := by
        simp [hAccLen, hRowLen]
      have hStepEq :
          bls12381StrausStep G points accPoint row =
            G.add (G.smul (16 ^ (k + 1)) h)
              (bls12381MsmEval G (List.zipWith (fun s w => 16 * s + w) accScalar row) points) := by
        unfold bls12381StrausStep
        rw [hAcc, G.smul_distrib, G.smul_smul, ← Nat.pow_succ',
          bls12381MsmEval_horner_step G accScalar row points hAccLen hRowLen]
        ac_rfl
      have hGoal := ih (List.zipWith (fun s w => 16 * s + w) accScalar row)
        (bls12381StrausStep G points accPoint row) (k + 1) hNextLen
        (fun r hr => hRemRows r (List.Mem.tail _ hr)) hStepEq
      have hExp : k + 1 + rest.length = k + (rest.length + 1) := by omega
      rw [← hExp]
      exact hGoal
  have hZero := bls12381MsmEval_replicate_zero G points
  have hInit : h = G.add (G.smul (16 ^ 0) h)
      (bls12381MsmEval G (List.replicate points.length 0) points) := by
    rw [Nat.pow_zero, G.smul_one, hZero, G.add_zero]
  simpa using hGen (List.replicate points.length 0) h 0 rounds List.length_replicate hRows hInit

/-- **64-Round 4-Bit Straus MSM Soundness over BLS12-381 (`bls12381_msm_sound`)**. -/
theorem bls12381_msm_sound
    (G : BLS12381G1) (points : List G.Point) (h : G.Point)
    (rounds : List (List Nat))
    (hLen64 : rounds.length = 64)
    (hRows : ∀ row ∈ rounds, row.length = points.length) :
    let acc64 := bls12381StrausLoop G points h rounds
    let scalars := bls12381FoldWindowRows points.length rounds
    acc64 = G.add (G.smul (16 ^ 64) h) (bls12381MsmEval G scalars points) ∧
    G.add acc64 (G.neg (G.smul (16 ^ 64) h)) = bls12381MsmEval G scalars points := by
  dsimp only
  have hInv := bls12381_straus_loop_invariant G points h rounds hRows
  rw [hLen64] at hInv
  refine ⟨hInv, ?_⟩
  rw [hInv]
  calc
    G.add (G.add (G.smul (16 ^ 64) h)
        (bls12381MsmEval G (bls12381FoldWindowRows points.length rounds) points))
        (G.neg (G.smul (16 ^ 64) h))
      = G.add (bls12381MsmEval G (bls12381FoldWindowRows points.length rounds) points)
          (G.add (G.smul (16 ^ 64) h) (G.neg (G.smul (16 ^ 64) h))) := by ac_rfl
    _ = G.add (bls12381MsmEval G (bls12381FoldWindowRows points.length rounds) points) G.zero := by
        rw [G.add_neg_cancel]
    _ = bls12381MsmEval G (bls12381FoldWindowRows points.length rounds) points := by
        rw [G.add_zero]

/-- **Shifted-Digit Correction Cancellation (`bls12381_msm_shifted_correction_sound`)**. -/
theorem bls12381_msm_shifted_correction_sound
    (G : BLS12381G1) (h msmVal baseSum : G.Point) (k c : Nat)
    (hKC : k + c = 16 ^ 64) :
    let sum := G.add h baseSum
    let acc := G.add (G.smul (16 ^ 64) h) (G.add msmVal (G.smul k baseSum))
    let correction := G.add (G.smul k sum) (G.smul c h)
    G.add acc (G.neg correction) = msmVal := by
  dsimp only
  have hCorr :
      G.add (G.smul k (G.add h baseSum)) (G.smul c h) =
        G.add (G.smul (16 ^ 64) h) (G.smul k baseSum) := by
    calc
      G.add (G.smul k (G.add h baseSum)) (G.smul c h)
        = G.add (G.add (G.smul k h) (G.smul c h)) (G.smul k baseSum) := by
          rw [G.smul_distrib]; ac_rfl
      _ = G.add (G.smul (k + c) h) (G.smul k baseSum) := by
          rw [← G.smul_add]
      _ = G.add (G.smul (16 ^ 64) h) (G.smul k baseSum) := by
          rw [hKC]
  rw [hCorr]
  calc
    G.add (G.add (G.smul (16 ^ 64) h) (G.add msmVal (G.smul k baseSum)))
        (G.neg (G.add (G.smul (16 ^ 64) h) (G.smul k baseSum)))
      = G.add msmVal
          (G.add (G.add (G.smul (16 ^ 64) h) (G.smul k baseSum))
            (G.neg (G.add (G.smul (16 ^ 64) h) (G.smul k baseSum)))) := by ac_rfl
    _ = G.add msmVal G.zero := by rw [G.add_neg_cancel]
    _ = msmVal := by rw [G.add_zero]

/-! ## 4. Concrete Mathlib `BLS12381::G1` Weierstrass Curve Instantiation -/

/-- The concrete BLS12-381 short Weierstrass curve $E(\mathbb{F}_q) : y^2 = x^3 + 4$. -/
abbrev bls12381Curve : WeierstrassCurve.Affine BLS12381Fq :=
  bls12381CurveAt bls12381FqModulus

theorem bls12381FqModulus_ne_two : bls12381FqModulus ≠ 2 :=
  (prime_dvd_fq_ne_two_three (dvd_refl _)).1

theorem bls12381FqModulus_ne_three : bls12381FqModulus ≠ 3 :=
  (prime_dvd_fq_ne_two_three (dvd_refl _)).2

theorem bls12381Curve_Δ_ne_zero : bls12381Curve.Δ ≠ 0 :=
  bls12381CurveAt_Δ_ne_zero bls12381FqModulus_ne_two bls12381FqModulus_ne_three

private lemma bls12381Curve_equation_iff (x y : BLS12381Fq) :
    bls12381Curve.Equation x y ↔ y ^ 2 = x ^ 3 + 4 :=
  bls12381CurveAt_equation_iff bls12381FqModulus x y

private lemma bls12381Curve_nonsingular_of_eq {x y : BLS12381Fq} (h : y ^ 2 = x ^ 3 + 4) :
    bls12381Curve.Nonsingular x y :=
  bls12381CurveAt_nonsingular_of_eq bls12381FqModulus_ne_two bls12381FqModulus_ne_three h

/-- Canonical `BLS12381Fq` lift of a 5-limb `Bls12381FqLimbs`. -/
def limbsToBlsFq (l : Bls12381FqLimbs) : BLS12381Fq := (evalLimbsInt l : BLS12381Fq)

theorem bls12381FqRelation_iff_zmod_zero (e : ℤ) :
    Bls12381FqRelationHolds e ↔ (e : BLS12381Fq) = 0 := by
  unfold Bls12381FqRelationHolds
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, _root_.Int.dvd_iff_emod_eq_zero]

theorem bls12381OnCurve_iff_eq (p : Bls12381AffineCoords) :
    Bls12381OnCurve p ↔ (limbsToBlsFq p.y) ^ 2 = (limbsToBlsFq p.x) ^ 3 + 4 := by
  unfold Bls12381OnCurve limbsToBlsFq
  have hcast : ((evalLimbsInt p.x * evalLimbsInt p.x * evalLimbsInt p.x + 4 -
      evalLimbsInt p.y * evalLimbsInt p.y : ℤ) : BLS12381Fq) =
      (evalLimbsInt p.x : BLS12381Fq) ^ 3 + 4 - (evalLimbsInt p.y : BLS12381Fq) ^ 2 := by
    push_cast; ring
  rw [← _root_.Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast,
    sub_eq_zero, eq_comm]

open Classical in
/-- Lift `Bls12381AffineCoords` to `bls12381Curve.Point` (returning `0` when not on curve). -/
noncomputable def bls12381FromAffine (p : Bls12381AffineCoords) : bls12381Curve.Point :=
  if h : Bls12381OnCurve p then
    WeierstrassCurve.Affine.Point.some (limbsToBlsFq p.x) (limbsToBlsFq p.y)
      (bls12381Curve_nonsingular_of_eq ((bls12381OnCurve_iff_eq p).mp h))
  else 0

theorem bls12381FromAffine_of_onCurve {p : Bls12381AffineCoords} (h : Bls12381OnCurve p) :
    bls12381FromAffine p =
      WeierstrassCurve.Affine.Point.some (limbsToBlsFq p.x) (limbsToBlsFq p.y)
        (bls12381Curve_nonsingular_of_eq ((bls12381OnCurve_iff_eq p).mp h)) := by
  classical
  simp [bls12381FromAffine, h]

/-- Standard BLS12-381 $G_1$ generator $G \in E(\mathbb{F}_q)$. -/
noncomputable def bls12381Generator : bls12381Curve.Point :=
  WeierstrassCurve.Affine.Point.some
    (bls12381G1GenX : BLS12381Fq) (bls12381G1GenY : BLS12381Fq)
    (bls12381Generator_order_at_prime_dvd_q (dvd_refl bls12381FqModulus)).choose

theorem bls12381Generator_ne_zero : bls12381Generator ≠ 0 :=
  WeierstrassCurve.Affine.Point.some_ne_zero _

/-- Concrete Mathlib-backed `BLS12381G1` instance over `bls12381Curve.Point`. -/
noncomputable def bls12381G1 : BLS12381G1 where
  Point := bls12381Curve.Point
  zero := 0
  add := (· + ·)
  neg := (-·)
  smul := (· • ·)
  generator := bls12381Generator
  fromAffine := bls12381FromAffine
  add_assoc := _root_.add_assoc
  add_comm := _root_.add_comm
  zero_add := _root_.zero_add
  add_zero := _root_.add_zero
  add_neg_cancel := _root_.add_neg_cancel
  neg_add_cancel := _root_.neg_add_cancel
  smul_zero := _root_.zero_nsmul
  smul_zero_point := _root_.nsmul_zero
  smul_one := _root_.one_nsmul
  smul_add m n a := _root_.add_nsmul a m n
  smul_distrib n a b := _root_.nsmul_add a b n
  smul_smul m n a := by rw [mul_smul]

/-- **Concrete Chord Addition Law (`bls12381_affineAddSpec_eq`)**:
Discharges `hGroupAdd` unconditionally for `bls12381G1`. -/
theorem bls12381_affineAddSpec_eq {p1 p2 p3 : Bls12381AffineCoords} {slope : Bls12381FqLimbs}
    (h1 : Bls12381OnCurve p1) (h2 : Bls12381OnCurve p2) (h3 : Bls12381OnCurve p3)
    (hSpec : Bls12381AffineAddSpec p1 p2 p3 slope) :
    bls12381G1.fromAffine p3 =
      bls12381G1.add (bls12381G1.fromAffine p1) (bls12381G1.fromAffine p2) := by
  obtain ⟨hne, hSlope, hX, hY⟩ := hSpec
  set x1 : BLS12381Fq := limbsToBlsFq p1.x
  set y1 : BLS12381Fq := limbsToBlsFq p1.y
  set x2 : BLS12381Fq := limbsToBlsFq p2.x
  set y2 : BLS12381Fq := limbsToBlsFq p2.y
  set x3 : BLS12381Fq := limbsToBlsFq p3.x
  set y3 : BLS12381Fq := limbsToBlsFq p3.y
  set s : BLS12381Fq := limbsToBlsFq slope
  have hxne : x1 ≠ x2 := by
    intro heq
    apply hne
    rw [← _root_.Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr heq.symm
  have hs : s = bls12381Curve.slope x1 x2 y1 y2 := by
    rw [WeierstrassCurve.Affine.slope]
    simp only [hxne, ↓reduceIte]
    have hSlopeZ : s * (x2 - x1) - (y2 - y1) = 0 := by
      have hz := (bls12381FqRelation_iff_zmod_zero _).mp hSlope
      push_cast at hz; exact hz
    have hdx : x1 - x2 ≠ 0 := sub_ne_zero.mpr hxne
    rw [eq_div_iff hdx]
    linear_combination -hSlopeZ
  have hx3 : x3 = bls12381Curve.addX x1 x2 s := by
    have hXZ : x3 + x1 + x2 - s * s = 0 := by
      have hz := (bls12381FqRelation_iff_zmod_zero _).mp hX
      push_cast at hz; exact hz
    unfold WeierstrassCurve.Affine.addX
    simp only [bls12381Curve, bls12381CurveAt, zero_mul, add_zero, sub_zero]
    linear_combination hXZ
  have hy3 : y3 = bls12381Curve.addY x1 x2 y1 s := by
    have hYZ : y3 + y1 - s * (x1 - x3) = 0 := by
      have hz := (bls12381FqRelation_iff_zmod_zero _).mp hY
      push_cast at hz; exact hz
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.negAddY
    rw [← hx3]
    simp only [bls12381Curve, bls12381CurveAt, zero_mul, sub_zero]
    linear_combination hYZ
  change bls12381FromAffine p3 = bls12381FromAffine p1 + bls12381FromAffine p2
  rw [bls12381FromAffine_of_onCurve h1, bls12381FromAffine_of_onCurve h2,
    bls12381FromAffine_of_onCurve h3, WeierstrassCurve.Affine.Point.add_of_X_ne hxne]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hx3.trans (by rw [hs]), hy3.trans (by rw [hs])⟩

/-- **Concrete Tangent Doubling Law (`bls12381_affineDoubleSpec_eq`)**:
Discharges `hGroupDbl` unconditionally for `bls12381G1`. -/
theorem bls12381_affineDoubleSpec_eq {p1 p3 : Bls12381AffineCoords} {slope : Bls12381FqLimbs}
    (h1 : Bls12381OnCurve p1) (h3 : Bls12381OnCurve p3)
    (hy1_ne : (evalLimbsInt p1.y) % (bls12381FqModulus : ℤ) ≠ 0)
    (hSpec : Bls12381AffineDoubleSpec p1 p3 slope) :
    bls12381G1.fromAffine p3 = bls12381G1.smul 2 (bls12381G1.fromAffine p1) := by
  obtain ⟨hSlope, hX, hY⟩ := hSpec
  set x1 : BLS12381Fq := limbsToBlsFq p1.x
  set y1 : BLS12381Fq := limbsToBlsFq p1.y
  set x3 : BLS12381Fq := limbsToBlsFq p3.x
  set y3 : BLS12381Fq := limbsToBlsFq p3.y
  set s : BLS12381Fq := limbsToBlsFq slope
  have hy1 : y1 ≠ 0 := by
    intro h0; apply hy1_ne
    rw [← _root_.Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h0
  have h2ne : (2 : BLS12381Fq) ≠ 0 := by decide
  have h2y1 : 2 * y1 ≠ 0 := mul_ne_zero h2ne hy1
  have hy_neg : y1 ≠ bls12381Curve.negY x1 y1 := by
    unfold WeierstrassCurve.Affine.negY
    simp only [bls12381Curve, bls12381CurveAt, zero_mul, sub_zero]
    intro heq; apply h2y1; linear_combination heq
  have hs : s = bls12381Curve.slope x1 x1 y1 y1 := by
    rw [WeierstrassCurve.Affine.slope]
    simp only [↓reduceIte, hy_neg]
    have hSlopeZ : 2 * y1 * s - 3 * x1 * x1 = 0 := by
      have hz := (bls12381FqRelation_iff_zmod_zero _).mp hSlope
      push_cast at hz; exact hz
    unfold WeierstrassCurve.Affine.negY
    simp only [bls12381Curve, bls12381CurveAt, zero_mul, add_zero, sub_zero, sub_neg_eq_add]
    have hden : y1 + y1 ≠ 0 := by rwa [← two_mul]
    rw [eq_div_iff hden]
    linear_combination hSlopeZ
  have hx3 : x3 = bls12381Curve.addX x1 x1 s := by
    have hXZ : x3 + 2 * x1 - s * s = 0 := by
      have hz := (bls12381FqRelation_iff_zmod_zero _).mp hX
      push_cast at hz; exact hz
    unfold WeierstrassCurve.Affine.addX
    simp only [bls12381Curve, bls12381CurveAt, zero_mul, add_zero, sub_zero]
    linear_combination hXZ
  have hy3 : y3 = bls12381Curve.addY x1 x1 y1 s := by
    have hYZ : y3 + y1 - s * (x1 - x3) = 0 := by
      have hz := (bls12381FqRelation_iff_zmod_zero _).mp hY
      push_cast at hz; exact hz
    unfold WeierstrassCurve.Affine.addY WeierstrassCurve.Affine.negY WeierstrassCurve.Affine.negAddY
    rw [← hx3]
    simp only [bls12381Curve, bls12381CurveAt, zero_mul, sub_zero]
    linear_combination hYZ
  change bls12381FromAffine p3 = 2 • bls12381FromAffine p1
  rw [two_nsmul, bls12381FromAffine_of_onCurve h1, bls12381FromAffine_of_onCurve h3,
    WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy_neg]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hx3.trans (by rw [hs]), hy3.trans (by rw [hs])⟩

/-- **Concrete Opposite-Point Cancellation (`bls12381_sameX_neY_imp_neg`)**:
Discharges `hOpp` unconditionally for `bls12381G1`. -/
theorem bls12381_sameX_neY_imp_neg {p1 p2 : Bls12381AffineCoords}
    (h1 : Bls12381OnCurve p1) (h2 : Bls12381OnCurve p2)
    (hx : (evalLimbsInt p1.x - evalLimbsInt p2.x) % (bls12381FqModulus : ℤ) = 0)
    (hy : (evalLimbsInt p1.y - evalLimbsInt p2.y) % (bls12381FqModulus : ℤ) ≠ 0) :
    bls12381G1.fromAffine p2 = bls12381G1.neg (bls12381G1.fromAffine p1) := by
  have hxEq : limbsToBlsFq p1.x = limbsToBlsFq p2.x := by
    have hz := (bls12381FqRelation_iff_zmod_zero _).mp hx
    push_cast at hz; exact sub_eq_zero.mp hz
  have hyNe : limbsToBlsFq p1.y ≠ limbsToBlsFq p2.y := by
    intro heq; apply hy
    rw [← _root_.Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; exact sub_eq_zero.mpr heq
  have hcases := WeierstrassCurve.Affine.Y_eq_of_X_eq
    ((bls12381Curve_equation_iff _ _).mpr ((bls12381OnCurve_iff_eq p1).mp h1))
    ((bls12381Curve_equation_iff _ _).mpr ((bls12381OnCurve_iff_eq p2).mp h2)) hxEq
  have hyNeg : limbsToBlsFq p2.y = bls12381Curve.negY (limbsToBlsFq p1.x) (limbsToBlsFq p1.y) := by
    rcases hcases with hsame | hopp
    · exact absurd hsame hyNe
    · unfold WeierstrassCurve.Affine.negY at hopp ⊢
      simp only [bls12381Curve, bls12381CurveAt, zero_mul, sub_zero] at hopp ⊢
      linear_combination hopp
  change bls12381FromAffine p2 = -bls12381FromAffine p1
  rw [bls12381FromAffine_of_onCurve h1, bls12381FromAffine_of_onCurve h2,
    WeierstrassCurve.Affine.Point.neg_some]
  simp only [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hxEq.symm, hyNeg⟩

/-! ## 5. Mandatory BLS12-381 $G_1$ Prime-Order Subgroup Check & Negative Control -/

/-- Prime-order $G_1$ subgroup membership predicate on `bls12381Curve.Point`:
`InPrimeSubgroup P ↔ bls12381FrModulus • P = 0`. -/
abbrev InPrimeSubgroup (P : bls12381Curve.Point) : Prop :=
  bls12381G1.InPrimeSubgroup P

/-- The GLV cube root of unity $\beta \in \mathbb{F}_q$ (`ark_bls12_381::g1::BETA`). -/
abbrev bls12381EndoBeta : BLS12381Fq := (bls12381EndoBetaNat : BLS12381Fq)

theorem bls12381EndoBeta_poly :
    bls12381EndoBeta ^ 2 + bls12381EndoBeta + 1 = 0 := by
  have hc := congrArg (fun n : Nat => (n : BLS12381Fq)) bls12381EndoBetaNat_poly_mod
  rw [ZMod.natCast_mod] at hc
  push_cast at hc
  linear_combination hc

/-- Concrete GLV endomorphism $\phi : E(\mathbb{F}_q) \to E(\mathbb{F}_q)$,
$(x, y) \mapsto (\beta x, y)$. -/
def bls12381Endo (P : bls12381Curve.Point) : bls12381Curve.Point :=
  bls12381EndoAt bls12381FqModulus bls12381FqModulus_ne_two bls12381FqModulus_ne_three
    bls12381EndoBeta bls12381EndoBeta_poly P

/-- The fast BLS12-381 $G_1$ endomorphism subgroup check criterion (`native_curve.rs:181-198`):
$[u^2] P = -\phi(P)$ where $u = \text{bls12381Seed}$. -/
def EndoSubgroupChecked (P : bls12381Curve.Point) : Prop :=
  (bls12381Seed ^ 2) • P = -(bls12381Endo P)

/-- **Soundness of the Fast Endomorphism $G_1$ Subgroup Check (`bls12381_endoSubgroupCheck_sound`):**
Every point $P \in E(\mathbb{F}_q)$ passing $[u^2] P = -\phi(P)$ satisfies
$[r] P = \mathcal{O}$ (`InPrimeSubgroup P`). -/
theorem bls12381_endoSubgroupCheck_sound {P : bls12381Curve.Point}
    (hCheck : EndoSubgroupChecked P) :
    InPrimeSubgroup P :=
  order_r_of_endo_eq_at bls12381FqModulus bls12381FqModulus_ne_two bls12381FqModulus_ne_three
    bls12381EndoBeta bls12381EndoBeta_poly P hCheck

/-- Circuit-level specification of `Affine::subgroup_check` (`native_curve.rs:181-198`):
given affine witnesses `p`, `xp = [u] p`, and `x2p = [u] xp` on $E(\mathbb{F}_q)$, enforces
$x_{2p}.x \equiv \beta \cdot p.x \pmod q$ and $x_{2p}.y + p.y \equiv 0 \pmod q$. -/
def Bls12381AffineSubgroupSpec (p xp x2p : Bls12381AffineCoords) : Prop :=
  Bls12381OnCurve p ∧
  Bls12381OnCurve xp ∧
  Bls12381OnCurve x2p ∧
  bls12381FromAffine xp = bls12381Seed • bls12381FromAffine p ∧
  bls12381FromAffine x2p = bls12381Seed • bls12381FromAffine xp ∧
  Bls12381FqRelationHolds (evalLimbsInt x2p.x - (bls12381EndoBetaNat : ℤ) * evalLimbsInt p.x) ∧
  Bls12381FqRelationHolds (evalLimbsInt x2p.y + evalLimbsInt p.y)

/-- **Circuit-Level Affine Subgroup Check Soundness (`bls12381_affineSubgroupSpec_sound`):**
Satisfying `Bls12381AffineSubgroupSpec p xp x2p` proves `EndoSubgroupChecked (bls12381FromAffine p)`
and unconditionally implies `InPrimeSubgroup (bls12381FromAffine p)`. -/
theorem bls12381_affineSubgroupSpec_sound {p xp x2p : Bls12381AffineCoords}
    (hSpec : Bls12381AffineSubgroupSpec p xp x2p) :
    EndoSubgroupChecked (bls12381FromAffine p) ∧ InPrimeSubgroup (bls12381FromAffine p) := by
  obtain ⟨hp, _, hx2p, hxpEq, hx2pEq, hRelX, hRelY⟩ := hSpec
  have hX : limbsToBlsFq x2p.x = bls12381EndoBeta * limbsToBlsFq p.x := by
    have hz := (bls12381FqRelation_iff_zmod_zero _).mp hRelX
    push_cast at hz
    exact sub_eq_zero.mp hz
  have hY : limbsToBlsFq x2p.y = -(limbsToBlsFq p.y) := by
    have hz := (bls12381FqRelation_iff_zmod_zero _).mp hRelY
    push_cast at hz
    exact eq_neg_of_add_eq_zero_left hz
  have hEndo : EndoSubgroupChecked (bls12381FromAffine p) := by
    unfold EndoSubgroupChecked
    rw [sq, mul_smul, ← hxpEq, ← hx2pEq]
    rw [bls12381FromAffine_of_onCurve hp, bls12381FromAffine_of_onCurve hx2p]
    dsimp only [bls12381Endo, bls12381EndoAt]
    rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    simp only [WeierstrassCurve.Affine.negY, bls12381CurveAt, zero_mul, sub_zero]
    exact ⟨hX, hY⟩
  exact ⟨hEndo, bls12381_endoSubgroupCheck_sound hEndo⟩

/-- **The Standard BLS12-381 Generator Lies in the Prime-Order Subgroup $G_1$:**
Follows unconditionally from our kernel-checked Endomorphism-ECPP certificate in `Field.lean`. -/
theorem bls12381Generator_inPrimeSubgroup : InPrimeSubgroup bls12381Generator :=
  (bls12381Generator_order_at_prime_dvd_q (dvd_refl bls12381FqModulus)).choose_spec

/-! ### Subgroup Closure Under Group Operations and MSM -/

theorem inPrimeSubgroup_zero (G : BLS12381G1) : G.InPrimeSubgroup G.zero :=
  G.smul_zero_point bls12381FrModulus

theorem inPrimeSubgroup_add (G : BLS12381G1) {P Q : G.Point}
    (hP : G.InPrimeSubgroup P) (hQ : G.InPrimeSubgroup Q) :
    G.InPrimeSubgroup (G.add P Q) := by
  unfold BLS12381G1.InPrimeSubgroup at *
  rw [G.smul_distrib, hP, hQ, G.add_zero]

theorem inPrimeSubgroup_neg (G : BLS12381G1) {P : G.Point}
    (hP : G.InPrimeSubgroup P) :
    G.InPrimeSubgroup (G.neg P) := by
  unfold BLS12381G1.InPrimeSubgroup at *
  have hsum : G.add (G.smul bls12381FrModulus P) (G.smul bls12381FrModulus (G.neg P)) = G.zero := by
    rw [← G.smul_distrib, G.add_neg_cancel, G.smul_zero_point]
  rw [hP, G.zero_add] at hsum
  exact hsum

theorem inPrimeSubgroup_smul (G : BLS12381G1) (k : Nat) {P : G.Point}
    (hP : G.InPrimeSubgroup P) :
    G.InPrimeSubgroup (G.smul k P) := by
  unfold BLS12381G1.InPrimeSubgroup at *
  rw [G.smul_smul, Nat.mul_comm, ← G.smul_smul, hP, G.smul_zero_point]

/-- **MSM Subgroup Closure (`bls12381_msm_inPrimeSubgroup`):**
If every base point $P_i$ passes the BLS12-381 prime-order $G_1$ subgroup check, then
$\bigoplus_i [s_i] P_i$ automatically lies in the prime-order subgroup $G_1$. -/
theorem bls12381_msm_inPrimeSubgroup (G : BLS12381G1) :
    ∀ (scalars : List Nat) (points : List G.Point),
      (∀ P ∈ points, G.InPrimeSubgroup P) →
      G.InPrimeSubgroup (bls12381MsmEval G scalars points)
  | [], _, _ => inPrimeSubgroup_zero G
  | _ :: _, [], _ => inPrimeSubgroup_zero G
  | s :: ss, p :: ps, hAll => by
    simp only [bls12381MsmEval]
    exact inPrimeSubgroup_add G
      (inPrimeSubgroup_smul G s (hAll p (List.Mem.head _)))
      (bls12381_msm_inPrimeSubgroup G ss ps (fun q hq => hAll q (List.Mem.tail _ hq)))

/-! ### Constructive Negative Control: 3-Torsion Point `(0, 2)` Fails the $G_1$ Subgroup Check

Unlike BN254 ($h_1 = 1$, where every point on $y^2 = x^3 + 3$ lies in the prime-order subgroup),
BLS12-381 has $h_1 = (u+1)^2 / 3$ divisible by $3$ and the explicit canonical curve point
$T = (0, 2) \in E(\mathbb{F}_q)$ ($2^2 = 0^3 + 4$) has exact order $3$, so
$[r] T = T \neq \mathcal{O}$ (`¬ InPrimeSubgroup T`). Omitting the $G_1$ subgroup check is
therefore strictly unsound on BLS12-381! -/

theorem three_dvd_bls12381G1Cofactor : 3 ∣ bls12381G1Cofactor := by
  exact Nat.dvd_of_mod_eq_zero (by decide)

/-- Explicit 5-limb canonical coordinates of the 3-torsion point $T = (0, 2)$ on $y^2 = x^3 + 4$. -/
def bls12381TorsionCoords : Bls12381AffineCoords :=
  ⟨⟨0, 0, 0, 0, 0⟩, ⟨2, 0, 0, 0, 0⟩⟩

theorem bls12381TorsionCoords_canonical : bls12381TorsionCoords.Canonical := by
  unfold Bls12381AffineCoords.Canonical Bls12381FqLimbs.Canonical bls12381TorsionCoords evalLimbs
  constructor <;> decide

theorem bls12381TorsionCoords_onCurve : Bls12381OnCurve bls12381TorsionCoords := by
  unfold Bls12381OnCurve bls12381TorsionCoords evalLimbsInt evalLimbs
  decide

/-- Concrete 3-torsion curve point $T = (0, 2) \in E(\mathbb{F}_q) \setminus E(\mathbb{F}_q)[r]$. -/
noncomputable def bls12381TorsionPoint : bls12381Curve.Point :=
  bls12381FromAffine bls12381TorsionCoords

theorem bls12381TorsionPoint_ne_zero : bls12381TorsionPoint ≠ 0 := by
  unfold bls12381TorsionPoint
  rw [bls12381FromAffine_of_onCurve bls12381TorsionCoords_onCurve]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem bls12381TorsionPoint_order_three : (3 : Nat) • bls12381TorsionPoint = 0 := by
  unfold bls12381TorsionPoint
  rw [bls12381FromAffine_of_onCurve bls12381TorsionCoords_onCurve]
  have hx0 : limbsToBlsFq bls12381TorsionCoords.x = 0 := by
    unfold limbsToBlsFq bls12381TorsionCoords evalLimbsInt evalLimbs; simp
  have hy2 : limbsToBlsFq bls12381TorsionCoords.y = 2 := by
    unfold limbsToBlsFq bls12381TorsionCoords evalLimbsInt evalLimbs; simp
  set P : bls12381Curve.Point :=
    WeierstrassCurve.Affine.Point.some (limbsToBlsFq bls12381TorsionCoords.x)
      (limbsToBlsFq bls12381TorsionCoords.y)
      (bls12381Curve_nonsingular_of_eq ((bls12381OnCurve_iff_eq bls12381TorsionCoords).mp
        bls12381TorsionCoords_onCurve))
  have hfix : bls12381Endo P = P := by
    dsimp only [P, bls12381Endo, bls12381EndoAt]
    rw [WeierstrassCurve.Affine.Point.some.injEq]
    simp [hx0]
  have hchar := bls12381EndoAt_charpoly bls12381FqModulus
    bls12381FqModulus_ne_two bls12381FqModulus_ne_three
    bls12381EndoBeta bls12381EndoBeta_poly P
  change bls12381Endo (bls12381Endo P) + bls12381Endo P + P = 0 at hchar
  rw [hfix, hfix] at hchar
  have h3 : (3 : Nat) • P = P + P + P := by
    rw [show (3 : Nat) = 1 + 1 + 1 from rfl, add_nsmul, add_nsmul, one_nsmul]
  rw [h3]
  exact hchar

/-- **Constructive Negative Control (`bls12381_torsionPoint_not_inPrimeSubgroup`):**
The canonical curve point $T = (0, 2)$ lies on $y^2 = x^3 + 4$ (`bls12381TorsionCoords_onCurve`),
yet $[r] T = T \neq \mathcal{O}$, proving `¬ InPrimeSubgroup bls12381TorsionPoint`! -/
theorem bls12381_torsionPoint_not_inPrimeSubgroup :
    ¬ InPrimeSubgroup bls12381TorsionPoint := by
  intro hin
  have hmod : bls12381FrModulus % 3 = 1 := by decide
  have hdiv : 3 * (bls12381FrModulus / 3) + 1 = bls12381FrModulus := by
    have := Nat.div_add_mod bls12381FrModulus 3
    omega
  have hrT : bls12381FrModulus • bls12381TorsionPoint = bls12381TorsionPoint := by
    conv_lhs => rw [← hdiv]
    rw [add_smul, Nat.mul_comm, mul_smul, bls12381TorsionPoint_order_three,
      nsmul_zero, zero_add, one_nsmul]
  change bls12381FrModulus • bls12381TorsionPoint = 0 at hin
  rw [hrT] at hin
  exact bls12381TorsionPoint_ne_zero hin

/-- **Constructive Negative Control (`bls12381_torsionPoint_fails_endoCheck`):**
The 3-torsion point $T = (0, 2)$ is rejected by `EndoSubgroupChecked`. -/
theorem bls12381_torsionPoint_fails_endoCheck :
    ¬ EndoSubgroupChecked bls12381TorsionPoint :=
  fun h => bls12381_torsionPoint_not_inPrimeSubgroup (bls12381_endoSubgroupCheck_sound h)

end Ix.Cert.Compression.Bls12381.CurveMsm
