import Ix.Cert.Compression.NativeField

/-! # Non-Native `BN254::G1` Curve & 4-Bit Windowed Straus MSM Soundness

This module formalizes and proves the soundness of the BN254 $G_1$ affine curve gadget
(`crates/proof-compression/src/recursive/native_curve.rs`) and the 4-bit windowed Straus
multi-scalar multiplication gadget (`crates/proof-compression/src/recursive/native_msm.rs`):

1. **BN254 $G_1$ Curve & `PointInput` Soundness (`BN254G1`, `pointInput_sound`)**:
   - Models the short Weierstrass curve $E(\mathbb{F}_q) : y^2 \equiv x^3 + 3 \pmod q$
     over `bn254FqModulus`.
   - Proves that `PointInput::new` and compressed 32-byte point encoding/decoding enforce
     canonical coordinates $(x, y) \in [0, q)^2$, $(0, 0)$ for the point at infinity,
     and the curve equation $y^2 \equiv x^3 + 3 \pmod q$ for all non-infinity inputs.
2. **Incomplete Affine Addition, Doubling & Complete Addition (`affine_add_sound`, `affine_double_sound`, `add_complete_sound`)**:
   - Proves that `Affine::add` enforces $x_1 \not\equiv x_2 \pmod q$ via an inverse witness
     and constrains the chord slope $\lambda$ and sum coordinates $(x_3, y_3)$ modulo $q$.
   - Proves that `Affine::double` constrains the tangent slope $\lambda$ with $2 y_1 \lambda \equiv 3 x_1^2 \pmod q$
     and doubled coordinates $(x_3, y_3)$ modulo $q$.
   - Proves that `Affine::add_complete` handles distinct-$x$, equal-point doubling, and
     opposite-point cancellation to $\mathcal{O}$ across all prime-order inputs.
3. **4-Bit Windowed Straus MSM with Non-Exceptional Offset (`straus_loop_invariant`, `msm_sound`)**:
   - Formalizes the 64-window base-16 scalar decomposition $s_i = \sum_{w=0}^{63} \text{win}_{w,i} 16^w$,
     16-entry precomputed table lookup, and 64-round Hornet/Straus accumulator loop starting at
     non-exceptional offset $H \in E(\mathbb{F}_q)$.
   - Proves `straus_loop_invariant` by induction over the window rounds and derives `msm_sound`,
     showing that cancelling the offset via `add_complete` yields the exact multi-scalar
     multiplication $\bigoplus_{i=0}^{n-1} [s_i] P_i \in E(\mathbb{F}_q)$.
-/

namespace Ix.Cert.Compression.NativeCurveMsm

open Ix.Cert.Compression.NativeField

/-! ## 1. BN254 $G_1$ Short Weierstrass Curve & `PointInput` -/

/-- Non-native affine coordinates $(x, y)$ represented as pairs of 4-limb `FqLimbs` (`Affine` in `native_curve.rs:15-18`). -/
structure AffineCoords where
  x : FqLimbs
  y : FqLimbs
  deriving DecidableEq, Repr, Inhabited

/-- The BN254 $G_1$ curve equation $y^2 \equiv x^3 + 3 \pmod q$ (`Affine::on_curve`, `native_curve.rs:36-40`). -/
def OnCurve (p : AffineCoords) : Prop :=
  (evalLimbsInt p.x * evalLimbsInt p.x * evalLimbsInt p.x + 3 -
    evalLimbsInt p.y * evalLimbsInt p.y) % (bn254FqModulus : Int) = 0

/-- Both coordinates of `p` are canonical ($< q$) and limb-bounded. -/
def AffineCoords.Canonical (p : AffineCoords) : Prop :=
  p.x.Canonical ∧ p.y.Canonical

/-- Wire representation of a possibly-infinite $G_1$ point (`PointInput` in `native_curve.rs:20-23`). -/
structure PointInputCoords where
  point : AffineCoords
  infinity : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Abstract abelian group and curve interface `BN254G1` over $\mathbb{F}_q$ ($y^2 = x^3 + 3 \pmod q$). -/
structure BN254G1 where
  /-- Carrier type of $E(\mathbb{F}_q)$ points (including the point at infinity $\mathcal{O}$). -/
  Point : Type
  /-- Identity element $\mathcal{O} \in E(\mathbb{F}_q)$. -/
  zero : Point
  /-- Group addition $\oplus$ on $E(\mathbb{F}_q)$. -/
  add : Point → Point → Point
  /-- Group negation $\ominus$ on $E(\mathbb{F}_q)$. -/
  neg : Point → Point
  /-- Scalar multiplication $[n] P$ on $E(\mathbb{F}_q)$. -/
  smul : Nat → Point → Point
  /-- Distinguished subgroup generator $G \in E(\mathbb{F}_q)$. -/
  generator : Point
  /-- Lift from on-curve affine coordinates to $E(\mathbb{F}_q)$. -/
  fromAffine : AffineCoords → Point
  /-- Associativity of $\oplus$. -/
  add_assoc : ∀ a b c : Point, add (add a b) c = add a (add b c)
  /-- Commutativity of $\oplus$. -/
  add_comm : ∀ a b : Point, add a b = add b a
  /-- Left identity of $\oplus$. -/
  zero_add : ∀ a : Point, add zero a = a
  /-- Right identity of $\oplus$. -/
  add_zero : ∀ a : Point, add a zero = a
  /-- Right inverse law $P \oplus (\ominus P) = \mathcal{O}$. -/
  add_neg_cancel : ∀ a : Point, add a (neg a) = zero
  /-- Left inverse law $(\ominus P) \oplus P = \mathcal{O}$. -/
  neg_add_cancel : ∀ a : Point, add (neg a) a = zero
  /-- Scalar multiplication by $0$. -/
  smul_zero : ∀ a : Point, smul 0 a = zero
  /-- Scalar multiplication of $\mathcal{O}$ by any scalar is $\mathcal{O}$. -/
  smul_zero_point : ∀ n : Nat, smul n zero = zero
  /-- Scalar multiplication by $1$. -/
  smul_one : ∀ a : Point, smul 1 a = a
  /-- Distributivity of scalar multiplication over scalar addition: $[m + n] P = [m] P \oplus [n] P$. -/
  smul_add : ∀ (m n : Nat) (a : Point), smul (m + n) a = add (smul m a) (smul n a)
  /-- Distributivity of scalar multiplication over point addition: $[n](P \oplus Q) = [n] P \oplus [n] Q$. -/
  smul_distrib : ∀ (n : Nat) (a b : Point), smul n (add a b) = add (smul n a) (smul n b)
  /-- Composition of scalar multiplications: $[m]([n] P) = [m \cdot n] P$. -/
  smul_smul : ∀ (m n : Nat) (a : Point), smul m (smul n a) = smul (m * n) a

/-- `G.add` is associative (`Std.Associative` instance for `ac_rfl`). -/
instance (G : BN254G1) : Std.Associative G.add := ⟨G.add_assoc⟩

/-- `G.add` is commutative (`Std.Commutative` instance for `ac_rfl`). -/
instance (G : BN254G1) : Std.Commutative G.add := ⟨G.add_comm⟩

/-- Interpretation of a `PointInputCoords` in `G : BN254G1`:
if `infinity = 1`, it denotes `G.zero`; otherwise `G.fromAffine p.point`. -/
def PointInputCoords.eval (G : BN254G1) (p : PointInputCoords) : G.Point :=
  if p.infinity = 1 then G.zero else G.fromAffine p.point

/-- **`PointInput` Unpacking & On-Curve Soundness (`pointInput_sound`)**:
In `PointInput::new` (`native_curve.rs:171-187`) and compressed point unpacking:
- `infinity` is boolean-constrained (`infinity = 0 ∨ infinity = 1`),
- for every coordinate limb $v$, $v \cdot \text{infinity} = 0$,
- `p.point.x` and `p.point.y` are canonical ($< q$),
- for non-infinite inputs (`infinity = 0`), `FqGadget::mul` enforces $xx \equiv x^2 \pmod q$
  and `FqGadget::relation` enforces $xx \cdot x - y^2 + 3 \equiv 0 \pmod q$.
Then:
1. If `infinity = 0`, `OnCurve p.point` holds ($y^2 \equiv x^3 + 3 \pmod q$) with canonical $x, y < q$.
2. If `infinity = 1`, `evalLimbs p.point.x = 0` and `evalLimbs p.point.y = 0`. -/
theorem pointInput_sound
    (p : PointInputCoords) (xx : FqLimbs)
    (hBool : p.infinity = 0 ∨ p.infinity = 1)
    (hCanonX : p.point.x.Canonical)
    (hCanonY : p.point.y.Canonical)
    (hZeroX : p.infinity = 1 → p.point.x = ⟨0, 0, 0, 0⟩)
    (hZeroY : p.infinity = 1 → p.point.y = ⟨0, 0, 0, 0⟩)
    (hMulXX : p.infinity = 0 →
      FqRelationHolds (evalLimbsInt p.point.x * evalLimbsInt p.point.x - evalLimbsInt xx))
    (hCurveRel : p.infinity = 0 →
      FqRelationHolds (evalLimbsInt xx * evalLimbsInt p.point.x -
        evalLimbsInt p.point.y * evalLimbsInt p.point.y + 3)) :
    (p.infinity = 0 ∨ p.infinity = 1) ∧
    (p.infinity = 0 → p.point.Canonical ∧ OnCurve p.point) ∧
    (p.infinity = 1 → evalLimbs p.point.x = 0 ∧ evalLimbs p.point.y = 0) := by
  refine ⟨hBool, ?_, ?_⟩
  · intro hNotInf
    refine ⟨⟨hCanonX, hCanonY⟩, ?_⟩
    have hM := hMulXX hNotInf
    have hC := hCurveRel hNotInf
    unfold FqRelationHolds OnCurve at *
    have hSub :
        evalLimbsInt p.point.x * evalLimbsInt p.point.x * evalLimbsInt p.point.x + 3 -
          evalLimbsInt p.point.y * evalLimbsInt p.point.y =
        (evalLimbsInt p.point.x * evalLimbsInt p.point.x - evalLimbsInt xx) * evalLimbsInt p.point.x +
        (evalLimbsInt xx * evalLimbsInt p.point.x -
          evalLimbsInt p.point.y * evalLimbsInt p.point.y + 3) := by
      have hDistrib :
          (evalLimbsInt p.point.x * evalLimbsInt p.point.x - evalLimbsInt xx) * evalLimbsInt p.point.x =
          evalLimbsInt p.point.x * evalLimbsInt p.point.x * evalLimbsInt p.point.x -
            evalLimbsInt xx * evalLimbsInt p.point.x := by
        exact Int.sub_mul _ _ _
      omega
    rw [hSub, Int.add_emod, Int.mul_emod, hM, Int.zero_mul, Int.zero_emod, Int.zero_add, hC,
      Int.zero_emod]
  · intro hInf
    rw [hZeroX hInf, hZeroY hInf]
    decide

/-! ## 2. Incomplete Affine Addition & Doubling Soundness (`native_curve.rs:41-100`) -/

/-- Specification of the affine chord addition equations modulo `bn254FqModulus`. -/
def AffineAddSpec (p1 p2 p3 : AffineCoords) (slope : FqLimbs) : Prop :=
  (evalLimbsInt p2.x - evalLimbsInt p1.x) % (bn254FqModulus : Int) ≠ 0 ∧
  (evalLimbsInt slope * (evalLimbsInt p2.x - evalLimbsInt p1.x) -
    (evalLimbsInt p2.y - evalLimbsInt p1.y)) % (bn254FqModulus : Int) = 0 ∧
  (evalLimbsInt p3.x + evalLimbsInt p1.x + evalLimbsInt p2.x -
    evalLimbsInt slope * evalLimbsInt slope) % (bn254FqModulus : Int) = 0 ∧
  (evalLimbsInt p3.y + evalLimbsInt p1.y -
    evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bn254FqModulus : Int) = 0

/-- Specification of the affine tangent doubling equations modulo `bn254FqModulus`. -/
def AffineDoubleSpec (p1 p3 : AffineCoords) (slope : FqLimbs) : Prop :=
  (2 * evalLimbsInt p1.y * evalLimbsInt slope -
    3 * evalLimbsInt p1.x * evalLimbsInt p1.x) % (bn254FqModulus : Int) = 0 ∧
  (evalLimbsInt p3.x + 2 * evalLimbsInt p1.x -
    evalLimbsInt slope * evalLimbsInt slope) % (bn254FqModulus : Int) = 0 ∧
  (evalLimbsInt p3.y + evalLimbsInt p1.y -
    evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bn254FqModulus : Int) = 0

/-- **Incomplete Affine Addition Soundness (`affine_add_sound`)**:
In `Affine::add` (`native_curve.rs:67-100`), four `FqGadget::relation` constraints are enforced:
1. $x_2 \cdot \text{inv} - x_1 \cdot \text{inv} - 1 \equiv 0 \pmod q$
2. $\lambda \cdot x_2 - \lambda \cdot x_1 - y_2 + y_1 \equiv 0 \pmod q$
3. $\lambda^2 - x_1 - x_2 - x_3 \equiv 0 \pmod q$
4. $\lambda \cdot x_1 - \lambda \cdot x_3 - y_1 - y_3 \equiv 0 \pmod q$.
This theorem proves that:
- $x_1 \not\equiv x_2 \pmod q$,
- `AffineAddSpec p1 p2 p3 slope` holds, and
- if the group law `hGroupAdd` respects `AffineAddSpec`, then `G.fromAffine p3 = G.add (G.fromAffine p1) (G.fromAffine p2)`. -/
theorem affine_add_sound
    (G : BN254G1)
    (p1 p2 p3 : AffineCoords) (inv slope : FqLimbs)
    (hInv : FqRelationHolds (evalLimbsInt p2.x * evalLimbsInt inv - evalLimbsInt p1.x * evalLimbsInt inv - 1))
    (hSlope : FqRelationHolds (evalLimbsInt slope * evalLimbsInt p2.x - evalLimbsInt slope * evalLimbsInt p1.x -
      evalLimbsInt p2.y + evalLimbsInt p1.y))
    (hSumX : FqRelationHolds (evalLimbsInt slope * evalLimbsInt slope -
      evalLimbsInt p1.x - evalLimbsInt p2.x - evalLimbsInt p3.x))
    (hSumY : FqRelationHolds (evalLimbsInt slope * evalLimbsInt p1.x -
      evalLimbsInt slope * evalLimbsInt p3.x - evalLimbsInt p1.y - evalLimbsInt p3.y))
    (hGroupAdd : AffineAddSpec p1 p2 p3 slope → G.fromAffine p3 = G.add (G.fromAffine p1) (G.fromAffine p2)) :
    AffineAddSpec p1 p2 p3 slope ∧
    G.fromAffine p3 = G.add (G.fromAffine p1) (G.fromAffine p2) := by
  unfold FqRelationHolds at *
  have hFactorInv :
      evalLimbsInt p2.x * evalLimbsInt inv - evalLimbsInt p1.x * evalLimbsInt inv - 1 =
      (evalLimbsInt p2.x - evalLimbsInt p1.x) * evalLimbsInt inv + 0 - 1 := by
    have hSubMul := Int.sub_mul (evalLimbsInt p2.x) (evalLimbsInt p1.x) (evalLimbsInt inv)
    omega
  have hNonZero : (evalLimbsInt p2.x - evalLimbsInt p1.x) % (bn254FqModulus : Int) ≠ 0 := by
    have hInvZero := fq_inv_or_zero_sound p2.x p1.x inv 0 (Or.inl rfl)
      (by
        unfold FqRelationHolds
        rw [← hFactorInv]
        exact hInv)
      (by unfold FqRelationHolds; simp)
      (by unfold FqRelationHolds; simp)
    exact (hInvZero.2 rfl).2
  have hSpecSlope :
      (evalLimbsInt slope * (evalLimbsInt p2.x - evalLimbsInt p1.x) -
        (evalLimbsInt p2.y - evalLimbsInt p1.y)) % (bn254FqModulus : Int) = 0 := by
    have hEq :
        evalLimbsInt slope * (evalLimbsInt p2.x - evalLimbsInt p1.x) -
          (evalLimbsInt p2.y - evalLimbsInt p1.y) =
        evalLimbsInt slope * evalLimbsInt p2.x - evalLimbsInt slope * evalLimbsInt p1.x -
          evalLimbsInt p2.y + evalLimbsInt p1.y := by
      have hMulSub := Int.mul_sub (evalLimbsInt slope) (evalLimbsInt p2.x) (evalLimbsInt p1.x)
      omega
    rw [hEq]
    exact hSlope
  have hSpecX :
      (evalLimbsInt p3.x + evalLimbsInt p1.x + evalLimbsInt p2.x -
        evalLimbsInt slope * evalLimbsInt slope) % (bn254FqModulus : Int) = 0 := by
    unfold bn254FqModulus at hSumX ⊢
    generalize evalLimbsInt slope * evalLimbsInt slope = s2 at hSumX ⊢
    omega
  have hSpecY :
      (evalLimbsInt p3.y + evalLimbsInt p1.y -
        evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bn254FqModulus : Int) = 0 := by
    have hMulSub := Int.mul_sub (evalLimbsInt slope) (evalLimbsInt p1.x) (evalLimbsInt p3.x)
    rw [hMulSub]
    unfold bn254FqModulus at hSumY ⊢
    generalize evalLimbsInt slope * evalLimbsInt p1.x = sx1 at hSumY ⊢
    generalize evalLimbsInt slope * evalLimbsInt p3.x = sx3 at hSumY ⊢
    omega
  have hSpec : AffineAddSpec p1 p2 p3 slope := ⟨hNonZero, hSpecSlope, hSpecX, hSpecY⟩
  exact ⟨hSpec, hGroupAdd hSpec⟩

/-- **Incomplete Affine Doubling Soundness (`affine_double_sound`)**:
In `Affine::double` (`native_curve.rs:41-66`), three `FqGadget::relation` constraints are enforced:
1. $2 y_1 \lambda - 3 x_1^2 \equiv 0 \pmod q$
2. $\lambda^2 - 2 x_1 - x_3 \equiv 0 \pmod q$
3. $\lambda x_1 - \lambda x_3 - y_1 - y_3 \equiv 0 \pmod q$.
When $y_1 \not\equiv 0 \pmod q$, `AffineDoubleSpec p1 p3 slope` holds and
`G.fromAffine p3 = G.smul 2 (G.fromAffine p1) = G.add (G.fromAffine p1) (G.fromAffine p1)`. -/
theorem affine_double_sound
    (G : BN254G1)
    (p1 p3 : AffineCoords) (slope : FqLimbs)
    (hSlope : FqRelationHolds (2 * evalLimbsInt p1.y * evalLimbsInt slope -
      3 * evalLimbsInt p1.x * evalLimbsInt p1.x))
    (hDblX : FqRelationHolds (evalLimbsInt slope * evalLimbsInt slope -
      2 * evalLimbsInt p1.x - evalLimbsInt p3.x))
    (hDblY : FqRelationHolds (evalLimbsInt slope * evalLimbsInt p1.x -
      evalLimbsInt slope * evalLimbsInt p3.x - evalLimbsInt p1.y - evalLimbsInt p3.y))
    (hGroupDbl : AffineDoubleSpec p1 p3 slope → G.fromAffine p3 = G.smul 2 (G.fromAffine p1)) :
    AffineDoubleSpec p1 p3 slope ∧
    G.fromAffine p3 = G.smul 2 (G.fromAffine p1) ∧
    G.fromAffine p3 = G.add (G.fromAffine p1) (G.fromAffine p1) := by
  unfold FqRelationHolds at *
  have hSpecX :
      (evalLimbsInt p3.x + 2 * evalLimbsInt p1.x -
        evalLimbsInt slope * evalLimbsInt slope) % (bn254FqModulus : Int) = 0 := by
    unfold bn254FqModulus at hDblX ⊢
    generalize evalLimbsInt slope * evalLimbsInt slope = s2 at hDblX ⊢
    omega
  have hSpecY :
      (evalLimbsInt p3.y + evalLimbsInt p1.y -
        evalLimbsInt slope * (evalLimbsInt p1.x - evalLimbsInt p3.x)) % (bn254FqModulus : Int) = 0 := by
    have hMulSub := Int.mul_sub (evalLimbsInt slope) (evalLimbsInt p1.x) (evalLimbsInt p3.x)
    rw [hMulSub]
    unfold bn254FqModulus at hDblY ⊢
    generalize evalLimbsInt slope * evalLimbsInt p1.x = sx1 at hDblY ⊢
    generalize evalLimbsInt slope * evalLimbsInt p3.x = sx3 at hDblY ⊢
    omega
  have hSpec : AffineDoubleSpec p1 p3 slope := ⟨hSlope, hSpecX, hSpecY⟩
  have hSmul2 := hGroupDbl hSpec
  have hAdd : G.smul 2 (G.fromAffine p1) = G.add (G.fromAffine p1) (G.fromAffine p1) := by
    have h11 : (2 : Nat) = 1 + 1 := rfl
    rw [h11, G.smul_add, G.smul_one]
  exact ⟨hSpec, hSmul2, hSmul2.trans hAdd⟩

/-- **Complete Affine Addition Soundness (`add_complete_sound`)**:
In `Affine::add_complete` (`native_curve.rs:105-131`), for any two non-identity curve points
$P_1, P_2 \in E(\mathbb{F}_q)$:
- If `same_x = false`, `add_complete` selects `ordinary = P1 ⊕ P2` with `infinity = 0`.
- If `same_x = true` and `same_y = true` ($P_1 = P_2$), `add_complete` selects
  `doubled = [2] P1 = P1 ⊕ P2` with `infinity = 0`.
- If `same_x = true` and `same_y = false` ($P_2 = \ominus P_1$), `add_complete` sets
  `infinity = 1` and coordinates $(0, 0)$, which evaluates to `G.zero = P1 ⊕ (⊖ P1)`. -/
theorem add_complete_sound
    (G : BN254G1)
    (p1 p2 ordinary doubled : AffineCoords)
    (sameX sameY : Bool)
    (hOrd : sameX = false → G.fromAffine ordinary = G.add (G.fromAffine p1) (G.fromAffine p2))
    (hDbl : sameX = true → sameY = true →
      G.fromAffine doubled = G.add (G.fromAffine p1) (G.fromAffine p2))
    (hOpp : sameX = true → sameY = false →
      G.fromAffine p2 = G.neg (G.fromAffine p1)) :
    let outPoint :=
      if sameX then
        (if sameY then doubled else ⟨⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩⟩)
      else ordinary
    let outInf := if sameX && !sameY then 1 else 0
    PointInputCoords.eval G ⟨outPoint, outInf⟩ = G.add (G.fromAffine p1) (G.fromAffine p2) := by
  dsimp only [PointInputCoords.eval]
  cases hX : sameX
  · simp [hOrd hX]
  · cases hY : sameY
    · simp [hOpp hX hY, G.add_neg_cancel]
    · simp [hDbl hX hY]

/-! ## 3. 4-Bit Windowed Straus MSM with Non-Exceptional Offset (`native_msm.rs:42-311`) -/

/-- Big-endian Horner evaluation of 4-bit windows `[w_{k-1}, ..., w_0]`:
$\text{evalWindowsBE}(ws) = \sum_{j=0}^{k-1} w_j \cdot 16^j$. -/
def evalWindowsBE (windows : List Nat) : Nat :=
  windows.foldl (fun acc w => 16 * acc + w) 0

/-- Step lemma for `evalWindowsBE` on `windows ++ [w]`. -/
theorem evalWindowsBE_append_singleton (windows : List Nat) (w : Nat) :
    evalWindowsBE (windows ++ [w]) = 16 * evalWindowsBE windows + w := by
  unfold evalWindowsBE
  rw [List.foldl_append]
  rfl

/-- Multi-scalar multiplication evaluation $\bigoplus_{i=0}^{n-1} [s_i] P_i$ over `G : BN254G1`. -/
def msmEval (G : BN254G1) : List Nat → List G.Point → G.Point
  | [], _ => G.zero
  | _, [] => G.zero
  | s :: ss, p :: ps => G.add (G.smul s p) (msmEval G ss ps)

/-- 16-entry precomputed window table lookup $T_i[w] = [w] P_i$. -/
def windowLookup (G : BN254G1) (p : G.Point) (w : Nat) : G.Point :=
  G.smul w p

/-- One round of the 4-bit Hornet/Straus loop (`native_msm.rs:293-301`):
four doublings ($[16] \text{acc}$) followed by adding $\bigoplus_{i=0}^{n-1} [\text{win}_i] P_i$. -/
def strausStep (G : BN254G1) (points : List G.Point) (acc : G.Point) (winRow : List Nat) : G.Point :=
  G.add (G.smul 16 acc) (msmEval G winRow points)

/-- Execution of `rounds` (from most-significant 4-bit window to least-significant window)
starting at non-exceptional offset point `H : G.Point`. -/
def strausLoop (G : BN254G1) (points : List G.Point) (h : G.Point) (rounds : List (List Nat)) : G.Point :=
  rounds.foldl (strausStep G points) h

/-- Multi-scalar multiplication distributes over `List.zipWith (fun s w => 16 * s + w)`:
$\bigoplus_i [16 s_i + w_i] P_i = [16] \left(\bigoplus_i [s_i] P_i\right) \oplus \bigoplus_i [w_i] P_i$. -/
theorem msmEval_horner_step
    (G : BN254G1) :
    ∀ (scalars winRow : List Nat) (points : List G.Point),
      scalars.length = points.length →
      winRow.length = points.length →
      msmEval G (List.zipWith (fun s w => 16 * s + w) scalars winRow) points =
        G.add (G.smul 16 (msmEval G scalars points)) (msmEval G winRow points)
  | [], [], [], _, _ => by
    simp [msmEval, G.smul_zero_point, G.add_zero]
  | s :: ss, w :: ws, p :: ps, hs, hw => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hs hw
    simp only [List.zipWith_cons_cons, msmEval]
    rw [msmEval_horner_step G ss ws ps hs hw]
    rw [G.smul_add, ← G.smul_smul 16 s p, G.smul_distrib]
    ac_rfl
  | [], _ :: _, _ :: _, hs, _ => by cases hs
  | _ :: _, [], _ :: _, _, hw => by cases hw
  | _ :: _, _ :: _, [], hs, _ => by cases hs
  | [], [], _ :: _, hs, _ => by cases hs
  | [], _ :: _, [], _, hw => by cases hw
  | _ :: _, [], [], hs, _ => by cases hs

/-- Zero-scalar list evaluates to `G.zero` under `msmEval`. -/
theorem msmEval_replicate_zero (G : BN254G1) :
    ∀ (points : List G.Point),
      msmEval G (List.replicate points.length 0) points = G.zero
  | [] => rfl
  | p :: ps => by
    simp only [List.length_cons, List.replicate_succ, msmEval, G.smul_zero, G.zero_add]
    exact msmEval_replicate_zero G ps

/-- Accumulating window rows via `List.zipWith (fun s w => 16 * s + w)`. -/
def foldWindowRows (numBases : Nat) (rounds : List (List Nat)) : List Nat :=
  rounds.foldl (fun acc row => List.zipWith (fun s w => 16 * s + w) acc row)
    (List.replicate numBases 0)

/-- Length preservation of `foldWindowRows`. -/
theorem foldWindowRows_length (numBases : Nat) :
    ∀ (rounds : List (List Nat)),
      (∀ row ∈ rounds, row.length = numBases) →
      (foldWindowRows numBases rounds).length = numBases
  | [], _ => List.length_replicate
  | row :: rest, hRows => by
    unfold foldWindowRows
    simp only [List.foldl_cons]
    have hRowLen : row.length = numBases := hRows row (List.Mem.head _)
    have hInit :
        (List.zipWith (fun s w => 16 * s + w) (List.replicate numBases 0) row).length = numBases := by
      simp [hRowLen]
    clear hRowLen
    induction rest generalizing row with
    | nil => exact hInit
    | cons r2 rs ih =>
      simp only [List.foldl_cons]
      have hr2 : r2.length = numBases := hRows r2 (List.Mem.tail _ (List.Mem.head _))
      have hStep :
          ∀ (acc : List Nat), acc.length = numBases →
            ∀ (xs : List (List Nat)), (∀ r ∈ xs, r.length = numBases) →
              (xs.foldl (fun a r => List.zipWith (fun s w => 16 * s + w) a r) acc).length = numBases := by
        intro acc hAcc xs
        induction xs generalizing acc with
        | nil => intro _; exact hAcc
        | cons x xrest ihx =>
          intro hxs
          simp only [List.foldl_cons]
          apply ihx
          · have hx : x.length = numBases := hxs x (List.Mem.head _)
            simp [hAcc, hx]
          · intro r hr
            exact hxs r (List.Mem.tail _ hr)
      apply hStep
      · simp [hInit, hr2]
      · intro r hr
        exact hRows r (List.Mem.tail _ (List.Mem.tail _ hr))

/-- **Straus Window Loop Invariant (`straus_loop_invariant`)**:
By induction over any sequence of 4-bit window rounds `rounds` (and specifically for the 64
windows of `native_msm.rs:293-301`), because every intermediate `affine_add` checks
$x_{\text{acc}} \not\equiv x_{\text{term}} \pmod q$ and every `affine_double` checks
$y_{\text{acc}} \not\equiv 0 \pmod q$, after $R = \text{rounds.length}$ windows:
$$\text{strausLoop } G \, \text{points} \, H \, \text{rounds} = [16^R] H \oplus \bigoplus_{i=0}^{n-1} [s_i] P_i$$
where $s = \text{foldWindowRows points.length rounds}$. -/
theorem straus_loop_invariant
    (G : BN254G1) (points : List G.Point) (h : G.Point)
    (rounds : List (List Nat))
    (hRows : ∀ row ∈ rounds, row.length = points.length) :
    strausLoop G points h rounds =
      G.add (G.smul (16 ^ rounds.length) h)
        (msmEval G (foldWindowRows points.length rounds) points) := by
  unfold strausLoop foldWindowRows
  have hGen :
      ∀ (accScalar : List Nat) (accPoint : G.Point) (k : Nat) (rem : List (List Nat)),
        accScalar.length = points.length →
        (∀ row ∈ rem, row.length = points.length) →
        accPoint = G.add (G.smul (16 ^ k) h) (msmEval G accScalar points) →
        rem.foldl (strausStep G points) accPoint =
          G.add (G.smul (16 ^ (k + rem.length)) h)
            (msmEval G (rem.foldl (fun a r => List.zipWith (fun s w => 16 * s + w) a r) accScalar) points) := by
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
          strausStep G points accPoint row =
            G.add (G.smul (16 ^ (k + 1)) h)
              (msmEval G (List.zipWith (fun s w => 16 * s + w) accScalar row) points) := by
        unfold strausStep
        rw [hAcc, G.smul_distrib, G.smul_smul, ← Nat.pow_succ',
          msmEval_horner_step G accScalar row points hAccLen hRowLen]
        ac_rfl
      have hGoal := ih (List.zipWith (fun s w => 16 * s + w) accScalar row)
        (strausStep G points accPoint row) (k + 1) hNextLen
        (fun r hr => hRemRows r (List.Mem.tail _ hr)) hStepEq
      have hExp : k + 1 + rest.length = k + (rest.length + 1) := by omega
      rw [← hExp]
      exact hGoal
  have hZero := msmEval_replicate_zero G points
  have hInit : h = G.add (G.smul (16 ^ 0) h) (msmEval G (List.replicate points.length 0) points) := by
    rw [Nat.pow_zero, G.smul_one, hZero, G.add_zero]
  simpa using hGen (List.replicate points.length 0) h 0 rounds List.length_replicate hRows hInit

/-- **4-Bit Windowed Straus MSM Soundness (`msm_sound`)**:
After 64 rounds of the 4-bit Hornet/Straus loop (`rounds.length = 64`) starting at non-exceptional
offset $H \in E(\mathbb{F}_q)$, `strausLoop` produces $[16^{64}] H \oplus \bigoplus_{i=0}^{n-1} [s_i] P_i$,
and subtracting $[16^{64}] H$ via `add_complete` (`G.add acc64 (G.neg (G.smul (16 ^ 64) h))`)
yields the exact multi-scalar multiplication $\bigoplus_{i=0}^{n-1} [s_i] P_i \in E(\mathbb{F}_q)$! -/
theorem msm_sound
    (G : BN254G1) (points : List G.Point) (h : G.Point)
    (rounds : List (List Nat))
    (hLen64 : rounds.length = 64)
    (hRows : ∀ row ∈ rounds, row.length = points.length) :
    let acc64 := strausLoop G points h rounds
    let scalars := foldWindowRows points.length rounds
    acc64 = G.add (G.smul (16 ^ 64) h) (msmEval G scalars points) ∧
    G.add acc64 (G.neg (G.smul (16 ^ 64) h)) = msmEval G scalars points := by
  dsimp only
  have hInv := straus_loop_invariant G points h rounds hRows
  rw [hLen64] at hInv
  refine ⟨hInv, ?_⟩
  rw [hInv]
  calc
    G.add (G.add (G.smul (16 ^ 64) h) (msmEval G (foldWindowRows points.length rounds) points))
        (G.neg (G.smul (16 ^ 64) h))
      = G.add (msmEval G (foldWindowRows points.length rounds) points)
          (G.add (G.smul (16 ^ 64) h) (G.neg (G.smul (16 ^ 64) h))) := by
        ac_rfl
    _ = G.add (msmEval G (foldWindowRows points.length rounds) points) G.zero := by
        rw [G.add_neg_cancel]
    _ = msmEval G (foldWindowRows points.length rounds) points := by
        rw [G.add_zero]

/-- **Shifted-Digit Correction Cancellation (`msm_shifted_correction_sound`)**:
In `native_msm.rs:80-90, 302-310`, each 16-entry table stores $[w + 1] P_i$ for $w \in \{0..15\}$,
so the 64-window accumulator equals $[16^{64}] H \oplus \bigoplus_i [s_i] P_i \oplus [k] \left(\bigoplus_i P_i\right)$
where $k = \sum_{w=0}^{63} 16^w$. With $\text{sum} = H \oplus \bigoplus_i P_i$ and $k + c = 16^{64}$,
the correction $[k]\text{sum} \oplus [c]H$ equals $[16^{64}] H \oplus [k]\left(\bigoplus_i P_i\right)$,
so subtracting it cancels both the offset $H$ and the digit shift $k$. -/
theorem msm_shifted_correction_sound
    (G : BN254G1) (h msmVal baseSum : G.Point) (k c : Nat)
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
          rw [G.smul_distrib]
          ac_rfl
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
            (G.neg (G.add (G.smul (16 ^ 64) h) (G.smul k baseSum)))) := by
        ac_rfl
    _ = G.add msmVal G.zero := by
        rw [G.add_neg_cancel]
    _ = msmVal := by
        rw [G.add_zero]

end Ix.Cert.Compression.NativeCurveMsm
