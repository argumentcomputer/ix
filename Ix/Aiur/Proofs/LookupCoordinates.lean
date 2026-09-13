/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.LookupCoordinates
import Ix.Aiur.Proofs.ExtensionField

/-! Ring laws for the separate logUp coordinates, and the field identification
available on base-field trace rows. No field instance is assigned to coordinates
over the challenge field. -/

namespace Aiur.NativeAIR.LogUp.Coordinates

theorem ext {a b : Coordinates W} (first : a.c0 = b.c0) (second : a.c1 = b.c1) : a = b := by
  cases a; cases b; cases first; cases second; rfl

theorem zero_iff [OfNat W 0] (a : Coordinates W) : a = 0 ↔ a.c0 = 0 ∧ a.c1 = 0 := by
  constructor
  · intro same; cases same; exact ⟨rfl, rfl⟩
  · exact fun same => ext same.1 same.2

theorem flatten_length (values : List (Coordinates W)) : (flatten values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [flatten, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *; omega

theorem flatten_zero_iff [OfNat W 0] (values : List (Coordinates W)) :
    (∀ x ∈ flatten values, x = 0) ↔ ∀ value ∈ values, value = 0 := by
  constructor
  · intro zero value member
    apply (zero_iff value).mpr
    exact ⟨zero _ (List.mem_flatMap.mpr ⟨value, member, by simp⟩),
      zero _ (List.mem_flatMap.mpr ⟨value, member, by simp⟩)⟩
  · intro zero x member
    obtain ⟨value, present, coordinate⟩ := List.mem_flatMap.mp member
    cases zero value present
    change x ∈ [(0 : W), 0] at coordinate
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using coordinate

section Algebra

variable {W : Type u} [Lean.Grind.CommRing W]

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

theorem mul_schoolbook (a b : Coordinates W) :
    a * b = ⟨a.c0 * b.c0 + 7 * a.c1 * b.c1, a.c0 * b.c1 + a.c1 * b.c0⟩ := by
  apply ext
  · change a.c0 * b.c0 + (a.c1 * b.c1) * 7 = _; grind
  · change (a.c0 + a.c1) * (b.c0 + b.c1) - a.c0 * b.c0 - a.c1 * b.c1 = _; grind

theorem add_zero (a : Coordinates W) : a + 0 = a := by
  apply ext <;> change _ + (0 : W) = _ <;> grind

theorem add_comm (a b : Coordinates W) : a + b = b + a := by
  apply ext <;> change (_ : W) + _ = _ + _ <;> grind

theorem add_assoc (a b c : Coordinates W) : a + b + c = a + (b + c) := by
  apply ext <;> change (_ : W) + _ + _ = _ + (_ + _) <;> grind

theorem mul_one (a : Coordinates W) : a * 1 = a := by
  rw [mul_schoolbook]
  apply ext
  · change a.c0 * 1 + 7 * a.c1 * 0 = a.c0; grind
  · change a.c0 * 0 + a.c1 * 1 = a.c1; grind

theorem mul_zero (a : Coordinates W) : a * 0 = 0 := by
  rw [mul_schoolbook]
  apply ext
  · change a.c0 * 0 + 7 * a.c1 * 0 = (0 : W); grind
  · change a.c0 * 0 + a.c1 * 0 = (0 : W); grind

theorem mul_comm (a b : Coordinates W) : a * b = b * a := by
  rw [mul_schoolbook, mul_schoolbook]
  apply ext <;> dsimp only <;> grind

theorem mul_assoc (a b c : Coordinates W) : a * b * c = a * (b * c) := by
  simp only [mul_schoolbook]
  apply ext <;> dsimp only <;> grind

theorem left_distrib (a b c : Coordinates W) : a * (b + c) = a * b + a * c := by
  simp only [mul_schoolbook]
  apply ext
  · change a.c0 * (b.c0 + c.c0) + 7 * a.c1 * (b.c1 + c.c1) =
      (a.c0 * b.c0 + 7 * a.c1 * b.c1) + (a.c0 * c.c0 + 7 * a.c1 * c.c1)
    grind
  · change a.c0 * (b.c1 + c.c1) + a.c1 * (b.c0 + c.c0) =
      (a.c0 * b.c1 + a.c1 * b.c0) + (a.c0 * c.c1 + a.c1 * c.c0)
    grind

theorem neg_add_cancel (a : Coordinates W) : -a + a = 0 := by
  apply ext <;> change -(_ : W) + _ = 0 <;> grind

theorem sub_eq_add_neg (a b : Coordinates W) : a - b = a + -b := by
  apply ext <;> change (_ : W) - _ = _ + -_ <;> grind

theorem ofBase_add (a b : W) : ofBase (a + b) = ofBase a + ofBase b := by
  apply ext
  · rfl
  · change (0 : W) = 0 + 0; grind

theorem ofBase_neg (a : W) : ofBase (-a) = -ofBase a := by
  apply ext
  · rfl
  · change (0 : W) = -0; grind

theorem ofBase_mul (a b : W) : ofBase (a * b) = ofBase a * ofBase b := by
  rw [mul_schoolbook]
  apply ext
  · change a * b = a * b + 7 * 0 * 0; grind
  · change (0 : W) = a * 0 + 0 * b; grind

instance natCast : NatCast (Coordinates W) := ⟨fun n => ofBase (Nat.cast n)⟩
instance intCast : IntCast (Coordinates W) := ⟨fun n => ofBase (Int.cast n)⟩
instance nsmul : SMul Nat (Coordinates W) := ⟨fun n a => ofBase (Nat.cast n) * a⟩
instance zsmul : SMul Int (Coordinates W) := ⟨fun n a => ofBase (Int.cast n) * a⟩
instance npow : HPow (Coordinates W) Nat (Coordinates W) := ⟨fun a n => npowRec n a⟩

theorem neg_mul (a b : Coordinates W) : -a * b = -(a * b) := by
  simp only [mul_schoolbook]
  apply ext
  · change -a.c0 * b.c0 + 7 * -a.c1 * b.c1 = -(a.c0 * b.c0 + 7 * a.c1 * b.c1); grind
  · change -a.c0 * b.c1 + -a.c1 * b.c0 = -(a.c0 * b.c1 + a.c1 * b.c0); grind

instance commRing : Lean.Grind.CommRing (Coordinates W) where
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  left_distrib := left_distrib
  zero_mul a := by rw [mul_comm, mul_zero]
  mul_zero := mul_zero
  pow_zero _ := rfl
  pow_succ _ _ := rfl
  ofNat_succ n := by
    change ofBase (OfNat.ofNat (n + 1) : W) = ofBase (OfNat.ofNat n : W) + ofBase (1 : W)
    rw [Lean.Grind.Semiring.ofNat_succ, ofBase_add]
  ofNat_eq_natCast n := by
    change ofBase (OfNat.ofNat n : W) = ofBase (Nat.cast n : W)
    rw [Lean.Grind.Semiring.ofNat_eq_natCast]
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  intCast_neg n := by
    change ofBase (Int.cast (-n) : W) = -ofBase (Int.cast n : W)
    rw [Lean.Grind.Ring.intCast_neg, ofBase_neg]
  intCast_ofNat n := by
    change ofBase (Int.cast (OfNat.ofNat n) : W) = ofBase (OfNat.ofNat n : W)
    rw [Lean.Grind.Ring.intCast_ofNat]
  zsmul_natCast_eq_nsmul n a := by
    change ofBase (Int.cast (Nat.cast n) : W) * a = ofBase (Nat.cast n : W) * a
    rw [Lean.Grind.Ring.intCast_natCast]
  neg_zsmul n a := by
    change ofBase (Int.cast (-n) : W) * a = -(ofBase (Int.cast n : W) * a)
    rw [Lean.Grind.Ring.intCast_neg, ofBase_neg, neg_mul]

theorem scale_eq_mul (a : Coordinates W) (b : W) : a.scale b = a * ofBase b := by
  rw [mul_schoolbook]
  apply ext
  · change a.c0 * b = a.c0 * b + 7 * a.c1 * 0; grind
  · change a.c1 * b = a.c0 * 0 + a.c1 * b; grind

end Algebra

theorem toExtension_injective {a b : Coordinates G} (same : a.toExtension = b.toExtension) : a = b :=
  ext (congrArg ProofCodec.Extension.c0 same) (congrArg ProofCodec.Extension.c1 same)

theorem toExtension_fromExtension (a : ProofCodec.Extension) : (fromExtension a).toExtension = a := rfl

theorem fromExtension_toExtension (a : Coordinates G) : fromExtension a.toExtension = a := rfl

theorem toExtension_zero_iff (a : Coordinates G) : a.toExtension = 0 ↔ a = 0 :=
  ⟨fun same => toExtension_injective (b := 0) same, fun same => same ▸ rfl⟩

theorem toExtension_ofBase (a : G) : (ofBase a).toExtension = ProofCodec.Extension.ofBase a := rfl
theorem toExtension_add (a b : Coordinates G) : (a + b).toExtension = a.toExtension + b.toExtension := rfl
theorem toExtension_sub (a b : Coordinates G) : (a - b).toExtension = a.toExtension - b.toExtension := rfl

theorem toExtension_mul (a b : Coordinates G) : (a * b).toExtension = a.toExtension * b.toExtension := by
  rw [mul_schoolbook]
  apply ProofCodec.Extension.ext
  · change a.c0 * b.c0 + 7 * a.c1 * b.c1 = a.c0 * b.c0 + a.c1 * (b.c1 * 7); grind
  · rfl

/-- Over challenge-field coordinates, combining them with the basis loses a
constraint: this nonzero pair combines to zero. -/
theorem collapse_loses_constraint :
    let a : Coordinates ProofCodec.Extension := ⟨-ProofCodec.Extension.basis, 1⟩
    a ≠ 0 ∧ a.c0 + a.c1 * ProofCodec.Extension.basis = 0 := by
  constructor
  · intro same
    exact ProofCodec.Extension.one_ne_zero (congrArg Coordinates.c1 same)
  · change -ProofCodec.Extension.basis + 1 * ProofCodec.Extension.basis = 0
    grind

end Aiur.NativeAIR.LogUp.Coordinates
