import Mathlib.Tactic
import Std.Tactic.BVDecide

/-! Arithmetic identities used by the ordinary Aiur byte library to reuse
XOR's fixed lookup for AND/OR. The BitVec decision procedure produces a checked
proof, then the identities lift to any field in which two is nonzero. -/
namespace Aiur.Library.U8

theorem xor_and_sum (a b : BitVec 8) :
    a.toNat + b.toNat = (a ^^^ b).toNat + 2 * (a &&& b).toNat := by
  have bits : a.zeroExtend 10 + b.zeroExtend 10 =
      (a ^^^ b).zeroExtend 10 + 2 * (a &&& b).zeroExtend 10 := by bv_decide
  have h := congrArg BitVec.toNat bits
  simp only [BitVec.zeroExtend, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth] at h
  norm_num at h
  have ha := a.isLt
  have hb := b.isLt
  have hx := (a ^^^ b).isLt
  have hy := (a &&& b).isLt
  simp only [BitVec.toNat_xor, BitVec.toNat_and] at *
  omega

theorem xor_or_sum (a b : BitVec 8) :
    2 * (a ||| b).toNat = a.toNat + b.toNat + (a ^^^ b).toNat := by
  have bits : 2 * (a ||| b).zeroExtend 10 =
      a.zeroExtend 10 + b.zeroExtend 10 + (a ^^^ b).zeroExtend 10 := by bv_decide
  have h := congrArg BitVec.toNat bits
  simp only [BitVec.zeroExtend, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth] at h
  norm_num at h
  have ha := a.isLt
  have hb := b.isLt
  have hx := (a ^^^ b).isLt
  have hy := (a ||| b).isLt
  simp only [BitVec.toNat_xor, BitVec.toNat_or] at *
  omega

theorem and_field {F : Type*} [Field F] (two : (2 : F) ≠ 0) (a b : BitVec 8) :
    ((a.toNat : F) + b.toNat - (a ^^^ b).toNat) / 2 = ((a &&& b).toNat : F) := by
  have h := congrArg (fun n : Nat => (n : F)) (xor_and_sum a b)
  push_cast at h
  apply (div_eq_iff two).mpr
  linear_combination h

theorem or_field {F : Type*} [Field F] (two : (2 : F) ≠ 0) (a b : BitVec 8) :
    ((a.toNat : F) + b.toNat + (a ^^^ b).toNat) / 2 = ((a ||| b).toNat : F) := by
  have h := congrArg (fun n : Nat => (n : F)) (xor_or_sum a b)
  push_cast at h
  apply (div_eq_iff two).mpr
  linear_combination -h

end Aiur.Library.U8
