import Ix.Compiler.X86.ScalarTotal

namespace Ix.Compiler.X86.Scalar
open WordRegion

/-- A caller-provided finite stack reservation. It includes the external
return slot. No initial contents of local or saved-base slots are required. -/
structure Stack where
  base : Word
  depth : Nat
  positive : 0 < depth
  aligned : base % 16 = 0
  fits : base.toNat + 272 * depth ≤ UInt64.size

def Stack.layout (stack : Stack) : Layout where
  base := stack.base
  slots := frameStride * stack.depth
  aligned := by
    apply UInt64.toNat_inj.mp
    have aligned := congrArg UInt64.toNat stack.aligned
    simp only [UInt64.toNat_mod] at aligned ⊢
    change stack.base.toNat % 16 = 0 at aligned
    change stack.base.toNat % 8 = 0
    omega
  fits := by simpa only [frameStride, ← Nat.mul_assoc] using stack.fits

def Stack.frame (stack : Stack) : Frame stack.layout where
  top := frameStride * stack.depth - 1
  enough := by have := stack.positive; simp only [frameStride]; omega
  bound := by have := stack.positive; simp only [Stack.layout, frameStride]; omega
  aligned := by
    simp only [SysV.functionEntryAligned, beq_iff_eq]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_mod]
    change (stack.layout.address (frameStride * stack.depth - 1)).toNat % 16 = 8
    rw [stack.layout.address_toNat (by have := stack.positive; simp only [Stack.layout, frameStride]; omega)]
    have aligned := congrArg UInt64.toNat stack.aligned
    simp only [UInt64.toNat_mod] at aligned
    change stack.base.toNat % 16 = 0 at aligned
    have := stack.positive
    simp only [Stack.layout, frameStride]
    omega
  partition := by simp only [frameStride]; have := stack.positive; omega

theorem Stack.bytes (stack : Stack) : 8 * stack.layout.slots = 272 * stack.depth := by
  simp [Stack.layout, frameStride, ← Nat.mul_assoc]

theorem Stack.below_entry (stack : Stack) :
    (stack.layout.address stack.frame.top).toNat - stack.base.toNat = 272 * stack.depth - 8 := by
  rw [stack.layout.address_toNat stack.frame.bound]
  have := stack.positive
  simp only [Stack.layout, Stack.frame, frameStride]
  omega

theorem Stack.rank_capacity (stack : Stack) {index : Nat} (depth : index < stack.depth) :
    frameStride * (index + 1) - 1 ≤ stack.frame.top := by
  simp only [Stack.frame, frameStride]
  omega

end Ix.Compiler.X86.Scalar
