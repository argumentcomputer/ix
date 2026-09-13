/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Aiur.Proofs.Execution
import Ix.Aiur.Proofs.Memory
import Ix.Aiur.Proofs.LocalConstraints

/-! Concrete local semantics and finite-derivation regressions. The native
supplied-row counterparts live in `synthesis/tests/advice.rs`. -/

open Aiur Aiur.Bytecode Aiur.Bytecode.AIR

namespace Tests.Aiur.AIRSemantics

private def fixtures : Array (String × Op × Array G × Array G × Option (Array G)) := #[
  ("constant", .const 7, #[], #[], some #[7]),
  ("addition", .add 0 1, #[255, 2], #[], some #[257]),
  ("subtraction", .sub 0 1, #[255, 2], #[], some #[253]),
  ("multiplication", .mul 0 1, #[255, 2], #[], some #[510]),
  ("zero", .eqZero 0, #[0], #[], some #[1]),
  ("nonzero", .eqZero 0, #[9], #[], some #[0]),
  ("constrained-call-needs-provider", .call 1 #[0] 1 false, #[3], #[7], none),
  ("unconstrained-call-advice", .call 1 #[0] 1 true, #[3], #[7], some #[7]),
  ("unconstrained-call-width", .call 1 #[0] 1 true, #[3], #[7, 8], none),
  ("store-needs-memory", .store #[0], #[3], #[7], none),
  ("load-needs-memory", .load 1 0, #[7], #[3], none),
  ("assertion", .assertEq #[0] #[1] none, #[7, 7], #[], some #[]),
  ("false-assertion", .assertEq #[0] #[1] none, #[7, 8], #[], none),
  ("assertion-width", .assertEq #[0] #[0, 1] none, #[7, 8], #[], none),
  ("key-info-advice", .ioGetInfo 0 #[], #[0], #[300, 301], some #[300, 301]),
  ("key-insertion-no-relation", .ioSetInfo 0 #[] 1 2, #[0, 9, 4], #[], some #[]),
  ("read-advice", .ioRead 0 1 2, #[0, 9], #[302, 303], some #[302, 303]),
  ("read-width", .ioRead 0 1 2, #[0, 9], #[302], none),
  ("write-no-relation", .ioWrite 0 #[1], #[0, 7], #[], some #[]),
  ("bit-decomposition", .u8BitDecomposition 0, #[129], #[], some #[1, 0, 0, 0, 0, 0, 0, 1]),
  ("shift-left", .u8ShiftLeft 0, #[129], #[], some #[2]),
  ("shift-right", .u8ShiftRight 0, #[129], #[], some #[64]),
  ("xor", .u8Xor 0 1, #[255, 2], #[], some #[253]),
  ("add-with-carry", .u8Add 0 1, #[255, 2], #[], some #[1, 1]),
  ("byte-product", .u8Mul 0 1, #[255, 2], #[], some #[254, 1]),
  ("subtract-with-borrow", .u8Sub 0 1, #[2, 255], #[], some #[3, 1]),
  ("and", .u8And 0 1, #[255, 2], #[], some #[2]),
  ("or", .u8Or 0 1, #[255, 2], #[], some #[255]),
  ("byte-less-than", .u8LessThan 0 1, #[2, 255], #[], some #[1]),
  ("word-less-than", .u32LessThan 0 1, #[65536, 65537], #[], some #[1]),
  ("word-input-range", .u32LessThan 0 1, #[4294967296, 65537], #[], none),
  ("split-seven", .u8XorSplit7 0 1, #[255, 2], #[], some #[1, 250]),
  ("split-four", .u8XorSplit4 0 1, #[255, 2], #[], some #[15, 208]),
  ("debug-no-relation", .debug "test" (some #[0]), #[7], #[], some #[]),
  ("byte-range", .u8RangeCheck 0 1, #[255, 0], #[], some #[]),
  ("invalid-byte-range", .u8RangeCheck 0 1, #[256, 0], #[], none),
  ("byte-operation-requires-range", .u8Xor 0 1, #[256, 0], #[], none),
  ("division-advice", .unconstrainedBigUintDivMod 0 1, #[3, 2], #[304, 305], some #[304, 305]),
  ("decomposition-advice", .unconstrainedGToBytes 0, #[1],
    #[306, 307, 308, 309, 310, 311, 312, 313], some #[306, 307, 308, 309, 310, 311, 312, 313]),
  ("inverse-advice", .unconstrainedGInverse 0, #[1], #[314], some #[314]),
  ("word-add", .unconstrainedU32Add #[0, 1, 2, 3] #[4, 5, 6, 7],
    #[255, 255, 255, 255, 1, 0, 0, 0], #[0, 0, 0, 0], some #[0, 0, 0, 0, 1]),
  ("word-add-three", .unconstrainedU32Add3 #[0, 1, 2, 3] #[0, 1, 2, 3] #[0, 1, 2, 3],
    #[255, 255, 255, 255], #[253, 255, 255, 255], some #[253, 255, 255, 255, 2]),
  ("word-packing", .u32ToField #[0, 1, 2, 3], #[1, 2, 3, 4], #[], some #[67305985]),
  ("word-packing-width", .u32ToField #[0, 1, 2], #[1, 2, 3], #[], none),
  ("invalid-value-index", .mul 0 2, #[3, 5], #[], none)]

private def noMemory : Memory := fun _ _ _ => False

private def identity : Function :=
  ⟨⟨#[], .return 0 #[0]⟩, ⟨1, 1, 7, 4⟩, false, true⟩

private def caller : Function :=
  ⟨⟨#[.call 1 #[0] 1 false, .call 1 #[0] 1 false, .add 1 2], .return 0 #[3]⟩,
    ⟨1, 1, 23, 12⟩, true, true⟩

private def sharedProgram : Toplevel := ⟨#[caller, identity], #[], #[], #[]⟩
private def child : Call := ⟨1, #[3], #[3], 1⟩
private def parent : Call := ⟨0, #[3], #[6], 0⟩

private theorem childExecutes : Execution sharedProgram noMemory child := by
  apply Execution.function (calls := [])
  · apply RunFunction.function (function := identity) rfl rfl
    apply RunBlock.block (intermediate := #[3]) (opCalls := []) (ctrlCalls := [])
    · exact RunOps.nil
    · exact RunCtrl.returned (by cbv)
  · simp

/-- A shared callee supplies both calls; the finite derivation needs no
sequential cache state or multiplicity-dependent replay. -/
example : Execution sharedProgram noMemory parent := by
  apply Execution.function (calls := [child, child])
  · apply RunFunction.function (function := caller) rfl rfl
    apply RunBlock.block (intermediate := #[3, 3, 3, 6])
      (opCalls := [child, child]) (ctrlCalls := [])
    · apply RunOps.cons (intermediate := #[3, 3]) (firstCalls := [child]) (restCalls := [child])
      · exact Step.call (request := child) (by cbv) rfl
      · apply RunOps.cons (intermediate := #[3, 3, 3]) (firstCalls := [child]) (restCalls := [])
        · exact Step.call (request := child) (by cbv) rfl
        · exact RunOps.cons (Step.primitive (outputs := #[6]) (advice := #[]) (by cbv)) RunOps.nil
    · exact RunCtrl.returned (by cbv)
  · intro called member
    have : called = child := by simpa using member
    subst called
    exact childExecutes

private def yieldingArm : Block := ⟨#[.const 99, .const 5], .yield 0 #[2]⟩
private def continuation : Block := ⟨#[.const 7, .add 1 2], .return 1 #[3]⟩

/-- The branch-local 99 does not leak into the continuation's namespace. -/
example : RunCtrl noMemory
    (.matchContinue 0 #[(0, yieldingArm)] none 1 0 0 continuation)
    #[0] (.returned #[12]) [] := by
  apply RunCtrl.matchContinueYield (branchCalls := []) (contCalls := []) (yielded := #[5])
    (scrutinee := 0) (arm := yieldingArm) (by cbv) (SelectArm.case (by simp))
  · apply RunBlock.block (intermediate := #[0, 99, 5]) (opCalls := []) (ctrlCalls := [])
    · exact RunOps.cons (Step.primitive (outputs := #[99]) (advice := #[]) (by cbv))
        (RunOps.cons (Step.primitive (outputs := #[5]) (advice := #[]) (by cbv)) RunOps.nil)
    · exact RunCtrl.yielded (by cbv)
  · rfl
  · apply RunBlock.block (intermediate := #[0, 5, 7, 12]) (opCalls := []) (ctrlCalls := [])
    · exact RunOps.cons (Step.primitive (outputs := #[7]) (advice := #[]) (by cbv))
        (RunOps.cons (Step.primitive (outputs := #[12]) (advice := #[]) (by cbv)) RunOps.nil)
    · exact RunCtrl.returned (by cbv)

private def returningArm : Block := ⟨#[.const 5], .return 0 #[1]⟩
private def impossibleContinuation : Block :=
  ⟨#[.const 1, .assertEq #[0] #[1] none], .return 1 #[]⟩

/-- A branch return skips an otherwise failing continuation. -/
example : RunCtrl noMemory
    (.matchContinue 0 #[(0, returningArm)] none 0 0 0 impossibleContinuation)
    #[0] (.returned #[5]) [] := by
  apply RunCtrl.matchContinueReturn (scrutinee := 0) (arm := returningArm)
    (by cbv) (SelectArm.case (by simp))
  apply RunBlock.block (intermediate := #[0, 5]) (opCalls := []) (ctrlCalls := [])
  · exact RunOps.cons (Step.primitive (outputs := #[5]) (advice := #[]) (by cbv)) RunOps.nil
  · exact RunCtrl.returned (by cbv)

private def memory : Memory := fun width pointer contents =>
  width = 1 ∧ pointer = 7 ∧ contents = #[3]

example : Step memory (.store #[0]) #[3] #[3, 7] [] :=
  Step.store (by cbv) ⟨rfl, rfl, rfl⟩

example : Step memory (.load 1 0) #[7] #[7, 3] [] :=
  Step.load (pointer := 7) (contents := #[3]) (by cbv) rfl ⟨rfl, rfl, rfl⟩

private def wrappingRows : Array Aiur.AIR.MemoryRow := #[
  ⟨1, 0, G.ofNat (gSize.toNat - 1), #[7]⟩,
  ⟨1, 1, 0, #[8]⟩,
  ⟨0, 0, 0, #[0]⟩,
  ⟨0, 0, 0, #[0]⟩]

/-- The same four-row wrapping memory table used by the supplied native proof. -/
private theorem wrappingRows_polynomials : Aiur.AIR.MemoryRowsPolynomials 1 wrappingRows := by
  constructor
  all_goals
    intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      simp only [wrappingRows, List.size_toArray, List.length_cons, List.length_nil] at hi
      omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals decide +revert +kernel

example : wrappingRows[0].pointer ≠ wrappingRows[1].pointer := by
  intro same
  have impossible := wrappingRows_polynomials.valid.pointer_injective (by decide) 0 1
    (by decide) (by decide) rfl rfl same
  contradiction

def main : IO Unit := do
  for (label, op, values, advice, expected) in fixtures do
    unless primitive op values advice == expected do
      throw (IO.userError s!"AIR semantics fixture failed: {label}")
  -- The result bytes of an unchecked u32 sum may exceed 255, while its
  -- computed carry must still satisfy the field equation.
  let values : Array G := #[1, 2, 3, 4, 5, 6, 7, 8]
  let bytes : Array G := #[316, 317, 318, 319]
  let some output := primitive (.unconstrainedU32Add #[0, 1, 2, 3] #[4, 5, 6, 7]) values bytes
    | throw (IO.userError "unchecked u32 advice was rejected")
  unless output.size == 5 && output.extract 0 4 == bytes &&
      output[4]?.getD 0 * 4294967296 + packWord bytes ==
        packWord (values.extract 0 4) + packWord (values.extract 4 8) do
    throw (IO.userError "virtual u32 carry equation failed")
  IO.println s!"AIR semantics: {fixtures.size} operation fixtures and unchecked virtual carry passed."

end Tests.Aiur.AIRSemantics

def main := Tests.Aiur.AIRSemantics.main
