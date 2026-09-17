import Compilatrix.Ixby.Runtime.Native.Scalars

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution ScalarFunction Representation

private theorem canonical (f : Goldilocks) : Goldilocks.reduce f.val = f := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt f.isLt

private def binary (operation : Primitive) : Function := {
  arity := 2
  blocks := #[
    ⟨2, .letOp (.primitive .natToField [.local 0]) 1⟩,
    ⟨3, .letOp (.primitive .natToField [.local 1]) 2⟩,
    ⟨4, .letOp (.primitive operation [.local 2, .local 3]) 3⟩,
    ⟨5, .letOp (.primitive .fieldToNat [.local 4]) 4⟩,
    ⟨6, .ret (.local 5)⟩] }

private theorem binary_returns {program : Program} {id : FunctionId} {operation : Primitive}
    (checked : Checked program id (binary operation)) (limits : Limits)
    (room : 6 ≤ limits.locals) (a b result : Goldilocks)
    (left : NatValid limits a.val) (right : NatValid limits b.val)
    (valid : NatValid limits result.val)
    (evaluated : operation.eval limits [.scalar (.field a), .scalar (.field b)] =
      .ok (.scalar (.field result))) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[natural a.val, natural b.val] continuation)
      (returned (natural result.val) continuation) := by
  have castLeft := eval_natToField limits a.val left
  have castRight := eval_natToField limits b.val right
  rw [canonical] at castLeft castRight
  have castResult := eval_fieldToNat limits result valid
  have localRoom : ∀ n, n ≤ 6 → ¬limits.locals < n := by omega
  apply reaches_of_chunk (fuel := 5) (count := 0)
  iterate 5
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, binary, frameState, returned,
      natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      castLeft, castRight, evaluated, castResult, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.fieldReduce_returns (room : 3 ≤ limits.locals) (n : Nat)
    (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 83 0 #[natural n] continuation)
      (returned (natural (Goldilocks.reduce n).val) continuation) := by
  have code := (certificate.function 83).code
  change program.getFunction 83 = .ok Code.Ix_Ixby_Goldilocks_reduce at code
  have castInput := eval_natToField limits n valid
  have castOutput := eval_fieldToNat limits (Goldilocks.reduce n)
    (Conversion.validate_nat_mono (Nat.mod_le n goldilocksModulus) valid)
  have localRoom : ∀ k, k ≤ 3 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ix_Ixby_Goldilocks_reduce, frameState,
      returned, natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      castInput, castOutput, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.fieldAdd_returns (room : 6 ≤ limits.locals) (a b : Goldilocks)
    (left : NatValid limits a.val) (right : NatValid limits b.val)
    (valid : NatValid limits (a.add b).val) (continuation : Array Continuation) :
    Reaches limits program (frameState 84 0 #[natural a.val, natural b.val] continuation)
      (returned (natural (a.add b).val) continuation) :=
  binary_returns (certificate.function 84) limits room a b _ left right valid
    (eval_fieldAdd limits a b) continuation

theorem Certificate.fieldSub_returns (room : 6 ≤ limits.locals) (a b : Goldilocks)
    (left : NatValid limits a.val) (right : NatValid limits b.val)
    (valid : NatValid limits (a.sub b).val) (continuation : Array Continuation) :
    Reaches limits program (frameState 85 0 #[natural a.val, natural b.val] continuation)
      (returned (natural (a.sub b).val) continuation) :=
  binary_returns (certificate.function 85) limits room a b _ left right valid
    (eval_fieldSub limits a b) continuation

theorem Certificate.fieldMul_returns (room : 6 ≤ limits.locals) (a b : Goldilocks)
    (left : NatValid limits a.val) (right : NatValid limits b.val)
    (valid : NatValid limits (a.mul b).val) (continuation : Array Continuation) :
    Reaches limits program (frameState 86 0 #[natural a.val, natural b.val] continuation)
      (returned (natural (a.mul b).val) continuation) :=
  binary_returns (certificate.function 86) limits room a b _ left right valid
    (eval_fieldMul limits a b) continuation

theorem Certificate.fieldNeg_returns (room : 4 ≤ limits.locals) (a : Goldilocks)
    (input : NatValid limits a.val) (output : NatValid limits a.neg.val)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 87 0 #[natural a.val] continuation)
      (returned (natural a.neg.val) continuation) := by
  have code := (certificate.function 87).code
  change program.getFunction 87 = .ok Code.Ix_Ixby_Goldilocks_neg at code
  have castInput := eval_natToField limits a.val input
  rw [canonical] at castInput
  have evaluated := eval_fieldSub limits 0 a
  have castOutput := eval_fieldToNat limits a.neg output
  have same : Goldilocks.sub 0 a = a.neg := by apply Fin.ext; simp [Goldilocks.sub, Goldilocks.neg]
  rw [same] at evaluated
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ix_Ixby_Goldilocks_neg, frameState,
      returned, natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      castInput, evaluated, castOutput, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.fieldInverse_returns (room : 4 ≤ limits.locals) (a : Goldilocks)
    (input : NatValid limits a.val) (output : NatValid limits a.inverse.val)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 88 0 #[natural a.val] continuation)
      (returned (natural a.inverse.val) continuation) := by
  have code := (certificate.function 88).code
  change program.getFunction 88 = .ok Code.Ix_Ixby_Goldilocks_inverse at code
  have castInput := eval_natToField limits a.val input
  rw [canonical] at castInput
  have evaluated := eval_fieldInverse limits a
  have castOutput := eval_fieldToNat limits a.inverse output
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ix_Ixby_Goldilocks_inverse, frameState,
      returned, natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      castInput, evaluated, castOutput, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.extMk_returns (room : 5 ≤ limits.locals) (a b : Goldilocks)
    (left : NatValid limits a.val) (right : NatValid limits b.val)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 89 0 #[natural a.val, natural b.val] continuation)
      (returned (.scalar (.extField ⟨a, b⟩)) continuation) := by
  have code := (certificate.function 89).code
  change program.getFunction 89 = .ok Code.Ix_Ixby_ExtGoldilocks_mk at code
  have castLeft := eval_natToField limits a.val left
  have castRight := eval_natToField limits b.val right
  rw [canonical] at castLeft castRight
  have evaluated := eval_extPack limits a b
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ix_Ixby_ExtGoldilocks_mk, frameState,
      returned, natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp,
      castLeft, castRight, evaluated, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.extAdd_returns (room : 3 ≤ limits.locals) (a b : ExtGoldilocks)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 90 0 #[.scalar (.extField a), .scalar (.extField b)] continuation)
      (returned (.scalar (.extField (a.add b))) continuation) :=
  (certificate.function 90).binary_returns limits room _ _ _ (eval_extAdd limits a b) continuation

theorem Certificate.extSub_returns (room : 3 ≤ limits.locals) (a b : ExtGoldilocks)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 91 0 #[.scalar (.extField a), .scalar (.extField b)] continuation)
      (returned (.scalar (.extField (a.sub b))) continuation) :=
  (certificate.function 91).binary_returns limits room _ _ _ (eval_extSub limits a b) continuation

theorem Certificate.extMul_returns (room : 3 ≤ limits.locals) (a b : ExtGoldilocks)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 92 0 #[.scalar (.extField a), .scalar (.extField b)] continuation)
      (returned (.scalar (.extField (a.mul b))) continuation) :=
  (certificate.function 92).binary_returns limits room _ _ _ (eval_extMul limits a b) continuation

theorem Certificate.extInverse_returns (room : 2 ≤ limits.locals) (a : ExtGoldilocks)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 93 0 #[.scalar (.extField a)] continuation)
      (returned (.scalar (.extField a.inverse)) continuation) :=
  (certificate.function 93).unary_returns limits room _ _ (eval_extInverse limits a) continuation

theorem Certificate.extEq_returns (room : 3 ≤ limits.locals) (a b : ExtGoldilocks)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 94 0 #[.scalar (.extField a), .scalar (.extField b)] continuation)
      (returned (.scalar (.bool (a == b))) continuation) :=
  (certificate.function 94).binary_returns limits room _ _ _ (eval_extEq limits a b) continuation

omit certificate in
private theorem projection_returns {id : FunctionId} {operation : Primitive} (a : ExtGoldilocks)
    (result : Goldilocks) (valid : NatValid limits result.val) (room : 3 ≤ limits.locals)
    (checked : Checked program id { arity := 1, blocks := #[
      ⟨1, .letOp (.primitive operation [.local 0]) 1⟩,
      ⟨2, .letOp (.primitive .fieldToNat [.local 1]) 2⟩,
      ⟨3, .ret (.local 2)⟩] })
    (evaluated : operation.eval limits [.scalar (.extField a)] = .ok (.scalar (.field result)))
    (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[.scalar (.extField a)] continuation)
      (returned (natural result.val) continuation) := by
  have castResult := eval_fieldToNat limits result valid
  have localRoom : ∀ k, k ≤ 3 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, frameState, returned, natural,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated, castResult,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.extFst_returns (room : 3 ≤ limits.locals) (a : ExtGoldilocks)
    (valid : NatValid limits a.c0.val) (continuation : Array Continuation) :
    Reaches limits program (frameState 95 0 #[.scalar (.extField a)] continuation)
      (returned (natural a.c0.val) continuation) :=
  projection_returns limits a a.c0 valid room (certificate.function 95) (eval_extFst limits a) continuation

theorem Certificate.extSnd_returns (room : 3 ≤ limits.locals) (a : ExtGoldilocks)
    (valid : NatValid limits a.c1.val) (continuation : Array Continuation) :
    Reaches limits program (frameState 96 0 #[.scalar (.extField a)] continuation)
      (returned (natural a.c1.val) continuation) :=
  projection_returns limits a a.c1 valid room (certificate.function 96) (eval_extSnd limits a) continuation

end Compilatrix.Ixby.Runtime.Native
