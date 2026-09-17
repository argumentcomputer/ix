import Compilatrix.Ixby.Runtime.Native.Machine
import Compilatrix.Ixby.Runtime.Native.Values
import Compilatrix.Ixby.Runtime.ToWord
import Compilatrix.Ixby.Runtime.FromWord

/-! Scalar contracts for the actual unboxed runtime prefix. All capacities
are semantic premises; no theorem upgrades the paged prover's Nat128 bound. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution ScalarFunction Representation

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.toWord_returns (room : 6 ≤ limits.locals) (n : Nat)
    (weight accumulator : UInt32) (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 0 0 #[natural n, word weight, word accumulator] continuation)
      (returned (word (accumulator + n.toUInt32 * weight)) continuation) :=
  Conversion.toWord_returns (digit := 0) (certificate.function 0) limits room n weight accumulator valid continuation

theorem Certificate.fromWordLoop_returns (room : 6 ≤ limits.locals) (w : UInt32)
    (weight accumulator : Nat) (wordValid : NatValid limits w.toNat)
    (weightValid : NatValid limits weight) (valid : NatValid limits (accumulator + w.toNat * weight))
    (continuation : Array Continuation) :
    Reaches limits program
      (frameState 1 0 #[word w, natural weight, natural accumulator] continuation)
      (returned (natural (accumulator + w.toNat * weight)) continuation) :=
  Conversion.fromWordLoop_returns (digit := 0) (certificate.function 1) limits room w weight accumulator
    wordValid weightValid valid continuation

theorem Certificate.fromWord_returns (room : 2 ≤ limits.locals) (w : UInt32)
    (valid : NatValid limits w.toNat) (continuation : Array Continuation) :
    Reaches limits program (frameState 2 0 #[word w] continuation)
      (returned (natural w.toNat) continuation) :=
  (certificate.function 2).unary_returns limits room _ _ (eval_word32ToNat limits w valid) continuation

theorem Certificate.fromRaw_returns (room : 1 ≤ limits.locals) (n : Nat)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 3 0 #[natural n] continuation)
      (returned (natural n) continuation) :=
  (certificate.function 3).identity_returns limits room _ continuation

theorem Certificate.lowWord_returns (room : 2 ≤ limits.locals) (n : Nat)
    (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 4 0 #[natural n] continuation)
      (returned (word n.toUInt32) continuation) :=
  (certificate.function 4).unary_returns limits room _ _ (eval_natToWord32 limits n valid) continuation

theorem Certificate.natural_returns (room : 1 ≤ limits.locals) (n : Nat)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 5 0 #[natural n] continuation)
      (returned (natural n) continuation) :=
  (certificate.function 5).identity_returns limits room _ continuation

theorem Certificate.fieldNatural_returns (room : 2 ≤ limits.locals) (f : Goldilocks)
    (valid : NatValid limits f.val) (continuation : Array Continuation) :
    Reaches limits program (frameState 6 0 #[field f] continuation)
      (returned (natural f.val) continuation) :=
  (certificate.function 6).unary_returns limits room _ _ (eval_fieldToNat limits f valid) continuation

theorem Certificate.asField_returns (room : 2 ≤ limits.locals) (n : Nat)
    (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 7 0 #[natural n] continuation)
      (returned (field (Goldilocks.reduce n)) continuation) :=
  (certificate.function 7).unary_returns limits room _ _ (eval_natToField limits n valid) continuation

theorem Certificate.fieldFromNatural_returns (room : 2 ≤ limits.locals) (n : Nat)
    (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 8 0 #[natural n] continuation)
      (returned (field (Goldilocks.reduce n)) continuation) :=
  (certificate.function 8).unary_returns limits room _ _ (eval_natToField limits n valid) continuation

theorem Certificate.natAdd_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (result : NatValid limits (a + b))
    (continuation : Array Continuation) :
    Reaches limits program (frameState 12 0 #[natural a, natural b] continuation)
      (returned (natural (a + b)) continuation) :=
  (certificate.function 12).binary_returns limits room _ _ _
    (eval_natAdd limits a b left right result) continuation

theorem Certificate.natSub_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 13 0 #[natural a, natural b] continuation)
      (returned (natural (a - b)) continuation) :=
  (certificate.function 13).binary_returns limits room _ _ _
    (eval_natSub limits a b left right (Conversion.validate_nat_mono (Nat.sub_le ..) left)) continuation

theorem Certificate.natMul_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (result : NatValid limits (a * b))
    (continuation : Array Continuation) :
    Reaches limits program (frameState 14 0 #[natural a, natural b] continuation)
      (returned (natural (a * b)) continuation) :=
  (certificate.function 14).binary_returns limits room _ _ _
    (eval_natMul limits a b left right result) continuation

theorem Certificate.natDiv_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 15 0 #[natural a, natural b] continuation)
      (returned (natural (a / b)) continuation) :=
  (certificate.function 15).binary_returns limits room _ _ _
    (eval_natDiv limits a b left right (Conversion.validate_nat_mono (Nat.div_le_self ..) left)) continuation

theorem Certificate.natMod_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 16 0 #[natural a, natural b] continuation)
      (returned (natural (a % b)) continuation) :=
  (certificate.function 16).binary_returns limits room _ _ _
    (eval_natMod limits a b left right (Conversion.validate_nat_mono (Nat.mod_le ..) left)) continuation

theorem Certificate.natEq_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 17 0 #[natural a, natural b] continuation)
      (returned (.scalar (.bool (a == b))) continuation) :=
  (certificate.function 17).binary_returns limits room _ _ _
    (eval_natEq limits a b left right) continuation

theorem Certificate.natLt_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 18 0 #[natural a, natural b] continuation)
      (returned (.scalar (.bool (a < b))) continuation) :=
  (certificate.function 18).binary_returns limits room _ _ _
    (eval_natLt limits a b left right) continuation

theorem Certificate.natLe_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 19 0 #[natural a, natural b] continuation)
      (returned (.scalar (.bool (a ≤ b))) continuation) := by
  have code := (certificate.function 19).code
  change program.getFunction 19 = .ok Code.Nat_decLe at code
  have evaluated := eval_natLt limits b a right left
  have localRoom : ∀ n, n ≤ 3 → ¬limits.locals < n := by omega
  by_cases order : a ≤ b
  · apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.Nat_decLe, frameState, returned,
        natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated,
        order, show ¬b < a by omega, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  · apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.Nat_decLe, frameState, returned,
        natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp, evaluated,
        order, show b < a by omega, localRoom, bind, Except.bind, pure, Except.pure]
    rfl

end Compilatrix.Ixby.Runtime.Native
