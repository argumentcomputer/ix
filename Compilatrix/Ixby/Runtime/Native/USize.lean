import Compilatrix.Ixby.Runtime.Native.Scalars

/-! USize is represented by a Nat on the compiler's declared 64-bit source
platform. Wrapping addition and subtraction need 65-bit intermediates. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} (certificate : Certificate program) (limits : Limits)

include certificate

theorem Certificate.usizeOfNat_returns (room : 2 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (n : Nat) (valid : NatValid limits n) (continuation : Array Continuation) :
    Reaches limits program (frameState 44 0 #[natural n] continuation)
      (returned (natural (n % 2 ^ 64)) continuation) := by
  have code := (certificate.function 44).code
  change program.getFunction 44 = .ok Code.USize_ofNat at code
  have modulusValid := validate_nat_of_bits (n := 2 ^ 64) (bits := 65) (by decide) capacity
  have reduced := eval_natMod limits n (2 ^ 64) valid modulusValid
    (validate_nat_mono (Nat.mod_le ..) valid)
  have localRoom : ∀ k, k ≤ 2 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.USize_ofNat, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, reduced, localRoom,
      bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.usizeToNat_returns (room : 1 ≤ limits.locals) (a : USize)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 45 0 #[natural a.toNat] continuation)
      (returned (natural a.toNat) continuation) :=
  (certificate.function 45).identity_returns limits room _ continuation

theorem Certificate.usizeAddRaw_returns (room : 4 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (a b : Nat) (leftBound : a < 2 ^ 64) (rightBound : b < 2 ^ 64)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 46 0 #[natural a, natural b] continuation)
      (returned (natural ((a + b) % 2 ^ 64)) continuation) := by
  have code := (certificate.function 46).code
  change program.getFunction 46 = .ok Code.USize_add at code
  have leftValid := validate_nat_of_bits leftBound (show 64 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits rightBound (show 64 ≤ limits.natBits by omega)
  have modulusValid := validate_nat_of_bits (n := 2 ^ 64) (bits := 65) (by decide) capacity
  have resultValid := validate_nat_of_bits (n := a + b) (bits := 65) (by omega) capacity
  have added := eval_natAdd limits a b leftValid rightValid resultValid
  have reduced := eval_natMod limits (a + b) (2 ^ 64) resultValid modulusValid
    (validate_nat_mono (Nat.mod_le ..) resultValid)
  have localRoom : ∀ k, k ≤ 4 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 3) (count := 0)
  iterate 3
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.USize_add, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, added, reduced,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.usizeAdd_returns (room : 4 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (platform : System.Platform.numBits = 64) (a b : USize) (continuation : Array Continuation) :
    Reaches limits program (frameState 46 0 #[natural a.toNat, natural b.toNat] continuation)
      (returned (natural (a + b).toNat) continuation) := by
  simpa only [USize.toNat_add, platform] using
    certificate.usizeAddRaw_returns limits room capacity a.toNat b.toNat a.toNat_lt b.toNat_lt continuation

def modularSubCode (modulus : Nat) : Function := {
  arity := 2
  blocks := #[
    ⟨2, .letOp (.primitive .natAdd [.local 0, .literal (.nat modulus)]) 1⟩,
    ⟨3, .letOp (.primitive .natSub [.local 2, .local 1]) 2⟩,
    ⟨4, .letOp (.primitive .natMod [.local 3, .literal (.nat modulus)]) 3⟩,
    ⟨5, .ret (.local 4)⟩] }

omit certificate in
theorem modularSub_returns {id : FunctionId} (modulus : Nat)
    (checked : Checked program id (modularSubCode modulus)) (room : 5 ≤ limits.locals)
    (a b : Nat) (leftValid : NatValid limits a) (rightValid : NatValid limits b)
    (modulusValid : NatValid limits modulus) (sumValid : NatValid limits (a + modulus))
    (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[natural a, natural b] continuation)
      (returned (natural ((a + modulus - b) % modulus)) continuation) := by
  have resultValid := validate_nat_mono (Nat.sub_le (a + modulus) b) sumValid
  have added := eval_natAdd limits a modulus leftValid modulusValid sumValid
  have subtracted := eval_natSub limits (a + modulus) b sumValid rightValid resultValid
  have reduced := eval_natMod limits (a + modulus - b) modulus resultValid modulusValid
    (validate_nat_mono (Nat.mod_le ..) resultValid)
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, modularSubCode, frameState, returned,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, natural, added, subtracted, reduced,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem Certificate.usizeSubRaw_returns (room : 5 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (a b : Nat) (leftBound : a < 2 ^ 64) (rightBound : b < 2 ^ 64)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 47 0 #[natural a, natural b] continuation)
      (returned (natural ((a + 2 ^ 64 - b) % 2 ^ 64)) continuation) := by
  exact modularSub_returns limits (2 ^ 64) (certificate.function 47) room a b
    (validate_nat_of_bits leftBound (by omega)) (validate_nat_of_bits rightBound (by omega))
    (validate_nat_of_bits (n := 2 ^ 64) (bits := 65) (by decide) capacity)
    (validate_nat_of_bits (n := a + 2 ^ 64) (bits := 65) (by omega) capacity) continuation

theorem Certificate.usizeSub_returns (room : 5 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (platform : System.Platform.numBits = 64) (a b : USize) (continuation : Array Continuation) :
    Reaches limits program (frameState 47 0 #[natural a.toNat, natural b.toNat] continuation)
      (returned (natural (a - b).toNat) continuation) := by
  have result : (a.toNat + 2 ^ 64 - b.toNat) % 2 ^ 64 = (a - b).toNat := by
    rw [USize.toNat_sub, platform]
    congr 1
    have bound := b.toNat_lt
    omega
  rw [← result]
  exact certificate.usizeSubRaw_returns limits room capacity a.toNat b.toNat a.toNat_lt b.toNat_lt continuation

theorem Certificate.usizeEq_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 48 0 #[natural a, natural b] continuation)
      (returned (.scalar (.bool (a == b))) continuation) :=
  (certificate.function 48).binary_returns limits room _ _ _ (eval_natEq limits a b left right) continuation

theorem Certificate.usizeLt_returns (room : 3 ≤ limits.locals) (a b : Nat)
    (left : NatValid limits a) (right : NatValid limits b) (continuation : Array Continuation) :
    Reaches limits program (frameState 49 0 #[natural a, natural b] continuation)
      (returned (.scalar (.bool (a < b))) continuation) :=
  (certificate.function 49).binary_returns limits room _ _ _ (eval_natLt limits a b left right) continuation

end Compilatrix.Ixby.Runtime.Native
