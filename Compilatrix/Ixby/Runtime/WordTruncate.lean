import Compilatrix.Ixby.Runtime.WordCertificate
import Compilatrix.Ixby.Runtime.WordCall
import Compilatrix.Ixby.Runtime.WordLaws

/-! Truncation observes both components before computing the canonical result.
The optional second argument is the erased proof slot of UInt32.ofNatLT. -/

namespace Compilatrix.Ixby.Runtime.Words

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def truncateArgs (value : Value) : Option Value → Array Value
  | none => #[value]
  | some proofValue => #[value, proofValue]

theorem truncate_returns {program : Program} {links : Conversion.Links}
    (conversions : Conversion.Certificate program links) {id : FunctionId}
    (bits : Nat) (width : bits = 8 ∨ bits = 32 ∨ bits = 64) (value : Value) (erased : Option Value)
    (checked : Checked program id
      (truncate links.natural links.lowWord links.cachedCtor (truncateArgs value erased).size bits))
    (limits : Limits) (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (n : Nat)
    (represented : Number links.layout n value) (valid : (Scalar.nat n).validate limits = .ok ())
    (modulusValid : (Scalar.nat (2 ^ bits)).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState id 0 (truncateArgs value erased) continuation)
      (returned (cachedValue links.layout (n % 2 ^ bits)) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have reduced := eval_natMod limits n (2 ^ bits) valid modulusValid
    (validate_nat_mono (Nat.mod_le n (2 ^ bits)) valid)
  have masked : Primitive.word32And.eval limits
      [.scalar (.word32 n.toUInt32), .scalar (.word32 255)] =
      .ok (.scalar (.word32 (n % 256).toUInt32)) := by
    simp [Primitive.eval, Primitive.arity, lowWord_mask8] <;> rfl
  have cache32 := (lowWord_mod n 32 (by decide)).symm
  have cache64 := (lowWord_mod n 64 (by decide)).symm
  simp only [Nat.toUInt32, Nat.reducePow] at cache32 cache64
  cases erased <;> rcases width with rfl | rfl | rfl
  all_goals
    have observed := conversions.read_parts checked 0 _ (.local 0) rfl rfl _ rfl limits room
      (by simp [truncateArgs]; omega) capacity bytesCapacity n value represented valid rfl rfl
      continuation stack
    apply observed.trans
    first
    | (apply reaches_of_chunk (fuel := 4) (count := 0)
       iterate 4
         rw [runChunk]
         simp [step, stepEval, Frame.check, checked.code, truncate, truncateArgs,
           conversions.cached, frameState, returned, cachedValue, Frame.read, Frame.readOperands,
           Frame.transfer, evalOp, N, W, reduced, masked,
           localRoom, bind, Except.bind, pure, Except.pure]
       rfl)
    | (apply reaches_of_chunk (fuel := 3) (count := 0)
       iterate 3
         rw [runChunk]
         simp [step, stepEval, Frame.check, checked.code, truncate, truncateArgs,
           conversions.cached, frameState, returned, cachedValue, Frame.read, Frame.readOperands,
           Frame.transfer, evalOp, N, reduced,
           localRoom, bind, Except.bind, pure, Except.pure]
       simp only [cache32, cache64]
       rfl)

end Compilatrix.Ixby.Runtime.Words
