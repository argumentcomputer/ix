import Compilatrix.Ixby.Runtime.ArrayTreeCall

/-! Tree-backed size, empty-array construction, and the explicit 64-bit
USize observation. Ignored type, capacity, and proof slots stay arbitrary. -/

namespace Compilatrix.Ixby.Runtime.ArrayTrees.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion
open Words (cachedValue)

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem size_returns (room : 5 ≤ limits.locals) (typeValue : Value)
    (height : Nat) (tree : Tree height) (size : Value) (continuation : Array Continuation) :
    Reaches limits program
      (frameState links.size 0 #[typeValue, arrayValue links.layout height tree size] continuation)
      (returned size continuation) := by
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 2) (count := 0)
  iterate 2
    rw [runChunk]
    simp [step, stepEval, Frame.check, certificate.size.code, ArrayTrees.size,
      certificate.bytesCtor, certificate.arrayCtor, certificate.bytesArray,
      frameState, returned, arrayValue, Frame.read, Frame.transfer,
      selectCase, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem empty_returns {id : FunctionId} (checked : Checked program id (ArrayTrees.empty links))
    (room : 5 ≤ limits.locals) (typeValue capacityValue : Value) (continuation : Array Continuation) :
    Reaches limits program (frameState id 0 #[typeValue, capacityValue] continuation)
      (returned (arrayValue links.layout 0 (.empty 0)
        (cachedValue links.arithmetic.conversions.layout 0)) continuation) := by
  have localRoom : ∀ k, k ≤ 5 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 4) (count := 0)
  iterate 4
    rw [runChunk]
    simp [step, stepEval, Frame.check, checked.code, ArrayTrees.empty,
      certificate.arithmetic.conversions.cached, certificate.emptyCtor, certificate.arrayCtor,
      frameState, returned, arrayValue, cachedValue, Tree.encode, Frame.read, Frame.readOperands,
      Frame.transfer, evalOp, N, W, localRoom, bind, Except.bind, pure, Except.pure]
  rfl

theorem call_size (room : 5 ≤ limits.locals) (frame : Frame) (operand : Operand) (target : BlockId)
    (height : Nat) (tree : Tree height) (size : Value) (resumed : Frame)
    (code : frame.check limits program =
      .ok ⟨frame.locals.size, .letOp (.call links.size [.erased, operand]) target⟩)
    (read : frame.read operand = .ok (arrayValue links.layout height tree size))
    (transfer : frame.transfer limits program target #[size] = .ok resumed)
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program { control := .eval frame, continuation }
      { control := .eval resumed, continuation } := by
  apply ArrayTrees.call_returns limits program frame links.size [.erased, operand]
    #[.erased, arrayValue links.layout height tree size] target size resumed continuation stack code
  · have erasedRead : frame.read .erased = .ok .erased := rfl
    simp [Frame.readOperands, erasedRead, read, bind, Except.bind, pure, Except.pure]
  · simp [enter, Frame.check, certificate.size.code, ArrayTrees.size,
      show ¬limits.locals < 2 by omega, bind, Except.bind, pure, Except.pure]
  · exact transfer
  · exact certificate.size_returns limits room .erased height tree size _

theorem usize_returns (room : 11 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64)
    (typeValue : Value) (height : Nat) (tree : Tree height) (size : Value) (n : Nat)
    (represented : Number links.arithmetic.conversions.layout n size)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program
      (frameState links.usize 0 #[typeValue, arrayValue links.layout height tree size] continuation)
      (returned (cachedValue links.arithmetic.conversions.layout (USize.ofNat n).toNat) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  have observed := certificate.call_size limits (by omega)
    { function := links.usize, block := 0, locals := #[typeValue, arrayValue links.layout height tree size] }
    (.local 1) 1 height tree size
    { function := links.usize, block := 1, locals := #[typeValue, arrayValue links.layout height tree size, size] }
    (by simp [Frame.check, certificate.usize.code, ArrayTrees.usize, localRoom,
      bind, Except.bind, pure, Except.pure]) rfl
    (by simp [Frame.transfer, Frame.check, certificate.usize.code, ArrayTrees.usize, localRoom,
      bind, Except.bind, pure, Except.pure]) continuation (by omega)
  have entered : Reaches limits program
      (frameState links.usize 1 #[typeValue, arrayValue links.layout height tree size, size] continuation)
      (frameState links.usizeOfNat 0 #[size] continuation) := by
    apply Reaches.of_step
    simp [step, stepEval, Frame.check, certificate.usize.code, ArrayTrees.usize,
      certificate.usizeOfNat.code, Words.truncate, frameState, Frame.read, Frame.readOperands,
      enter, localRoom, bind, Except.bind, pure, Except.pure]
  have truncated := Words.truncate_returns certificate.arithmetic.conversions 64 (Or.inr (Or.inr rfl))
    size none certificate.usizeOfNat limits room (by omega) bytesCapacity n represented valid
    (validate_nat_of_bits (bits := 65) (by decide) capacity) continuation stack
  exact observed.trans (entered.trans (by simpa only [Words.truncateArgs, USize.toNat_ofNat', platform] using truncated))

end Compilatrix.Ixby.Runtime.ArrayTrees.Certificate
