import Compilatrix.Ixby.Runtime.Native.WireValues
import Compilatrix.Ixby.Runtime.Native.NatLoops
import Compilatrix.Ixby.Runtime.Native.Sequence

/-! Fixed-width integer writes compare against precomputed bounds for the
widths the Stage2 codecs use, and still compute `2 ^ (8 * width)` for every
other width. The range helper then encodes through the existing little-endian
body or rejects with the source's integer-range error, in the source order. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby Execution Representation ScalarFunction Conversion

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def integerRangeError : Value := errorValue (.ctor ⟨1, 0, 12⟩ #[])

/-- The frame saved while the range helper calls the little-endian encoder. -/
def rangeSaved (width n limit : Nat) (state : Value) : Frame :=
  { function := 110, block := 4,
    locals := #[natural width, natural n, state, natural limit, .scalar (.bool true)] }

/-- Each precomputed bound is exactly the source's power of two. -/
theorem fixed_width_bounds :
    2 ^ (8 * 1) = 256 ∧ 2 ^ (8 * 2) = 65536 ∧ 2 ^ (8 * 4) = 4294967296 ∧
      2 ^ (8 * 8) = 18446744073709551616 := by decide

variable {program : Program} (certificate : WireCertificate program) (limits : Limits)

include certificate

/-- A value at or above the bound returns the source error without encoding. -/
theorem WireCertificate.wireNatRange_rejects (room : 7 ≤ limits.locals) (width n limit : Nat)
    (state : Value) (nValid : NatValid limits n) (limitValid : NatValid limits limit)
    (outside : limit ≤ n) (continuation : Array Continuation) :
    Reaches limits program
      (frameState 110 0 #[natural width, natural n, state, natural limit] continuation)
      (returned integerRangeError continuation) := by
  have code := (certificate.function 12).code
  change program.getFunction 110 = .ok Code.Ixby_Runtime_wireNatRange at code
  have compare := eval_natLt limits n limit nValid limitValid
  have localRoom : ∀ k, k ≤ 7 → ¬limits.locals < k := by omega
  apply reaches_of_chunk (fuel := 5) (count := 0)
  iterate 5
    rw [runChunk]
    simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_wireNatRange, frameState, returned,
      natural, integerRangeError, errorValue, certificate.integerRangeCtor, certificate.errorCtor,
      Frame.read, Frame.readOperands, Frame.transfer, evalOp, compare, Nat.not_lt.mpr outside,
      localRoom, bind, Except.bind, pure, Except.pure]
  rfl

/-- A value below the bound is encoded by the existing little-endian body and
handed to the byte writer, whose own contracts continue from its entry. -/
theorem WireCertificate.wireNatRange_encodes (room : 7 ≤ limits.locals) (width n limit : Nat)
    (state encoded : Value) (nValid : NatValid limits n) (limitValid : NatValid limits limit)
    (inside : n < limit) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations)
    (encoding : Reaches limits program
      (frameState 102 0 #[natural width, natural n]
        (continuation.push (.resume (rangeSaved width n limit state))))
      (returned encoded (continuation.push (.resume (rangeSaved width n limit state))))) :
    Reaches limits program
      (frameState 110 0 #[natural width, natural n, state, natural limit] continuation)
      (frameState 101 0 #[encoded, state] continuation) := by
  have code := (certificate.function 12).code
  have encoder := (certificate.function 4).code
  have writer := (certificate.function 3).code
  change program.getFunction 110 = .ok Code.Ixby_Runtime_wireNatRange at code
  change program.getFunction 102 = .ok Code.MultiStark_Verify_Codec_Wire_littleEndian at encoder
  change program.getFunction 101 = .ok Code.MultiStark_Verify_Codec_Wire_writeBytes at writer
  have compare := eval_natLt limits n limit nValid limitValid
  have localRoom : ∀ k, k ≤ 7 → ¬limits.locals < k := by omega
  let checked : Array Value := #[natural width, natural n, state, natural limit, .scalar (.bool true)]
  have beforeCall : Reaches limits program
      (frameState 110 0 #[natural width, natural n, state, natural limit] continuation)
      (frameState 110 2 checked continuation) := by
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.Ixby_Runtime_wireNatRange, frameState, checked,
        natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp, compare, inside, localRoom,
        bind, Except.bind, pure, Except.pure]
    rfl
  have encodePath := call_returns limits program { function := 110, block := 2, locals := checked }
    102 [.local 0, .local 1] #[natural width, natural n] 4 encoded
    { function := 110, block := 4, locals := checked.push encoded } continuation stack
    (by simp [Frame.check, code, Code.Ixby_Runtime_wireNatRange, checked, localRoom,
      bind, Except.bind, pure, Except.pure])
    rfl
    (by simp [enter, Frame.check, encoder, Code.MultiStark_Verify_Codec_Wire_littleEndian, localRoom,
      bind, Except.bind, pure, Except.pure])
    (by simp [Frame.transfer, Frame.check, code, Code.Ixby_Runtime_wireNatRange, checked, localRoom,
      bind, Except.bind, pure, Except.pure])
    encoding
  apply beforeCall.trans (encodePath.trans ?_)
  apply Reaches.of_step
  simp [step, stepEval, Frame.check, code, writer, Code.Ixby_Runtime_wireNatRange,
    Code.MultiStark_Verify_Codec_Wire_writeBytes, frameState, checked, Frame.read, Frame.readOperands,
    enter, localRoom, bind, Except.bind, pure, Except.pure]

/-- The four codec widths reach the range helper with their precomputed bound. -/
theorem WireCertificate.writeNat_fixed_reaches_range (room : 7 ≤ limits.locals)
    (capacity : 4 ≤ limits.natBits) (width n : Nat) (state : Value)
    (fixed : width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8) (widthValid : NatValid limits width)
    (continuation : Array Continuation) :
    Reaches limits program (frameState 111 0 #[natural width, natural n, state] continuation)
      (frameState 110 0 #[natural width, natural n, state, natural (2 ^ (8 * width))] continuation) := by
  have code := (certificate.function 13).code
  have range := (certificate.function 12).code
  change program.getFunction 111 = .ok Code.MultiStark_Verify_Codec_Wire_writeNat at code
  change program.getFunction 110 = .ok Code.Ixby_Runtime_wireNatRange at range
  have localRoom : ∀ k, k ≤ 7 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 8) : NatValid limits k :=
    validate_nat_of_bits (by omega : k < 2 ^ 4) capacity
  have one := eval_natEq limits width 1 widthValid (smallNat 1 (by omega))
  have two := eval_natEq limits width 2 widthValid (smallNat 2 (by omega))
  have four := eval_natEq limits width 4 widthValid (smallNat 4 (by omega))
  have eight := eval_natEq limits width 8 widthValid (smallNat 8 (by omega))
  obtain ⟨b1, b2, b4, b8⟩ := fixed_width_bounds
  rcases fixed with rfl | rfl | rfl | rfl
  · rw [b1]
    apply reaches_of_chunk (fuel := 7) (count := 0)
    iterate 7
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, range, Code.MultiStark_Verify_Codec_Wire_writeNat,
        Code.Ixby_Runtime_wireNatRange, frameState, natural, Frame.read, Frame.readOperands,
        Frame.transfer, enter, evalOp, one, two, eight, localRoom,
        bind, Except.bind, pure, Except.pure]
    rfl
  · rw [b2]
    apply reaches_of_chunk (fuel := 3) (count := 0)
    iterate 3
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, range, Code.MultiStark_Verify_Codec_Wire_writeNat,
        Code.Ixby_Runtime_wireNatRange, frameState, natural, Frame.read, Frame.readOperands,
        Frame.transfer, enter, evalOp, two, localRoom,
        bind, Except.bind, pure, Except.pure]
    rfl
  · rw [b4]
    apply reaches_of_chunk (fuel := 9) (count := 0)
    iterate 9
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, range, Code.MultiStark_Verify_Codec_Wire_writeNat,
        Code.Ixby_Runtime_wireNatRange, frameState, natural, Frame.read, Frame.readOperands,
        Frame.transfer, enter, evalOp, one, two, four, eight, localRoom,
        bind, Except.bind, pure, Except.pure]
    rfl
  · rw [b8]
    apply reaches_of_chunk (fuel := 5) (count := 0)
    iterate 5
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, range, Code.MultiStark_Verify_Codec_Wire_writeNat,
        Code.Ixby_Runtime_wireNatRange, frameState, natural, Frame.read, Frame.readOperands,
        Frame.transfer, enter, evalOp, two, eight, localRoom,
        bind, Except.bind, pure, Except.pure]
    rfl

/-- Every other width computes the source bound with the certified power loop. -/
theorem WireCertificate.writeNat_general_reaches_range (room : 10 ≤ limits.locals)
    (capacity : 4 ≤ limits.natBits) (width n : Nat) (state : Value)
    (other : width ≠ 1 ∧ width ≠ 2 ∧ width ≠ 4 ∧ width ≠ 8) (widthValid : NatValid limits width)
    (bitsValid : NatValid limits (8 * width)) (powerValid : NatValid limits (2 ^ (8 * width)))
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 111 0 #[natural width, natural n, state] continuation)
      (frameState 110 0 #[natural width, natural n, state, natural (2 ^ (8 * width))] continuation) := by
  have code := (certificate.function 13).code
  have range := (certificate.function 12).code
  have power := (certificate.runtime.function 20).code
  change program.getFunction 111 = .ok Code.MultiStark_Verify_Codec_Wire_writeNat at code
  change program.getFunction 110 = .ok Code.Ixby_Runtime_wireNatRange at range
  change program.getFunction 20 = .ok Code.Nat_pow at power
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  have smallNat (k : Nat) (small : k ≤ 8) : NatValid limits k :=
    validate_nat_of_bits (by omega : k < 2 ^ 4) capacity
  obtain ⟨notOne, notTwo, notFour, notEight⟩ := other
  have one := eval_natEq limits width 1 widthValid (smallNat 1 (by omega))
  have two := eval_natEq limits width 2 widthValid (smallNat 2 (by omega))
  have four := eval_natEq limits width 4 widthValid (smallNat 4 (by omega))
  have eight := eval_natEq limits width 8 widthValid (smallNat 8 (by omega))
  have bits := eval_natMul limits 8 width (smallNat 8 (by omega)) widthValid bitsValid
  simp only [beq_eq_false_iff_ne.mpr notOne, beq_eq_false_iff_ne.mpr notTwo,
    beq_eq_false_iff_ne.mpr notFour, beq_eq_false_iff_ne.mpr notEight] at one two four eight
  let scanned : Array Value := #[natural width, natural n, state, .scalar (.bool false),
    .scalar (.bool false), .scalar (.bool false), .scalar (.bool false), natural (8 * width)]
  have beforePower : Reaches limits program
      (frameState 111 0 #[natural width, natural n, state] continuation)
      (frameState 111 13 scanned continuation) := by
    apply reaches_of_chunk (fuel := 9) (count := 0)
    iterate 9
      rw [runChunk]
      simp [step, stepEval, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_writeNat, frameState,
        scanned, natural, Frame.read, Frame.readOperands, Frame.transfer, evalOp, one, two, four,
        eight, bits, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  have powerPath := call_returns limits program { function := 111, block := 13, locals := scanned }
    20 [.literal (.nat 2), .local 7] #[natural 2, natural (8 * width)] 14 (natural (2 ^ (8 * width)))
    { function := 111, block := 14, locals := scanned.push (natural (2 ^ (8 * width))) } continuation stack
    (by simp [Frame.check, code, Code.MultiStark_Verify_Codec_Wire_writeNat, scanned, localRoom,
      bind, Except.bind, pure, Except.pure])
    rfl
    (by simp [enter, Frame.check, power, Code.Nat_pow, localRoom, bind, Except.bind, pure, Except.pure])
    (by simp [Frame.transfer, Frame.check, code, Code.MultiStark_Verify_Codec_Wire_writeNat, scanned,
      localRoom, bind, Except.bind, pure, Except.pure])
    (certificate.runtime.natPow_returns limits room (by omega) 2 (8 * width) (smallNat 2 (by omega))
      bitsValid powerValid _)
  apply beforePower.trans (powerPath.trans ?_)
  apply Reaches.of_step
  simp [step, stepEval, Frame.check, code, range, Code.MultiStark_Verify_Codec_Wire_writeNat,
    Code.Ixby_Runtime_wireNatRange, frameState, scanned, natural, Frame.read, Frame.readOperands,
    enter, localRoom, bind, Except.bind, pure, Except.pure]

theorem WireCertificate.writeNat_reaches_range (room : 10 ≤ limits.locals)
    (capacity : 4 ≤ limits.natBits) (width n : Nat) (state : Value) (widthValid : NatValid limits width)
    (bitsValid : NatValid limits (8 * width)) (powerValid : NatValid limits (2 ^ (8 * width)))
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 111 0 #[natural width, natural n, state] continuation)
      (frameState 110 0 #[natural width, natural n, state, natural (2 ^ (8 * width))] continuation) := by
  by_cases fixed : width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8
  · exact certificate.writeNat_fixed_reaches_range limits (by omega) capacity width n state fixed
      widthValid continuation
  · exact certificate.writeNat_general_reaches_range limits room capacity width n state
      (by omega) widthValid bitsValid powerValid continuation stack

/-- Complete source semantics of a successful write: the range check passes and
the encoded bytes reach the byte writer's entry with the original state. -/
theorem WireCertificate.writeNat_encodes (room : 10 ≤ limits.locals) (capacity : 4 ≤ limits.natBits)
    (width n : Nat) (state encoded : Value) (widthValid : NatValid limits width)
    (nValid : NatValid limits n) (bitsValid : NatValid limits (8 * width))
    (powerValid : NatValid limits (2 ^ (8 * width))) (inside : n < 2 ^ (8 * width))
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations)
    (encoding : Reaches limits program
      (frameState 102 0 #[natural width, natural n]
        (continuation.push (.resume (rangeSaved width n (2 ^ (8 * width)) state))))
      (returned encoded (continuation.push (.resume (rangeSaved width n (2 ^ (8 * width)) state))))) :
    Reaches limits program (frameState 111 0 #[natural width, natural n, state] continuation)
      (frameState 101 0 #[encoded, state] continuation) :=
  (certificate.writeNat_reaches_range limits room capacity width n state widthValid bitsValid
    powerValid continuation stack).trans
    (certificate.wireNatRange_encodes limits (by omega) width n _ state encoded nValid powerValid
      inside continuation stack encoding)

/-- Complete source semantics of a rejected write. -/
theorem WireCertificate.writeNat_rejects (room : 10 ≤ limits.locals) (capacity : 4 ≤ limits.natBits)
    (width n : Nat) (state : Value) (widthValid : NatValid limits width) (nValid : NatValid limits n)
    (bitsValid : NatValid limits (8 * width)) (powerValid : NatValid limits (2 ^ (8 * width)))
    (outside : 2 ^ (8 * width) ≤ n) (continuation : Array Continuation)
    (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState 111 0 #[natural width, natural n, state] continuation)
      (returned integerRangeError continuation) :=
  (certificate.writeNat_reaches_range limits room capacity width n state widthValid bitsValid
    powerValid continuation stack).trans
    (certificate.wireNatRange_rejects limits (by omega) width n _ state nValid powerValid outside
      continuation)

end Compilatrix.Ixby.Runtime.Native
