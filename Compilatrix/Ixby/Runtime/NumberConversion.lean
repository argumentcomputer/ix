import Compilatrix.Ixby.Runtime.FieldConversion

/-! Number-layout dispatch through the actual generated functions, composed
with the complete conversion loops. These contracts accept every value in the
representation relation, including exact naturals larger than a word or field. -/

namespace Compilatrix.Ixby.Runtime.Conversion.Certificate

open Ix.Ixby Execution Representation ScalarFunction

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem natural_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (n : Nat) (value : Value)
    (represented : Number links.layout n value) (continuation : Array Continuation)
    (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.natural 0 #[value] continuation)
      (returned (.scalar (.nat n)) continuation) := by
  have localRoom : ∀ k, k ≤ 10 → ¬limits.locals < k := by omega
  cases represented with
  | cached n =>
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.natural.code, Conversion.natural,
        certificate.cached, frameState, returned, Frame.read, Frame.transfer, selectCase,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  | raw n =>
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.natural.code, Conversion.natural,
        certificate.cached, certificate.raw, certificate.cachedRaw, frameState, returned,
        Frame.read, Frame.transfer, selectCase, localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  | field field =>
    have beforeCall : Reaches limits program
        (frameState links.natural 0 #[.ctor links.layout.field #[.scalar (.field field)]] continuation)
        (frameState links.fieldNatural 0 #[.scalar (.field field)] continuation) := by
      apply reaches_of_chunk (fuel := 2) (count := 0)
      iterate 2
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.natural.code, certificate.fieldNatural.code,
          Conversion.natural, Conversion.fieldNatural, certificate.cached, certificate.raw,
          certificate.field, certificate.cachedField, certificate.rawField, frameState,
          Frame.read, Frame.readOperands, Frame.transfer, selectCase, enter,
          localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    exact beforeCall.trans (certificate.fieldNatural_returns limits room capacity bytesCapacity
      field continuation stack)

theorem asField_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (n : Nat) (value : Value) (represented : Number links.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.asField 0 #[value] continuation)
      (returned (.scalar (.field (Goldilocks.reduce n))) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  cases represented with
  | cached n =>
    have beforeCall : Reaches limits program
        (frameState links.asField 0 #[.ctor links.layout.cached
          #[.scalar (.nat n), .scalar (.word32 n.toUInt32)]] continuation)
        (frameState links.fieldFromNatural 0 #[.scalar (.nat n)] continuation) := by
      apply reaches_of_chunk (fuel := 2) (count := 0)
      iterate 2
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.asField.code, certificate.fieldFromNatural.code,
          Conversion.asField, Conversion.fieldFromNatural, certificate.cached, frameState,
          Frame.read, Frame.readOperands, Frame.transfer, selectCase, enter,
          localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    exact beforeCall.trans (certificate.fieldFromNatural_returns limits room capacity n valid continuation stack)
  | raw n =>
    have beforeCall : Reaches limits program
        (frameState links.asField 0 #[.ctor links.layout.raw #[.scalar (.nat n)]] continuation)
        (frameState links.fieldFromNatural 0 #[.scalar (.nat n)] continuation) := by
      apply reaches_of_chunk (fuel := 2) (count := 0)
      iterate 2
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.asField.code, certificate.fieldFromNatural.code,
          Conversion.asField, Conversion.fieldFromNatural, certificate.cached, certificate.raw,
          certificate.cachedRaw, frameState, Frame.read, Frame.readOperands, Frame.transfer,
          selectCase, enter, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    exact beforeCall.trans (certificate.fieldFromNatural_returns limits room capacity n valid continuation stack)
  | field field =>
    have canonical : Goldilocks.reduce field.val = field := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt field.isLt
    rw [canonical]
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.asField.code, Conversion.asField,
        certificate.cached, certificate.raw, certificate.field, certificate.cachedField,
        certificate.rawField, frameState, returned, Frame.read, Frame.transfer, selectCase,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl

theorem lowWord_returns (room : 11 ≤ limits.locals) (capacity : 5 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (n : Nat) (value : Value)
    (represented : Number links.layout n value) (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size < limits.continuations) :
    Reaches limits program (frameState links.lowWord 0 #[value] continuation)
      (returned (.scalar (.word32 n.toUInt32)) continuation) := by
  have localRoom : ∀ k, k ≤ 11 → ¬limits.locals < k := by omega
  cases represented with
  | cached n =>
    apply reaches_of_chunk (fuel := 2) (count := 0)
    iterate 2
      rw [runChunk]
      simp [step, stepEval, Frame.check, certificate.lowWord.code, Conversion.lowWord,
        certificate.cached, frameState, returned, Frame.read, Frame.transfer, selectCase,
        localRoom, bind, Except.bind, pure, Except.pure]
    rfl
  | raw n =>
    have beforeCall : Reaches limits program
        (frameState links.lowWord 0 #[.ctor links.layout.raw #[.scalar (.nat n)]] continuation)
        (frameState links.toWord 0 #[.scalar (.nat n), .scalar (.word32 1), .scalar (.word32 0)]
          continuation) := by
      apply reaches_of_chunk (fuel := 2) (count := 0)
      iterate 2
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.lowWord.code, certificate.toWord.code,
          Conversion.lowWord, Conversion.toWord, certificate.cached, certificate.raw,
          certificate.cachedRaw, frameState, Frame.read, Frame.readOperands, Frame.transfer,
          selectCase, enter, W, localRoom, bind, Except.bind, pure, Except.pure]
      rfl
    exact beforeCall.trans (certificate.toWord_returns limits room capacity n valid continuation stack)
  | field field =>
    have fieldBytes := eval_fieldToBytes limits field bytesCapacity
    have slice := eval_fieldChunk limits field 0 (by decide) bytesCapacity
    have word := eval_fieldWord limits field 0 (by decide) bytesCapacity
    have result : Reaches limits program
        (frameState links.lowWord 0 #[.ctor links.layout.field #[.scalar (.field field)]] continuation)
        (returned (.scalar (.word32 (fieldWord field 0))) continuation) := by
      apply reaches_of_chunk (fuel := 5) (count := 0)
      iterate 5
        rw [runChunk]
        simp [step, stepEval, Frame.check, certificate.lowWord.code, Conversion.lowWord,
          certificate.cached, certificate.raw, certificate.field, certificate.cachedField,
          certificate.rawField, frameState, returned, Frame.read, Frame.readOperands,
          Frame.transfer, selectCase, evalOp, W, localRoom, fieldBytes, slice, word,
          bind, Except.bind, pure, Except.pure]
      rfl
    simpa only [fieldWord_low] using result

theorem fromWord_represents (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (word : UInt32) (continuation : Array Continuation)
    (stack : continuation.size + 2 ≤ limits.continuations) :
    ∃ value, Reaches limits program
        (frameState links.fromWord 0 #[.scalar (.word32 word)] continuation) (returned value continuation) ∧
      Number links.layout word.toNat value := by
  refine ⟨_, certificate.fromWord_returns limits room capacity word continuation stack, ?_⟩
  simpa only [Nat.toUInt32, UInt32.ofNat_toNat] using Number.cached (layout := links.layout) word.toNat

theorem natural_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 2 ≤ limits.continuations)
    (n : Nat) (value : Value) (represented : Number links.layout n value)
    (entry : program.entry = links.natural) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] (.scalar (.nat n)) := by
  apply (certificate.natural_returns limits room capacity bytesCapacity n value represented #[]
    (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.natural.code, Conversion.natural,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem asField_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (stack : 2 ≤ limits.continuations) (n : Nat) (value : Value)
    (represented : Number links.layout n value) (valid : (Scalar.nat n).validate limits = .ok ())
    (entry : program.entry = links.asField) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] (.scalar (.field (Goldilocks.reduce n))) := by
  apply (certificate.asField_returns limits room capacity n value represented valid #[]
    (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.asField.code, Conversion.asField,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem lowWord_evaluates (room : 11 ≤ limits.locals) (capacity : 5 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (stack : 0 < limits.continuations)
    (n : Nat) (value : Value) (represented : Number links.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (entry : program.entry = links.lowWord) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] (.scalar (.word32 n.toUInt32)) := by
  apply (certificate.lowWord_returns limits room capacity bytesCapacity n value represented valid #[]
    (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.lowWord.code, Conversion.lowWord,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem fromWord_evaluates (room : 10 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (stack : 2 ≤ limits.continuations) (word : UInt32)
    (entry : program.entry = links.fromWord) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [.scalar (.word32 word)] = .ok ()) :
    Evaluates limits program #[.scalar (.word32 word)]
      (.ctor links.layout.cached #[.scalar (.nat word.toNat), .scalar (.word32 word)]) := by
  apply (certificate.fromWord_returns limits room capacity word #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.fromWord.code, Conversion.fromWord,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem toWord_evaluates (room : 11 ≤ limits.locals) (capacity : 5 ≤ limits.natBits)
    (stack : 0 < limits.continuations) (n : Nat)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (entry : program.entry = links.toWord) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes
      [.scalar (.nat n), .scalar (.word32 1), .scalar (.word32 0)] = .ok ()) :
    Evaluates limits program #[.scalar (.nat n), .scalar (.word32 1), .scalar (.word32 0)]
      (.scalar (.word32 n.toUInt32)) := by
  apply (certificate.toWord_returns limits room capacity n valid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.toWord.code, Conversion.toWord,
    Frame.check, inputs, frameState, show ¬limits.locals < 3 by omega,
    bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.Conversion.Certificate
