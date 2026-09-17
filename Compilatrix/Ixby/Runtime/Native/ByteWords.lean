import Compilatrix.Ixby.Runtime.Native.BytesBasic

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby

theorem bytesLE_size (width n : Nat) : (bytesLE width n).size = width := by simp [bytesLE]

theorem bytesLE_first_byte (byte : UInt8) : (bytesLE 4 byte.toNat).extract 0 1 = #[byte] := by
  apply Array.ext
  · simp [bytesLE]
  · intro i _ small
    have zero : i = 0 := by simpa using small
    subst i
    simp [bytesLE, Nat.toUInt8]

theorem eval_word32ToBytes (limits : Limits) (w : UInt32) (capacity : 4 ≤ limits.byteArrayBytes) :
    Primitive.word32ToBytes.eval limits [word w] = .ok (.scalar (.bytes (bytesLE 4 w.toNat))) := by
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Scalar.validate,
    word, bytesLE_size, Nat.not_lt.mpr capacity, bind, Except.bind, pure, Except.pure]

theorem eval_bytesLength (limits : Limits) (bytes : Array UInt8)
    (capacity : bytes.size ≤ limits.byteArrayBytes) (bound : bytes.size < 2 ^ 32) :
    Primitive.bytesLength.eval limits [.scalar (.bytes bytes)] = .ok (word bytes.size.toUInt32) := by
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Scalar.validate,
    word, Nat.not_lt.mpr capacity, bound, bind, Except.bind, pure, Except.pure]

theorem eval_byteSlice (limits : Limits) (byte : UInt8) (capacity : 4 ≤ limits.byteArrayBytes) :
    Primitive.bytesSlice.eval limits [.scalar (.bytes (bytesLE 4 byte.toNat)), word 0, word 1] =
      .ok (.scalar (.bytes #[byte])) := by
  simpa only [show (0 : UInt32).toNat = 0 from rfl, show (1 : UInt32).toNat = 1 from rfl,
    Nat.zero_add, bytesLE_first_byte] using
    eval_bytesSlice limits (bytesLE 4 byte.toNat) 0 1
      (by simpa only [bytesLE_size] using capacity) (by simp [bytesLE_size])

end Compilatrix.Ixby.Runtime.Native
