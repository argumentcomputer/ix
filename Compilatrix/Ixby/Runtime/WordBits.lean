import Compilatrix.Ixby.Runtime.WordSimple
import Compilatrix.Ixby.Runtime.WordShiftLaws

/-! Logical and shift source contracts include source count reduction, the
primitive range guard, and the final 8-bit mask. -/

namespace Compilatrix.Ixby.Runtime.Words.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem u32And_returns (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32And 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a &&& b).toNat) continuation) := by
  apply logical_returns certificate.conversions certificate.u32And limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep
    (validate_nat_of_bits a.toNat_lt (by omega)) (validate_nat_of_bits b.toNat_lt (by omega)) (a &&& b)
    ?_ continuation stack
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl

theorem u32Or_returns (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32Or 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a ||| b).toNat) continuation) := by
  apply logical_returns certificate.conversions certificate.u32Or limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep
    (validate_nat_of_bits a.toNat_lt (by omega)) (validate_nat_of_bits b.toNat_lt (by omega)) (a ||| b)
    ?_ continuation stack
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl

theorem u32Xor_returns (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32Xor 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a ^^^ b).toNat) continuation) := by
  apply logical_returns certificate.conversions certificate.u32Xor limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep
    (validate_nat_of_bits a.toNat_lt (by omega)) (validate_nat_of_bits b.toNat_lt (by omega)) (a ^^^ b)
    ?_ continuation stack
  simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl

theorem u8ShiftLeft_returns (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.u8ShiftLeft 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a <<< b).toNat) continuation) := by
  have bounded : b.toUInt32 &&& 7 < (32 : UInt32) := masked_count_lt b.toUInt32 8 (Or.inl rfl)
  have path := shift_returns certificate.conversions 8 (Or.inl rfl) certificate.u8ShiftLeft
    limits room capacity bytesCapacity a.toNat b.toNat left right leftRep rightRep
    (validate_nat_of_bits a.toNat_lt (by omega)) (validate_nat_of_bits b.toNat_lt (by omega))
    (a.toUInt32 <<< (b.toUInt32 &&& 7))
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, bounded] <;> rfl)
    continuation stack
  have result : (if 8 < 32 then (a.toUInt32 <<< (b.toUInt32 &&& 7)) &&& (2 ^ 8 - 1).toUInt32 else (a.toUInt32 <<< (b.toUInt32 &&& 7))).toNat =
      (a <<< b).toNat := u8_shiftLeft_nat a b
  simpa only [result] using path

theorem u8ShiftRight_returns (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.u8ShiftRight 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a >>> b).toNat) continuation) := by
  have bounded : b.toUInt32 &&& 7 < (32 : UInt32) := masked_count_lt b.toUInt32 8 (Or.inl rfl)
  have path := shift_returns certificate.conversions 8 (Or.inl rfl) certificate.u8ShiftRight
    limits room capacity bytesCapacity a.toNat b.toNat left right leftRep rightRep
    (validate_nat_of_bits a.toNat_lt (by omega)) (validate_nat_of_bits b.toNat_lt (by omega))
    (a.toUInt32 >>> (b.toUInt32 &&& 7))
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, bounded] <;> rfl)
    continuation stack
  have result : (if 8 < 32 then (a.toUInt32 >>> (b.toUInt32 &&& 7)) &&& (2 ^ 8 - 1).toUInt32 else (a.toUInt32 >>> (b.toUInt32 &&& 7))).toNat =
      (a >>> b).toNat := u8_shiftRight_nat a b
  simpa only [result] using path

theorem u32ShiftLeft_returns (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32ShiftLeft 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a <<< b).toNat) continuation) := by
  have bounded : b &&& 31 < (32 : UInt32) := masked_count_lt b 32 (Or.inr rfl)
  have path := shift_returns certificate.conversions 32 (Or.inr rfl) certificate.u32ShiftLeft
    limits room capacity bytesCapacity a.toNat b.toNat left right leftRep rightRep
    (validate_nat_of_bits a.toNat_lt (by omega)) (validate_nat_of_bits b.toNat_lt (by omega))
    (a <<< (b &&& 31))
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32, bounded] <;> rfl)
    continuation stack
  have result : (if 32 < 32 then (a <<< (b &&& 31)) &&& (2 ^ 32 - 1).toUInt32 else (a <<< (b &&& 31))).toNat =
      (a <<< b).toNat := u32_shiftLeft_nat a b
  simpa only [result] using path

theorem u32ShiftRight_returns (room : 11 ≤ limits.locals) (capacity : 32 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 2 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32ShiftRight 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a >>> b).toNat) continuation) := by
  have bounded : b &&& 31 < (32 : UInt32) := masked_count_lt b 32 (Or.inr rfl)
  have path := shift_returns certificate.conversions 32 (Or.inr rfl) certificate.u32ShiftRight
    limits room capacity bytesCapacity a.toNat b.toNat left right leftRep rightRep
    (validate_nat_of_bits a.toNat_lt (by omega)) (validate_nat_of_bits b.toNat_lt (by omega))
    (a >>> (b &&& 31))
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32, bounded] <;> rfl)
    continuation stack
  have result : (if 32 < 32 then (a >>> (b &&& 31)) &&& (2 ^ 32 - 1).toUInt32 else (a >>> (b &&& 31))).toNat =
      (a >>> b).toNat := u32_shiftRight_nat a b
  simpa only [result] using path


end Compilatrix.Ixby.Runtime.Words.Certificate
