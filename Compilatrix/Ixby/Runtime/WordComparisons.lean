import Compilatrix.Ixby.Runtime.WordSimple

/-! Comparisons use the exact source values in every admitted number layout. -/

namespace Compilatrix.Ixby.Runtime.Words.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem u8Equal_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u8Equal 0 #[left, right] continuation)
      (returned (.scalar (.bool (decide (a = b)))) continuation) := by
  have leftValid := validate_nat_of_bits a.toNat_lt (show 8 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits b.toNat_lt (show 8 ≤ limits.natBits by omega)
  apply compare_returns certificate.conversions certificate.u8Equal limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep _ ?_ continuation stack
  have equal : (a.toNat == b.toNat) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp [UInt8.toNat_inj]
  simpa only [equal] using eval_natEq limits a.toNat b.toNat leftValid rightValid

theorem u32Equal_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32Equal 0 #[left, right] continuation)
      (returned (.scalar (.bool (decide (a = b)))) continuation) := by
  have leftValid := validate_nat_of_bits a.toNat_lt (show 32 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits b.toNat_lt (show 32 ≤ limits.natBits by omega)
  apply compare_returns certificate.conversions certificate.u32Equal limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep _ ?_ continuation stack
  have equal : (a.toNat == b.toNat) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp [UInt32.toNat_inj]
  simpa only [equal] using eval_natEq limits a.toNat b.toNat leftValid rightValid

theorem u32Less_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32Less 0 #[left, right] continuation)
      (returned (.scalar (.bool (decide (a < b)))) continuation) := by
  have leftValid := validate_nat_of_bits a.toNat_lt (show 32 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits b.toNat_lt (show 32 ≤ limits.natBits by omega)
  apply compare_returns certificate.conversions certificate.u32Less limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep _ ?_ continuation stack
  simp [Primitive.eval, Primitive.arity, leftValid, rightValid, UInt32.lt_iff_toNat_lt] <;> rfl

theorem usizeEqual_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.usizeEqual 0 #[left, right] continuation)
      (returned (.scalar (.bool (decide (a = b)))) continuation) := by
  have leftValid := validate_nat_of_bits a.toNat_lt (show 64 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits b.toNat_lt (show 64 ≤ limits.natBits by omega)
  apply compare_returns certificate.conversions certificate.usizeEqual limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep _ ?_ continuation stack
  have equal : (a.toNat == b.toNat) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp [USize.toNat_inj]
  simpa only [equal] using eval_natEq limits a.toNat b.toNat leftValid rightValid

theorem usizeLess_returns (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.usizeLess 0 #[left, right] continuation)
      (returned (.scalar (.bool (decide (a < b)))) continuation) := by
  have leftValid := validate_nat_of_bits a.toNat_lt (show 64 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits b.toNat_lt (show 64 ≤ limits.natBits by omega)
  apply compare_returns certificate.conversions certificate.usizeLess limits room capacity bytesCapacity
    a.toNat b.toNat left right leftRep rightRep _ ?_ continuation stack
  simp [Primitive.eval, Primitive.arity, leftValid, rightValid, USize.lt_iff_toNat_lt] <;> rfl


end Compilatrix.Ixby.Runtime.Words.Certificate
