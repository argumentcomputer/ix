import Compilatrix.Ixby.Runtime.WordModular

/-! Source modular arithmetic. Bounds for the unreduced sum/product are
derived from source word widths; USize arithmetic needs 65 Nat bits. -/

namespace Compilatrix.Ixby.Runtime.Words.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem u8Add_returns (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u8Add 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a + b).toNat) continuation) := by
  have leftBound := a.toNat_lt
  have rightBound := b.toNat_lt
  have leftValid := validate_nat_of_bits leftBound (show 8 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits rightBound (show 8 ≤ limits.natBits by omega)
  have modulusValid := validate_nat_of_bits (n := 2 ^ 8) (bits := 64) (by decide) capacity
  have resultValid := validate_nat_of_bits (n := a.toNat + b.toNat) (bits := 64) (by omega) capacity
  have path := modular_returns certificate.conversions 8 (Or.inl rfl) certificate.u8Add
    limits room capacity bytesCapacity a.toNat b.toNat (a.toNat + b.toNat) left right
    leftRep rightRep leftValid rightValid resultValid modulusValid
    (eval_natAdd limits a.toNat b.toNat leftValid rightValid resultValid)
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl) continuation stack
  simpa only [UInt8.toNat_add] using path

theorem u32Add_returns (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32Add 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a + b).toNat) continuation) := by
  have leftBound := a.toNat_lt
  have rightBound := b.toNat_lt
  have leftValid := validate_nat_of_bits leftBound (show 32 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits rightBound (show 32 ≤ limits.natBits by omega)
  have modulusValid := validate_nat_of_bits (n := 2 ^ 32) (bits := 64) (by decide) capacity
  have resultValid := validate_nat_of_bits (n := a.toNat + b.toNat) (bits := 64) (by omega) capacity
  have path := modular_returns certificate.conversions 32 (Or.inr (Or.inl rfl)) certificate.u32Add
    limits room capacity bytesCapacity a.toNat b.toNat (a.toNat + b.toNat) left right
    leftRep rightRep leftValid rightValid resultValid modulusValid
    (eval_natAdd limits a.toNat b.toNat leftValid rightValid resultValid)
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl) continuation stack
  simpa only [UInt32.toNat_add] using path

theorem u32Mul_returns (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32Mul 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a * b).toNat) continuation) := by
  have leftBound := a.toNat_lt
  have rightBound := b.toNat_lt
  have leftValid := validate_nat_of_bits leftBound (show 32 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits rightBound (show 32 ≤ limits.natBits by omega)
  have modulusValid := validate_nat_of_bits (n := 2 ^ 32) (bits := 64) (by decide) capacity
  have productBound := Nat.mul_le_mul (show a.toNat ≤ 4294967295 by omega)
    (show b.toNat ≤ 4294967295 by omega)
  have resultValid := validate_nat_of_bits (n := a.toNat * b.toNat) (bits := 64)
    (Nat.lt_of_le_of_lt productBound (by decide)) capacity
  have path := modular_returns certificate.conversions 32 (Or.inr (Or.inl rfl)) certificate.u32Mul
    limits room capacity bytesCapacity a.toNat b.toNat (a.toNat * b.toNat) left right
    leftRep rightRep leftValid rightValid resultValid modulusValid
    (eval_natMul limits a.toNat b.toNat leftValid rightValid resultValid)
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl) continuation stack
  simpa only [UInt32.toNat_mul] using path

theorem usizeAdd_returns (room : 14 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64)
    (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.usizeAdd 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a + b).toNat) continuation) := by
  have leftBound := a.toNat_lt
  have rightBound := b.toNat_lt
  have leftValid := validate_nat_of_bits leftBound (show 64 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits rightBound (show 64 ≤ limits.natBits by omega)
  have modulusValid := validate_nat_of_bits (n := 2 ^ 64) (bits := 65) (by decide) capacity
  have resultValid := validate_nat_of_bits (n := a.toNat + b.toNat) (bits := 65) (by omega) capacity
  have path := modular_returns certificate.conversions 64 (Or.inr (Or.inr rfl)) certificate.usizeAdd
    limits room (by omega) bytesCapacity a.toNat b.toNat (a.toNat + b.toNat) left right
    leftRep rightRep leftValid rightValid resultValid modulusValid
    (eval_natAdd limits a.toNat b.toNat leftValid rightValid resultValid)
    (by simp [Primitive.eval, Primitive.evalScalarUnchecked, Primitive.arity, Nat.toUInt32] <;> rfl) continuation stack
  simpa only [USize.toNat_add, platform] using path

theorem u32Sub_returns (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32Sub 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a - b).toNat) continuation) := by
  have leftBound := a.toNat_lt
  have rightBound := b.toNat_lt
  have leftValid := validate_nat_of_bits leftBound (show 32 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits rightBound (show 32 ≤ limits.natBits by omega)
  have modulusValid := validate_nat_of_bits (n := 2 ^ 32) (bits := 64) (by decide) capacity
  have sumValid := validate_nat_of_bits (n := a.toNat + 2 ^ 32) (bits := 64) (by omega) capacity
  have path := subtract_returns certificate.conversions 32 (Or.inl rfl) certificate.u32Sub
    limits room capacity bytesCapacity a.toNat b.toNat left right leftRep rightRep
    leftValid rightValid rightBound sumValid modulusValid continuation stack
  have result : (a.toNat + 2 ^ 32 - b.toNat) % 2 ^ 32 = (a - b).toNat := by
    rw [UInt32.toNat_sub]
    congr 1
    omega
  rw [result] at path
  exact path

theorem usizeSub_returns (room : 14 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64)
    (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.usizeSub 0 #[left, right] continuation)
      (returned (cachedValue links.conversions.layout (a - b).toNat) continuation) := by
  have leftBound := a.toNat_lt
  have rightBound := b.toNat_lt
  have leftValid := validate_nat_of_bits leftBound (show 64 ≤ limits.natBits by omega)
  have rightValid := validate_nat_of_bits rightBound (show 64 ≤ limits.natBits by omega)
  have modulusValid := validate_nat_of_bits (n := 2 ^ 64) (bits := 65) (by decide) capacity
  have sumValid := validate_nat_of_bits (n := a.toNat + 2 ^ 64) (bits := 65) (by omega) capacity
  have path := subtract_returns certificate.conversions 64 (Or.inr rfl) certificate.usizeSub
    limits room (by omega) bytesCapacity a.toNat b.toNat left right leftRep rightRep
    leftValid rightValid rightBound sumValid modulusValid continuation stack
  have result : (a.toNat + 2 ^ 64 - b.toNat) % 2 ^ 64 = (a - b).toNat := by
    rw [USize.toNat_sub, platform]
    congr 1
    omega
  rw [result] at path
  exact path


end Compilatrix.Ixby.Runtime.Words.Certificate
