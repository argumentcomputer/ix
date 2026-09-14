import Compilatrix.Ixby.Runtime.WordTruncate
import Compilatrix.Ixby.Runtime.WordSimple

/-! Source conversion contracts, including the erased ofNatLT proof slot.
USize truncation explicitly assumes the compiler's fixed 64-bit platform. -/

namespace Compilatrix.Ixby.Runtime.Words.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem u8ToNat_returns (room : 1 ≤ limits.locals) (a : UInt8) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (continuation : Array Continuation) :
    Reaches limits program (frameState links.u8ToNat 0 #[value] continuation)
      (returned value continuation) ∧ Number links.conversions.layout (a.toNat) value := by
  exact ⟨identity_returns certificate.u8ToNat limits room value continuation, represented⟩

theorem u8ToU32_returns (room : 1 ≤ limits.locals) (a : UInt8) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (continuation : Array Continuation) :
    Reaches limits program (frameState links.u8ToU32 0 #[value] continuation)
      (returned value continuation) ∧ Number links.conversions.layout (a.toUInt32.toNat) value := by
  exact ⟨identity_returns certificate.u8ToU32 limits room value continuation,
    by simpa only [UInt8.toNat_toUInt32] using represented⟩

theorem u32ToNat_returns (room : 1 ≤ limits.locals) (a : UInt32) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (continuation : Array Continuation) :
    Reaches limits program (frameState links.u32ToNat 0 #[value] continuation)
      (returned value continuation) ∧ Number links.conversions.layout (a.toNat) value := by
  exact ⟨identity_returns certificate.u32ToNat limits room value continuation, represented⟩

theorem usizeToNat_returns (room : 1 ≤ limits.locals) (a : USize) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (continuation : Array Continuation) :
    Reaches limits program (frameState links.usizeToNat 0 #[value] continuation)
      (returned value continuation) ∧ Number links.conversions.layout (a.toNat) value := by
  exact ⟨identity_returns certificate.usizeToNat limits room value continuation, represented⟩

theorem u8OfNat_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u8OfNat 0 #[value] continuation)
      (returned (cachedValue links.conversions.layout (UInt8.ofNat n).toNat) continuation) := by
  have path := truncate_returns certificate.conversions 8 (Or.inl rfl) value none certificate.u8OfNat
    limits room capacity bytesCapacity n represented valid
    (validate_nat_of_bits (bits := 64) (by decide) capacity) continuation stack
  simpa only [truncateArgs, UInt8.toNat_ofNat'] using path

theorem u32OfNat_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32OfNat 0 #[value] continuation)
      (returned (cachedValue links.conversions.layout (UInt32.ofNat n).toNat) continuation) := by
  have path := truncate_returns certificate.conversions 32 (Or.inr (Or.inl rfl)) value none certificate.u32OfNat
    limits room capacity bytesCapacity n represented valid
    (validate_nat_of_bits (bits := 64) (by decide) capacity) continuation stack
  simpa only [truncateArgs, UInt32.toNat_ofNat'] using path

theorem usizeOfNat_returns (room : 11 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.usizeOfNat 0 #[value] continuation)
      (returned (cachedValue links.conversions.layout (USize.ofNat n).toNat) continuation) := by
  have path := truncate_returns certificate.conversions 64 (Or.inr (Or.inr rfl)) value none certificate.usizeOfNat
    limits room (by omega) bytesCapacity n represented valid
    (validate_nat_of_bits (bits := 65) (by decide) capacity) continuation stack
  simpa only [truncateArgs, USize.toNat_ofNat', platform] using path

theorem u32ToU8_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a : UInt32) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32ToU8 0 #[value] continuation)
      (returned (cachedValue links.conversions.layout a.toUInt8.toNat) continuation) := by
  have path := truncate_returns certificate.conversions 8 (Or.inl rfl) value none certificate.u32ToU8
    limits room capacity bytesCapacity a.toNat represented
    (validate_nat_of_bits a.toNat_lt (by omega))
    (validate_nat_of_bits (bits := 64) (by decide) capacity) continuation stack
  simpa only [truncateArgs, UInt32.toNat_toUInt8] using path

theorem u32OfNatLT_returns (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (n : Nat) (bounded : n < UInt32.size)
    (value proofValue : Value) (represented : Number links.conversions.layout n value)
    (continuation : Array Continuation) (stack : continuation.size + 3 ≤ limits.continuations) :
    Reaches limits program (frameState links.u32OfNatLT 0 #[value, proofValue] continuation)
      (returned (cachedValue links.conversions.layout (UInt32.ofNatLT n bounded).toNat) continuation) := by
  have path := truncate_returns certificate.conversions 32 (Or.inr (Or.inl rfl)) value (some proofValue)
    certificate.u32OfNatLT limits room capacity bytesCapacity n represented
    (validate_nat_of_bits (show n < 2 ^ 32 from bounded) (by omega))
    (validate_nat_of_bits (bits := 64) (by decide) capacity) continuation stack
  simpa only [truncateArgs, UInt32.toNat_ofNatLT, Nat.mod_eq_of_lt bounded] using path


end Compilatrix.Ixby.Runtime.Words.Certificate
