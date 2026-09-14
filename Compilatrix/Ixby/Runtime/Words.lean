import Compilatrix.Ixby.Runtime.WordConversions
import Compilatrix.Ixby.Runtime.WordComparisons
import Compilatrix.Ixby.Runtime.WordArithmetic
import Compilatrix.Ixby.Runtime.WordBits

/-! Whole-program source contracts for all twenty-seven UInt8, UInt32, and
USize helpers. Ordinary program and input admission remains required. The
local contracts additionally preserve arbitrary callers. -/

namespace Compilatrix.Ixby.Runtime.Words.Certificate

open Ix.Ixby Execution Representation ScalarFunction Conversion

variable {program : Program} {links : Links} (certificate : Certificate program links)
  (limits : Limits)

include certificate

theorem u8ToNat_evaluates (room : 1 ≤ limits.locals) (a : UInt8) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (entry : program.entry = links.u8ToNat) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] value ∧ Number links.conversions.layout (a.toNat) value := by
  obtain ⟨path, representedResult⟩ := certificate.u8ToNat_returns limits room a value represented #[]
  refine ⟨path.evaluates ?_, representedResult⟩
  simp [initialState, admitted, enter, entry, certificate.u8ToNat.code, identity,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u8ToU32_evaluates (room : 1 ≤ limits.locals) (a : UInt8) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (entry : program.entry = links.u8ToU32) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] value ∧ Number links.conversions.layout (a.toUInt32.toNat) value := by
  obtain ⟨path, representedResult⟩ := certificate.u8ToU32_returns limits room a value represented #[]
  refine ⟨path.evaluates ?_, representedResult⟩
  simp [initialState, admitted, enter, entry, certificate.u8ToU32.code, identity,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32ToNat_evaluates (room : 1 ≤ limits.locals) (a : UInt32) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (entry : program.entry = links.u32ToNat) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] value ∧ Number links.conversions.layout (a.toNat) value := by
  obtain ⟨path, representedResult⟩ := certificate.u32ToNat_returns limits room a value represented #[]
  refine ⟨path.evaluates ?_, representedResult⟩
  simp [initialState, admitted, enter, entry, certificate.u32ToNat.code, identity,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem usizeToNat_evaluates (room : 1 ≤ limits.locals) (a : USize) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (entry : program.entry = links.usizeToNat) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] value ∧ Number links.conversions.layout (a.toNat) value := by
  obtain ⟨path, representedResult⟩ := certificate.usizeToNat_returns limits room a value represented #[]
  refine ⟨path.evaluates ?_, representedResult⟩
  simp [initialState, admitted, enter, entry, certificate.usizeToNat.code, identity,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u8OfNat_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u8OfNat) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] (cachedValue links.conversions.layout (UInt8.ofNat n).toNat) := by
  apply (certificate.u8OfNat_returns limits room capacity bytesCapacity n value represented valid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u8OfNat.code, truncate,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32OfNat_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32OfNat) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] (cachedValue links.conversions.layout (UInt32.ofNat n).toNat) := by
  apply (certificate.u32OfNat_returns limits room capacity bytesCapacity n value represented valid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32OfNat.code, truncate,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem usizeOfNat_evaluates (room : 11 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64)
    (n : Nat) (value : Value) (represented : Number links.conversions.layout n value)
    (valid : (Scalar.nat n).validate limits = .ok ())
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.usizeOfNat) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] (cachedValue links.conversions.layout (USize.ofNat n).toNat) := by
  apply (certificate.usizeOfNat_returns limits room capacity bytesCapacity platform n value represented valid #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.usizeOfNat.code, truncate,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32ToU8_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a : UInt32) (value : Value)
    (represented : Number links.conversions.layout a.toNat value)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32ToU8) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value] = .ok ()) :
    Evaluates limits program #[value] (cachedValue links.conversions.layout a.toUInt8.toNat) := by
  apply (certificate.u32ToU8_returns limits room capacity bytesCapacity a value represented #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32ToU8.code, truncate,
    Frame.check, inputs, frameState, show ¬limits.locals < 1 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32OfNatLT_evaluates (room : 11 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (n : Nat) (bounded : n < UInt32.size)
    (value proofValue : Value) (represented : Number links.conversions.layout n value)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32OfNatLT) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [value, proofValue] = .ok ()) :
    Evaluates limits program #[value, proofValue] (cachedValue links.conversions.layout (UInt32.ofNatLT n bounded).toNat) := by
  apply (certificate.u32OfNatLT_returns limits room capacity bytesCapacity n bounded value proofValue represented #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32OfNatLT.code, truncate,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u8Equal_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u8Equal) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (decide (a = b)))) := by
  apply (certificate.u8Equal_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u8Equal.code, compare,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32Equal_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32Equal) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (decide (a = b)))) := by
  apply (certificate.u32Equal_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32Equal.code, compare,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32Less_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32Less) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (decide (a < b)))) := by
  apply (certificate.u32Less_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32Less.code, compare,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem usizeEqual_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.usizeEqual) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (decide (a = b)))) := by
  apply (certificate.usizeEqual_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.usizeEqual.code, compare,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem usizeLess_evaluates (room : 10 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.usizeLess) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (.scalar (.bool (decide (a < b)))) := by
  apply (certificate.usizeLess_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.usizeLess.code, compare,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u8Add_evaluates (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u8Add) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a + b).toNat) := by
  apply (certificate.u8Add_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u8Add.code, modular,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32Add_evaluates (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32Add) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a + b).toNat) := by
  apply (certificate.u32Add_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32Add.code, modular,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32Mul_evaluates (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32Mul) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a * b).toNat) := by
  apply (certificate.u32Mul_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32Mul.code, modular,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem usizeAdd_evaluates (room : 14 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64)
    (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.usizeAdd) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a + b).toNat) := by
  apply (certificate.usizeAdd_returns limits room capacity bytesCapacity platform a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.usizeAdd.code, modular,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32Sub_evaluates (room : 14 ≤ limits.locals) (capacity : 64 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes)
    (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.u32Sub) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a - b).toNat) := by
  apply (certificate.u32Sub_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32Sub.code, subtract,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem usizeSub_evaluates (room : 14 ≤ limits.locals) (capacity : 65 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (platform : System.Platform.numBits = 64)
    (a b : USize) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 3 ≤ limits.continuations)
    (entry : program.entry = links.usizeSub) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a - b).toNat) := by
  apply (certificate.usizeSub_returns limits room capacity bytesCapacity platform a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.usizeSub.code, subtract,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32And_evaluates (room : 11 ≤ limits.locals) (capacity : 33 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 2 ≤ limits.continuations)
    (entry : program.entry = links.u32And) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a &&& b).toNat) := by
  apply (certificate.u32And_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32And.code, logical,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32Or_evaluates (room : 11 ≤ limits.locals) (capacity : 33 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 2 ≤ limits.continuations)
    (entry : program.entry = links.u32Or) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a ||| b).toNat) := by
  apply (certificate.u32Or_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32Or.code, logical,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32Xor_evaluates (room : 11 ≤ limits.locals) (capacity : 33 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 2 ≤ limits.continuations)
    (entry : program.entry = links.u32Xor) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a ^^^ b).toNat) := by
  apply (certificate.u32Xor_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32Xor.code, logical,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u8ShiftLeft_evaluates (room : 11 ≤ limits.locals) (capacity : 33 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 2 ≤ limits.continuations)
    (entry : program.entry = links.u8ShiftLeft) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a <<< b).toNat) := by
  apply (certificate.u8ShiftLeft_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u8ShiftLeft.code, shift,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u8ShiftRight_evaluates (room : 11 ≤ limits.locals) (capacity : 33 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt8) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 2 ≤ limits.continuations)
    (entry : program.entry = links.u8ShiftRight) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a >>> b).toNat) := by
  apply (certificate.u8ShiftRight_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u8ShiftRight.code, shift,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32ShiftLeft_evaluates (room : 11 ≤ limits.locals) (capacity : 33 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 2 ≤ limits.continuations)
    (entry : program.entry = links.u32ShiftLeft) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a <<< b).toNat) := by
  apply (certificate.u32ShiftLeft_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32ShiftLeft.code, shift,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

theorem u32ShiftRight_evaluates (room : 11 ≤ limits.locals) (capacity : 33 ≤ limits.natBits)
    (bytesCapacity : 8 ≤ limits.byteArrayBytes) (a b : UInt32) (left right : Value)
    (leftRep : Number links.conversions.layout a.toNat left)
    (rightRep : Number links.conversions.layout b.toNat right)
    (stack : 2 ≤ limits.continuations)
    (entry : program.entry = links.u32ShiftRight) (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [left, right] = .ok ()) :
    Evaluates limits program #[left, right] (cachedValue links.conversions.layout (a >>> b).toNat) := by
  apply (certificate.u32ShiftRight_returns limits room capacity bytesCapacity a b left right leftRep rightRep #[] (by simpa using stack)).evaluates
  simp [initialState, admitted, enter, entry, certificate.u32ShiftRight.code, shift,
    Frame.check, inputs, frameState, show ¬limits.locals < 2 by omega,
    bind, Except.bind, pure, Except.pure]

end Compilatrix.Ixby.Runtime.Words.Certificate
