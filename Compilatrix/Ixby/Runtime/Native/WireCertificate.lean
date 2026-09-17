import Compilatrix.Ixby.Runtime.Native.Certificate
import Compilatrix.Ixby.Runtime.Native.Code.Wire

namespace Compilatrix.Ixby.Runtime.Native

open Lean Ix.Ixby

def wireConstructors : Array (Name × CtorDecl) := Code.constructors ++ #[
  (`MultiStark.Verify.Codec.Wire.WriteState.mk, ⟨⟨1, 0, 5⟩, 4⟩),
  (`Except.error, ⟨⟨1, 0, 6⟩, 1⟩), (`Except.ok, ⟨⟨1, 0, 7⟩, 1⟩),
  (`MultiStark.Verify.DecodeError.byteLimit, ⟨⟨1, 0, 8⟩, 0⟩),
  (`PUnit.unit, ⟨⟨1, 0, 9⟩, 0⟩), (`Prod.mk, ⟨⟨1, 0, 10⟩, 2⟩),
  (`MultiStark.Verify.DecodeError.field, ⟨⟨1, 0, 11⟩, 0⟩)]

structure WireCertificate (program : Program) where
  runtime : Certificate program
  functions : FunctionPrefix program Code.wireEntries Code.wireEntries.size
  constructors : ConstructorPrefix program wireConstructors wireConstructors.size

def certifyWire (program : Program) : Except String (WireCertificate program) := do
  return {
    runtime := ← certify program
    functions := ← checkFunctions program Code.wireEntries Code.wireEntries.size (Nat.le_refl _)
    constructors := ← checkConstructors program wireConstructors wireConstructors.size (Nat.le_refl _) }

def WireCertificate.function {program : Program} (certificate : WireCertificate program)
    (index : Nat) (bound : index < Code.wireEntries.size := by decide) :
    ScalarFunction.Checked program Code.wireEntries[index].id Code.wireEntries[index].body :=
  certificate.functions.checked index bound bound

theorem WireCertificate.constructor {program : Program} (certificate : WireCertificate program)
    (index : Nat) (bound : index < wireConstructors.size := by decide) :
    program.getConstructor index = .ok wireConstructors[index].2 :=
  certificate.constructors.checked index bound bound

theorem WireCertificate.stateCtor {program : Program} (certificate : WireCertificate program) :
    program.getConstructor 5 = .ok ⟨⟨1, 0, 5⟩, 4⟩ := certificate.constructor 5

theorem WireCertificate.errorCtor {program : Program} (certificate : WireCertificate program) :
    program.getConstructor 6 = .ok ⟨⟨1, 0, 6⟩, 1⟩ := certificate.constructor 6

theorem WireCertificate.okCtor {program : Program} (certificate : WireCertificate program) :
    program.getConstructor 7 = .ok ⟨⟨1, 0, 7⟩, 1⟩ := certificate.constructor 7

theorem WireCertificate.byteLimitCtor {program : Program} (certificate : WireCertificate program) :
    program.getConstructor 8 = .ok ⟨⟨1, 0, 8⟩, 0⟩ := certificate.constructor 8

theorem WireCertificate.unitCtor {program : Program} (certificate : WireCertificate program) :
    program.getConstructor 9 = .ok ⟨⟨1, 0, 9⟩, 0⟩ := certificate.constructor 9

theorem WireCertificate.pairCtor {program : Program} (certificate : WireCertificate program) :
    program.getConstructor 10 = .ok ⟨⟨1, 0, 10⟩, 2⟩ := certificate.constructor 10

theorem WireCertificate.fieldErrorCtor {program : Program} (certificate : WireCertificate program) :
    program.getConstructor 11 = .ok ⟨⟨1, 0, 11⟩, 0⟩ := certificate.constructor 11

end Compilatrix.Ixby.Runtime.Native
