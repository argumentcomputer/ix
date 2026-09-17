import Compilatrix.Ixby.Runtime.Native.Code
import Compilatrix.Ixby.Runtime.ScalarFunction

/-! Certificates bind complete current runtime bodies to the actual program.
No digest, Boolean equality oracle, host evaluation, or source execution is
used as evidence. The private prefix makes every call target reviewable. -/

namespace Compilatrix.Ixby.Runtime.Native

open Ix.Ixby ScalarFunction

structure FunctionPrefix (program : Program) (entries : Array Code.Entry) (count : Nat) where
  checked : ∀ i, i < count → (bound : i < entries.size) →
    Checked program entries[i].id entries[i].body

def checkFunctions (program : Program) (entries : Array Code.Entry) :
    (count : Nat) → count ≤ entries.size → Except String (FunctionPrefix program entries count)
  | 0, _ => .ok ⟨fun _ impossible _ => False.elim (Nat.not_lt_zero _ impossible)⟩
  | count + 1, bound => do
    let previous ← checkFunctions program entries count (by omega)
    let index : count < entries.size := by omega
    let current ← check program entries[count].id entries[count].body
    return ⟨fun i below available => by
      by_cases equal : i = count
      · subst i; exact current
      · exact previous.checked i (by omega) available⟩

structure ConstructorPrefix (program : Program) (entries : Array (Lean.Name × CtorDecl))
    (count : Nat) : Type where
  checked : ∀ i, i < count → (bound : i < entries.size) →
    program.getConstructor i = .ok entries[i].2

def checkConstructors (program : Program) (entries : Array (Lean.Name × CtorDecl)) :
    (count : Nat) → count ≤ entries.size → Except String (ConstructorPrefix program entries count)
  | 0, _ => .ok ⟨fun _ impossible _ => False.elim (Nat.not_lt_zero _ impossible)⟩
  | count + 1, bound => do
    let previous ← checkConstructors program entries count (by omega)
    let index : count < entries.size := by omega
    match found : program.getConstructor count with
    | .error _ => throw s!"missing native runtime constructor {count}"
    | .ok actual =>
      if equal : actual = entries[count].2 then
        return ⟨fun i below available => by
          by_cases same : i = count
          · subst i; exact equal ▸ found
          · exact previous.checked i (by omega) available⟩
      else throw s!"native runtime constructor differs: {count}"

structure Certificate (program : Program) where
  functions : FunctionPrefix program Code.entries Code.entries.size
  constructors : ConstructorPrefix program Code.constructors Code.constructors.size

def certify (program : Program) : Except String (Certificate program) := do
  return {
    functions := ← checkFunctions program Code.entries Code.entries.size (Nat.le_refl _)
    constructors := ← checkConstructors program Code.constructors Code.constructors.size (Nat.le_refl _) }

def Certificate.function {program : Program} (certificate : Certificate program)
    (index : Nat) (bound : index < Code.entries.size := by decide) :
    Checked program Code.entries[index].id Code.entries[index].body :=
  certificate.functions.checked index bound bound

theorem Certificate.constructor {program : Program} (certificate : Certificate program)
    (index : Nat) (bound : index < Code.constructors.size := by decide) :
    program.getConstructor index = .ok Code.constructors[index].2 :=
  certificate.constructors.checked index bound bound

theorem Certificate.bytesCtor {program : Program} (certificate : Certificate program) :
    program.getConstructor 0 = .ok ⟨⟨1, 0, 0⟩, 2⟩ := certificate.constructor 0

theorem Certificate.arrayCtor {program : Program} (certificate : Certificate program) :
    program.getConstructor 1 = .ok ⟨⟨1, 0, 1⟩, 1⟩ := certificate.constructor 1

theorem Certificate.writerCtor {program : Program} (certificate : Certificate program) :
    program.getConstructor 2 = .ok ⟨⟨1, 0, 2⟩, 1⟩ := certificate.constructor 2

end Compilatrix.Ixby.Runtime.Native
