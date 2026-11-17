module

public import IxC.Kernel.Semantics.Inductives.DeclNativeJ

@[expose] public section

/-!
# A stored native family's summary

`NativeFam` names what a native install leaves of an inductive family: the completed record,
the stored former, the telescope constant the stages read, and the stored constructors with
their field counts. The model lane keeps the family's data at a model under this summary
(`NativeFamOk`, `Model/Inductives/NativeFam.lean`), so that the recursor's stage applies to the
family at a later environment.
-/

namespace Ix.Kernel.Semantics

open Ix.Kernel (ConstantVal NativeParts)

/-- **A native family's summary**: the completed record (its recursor fields are not
read), the stored former, the telescope constant, and the stored constructors in order,
each with its field count. -/
structure NativeFam (md : Ix.Kernel.Mode) where
  /-- the completed record; `cvR`, `elim`, `large`, `rhss` and `recPinned` are not read -/
  p : NativeParts md
  /-- the stored former -/
  cvS : ConstantVal md
  /-- the telescope constant -/
  cvTa : ConstantVal md
  /-- the stored constructors, in order -/
  ctorsA : List (ConstantVal md × Nat)

end Ix.Kernel.Semantics
