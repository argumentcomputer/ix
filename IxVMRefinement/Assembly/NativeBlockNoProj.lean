import IxVMRefinement.Decl.NativeEnv
import IxC.Kernel.Semantics.Inductives.DeclNativeRecLateExtJ

/-! # No stored constructor type of a registered family projects out of the family

The late recursor step's comparison reads, of the matched registry entry, that no stored
constructor type projects out of the family (`Decl.noProjAt`). The native block's constructor
stage has it (`Decl.noProjAt_of_infer_full`: the constructors are typed where the family has no
projection table yet); neither the store nor the registry entry carries it, so the fold carries
it beside the registry (`RetHeadRegistry`).

`BlockFamCtorNoProj` has the body of the recursor step's `FamCtorNoProj`.
-/

namespace IxVM.Refinement.Typing

open Ix.Kernel (ConstantVal)
open Ix.Kernel.Semantics (NativeFam)

/-- **No stored constructor type of the family projects out of the family.** -/
def BlockFamCtorNoProj (fam : NativeFam .anon) : Prop :=
  ∀ (j : Nat) (cA : ConstantVal .anon × Nat), fam.ctorsA[j]? = some cA →
    Decl.noProjAt fam.p.cvT.name cA.1.type = true

end IxVM.Refinement.Typing
