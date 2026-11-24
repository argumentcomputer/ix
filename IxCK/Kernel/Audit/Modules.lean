import IxCK.Kernel
import IxCK.Kernel.Audit.Axioms
import IxCK.Kernel.Ixon.NonContradiction
import IxCK.Kernel.Ixon.PreludeShape
import IxCK.Kernel.Ixon.RoleTableInj
import IxCK.Kernel.Verify.Frontend.HoistUnits
import IxCK.Kernel.Verify.Frontend.InModelGenNested
import IxCK.Kernel.Verify.Rename.Model
import IxCK.Kernel.Verify.Rename.UnionUnits

/-! # Axioms of every kernel module

`Audit/Roots.lean` fixes the exact axioms of the public roots, and so bounds
every declaration they reach. Some of the package's theorems are reached by no
root:
* non-contradiction: no proposition is refuted in an environment a Source
  check accepts and proved in one a certificate's check installs
  (`Ixon/NonContradiction.lean`);
* the renaming development (`Verify/Rename/*`), with the union of two checks
  over a shared front and models pulled back along a renaming;
* the hoisting of Nat-operation units (`Verify/Frontend/HoistUnits.lean`) and
  the in-model generators under a renaming (`Verify/Frontend/InModel*`);
* the prelude's shape and a well-formed role table's injectivity
  (`Ixon/PreludeShape.lean`, `Ixon/RoleTableInj.lean`).

The library's glob builds them. This module imports them with the kernel, and
bounds every safe declaration of every module of the package that it imports
by the standard logical axioms `propext`, `Classical.choice` and `Quot.sound`
(`#guard_module_axioms_under`, `Audit/Axioms.lean`). The other audits and the
fixtures are not imported. Nor is the typing tier's answer view
(`Tier/Answer.lean`): the kernel's layering fence forbids importing it here.

The four modules that no other module of either package imports are also
named one by one, so that each fails here if it stops being imported or
declares nothing, and the exact axiom sets of their main theorems are
frozen. -/

#guard_module_axioms_under IxCK

#guard_module_axioms
  IxCK.Kernel.Ixon.NonContradiction
  IxCK.Kernel.Verify.Rename.UnionJoin
  IxCK.Kernel.Verify.Rename.UnionUnits
  IxCK.Kernel.Verify.Frontend.HoistUnits

#guard_kernel_axioms Ix.Kernel.nonContradiction [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Model.not_refuted_and_proved [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.AcceptsRef.union [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.unitsOk_of_check [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Frontend.unitsOf_hoist_lowerings [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Frontend.hoistNatOpGround_lowerings [propext, Classical.choice, Quot.sound]
