import Ix.IxVM.Refinement.Statement
import IxC.Kernel.Audit.Axioms

/-! # The IxVM ↔ IxC refinement statement, frozen

`#print` freezes every statement (`def … : Prop`) of
`Ix.IxVM.Refinement.Statement` and every definition they read from
`Ix.IxVM.Refinement.Claim`; the structurally recursive tree functions are
frozen by their equations. `#check` freezes the proved composition theorems,
and `#guard_kernel_axioms` and `#guard_module_axioms` freeze the axioms of
the statements, the theorems and both modules (decision D5: `propext`,
`Classical.choice`, `Quot.sound`). A change to any of them fails the build,
so the statement cannot drift silently. The module is outside any namespace,
so every name prints in full.

Two guards keep the statement about the deployed object:

* it names `IxVM.program` and the entry `IxVM::verify_claim` (the `run_meta`
  check, beside the frozen text);
* it is not vacuous for want of a preparation: preparing `IxVM.program` for
  `verify_claim` succeeds, selects the entry, and the entry's world prepares
  a call on a digest argument (`#guard`, evaluated when this module builds;
  an evaluation, not a proof). -/

example : IxVM.Refinement.verifyClaim = "IxVM::verify_claim" := rfl

open Lean in
run_meta do
  let names : List (Name × List Name) := [
    (``IxVM.Refinement.SourceSound, [``IxVM.program, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Modules.prepare, ``Aiur.Modules.Prepared.EvalFn, ``IxVM.Refinement.digestValue]),
    (``IxVM.Refinement.CircuitSound, [``IxVM.program, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Modules.prepare, ``IxVM.Refinement.AcyclicDerivation, ``IxVM.Refinement.digestValue]),
    (``IxVM.Refinement.IxVMClaimSpec, [``IxVM.Refinement.packDigest, ``Address.blake3Pure,
      ``Ix.Claim.de, ``Ix.Claim.Holds]),
    (``IxVM.Refinement.IxVMClaimSpecIn, [``IxVM.Refinement.packDigest, ``Address.blake3Pure,
      ``Ix.Claim.de, ``Ix.Claim.HoldsIn, ``IxVM.Refinement.View.Collision])]
  for (statement, needed) in names do
    let some info := (← getEnv).find? statement | throwError "{statement} is missing"
    let used := info.value!.getUsedConstants
    for n in needed do
      unless used.contains n do throwError "{statement} no longer names {n}"

#guard match Aiur.Modules.prepare IxVM.program [IxVM.Refinement.verifyClaim] with
  | .ok prepared => match prepared.find? IxVM.Refinement.verifyClaim with
    | some entry =>
      (prepared.environment.source.world.prepare entry.resolved.name
        [IxVM.Refinement.digestValue 0]).toBool
    | none => false
  | .error _ => false

/-! ## The statements -/

#print IxVM.Refinement.VerifyClaimSound
#print IxVM.Refinement.VerifyClaimSoundIn
#print IxVM.Refinement.VerifyClaimCircuitSound
#print IxVM.Refinement.VerifyClaimCircuitSoundIn
#print IxVM.Refinement.SourceSound
#print IxVM.Refinement.CircuitSound
#print IxVM.Refinement.AcyclicDerivation
#print IxVM.Refinement.IxVMClaimSpec
#print IxVM.Refinement.IxVMClaimSpecIn
#print IxVM.Refinement.Digest
#print IxVM.Refinement.packDigest
#print IxVM.Refinement.digestValue
#print IxVM.Refinement.verifyClaim

/-! ## What a claim means -/

#print Ix.Claim.Holds
#print Ix.Claim.HoldsIn
#print Ix.Claim.Covers
#print IxVM.Refinement.TypingIn
#print IxVM.Refinement.AssumingIn
#print IxVM.Refinement.AcceptsIn
#print IxVM.Refinement.Draws
#print IxVM.Refinement.IsRecursorRecord
#print IxVM.Refinement.BindingIn
#print IxVM.Refinement.BindingSeeds
#print IxVM.Refinement.EvalOutputIn
#print IxVM.Refinement.RevealLE
#print IxVM.Refinement.RevealMutLE
#print IxVM.Refinement.RevealDefnLE
#print IxVM.Refinement.RevealRecrLE
#print IxVM.Refinement.RevealIndcLE
#print IxVM.Refinement.RevealConstructorLE
#print IxVM.Refinement.revealRules
#print IxVM.Refinement.exprAddr
#print IxVM.Refinement.OptEq

/-! ## Views -/

#print IxVM.Refinement.View
#print IxVM.Refinement.View.LeavesAt
#print IxVM.Refinement.View.HoldsTree
#print IxVM.Refinement.View.binding?
#print IxVM.Refinement.View.Stores
#print IxVM.Refinement.View.Authentic
#print IxVM.Refinement.View.Preimage
#print IxVM.Refinement.View.Collision
#print IxVM.Refinement.View.Closed
#print IxVM.Refinement.View.TypingCovers

example (a : Address) : IxVM.Refinement.treeRoot (.leaf a) = Ix.HostAdmission.Merkle.leaf a := rfl
example : IxVM.Refinement.treeRoot .padding = Ix.HostAdmission.Merkle.padding := rfl
example (l r : Ix.AssumptionTree) : IxVM.Refinement.treeRoot (.node l r) =
    Ix.HostAdmission.Merkle.node (IxVM.Refinement.treeRoot l) (IxVM.Refinement.treeRoot r) := rfl
example (a : Address) : IxVM.Refinement.treeLeaves (.leaf a) = [a] := rfl
example : IxVM.Refinement.treeLeaves .padding = [] := rfl
example (l r : Ix.AssumptionTree) : IxVM.Refinement.treeLeaves (.node l r) =
    IxVM.Refinement.treeLeaves l ++ IxVM.Refinement.treeLeaves r := rfl
example (a : Address) : IxVM.Refinement.treeImages (.leaf a) = [ByteArray.mk #[0] ++ a.hash] := rfl
example : IxVM.Refinement.treeImages .padding = [] := rfl
example (l r : Ix.AssumptionTree) : IxVM.Refinement.treeImages (.node l r) =
    (ByteArray.mk #[1] ++ (IxVM.Refinement.treeRoot l).hash ++ (IxVM.Refinement.treeRoot r).hash) ::
      (IxVM.Refinement.treeImages l ++ IxVM.Refinement.treeImages r) := rfl

/-! ## Theorems and axioms -/

#check @IxVM.Refinement.circuitSound_of_sourceSound
#check @IxVM.Refinement.SourceSound.run

#guard_kernel_axioms IxVM.Refinement.circuitSound_of_sourceSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.SourceSound.run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSoundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSoundIn [propext, Classical.choice, Quot.sound]

#guard_module_axioms Ix.IxVM.Refinement.Claim Ix.IxVM.Refinement.Statement
