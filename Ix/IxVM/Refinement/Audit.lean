import Ix.IxVM.Refinement.Statement
import IxC.Kernel.Audit.Axioms

/-! # The IxVM ↔ IxC refinement statement, frozen

`#print` freezes every statement (`def … : Prop`) of
`Ix.IxVM.Refinement.Statement` and every definition they read from
`Ix.IxVM.Refinement.Claim`; `#guard_kernel_axioms` and
`#guard_module_axioms` freeze the axioms of the composition theorems and of
both modules (decision D5: `propext`, `Classical.choice`, `Quot.sound`). A
change to any of them fails the build, so the statement cannot drift
silently.

Two guards keep the statement about the deployed object:

* it names `IxVM.program` and the entry `IxVM::verify_claim` (the `run_meta`
  check below, beside the frozen text);
* it is not vacuous for want of a preparation: preparing `IxVM.program` for
  `verify_claim` succeeds, selects the entry, and the entry's world prepares
  a call on a digest argument (`#guard`, evaluated when this module builds;
  an evaluation, not a proof). -/

namespace IxVM.Refinement.Audit

open IxVM.Refinement

example : verifyClaim = "IxVM::verify_claim" := rfl

open Lean in
run_meta do
  let names : List (Name × List Name) := [
    (``SourceSound, [``IxVM.program, ``verifyClaim, ``Aiur.Modules.prepare,
      ``Aiur.Modules.Prepared.EvalFn, ``digestValue]),
    (``CircuitSound, [``IxVM.program, ``verifyClaim, ``Aiur.Modules.prepare,
      ``AcyclicDerivation, ``digestValue]),
    (``IxVMClaimSpec, [``packDigest, ``Address.blake3Pure, ``Ix.Claim.de, ``Ix.Claim.Holds]),
    (``IxVMClaimSpecIn, [``packDigest, ``Address.blake3Pure, ``Ix.Claim.de, ``Ix.Claim.HoldsIn,
      ``View.Collision])]
  for (statement, needed) in names do
    let some info := (← getEnv).find? statement | throwError "{statement} is missing"
    let used := info.value!.getUsedConstants
    for n in needed do
      unless used.contains n do throwError "{statement} no longer names {n}"

#guard match Aiur.Modules.prepare IxVM.program [verifyClaim] with
  | .ok prepared => match prepared.find? verifyClaim with
    | some entry =>
      (prepared.environment.source.world.prepare entry.resolved.name [digestValue 0]).toBool
    | none => false
  | .error _ => false

#print IxVM.Refinement.SourceSound
#print IxVM.Refinement.CircuitSound
#print IxVM.Refinement.AcyclicDerivation
#print IxVM.Refinement.VerifyClaimSound
#print IxVM.Refinement.VerifyClaimSoundIn
#print IxVM.Refinement.VerifyClaimCircuitSound
#print IxVM.Refinement.VerifyClaimCircuitSoundIn
#print IxVM.Refinement.IxVMClaimSpec
#print IxVM.Refinement.IxVMClaimSpecIn
#print IxVM.Refinement.packDigest
#print IxVM.Refinement.digestValue
#print IxVM.Refinement.verifyClaim
#print Ix.Claim.Holds
#print Ix.Claim.HoldsIn
#print Ix.Claim.Covers
#print IxVM.Refinement.TypingIn
#print IxVM.Refinement.AssumingIn
#print IxVM.Refinement.AcceptsIn
#print IxVM.Refinement.Draws
#print IxVM.Refinement.BindingIn
#print IxVM.Refinement.BindingSeeds
#print IxVM.Refinement.EvalOutputIn
#print IxVM.Refinement.RevealLE
#print IxVM.Refinement.View.Authentic
#print IxVM.Refinement.View.Collision
#print IxVM.Refinement.View.Preimage
#print IxVM.Refinement.View.Closed
#print IxVM.Refinement.View.TypingCovers
#print IxVM.Refinement.treeRoot

#check @IxVM.Refinement.circuitSound_of_sourceSound
#check @IxVM.Refinement.SourceSound.run

#guard_kernel_axioms IxVM.Refinement.circuitSound_of_sourceSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.SourceSound.run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSoundIn [propext, Classical.choice, Quot.sound]

#guard_module_axioms Ix.IxVM.Refinement.Claim Ix.IxVM.Refinement.Statement

end IxVM.Refinement.Audit
