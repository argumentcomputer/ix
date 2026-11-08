import Ix.IxVM.Refinement.Statement
import IxC.Kernel.Audit.Axioms

/-! # The IxVM ↔ IxC refinement statement, frozen

`#print` freezes every statement (`def … : Prop`) of
`Ix.IxVM.Refinement.Statement`, every definition they read from
`Ix.IxVM.Refinement.Claim`, the observed semantics' records
(`Ix.IxVM.Refinement.Observe`) and the policy forms of IxC's acceptance
(`Ix.Cert.IxonAcceptsRefUnder`, `Ix.Kernel.Cached.AcceptsRefUnder`); the
structurally recursive tree functions are frozen by their equations.
`#check` freezes the proved theorems, and `#guard_kernel_axioms` and
`#guard_module_axioms` freeze the axioms of the statements, the theorems and
the modules (decision D5: `propext`, `Classical.choice`, `Quot.sound`). A
change to any of them fails the build, so the statement cannot drift
silently. The module is outside any namespace, so every name prints in full.

Two guards keep the statement about the deployed object:

* it names `IxVM.program` and the entry `IxVM::verify_claim` (the `run_meta`
  check, beside the frozen text);
* it is not vacuous for want of a preparation, and its escape names a real
  function: preparing `IxVM.program` for `verify_claim` succeeds, selects the
  entry, the entry's world prepares a call on a digest argument, and the
  prepared program has the function `Blake3::hash` the escape observes, whose
  one parameter is a pointer to the byte-stream enum `Hashed` reads
  (`#guard`, evaluated when this module builds; an evaluation, not a
  proof). -/

example : IxVM.Refinement.verifyClaim = "IxVM::verify_claim" := rfl
example : IxVM.Refinement.blake3Hash = "Blake3::hash" := rfl
example : IxVM.Refinement.byteStreamEnum = "${\"name\":\"Lists::Node\",\"types\":[\"field\"]}" := rfl

open Lean in
run_meta do
  let names : List (Name × List Name) := [
    (``IxVM.Refinement.SourceSound, [``IxVM.program, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Modules.prepare, ``Aiur.Modules.Prepared.ObsFn, ``IxVM.Refinement.digestValue]),
    (``IxVM.Refinement.CircuitSound, [``IxVM.program, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Modules.prepare, ``IxVM.Refinement.AcyclicDerivation, ``IxVM.Refinement.digestValue,
      ``IxVM.Refinement.CallsInROM]),
    (``IxVM.Refinement.CircuitSoundUntied, [``IxVM.program, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Modules.prepare, ``IxVM.Refinement.AcyclicDerivation, ``IxVM.Refinement.digestValue]),
    (``IxVM.Refinement.IxVMClaimSpecIn, [``IxVM.Refinement.packDigest, ``Address.blake3Pure,
      ``Ix.Claim.de, ``Ix.Claim.HoldsIn, ``IxVM.Refinement.View.HashedCollision]),
    (``IxVM.Refinement.Hashed, [``IxVM.Refinement.blake3Hash, ``IxVM.Refinement.byteStreamEnum])]
  for (statement, needed) in names do
    let some info := (← getEnv).find? statement | throwError "{statement} is missing"
    let used := info.value!.getUsedConstants
    for n in needed do
      unless used.contains n do throwError "{statement} no longer names {n}"

#guard match Aiur.Modules.prepare IxVM.program [IxVM.Refinement.verifyClaim] with
  | .ok prepared => match prepared.find? IxVM.Refinement.verifyClaim with
    | some entry =>
      (prepared.environment.source.world.prepare entry.resolved.name
          [IxVM.Refinement.digestValue 0]).toBool &&
        (match prepared.environment.source.program.sourceFunction? IxVM.Refinement.blake3Hash with
          | some f => f.params.map Prod.snd == [.ptr (.enum IxVM.Refinement.byteStreamEnum)]
          | none => false)
    | none => false
  | .error _ => false

/-! ## The statements -/

#print IxVM.Refinement.VerifyClaimSoundIn

#print IxVM.Refinement.VerifyClaimCircuitSoundIn

#print IxVM.Refinement.VerifyClaimCircuitSoundInUntied

#print IxVM.Refinement.SourceSound

#print IxVM.Refinement.CircuitSound

#print IxVM.Refinement.CircuitSoundUntied

#print IxVM.Refinement.ObservedHeadline

#print IxVM.Refinement.AcyclicDerivation

#print IxVM.Refinement.traceROM

#print IxVM.Refinement.CallsInROM

#print IxVM.Refinement.IxVMClaimSpecIn

#print IxVM.Refinement.View.HashedCollision

#print IxVM.Refinement.Hashed

#print IxVM.Refinement.blake3Hash
#print IxVM.Refinement.byteStreamEnum

#print IxVM.Refinement.Digest

#print IxVM.Refinement.packDigest

#print IxVM.Refinement.digestValue

#print IxVM.Refinement.verifyClaim

#print Aiur.Modules.Prepared.ObsFn

#print Aiur.Generic.SourceSemantics.Call

/-! ## What a claim means -/

#print Ix.Claim.HoldsIn

#print Ix.Claim.Covers

#print IxVM.Refinement.TypingIn

#print IxVM.Refinement.AxiomScopeIn
#print IxVM.Refinement.UserAxiomLeavesIn

#print IxVM.Refinement.AssumingIn

#print IxVM.Refinement.AcceptsIn

#print IxVM.Refinement.Scope

#print IxVM.Refinement.Scope.strict

#print IxVM.Refinement.UserAxiomsWithin

#print IxVM.Refinement.Draws

#print IxVM.Refinement.IsRecursorRecord

#print IxVM.Refinement.BindingIn

#print IxVM.Refinement.BindingSeeds

#print IxVM.Refinement.EvalValues

#print IxVM.Refinement.declValue?

#print IxVM.Refinement.AddressKey

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

/-! ## IxC acceptance under an axiom policy -/

#print Ix.Cert.IxonAcceptsRefUnder

#print Ix.Kernel.Cached.AcceptsRefUnder

#print Ix.Kernel.checkDeclsPureUnder

#print Ix.Kernel.checkDeclUnder

#print Ix.Kernel.checkUserAxiomDecl

/-! ## Views -/

#print IxVM.Refinement.View

#print IxVM.Refinement.View.LeavesAt

#print IxVM.Refinement.View.HoldsTree

#print IxVM.Refinement.View.binding?

#print IxVM.Refinement.View.Stores

#print IxVM.Refinement.View.Authentic

#print IxVM.Refinement.View.Preimage

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

#check @Aiur.Generic.SourceSemantics.EvalFn.observe

#check @Aiur.Generic.SourceSemantics.ObsFn.erase

#check @Aiur.Modules.Prepared.EvalFn.observe

#check @Aiur.Modules.Prepared.ObsFn.erase

#check @IxVM.Refinement.SourceSound.eval

#check @IxVM.Refinement.SourceSound.run

#check @IxVM.Refinement.circuitSoundUntied_of_sourceSound

#check @IxVM.Refinement.circuitSound_of_sourceSound

#check @IxVM.Refinement.AcceptsIn.ixonAcceptsRefUnder

#check @IxVM.Refinement.AcceptsIn.ixonAcceptsRef

#check @Ix.Cert.ixonAcceptsRefUnder_strict

#check @Ix.Kernel.Cached.acceptsRefUnder_strict

#check @Ix.Kernel.Cached.acceptsRefUnder_iff_of_nil

#guard_kernel_axioms Aiur.Generic.SourceSemantics.EvalFn.observe [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Aiur.Generic.SourceSemantics.ObsFn.erase [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.SourceSound.eval [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.SourceSound.run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.circuitSoundUntied_of_sourceSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.circuitSound_of_sourceSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSoundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSoundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSoundInUntied [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.ObservedHeadline [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.ixonAcceptsRefUnder_strict [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.acceptsRefUnder_strict [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.acceptsRefUnder_iff_of_nil [propext, Classical.choice, Quot.sound]

#guard_module_axioms Ix.IxVM.Refinement.Observe Ix.IxVM.Refinement.Claim Ix.IxVM.Refinement.Statement
  Ix.Cert.AcceptsUnder IxC.Kernel.Verify.Cached.ReferenceUnder
