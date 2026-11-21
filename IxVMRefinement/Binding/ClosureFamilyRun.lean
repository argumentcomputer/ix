import IxVMRefinement.Binding.ClosureFoldProof
import IxVMRefinement.Binding.RunPredicate

/-! # The closure in the family form at the binding run predicate

The residual's closure hypothesis in the family form (`GroupClosureFamily`): the closure of
every group of every binding run (`BindingRun`), from the closure fold (`ClosureFoldStatement`,
proved: `closureFoldStatement`) and its three step premises. It sits downstream of both the fold
and the run predicate, which reads the fold's `ClosureFam`. -/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-- **The residual's closure hypothesis in the family form**, at the binding run predicate: the
closure of every group of every run, in the family form with the walked records stored. -/
def GroupClosureFamily (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) : Prop :=
  ∀ calls, AtGroups (BindingRun calls) fun ρ t g =>
    ClosureStepOverFamilyW.{u} L ρ t g (ClosureFam calls ρ t g)

/-- **The residual's closure hypothesis from the fold and the three step premises at every
group of every run.** -/
theorem groupClosureFamily_of_fold {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (fold : ClosureFoldStatement.{u} L)
    (unitSteps : ∀ calls, AtGroups (BindingRun calls) (ClosureUnitSteps.{u} L calls))
    (familySteps : ∀ calls, AtGroups (BindingRun calls) (ClosureFamilySteps.{u} L calls))
    (twinSteps : ∀ calls, AtGroups (BindingRun calls) (ClosureTwinSteps.{u} L calls)) :
    GroupClosureFamily.{u} L := by
  intro calls t ρ Rs hrun hall ht g hg6 hg
  exact fold calls ρ t g hg6 hg hall ht (unitSteps calls t ρ Rs hrun hall ht g hg6 hg)
    (familySteps calls t ρ Rs hrun hall ht g hg6 hg) (twinSteps calls t ρ Rs hrun hall ht g hg6 hg)

/-- **The residual's closure hypothesis in the family form, from the three step premises at every
group of every run.** -/
theorem groupClosureFamily_of_steps {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (unitSteps : ∀ calls, AtGroups (BindingRun calls) (ClosureUnitSteps.{u} L calls))
    (familySteps : ∀ calls, AtGroups (BindingRun calls) (ClosureFamilySteps.{u} L calls))
    (twinSteps : ∀ calls, AtGroups (BindingRun calls) (ClosureTwinSteps.{u} L calls)) :
    GroupClosureFamily.{u} L :=
  groupClosureFamily_of_fold (closureFoldStatement L) unitSteps familySteps twinSteps

end IxVM.Refinement.Binding
