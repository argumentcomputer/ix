import IxVMRefinement.FamilyGraph.Composition
import IxVMRefinement.Binding.FoldFamily

/-! # The composed statement with the binding half's family form

The two halves meet at one internal part of the table witness. With the binding fold's family form
(`Binding.binding_skeleton_overW`) the binding half gives the witness with its stored families,
`OverWFam L` (the internal part `OverW L` and one selected family map). The typing half over the
family graph (`typing_skeleton_over_family`) is stated at `OverW L`; it holds at every internal
part that has `OverW L` as a part (`typingSpecOn_mono`), so at `OverWFam L`. When the typing half
reads the stored families from the witness (its imports of the family map), it is stated at
`OverWFam L` itself and the weakening goes.

* `typingSpecOn_mono`: the typing half at an internal part holds at every stronger one.
* `composed_skeleton_over_familyW`: **the composed statement**, the binding half with the family
  form and the typing half over the family graph, joined at `OverWFam L` by `binding_discharge`.
-/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.Binding

set_option linter.unusedVariables false

/-- **The typing half at an internal part holds at every stronger one**: a witness of the stronger
part is one of the weaker. -/
theorem typingSpecOn_mono
    {Facts Facts' : Ix.Kernel.RoleTable → (Nat → Prop) → Ixon.Env → Ix.Kernel.Env .anon → Prop}
    (hF : ∀ t G R env, Facts' t G R env → Facts t G R env) {calls : List (Call F)} {d : Digest}
    (h : TypingSpecOn.{u} Facts calls d) : TypingSpecOn.{u} Facts' calls d := by
  intro bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT hW
  exact h bytes c hde hdig hscope V seeds hseeds ctx hctx tb t hadm R envT
    ⟨hW.shape, hF _ _ _ _ hW.facts⟩

/-- **The composed statement with the binding half's family form** (module docstring): the binding
half from its named hypotheses (`Binding.binding_skeleton_overW`), the typing half from the walk,
its limit, its graph and `FamilySteps`, at the internal part with its stored families. -/
theorem composed_skeleton_over_familyW {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {Run : Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    {Fam : BRun → Ix.Kernel.RoleTable → Nat → Ixon.Env → Ixon.Env →
      (_root_.Address → Option _root_.Address) → (_root_.Address → _root_.Address → Prop) →
      (_root_.Address → _root_.Address → Prop) → Prop}
    {Walk : Ix.Kernel.RoleTable → List _root_.Address → Ixon.Env → Option Nat →
      (_root_.Address → Prop) → (_root_.Address → Nat) → Prop}
    {callsA callsB : List (Call F)} {dA dB : Digest}
    (bindingClaimExport : BindingClaimExportObs Run callsB dB)
    (basisGroups : BasisOverW.{u} L Run)
    (groupAdmissions : AdmitsChain Run) (groupAdmissionReads : AdmitsReadsChain Run)
    (groupFamilies : FamiliesChain Run Fam)
    (groupClosure : AtGroups Run fun ρ t g => ClosureStepOverFamilyW.{u} L ρ t g (Fam ρ t g))
    (groupWithoutRoleUnit : AtGroups Run (RoleFreeShapes.{u} L))
    (operationRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ RoleOps.opRoles) L))
    (standardAxiomRoleUnit : AtGroups Run (RoleUnitStepOverW.{u} (· ∈ standardAxioms) L))
    (hb : Bounded callsA) (hclaimA : ClaimExport Walk callsA dA) (hlim : WalkLim Walk)
    (hgraph : ∀ t seeds E₀ lim Top rank, Walk t seeds E₀ lim Top rank →
      TopGraph t E₀ seeds Top rank)
    (hstepsA : FamilySteps.{u} L callsA Walk) :
    ComposedSpec.{u} callsA callsB dA dB :=
  binding_discharge
    (binding_skeleton_overW bindingClaimExport basisGroups groupAdmissions groupAdmissionReads
      groupFamilies groupClosure groupWithoutRoleUnit operationRoleUnit standardAxiomRoleUnit)
    (typingSpecOn_mono (fun _ _ _ _ h => h.1)
      (typing_skeleton_over_family hb hclaimA hlim hgraph hstepsA))

end IxVM.Refinement.Typing
