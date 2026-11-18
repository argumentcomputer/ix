import IxVMRefinement.Endpoint.ComposedResidual
import IxVMRefinement.Assembly.TypingDefnLimKeyed
import IxVMRefinement.Binding.RegistryBasis

/-! # Two open obligations at the registered-family clause

`circuitComposed_residual` takes its hypotheses for any carried clause. At the clause the
steps carry today, `NativeBlockXR`, two of them have a conditional theorem. This file applies
each and states what it leaves:

* `standaloneDefinition_registered`: the step of a top-walked standalone definition, at either
  limit, from `unitStep_defn_lim_nativeXR`. What is left is that the key of such a record's
  address is free where the table binds a role to the address; elsewhere it is free outright
  (`keyFree_keyOf_of_unbound`).
* `basisGroups_registered`: the invariant at the six basis groups, from `basisBase_registered`.
  What is left is of the run: its table's check, the pinned prelude, and that its store at
  group 6 holds the basis store's entries.

Neither changes what `circuitComposed_residual` assumes; they show that its two hypotheses
have the shape the existing theorems produce.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Endpoint

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

/-- **The step of a top-walked standalone definition at the registered-family clause**, at the
walk's limit, from key-freeness at the addresses the table binds a role to. -/
theorem standaloneDefinition_registered
    (boundKeyFree : ∀ (calls : List (Call F)) (bAddr : _root_.Address)
      (t : Ix.Kernel.RoleTable) (seeds : List _root_.Address) (E₀ : Ixon.Env)
      (lim : Option Nat) (Top : _root_.Address → Prop) (rank : _root_.Address → Nat),
      Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank →
      ∀ (A : _root_.Address) (c : Ixon.Constant) (d : Ixon.Definition),
        Top A → recordOf E₀ A = some c → c.info = .defn d → d.kind = .defn →
        (∃ r, (r, A) ∈ t.bound.toList) → Decl.KeyFree (keyOf t A)) :
    WalkedUnitStep.{u} NativeBlockXR.{u} fun _ _ _ _ c =>
      ∃ d : Ixon.Definition, c.info = .defn d ∧ d.kind = .defn := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hinert hcover hchk
  obtain ⟨d, hinfo, hk⟩ := hkind
  have hchk' : Claim.CheckedLimAt calls bAddr t A lim := by
    rcases hchk with ⟨ms, hms, -⟩ | h
    · have e := hinfo.symm.trans hms
      cases e
    · exact h
  have hkey : Decl.KeyFree (keyOf t A) := by
    by_cases hb : ∃ r, (r, A) ∈ t.bound.toList
    · exact boundKeyFree calls bAddr t seeds E₀ lim Top rank hW A c d hT hc hinfo hk hb
    · exact keyFree_keyOf_of_unbound (fun r h => hb ⟨r, h⟩)
  exact unitStep_defn_lim_nativeXR ht hS hst hc hinfo hlog hk hchk' hkey hinert hcover

/-- **The invariant at the six basis groups at the registered-family clause**, from the run's
table check, its pinned prelude and its store at group 6. -/
theorem basisGroups_registered
    {Run : List (Call F) → Ix.Kernel.RoleTable → BRun → (Nat → Ixon.Env) → Prop}
    (hrun : ∀ calls t ρ Rs, Run calls t ρ Rs →
      t.check = .ok () ∧ PreludePinned t ∧
        (∀ a, (Rs 6).consts.get? a = StoreInhabit.basisStore.consts.get? a) ∧
        ∀ a, (Rs 6).blobs.get? a = StoreInhabit.basisStore.blobs.get? a) :
    ∀ calls, BasisBase.{u} (StoreX NativeBlockXR.{u}) (Run calls) :=
  fun calls => basisBase_registered (hrun calls)

end IxVM.Refinement.Endpoint
