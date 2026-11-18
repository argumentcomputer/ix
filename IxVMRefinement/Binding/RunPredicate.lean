import IxVMRefinement.Binding.ClauseFold
import IxVMRefinement.StatementRel.LoadedReadsWalked

/-! # The run predicate of an accepted binding claim

The binding fold (`binding_skeleton_over`) is stated over a predicate `Run t ρ Rs` that relates a
role table, a run record and a sequence of stores, one per validation group. This file fixes it.

`BindingRun calls t ρ Rs` says what an accepted run of the circuit on a `binding` claim for the
table `t`, with the calls `calls`, establishes:

* the calls are those of a bounded derivation;
* the run record is the observed one (`observedRun`): `t` is the table the run's bytes admit at
  the claim's binding address, the check of a unit is the run's own call of
  `KernelCheck::check_const` under the role context at a named limit, and the validation of a
  role is the run's own call of `KernelRoles::validate_role`;
* the run's records are one store (`LoadedReads.RunStore`) that holds every record the run
  hashed (`LoadedReads.HashedRecordsStored`);
* the table pins the prelude, and the store after the six basis groups has the entries of the
  committed basis rows;
* the admission of each group from 6 to 76 takes the store before it to the store after it
  (`Admits`), with its reading clause (`AdmitsReads`).

With the predicate fixed, three hypotheses of the fold are theorems: the invariant at the six
basis groups (`basisOver_bindingRun`), the admission of each group (`admitsChain_bindingRun`) and
its reading clause (`admitsReadsChain_bindingRun`). They are projections: what they say of a run
is now part of what the claim's export (`BindingClaimExportObs (BindingRun calls)`) has to
produce from the run's observations. Nothing is proved about a run here.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.StoreInhabit (basisStore)

/-- **What an accepted binding claim's run establishes** about the table `t`, the run record `ρ`
and the stores `Rs` (module docstring). -/
structure BindingRun (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (ρ : BRun)
    (Rs : Nat → Ixon.Env) : Prop where
  /-- The calls are those of a bounded derivation. -/
  bounded : Bounded calls
  /-- The run record is the observed one, at the binding address the table admits at. -/
  observed : ∃ (bAddr : _root_.Address) (tb : ByteArray), Hashed calls tb ∧
    Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨bAddr, tb⟩ = .ok t ∧
    ρ = observedRun calls bAddr t ρ.E₀ ρ.rank
  /-- The run's records are one store. -/
  runStore : LoadedReads.RunStore calls ρ.E₀
  /-- The store holds every record the run hashed. -/
  hashedStored : LoadedReads.HashedRecordsStored calls ρ.E₀
  /-- The table binds the prelude roles at the committed prelude records. -/
  preludePinned : PreludePinned t
  /-- The store after the six basis groups has the committed basis rows' records. -/
  basisConsts : ∀ a, (Rs 6).consts.get? a = basisStore.consts.get? a
  /-- The store after the six basis groups has the committed basis rows' blobs. -/
  basisBlobs : ∀ a, (Rs 6).blobs.get? a = basisStore.blobs.get? a
  /-- The admission of each group from 6 to 76. -/
  admits : ∀ g, 6 ≤ g → g < 77 → Admits ρ t g (Rs g) (Rs (g + 1))
  /-- The reading clause of each group's admission. -/
  reads : ∀ g, 6 ≤ g → g < 77 → AdmitsReads ρ t (Rs g) (Rs (g + 1))

/-- **The invariant at the six basis groups, for a binding run.** -/
theorem basisOver_bindingRun (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) : BasisOver.{u} L (BindingRun calls) :=
  basisOver_of_run L fun _ _ _ h => ⟨h.preludePinned, h.basisConsts, h.basisBlobs⟩

/-- **The admission of each group, for a binding run.** -/
theorem admitsChain_bindingRun (calls : List (Call F)) : AdmitsChain (BindingRun calls) :=
  fun _ _ _ h => h.admits

/-- **The reading clause of each group's admission, for a binding run.** -/
theorem admitsReadsChain_bindingRun (calls : List (Call F)) :
    AdmitsReadsChain (BindingRun calls) :=
  fun _ _ _ h => h.reads

/-- The check a binding run's record names is the observed check at the binding address. -/
theorem BindingRun.checked_iff {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (h : BindingRun calls t ρ Rs) :
    ∃ bAddr : _root_.Address, ∀ a n,
      ρ.checked a n ↔ UnitCheckedAt calls bAddr t ρ.E₀ a (some n) := by
  obtain ⟨bAddr, tb, -, -, hρ⟩ := h.observed
  refine ⟨bAddr, fun a n => ?_⟩
  have e : ρ.checked = (observedRun calls bAddr t ρ.E₀ ρ.rank).checked := congrArg BRun.checked hρ
  rw [e]
  exact Iff.rfl

/-- The store after the last group holds records the run loaded. -/
theorem BindingRun.loadedBy_last {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (h : BindingRun calls t ρ Rs) : LoadedBy calls (Rs 77) :=
  loadedBy_sub h.runStore.loaded (h.admits 76 (by omega) (by omega)).loaded
    (h.admits 76 (by omega) (by omega)).loadedBlobs

end IxVM.Refinement.Binding
