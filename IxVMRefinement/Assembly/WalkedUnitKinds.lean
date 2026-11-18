import IxVMRefinement.Endpoint.ComposedResidual
import IxVMRefinement.Assembly.BlockRouteFunctional
import IxVMRefinement.FamilyGraph.Graph

/-! # The kinds of a top-walked unit, in the shape the composed statement asks them

The composed statement (`Endpoint.circuitComposed_residual`) takes the step of a top-walked
unit kind by kind (`WalkedUnit`, `WalkedUnitStep`). This module gives, in that shape, what the
routing and the block kinds settle. Each statement either is a hypothesis of the composed
statement, or produces one from strictly smaller ones.

* `nativeBlockOtherTelescope_step`: the step of a one-type native block whose former reads as
  a telescope of another length. The circuit refuses such a block, so the kind is empty.
* `emptyBlock_step`, `definitionBlock_of_nonempty`: an empty block installs nothing; a block of
  definitions is empty or a non-empty block of definitions.
* `oneTypeBlockOffNativeRoute_of_modeled`: a one-type block off the native route is on the
  modeled route in the run and at the step's store, which is what a family step is handed.
* `otherBlock_of_kinds`: a block that is no block of definitions and no block of one inductive
  type is a block of two or more inductive types, which is on the modeled route in the run and
  at the step's store, or a non-empty block of recursors. A block of mixed kinds is refused.
* `recursorWithoutNativeParent_of_parts`: at a validating walk, a standalone recursor record
  whose check found no native parent at some environment has a major premise headed by a
  reserved basis name; what is left beside it is the walk at the assumed limit.
* `constAddrOf_emptyBlock`, `not_isUnit_emptyBlock`: an empty block has no constant address,
  so it is no unit of the family graph (`IsUnit`).
* `walkedUnit_byFamilyRecord`: a kind of block split by whether the family graph gives the
  block a family record; a modeled block whose only accepted family record is empty is the
  case without one.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Endpoint

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)

variable {X : Ix.Kernel.RoleTable → Ixon.Env → Ix.Kernel.Env .anon → Prop}

/-- **The step of a one-type native block whose former reads as a telescope of another
length**, for every carried clause: the circuit refuses the block
(`Typing.formerTeleOther_false`). -/
theorem nativeBlockOtherTelescope_step :
    WalkedUnitStep.{u} X fun calls t E₀ B cb =>
      ∃ ind : Ixon.Inductive,
        BlockUnitRecord E₀ B cb ind ∧ NativeRouteAt calls B ∧ FormerTeleOther t E₀ B cb ind := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ind, hrec, hnat, hother⟩ := hkind
  exact unitStep_formerTeleOther ht hS hst hrec hchk hnat hother hinert hcover

/-- **The step of an empty block**, for every carried clause: it installs nothing. -/
theorem emptyBlock_step :
    WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ ms.size = 0 := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ms, hcm, h0⟩ := hkind
  exact unitStep_emptyBlock hcm h0

/-- **The step of a block of definitions, from the step of a non-empty one.** -/
theorem definitionBlock_of_nonempty
    (nonemptyDefinitionBlock : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ 0 < ms.size ∧ DefnBlock ms) :
    WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ DefnBlock ms := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ms, hcm, hd⟩ := hkind
  rcases Nat.eq_zero_or_pos ms.size with h0 | hp
  · exact unitStep_emptyBlock hcm h0
  · exact nonemptyDefinitionBlock calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT
      hc hlog ⟨ms, hcm, hp, hd⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys

/-- **The step of a one-type block off the native route, from its step on the modeled route**:
the block is on the modeled route in the run (in the kind) and at the step's store (handed to
the goal). -/
theorem oneTypeBlockOffNativeRoute_of_modeled
    (oneTypeBlockModeled :
      WalkedUnit.{u} (fun calls _ E₀ B cb =>
          ∃ ind : Ixon.Inductive, BlockUnitRecord E₀ B cb ind ∧ ModeledRouteAt calls B)
        fun _ t envT E₀ E lim B cb =>
          ModeledAt E B → UnitStep.{u} (X t E) t envT E₀ E lim B cb) :
    WalkedUnitStep.{u} X fun calls _ E₀ B cb =>
      ∃ ind : Ixon.Inductive, BlockUnitRecord E₀ B cb ind ∧ ¬ NativeRouteAt calls B := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ind, hrec, hnn⟩ := hkind
  obtain ⟨hroute, hmod⟩ := modeled_of_offNativeRoute hS hst hcanon hrec hchk hnn
  exact oneTypeBlockModeled calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc
    hlog ⟨ind, hrec, hroute⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys hmod

/-- **The step of a block that is no block of definitions and no block of one inductive type,
from its two kinds**: a block of two or more inductive types, on the modeled route in the run
(in the kind) and at the step's store (handed to the goal); or a non-empty block of
recursors. -/
theorem otherBlock_of_kinds
    (mutualBlock :
      WalkedUnit.{u} (fun calls _ _ B cb =>
          ∃ ms : Array Ixon.MutConst, cb.info = .muts ms ∧ 2 ≤ ms.size ∧
            (∀ m ∈ ms.toList, ∃ i, m = Ixon.MutConst.indc i) ∧ ModeledRouteAt calls B)
        fun _ t envT E₀ E lim B cb =>
          ModeledAt E B → UnitStep.{u} (X t E) t envT E₀ E lim B cb)
    (recursorBlock : WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ 0 < ms.size ∧
        ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r) :
    WalkedUnitStep.{u} X fun _ _ _ _ c =>
      ∃ ms : Array Ixon.MutConst, c.info = .muts ms ∧ ¬ DefnBlock ms ∧
        ∀ ind : Ixon.Inductive, ms ≠ #[.indc ind] := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  obtain ⟨ms, hcm, hnd, hone⟩ := hkind
  rcases hW.otherBlock_cases hT hc hcm hnd hone with ⟨hsize, hall⟩ | ⟨hpos, hall⟩
  · obtain ⟨hroute, hmod⟩ := modeledRouteAt_of_multi ht hst hc hcm hsize hall
    exact mutualBlock calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog
      ⟨ms, hcm, hsize, hall, hroute⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys hmod
  · exact recursorBlock calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog
      ⟨ms, hcm, hpos, hall⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys

/-- **The step of a standalone recursor record whose check found no native parent, from its
two parts.** At a validating walk the check of the record finds, at every environment the
step is asked at, the parent heading the major premise, a stored former that the circuit
dispatched natively, unless the head of the major premise is a reserved basis name
(`recParent_of_arm_tied`): a recursor of a mutual or nested family is refused. So what is left
is the record whose major premise is headed by a basis name, and the walk at the assumed
limit. -/
theorem recursorWithoutNativeParent_of_parts
    (majorAtBasisName :
      WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
        fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
          ¬ RecMajorNotBasis t E₀ A c rc → UnitStep.{u} (X t E) t envT E₀ E lim A c)
    (atAssumedLimit :
      WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
        fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc → lim = none →
          ¬ (∀ env, StepAt.{u} t envT E₀ E lim A c env →
              ∃ P ip, RecParent t E env P ip ∧ RecMajorTie t E₀ A c rc P) →
          UnitStep.{u} (X t E) t envT E₀ E lim A c) :
    WalkedUnit.{u} (fun _ _ _ _ c => ∃ rc : Ixon.Recursor, c.info = .recr rc)
      fun _ t envT E₀ E lim A c => ∀ rc : Ixon.Recursor, c.info = .recr rc →
        ¬ (∀ env, StepAt.{u} t envT E₀ E lim A c env →
            ∃ P ip, RecParent t E env P ip ∧ RecMajorTie t E₀ A c rc P) →
        UnitStep.{u} (X t E) t envT E₀ E lim A c := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys rc hinfo hneg
  rcases hW.topLim with hl | hl
  · by_cases hres : RecMajorNotBasis t E₀ A c rc
    · exfalso
      subst hl
      exact hneg fun env hstep =>
        recParent_of_arm_tied ht hS hst hc hinfo rfl (hW.nativeRecArm hT hc hinfo) hinert
          hcover hres env hstep
    · exact majorAtBasisName calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc
        hlog hkind ht hS hcov hst hcanon hinert hcover hchk hns hkeys rc hinfo hres
  · exact atAssumedLimit calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog
      hkind ht hS hcov hst hcanon hinert hcover hchk hns hkeys rc hinfo hl hneg


/-! ## The line-up with the family graph's units -/

/-- **An empty block has no constant address.** -/
theorem constAddrOf_emptyBlock {A x : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hc : c.info = .muts ms) (h0 : ms.size = 0) :
    ¬ ConstAddrOf A c x := by
  intro hx
  rcases hx with ⟨-, hs⟩ | ⟨ms', i, m, hms, hm, -⟩
  · rcases hs with ⟨d, hd⟩ | ⟨rc, hr⟩ | ⟨ax, ha⟩ | ⟨q, hq⟩
    · rw [hc] at hd
      cases hd
    · rw [hc] at hr
      cases hr
    · rw [hc] at ha
      cases ha
    · rw [hc] at hq
      cases hq
  · have e : ms = ms' := Ixon.ConstantInfo.muts.inj (hc.symm.trans hms)
    subst e
    have := (Array.getElem?_eq_some_iff.mp hm).1
    omega

/-- **An empty block is no unit of the family graph**: a unit has a constant address. -/
theorem not_isUnit_emptyBlock {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon}
    {E₀ : Ixon.Env} {Top Inner : _root_.Address → Prop}
    {fam : _root_.Address → Option _root_.Address} {A : _root_.Address} {c : Ixon.Constant}
    {ms : Array Ixon.MutConst} (hrec : recordOf E₀ A = some c) (hc : c.info = .muts ms)
    (h0 : ms.size = 0) : ¬ IsUnit t envT E₀ Top Inner fam A := by
  rintro ⟨-, -, c', hc', -, x, hx, -⟩
  have e : c' = c := Option.some.inj (hc'.symm.trans hrec)
  rw [e] at hx
  exact constAddrOf_emptyBlock hc h0 hx

/-- **A fact about the units of a kind, split by whether the family graph gives the block a
family record.** A modeled block whose only accepted family record is empty has none
(`FamilyGraph.famRecord` excludes empty recursor blocks): it is the second case, whose step
installs the block's own constants and no recursor. -/
theorem walkedUnit_byFamilyRecord (fam : _root_.Address → Option _root_.Address)
    {Kind : List (Call F) → Ix.Kernel.RoleTable → Ixon.Env → _root_.Address → Ixon.Constant →
      Prop}
    {Goal : List (Call F) → Ix.Kernel.RoleTable → Ix.Kernel.Env .anon → Ixon.Env → Ixon.Env →
      Option Nat → _root_.Address → Ixon.Constant → Prop}
    (withFamilyRecord :
      WalkedUnit.{u} (fun calls t E₀ B cb => Kind calls t E₀ B cb ∧ ∃ rb, fam B = some rb) Goal)
    (withoutFamilyRecord :
      WalkedUnit.{u} (fun calls t E₀ B cb => Kind calls t E₀ B cb ∧ fam B = none) Goal) :
    WalkedUnit.{u} Kind Goal := by
  intro calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc hlog hkind ht hS hcov
    hst hcanon hinert hcover hchk hns hkeys
  cases hf : fam A with
  | none =>
    exact withoutFamilyRecord calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc
      hlog ⟨hkind, hf⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys
  | some rb =>
    exact withFamilyRecord calls bAddr t seeds E₀ lim Top rank hW hG R envT E hctx A c hT hc
      hlog ⟨hkind, rb, hf⟩ ht hS hcov hst hcanon hinert hcover hchk hns hkeys

end IxVM.Refinement.Endpoint
