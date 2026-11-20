import IxVMRefinement.Assembly.BlockRoute
import IxVMRefinement.Callees.RouteDispatch

/-! # The dispatch's answer is a function of the store's records

`blockRouteFunctional`: two observations of `KernelModeled::block_is_modeled` at one block,
each bounded and hashing no collision with a store, answer alike where the store holds every
canonical record the first one hashed. Both agree with `Route.blockRoute`, the answer computed
from the store's records (`Route.block_is_modeled_agrees`); coverage of the first makes that
value known.

With it the statements of `Assembly/BlockRoute.lean` hold without a functionality premise:

* `oneTypeBlock_routes`, `modeled_of_offNativeRoute`: a top-walked block of one inductive type
  is native in the run and at the step's store, or modeled in the run and at the step's store;
* `nativeRouteAt_of_nativeObs`, `modeledAt_of_modeledRoute`: one observation in the run fixes
  the route, and the run-level modeled route gives the store-level one;
* `Claim.TopWalkCore.recFamily_native`: the family block of a top-walked standalone recursor
  record is on the native route in the run and at the store.
-/

universe u

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency

/-- **The dispatch's answer is a function of the store's records.** -/
theorem blockRouteFunctional (E : Ixon.Env) : BlockRouteFunctional E := by
  intro bq₁ bq₂ h₁ h₁' h₂ h₂' cs₁ cs₂ bb₁ bb₂ r₁ r₂ ev₁ ev₂ nc₁ bd₁ cov₁ nc₂ bd₂ rep₁ rep₂ heq
  have a₁ := Route.block_is_modeled_agrees nc₁ bd₁ rep₁ ev₁
  have a₂ := Route.block_is_modeled_agrees nc₂ bd₂ rep₂ ev₂
  obtain ⟨v, hv⟩ := a₁.known cov₁
  rw [a₁.value v hv, a₂.value v (by rw [← heq]; exact hv)]

section Route

variable {c : Core.Ctx} {calls : List (Call F)}

/-- **One native observation in the run puts the block on the native route.** -/
theorem nativeRouteAt_of_nativeObs (hg : Core.Good c calls)
    (hcov : Ingress.CanonicalHashCoverage c.E calls) {B : _root_.Address}
    (hobs : Claim.NativeObsAt calls B) : NativeRouteAt calls B :=
  nativeRouteAt_of_obs (blockRouteFunctional c.E) hg hcov hobs

/-- **The run-level modeled route gives the store-level one**, where the run observed the
dispatch on the block. -/
theorem modeledAt_of_modeledRoute (hg : Core.Good c calls)
    (hcov : Ingress.CanonicalHashCoverage c.E calls) {B : _root_.Address}
    (hroute : ModeledRouteAt calls B)
    (hobs : ∃ (bp r : SourceValue F) (h h' : Heap F) (cs : List (Call F)) (b : Bytes.Address),
      ObsFn Core.W "KernelModeled::block_is_modeled" [bp] h r h' cs ∧
      (∀ cl ∈ cs, cl ∈ calls) ∧ Bytes.RepAddressRef Core.addrTy h b bp ∧
      Core.ixAddr b = B) : ModeledAt c.E B :=
  modeledAt_of_route (blockRouteFunctional c.E) hg hcov hroute hobs

end Route

section Blocks

variable {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {lim : Option Nat}

/-- **The two routes of a top-walked block of one inductive type**: native in the run and at
the step's store, or modeled in the run and at the step's store. -/
theorem oneTypeBlock_routes (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hcov : Ingress.CanonicalHashCoverage E calls)
    {ind : Ixon.Inductive} (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : (∃ ms, cb.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t B lim) :
    (NativeRouteAt calls B ∧ NativeAt E B) ∨ (ModeledRouteAt calls B ∧ ModeledAt E B) :=
  oneTypeBlock_route_cases (blockRouteFunctional E) hS hst hcov hrec hchk

/-- **A top-walked block of one inductive type off the native route is on the modeled route**,
in the run and at the step's store. -/
theorem modeled_of_offNativeRoute (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hcov : Ingress.CanonicalHashCoverage E calls)
    {ind : Ixon.Inductive} (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : (∃ ms, cb.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t B lim)
    (hnn : ¬ NativeRouteAt calls B) : ModeledRouteAt calls B ∧ ModeledAt E B :=
  modeled_of_not_nativeRoute (blockRouteFunctional E) hS hst hcov hrec hchk hnn

end Blocks

end IxVM.Refinement.Typing

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- **The family block of a top-walked standalone recursor record is on the native route**, in
the run and at a store the run is good for and that covers it, at every limit. -/
theorem TopWalkCore.recFamily_native {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env}
    {lim : Option Nat} {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    {c : Core.Ctx} (hg : Core.Good c calls) (hcov : Ingress.CanonicalHashCoverage c.E calls)
    (hW : TopWalkCore calls bAddr t seeds E₀ lim Top rank) {A : _root_.Address}
    {c₀ : Ixon.Constant} {rc : Ixon.Recursor}
    (hT : Top A) (hc : recordOf E₀ A = some c₀) (hinfo : c₀.info = .recr rc) :
    ∃ (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      RecFamilyNativeObs calls A B ∧ Typing.NativeRouteAt calls B ∧ Typing.NativeAt c.E B ∧
      recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧
      (ms.toList.filter Specs.Callees.isIndc).length = 1 :=
  hW.recFamily_nativeRoute (Typing.blockRouteFunctional c.E) hg hcov hT hc hinfo

end IxVM.Refinement.Claim
