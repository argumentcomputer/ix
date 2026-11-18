import IxVMRefinement.Binding.RunStepStores
import IxVMRefinement.FamilyAlias.ClosureStep
import IxVMRefinement.Binding.ClosureRoute
import IxVMRefinement.Binding.ClosureFold

/-! # The modeled route of a block, from its route over a store of the run

`ClosureRunFacts.routeNew` starts from a block the closure's store routes as modeled
(`Route.blockRoute R₁ B = some true`) and asks for its selected family record, which
`runFamOf` selects only on the run's modeled route (`ModeledRouteAt calls B`: every observation
of `KernelModeled::block_is_modeled` on the block answers non-zero). Two facts connect them:

* `blockRoute_closureStore_new`: at a block new in the group, the closure's store routes as the
  store after the group does. The two differ only at the records of the group's role units, a
  definition or an axiom record each (`roleUnitForm`), which no new record uses (`unitsLast`) and
  which are no projection record of a block.
* `modeledRouteAt_of_blockRoute`: a block a used-closed store within the run's records routes as
  modeled is on the run's modeled route. The run is good for a record store holding that store's
  records (`RunStepStores`), and every observed dispatch answers that store's route
  (`Route.block_is_modeled_agrees`), which is the store's (`FamilyAlias.blockRoute_recordsFor`).
-/

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option linter.unusedVariables false

/-- **At an address held before the group, or no role unit's, the closure's store holds the entry
of the store after the group.** -/
theorem consts_closureStore_eq {t : Ix.Kernel.RoleTable} {g : Nat} {R R' R₁ : Ixon.Env}
    (hR₁ : ClosureStore t g R R' R₁) {a : _root_.Address}
    (ha : (R.consts.get? a).isSome = true ∨ ¬ RoleUnitAt t g a) :
    R₁.consts.get? a = R'.consts.get? a := by
  cases h1 : R₁.consts.get? a with
  | some lc => exact (hR₁.le₂.1 a lc h1).symm
  | none =>
    cases h' : R'.consts.get? a with
    | none => rfl
    | some lc' =>
      exfalso
      rcases ha with hR | hnu
      · obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp hR
        rw [hR₁.le₁.1 a lc hlc] at h1
        cases h1
      · exact hnu (hR₁.units a (by rw [h']; rfl) h1)

theorem recordOf_closureStore_eq {t : Ix.Kernel.RoleTable} {g : Nat} {R R' R₁ : Ixon.Env}
    (hR₁ : ClosureStore t g R R' R₁) {a : _root_.Address}
    (ha : (R.consts.get? a).isSome = true ∨ ¬ RoleUnitAt t g a) :
    recordOf R₁ a = recordOf R' a := by
  unfold recordOf
  rw [consts_closureStore_eq hR₁ ha]

/-- **At a block new in the group, the closure's store routes as the store after the group**
(module docstring). -/
theorem blockRoute_closureStore_new {t : Ix.Kernel.RoleTable} {g : Nat} {R R' R₁ : Ixon.Env}
    (hR₁ : ClosureStore t g R R' R₁) (hcl' : UsedClosed R')
    (hunits : ∀ x a, New R R' x → UsedRef R' x a → ¬ RoleUnitAt t g a)
    (hform : ∀ a c, RoleUnitAt t g a → New R R' a → recordOf R' a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax)
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hnew : New R R' B) (hB : recordOf R' B = some cb) (hms : cb.info = .muts ms) :
    Route.blockRoute R₁ B = Route.blockRoute R' B := by
  have hnotUnit : ∀ a c, recordOf R' a = some c → (∀ d, c.info ≠ .defn d) →
      (∀ ax, c.info ≠ .axio ax) → (R.consts.get? a).isSome = true ∨ ¬ RoleUnitAt t g a := by
    intro a c hc hd hax
    by_cases hR : (R.consts.get? a).isSome = true
    · exact Or.inl hR
    · refine Or.inr fun hu => ?_
      have hRn : R.consts.get? a = none := by
        cases h : R.consts.get? a with
        | none => rfl
        | some lc => rw [h] at hR; exact absurd rfl hR
      have hnewa : New R R' a := ⟨by rw [hc]; rfl, by unfold recordOf; rw [hRn]; rfl⟩
      rcases hform a c hu hnewa hc with ⟨d, hd'⟩ | ⟨ax, hax'⟩
      · exact hd d hd'
      · exact hax ax hax'
  have hB₁ : recordOf R₁ B = some cb := by
    rw [recordOf_closureStore_eq hR₁ (hnotUnit B cb hB (fun d h => by rw [hms] at h; cases h)
      (fun ax h => by rw [hms] at h; cases h))]
    exact hB
  refine blockRoute_congr hB hB₁ (fun a ha => ?_)
  unfold Route.isIndAt
  rcases ha with ⟨i, hi, hx⟩ | ⟨ms', i, m, hms', hm, rfl⟩
  · rw [recordOf_closureStore_eq hR₁ (Or.inr (hunits B a hnew ⟨cb, i, hB, hi, hx⟩))]
  · have hP := (hcl'.2 B cb ms' hB hms' i m hm).1
    rw [recordOf_closureStore_eq hR₁ (hnotUnit _ _ hP
      (fun d h => by cases m <;> simp [memberProjection] at h)
      (fun ax h => by cases m <;> simp [memberProjection] at h))]

/-- **A block a used-closed store within the run's records routes as modeled is on the run's
modeled route** (module docstring). -/
theorem modeledRouteAt_of_blockRoute {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ R : Ixon.Env} (hstep : RunStepStores calls t E₀)
    (hRE : ∀ a lr, R.consts.get? a = some lr → E₀.consts.get? a = some lr)
    (hRb : ∀ a b, R.blobs.get? a = some b → E₀.blobs.get? a = some b)
    (hcomm : AgreesCommitted R)
    (hzero : R.consts.get? Ix.HostAdmission.Merkle.padding = none ∧
      R.blobs.get? Ix.HostAdmission.Merkle.padding = none)
    (hcl : UsedClosed R) {B : _root_.Address} {cb : Ixon.Constant}
    (hB : recordOf R B = some cb) (hroute : Route.blockRoute R B = some true) :
    ModeledRouteAt calls B := by
  obtain ⟨Ec, hRec, hst⟩ := hstep R hRE hRb hcomm hzero
  have hrEc : Route.blockRoute Ec B = some true := by
    rw [FamilyAlias.blockRoute_recordsFor hcl hRec hB]
    exact hroute
  intro bp r h h' cs b ev hsub hb hbB
  have g : Core.Good ⟨Ec, Ix.Kernel.Env.empty, t, none⟩ cs :=
    (hst.good Ix.Kernel.Env.empty none).sub hsub
  have hag := Route.block_is_modeled_agrees (E := Ec) g.1 g.2 hb ev
  rw [hbB] at hag
  have hv : r = Route.bit true := hag.value true hrEc
  rw [hv, Route.bit_true]
  intro he
  exact zero_ne_one (Value.field.inj he).symm

end IxVM.Refinement.Binding
