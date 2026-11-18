import IxVMRefinement.Binding.GroupRank
import IxVMRefinement.Binding.ClosureFold
import IxVMRefinement.Binding.StoreOpOrder
import IxVMRefinement.RoleVal.BoundSafety
import IxVMRefinement.FamilyGraph.ProducersModeled
import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Binding.BasisAt
import IxVMRefinement.Assembly.TypingBasisInv
import IxVMRefinement.StatementRel.StoreInhabit
import IxVMRefinement.Binding.ReadsLocal
import IxVMRefinement.Binding.ReadsLiteralFree
import IxVMRefinement.Binding.RouteModeledRun
import IxVMRefinement.Binding.RootSafety

/-! # The family checks of a binding run, group by group

The run's payload and family selection, and what of the family form's clauses is left.

* `runPayload calls bAddr t`: the payload of the run's family checks: at group `g`, the family
  check of the block at `B` under the context at `valLimit g` names `a` as its family record, an
  advice record or a container recursor.
* `runFamOf`, `runAdv`, `runCont`: the family selection of group `g`: a block new in the group,
  routed as modeled, with a family check at the group's limit, selects the family record of one
  such check; the advice and container recursors of a block are those of its checks.
  `runFamOf_famCall`: the clause `GroupFamilyChecks.famCall` of that selection;
  `modeled_of_run`: the clause `GroupFamilyChecks.modeled` of every run;
  `familyCall_block_nonempty`, `famNonempty_of_run`: the block of a family check is a non-empty
  block of the run's store; `noPinned_of_run`: no constant address of a new record is at a
  pinned basis key; `readsDown_of_run`, `readsDownBasis_of_run`: a reading over the closure's store
  of an address held before the group is a reading over that store.
* `RemainingFamilyClauses calls bAddr t E₀`: what is not proved of the run's family checks, at
  the store sequence with the run's payload. Each field names the source it comes from.
* `families_of_remaining`: the family form's clauses at a group (`ClosureFam` and
  `FamilyAdmits`), for any rank of the group's new records (`GroupRanked`). -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.StoreInhabit (basisStore)

/-- **The payload of a run's family checks** (module docstring). -/
def runPayload (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable) :
    PayloadRel := fun g B a =>
  ∃ rb cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧
    (a = rb ∨ AdviceIn cs a ∨ ContainerRecIn cs a)

/-- **A family check of the block at `B` with the record at `rb` at group `g`'s limit.** -/
def FamCallAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (g : Nat) (B rb : _root_.Address) : Prop :=
  ∃ cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs

open Classical in
/-- **The family selection of group `g`** (module docstring). -/
noncomputable def runFamOf (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat) (B : _root_.Address) :
    Option _root_.Address :=
  if h : New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧ ModeledRouteAt calls B ∧
      ∃ rb, FamCallAt calls bAddr t g B rb then
    some (Classical.choose h.2.2)
  else none

/-- **The advice of a block's family checks at group `g`.** -/
def runAdv (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (g : Nat) (B a : _root_.Address) : Prop :=
  ∃ rb cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧ AdviceIn cs a

/-- **The container recursors of a block's family checks at group `g`.** -/
def runCont (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (g : Nat) (B x : _root_.Address) : Prop :=
  ∃ rb cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧ ContainerRecIn cs x

section Run

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

theorem runFamOf_spec {g : Nat} {B rb : _root_.Address}
    (h : runFamOf calls bAddr t E₀ g B = some rb) :
    New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧
      ModeledRouteAt calls B ∧ FamCallAt calls bAddr t g B rb := by
  unfold runFamOf at h
  split at h
  · rename_i hc
    have e := Option.some.inj h
    subst e
    exact ⟨hc.1, hc.2.1, Classical.choose_spec hc.2.2⟩
  · cases h

/-- The selected record is in the group's payload. -/
theorem runFamOf_payload {g : Nat} {B rb : _root_.Address}
    (h : runFamOf calls bAddr t E₀ g B = some rb) : runPayload calls bAddr t g B rb := by
  obtain ⟨-, -, cs, hcs⟩ := runFamOf_spec h
  exact ⟨rb, cs, hcs, Or.inl rfl⟩

/-- **`GroupFamilyChecks.famCall` of the run's selection.** -/
theorem runFamOf_famCall {g : Nat} :
    ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
          (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧ ModeledRouteAt calls B ∧
      ∃ cs, FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧
        (∀ a, AdviceIn cs a → runAdv calls bAddr t g B a) ∧
        (∀ x, ContainerRecIn cs x → runCont calls bAddr t g B x) := by
  intro B rb h
  obtain ⟨hn, hm, cs, hcs⟩ := runFamOf_spec h
  exact ⟨hn, hm, cs, hcs, fun a ha => ⟨rb, cs, hcs, ha⟩, fun x hx => ⟨rb, cs, hcs, hx⟩⟩

/-- **`GroupFamilyChecks.modeled` of every run**: the check of a member of a new block of
inductive types in Lean's logic on the modeled route, at the group's limit, ran the family check
of the record the block's payload names (`familyCallLim_of_member`: `Ingress::get_ci` returns the
member's inductive with its unsafe flag `0`, the dispatch's non-zero answer refutes
`KernelCheck::check_const`'s native arm, and the modeled arm ends in
`KernelModeled::check_modeled_block`'s `check_family`), so the group's selection has a record for
the block. -/
theorem modeled_of_run (hC : CollisionFreeRun calls E₀) (g : Nat) :
    ∀ B cb (ms : Array Ixon.MutConst),
      New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B →
      recordOf E₀ B = some cb → InLogic cb → cb.info = .muts ms →
      (∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) → ModeledRouteAt calls B →
      (∃ k, k < ms.size ∧ Claim.MemberCheckedLimAt calls bAddr t B ms k (some (valLimit g))) →
      ∃ rb, runFamOf calls bAddr t E₀ g B = some rb := by
  rintro B cb ms hnew hcb hlog hmuts hall hmod ⟨k, -, hk⟩
  obtain ⟨rb, cs, hfc⟩ := familyCallLim_of_member hC.runStore hcb hmuts hlog hall hk hmod
  have h : New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧ ModeledRouteAt calls B ∧
      ∃ rb, FamCallAt calls bAddr t g B rb := ⟨hnew, hmod, rb, cs, hfc⟩
  unfold runFamOf
  rw [dite_eq_left h]
  exact ⟨_, rfl⟩

/-- **The block of an observed family check is a non-empty block of the run's store**:
`KernelModeled::check_family` loads the block's record (`Ingress::load_verified_constant`) in its
one arm, a block (`Muts`), and `KernelModeled::block_nparams` has no arm for an empty member
list. -/
theorem familyCall_block_nonempty (hS : LoadedReads.RunStore calls E₀)
    (hH : LoadedReads.HashedRecordsStored calls E₀) {B rb : _root_.Address} {lim : Option Nat}
    {cs : List (Call F)} (hfc : FamilyCallAtLim calls bAddr t B rb lim cs) :
    ∃ cb ms, recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧ 0 < ms.size := by
  obtain ⟨h, h', rc, xb, xrb, r, -, ⟨b, hb, rfl⟩, -, ev, -, hsub⟩ := hfc
  match Obs.«KernelModeled::check_family».obs ev with
  | .run (m105 := m105) (m501 := m501) (m589 := m589) (m624 := m624) (x_members := x_members)
      (cs511 := cs511) (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev231 := ev231) (ev266 := ev266) (ev309 := ev309) (ev344 := ev344) (ev403 := ev403)
      (ev435 := ev435) (ev465 := ev465) (ev513 := ev513) (ev601 := ev601) (ev634 := ev634)
      (ev664 := ev664) (hc1474 := hc) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. =>
        rw [he33]
        exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have e453 := e0.trans (ev126.heap_extends.trans (ev148.heap_extends.trans
      (ev194.heap_extends.trans (ev231.heap_extends.trans (ev266.heap_extends.trans
      (ev309.heap_extends.trans (ev344.heap_extends.trans (ev403.heap_extends.trans
      (ev435.heap_extends.trans ev465.heap_extends)))))))))
    have hsub511 : ∀ cl ∈ cs511, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨-, bytes, c, hsz, hh, haddr, hex, hde, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded
        (Bytes.repAddressRef_heapMono₂ Core.addrTy e453 hb) ev513
    obtain ⟨lc, hget, -, hlc⟩ := hH ⟨bytes.toArray⟩ c (Core.hashed_mono hsub511 hh)
      (by simpa only [ByteArray.size, List.size_toArray] using hsz) hde hex
    have haddr' : Address.blake3Pure ⟨bytes.toArray⟩ = Core.ixAddr b := haddr
    have hrec : recordOf E₀ (Core.ixAddr b) = some c := by
      rw [hS.recordOf_eq_recordAt]
      unfold Ix.Cert.recordAt
      rw [← haddr', hget]
      exact hlc
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfoRep, -, -, -, -⟩ := cRep
    have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    rw [← hinfo_eq] at hinfoRep
    obtain ⟨ms, hms, hrep⟩ := L1.repConstantInfo_muts_inv hinfoRep
    refine ⟨c, ms, hrec, hms, ?_⟩
    match Obs.«KernelModeled::block_nparams».obs ev664 with
    | .run (ld12 := ld12) .. =>
      have e624 : Heap.Extends m501 m624 := ev601.heap_extends.trans ev634.heap_extends
      obtain ⟨z, zs, hz, -, -⟩ :=
        Lib.rep_cons_of_load (RepLinkedList.mono L1.repMutConst_heapMono₂ e624 hrep) ld12
      have hlen : ms.toList.length = zs.length + 1 := by rw [hz]; rfl
      rw [← Array.length_toList, hlen]
      exact Nat.succ_pos _

/-- **`ClosureRunFacts.famNonempty` of every run**: the selected record's block had a family check
at the group's limit (`runFamOf_spec`), so it is a non-empty block of the run's store
(`familyCall_block_nonempty`). -/
theorem famNonempty_of_run (hC : CollisionFreeRun calls E₀) {g : Nat} :
    ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
      ∃ cb ms, recordOf E₀ B = some cb ∧ cb.info = .muts ms ∧ 0 < ms.size := by
  intro B rb h
  obtain ⟨-, -, cs, hcs⟩ := runFamOf_spec h
  exact familyCall_block_nonempty hC.runStore hC.hashedStored hcs

/-- The route of a block none of whose members is an inductive type is `some false`. -/
private theorem mutsRoute_noIndc {E : Ixon.Env} {B : _root_.Address} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} (h : ms.toList.filter Core.Specs.Callees.isIndc = []) :
    Route.mutsRoute E B cb ms = some false := by
  unfold Route.mutsRoute
  rw [h]
  rfl

/-- **`ClosureRunFacts.routeNew` of every run, from its payload case**: a new block the closure's
store routes as modeled is a block, routed alike by the store after the group
(`blockRoute_closureStore_new`), so it is on the run's modeled route
(`modeledRouteAt_of_blockRoute`). A block the group's walk adds was checked member by member at the
group's limit (a block has no check of its own, `Claim.checked_not_block`); its members are of one
kind (`Claim.check_block_member_kinds_uniform`), inductive types since it routes as modeled, and it
is in Lean's logic, so the group's selection has a record for it (`modeled_of_run`). A block the
walk does not add is reached through the group's payload (`hpay`). -/
theorem routeNew_of_run (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hP : PayloadFacts t E₀ (runPayload calls bAddr t))
    (hstep : RunStepStores calls t E₀) {g : Nat} (hg6 : 6 ≤ g)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hcl' : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) (g + 1)))
    (hunits : ∀ x a, New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) x →
      UsedRef (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) x a → ¬ RoleUnitAt t g a)
    (hform : ∀ a c, RoleUnitAt t g a → New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
      recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax)
    (hlogic : ∀ a c, New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
      recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c → InLogic c)
    (hpay : ∀ B, PayReach t E₀ (runPayload calls bAddr t) g B →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B →
      ModeledRouteAt calls B → ∃ rb, runFamOf calls bAddr t E₀ g B = some rb) :
    ∀ R₁ B, ClosureStore t g (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) R₁ →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B →
      Route.blockRoute R₁ B = some true → ∃ rb, runFamOf calls bAddr t E₀ g B = some rb := by
  intro R₁ B hR₁ hnew hroute
  have h7 : 6 < g + 1 := Nat.lt_succ_of_le hg6
  obtain ⟨c, hcE, hcR', hadd, -⟩ := new_groupStore hb hg6 hnew
  -- the closure's store holds the block's record, which routes as modeled
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, recordOf R₁ B = some c₁ := by
    unfold Route.blockRoute at hroute
    cases h₁ : recordOf R₁ B with
    | none => rw [h₁] at hroute; cases hroute
    | some c₁ => exact ⟨c₁, rfl⟩
  have e : c₁ = c := Option.some.inj ((recordOf_of_loaded hR₁.le₂.1 hc₁).symm.trans hcR')
  subst e
  have hrr : Route.recordRoute R₁ B c₁ = some true := by
    unfold Route.blockRoute at hroute
    rw [hc₁] at hroute
    exact hroute
  obtain ⟨ms, hms⟩ : ∃ ms, c₁.info = .muts ms := by
    by_contra hn
    rw [Route.recordRoute_of_not_muts (fun ms h => hn ⟨ms, h⟩)] at hrr
    cases hrr
  have hmr : Route.mutsRoute R₁ B c₁ ms = some true := by
    unfold Route.recordRoute at hrr
    rw [hms] at hrr
    exact hrr
  have hind : ms.toList.filter Core.Specs.Callees.isIndc ≠ [] := by
    intro h
    rw [mutsRoute_noIndc h] at hmr
    cases hmr
  -- the run's dispatch answers the store's route
  have hrouteR' : Route.blockRoute (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B =
      some true := by
    rw [← blockRoute_closureStore_new hR₁ hcl' hunits hform hnew hcR' hms]
    exact hroute
  have hmod : ModeledRouteAt calls B :=
    modeledRouteAt_of_blockRoute hstep (groupStore_loaded hb (Nat.le_succ_of_le hg6))
      (groupStore_loadedBlobs h7) (groupStore_committed hC hb (Nat.le_succ_of_le hg6))
      (groupStore_zeroFree hC hb h7) hcl' hcR' hrouteR'
  rcases groupAdds_cases hC hax hw hadd with ⟨-, r, -, hra⟩ | ⟨_, -, -, -, p, hp, hproj, -⟩ |
      ⟨_, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpa
  · -- a block the walk adds: every member checked at the group's limit
    have hU : UnitCheckedAt calls bAddr t E₀ B (some (valLimit g)) := by
      rw [← hra]
      exact unitCheckedAt_of_topRec hC.hashedStored r
    have hmem : ∀ k, k < ms.size →
        Claim.MemberCheckedLimAt calls bAddr t B ms k (some (valLimit g)) := by
      rcases hU with h | ⟨c', ms', hc', hms', hk'⟩
      · exact (Claim.checked_not_block hC.runStore hcE hms h).elim
      · rw [Option.some.inj (hc'.symm.trans hcE), hms] at hms'
        have e : ms' = ms := (Ixon.ConstantInfo.muts.inj hms').symm
        rw [e] at hk'
        exact hk'
    have hpos : 0 < ms.size := by
      rcases Nat.eq_zero_or_pos ms.size with h0 | h
      · exfalso
        apply hind
        have hnil : ms.toList = [] :=
          List.eq_nil_of_length_eq_zero (by rw [Array.length_toList]; exact h0)
        rw [hnil]
        rfl
      · exact h
    obtain ⟨xk, rk, h₁, h₂, cs₁, hak, evk, hsubk⟩ :=
      Claim.MemberCheckedLimAt.block_kinds hC.runStore (hmem 0 hpos)
    rcases Claim.check_block_member_kinds_uniform hC.runStore
        ((hC.runStore.recordOf_eq_recordAt B).symm.trans hcE) hms hak evk hsubk with
      hdefs | hinds | hrecs
    · exfalso
      apply hind
      exact List.filter_eq_nil_iff.mpr fun m hm => by
        obtain ⟨d, rfl⟩ := hdefs m hm
        simp [Core.Specs.Callees.isIndc, Core.isIndc]
    · exact modeled_of_run hC g B c₁ ms hnew hcE (hlogic B c₁ hnew hcR') hms hinds hmod
        ⟨0, hpos, hmem 0 hpos⟩
    · exfalso
      apply hind
      exact List.filter_eq_nil_iff.mpr fun m hm => by
        obtain ⟨d, rfl⟩ := hrecs m hm
        simp [Core.Specs.Callees.isIndc, Core.isIndc]
  · have e : p = c₁ := Option.some.inj (hp.symm.trans hcE)
    rw [e] at hproj
    exact (proj_not_block hproj ⟨ms, hms⟩).elim
  · have e : c₂ = c₁ := Option.some.inj (hc₂.symm.trans hcE)
    rw [e, hms] at hinfo
    cases hinfo
  · rcases payAdds_cases hP hpa with ⟨hrB, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · exact hpay B hrB hnew hmod
    · have e : p = c₁ := Option.some.inj (hp.symm.trans hcE)
      rw [e] at hproj
      exact (proj_not_block hproj ⟨ms, hms⟩).elim

end Run

/-- **What is left of `ClosureRunFacts`** at a group: its fields but `famRefs` (the rank's,
`GroupRanked.famRefs`), `advNotUnit` (`advNotUnit_of_run`), `roleUnitForm`
(`roleUnitForm_of_run`), `keptRoles` (`keptRoles_of_run`), `famNonempty`
(`famNonempty_of_run`), `noPinned` (`noPinned_of_run`), `readsDown` (`readsDown_of_run` from
group 7 on, `readsDownBasis_of_run` at the basis group) and `routeNew` (`routeNew_of_run`, with its
payload case `RemainingFamilyClauses.routeNewPay`), which are proved. Each field's source:
* `notInert`, `needOk`, `literals`, `famNotInert`, `famNeedOk`: the producers are in each field's
  docstring (the group's walk; the walk's reference assertions run on the payload's records for
  payload records; the literal roles' validations at or below group 45). -/
structure RunFactsLeft (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) : Prop where
  /-- No reference a plain unit uses is an inert axiom's. Producer: the group's walk.
  `KernelRoles::assert_ref_allowed` admits a reference bound to an inert role whose group is at or
  above the group's validation limit (`Claim.refAllowed_inert`); such a reference is excluded by
  `check_const`'s axiom arm with the inert role's own validation. For the records of the
  group's payload (advice records, container recursors), the circuit asserts nothing of their
  references until the advice and container checks run the walk's reference assertions on them
  (`KernelClaim::assert_safe_used_refs`, `assert_not_block_ref`). -/
  notInert : ∀ A c x, PlainUnitAt t g R R' famOf A c → UsedRef ρ.E₀ A x → ¬ InertAt t x
  /-- Every reference a plain unit uses is one a step needs stored: a record of the run's store,
  no block, in Lean's logic with its block. Producer: the group's walk
  (`KernelClaim::assert_not_block_ref`, `assert_safe_used_refs`); for the records of the group's
  payload, the same assertions once the advice and container checks run them on their records'
  references. -/
  needOk : ∀ A c x, PlainUnitAt t g R R' famOf A c → UsedRef ρ.E₀ A x → NeedOk ρ.E₀ x
  /-- The key of the member of a plain unit that is a block of one inductive type is none of the
  keys of the four literal functions (`String.ofList`, `List.nil`, `List.cons`, `Char.ofNat`), which
  the step of a block whose former is declared at a definition reads apart. Producer: above
  group 45 the four roles' records are held before the group (`Admits.kept` at their groups) and
  the member's projection record is new, so the addresses and keys differ; at or below group 45,
  the four roles' validations (their records are no inductive projection), not proved. -/
  literals : ∀ A c ind, PlainUnitAt t g R R' famOf A c → c.info = .muts #[.indc ind] →
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.stringOfListName ∧
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.listNilName ∧
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.listConsName ∧
    keyOf t (memberAddr A 0 (.indc ind)) ≠ Ix.Kernel.charOfNatName
  /-- No reference the block of a selected family record uses, the block new in the group, is an
  inert axiom's. Producer: the group's walk at the block, a new walked unit checked at the group's
  validation limit (`FamilyAdmits.checked`; the block is claimed by no block):
  `KernelRoles::assert_ref_allowed` admits a reference bound to an inert role whose group is at or
  above the group's validation limit (`Claim.refAllowed_inert`), and such a reference is excluded
  by `KernelCheck::check_const`'s axiom arm with the inert role's own validation, as for
  `notInert`. -/
  famNotInert : ∀ B rb x, famOf B = some rb → New R R' B → UsedRef ρ.E₀ B x → ¬ InertAt t x
  /-- Every reference the block of a selected family record uses, the block new in the group, is
  one a step needs stored: a record of the run's store, no block, in Lean's logic with its block.
  Producer: the group's walk at the block, a new walked unit checked at the group's validation
  limit (`KernelClaim::assert_not_block_ref`, `KernelClaim::assert_safe_used_refs`), as for
  `needOk`. -/
  famNeedOk : ∀ B rb x, famOf B = some rb → New R R' B → UsedRef ρ.E₀ B x → NeedOk ρ.E₀ x

/-- **What is left of the run's family checks**, at the store sequence with the run's payload
(`Rs g` below is `groupStore t E₀ (runPayload calls bAddr t) g`). Status: premises; nothing
proves them of any run. Each field is tagged with its source: today's circuit (not yet specified),
a named change of the circuit source, or unknown.
* `payloadFacts`: the facts the store's clauses need of the payload's records (`PayloadFacts`:
  `KernelModeled::check_family`, `check_advice_record`, `advice_refs_ok`, `check_witness`,
  `check_container_rec`, `container_refs_ok`, `check_recs`). Source: per field, in
  `PayloadFacts`.
* `payloadRanked`: at a group with a payload, a rank of its new records (`GroupRanked`): the
  order has no cycle among them (content addressing, with `check_advice_record`'s refusal of a
  modeled block, of a projection of the modeled block and of a recursor projection,
  `advice_refs_ok`'s earlier advice and witnesses, and `walk_from_block`'s paths in the block's
  dependency closure). Source: today's circuit, with the change of
  `KernelModeled::check_container_rec` that refuses a container recursor naming itself among its
  container block's used references.
* `family`, `claimed`: the fields of `GroupFamilyChecks` but `famCall` (`runFamOf_famCall`) and
  `modeled` (`modeled_of_run`): `check_family` and
  `check_recs` check the record position by position against the flattened block (`family`,
  with a change of `check_recs` that refuses an empty record under a group's validation); a new
  block of recursors is a selected record or a second family record checked by `check_family`
  (`claimed`). Source: `family` the change of `check_family` and
  `check_recs` that takes the family record as the reconstruction of the block's recursors, and
  the change that compares nested pins in `check_recs`; `claimed` the first of these changes.
* `familyFlat`: the field `GroupFamilyChecks.familyFlat`: the selected record's flattened family,
  entry by entry, derived from the block's constructors and read off the record. Source: the
  observations of `KernelModeled::check_family` regenerated with the changed `aux_all_in`
  (`check_nested_aux`: the record's entries, `build_flat_block`, are the derived ones,
  `nested_walk`, in order), with `check_recs` (entry `k` at recursor `k`), at the offset
  `block_elim` computes.
* `familyForm`: the field `GroupFamilyChecks.familyForm`: the selected record's reconstruction
  form. Source: `check_recs`' form state under the group's validation (the reconstruction
  comparison in `canonical_rules_at_pos`), in the regenerated observations of
  `KernelModeled::check_family` and `check_recs`.
* `runFacts`: what is left of `ClosureRunFacts` at the group (`RunFactsLeft`, which names each
  field's source); `famRefs` is the rank's, `advNotUnit`, `roleUnitForm` and `keptRoles` are proved
  (`families_of_remaining`).
* `famNew`: the selected record of a new block is new in the group. Source: unknown (no reading
  of the circuit excludes a family record an earlier group stored).
* `payloadChecked`: a new unit reached through the payload is checked at the group's limit by a
  check of a unit (`KernelClaim::run_check` in `check_advice_record`, `check_container_rec`;
  `KernelClaim::check_muts_all` for an advice block), or is a selected family record of a new
  block (checked by `check_recs`). Source: today's circuit, with the walk's assertions on inner
  references (`assert_safe_used_refs`, `assert_not_block_ref`) added to the advice, container
  and witnessed-reference checks, for what the payload's records reference.
* `routeNewPay`: the payload case of `ClosureRunFacts.routeNew` (`routeNew_of_run` proves the walk's
  case): a new block reached through the group's payload, on the run's modeled route, has a
  family check at the group's limit, so the group's selection has a record for it. Source: today's
  circuit, not specified: an advice block is refused by `KernelModeled::check_advice_record`
  (`block_is_modeled` answers 0 there); a block reached as a projection's block or a used
  reference of a payload record (`PayReach.owner`, `PayReach.ref`) has its family check in the
  check that reached it (`KernelClaim::run_check_transitive` of a witness of kind 0), or lies in
  the closure the group's walk checks (witnesses of kinds 1 and 3). -/
structure RemainingFamilyClauses (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop where
  payloadFacts : PayloadFacts t E₀ (runPayload calls bAddr t)
  payloadRanked : ∀ g, 6 ≤ g → g < 77 → (∃ B a, runPayload calls bAddr t g B a) →
    ∃ rank, GroupRanked t E₀ (runPayload calls bAddr t) g (runFamOf calls bAddr t E₀ g)
      (runAdv calls bAddr t g) (runCont calls bAddr t g) rank
  family : ∀ g, 6 ≤ g → g < 77 → ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
    ∃ cb ms crb rs flat, FamilyOfBlock E₀ B cb ms rb crb rs flat
  familyFlat : ∀ g, 6 ≤ g → g < 77 → ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
    ∃ (cb crb : Ixon.Constant) (ms rs : Array Ixon.MutConst) (es : List FamilyFlat.FlatEntry)
      (off : Nat),
      FamilyOfBlock E₀ B cb ms rb crb rs (es.map FamilyFlat.FlatEntry.addr) ∧
      FamilyFlat.RecordFlat t E₀ rb crb rs es ∧ FamilyFlat.BlockDerivedFlat t E₀ B off es
  familyForm : ∀ g, 6 ≤ g → g < 77 → ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
    FamilyRecon.RFormS t E₀ B rb
  claimed : ∀ g, 6 ≤ g → g < 77 → ∀ (A : _root_.Address) (c : Ixon.Constant)
    (rs' : Array Ixon.MutConst),
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) A →
    recordOf E₀ A = some c → c.info = .muts rs' → 0 < rs'.size →
    (∀ m ∈ rs'.toList, ∃ r, m = Ixon.MutConst.recr r) →
    (∃ B, runFamOf calls bAddr t E₀ g B = some A) ∨
      ∃ B cs, FamilyCallAtLim calls bAddr t B A (some (valLimit g)) cs
  runFacts : ∀ g, 6 ≤ g → g < 77 → ∀ rk : Nat → _root_.Address → Nat,
    RunFactsLeft (observedRun calls bAddr t E₀ rk) t g
      (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g)
      (runAdv calls bAddr t g)
  famNew : ∀ g, 6 ≤ g → g < 77 → ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) rb
  payloadChecked : ∀ g, 6 ≤ g → g < 77 → ∀ a c,
    PayReach t E₀ (runPayload calls bAddr t) g a →
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
    recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c → UnitKind c →
    UnitCheckedAt calls bAddr t E₀ a (some (valLimit g)) ∨
      ∃ B, runFamOf calls bAddr t E₀ g B = some a ∧
        New (groupStore t E₀ (runPayload calls bAddr t) g)
          (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B
  routeNewPay : ∀ g, 6 ≤ g → g < 77 → ∀ B,
    PayReach t E₀ (runPayload calls bAddr t) g B →
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B →
    ModeledRouteAt calls B → ∃ rb, runFamOf calls bAddr t E₀ g B = some rb

section Families

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **An address the family check of a selected block names is reached through the payload**: the
selected block is a block record (`FamilyOfBlock.block`), so the group reaches it by its walk or
through its payload. -/
theorem runPayload_reach (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀) {g : Nat}
    (hg6 : 6 ≤ g) (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {B rb a : _root_.Address}
    (hfam : runFamOf calls bAddr t E₀ g B = some rb)
    (hpay : runPayload calls bAddr t g B a) :
    PayReach t E₀ (runPayload calls bAddr t) g a := by
  have hP := hR.payloadFacts
  obtain ⟨hnew, -, -⟩ := runFamOf_spec hfam
  obtain ⟨-, -, -, hadd, -⟩ := new_groupStore hb hg6 hnew
  obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hR.family g hg6 hg B rb hfam
  have hB := hF.block
  rcases groupAdds_cases hC hax hw hadd with ⟨hra, -⟩ | ⟨-, -, -, -, p, hp, hproj, -⟩ |
      ⟨-, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpa
  · exact PayReach.payload hra hpay
  · have e : p = cb := Option.some.inj (hp.symm.trans hB.record)
    rw [e] at hproj
    exact (proj_not_block hproj ⟨ms, hB.muts⟩).elim
  · have e : c₂ = cb := Option.some.inj (hc₂.symm.trans hB.record)
    rw [e, hB.muts] at hinfo
    cases hinfo
  · rcases payAdds_cases hP hpa with ⟨hrB, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · exact PayReach.payloadOf hrB hpay
    · have e : p = cb := Option.some.inj (hp.symm.trans hB.record)
      rw [e] at hproj
      exact (proj_not_block hproj ⟨ms, hB.muts⟩).elim

/-- **An address the family check of a selected block names is held after the group**
(`runPayload_reach`). -/
theorem runPayload_held (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀) {g : Nat}
    (hg6 : 6 ≤ g) (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) {B rb a : _root_.Address}
    (hfam : runFamOf calls bAddr t E₀ g B = some rb)
    (hpay : runPayload calls bAddr t g B a) :
    (recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a).isSome = true := by
  have hreach := runPayload_reach hC hb hax hR hg6 hg hw hfam hpay
  obtain ⟨c, hc⟩ := hR.payloadFacts.record g a hreach
  rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
    ⟨storedBelow_of_adds hg6 (GroupAdds.payReach hreach), hc⟩]
  rfl

/-- **`ClosureRunFacts.roleUnitForm` of every run**: the record of an operation is a definition
(`validate_role_op_obs`: `validate_op` asserts a standalone definition), and the record of a
standard axiom an axiom record (`AxiomRolesDeclared`). -/
theorem roleUnitForm_of_run (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hcheck : t.check = .ok ()) {Pay : PayloadRel} {g : Nat}
    (hg6 : 6 ≤ g) (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r) :
    ∀ a c, RoleUnitAt t g a → New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) a →
      recordOf (groupStore t E₀ Pay (g + 1)) a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax := by
  rintro a c ⟨r, hr, had, hk⟩ - hc
  have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc).2
  rcases hk with hop | hs
  · obtain ⟨a₁, c₁, d, had₁, hc₁, hd, -⟩ :=
      validate_role_op_obs hcheck hC.runStore hC.hashedStored
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr) hop
    have ea : a₁ = a := Option.some.inj (had₁.symm.trans had)
    rw [ea, hE] at hc₁
    left
    refine ⟨d, ?_⟩
    rw [Option.some.inj hc₁]
    exact hd
  · obtain ⟨c₂, ax, hc₂, hi, -⟩ := hax r hs a had
    right
    refine ⟨ax, ?_⟩
    rw [Option.some.inj (hE.symm.trans hc₂)]
    exact hi

/-- **`ClosureRunFacts.advNotUnit` of every run**, given the order of the records the payload
reaches: an advice record of a selected block's family check is reached through the payload
(`runPayload_reach`), so it is no operation of the group (`OpEarlier`) and no axiom record
(`PayloadFacts.notAxiomLike`). -/
theorem advNotUnit_of_run (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀) {g : Nat}
    (hg6 : 6 ≤ g) (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hpay : ∀ x, PayReach t E₀ (runPayload calls bAddr t) g x → OpEarlier t g x) :
    ∀ B rb a, runFamOf calls bAddr t E₀ g B = some rb → runAdv calls bAddr t g B a →
      ¬ (RoleUnitAt t g a ∧ New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a) := by
  rintro B rb a hfam ⟨rb', cs, hcs, hin⟩ ⟨⟨r, hr, had, hk⟩, hnew⟩
  have hreach := runPayload_reach hC hb hax hR hg6 hg hw hfam ⟨rb', cs, hcs, Or.inr (Or.inl hin)⟩
  rcases hk with hop | hs
  · have h1 := hpay a hreach r had hop
    rw [groupOf_of_mem_roleGroup hr] at h1
    exact Nat.lt_irrefl g h1
  · obtain ⟨c, ax, hc, hi, -⟩ := hax r hs a had
    exact hR.payloadFacts.notAxiomLike g a c hreach hnew hc (Or.inl ⟨ax, hi⟩)

/-- **`ClosureRunFacts.keptRoles` of every run**: the record of a kept or prelude role of the group
that is no role unit is the record its validation walked (`kept_walked`, `GroupWalked.roots`), so
the store after the group holds it; it is no block record (`Ingress::get_ci` at the bound address,
`RoleVal.ValidateRoleIn.bound_load_safe`, has no arm for a block); it is in Lean's logic with its
block (`RootsSafe.bound`); and it was checked at the group's limit (`unitCheckedAt_of_topRec`). -/
theorem keptRoles_of_run (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hroots : RootsSafe t E₀) {Pay : PayloadRel} {rk : Nat → _root_.Address → Nat} {g : Nat}
    (hg6 : 6 ≤ g) (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs) :
    ∀ r ∈ roleGroup g, (keptRole r ∨ r ∈ preludeRoles) →
      ¬ (r ∈ RoleOps.opRoles ∨ r ∈ standardAxioms) → ∀ a, t.addressOf? r = some a →
      ∃ c, recordOf (groupStore t E₀ Pay (g + 1)) a = some c ∧ (∀ ms, c.info ≠ .muts ms) ∧
        InLogic c ∧
        (∀ cb, recordOf (groupStore t E₀ Pay (g + 1)) (Ix.Cert.ownerOf a c) = some cb →
          InLogic cb) ∧
        ((recordOf (groupStore t E₀ Pay g) a).isSome = true →
          ∃ n, (observedRun calls bAddr t E₀ rk).checked a n) := by
  intro r hr hk hnot a had
  have h6 : 6 ≤ g + 1 := Nat.le_succ_of_le hg6
  have hgr : 6 ≤ Ix.SpecDigest.groupOf r := by
    rw [groupOf_of_mem_roleGroup hr]
    exact hg6
  have hwk : RoleVal.roleWalksBound r = true ∨ RoleVal.anchorWalked r = true := by
    rcases kept_walked hgr hk with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (Or.inr h) hnot
  obtain ⟨x, hx, hxa⟩ := hw.roots r hr hwk a had
  have hE : recordOf E₀ a = some x.c := by
    rw [← hxa]
    exact topRec_recordOf hC.hashedStored x
  have hsafe := hroots.bound r hwk a had
  refine ⟨x.c, (groupStore_recordOf hb h6).mpr
    ⟨storedBelow_of_adds hg6 (GroupAdds.reach (GroupReach.root hr hwk had)), hE⟩, ?_,
    (hsafe x.c hE).1, fun cb hcb => (hsafe x.c hE).2 cb ((groupStore_recordOf hb h6).mp hcb).2,
    fun _ => ⟨valLimit g, ?_⟩⟩
  · intro ms hms
    obtain ⟨a', had', h₀, h₁, ap, ptr, v, cs, ha, ev, hsub, -, -⟩ :=
      RoleVal.ValidateRoleIn.bound_load_safe
        (show RoleVal.ValidateRoleIn calls bAddr t g r from hval r hr)
        (RoleVal.roleSpecKind_of_walked r hwk)
    have e : a' = a := Option.some.inj (had'.symm.trans had)
    rw [e] at ha
    obtain ⟨ab, hab, hab'⟩ := ha
    rw [← hab'] at hE
    obtain ⟨raw, c', -, hh, hba, hx', -, hhead⟩ := Claim.get_ci_head hab ev
    have hcc : c' = x.c := hC.runStore.record_eq
      ((hC.runStore.recordOf_eq_recordAt _).symm.trans hE) (Core.hashed_mono hsub hh) hba hx'
    rw [hcc] at hhead
    exact hhead.notMuts ms hms
  · show UnitCheckedAt calls bAddr t E₀ a (some (valLimit g))
    rw [← hxa]
    exact unitCheckedAt_of_topRec hC.hashedStored x

set_option maxRecDepth 100000 in
/-- The names of the pinned basis constants are keys of basis roles. -/
private theorem pinned_names_basis (kind : Ix.Kernel.BasisKind) :
    ∀ n ∈ (kind.declsA (md := .anon)).map (·.name),
      n ∈ TableInhabit.basisRoleOrder.map Ix.Kernel.Key.role := by
  cases kind <;> decide +kernel

/-- A basis row is a record of the run's store, at an address the basis store holds. -/
private theorem basis_row_run (hb : BasisRowsLoaded E₀) {y : _root_.Address}
    {cy : Ixon.Constant} (h : recordOf basisStore y = some cy) :
    (basisStore.consts.get? y).isSome = true ∧ recordOf E₀ y = some cy := by
  unfold recordOf at h ⊢
  cases hg : basisStore.consts.get? y with
  | none => rw [hg] at h; cases h
  | some lc =>
    rw [hg] at h
    rw [hb y lc hg]
    exact ⟨rfl, h⟩

/-- **`ClosureRunFacts.noPinned` of every run**: the name of a pinned basis constant is the key of
a basis role (`pinned_names_basis`), so a constant address at that key is the address the table
binds the role to, which a table pinning the prelude binds to a basis row (`addressOf_basis`,
`basisRoles_rows`). A basis row is held before the group, so it is no new record's own address;
and it is no member's or constructor's address of a new block, since the basis store holds the
block of each of its projection records (`StoreInhabit.store_usedClosed`). -/
theorem noPinned_of_run (hb : BasisRowsLoaded E₀) (hpin : PreludePinned t)
    (hcheck : t.check = .ok ()) {Pay : PayloadRel} {g : Nat} (hg6 : 6 ≤ g)
    (hcl : UsedClosed (groupStore t E₀ Pay (g + 1))) :
    ∀ A c x ci, New (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) A →
      recordOf (groupStore t E₀ Pay (g + 1)) A = some c → ConstAddrOf A c x →
      PinnedBasis ci → ci.name ≠ keyOf t x := by
  intro A c x ci hnew hc hx ⟨kind, hci⟩ hk
  obtain ⟨r, hr, hrk⟩ : ∃ r ∈ TableInhabit.basisRoleOrder, ci.name = .role r := by
    obtain ⟨r, hr, he⟩ :=
      List.mem_map.mp (pinned_names_basis kind ci.name (List.mem_map.mpr ⟨ci, hci, rfl⟩))
    exact ⟨r, hr, he.symm⟩
  rw [hrk] at hk
  have had : t.addressOf? r = some x :=
    Core.addressOf_of_keyOf (wf_of_check hcheck) (by rw [LoadedReads.keyOf_eq]; exact hk.symm)
  have hrows := List.all_eq_true.mp basisRoles_rows r hr
  simp only [← addressOf_basis hpin hr, had] at hrows
  have hxb : (recordOf basisStore x).isSome = true := StoreInhabit.isSome_of_hasKey hrows
  obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp hxb
  have hA : (recordOf basisStore A).isSome = true := by
    rcases hx with ⟨rfl, -⟩ | ⟨ms, i, m, hms, hm, hxm⟩
    · exact hxb
    · obtain ⟨p, hp, hown⟩ : ∃ p, recordOf (groupStore t E₀ Pay (g + 1)) x = some p ∧
          Ix.Cert.ownerOf x p = A := by
        obtain ⟨h1, h2⟩ := hcl.2 A c ms hc hms i m hm
        rcases hxm with rfl | ⟨ind, j, rfl, hj, rfl⟩
        · exact ⟨_, h1, ownerOf_memberProjection _ _ _ _⟩
        · exact ⟨_, h2 ind rfl j hj, ownerOf_constructorProjection _ _ _ _⟩
      have hpE : recordOf E₀ x = some p :=
        ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hp).2
      have e : cx = p := Option.some.inj ((basis_row_run hb hcx).2.symm.trans hpE)
      subst e
      have hown' := (StoreInhabit.store_usedClosed.1 x cx hcx).1
      rw [hown] at hown'
      exact hown'
  obtain ⟨cA, hcA⟩ := Option.isSome_iff_exists.mp hA
  obtain ⟨hkA, hEA⟩ := basis_row_run hb hcA
  have hheld := (groupStore_recordOf (t := t) (Pay := Pay) hb hg6).mpr ⟨Or.inl hkA, hEA⟩
  rw [hnew.2] at hheld
  cases hheld

/-- **`ClosureRunFacts.readsDown` of every run, from group 7 on**: the store before the group is
used-closed and, from group 7 on, holds every blob of the run, which the closure's store holds no
more of; and the closure's store extends it. A reading over the closure's store at an address the
store before the group holds is then a reading over that store (`reads_of_closed_sub`). -/
theorem readsDown_of_run (hcheck : t.check = .ok ()) {Pay : PayloadRel} {g : Nat} (hg : 6 < g)
    (hcl : UsedClosed (groupStore t E₀ Pay g)) :
    ∀ R₁ x ci₀,
      ClosureStore t g (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) R₁ →
      (recordOf (groupStore t E₀ Pay g) x).isSome = true →
      IxVM.Consistency.Reads t R₁ x ci₀ →
      IxVM.Consistency.Reads t (groupStore t E₀ Pay g) x ci₀ := by
  intro R₁ x ci₀ hR₁ hx hr
  refine reads_of_closed_sub hcheck (wf_of_check hcheck) ?_ hcl ?_ hx hr
  · intro y c hy
    unfold recordOf at hy ⊢
    cases hgy : (groupStore t E₀ Pay g).consts.get? y with
    | none => rw [hgy] at hy; cases hy
    | some lc =>
      rw [hgy] at hy
      rw [hR₁.le₁.1 y lc hgy]
      exact hy
  · intro y b hy
    exact groupStore_reads_blobs hg y b
      (groupStore_loadedBlobs (Nat.lt_succ_of_lt hg) y b (hR₁.le₂.2 y b hy))

/-- **`ClosureRunFacts.readsDown` of every run at the basis group**: the store before group 6 is
the basis store, which is used-closed (`StoreInhabit.store_usedClosed`) and which the closure's
store extends. So a reading over the closure's store at a basis row is a reading over the basis
rows with the closure's blobs (`reads_of_closed_sub`, at the basis store's records with the
closure's blobs). The basis store holds no blob, but no basis row has a literal
(`basisStore_litFree`, decided over the 24 rows), so the reading looks up no blob and is one over
the basis store itself (`readsIn_litFree`). -/
theorem readsDownBasis_of_run (hcheck : t.check = .ok ()) {Pay : PayloadRel} {g : Nat}
    (hg : g = 6) :
    ∀ R₁ x ci₀,
      ClosureStore t g (groupStore t E₀ Pay g) (groupStore t E₀ Pay (g + 1)) R₁ →
      (recordOf (groupStore t E₀ Pay g) x).isSome = true →
      IxVM.Consistency.Reads t R₁ x ci₀ →
      IxVM.Consistency.Reads t (groupStore t E₀ Pay g) x ci₀ := by
  subst hg
  intro R₁ x ci₀ hR₁ hx hr
  have hsub : ∀ y c, recordOf basisStore y = some c → recordOf R₁ y = some c := by
    intro y c hy
    unfold recordOf at hy ⊢
    cases hgy : basisStore.consts.get? y with
    | none => rw [hgy] at hy; cases hy
    | some lc =>
      rw [hgy] at hy
      rw [hR₁.le₁.1 y lc ((groupStore_basis_consts y).trans hgy)]
      exact hy
  rw [groupStore_six] at hx ⊢
  have h1 : IxVM.Consistency.ReadsIn t (recordOf basisStore) (fun y => R₁.blobs.get? y) x ci₀ :=
    reads_of_closed_sub (R := { basisStore with blobs := R₁.blobs }) (E₀ := R₁) hcheck
      (wf_of_check hcheck) hsub StoreInhabit.store_usedClosed (fun _ _ h => h) hx hr
  exact readsIn_litFree (fun _ _ h => basisStore_litFree h) h1

/-- **The family form's clauses at a group**, for a rank of its new records: `ClosureRunFacts`
from what is left of it (`RemainingFamilyClauses.runFacts`), the rank's `famRefs`, and
`advNotUnit`, `roleUnitForm`, `keptRoles`, `famNonempty`, `noPinned`, `readsDown` and `routeNew`
(with its payload case) proved of the run;
`GroupFamilyChecks.modeled` and `famCall` proved of the run. -/
theorem families_of_remaining (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀)
    (hcheck : t.check = .ok ()) (hroots : RootsSafe t E₀) (hpin : PreludePinned t)
    {rk : Nat → _root_.Address → Nat} {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77)
    (hval : ∀ r ∈ roleGroup g, RoleValidationIn calls bAddr t g r)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hrank : GroupRanked t E₀ (runPayload calls bAddr t) g (runFamOf calls bAddr t E₀ g)
      (runAdv calls bAddr t g) (runCont calls bAddr t g) (rk g))
    (hpay : ∀ x, PayReach t E₀ (runPayload calls bAddr t) g x → OpEarlier t g x)
    (hclg : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) g))
    (hcl : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) (g + 1)))
    (hstep : RunStepStores calls t E₀)
    (hunits : ∀ x a, New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) x →
      UsedRef (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) x a → ¬ RoleUnitAt t g a)
    (hlogic : ∀ a c, New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
      recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c → InLogic c) :
    ClosureFam calls (observedRun calls bAddr t E₀ rk) t g
        (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g)
        (runAdv calls bAddr t g) (runCont calls bAddr t g) ∧
      FamilyAdmits (observedRun calls bAddr t E₀ rk) t g
        (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g)
        (runAdv calls bAddr t g) (runCont calls bAddr t g) := by
  have hL := hR.runFacts g hg6 hg rk
  refine ⟨⟨⟨bAddr, ?_⟩, ?_⟩, ?_⟩
  · exact
      { modeled := modeled_of_run hC g
        famCall := runFamOf_famCall
        family := hR.family g hg6 hg
        familyFlat := hR.familyFlat g hg6 hg
        familyForm := hR.familyForm g hg6 hg
        claimed := hR.claimed g hg6 hg }
  · exact
      { famRefs := hrank.famRefs
        famNonempty := famNonempty_of_run hC
        advNotUnit := advNotUnit_of_run hC hb hax hR hg6 hg hw hpay
        noPinned := noPinned_of_run hb hpin hcheck hg6 hcl
        roleUnitForm := roleUnitForm_of_run hC hb hax hcheck hg6 hval
        keptRoles := keptRoles_of_run hC hb hroots hg6 hval hw
        routeNew := routeNew_of_run hC hb hax hR.payloadFacts hstep hg6 hw hcl hunits
          (roleUnitForm_of_run hC hb hax hcheck hg6 hval) hlogic (hR.routeNewPay g hg6 hg)
        readsDown := by
          rcases Nat.lt_or_ge 6 g with h7 | h6
          · exact readsDown_of_run hcheck h7 hclg
          · exact readsDownBasis_of_run hcheck (Nat.le_antisymm h6 hg6)
        notInert := hL.notInert
        needOk := hL.needOk
        literals := hL.literals
        famNotInert := hL.famNotInert
        famNeedOk := hL.famNeedOk }
  · exact
      { famNew := fun B rb h hB => ⟨hR.famNew g hg6 hg B rb h, hrank.fam B rb h hB⟩
        advice := fun B rb a h hB ha => by
          obtain ⟨rb', cs, hcs, hin⟩ := ha
          exact ⟨runPayload_held hC hb hax hR hg6 hg hw h ⟨rb', cs, hcs, Or.inr (Or.inl hin)⟩,
            fun hn => hrank.advice B rb a h hB ⟨rb', cs, hcs, hin⟩ hn⟩
        container := fun B rb x h hB hx => by
          obtain ⟨rb', cs, hcs, hin⟩ := hx
          exact ⟨runPayload_held hC hb hax hR hg6 hg hw h ⟨rb', cs, hcs, Or.inr (Or.inr hin)⟩,
            fun hn => hrank.container B rb x h hB ⟨rb', cs, hcs, hin⟩ hn⟩
        checked := fun a c hn hc hu => by
          rcases groupStore_checked hC hb hax hR.payloadFacts hg6 hw a c hn hc hu with h | h
          · exact Or.inl h
          · exact hR.payloadChecked g hg6 hg a c h hn hc hu }

end Families

end IxVM.Refinement.Binding
