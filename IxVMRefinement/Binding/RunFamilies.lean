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
import IxVMRefinement.Binding.PayloadDirect
import IxVMRefinement.Binding.PayloadAdvice
import IxVMRefinement.Binding.PayloadDirectLoads
import IxVMRefinement.Binding.PayloadDirectClosed
import IxVMRefinement.Binding.RunFactsLiterals
import IxVMRefinement.Binding.WalkedRefs
import IxVMRefinement.Binding.PayloadRefSpecs

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
* `PayAdviceAt`, `PayContainerAt`, `PayRecordAt`, `PayloadDirectLeft`, `payloadDirect_of_left`,
  `RemainingFamilyClauses.payload`: the payload's facts at the addresses the family checks name
  directly, from the family checks' own loads (`Binding/PayloadAdvice.lean`,
  `Binding/PayloadDirectLoads.lean`) but an advice projection's member address and a container
  recursor's logic, and the payload's facts from those and the stepped ones
  (`Binding/PayloadDirect.lean`).
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

/-- **The payload of a run's family checks** (module docstring): restricted to blocks routed as
modeled (`ModeledRouteAt`), so `op_order_scan_refs` (which asserts `block_is_modeled = 0`)
directly excludes any payload in the well-founded block. Each check contributes its own family
record, its own advice records (`AdviceListedIn`), and its directly witnessed container recursors
(`DirectContOwn`). -/
def runPayload (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable) :
    PayloadRel := fun g B a =>
  ModeledRouteAt calls B ∧
  ∃ rb cs advAs, FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs ∧
    (a = rb ∨ AdviceListedIn advAs a ∨
      DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs a)

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
  ∃ rb cs advAs, FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs ∧
    AdviceListedIn advAs a

/-- **The container recursors of a block's family checks at group `g`.** -/
def runCont (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (g : Nat) (B x : _root_.Address) : Prop :=
  ∃ rb cs advAs, FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs ∧
    DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs x

/-- **An advice record of a family check of a block group `g` reaches**, at the group's limit
(listed by the check or by an advice walk nested in its calls). -/
def PayAdviceAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (g : Nat) (a : _root_.Address) : Prop :=
  ∃ B rb cs, (GroupReach t E₀ g B ∨ PayReach t E₀ (runPayload calls bAddr t) g B) ∧
    FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧ AdviceIn cs a

/-- **A container recursor of a family check of a block group `g` reaches**, at the group's
limit. -/
def PayContainerAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (g : Nat) (a : _root_.Address) : Prop :=
  ∃ B rb cs, (GroupReach t E₀ g B ∨ PayReach t E₀ (runPayload calls bAddr t) g B) ∧
    FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs ∧ ContainerRecIn cs a

/-- **The family record of a family check of a block group `g` reaches**, at the group's
limit. -/
def PayRecordAt (calls : List (Call F)) (bAddr : _root_.Address) (t : Ix.Kernel.RoleTable)
    (E₀ : Ixon.Env) (g : Nat) (a : _root_.Address) : Prop :=
  ∃ B cs, (GroupReach t E₀ g B ∨ PayReach t E₀ (runPayload calls bAddr t) g B) ∧
    FamilyCallAtLim calls bAddr t B a (some (valLimit g)) cs

/-- An address the run's payload names directly is an advice record, a container recursor or the
family record of a family check of a block the group reaches. -/
theorem payDirect_cases {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {g : Nat} {a : _root_.Address}
    (h : PayDirect t E₀ (runPayload calls bAddr t) g a) :
    PayAdviceAt calls bAddr t E₀ g a ∨ PayContainerAt calls bAddr t E₀ g a ∨
      PayRecordAt calls bAddr t E₀ g a := by
  obtain ⟨B, hB, -, rb, cs, advAs, hex, rfl | ha | ha⟩ := h
  · exact Or.inr (Or.inr ⟨B, cs, hB, hex.toCall⟩)
  · exact Or.inl ⟨B, rb, cs, hB, hex.toCall, adviceListedIn_toAdviceIn hex.toOwn ha⟩
  · exact Or.inr (Or.inl ⟨B, rb, cs, hB, hex.toCall, directContOwn_toContainerRecIn ha⟩)

/-- **What is left of the payload's facts at the addresses the run's family checks name
directly** (`PayDirect`). Both fields are proved of every collision-free run
(`payloadDirect_of_run`, `Binding/PayloadDirectClosed.lean`). -/
structure PayloadDirectLeft (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop where
  projMember : ∀ g a c, PayAdviceAt calls bAddr t E₀ g a → recordOf E₀ a = some c → IsProj c →
    ∃ cb, recordOf E₀ (Ix.Cert.ownerOf a c) = some cb ∧ ConstAddrOf (Ix.Cert.ownerOf a c) cb a
  containerLogic : ∀ g a c, PayContainerAt calls bAddr t E₀ g a → recordOf E₀ a = some c →
    InLogic c

/-- **The remaining direct payload facts hold of every collision-free run**
(`adviceCheck_projMember`, `containerRecIn_logic`). -/
theorem payloadDirect_of_run {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀) :
    PayloadDirectLeft calls bAddr t E₀ where
  projMember := fun _ _ _ ⟨_, _, _, _, hfc, hadv⟩ hc hp =>
    adviceCheck_projMember hC.runStore hC.hashedStored (adviceCheckObs_of_familyCall hfc hadv) hc hp
  containerLogic := fun _ _ _ ⟨_, _, _, _, hfc, hcon⟩ hc =>
    containerRecIn_logic hC.runStore hfc hcon hc

/-- **The payload's facts at the addresses the run's family checks name directly**, from what is
left of them (`PayloadDirectLeft`) and the family checks' own loads. -/
theorem payloadDirect_of_left {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} (hC : CollisionFreeRun calls E₀)
    (h : PayloadDirectLeft calls bAddr t E₀) :
    PayloadFactsOn t E₀ (runPayload calls bAddr t) (PayDirect t E₀ (runPayload calls bAddr t))
    where
  record := fun g a ha => by
    rcases payDirect_cases ha with ⟨B, rb, cs, -, hfc, hadv⟩ | ⟨B, rb, cs, -, hfc, hcon⟩ |
        ⟨B, cs, -, hfc⟩
    · exact adviceIn_record hC.runStore hC.hashedStored hfc hadv
    · exact containerRecIn_record hC.runStore hC.hashedStored hfc hcon
    · obtain ⟨c, hc, -⟩ := familyCall_record_facts hC.runStore hC.hashedStored hfc
      exact ⟨c, hc⟩
  blockMembers := fun g B c ms hB hc hms => by
    rcases payDirect_cases hB with ⟨B', rb, cs, -, hfc, hadv⟩ | ⟨B', rb, cs, -, hfc, hcon⟩ |
        ⟨B', cs, -, hfc⟩
    · exact (adviceCheck_block t hC.runStore hC.hashedStored
        (adviceCheckObs_of_familyCall hfc hadv) hc hms).2
    · exact (containerRecIn_notBlock hC.runStore hfc hcon hc ms hms).elim
    · obtain ⟨c₀, hc₀, -, hshape⟩ := familyCall_record_facts hC.runStore hC.hashedStored hfc
      have e : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
      subst e
      rcases hshape with ⟨rcr, hr⟩ | ⟨ms₀, hms₀, hall, hmem⟩
      · cases hr.symm.trans hms
      · have e' : ms₀ = ms := Ixon.ConstantInfo.muts.inj (hms₀.symm.trans hms)
        subst e'
        intro i m hm
        refine ⟨hmem i m hm, fun ind j hind _ => ?_⟩
        have hmL : ms₀.toList[i]? = some m := by rw [Array.getElem?_toList]; exact hm
        obtain ⟨r, hr⟩ := hall m (List.mem_of_getElem? hmL)
        rw [hind] at hr
        cases hr
  projMember := fun g a c ha hc hp => by
    rcases payDirect_cases ha with hadv | ⟨B, rb, cs, -, hfc, hcon⟩ | ⟨B, cs, -, hfc⟩
    · exact h.projMember g a c hadv hc hp
    · exact containerRecIn_projMember hC.runStore hC.hashedStored hfc hcon hc hp
    · obtain ⟨c₀, hc₀, -, hshape⟩ := familyCall_record_facts hC.runStore hC.hashedStored hfc
      have e : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
      subst e
      exfalso
      rcases hshape with ⟨rcr, hr⟩ | ⟨ms, hms, -, -⟩
      · rcases hp with ⟨_, hq⟩ | ⟨_, hq⟩ | ⟨_, hq⟩ | ⟨_, hq⟩ <;> cases hr.symm.trans hq
      · exact proj_not_block hp ⟨ms, hms⟩
  logic := fun g a c ha hc => by
    rcases payDirect_cases ha with ⟨B, rb, cs, -, hfc, hadv⟩ | hcon | ⟨B, cs, -, hfc⟩
    · exact adviceCheck_logic t hC.runStore hC.hashedStored
        (adviceCheckObs_of_familyCall hfc hadv) hc
    · exact h.containerLogic g a c hcon hc
    · obtain ⟨c₀, hc₀, hl, -⟩ := familyCall_record_facts hC.runStore hC.hashedStored hfc
      rw [← Option.some.inj (hc₀.symm.trans hc)]
      exact hl
  notAxiomLike := fun g a c ha hn hc => by
    rcases payDirect_cases ha with ⟨B, rb, cs, -, hfc, hadv⟩ | ⟨B, rb, cs, -, hfc, hcon⟩ |
        ⟨B, cs, -, hfc⟩
    · exact adviceIn_notAxiomLike hC.runStore hfc hadv hc
    · exact containerRecIn_notAxiomLike hC.runStore hfc hcon hc
    · obtain ⟨c₀, hc₀, -, hshape⟩ := familyCall_record_facts hC.runStore hC.hashedStored hfc
      have e : c₀ = c := Option.some.inj (hc₀.symm.trans hc)
      subst e
      rcases hshape with ⟨rcr, hr⟩ | ⟨ms, hms, -, -⟩
      · rintro (⟨ax, hax⟩ | ⟨q, hq⟩)
        · cases hr.symm.trans hax
        · cases hr.symm.trans hq
      · rintro (⟨ax, hax⟩ | ⟨q, hq⟩)
        · cases hms.symm.trans hax
        · cases hms.symm.trans hq

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
  obtain ⟨-, hmod, cs, hcs⟩ := runFamOf_spec h
  obtain ⟨advAs, hex⟩ := familyCallExact_of_call hcs
  exact ⟨hmod, rb, cs, advAs, hex, Or.inl rfl⟩

/-- **`GroupFamilyChecks.famCall` of the run's selection.** -/
theorem runFamOf_famCall {g : Nat} :
    ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
          (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B ∧ ModeledRouteAt calls B ∧
      ∃ cs advAs, FamilyCallOwn calls bAddr t B rb (some (valLimit g)) cs advAs ∧
        (∀ a, AdviceListedIn advAs a → runAdv calls bAddr t g B a) ∧
        (∀ x, DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs x →
          runCont calls bAddr t g B x) := by
  intro B rb h
  obtain ⟨hn, hm, cs, hcs⟩ := runFamOf_spec h
  obtain ⟨advAs, hex⟩ := familyCallExact_of_call hcs
  exact ⟨hn, hm, cs, advAs, hex.toOwn, fun a ha => ⟨rb, cs, advAs, hex, ha⟩,
    fun x hx => ⟨rb, cs, advAs, hex, hx⟩⟩

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
      (ev_yqjbwijz := evo) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309) (ev344 := ev344)
      (ev403 := ev403) (ev435 := ev435) (ev465 := ev465) (ev513 := ev513) (ev601 := ev601)
      (ev634 := ev634) (ev664 := ev664) (hc1474 := hc) .. =>
    have e0 : Heap.Extends h m105 := by
      match sg112 with
      | .Nil (ev15 := ev15) (he33 := he33) .. =>
        rw [he33]
        exact ev15.heap_extends
      | .Node (heq97 := heq) .. => exact absurd (Value.field.inj heq) zero_ne_one
    have e453 := e0.trans (ev126.heap_extends.trans (ev148.heap_extends.trans
      (ev194.heap_extends.trans (evo.heap_extends.trans (ev231.heap_extends.trans
      (ev266.heap_extends.trans (ev309.heap_extends.trans (ev344.heap_extends.trans
      (ev403.heap_extends.trans (ev435.heap_extends.trans ev465.heap_extends))))))))))
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

/-- **`ClosureRunFacts.routeNew` of every run**: a new block the closure's store routes as modeled
is a block with an inductive member, routed alike by the store after the group
(`blockRoute_closureStore_new`), so it is on the run's modeled route
(`modeledRouteAt_of_blockRoute`). A block checked member by member at the group's limit (a block
has no check of its own, `Claim.checked_not_block`) has members of one kind
(`Claim.check_block_member_kinds_uniform`), inductive types since it routes as modeled, and is in
Lean's logic, so the group's selection has a record for it (`modeled_of_run`). A block the group's
walk adds was so checked; a block the group's payload reaches was so checked or is the family
record of a family check at the group's limit (`hpc`, the run's `payloadChecked` clause), which is
a recursor record or a block of recursors (`familyCall_record_facts`), so no block with an
inductive member. -/
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
    (hpc : ∀ a c, PayReach t E₀ (runPayload calls bAddr t) g a →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
      recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c → UnitKind c →
      ¬ IsTwinShape c →
      UnitCheckedAt calls bAddr t E₀ a (some (valLimit g)) ∨
        ∃ B cs, FamilyCallAtLim calls bAddr t B a (some (valLimit g)) cs) :
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
  -- a block checked member by member at the group's limit had its family check
  have hfromU : UnitCheckedAt calls bAddr t E₀ B (some (valLimit g)) →
      ∃ rb, runFamOf calls bAddr t E₀ g B = some rb := by
    intro hU
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
  rcases groupAdds_cases hC hax hw hadd with ⟨-, r, -, hra⟩ | ⟨_, -, -, -, p, hp, hproj, -⟩ |
      ⟨_, -, -, -, c₂, ax, hc₂, hinfo, -⟩ | hpa
  · -- a block the walk adds: every member checked at the group's limit
    apply hfromU
    rw [← hra]
    exact unitCheckedAt_of_topRec hC.hashedStored r
  · have e : p = c₁ := Option.some.inj (hp.symm.trans hcE)
    rw [e] at hproj
    exact (proj_not_block hproj ⟨ms, hms⟩).elim
  · have e : c₂ = c₁ := Option.some.inj (hc₂.symm.trans hcE)
    rw [e, hms] at hinfo
    cases hinfo
  · rcases payAdds_cases hP hpa with ⟨hrB, -⟩ | ⟨-, -, -, -, -, p, hp, hproj, -⟩
    · -- a block the payload reaches, with an inductive member, so of no twin's shape: checked at
      -- the group's limit, or a family record, which is a recursor record or a block of recursors
      have hntw : ¬ IsTwinShape c₁ := by
        rintro ⟨rs, hrs, -, hrecs⟩
        have e : rs = ms := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hms)
        subst e
        apply hind
        exact List.filter_eq_nil_iff.mpr fun m hm => by
          obtain ⟨d, rfl⟩ := hrecs m hm
          simp [Core.Specs.Callees.isIndc, Core.isIndc]
      rcases hpc B c₁ hrB hnew hcR' (Or.inr (Or.inr ⟨ms, hms⟩)) hntw with hU | ⟨B', cs, hfc⟩
      · exact hfromU hU
      · exfalso
        obtain ⟨c₀, hc₀, -, hshape⟩ := familyCall_record_facts hC.runStore hC.hashedStored hfc
        have e : c₀ = c₁ := Option.some.inj (hc₀.symm.trans hcE)
        subst e
        rcases hshape with ⟨rcr, hr⟩ | ⟨ms₀, hms₀, hall, -⟩
        · cases hr.symm.trans hms
        · have e' : ms₀ = ms := Ixon.ConstantInfo.muts.inj (hms₀.symm.trans hms)
          subst e'
          apply hind
          exact List.filter_eq_nil_iff.mpr fun m hm => by
            obtain ⟨d, rfl⟩ := hall m hm
            simp [Core.Specs.Callees.isIndc, Core.isIndc]
    · have e : p = c₁ := Option.some.inj (hp.symm.trans hcE)
      rw [e] at hproj
      exact (proj_not_block hproj ⟨ms, hms⟩).elim

end Run

/-- **What is left of `ClosureRunFacts`** at a group: its fields but `famRefs` (the rank's,
`GroupRanked.famRefs`), `advNotUnit` (`advNotUnit_of_run`), `roleUnitForm`
(`roleUnitForm_of_run`), `keptRoles` (`keptRoles_of_run`), `famNonempty`
(`famNonempty_of_run`), `noPinned` (`noPinned_of_run`), `readsDown` (`readsDown_of_run` from
group 7 on, `readsDownBasis_of_run` at the basis group), `literals` (`literals_of_run`), and
`routeNew` (`routeNew_of_run`, its payload case from `RemainingFamilyClauses.payloadChecked`),
which are proved, and of the four below what the group's walk gives (`walkedRef_not_inert`,
`walkedRef_needOk`, `IxVMRefinement.Binding.WalkedRefs`). `pay A` says that the group reaches `A`
through its payload (`PayReach` at the run's payload). -/
structure RunFactsLeft (ρ : BRun) (t : Ix.Kernel.RoleTable) (g : Nat) (R R' : Ixon.Env)
    (famOf : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (pay : _root_.Address → Prop) : Prop where
  /-- No reference a plain unit reached through the group's payload uses is an inert axiom's. -/
  notInert : ∀ A c x, PlainUnitAt t g R R' famOf A c → pay A → UsedRef ρ.E₀ A x → ¬ InertAt t x
  /-- Every reference a plain unit reached through the group's payload uses is one a step needs
  stored: a record of the run's store, no block, in Lean's logic with its block. -/
  needOk : ∀ A c x, PlainUnitAt t g R R' famOf A c → pay A → UsedRef ρ.E₀ A x → NeedOk ρ.E₀ x
  /-- No reference the block of a selected family record uses, the block new in the group and
  reached through the group's payload, is an inert axiom's. -/
  famNotInert : ∀ B rb x, famOf B = some rb → New R R' B → pay B → UsedRef ρ.E₀ B x →
    ¬ InertAt t x
  /-- Every reference the block of a selected family record uses, the block new in the group and
  reached through the group's payload, is one a step needs stored: a record of the run's store, no
  block, in Lean's logic with its block. -/
  famNeedOk : ∀ B rb x, famOf B = some rb → New R R' B → pay B → UsedRef ρ.E₀ B x →
    NeedOk ρ.E₀ x

/-- **What is left of the run's family checks**, at the store sequence with the run's payload
(`Rs g` below is `groupStore t E₀ (runPayload calls bAddr t) g`). Status: premises; nothing
proves them of any run. Each field is tagged with its source: today's circuit (not yet specified),
a named change of the circuit source, or unknown.
* `payloadDirect`, `payloadSteps`: the facts the store's clauses need of the payload's records
  (`PayloadFacts`, which follows from the two with the advice check's own facts,
  `RemainingFamilyClauses.payload`). `payloadDirect`: at the addresses the family checks name,
  what their own loads do not give (`PayloadDirectLeft`, which names each field's producer, both
  changes of the circuit source). `payloadSteps`: at the addresses reached
  from those by an uncovered used reference or a projection's block (`PayStep`): what
  `KernelModeled::advice_refs_ok`, `family_refs_go` and `container_refs_ok` admit (an earlier
  advice record, a projection of an advice block, a used reference of the block or a projection
  of the block one projects from, a witness), each witness checked by `check_witness` (kind 0:
  `KernelClaim::run_check_transitive`; kind 2: `check_container_rec`; kinds 1 and 3: the stop of
  `walk_path`, loaded by `Ingress::get_ci` once the circuit's `check_witness` calls it there).
  Source: today's circuit with that change, and the walk's assertions on inner references
  (`assert_safe_used_refs`, `assert_not_block_ref`) added to the advice, container and
  witnessed-reference checks.
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
  `block_elim` computes (every term read off the store in the canonical reading,
  `FamilyFlat.loadedAt`: the binder data of the record's binder blocks at the expression's root,
  as `get_ci` loads it).
* `familyForm`: the field `GroupFamilyChecks.familyForm`: the selected record's reconstruction
  form. Source: `check_recs`' form state under the group's validation (the reconstruction
  comparison in `canonical_rules_at_pos`), in the regenerated observations of
  `KernelModeled::check_family` and `check_recs` (every term read off the store in the canonical
  reading, `FamilyFlat.loadedAt`: the binder data of the record's binder blocks at the
  expression's root, as `get_ci` loads it).
* `runFacts`: what is left of `ClosureRunFacts` at the group (`RunFactsLeft`, which names each
  field's source); `famRefs` is the rank's, `advNotUnit`, `roleUnitForm` and `keptRoles` are proved
  (`families_of_remaining`).
* `famNew`: the selected record of a new block is new in the group. Source: unknown (no reading
  of the circuit excludes a family record an earlier group stored).
* `payloadChecked`: a new unit reached through the payload, of no twin's shape (`IsTwinShape`: a
  non-empty block of recursors only, which a container's projection may reach in a family record
  that only `check_recs` traverses; such a record is `claimed`'s), is checked at the group's limit
  by a check of a unit (`KernelClaim::run_check` in `check_advice_record`, `check_container_rec`;
  `KernelClaim::check_muts_all` for an advice block), or is a selected family record of a new
  block (checked by `check_recs`). Source: today's circuit, with the walk's assertions on inner
  references (`assert_safe_used_refs`, `assert_not_block_ref`) added to the advice, container
  and witnessed-reference checks, for what the payload's records reference. It also gives the
  payload case of `ClosureRunFacts.routeNew` (`routeNew_of_run`). -/
structure RemainingFamilyClauses (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) : Prop where
  payloadSteps : PayloadFactsOn t E₀ (runPayload calls bAddr t)
    (PayStep t E₀ (runPayload calls bAddr t))
  payloadRanked : ∀ g, 6 ≤ g → g < 77 → (∃ B a, runPayload calls bAddr t g B a) →
    ∃ rank, GroupRanked t E₀ (runPayload calls bAddr t) g (runFamOf calls bAddr t E₀ g)
      (runAdv calls bAddr t g) (runCont calls bAddr t g) rank
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
      (runAdv calls bAddr t g) (PayReach t E₀ (runPayload calls bAddr t) g)
  payloadChecked : ∀ g, 6 ≤ g → g < 77 → ∀ a c,
    PayReach t E₀ (runPayload calls bAddr t) g a →
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a →
    recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a = some c → UnitKind c →
    ¬ IsTwinShape c →
    UnitCheckedAt calls bAddr t E₀ a (some (valLimit g)) ∨
      ∃ B, runFamOf calls bAddr t E₀ g B = some a ∧
        New (groupStore t E₀ (runPayload calls bAddr t) g)
          (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B

section Families

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- **The payload's facts of a run**, from the direct facts proved of every run
(`payloadDirect_of_run`, `payloadDirect_of_left`) and the stepped ones (`payloadFacts_of_on`). -/
theorem RemainingFamilyClauses.payload (hR : RemainingFamilyClauses calls bAddr t E₀)
    (hC : CollisionFreeRun calls E₀) : PayloadFacts t E₀ (runPayload calls bAddr t) :=
  payloadFacts_of_on (payloadDirect_of_left hC (payloadDirect_of_run hC)) hR.payloadSteps

/-- **`GroupFamilyChecks.family` as a projection of `familyFlat`.** -/
theorem RemainingFamilyClauses.family (hR : RemainingFamilyClauses calls bAddr t E₀)
    (g : Nat) (hg6 : 6 ≤ g) (hg : g < 77) (B rb : _root_.Address)
    (hf : runFamOf calls bAddr t E₀ g B = some rb) :
    ∃ cb ms crb rs flat, FamilyOfBlock E₀ B cb ms rb crb rs flat := by
  obtain ⟨cb, crb, ms, rs, es, _, hF, -, -⟩ := hR.familyFlat g hg6 hg B rb hf
  exact ⟨cb, ms, crb, rs, es.map FamilyFlat.FlatEntry.addr, hF⟩

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
  have hP := (hR.payload hC)
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
  obtain ⟨c, hc⟩ := (hR.payload hC).record g a hreach
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
  rintro B rb a hfam ⟨rb', cs, advAs, hex, hin⟩ ⟨⟨r, hr, had, hk⟩, hnew⟩
  have hmod := (runFamOf_spec hfam).2.1
  have hreach := runPayload_reach hC hb hax hR hg6 hg hw hfam
    ⟨hmod, rb', cs, advAs, hex, Or.inr (Or.inl hin)⟩
  rcases hk with hop | hs
  · have h1 := hpay a hreach r had hop
    rw [groupOf_of_mem_roleGroup hr] at h1
    exact Nat.lt_irrefl g h1
  · obtain ⟨c, ax, hc, hi, -⟩ := hax r hs a had
    exact (hR.payload hC).notAxiomLike g a c hreach hnew hc (Or.inl ⟨ax, hi⟩)

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

/-- An expression whose constant reference indices all belong to `usedRefIdxs c`. -/
private def ExprRefsIn (c : Ixon.Constant) (e : Ixon.Expr) : Prop :=
  ∀ j ∈ exprRefIdxs e, j ∈ usedRefIdxs c

private theorem exprRefsIn_sharing (c : Ixon.Constant) {i : Nat} {e : Ixon.Expr}
    (h : c.sharing[i]? = some e) : ExprRefsIn c e := by
  intro j hj
  unfold usedRefIdxs
  apply List.mem_append_left
  rw [List.mem_flatMap]
  refine ⟨e, ?_, hj⟩
  have hL : c.sharing.toList[i]? = some e := by rw [Array.getElem?_toList]; exact h
  exact List.mem_of_getElem? hL

private theorem exprRefsIn_unshare (c : Ixon.Constant) :
    ∀ (k : Nat) (e : Ixon.Expr), ExprRefsIn c e → ExprRefsIn c (FamilyOf.unshare c k e)
  | 0, e, h => h
  | k + 1, .share i, _ => by
    unfold FamilyOf.unshare
    cases hs : c.sharing[i.toNat]? with
    | none => intro j hj; cases hj
    | some e' => exact exprRefsIn_unshare c k e' (exprRefsIn_sharing c hs)
  | _ + 1, .sort _, h | _ + 1, .var _, h | _ + 1, .ref _ _, h | _ + 1, .recur _ _, h
  | _ + 1, .prj _ _ _, h | _ + 1, .str _, h | _ + 1, .nat _, h | _ + 1, .app _ _, h
  | _ + 1, .lam _ _, h | _ + 1, .all _ _, h | _ + 1, .letE _ _ _ _ _, h => h

private theorem exprRefsIn_node (c : Ixon.Constant) {e : Ixon.Expr} (h : ExprRefsIn c e) :
    ExprRefsIn c (FamilyOf.node c e) :=
  exprRefsIn_unshare c (c.sharing.size + 1) e h

private theorem exprRefsIn_peel (c : Ixon.Constant) :
    ∀ (n : Nat) {e e' : Ixon.Expr}, ExprRefsIn c e → FamilyOf.peel c n e = some e' →
      ExprRefsIn c e'
  | 0, e, e', h, hp => by cases hp; exact h
  | n + 1, e, e', h, hp => by
    unfold FamilyOf.peel at hp
    have hn := exprRefsIn_node c h
    cases hnd : FamilyOf.node c e with
    | all d b =>
      rw [hnd] at hp hn
      exact exprRefsIn_peel c n (fun j hj => hn j (List.mem_append_right _ hj)) hp
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
    | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hp
      cases hp

private theorem exprRefsIn_domOf (c : Ixon.Constant) {e d : Ixon.Expr} (h : ExprRefsIn c e)
    (hd : FamilyOf.domOf c e = some d) : ExprRefsIn c d := by
  unfold FamilyOf.domOf at hd
  have hn := exprRefsIn_node c h
  cases hnd : FamilyOf.node c e with
  | all d' b =>
    rw [hnd] at hd hn
    cases hd
    exact fun j hj => hn j (List.mem_append_left _ hj)
  | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
  | letE _ _ _ _ _ | share _ =>
    rw [hnd] at hd
    cases hd

private theorem exprRefsIn_spineHead (c : Ixon.Constant) :
    ∀ (n : Nat) (e : Ixon.Expr), ExprRefsIn c e → ExprRefsIn c (FamilyOf.spineHead c n e)
  | 0, e, h => exprRefsIn_node c h
  | n + 1, e, h => by
    unfold FamilyOf.spineHead
    have hn := exprRefsIn_node c h
    cases hnd : FamilyOf.node c e with
    | app f a =>
      rw [hnd] at hn
      exact exprRefsIn_spineHead c n f (fun j hj => hn j (List.mem_append_left _ hj))
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _ | all _ _
    | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hn
      exact hn

/-- **The head constant of a recursor's major premise is a used reference of its block record**:
`refHeadAt` matches `.ref i _` (never `.recur`), and `unshare`/`peel`/`domOf`/`spineHead` stay
within `usedRefIdxs`. -/
theorem majorHeadAt_usedRef {crb : Ixon.Constant} {rs : Array Ixon.MutConst} {k : Nat}
    {r : Ixon.Recursor} {n : Nat} {a : _root_.Address}
    (hmuts : crb.info = .muts rs) (hr : rs[k]? = some (.recr r))
    (hmaj : FamilyOf.majorHeadAt crb r n = some a) :
    ∃ i ∈ usedRefIdxs crb, crb.refs[i]? = some a := by
  have htyp : ExprRefsIn crb r.typ := by
    intro j hj
    unfold usedRefIdxs
    rw [hmuts]
    apply List.mem_append_right
    rw [List.mem_flatMap]
    refine ⟨.recr r, ?_, List.mem_append_left _ hj⟩
    have hL : rs.toList[k]? = some (.recr r) := by rw [Array.getElem?_toList]; exact hr
    exact List.mem_of_getElem? hL
  unfold FamilyOf.majorHeadAt at hmaj
  cases hp : FamilyOf.peel crb
      (r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat) r.typ with
  | none => rw [hp] at hmaj; simp at hmaj
  | some e =>
    rw [hp] at hmaj
    dsimp only [bind, Option.bind] at hmaj
    cases hd : FamilyOf.domOf crb e with
    | none => rw [hd] at hmaj; simp at hmaj
    | some d =>
      rw [hd] at hmaj
      dsimp only [bind, Option.bind] at hmaj
      have hsp := exprRefsIn_spineHead crb n d
        (exprRefsIn_domOf crb (exprRefsIn_peel crb _ htyp hp) hd)
      unfold FamilyOf.refHeadAt at hmaj
      cases hsh : FamilyOf.spineHead crb n d with
      | ref i _ =>
        rw [hsh] at hmaj hsp
        exact ⟨i.toNat, hsp i.toNat (List.mem_singleton_self _), hmaj⟩
      | sort _ | var _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _ | all _ _
      | letE _ _ _ _ _ | share _ =>
        rw [hsh] at hmaj
        cases hmaj

/-- **`FamilyAdmits.famNew` of every run**: the selected family record `rb` of a new block `B`
is held after the group (`runPayload_held`) and cannot already be held in `groupStore ... g`.
If `recordOf (Rs g) rb = some crb`, then by `FamilyOfBlock.originals` and `.recursor_at` on the
non-empty block `B` (`famNonempty_of_run`), `crb` uses `memberAddr B 0 ms[0]`
(`majorHeadAt_usedRef`); two applications of `UsedClosed (Rs g)` (identifying the stored record
at `memberAddr B 0 ms[0]` with `memberProjection B 0 ms[0]` through `E₀` and
`FamBlockRecord.members`) then force `B` to be held in `Rs g`, contradicting `New (Rs g) _ B`. -/
theorem famNew_of_run (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀) {g : Nat}
    (hg6 : 6 ≤ g) (hg : g < 77)
    {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}
    (hw : GroupWalked calls bAddr t E₀ g recs)
    (hclg : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) g))
    {B rb : _root_.Address} (hfam : runFamOf calls bAddr t E₀ g B = some rb) :
    New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) rb := by
  refine ⟨runPayload_held hC hb hax hR hg6 hg hw hfam (runFamOf_payload hfam), ?_⟩
  cases hheld : recordOf (groupStore t E₀ (runPayload calls bAddr t) g) rb with
  | none => rfl
  | some crb₀ =>
    exfalso
    have hnewB := (runFamOf_spec hfam).1
    obtain ⟨cb₀, ms₀, hcb₀, hmuts₀, hpos₀⟩ := famNonempty_of_run hC B rb hfam
    obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hR.family g hg6 hg B rb hfam
    have ecb : cb = cb₀ := Option.some.inj (hF.block.record.symm.trans hcb₀)
    have ems : ms = ms₀ := Ixon.ConstantInfo.muts.inj
      ((ecb ▸ hF.block.muts).symm.trans hmuts₀)
    have hpos : 0 < ms.size := ems ▸ hpos₀
    have ecrb : crb₀ = crb := Option.some.inj
      (((groupStore_recordOf hb hg6).mp hheld).2.symm.trans hF.record.record)
    subst ecrb
    have hm0 : ms[0]? = some ms[0] := Array.getElem?_eq_getElem hpos
    have hflat0 := hF.originals 0 ms[0] hm0
    obtain ⟨r, hrs0, n, hmaj⟩ := hF.recursor_at hflat0
    obtain ⟨i, hi, href⟩ := majorHeadAt_usedRef hF.record.muts hrs0 hmaj
    have hmHeld := (hclg.1 rb crb₀ hheld).2 i hi (memberAddr B 0 ms[0]) href
    obtain ⟨cp, hcp⟩ := Option.isSome_iff_exists.mp hmHeld
    have hcpE : recordOf E₀ (memberAddr B 0 ms[0]) = some cp :=
      ((groupStore_recordOf hb hg6).mp hcp).2
    have ecp : cp = memberProjection B 0 ms[0] := Option.some.inj
      (hcpE.symm.trans (hF.block.members 0 ms[0] hm0))
    subst ecp
    have hBHeld := (hclg.1 (memberAddr B 0 ms[0]) (memberProjection B 0 ms[0]) hcp).1
    rw [ownerOf_memberProjection, hnewB.2] at hBHeld
    cases hBHeld

/-- **The family form's clauses at a group**, for a rank of its new records: `ClosureRunFacts`
from what is left of it (`RemainingFamilyClauses.runFacts`), the rank's `famRefs`, and
`advNotUnit`, `roleUnitForm`, `keptRoles`, `famNonempty`, `noPinned`, `readsDown`, `literals`
and `routeNew` (its payload case from `payloadChecked`) proved of the run;
`GroupFamilyChecks.modeled`, `famCall`, `family` and `FamilyAdmits.famNew` proved of the run. -/
theorem families_of_remaining (hC : CollisionFreeRun calls E₀) (hb : BasisRowsLoaded E₀)
    (hax : AxiomRolesDeclared t E₀) (hR : RemainingFamilyClauses calls bAddr t E₀)
    (hcheck : t.check = .ok ()) (hroots : RootsSafe t E₀) (hpin : PreludePinned t)
    {rk : Nat → _root_.Address → Nat} {g : Nat} (hg6 : 6 ≤ g) (hg : g < 77)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
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
  have hval := hvalAll g
  have hval77 : ∀ k, k < 77 → ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r :=
    fun k _ => hvalAll k
  have hL := hR.runFacts g hg6 hg rk
  have hplain : ∀ A c, PlainUnitAt t g (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) (runFamOf calls bAddr t E₀ g) A c →
      GroupReach t E₀ g A ∨ PayReach t E₀ (runPayload calls bAddr t) g A :=
    fun A c ⟨hn, hc, hu, _⟩ =>
      new_reach_cases hC hb hax (hR.payload hC) hg6 hw hn
        ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc).2 (unitKind_not_proj hu)
        (fun ax h => unitKind_not_axiom hu h)
  have hfamReach : ∀ B rb, runFamOf calls bAddr t E₀ g B = some rb →
      New (groupStore t E₀ (runPayload calls bAddr t) g)
        (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B →
      GroupReach t E₀ g B ∨ PayReach t E₀ (runPayload calls bAddr t) g B := by
    intro B rb hfam hn
    obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hR.family g hg6 hg B rb hfam
    exact new_reach_cases hC hb hax (hR.payload hC) hg6 hw hn hF.block.record
      (fun hp => proj_not_block hp ⟨ms, hF.block.muts⟩)
      (fun ax h => by rw [hF.block.muts] at h; cases h)
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
        routeNew := routeNew_of_run hC hb hax (hR.payload hC) hstep hg6 hw hcl hunits
          (roleUnitForm_of_run hC hb hax hcheck hg6 hval) hlogic
          (fun a c hr hn hc hu htw => (hR.payloadChecked g hg6 hg a c hr hn hc hu htw).imp id
            fun ⟨B, hB, _⟩ => by
              obtain ⟨-, -, cs, hfc⟩ := runFamOf_spec hB
              exact ⟨B, cs, hfc⟩)
        readsDown := by
          rcases Nat.lt_or_ge 6 g with h7 | h6
          · exact readsDown_of_run hcheck h7 hclg
          · exact readsDownBasis_of_run hcheck (Nat.le_antisymm h6 hg6)
        notInert := fun A c x hA hu => by
          rcases hplain A c hA with hr | hp
          · exact walkedRef_not_inert hC hval77 hw hr hu
          · exact hL.notInert A c x hA hp hu
        needOk := fun A c x hA hu => by
          rcases hplain A c hA with hr | hp
          · exact walkedRef_needOk hC hb hpin hax hval77 hroots hg hw hr hu
          · exact hL.needOk A c x hA hp hu
        literals := literals_of_run hC hb hcheck hvalAll hg6 hcl
        famNotInert := fun B rb x hfam hn hu => by
          rcases hfamReach B rb hfam hn with hr | hp
          · exact walkedRef_not_inert hC hval77 hw hr hu
          · exact hL.famNotInert B rb x hfam hn hp hu
        famNeedOk := fun B rb x hfam hn hu => by
          rcases hfamReach B rb hfam hn with hr | hp
          · exact walkedRef_needOk hC hb hpin hax hval77 hroots hg hw hr hu
          · exact hL.famNeedOk B rb x hfam hn hp hu }
  · exact
      { famNew := fun B rb h hB => ⟨famNew_of_run hC hb hax hR hg6 hg hw hclg h,
          hrank.fam B rb h hB⟩
        advice := fun B rb a h hB ha => by
          obtain ⟨rb', cs, advAs, hex, hin⟩ := ha
          exact ⟨runPayload_held hC hb hax hR hg6 hg hw h
              ⟨(runFamOf_spec h).2.1, rb', cs, advAs, hex, Or.inr (Or.inl hin)⟩,
            fun hn => hrank.advice B rb a h hB ⟨rb', cs, advAs, hex, hin⟩ hn⟩
        container := fun B rb x h hB hx => by
          obtain ⟨rb', cs, advAs, hex, hin⟩ := hx
          exact ⟨runPayload_held hC hb hax hR hg6 hg hw h
              ⟨(runFamOf_spec h).2.1, rb', cs, advAs, hex, Or.inr (Or.inr hin)⟩,
            fun hn => hrank.container B rb x h hB ⟨rb', cs, advAs, hex, hin⟩ hn⟩
        checked := fun a c hn hc hu htw => by
          rcases groupStore_checked hC hb hax (hR.payload hC) hg6 hw a c hn hc hu with h | h
          · exact Or.inl h
          · exact hR.payloadChecked g hg6 hg a c h hn hc hu htw }

end Families

end IxVM.Refinement.Binding
