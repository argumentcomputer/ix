import IxVMRefinement.Binding.PayloadClosed
import IxVMRefinement.FamilyGraph.ProducersAcyclic

/-! # Ranking the new records of a group with a family-check payload

Discharges `GroupRanked` at every group `6 ≤ g < 77` (`payloadRanked_of_run`), assigning a
lexicographic 4-tuple potential `Pot := Nat × Nat × Nat × Nat` to every new record of group `g`
and converting `PotLt` to a `Nat` rank via `potRank` (count of `E₀.consts.keys` with strictly
smaller potential):

* **Tier 0**:
  - `(0, 0, 0, 0)`: a new projection record whose owner block is already stored in `Rs g`;
  - `(0, 1, 0, 0)`: a new standalone container recursor (`.recr`) witnessed by a family check of a
    block `B` already stored in `Rs g` (every new used reference of such a recursor is a projection
    of a stored block, at `(0, 0, 0, 0)`).
* **Tier 1** (`(1, m1, k1, 0)`): a new non-projection record (not Tier 0) that is an advice record
  at index `k` (`(2 * cs.length, k + 1)`) or the family record (`(2 * cs.length + 1, 0)`) of a
  family check anchored at a block `B` already stored in `Rs g`, minimizing `(m1, k1)`
  lexicographically. Any nested `RPrj` container witness inside `cs` triggers a `check_family` call
  with strictly shorter call list `cs'.length < cs.length`, so `2 * cs'.length + 1 < 2 * cs.length`.
* **Tier ≥ 2**:
  - `(2 + walkRank recs B, 1, 0, 2)`: a new family record `rb` of a new modeled block `B` (unique
    by `familyCall_block_unique`);
  - `(2 + mu, τ, nu, 0)`: any other new non-projection record, minimizing `walkRank recs` over its
    own walk entry (if `GroupReach`) and over the new modeled blocks `B` of which it is a local
    standalone container (`p = 0`) or non-projection advice (`p = k + 1`), defaulting to
    `maxDepth recs + 1` (for the group's standard axiom).
* **New projections of new blocks**: `(pot0 owner).bump`, adding `+ 1` to the fourth coordinate
  (canonical projections have empty `usedRefIdxs`). -/

set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

/-! ## Rank conversion from `PotLt` -/

open Classical in
/-- Count of addresses in `keys` with strictly smaller potential under `PotLt`. -/
noncomputable def potRank (keys : List _root_.Address) (pot : _root_.Address → Pot)
    (y : _root_.Address) : Nat :=
  keys.countP fun z => decide (PotLt (pot z) (pot y))

theorem potRank_lt {keys : List _root_.Address} {pot : _root_.Address → Pot}
    {z y : _root_.Address} (hz : z ∈ keys) (hlt : PotLt (pot z) (pot y)) :
    potRank keys pot z < potRank keys pot y := by
  unfold potRank
  refine countP_lt_of_imp (y := z) ?_ hz ?_ ?_
  · intro x hx
    simp only [decide_eq_true_eq] at hx ⊢
    exact PotLt.trans hx hlt
  · simpa using hlt
  · simp [PotLt.irrefl]

/-! ## Structural and call-length helpers -/

section Helpers

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env}

/-- An observed `check_container_rec` on an `RPrj` recursor triggers a modeled `FamilyCallExact`
for its recursor block `rp.block` anchored at `ib`, with strictly shorter call list `cs'.length < csCr.length`. -/
theorem check_container_rec_rprj_family_lt_len (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hstep : RunStepStores calls t E₀)
    {lim : Option Nat} {x ib : _root_.Address} {cx : Ixon.Constant} {rp : Ixon.RecursorProj}
    {rc xx xib r : SourceValue F} {h h' : Heap F} {csCr : List (Call F)}
    (hrc : Claim.RCLimRep t bAddr lim h rc)
    (hx : Core.S0.addr h xx x) (hib : Core.S0.addr h xib ib)
    (evCr : ObsFn Obs.W "KernelModeled::check_container_rec" [rc, xx, xib] h r h' csCr)
    (hsubCr : ∀ cl ∈ csCr, cl ∈ calls)
    (hc : recordOf E₀ x = some cx) (hrp : cx.info = .rPrj rp) :
    ∃ (cs' : List (Call F)) (advAs' : List Bytes.Address),
      ModeledRouteAt calls ib ∧
      FamilyCallExact calls bAddr t ib rp.block lim cs' advAs' ∧
      cs'.length < csCr.length := by
  obtain ⟨v26, m29, cs37, evRfb1, hres1, hsub37⟩ :=
    check_container_rec_rec_family_block hC hbd hx hib evCr hsubCr
  match Obs.«KernelModeled::check_container_rec».obs evCr with
  | .run (cs73 := csRun) (ev39 := ev39) (ev25 := ev25) (ev_nqhglzzq := ev_ci)
      (ev75 := evRun) (hc96 := hc96) .. =>
    have ext : Heap.Extends h _ :=
      ev39.heap_extends.trans (ev25.heap_extends.trans ev_ci.heap_extends)
    have hsubRun : ∀ cl ∈ csRun, cl ∈ calls := fun cl hcl => hsubCr cl (by rw [hc96]; simp [hcl])
    have hlenRun : csRun.length < csCr.length := by rw [hc96]; simp; omega
    obtain ⟨v1, m2, p9, cs15, cs29, ev17, ld11, ev31, hc56⟩ :=
      Obs.«KernelClaim::run_check».obs evRun
    have hsub15 : ∀ cl ∈ cs15, cl ∈ calls := fun cl hcl => hsubRun cl (by rw [hc56]; simp [hcl])
    have hsub29 : ∀ cl ∈ cs29, cl ∈ calls := fun cl hcl => hsubRun cl (by rw [hc56]; simp [hcl])
    have hlen29 : cs29.length < csRun.length := by rw [hc56]; simp; omega
    obtain ⟨ab, hab, rfl⟩ := Core.S0.addr_mono ext hx
    obtain ⟨raw, c', -, hh, hba, hde, -, hhead⟩ := Claim.get_ci_head hab ev17
    have ec : c' = cx := hC.runStore.record_eq ((hC.runStore.recordOf_eq_recordAt _).symm.trans hc)
      (Core.hashed_mono hsub15 hh) hba hde
    subst ec
    obtain ⟨cb, ms, rcr, hbl, hmem, nl, ty, np, ni, nm, nmin, rules, k, x_blk, b, hldR, hb_rep,
      hb_eq⟩ := hhead.rPrj rp.idx rp.block hrp
    rw [ld11] at hldR
    injection hldR with hv
    subst hv
    obtain ⟨hrecB, hmsB⟩ := (hbl.mono hsub15).stored hC.hashedStored
    have ha_m : Core.S0.addr m2 xx (Core.ixAddr ab) :=
      ⟨ab, Bytes.repAddressRef_heapMono₂ Core.addrTy ev17.heap_extends hab, rfl⟩
    obtain ⟨family, cs', h_rf, m_rf, ap_rf, fb_rf, cs_rf, hmod, hfc, -, hlen',
        ha_rf, hfb_rf, ev_rf, hsub_rf⟩ :=
      check_const_rec_block_modeled_family hC hstep ((hrc.mono ext).mono ev17.heap_extends) ha_m
        ⟨b, hb_rep, hb_eq⟩ hrecB hmsB ⟨rcr, List.mem_of_getElem? hmem⟩ ev31 hsub29
    have efam : family = ib := rec_family_block_det hC hbd ha_rf hx ev_rf evRfb1
      (fun cl hcl => hsub29 cl (hsub_rf cl hcl)) hsub37 hfb_rf hres1
    subst efam
    obtain ⟨advAs', hex'⟩ := familyCallExact_of_call hfc
    exact ⟨cs', advAs', hmod, hex', Nat.lt_trans hlen' (Nat.lt_trans hlen29 hlenRun)⟩

/-- Every `New` projection record in group `g` has empty `usedRefIdxs` (hence no `UsedRef`). -/
theorem new_proj_no_usedRef (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) (hg77 : g < 77)
    {a : _root_.Address} {c : Ixon.Constant}
    (hnew : New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) a)
    (hc : recordOf E₀ a = some c) (hp : IsProj c) :
    ∀ x, ¬ UsedRef E₀ a x := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  obtain ⟨recs, hw⟩ := hws g
  have hfromWalk : GroupReach t E₀ g a → usedRefIdxs c = [] := by
    intro hgr
    obtain ⟨y, -, hya⟩ := hgr.listed hC.hashedStored hw
    have hyc : y.c = c := by
      have h1 := topRec_recordOf hC.hashedStored y
      rw [hya, hc] at h1
      exact (Option.some.inj h1).symm
    rcases y.hchecked with ⟨ms, hms, -⟩ | hchk
    · rw [hyc] at hms
      exact (proj_not_block hp ⟨ms, hms⟩).elim
    · rw [hya] at hchk
      obtain ⟨_, _, _, _, _, _, _, _, cs_load, _, -, -, ⟨ab, hab, rfl⟩, -, ev_ld, -, hsub_ld, -⟩ :=
        hchk
      exact proj_usedRefIdxs_nil hC.runStore hab ev_ld hsub_ld hc hp
  have hnilOrEmpty : usedRefIdxs c = [] ∨ c.refs = #[] := by
    obtain ⟨c₀, hE₀, -, hadd, -⟩ := new_groupStore hb hg6 hnew
    have ec0 : c₀ = c := Option.some.inj (hE₀.symm.trans hc)
    subst ec0
    rcases groupAdds_cases hC hax hw hadd with ⟨hgr, -⟩ |
        ⟨-, -, -, -, p, hp', -, -, hrefs, -⟩ | ⟨_, -, -, -, c₂, ax, hc₂, hi, -⟩ | hpay
    · exact Or.inl (hfromWalk hgr)
    · have ep : p = c₀ := Option.some.inj (hp'.symm.trans hc)
      exact Or.inr (ep ▸ hrefs)
    · have ec : c₂ = c₀ := Option.some.inj (hc₂.symm.trans hc)
      exact (proj_not_axiom hp (ec ▸ hi)).elim
    · rcases payAdds_cases hP hpay with ⟨hpr, -⟩ | ⟨-, -, -, -, -, p, hp', -, -, hrefs, -⟩
      · cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws hg6 hg77 hpr with
        | stored hst => rw [hnew.2] at hst; cases hst
        | walked hgr => exact Or.inl (hfromWalk hgr)
        | famRec _ _ hex =>
          have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
          obtain ⟨c', rs, hc', -, hrs, -, -, -⟩ :=
            familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
          have ec : c' = c₀ := Option.some.inj (hc'.symm.trans hc)
          exact (proj_not_block hp ⟨rs, ec ▸ hrs⟩).elim
        | directAdv _ _ hex hadv =>
          obtain ⟨outs, hU⟩ := hex.unpack hC hbd
          obtain ⟨ab, habMem, habEq⟩ := hadv
          obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
          have hfacts := hU.adviceFacts k hk
          rw [hgetk, habEq] at hfacts
          obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
          have ec : ca = c₀ := Option.some.inj (hca.symm.trans hc)
          subst ec
          rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms, hms, -⟩ | ⟨-, hnil, -⟩
          · exact (standalone_not_proj (Or.inl ⟨d, hd⟩) hp).elim
          · exact (standalone_not_proj (Or.inr (Or.inl ⟨rc, hrc⟩)) hp).elim
          · exact (proj_not_block hp ⟨ms, hms⟩).elim
          · exact Or.inl hnil
        | directCont _ _ hex hdc =>
          obtain ⟨-, -, -, hcrIn, -⟩ := hdc.unpack hC hbd
          obtain ⟨_, _, ab, _, _, _, _, hab, rfl, evCi, hsubCi, -⟩ :=
            containerRecIn_load (FamilyCallExact.toCall hex) hcrIn
          exact Or.inl (proj_usedRefIdxs_nil hC.runStore hab evCi hsubCi hc hp)
        | checkedProj hc' _ hnil _ _ _ =>
          have ec : _ = c₀ := Option.some.inj (hc'.symm.trans hc)
          exact Or.inl (ec ▸ hnil)
      · have ep : p = c₀ := Option.some.inj (hp'.symm.trans hc)
        exact Or.inr (ep ▸ hrefs)
  intro x ⟨c', i, hc', hi, hx⟩
  have ec : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst ec
  rcases hnilOrEmpty with hnil | hrefs
  · rw [hnil] at hi; cases hi
  · rw [hrefs] at hx; simp at hx

/-- Every `New` modeled block with a `FamilyCallAtLim` at group `g` is `GroupReach t E₀ g`. -/
theorem new_modeledBlock_groupReach (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs)
    {g : Nat} (hg6 : 6 ≤ g) (hg77 : g < 77)
    {B rb : _root_.Address} {cs : List (Call F)}
    (hnew : New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B)
    (hmod : ModeledRouteAt calls B)
    (hfc : FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs) :
    GroupReach t E₀ g B := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
  obtain ⟨recs, hw⟩ := hws g
  obtain ⟨cb, ms, hcb, hms, hpos, hallIndc⟩ :=
    familyCall_block_indc_nonempty hC.runStore hC.hashedStored hfc
  rcases new_reach_cases hC hb hax hP hg6 hw hnew hcb
      (fun hp => proj_not_block hp ⟨ms, hms⟩) (fun ax h => by rw [hms] at h; cases h) with
    hgr | hpr
  · exact hgr
  · cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws hg6 hg77 hpr with
    | stored hst => rw [hnew.2] at hst; cases hst
    | walked hgr => exact hgr
    | famRec _ _ hex =>
      exfalso
      obtain ⟨c', rs, hc', -, hrs, -, hallRec, -⟩ :=
        familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex)
      have ec : c' = cb := Option.some.inj (hc'.symm.trans hcb)
      subst ec
      have ers : rs = ms := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hms)
      subst rs
      have hm0 : ms[0] ∈ ms.toList := Array.getElem_mem_toList hpos
      have hbi : Core.Specs.Callees.isIndc ms[0] = true :=
        (List.length_filter_eq_length_iff.mp (by simpa [Array.length_toList] using hallIndc)) _ hm0
      obtain ⟨r, hr⟩ := hallRec _ hm0
      rw [hr] at hbi
      simp [Core.Specs.Callees.isIndc, Core.isIndc] at hbi
    | directAdv _ _ hex hadv =>
      exfalso
      obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      obtain ⟨ab, habMem, habEq⟩ := hadv
      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
      have ec : ca = cb := Option.some.inj (hca.symm.trans hcb)
      subst ec
      rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨_, _, -, -, hnat⟩ | ⟨hpr, -⟩
      · rw [hms] at hd; cases hd
      · rw [hms] at hrc; cases hrc
      · exact not_modeledRouteAt_of_nativeObs hnat hmod
      · exact proj_not_block hpr ⟨ms, hms⟩
    | directCont _ _ hex hdc =>
      exact (containerRecIn_notBlock hC.runStore (FamilyCallExact.toCall hex)
        (directContOwn_toContainerRecIn hdc) hcb ms hms).elim
    | checkedProj hc' hpr _ _ _ _ =>
      have ec : _ = cb := Option.some.inj (hc'.symm.trans hcb)
      rw [ec] at hpr
      exact (proj_not_block hpr ⟨ms, hms⟩).elim

/-- A family record `rb` of a `New` block `B` reaches `B` by a 2-step `PathPos` through
`memberAddr B 0 ms[0]`. -/
theorem new_famRec_pathPos_block (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    {g : Nat} (hg6 : 6 ≤ g) (hg77 : g < 77)
    (hcl' : UsedClosed (groupStore t E₀ (runPayload calls bAddr t) (g + 1)))
    {B rb : _root_.Address} {cs : List (Call F)}
    (hnewB : New (groupStore t E₀ (runPayload calls bAddr t) g)
      (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) B)
    (hfc : FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs) :
    PathPos E₀ rb B := by
  have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
  obtain ⟨cb, ms, hpos, hcbE, hms, -, hused⟩ :=
    familyCall_uses_block hC hbd hvl hfc
  obtain ⟨cb', hcb'⟩ := Option.isSome_iff_exists.mp hnewB.1
  have ecb : cb' = cb := Option.some.inj
    (((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcb').2.symm.trans hcbE)
  subst ecb
  have hm0R' := (hcl'.2 B cb' ms hcb' hms 0 ms[0] (Array.getElem?_eq_getElem hpos)).1
  have hm0E : recordOf E₀ (memberAddr B 0 ms[0]) = some (memberProjection B 0 ms[0]) :=
    ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hm0R').2
  exact PathPos.tail (PathPos.single (Or.inl hused))
    (Or.inr ⟨memberProjection B 0 ms[0], hm0E, memberProjection_isProj B 0 ms[0],
      (ownerOf_memberProjection (memberAddr B 0 ms[0]) B 0 ms[0]).symm⟩)

end Helpers

/-! ## The three-tier lexicographic potential -/

section Potential

variable (calls : List (Call F)) (bAddr : _root_.Address)
  (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (g : Nat)

/-- Shorthand for an address stored before group `g`. -/
def StoredAtG (x : _root_.Address) : Prop :=
  (recordOf (groupStore t E₀ (runPayload calls bAddr t) g) x).isSome = true

/-- Shorthand for an address new in group `g`. -/
def NewAtG (x : _root_.Address) : Prop :=
  New (groupStore t E₀ (runPayload calls bAddr t) g)
    (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) x

/-- Exact family check anchored at a block `B` already stored before group `g`. -/
def StoredFamCall (B rb : _root_.Address) (cs : List (Call F)) (advAs : List Bytes.Address) :
    Prop :=
  StoredAtG calls bAddr t E₀ g B ∧ ModeledRouteAt calls B ∧
    FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs

/-- Exact family check anchored at a block `B` new in group `g` (and walk-reached). -/
def NewFamCall (B rb : _root_.Address) (cs : List (Call F)) (advAs : List Bytes.Address) : Prop :=
  NewAtG calls bAddr t E₀ g B ∧ GroupReach t E₀ g B ∧ ModeledRouteAt calls B ∧
    FamilyCallExact calls bAddr t B rb (some (valLimit g)) cs advAs

/-- Tier 0 non-projection: standalone `.recr` container witness of a stored-anchored family check. -/
def StoredStandaloneCont (n : _root_.Address) : Prop :=
  (∃ c rc, recordOf E₀ n = some c ∧ c.info = .recr rc) ∧
  ∃ B rb cs advAs, StoredFamCall calls bAddr t E₀ g B rb cs advAs ∧
    DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs n

/-- Tier 1 `(2*M, k+1)` or `(2*M+1, 0)` candidate from a stored-anchored family check. -/
def StoredCand (n : _root_.Address) (q : Nat × Nat) : Prop :=
  (∃ B rb cs advAs, ∃ (k : Nat) (hk : k < advAs.length),
      StoredFamCall calls bAddr t E₀ g B rb cs advAs ∧
      Core.ixAddr (advAs[k]'hk) = n ∧ q = (2 * cs.length, k + 1)) ∨
  (∃ B cs advAs,
      StoredFamCall calls bAddr t E₀ g B n cs advAs ∧ q = (2 * cs.length + 1, 0))

/-- Tier 1 membership. -/
def StoredAnchored (n : _root_.Address) : Prop :=
  ∃ m k, StoredCand calls bAddr t E₀ g n (m, k)

open Classical in
/-- Minimum first Tier-1 coordinate. -/
noncomputable def tier1M (n : _root_.Address) : Nat :=
  if h : ∃ m, ∃ k, StoredCand calls bAddr t E₀ g n (m, k) then Nat.find h else 0

open Classical in
/-- Minimum second Tier-1 coordinate at `tier1M`. -/
noncomputable def tier1K (n : _root_.Address) : Nat :=
  if h : ∃ k, StoredCand calls bAddr t E₀ g n (tier1M calls bAddr t E₀ g n, k) then Nat.find h
  else 0

/-- Tier ≥ 2 family record of a new modeled block. -/
def NewRecAnch (n : _root_.Address) : Prop :=
  ∃ B cs advAs, NewFamCall calls bAddr t E₀ g B n cs advAs

/-- Local non-projection record (standalone container at `0`, advice at `k+1`) of a new-anchored
family check. -/
def LocalAtG (B rb : _root_.Address) (cs : List (Call F)) (advAs : List Bytes.Address)
    (n : _root_.Address) (p : Nat) : Prop :=
  (p = 0 ∧ (∃ c rc, recordOf E₀ n = some c ∧ c.info = .recr rc) ∧
    DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs n) ∨
  (∃ (k : Nat) (hk : k < advAs.length), p = k + 1 ∧ Core.ixAddr (advAs[k]'hk) = n ∧
    ∃ c, recordOf E₀ n = some c ∧ ¬ IsProj c)

/-- Walk-rank anchor for Tier ≥ 2 records. -/
def AnchorG (recs : List (Claim.TopRec calls bAddr t (some (valLimit g))))
    (n : _root_.Address) (k : Nat) : Prop :=
  (GroupReach t E₀ g n ∧ k = walkRank recs n) ∨
  ∃ B rb cs advAs p, NewFamCall calls bAddr t E₀ g B rb cs advAs ∧
    LocalAtG calls bAddr t E₀ g B rb cs advAs n p ∧ k = walkRank recs B

open Classical in
/-- Least Tier ≥ 2 anchor (defaulting to `maxDepth recs + 1` for unlisted records such as the
group's standard axiom). -/
noncomputable def muG (recs : List (Claim.TopRec calls bAddr t (some (valLimit g))))
    (n : _root_.Address) : Nat :=
  if h : ∃ k, AnchorG calls bAddr t E₀ g recs n k then Nat.find h else maxDepth recs + 1

/-- Local record attaining `muG` at position `p`. -/
def AtMuG (recs : List (Claim.TopRec calls bAddr t (some (valLimit g))))
    (n : _root_.Address) (p : Nat) : Prop :=
  ∃ B rb cs advAs, NewFamCall calls bAddr t E₀ g B rb cs advAs ∧
    LocalAtG calls bAddr t E₀ g B rb cs advAs n p ∧
    walkRank recs B = muG calls bAddr t E₀ g recs n

open Classical in
/-- Least position among `AtMuG` witnesses. -/
noncomputable def nuG (recs : List (Claim.TopRec calls bAddr t (some (valLimit g))))
    (n : _root_.Address) : Nat :=
  if h : ∃ p, AtMuG calls bAddr t E₀ g recs n p then Nat.find h else 0

open Classical in
/-- Potential of a non-projection record. -/
noncomputable def pot0G (recs : List (Claim.TopRec calls bAddr t (some (valLimit g))))
    (n : _root_.Address) : Pot :=
  if _h0 : StoredStandaloneCont calls bAddr t E₀ g n then (0, 1, 0, 0)
  else if _h1 : StoredAnchored calls bAddr t E₀ g n then
    (1, tier1M calls bAddr t E₀ g n, tier1K calls bAddr t E₀ g n, 0)
  else if h2 : NewRecAnch calls bAddr t E₀ g n then
    (2 + walkRank recs (Classical.choose h2), 1, 0, 2)
  else
    (2 + muG calls bAddr t E₀ g recs n,
      (if _ha : ∃ p, AtMuG calls bAddr t E₀ g recs n p then 0 else 1),
      nuG calls bAddr t E₀ g recs n, 0)

/-- Predicate identifying a projection record in `E₀`. -/
def IsProjRec (n : _root_.Address) : Prop :=
  ∃ c, recordOf E₀ n = some c ∧ IsProj c

open Classical in
/-- **The full three-tier potential** on group `g`. -/
noncomputable def potG (recs : List (Claim.TopRec calls bAddr t (some (valLimit g))))
    (n : _root_.Address) : Pot :=
  if h : IsProjRec E₀ n then
    if StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf n (Classical.choose h)) then (0, 0, 0, 0)
    else (pot0G calls bAddr t E₀ g recs (Ix.Cert.ownerOf n (Classical.choose h))).bump
  else pot0G calls bAddr t E₀ g recs n

end Potential

/-! ## Potential unfolding and monotonicity lemmas -/

section RankProof

variable {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
  {E₀ : Ixon.Env} {g : Nat} {recs : List (Claim.TopRec calls bAddr t (some (valLimit g)))}

private theorem tier1M_le {m k : Nat} {x : _root_.Address}
    (h : StoredCand calls bAddr t E₀ g x (m, k)) : tier1M calls bAddr t E₀ g x ≤ m := by
  classical
  have hex : ∃ m', ∃ k', StoredCand calls bAddr t E₀ g x (m', k') := ⟨m, k, h⟩
  unfold tier1M
  rw [dite_eq_left hex]
  exact Nat.find_min' hex ⟨k, h⟩

private theorem tier1K_le {x : _root_.Address} {k : Nat}
    (h : StoredCand calls bAddr t E₀ g x (tier1M calls bAddr t E₀ g x, k)) :
    tier1K calls bAddr t E₀ g x ≤ k := by
  classical
  have hex : ∃ k', StoredCand calls bAddr t E₀ g x (tier1M calls bAddr t E₀ g x, k') := ⟨k, h⟩
  unfold tier1K
  rw [dite_eq_left hex]
  exact Nat.find_min' hex h

private theorem tier1_spec {x : _root_.Address} (h : StoredAnchored calls bAddr t E₀ g x) :
    StoredCand calls bAddr t E₀ g x (tier1M calls bAddr t E₀ g x, tier1K calls bAddr t E₀ g x) := by
  classical
  unfold StoredAnchored at h
  have hm : ∃ k, StoredCand calls bAddr t E₀ g x (tier1M calls bAddr t E₀ g x, k) := by
    unfold tier1M
    rw [dite_eq_left h]
    exact Nat.find_spec h
  unfold tier1K
  rw [dite_eq_left hm]
  exact Nat.find_spec hm

private theorem muG_le {n : _root_.Address} {k : Nat}
    (h : AnchorG calls bAddr t E₀ g recs n k) : muG calls bAddr t E₀ g recs n ≤ k := by
  classical
  have hex : ∃ k', AnchorG calls bAddr t E₀ g recs n k' := ⟨k, h⟩
  unfold muG
  rw [dite_eq_left hex]
  exact Nat.find_min' hex h

private theorem muG_spec {n : _root_.Address} (hex : ∃ k, AnchorG calls bAddr t E₀ g recs n k) :
    AnchorG calls bAddr t E₀ g recs n (muG calls bAddr t E₀ g recs n) := by
  classical
  unfold muG
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

private theorem muG_none {n : _root_.Address}
    (hex : ¬ ∃ k, AnchorG calls bAddr t E₀ g recs n k) :
    muG calls bAddr t E₀ g recs n = maxDepth recs + 1 := by
  unfold muG
  rw [dite_eq_right hex]

private theorem nuG_le {n : _root_.Address} {p : Nat}
    (h : AtMuG calls bAddr t E₀ g recs n p) : nuG calls bAddr t E₀ g recs n ≤ p := by
  classical
  have hex : ∃ p', AtMuG calls bAddr t E₀ g recs n p' := ⟨p, h⟩
  unfold nuG
  rw [dite_eq_left hex]
  exact Nat.find_min' hex h

private theorem nuG_spec {n : _root_.Address} (hex : ∃ p, AtMuG calls bAddr t E₀ g recs n p) :
    AtMuG calls bAddr t E₀ g recs n (nuG calls bAddr t E₀ g recs n) := by
  classical
  unfold nuG
  rw [dite_eq_left hex]
  exact Nat.find_spec hex

private theorem nuG_none {n : _root_.Address} (hex : ¬ ∃ p, AtMuG calls bAddr t E₀ g recs n p) :
    nuG calls bAddr t E₀ g recs n = 0 := by
  unfold nuG
  rw [dite_eq_right hex]

private theorem potG_notProj {n : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E₀ n = some c) (hnp : ¬ IsProj c) :
    potG calls bAddr t E₀ g recs n = pot0G calls bAddr t E₀ g recs n := by
  have h : ¬ IsProjRec E₀ n := by
    rintro ⟨c', hc', hp⟩
    rw [Option.some.inj (hc'.symm.trans hc)] at hp
    exact hnp hp
  unfold potG
  rw [dite_eq_right h]

private theorem potG_storedProj {n : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E₀ n = some c) (hp : IsProj c)
    (hst : StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf n c)) :
    potG calls bAddr t E₀ g recs n = (0, 0, 0, 0) := by
  have h : IsProjRec E₀ n := ⟨c, hc, hp⟩
  unfold potG
  rw [dite_eq_left h]
  have ec : Classical.choose h = c :=
    Option.some.inj ((Classical.choose_spec h).1.symm.trans hc)
  rw [ec]; simp only [hst, ↓reduceIte]

private theorem potG_newProj {n : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf E₀ n = some c) (hp : IsProj c)
    (hns : ¬ StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf n c)) :
    potG calls bAddr t E₀ g recs n = (pot0G calls bAddr t E₀ g recs (Ix.Cert.ownerOf n c)).bump := by
  have h : IsProjRec E₀ n := ⟨c, hc, hp⟩
  unfold potG
  rw [dite_eq_left h]
  have ec : Classical.choose h = c :=
    Option.some.inj ((Classical.choose_spec h).1.symm.trans hc)
  rw [ec]; simp only [hns, ↓reduceIte]

private theorem pot0G_tier0 {n : _root_.Address}
    (h0 : StoredStandaloneCont calls bAddr t E₀ g n) :
    pot0G calls bAddr t E₀ g recs n = (0, 1, 0, 0) := by
  unfold pot0G; rw [dite_eq_left h0]

private theorem pot0G_tier1 {n : _root_.Address}
    (h0 : ¬ StoredStandaloneCont calls bAddr t E₀ g n)
    (h1 : StoredAnchored calls bAddr t E₀ g n) :
    pot0G calls bAddr t E₀ g recs n =
      (1, tier1M calls bAddr t E₀ g n, tier1K calls bAddr t E₀ g n, 0) := by
  unfold pot0G; rw [dite_eq_right h0, dite_eq_left h1]

private theorem pot0G_newRec {n B : _root_.Address}
    (h0 : ¬ StoredStandaloneCont calls bAddr t E₀ g n)
    (h1 : ¬ StoredAnchored calls bAddr t E₀ g n)
    (h2 : NewRecAnch calls bAddr t E₀ g n)
    (huniq : ∀ B' cs' advAs', NewFamCall calls bAddr t E₀ g B' n cs' advAs' → B' = B) :
    pot0G calls bAddr t E₀ g recs n = (2 + walkRank recs B, 1, 0, 2) := by
  unfold pot0G
  rw [dite_eq_right h0, dite_eq_right h1, dite_eq_left h2]
  obtain ⟨cs', advAs', hfc'⟩ := Classical.choose_spec h2
  rw [huniq _ cs' advAs' hfc']

private theorem pot0G_atMu {n : _root_.Address}
    (h0 : ¬ StoredStandaloneCont calls bAddr t E₀ g n)
    (h1 : ¬ StoredAnchored calls bAddr t E₀ g n)
    (h2 : ¬ NewRecAnch calls bAddr t E₀ g n)
    (ha : ∃ p, AtMuG calls bAddr t E₀ g recs n p) :
    pot0G calls bAddr t E₀ g recs n =
      (2 + muG calls bAddr t E₀ g recs n, 0, nuG calls bAddr t E₀ g recs n, 0) := by
  unfold pot0G; rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_left ha]

private theorem pot0G_own {n : _root_.Address}
    (h0 : ¬ StoredStandaloneCont calls bAddr t E₀ g n)
    (h1 : ¬ StoredAnchored calls bAddr t E₀ g n)
    (h2 : ¬ NewRecAnch calls bAddr t E₀ g n)
    (ha : ¬ ∃ p, AtMuG calls bAddr t E₀ g recs n p) :
    pot0G calls bAddr t E₀ g recs n = (2 + muG calls bAddr t E₀ g recs n, 1, 0, 0) := by
  unfold pot0G
  rw [dite_eq_right h0, dite_eq_right h1, dite_eq_right h2, dite_eq_right ha, nuG_none ha]

/-- **Tier 1 bound**: if `StoredCand x (m, k)` holds, then `pot0G x` is either `(0, 1, 0, 0)` or
`(1, m', k', 0)` with `(m', k') ≤_lex (m, k)`. -/
private theorem pot0G_le_tier1 {x : _root_.Address} {m k : Nat}
    (h : StoredCand calls bAddr t E₀ g x (m, k)) :
    pot0G calls bAddr t E₀ g recs x = (0, 1, 0, 0) ∨
      ((pot0G calls bAddr t E₀ g recs x).1 = 1 ∧
        ((pot0G calls bAddr t E₀ g recs x).2.1 < m ∨
          ((pot0G calls bAddr t E₀ g recs x).2.1 = m ∧
            (pot0G calls bAddr t E₀ g recs x).2.2.1 ≤ k))) := by
  by_cases h0 : StoredStandaloneCont calls bAddr t E₀ g x
  · exact Or.inl (pot0G_tier0 h0)
  · right
    have h1 : StoredAnchored calls bAddr t E₀ g x := ⟨m, k, h⟩
    rw [pot0G_tier1 h0 h1]
    have hm := tier1M_le h
    rcases Nat.lt_or_eq_of_le hm with hlt | heq
    · exact ⟨rfl, Or.inl hlt⟩
    · refine ⟨rfl, Or.inr ⟨heq, tier1K_le (heq ▸ h)⟩⟩

private theorem potLt_of_tier1_bound {v : Pot} {m k m' k' d' : Nat}
    (hv : v = (0, 1, 0, 0) ∨ (v.1 = 1 ∧ (v.2.1 < m ∨ (v.2.1 = m ∧ v.2.2.1 ≤ k))))
    (hlt : m < m' ∨ (m = m' ∧ k < k')) :
    PotLt v (1, m', k', d') := by
  rcases hv with rfl | ⟨h1, h2 | ⟨h2, h3⟩⟩
  · exact Or.inl Nat.zero_lt_one
  · rcases hlt with hlt | ⟨rfl, _⟩
    · exact Or.inr ⟨h1, Or.inl (Nat.lt_trans h2 hlt)⟩
    · exact Or.inr ⟨h1, Or.inl h2⟩
  · rcases hlt with hlt | ⟨rfl, hlt⟩
    · exact Or.inr ⟨h1, Or.inl (h2.symm ▸ hlt)⟩
    · exact Or.inr ⟨h1, Or.inr ⟨h2, Or.inl (Nat.lt_of_le_of_lt h3 hlt)⟩⟩

private theorem potLt_of_tier1_bound_bump {v : Pot} {m k m' k' d' : Nat}
    (hv : v = (0, 1, 0, 0) ∨ (v.1 = 1 ∧ (v.2.1 < m ∨ (v.2.1 = m ∧ v.2.2.1 ≤ k))))
    (hlt : m < m' ∨ (m = m' ∧ k < k')) :
    PotLt v.bump (1, m', k', d') := by
  rcases hv with rfl | ⟨h1, h2 | ⟨h2, h3⟩⟩
  · exact Or.inl Nat.zero_lt_one
  · rcases hlt with hlt | ⟨rfl, _⟩
    · exact Or.inr ⟨h1, Or.inl (Nat.lt_trans h2 hlt)⟩
    · exact Or.inr ⟨h1, Or.inl h2⟩
  · rcases hlt with hlt | ⟨rfl, hlt⟩
    · exact Or.inr ⟨h1, Or.inl (h2.symm ▸ hlt)⟩
    · exact Or.inr ⟨h1, Or.inr ⟨h2, Or.inl (Nat.lt_of_le_of_lt h3 hlt)⟩⟩

/-- **Tier ≥ 2 local bound**: `v` lies strictly below `2 + r` in coord 1, or at `(2 + r, 0, ≤ p, _)`. -/
private def LocBoundG (v : Pot) (r p : Nat) : Prop :=
  v.1 < 2 + r ∨ (v.1 = 2 + r ∧ v.2.1 = 0 ∧ v.2.2.1 ≤ p)

private theorem LocBoundG.bump {v : Pot} {r p : Nat} (h : LocBoundG v r p) :
    LocBoundG v.bump r p := h

private theorem LocBoundG.lt_local {v : Pot} {r p p' : Nat} (h : LocBoundG v r p) (hp : p < p') :
    PotLt v (2 + r, 0, p', 0) := by
  rcases h with h1 | ⟨h1, h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, Or.inr ⟨h2, Or.inl (Nat.lt_of_le_of_lt h3 hp)⟩⟩

private theorem LocBoundG.lt_block {v : Pot} {r p w : Nat} (h : LocBoundG v r p) :
    PotLt v (2 + r, 1, 0, w) := by
  rcases h with h1 | ⟨h1, h2, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h1, Or.inl (by dsimp only; omega)⟩

/-- **Main ranking theorem**: discharges `GroupRanked` at every group `6 ≤ g < 77`. -/
theorem payloadRanked_of_run (hC : CollisionFreeRun calls E₀)
    (hbd : IxVM.Consistency.Bounded calls) (hb : BasisRowsLoaded E₀)
    (hbr : BasisRolesStored t) (hax : AxiomRolesDeclared t E₀)
    (hpin : PreludePinned t) (hcheck : t.check = .ok ())
    (hroots : RootsSafe t E₀) (hstep : RunStepStores calls t E₀)
    (hvalAll : ∀ k, ∀ r ∈ roleGroup k, RoleValidationIn calls bAddr t k r)
    (hws : ∀ k, ∃ recs, GroupWalked calls bAddr t E₀ k recs) :
    ∀ g, 6 ≤ g → g < 77 →
      ∃ rank, GroupRanked t E₀ (runPayload calls bAddr t) g (runFamOf calls bAddr t E₀ g)
        (runAdv calls bAddr t g) (runCont calls bAddr t g) rank := by
  have hP := payloadFacts_of_run hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll hws
  intro g hg6 hg77
  have hvl : valLimit g < 77 := Nat.lt_of_le_of_lt (valLimit_le g) hg77
  obtain ⟨recs, hw⟩ := hws g
  have hcl_g := groupStore_usedClosed_all hC hb hbr hax hP hws g hg6
  have hcl' := groupStore_usedClosed_all hC hb hbr hax hP hws (g + 1) (Nat.le_succ_of_le hg6)
  have hrec_g : ∀ y c, recordOf (groupStore t E₀ (runPayload calls bAddr t) g) y = some c →
      recordOf E₀ y = some c := fun y c hy => ((groupStore_recordOf hb hg6).mp hy).2
  have halr_g : ∀ y, AlreadyStoredRole t g y → StoredAtG calls bAddr t E₀ g y := by
    intro y hst
    have hsb := storedBelow_of_alreadyStored (E₀ := E₀) (Pay := runPayload calls bAddr t) hbr hst
    obtain ⟨cy, hcy⟩ := storedBelow_record hC hb hax hP hws hsb
    rw [StoredAtG, (groupStore_recordOf hb hg6).mpr ⟨hsb, hcy⟩]
    rfl
  let pot := potG calls bAddr t E₀ g recs
  let pot0 := pot0G calls bAddr t E₀ g recs
  let rank := potRank E₀.consts.keys pot
  have hltRank : ∀ {z y}, (∃ c, recordOf E₀ z = some c) → PotLt (pot z) (pot y) →
      rank z < rank y := by
    intro z y ⟨c, hc⟩ hlt
    exact potRank_lt (mem_keys_of_recordOf hc) hlt
  have hnew_or_stored_of_held' : ∀ y,
      (recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) y).isSome = true →
      NewAtG calls bAddr t E₀ g y ∨ StoredAtG calls bAddr t E₀ g y := by
    intro y hy
    cases hg' : recordOf (groupStore t E₀ (runPayload calls bAddr t) g) y with
    | none => exact Or.inl ⟨hy, hg'⟩
    | some _ => exact Or.inr (by rw [StoredAtG, hg']; rfl)
  -- Helper: no `New` modeled block with a `FamilyCallAtLim` can be Tier 0, Tier 1, `NewRecAnch`,
  -- or `LocalAtG` of any family check.
  have hmodeled_pot : ∀ B rb cs, NewAtG calls bAddr t E₀ g B → ModeledRouteAt calls B →
      FamilyCallAtLim calls bAddr t B rb (some (valLimit g)) cs →
      pot B = (2 + walkRank recs B, 1, 0, 0) := by
    intro B rb cs hnewB hmodB hfcB
    have hgrB := new_modeledBlock_groupReach hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll
      hws hg6 hg77 hnewB hmodB hfcB
    obtain ⟨cb, ms, hcb, hms, hpos, hallIndc⟩ :=
      familyCall_block_indc_nonempty hC.runStore hC.hashedStored hfcB
    have hnpB : ¬ IsProj cb := fun hp => proj_not_block hp ⟨ms, hms⟩
    have hnotRecBlock : ∀ B' cs', FamilyCallAtLim calls bAddr t B' B (some (valLimit g)) cs' → False := by
      intro B' cs' hfc'
      obtain ⟨c', rs, hc', -, hrs, -, hallRec, -⟩ :=
        familyCall_isTwinShape hC.runStore hC.hashedStored hvl hfc'
      have ec : c' = cb := Option.some.inj (hc'.symm.trans hcb)
      subst ec
      have ers : rs = ms := Ixon.ConstantInfo.muts.inj (hrs.symm.trans hms)
      subst rs
      have hm0 : ms[0] ∈ ms.toList := Array.getElem_mem_toList hpos
      have hbi : Core.Specs.Callees.isIndc ms[0] = true :=
        (List.length_filter_eq_length_iff.mp (by simpa [Array.length_toList] using hallIndc)) _ hm0
      obtain ⟨r, hr⟩ := hallRec _ hm0
      rw [hr] at hbi
      simp [Core.Specs.Callees.isIndc, Core.isIndc] at hbi
    have hnotAdv : ∀ B' rb' cs' advAs' (k : Nat) (hk : k < advAs'.length),
        FamilyCallExact calls bAddr t B' rb' (some (valLimit g)) cs' advAs' →
        Core.ixAddr (advAs'[k]'hk) = B → False := by
      intro B' rb' cs' advAs' k hk hex' hEq
      obtain ⟨outs, hU⟩ := hex'.unpack hC hbd
      have hfacts := hU.adviceFacts k hk
      rw [hEq] at hfacts
      obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
      have ec : ca = cb := Option.some.inj (hca.symm.trans hcb)
      subst ec
      rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨_, _, -, -, hnat⟩ | ⟨hpr, -⟩
      · rw [hms] at hd; cases hd
      · rw [hms] at hrc; cases hrc
      · exact not_modeledRouteAt_of_nativeObs hnat hmodB
      · exact proj_not_block hpr ⟨ms, hms⟩
    have h0 : ¬ StoredStandaloneCont calls bAddr t E₀ g B := by
      rintro ⟨⟨c', rc', hc', hrc'⟩, -⟩
      rw [Option.some.inj (hc'.symm.trans hcb), hms] at hrc'; cases hrc'
    have h1 : ¬ StoredAnchored calls bAddr t E₀ g B := by
      rintro ⟨m, k, ⟨B', rb', cs', advAs', j, hj, hsf, hEq, -⟩ | ⟨B', cs', advAs', hsf, -⟩⟩
      · exact hnotAdv B' rb' cs' advAs' j hj hsf.2.2 hEq
      · exact hnotRecBlock B' cs' (FamilyCallExact.toCall hsf.2.2)
    have h2 : ¬ NewRecAnch calls bAddr t E₀ g B := by
      rintro ⟨B', cs', advAs', hnf⟩
      exact hnotRecBlock B' cs' (FamilyCallExact.toCall hnf.2.2.2)
    have hnoLoc : ∀ B' rb' cs' advAs' p, NewFamCall calls bAddr t E₀ g B' rb' cs' advAs' →
        LocalAtG calls bAddr t E₀ g B' rb' cs' advAs' B p → False := by
      rintro B' rb' cs' advAs' p hnf (⟨-, ⟨c', rc', hc', hrc'⟩, -⟩ | ⟨j, hj, -, hEq, -⟩)
      · rw [Option.some.inj (hc'.symm.trans hcb), hms] at hrc'; cases hrc'
      · exact hnotAdv B' rb' cs' advAs' j hj hnf.2.2.2 hEq
    have hmu : muG calls bAddr t E₀ g recs B = walkRank recs B := by
      have hex : ∃ k, AnchorG calls bAddr t E₀ g recs B k := ⟨walkRank recs B, Or.inl ⟨hgrB, rfl⟩⟩
      rcases muG_spec hex with ⟨-, heq⟩ | ⟨B', rb', cs', advAs', p, hnf, hloc, -⟩
      · exact heq
      · exact (hnoLoc B' rb' cs' advAs' p hnf hloc).elim
    have hnoAt : ¬ ∃ p, AtMuG calls bAddr t E₀ g recs B p := by
      rintro ⟨p, B', rb', cs', advAs', hnf, hloc, -⟩
      exact hnoLoc B' rb' cs' advAs' p hnf hloc
    rw [show pot B = pot0 B from potG_notProj hcb hnpB,
      show pot0 B = (2 + muG calls bAddr t E₀ g recs B, 1, 0, 0) from pot0G_own h0 h1 h2 hnoAt, hmu]
  -- Helper: potential of a `NewRecAnch` `rb` of `NewFamCall B rb cs advAs`.
  have hnewRec_pot : ∀ B rb cs advAs, NewFamCall calls bAddr t E₀ g B rb cs advAs →
      pot rb = (2 + walkRank recs B, 1, 0, 2) := by
    intro B rb cs advAs hnf
    obtain ⟨crb, rs, hcrb, -, hrs, hpos, hallRec, -⟩ :=
      familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hnf.2.2.2)
    have hnp : ¬ IsProj crb := fun hp => proj_not_block hp ⟨rs, hrs⟩
    have h0 : ¬ StoredStandaloneCont calls bAddr t E₀ g rb := by
      rintro ⟨⟨c', rc', hc', hrc'⟩, -⟩
      rw [Option.some.inj (hc'.symm.trans hcrb), hrs] at hrc'; cases hrc'
    have h1 : ¬ StoredAnchored calls bAddr t E₀ g rb := by
      rintro ⟨m, k, ⟨B', rb', cs', advAs', j, hj, hsf, hEq, -⟩ | ⟨B', cs', advAs', hsf, -⟩⟩
      · obtain ⟨outs, hU⟩ := hsf.2.2.unpack hC hbd
        have hfacts := hU.adviceFacts j hj
        rw [hEq] at hfacts
        obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
        have ec : ca = crb := Option.some.inj (hca.symm.trans hcrb)
        subst ec
        rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms', hms', hallI, -, -⟩ | ⟨hp, -⟩
        · rw [hrs] at hd; cases hd
        · rw [hrs] at hrc; cases hrc
        · have ems : ms' = rs := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hrs)
          subst ms'
          obtain ⟨ind, hind⟩ := hallI rs[0] (Array.getElem_mem_toList hpos)
          obtain ⟨r, hr⟩ := hallRec rs[0] (Array.getElem_mem_toList hpos)
          rw [hind] at hr; cases hr
        · exact proj_not_block hp ⟨rs, hrs⟩
      · have eB : B' = B := familyCall_block_unique hC hbd hvl hvl
          (FamilyCallExact.toCall hsf.2.2) (FamilyCallExact.toCall hnf.2.2.2)
        subst eB
        have hstB := hsf.1
        rw [StoredAtG, hnf.1.2] at hstB
        cases hstB
    have h2 : NewRecAnch calls bAddr t E₀ g rb := ⟨B, cs, advAs, hnf⟩
    have huniq : ∀ B' cs' advAs', NewFamCall calls bAddr t E₀ g B' rb cs' advAs' → B' = B :=
      fun B' cs' advAs' hnf' => familyCall_block_unique hC hbd hvl hvl
        (FamilyCallExact.toCall hnf'.2.2.2) (FamilyCallExact.toCall hnf.2.2.2)
    rw [show pot rb = pot0 rb from potG_notProj hcrb hnp,
      show pot0 rb = (2 + walkRank recs B, 1, 0, 2) from pot0G_newRec h0 h1 h2 huniq]
  -- Helper: any `New` node `x` with `GroupReach g x` has `(pot x).1 ≤ 2 + walkRank recs x`.
  have hpot_fst_le_walkRank : ∀ x, NewAtG calls bAddr t E₀ g x → GroupReach t E₀ g x →
      (pot x).1 ≤ 2 + walkRank recs x := by
    have hpot0_le : ∀ y, NewAtG calls bAddr t E₀ g y → GroupReach t E₀ g y →
        (pot0 y).1 ≤ 2 + walkRank recs y := by
      intro y hnewY hgrY
      by_cases h0 : StoredStandaloneCont calls bAddr t E₀ g y
      · rw [show pot0 y = (0, 1, 0, 0) from pot0G_tier0 h0]; omega
      · by_cases h1 : StoredAnchored calls bAddr t E₀ g y
        · rw [show pot0 y = (1, _, _, 0) from pot0G_tier1 h0 h1]; omega
        · by_cases h2 : NewRecAnch calls bAddr t E₀ g y
          · obtain ⟨B', cs', advAs', hnf'⟩ := h2
            have huniq : ∀ B'' cs'' advAs'', NewFamCall calls bAddr t E₀ g B'' y cs'' advAs'' →
                B'' = B' := fun B'' cs'' advAs'' hnf'' =>
              familyCall_block_unique hC hbd hvl hvl
                (FamilyCallExact.toCall hnf''.2.2.2) (FamilyCallExact.toCall hnf'.2.2.2)
            rw [show pot0 y = (2 + walkRank recs B', 1, 0, 2) from
              pot0G_newRec h0 h1 ⟨B', cs', advAs', hnf'⟩ huniq]
            have hpos := new_famRec_pathPos_block hC hbd hb hg6 hg77 hcl' hnf'.1
              (FamilyCallExact.toCall hnf'.2.2.2)
            have hlt := pathPos_walkRank_lt hC.hashedStored hw hrec_g hcl_g halr_g hgrY hpos hnf'.1.2
            dsimp only; omega
          · have hmu : muG calls bAddr t E₀ g recs y ≤ walkRank recs y :=
              muG_le (Or.inl ⟨hgrY, rfl⟩)
            by_cases ha : ∃ p, AtMuG calls bAddr t E₀ g recs y p
            · rw [show pot0 y = _ from pot0G_atMu h0 h1 h2 ha]; dsimp only; omega
            · rw [show pot0 y = _ from pot0G_own h0 h1 h2 ha]; dsimp only; omega
    intro x hnewX hgrX
    obtain ⟨cx, hcxE, -, -, -⟩ := new_groupStore hb hg6 hnewX
    by_cases hp : IsProj cx
    · by_cases hst : StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf x cx)
      · rw [show pot x = (0, 0, 0, 0) from potG_storedProj hcxE hp hst]; omega
      · rw [show pot x = (pot0 (Ix.Cert.ownerOf x cx)).bump from potG_newProj hcxE hp hst]
        have hgrOwn := GroupReach.owner hgrX hcxE hp
        obtain ⟨y, -, hyx⟩ := hgrOwn.listed hC.hashedStored hw
        have hownE : recordOf E₀ (Ix.Cert.ownerOf x cx) = some y.c := by
          rw [← hyx]; exact topRec_recordOf hC.hashedStored y
        have hnewOwn : NewAtG calls bAddr t E₀ g (Ix.Cert.ownerOf x cx) := by
          rcases hnew_or_stored_of_held' (Ix.Cert.ownerOf x cx)
            (by rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
              ⟨storedBelow_of_adds hg6 (GroupAdds.reach hgrOwn), hownE⟩]; rfl) with hn | hs
          · exact hn
          · exact absurd hs hst
        have hle := hpot0_le (Ix.Cert.ownerOf x cx) hnewOwn hgrOwn
        have hlt := walkRank_owner_lt hC.hashedStored hw (hgrX.listed hC.hashedStored hw) hcxE hp
        simp only [Pot.bump_fst]; omega
    · rw [show pot x = pot0 x from potG_notProj hcxE hp]
      exact hpot0_le x hnewX hgrX
  -- Helper: any `New` node `y` reached from a `New` walk-reached `B` by `PathPos E₀ B y` has
  -- `(pot y).1 < 2 + walkRank recs B` (and same for any `New` `IsProj` with owner `y`).
  have hpathPos_lt : ∀ B y, GroupReach t E₀ g B → PathPos E₀ B y → NewAtG calls bAddr t E₀ g y →
      (pot y).1 < 2 + walkRank recs B := by
    intro B y hgrB hpos hnewY
    have hgrY : GroupReach t E₀ g y := by
      rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g (Or.inl hgrB) hpos.toReach with
        h | hst
      · exact h
      · rw [hnewY.2] at hst; cases hst
    have hlt := pathPos_walkRank_lt hC.hashedStored hw hrec_g hcl_g halr_g hgrB hpos hnewY.2
    have hle := hpot_fst_le_walkRank y hnewY hgrY
    omega
  have hpathPos_proj_lt : ∀ B blk x cx, GroupReach t E₀ g B → PathPos E₀ B blk →
      recordOf E₀ x = some cx → IsProj cx → Ix.Cert.ownerOf x cx = blk →
      NewAtG calls bAddr t E₀ g x → (pot x).1 < 2 + walkRank recs B := by
    intro B blk x cx hgrB hpos hcx hp hown hnewX
    by_cases hst : StoredAtG calls bAddr t E₀ g blk
    · rw [show pot x = (0, 0, 0, 0) from potG_storedProj hcx hp (hown ▸ hst)]; omega
    · rw [show pot x = (pot0 blk).bump from by
        dsimp only [pot, pot0]; rw [← hown]; exact potG_newProj hcx hp (hown ▸ hst)]
      have hgrBlk : GroupReach t E₀ g blk := by
        rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g (Or.inl hgrB) hpos.toReach with
          h | hs
        · exact h
        · exact absurd hs hst
      obtain ⟨y, -, hyb⟩ := hgrBlk.listed hC.hashedStored hw
      have hblkE : recordOf E₀ blk = some y.c := by
        rw [← hyb]; exact topRec_recordOf hC.hashedStored y
      have hnewBlk : NewAtG calls bAddr t E₀ g blk := by
        rcases hnew_or_stored_of_held' blk
          (by rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
            ⟨storedBelow_of_adds hg6 (GroupAdds.reach hgrBlk), hblkE⟩]; rfl) with hn | hs
        · exact hn
        · exact absurd hs hst
      have hlt := hpathPos_lt B blk hgrB hpos hnewBlk
      -- `x` is a `New` `IsProj` whose owner `blk` is non-projection by `projMember`.
      obtain ⟨-, -, -, haddX, -⟩ := new_groupStore hb hg6 hnewX
      obtain ⟨cblk, hcblk', hca⟩ := groupStore_projMember hC hb hax hP hg6 hw x cx hnewX
        ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
          ⟨storedBelow_of_adds hg6 haddX, hcx⟩) hp
      have hblkE' : recordOf E₀ blk = some cblk := by
        rw [← hown]; exact ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcblk').2
      have hnpBlk : ¬ IsProj cblk := by
        rcases hca with ⟨_, hst'⟩ | ⟨ms, _, _, hms, -, -⟩
        · exact fun hp' => standalone_not_proj hst' hp'
        · exact fun hp' => proj_not_block hp' ⟨ms, hms⟩
      rw [show pot blk = pot0 blk from potG_notProj hblkE' hnpBlk] at hlt
      simp only [Pot.bump_fst]; exact hlt
  -- Helper: `LocalAtG` gives `LocBoundG (pot x) (walkRank recs B) p`.
  have hlocal_bound : ∀ B rb cs advAs x p, NewFamCall calls bAddr t E₀ g B rb cs advAs →
      LocalAtG calls bAddr t E₀ g B rb cs advAs x p → NewAtG calls bAddr t E₀ g x →
      LocBoundG (pot x) (walkRank recs B) p := by
    intro B rb cs advAs x p hnf hloc hnewX
    obtain ⟨cx, hcxE, -, -, -⟩ := new_groupStore hb hg6 hnewX
    have hnp : ¬ IsProj cx := by
      rcases hloc with ⟨-, ⟨c', rc', hc', hrc'⟩, -⟩ | ⟨_, _, -, -, c', hc', hnp'⟩
      · rw [← Option.some.inj (hc'.symm.trans hcxE)]
        exact fun hp => standalone_not_proj (Or.inr (Or.inl ⟨rc', hrc'⟩)) hp
      · rw [← Option.some.inj (hc'.symm.trans hcxE)]; exact hnp'
    rw [show pot x = pot0 x from potG_notProj hcxE hnp]
    by_cases h0 : StoredStandaloneCont calls bAddr t E₀ g x
    · rw [show pot0 x = (0, 1, 0, 0) from pot0G_tier0 h0]; left; omega
    · by_cases h1 : StoredAnchored calls bAddr t E₀ g x
      · rw [show pot0 x = (1, _, _, 0) from pot0G_tier1 h0 h1]; left; omega
      · by_cases h2 : NewRecAnch calls bAddr t E₀ g x
        · exfalso
          obtain ⟨B', cs', advAs', hnf'⟩ := h2
          obtain ⟨crb, rs, hcrb, -, hrs, hpos, hallRec, -⟩ :=
            familyCall_isTwinShape hC.runStore hC.hashedStored hvl
              (FamilyCallExact.toCall hnf'.2.2.2)
          rcases hloc with ⟨-, ⟨c', rc', hc', hrc'⟩, -⟩ | ⟨j, hj, -, hEq, -⟩
          · rw [Option.some.inj (hc'.symm.trans hcrb), hrs] at hrc'; cases hrc'
          · obtain ⟨outs, hU⟩ := hnf.2.2.2.unpack hC hbd
            have hfacts := hU.adviceFacts j hj
            rw [hEq] at hfacts
            obtain ⟨-, ca, hca, -, hkind, -⟩ := hfacts
            have ec : ca = crb := Option.some.inj (hca.symm.trans hcrb)
            subst ec
            rcases hkind with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms', hms', hallI, -, -⟩ | ⟨hp, -⟩
            · rw [hrs] at hd; cases hd
            · rw [hrs] at hrc; cases hrc
            · have ems : ms' = rs := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hrs)
              subst ms'
              obtain ⟨ind, hind⟩ := hallI rs[0] (Array.getElem_mem_toList hpos)
              obtain ⟨r, hr⟩ := hallRec rs[0] (Array.getElem_mem_toList hpos)
              rw [hind] at hr; cases hr
            · exact proj_not_block hp ⟨rs, hrs⟩
        · have hmu : muG calls bAddr t E₀ g recs x ≤ walkRank recs B :=
            muG_le (Or.inr ⟨B, rb, cs, advAs, p, hnf, hloc, rfl⟩)
          rcases Nat.lt_or_eq_of_le hmu with hlt | heq
          · by_cases ha : ∃ q, AtMuG calls bAddr t E₀ g recs x q
            · rw [show pot0 x = _ from pot0G_atMu h0 h1 h2 ha]; left; dsimp only; omega
            · rw [show pot0 x = _ from pot0G_own h0 h1 h2 ha]; left; dsimp only; omega
          · have ha : AtMuG calls bAddr t E₀ g recs x p := ⟨B, rb, cs, advAs, hnf, hloc, heq.symm⟩
            rw [show pot0 x = _ from pot0G_atMu h0 h1 h2 ⟨p, ha⟩]
            right
            exact ⟨by dsimp only; omega, rfl, nuG_le ha⟩
  -- Helper: Tier-1 witness bound: any `New` witness `w` of `StoredFamCall B rb cs advAs` satisfies
  -- `PotLt (pot w) (1, 2 * cs.length, 0, 0)`.
  have hstored_wit_lt : ∀ B rb cs advAs w, StoredFamCall calls bAddr t E₀ g B rb cs advAs →
      ((∃ ro : Ix.Kernel.Role, t.addressOf? ro = some w ∧
          Ix.SpecDigest.groupOf ro < 6 ∧
          (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
        (PathPos E₀ B w ∧ Claim.NotBlockIn calls w ∧
          ∃ c, recordOf E₀ w = some c ∧
            (IsProj c → usedRefIdxs c = [] ∧
              ∃ cb, recordOf E₀ (Ix.Cert.ownerOf w c) = some cb ∧
                ConstAddrOf (Ix.Cert.ownerOf w c) cb w)) ∨
        (DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs w ∧
          ∃ ib, PathPos E₀ B ib ∧
            ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
              Claim.RCLimRep t bAddr (some (valLimit g)) h₁ rc₁ ∧
              Core.S0.addr h₁ xx₁ w ∧ Core.S0.addr h₁ xib₁ ib ∧
              ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
              (∀ cl ∈ cs₁, cl ∈ calls) ∧ cs₁.length < cs.length) ∨
        (∃ ib c cib, PathPos E₀ B ib ∧ recordOf E₀ w = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf w c = ib ∧ usedRefIdxs c = [] ∧
          recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib w)) →
      NewAtG calls bAddr t E₀ g w →
      PotLt (pot w) (1, 2 * cs.length, 0, 0) := by
    intro B rb cs advAs w hsf hwCls hnewW
    rcases hwCls with ⟨ro, had, hlt, hk⟩ | ⟨hpos, -, -⟩ |
        ⟨hdc, ib, hposIb, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, hrc₁, hxx₁, hxib₁, evCr, hsubCr,
          hlen₁⟩ |
        ⟨ib, cw, -, hposIb, hcw, hpw, hownw, -, -, -⟩
    · have hstW := halr_g w (basisRole_alreadyStoredRole hg6 had hlt hk)
      rw [StoredAtG, hnewW.2] at hstW; cases hstW
    · have hstW := pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1 hpos.toReach
      rw [hnewW.2] at hstW; cases hstW
    · obtain ⟨cw, hcwE, -, -, -⟩ := new_groupStore hb hg6 hnewW
      rcases check_container_rec_shape hC hbd hxx₁ hxib₁ evCr hsubCr hcwE with
        ⟨rc, hrc⟩ | ⟨rp, hrp⟩
      · have hnp : ¬ IsProj cw := fun hp => standalone_not_proj (Or.inr (Or.inl ⟨rc, hrc⟩)) hp
        rw [show pot w = pot0 w from potG_notProj hcwE hnp,
          show pot0 w = (0, 1, 0, 0) from pot0G_tier0 ⟨⟨cw, rc, hcwE, hrc⟩, B, rb, cs, advAs, hsf, hdc⟩]
        exact Or.inl (by omega)
      · have hstIb : StoredAtG calls bAddr t E₀ g ib :=
          pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1 hposIb.toReach
        have hpw : IsProj cw := Or.inr (Or.inr (Or.inr ⟨rp, hrp⟩))
        have hownEq : Ix.Cert.ownerOf w cw = rp.block := by simp [Ix.Cert.ownerOf, hrp]
        by_cases hstBlk : StoredAtG calls bAddr t E₀ g rp.block
        · rw [show pot w = (0, 0, 0, 0) from potG_storedProj hcwE hpw (hownEq ▸ hstBlk)]
          exact Or.inl (by omega)
        · rw [show pot w = (pot0 rp.block).bump from by
            dsimp only [pot, pot0]; rw [← hownEq]; exact potG_newProj hcwE hpw (hownEq ▸ hstBlk)]
          obtain ⟨cs', advAs', hmodIb, hex', hlen'⟩ :=
            check_container_rec_rprj_family_lt_len hC hbd hstep hrc₁ hxx₁ hxib₁ evCr hsubCr hcwE hrp
          have hcand : StoredCand calls bAddr t E₀ g rp.block (2 * cs'.length + 1, 0) :=
            Or.inr ⟨ib, cs', advAs', ⟨hstIb, hmodIb, hex'⟩, rfl⟩
          exact potLt_of_tier1_bound_bump (pot0G_le_tier1 hcand)
            (Or.inl (by omega))
    · have hstIb : StoredAtG calls bAddr t E₀ g ib :=
        pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1 hposIb.toReach
      rw [show pot w = (0, 0, 0, 0) from potG_storedProj hcw hpw (hownw ▸ hstIb)]
      exact Or.inl (by omega)
  -- Helper: Tier ≥ 2 witness bound: any `New` witness `w` of `NewFamCall B rb cs advAs` satisfies
  -- `LocBoundG (pot w) (walkRank recs B) 0` (and strictly `< 2 + walkRank recs B` if non-`.recr`).
  have hnew_wit_bound : ∀ B rb cs advAs w, NewFamCall calls bAddr t E₀ g B rb cs advAs →
      ((∃ ro : Ix.Kernel.Role, t.addressOf? ro = some w ∧
          Ix.SpecDigest.groupOf ro < 6 ∧
          (RoleVal.roleWalksBound ro = true ∨ RoleVal.isQuotRole ro = true)) ∨
        (PathPos E₀ B w ∧ Claim.NotBlockIn calls w ∧
          ∃ c, recordOf E₀ w = some c ∧
            (IsProj c → usedRefIdxs c = [] ∧
              ∃ cb, recordOf E₀ (Ix.Cert.ownerOf w c) = some cb ∧
                ConstAddrOf (Ix.Cert.ownerOf w c) cb w)) ∨
        (DirectContOwn calls bAddr t B rb (some (valLimit g)) cs advAs w ∧
          ∃ ib, PathPos E₀ B ib ∧
            ∃ (h₁ h₂ : Heap F) (rc₁ xx₁ xib₁ r₁ : SourceValue F) (cs₁ : List (Call F)),
              Claim.RCLimRep t bAddr (some (valLimit g)) h₁ rc₁ ∧
              Core.S0.addr h₁ xx₁ w ∧ Core.S0.addr h₁ xib₁ ib ∧
              ObsFn Obs.W "KernelModeled::check_container_rec" [rc₁, xx₁, xib₁] h₁ r₁ h₂ cs₁ ∧
              (∀ cl ∈ cs₁, cl ∈ calls) ∧ cs₁.length < cs.length) ∨
        (∃ ib c cib, PathPos E₀ B ib ∧ recordOf E₀ w = some c ∧ IsProj c ∧
          Ix.Cert.ownerOf w c = ib ∧ usedRefIdxs c = [] ∧
          recordOf E₀ ib = some cib ∧ ConstAddrOf ib cib w)) →
      NewAtG calls bAddr t E₀ g w →
      LocBoundG (pot w) (walkRank recs B) 0 ∧
        ((∀ cw rc, recordOf E₀ w = some cw → cw.info ≠ .recr rc) →
          (pot w).1 < 2 + walkRank recs B) := by
    intro B rb cs advAs w hnf hwCls hnewW
    rcases hwCls with ⟨ro, had, hlt, hk⟩ | ⟨hpos, -, -⟩ |
        ⟨hdc, ib, hposIb, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, hrc₁, hxx₁, hxib₁, evCr, hsubCr, -⟩ |
        ⟨ib, cw, -, hposIb, hcw, hpw, hownw, -, -, -⟩
    · have hstW := halr_g w (basisRole_alreadyStoredRole hg6 had hlt hk)
      rw [StoredAtG, hnewW.2] at hstW; cases hstW
    · have hlt := hpathPos_lt B w hnf.2.1 hpos hnewW
      exact ⟨Or.inl hlt, fun _ => hlt⟩
    · obtain ⟨cw, hcwE, -, -, -⟩ := new_groupStore hb hg6 hnewW
      rcases check_container_rec_shape hC hbd hxx₁ hxib₁ evCr hsubCr hcwE with
        ⟨rc, hrc⟩ | ⟨rp, hrp⟩
      · refine ⟨hlocal_bound B rb cs advAs w 0 hnf
            (Or.inl ⟨rfl, ⟨cw, rc, hcwE, hrc⟩, hdc⟩) hnewW,
          fun hno => (hno cw rc hcwE hrc).elim⟩
      · have hpw : IsProj cw := Or.inr (Or.inr (Or.inr ⟨rp, hrp⟩))
        have hownEq : Ix.Cert.ownerOf w cw = rp.block := by simp [Ix.Cert.ownerOf, hrp]
        have hlt : (pot w).1 < 2 + walkRank recs B := by
          by_cases hstBlk : StoredAtG calls bAddr t E₀ g rp.block
          · rw [show pot w = (0, 0, 0, 0) from potG_storedProj hcwE hpw (hownEq ▸ hstBlk)]; omega
          · rw [show pot w = (pot0 rp.block).bump from by
              dsimp only [pot, pot0]; rw [← hownEq]; exact potG_newProj hcwE hpw (hownEq ▸ hstBlk)]
            obtain ⟨cs', advAs', hmodIb, hex', -⟩ :=
              check_container_rec_rprj_family_lt_len hC hbd hstep hrc₁ hxx₁ hxib₁ evCr hsubCr hcwE hrp
            by_cases hstIb : StoredAtG calls bAddr t E₀ g ib
            · have hcand : StoredCand calls bAddr t E₀ g rp.block (2 * cs'.length + 1, 0) :=
                Or.inr ⟨ib, cs', advAs', ⟨hstIb, hmodIb, hex'⟩, rfl⟩
              dsimp only [pot0]
              rcases pot0G_le_tier1 hcand with h0 | ⟨h1, -⟩
              · rw [h0]; simp only [Pot.bump_fst]; omega
              · simp only [Pot.bump_fst, h1]; omega
            · have hgrIb : GroupReach t E₀ g ib := by
                rcases pathReach_closed_of_usedClosed hrec_g hcl_g halr_g (Or.inl hnf.2.1)
                    hposIb.toReach with h | hs
                · exact h
                · exact absurd hs hstIb
              obtain ⟨y, -, hyi⟩ := hgrIb.listed hC.hashedStored hw
              have hibE : recordOf E₀ ib = some y.c := by
                rw [← hyi]; exact topRec_recordOf hC.hashedStored y
              have hnewIb : NewAtG calls bAddr t E₀ g ib := by
                rcases hnew_or_stored_of_held' ib
                  (by rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
                    ⟨storedBelow_of_adds hg6 (GroupAdds.reach hgrIb), hibE⟩]; rfl) with hn | hs
                · exact hn
                · exact absurd hs hstIb
              have hnf' : NewFamCall calls bAddr t E₀ g ib rp.block cs' advAs' :=
                ⟨hnewIb, hgrIb, hmodIb, hex'⟩
              have hrecPot := hnewRec_pot ib rp.block cs' advAs' hnf'
              obtain ⟨crb, rs, hcrb, -, hrs, -, -, -⟩ :=
                familyCall_isTwinShape hC.runStore hC.hashedStored hvl (FamilyCallExact.toCall hex')
              rw [show pot rp.block = pot0 rp.block from
                potG_notProj hcrb (fun hp => proj_not_block hp ⟨rs, hrs⟩)] at hrecPot
              rw [hrecPot]
              have hltIb := pathPos_walkRank_lt hC.hashedStored hw hrec_g hcl_g halr_g
                hnf.2.1 hposIb hnewIb.2
              simp only [Pot.bump_fst]; omega
        exact ⟨Or.inl hlt, fun _ => hlt⟩
    · have hlt := hpathPos_proj_lt B ib w cw hnf.2.1 hposIb hcw hpw hownw hnewW
      exact ⟨Or.inl hlt, fun _ => hlt⟩
  -- Helper: `PotLt (pot x) (pot a)` for any `New` `a`, `UsedRef E₀ a x`, `New` `x`.
  have hused_potLt : ∀ a x, NewAtG calls bAddr t E₀ g a → UsedRef E₀ a x →
      NewAtG calls bAddr t E₀ g x → PotLt (pot x) (pot a) := by
    intro a x hnewA hu hnewX
    obtain ⟨ca, hcaE, -, haddA, -⟩ := new_groupStore hb hg6 hnewA
    obtain ⟨cx, hcxE, -, -, -⟩ := new_groupStore hb hg6 hnewX
    have hnpA : ¬ IsProj ca := fun hp => new_proj_no_usedRef hC hbd hb hbr hax hpin hcheck
      hroots hstep hvalAll hws hg6 hg77 hnewA hcaE hp x hu
    rw [show pot a = pot0 a from potG_notProj hcaE hnpA]
    -- Case split on which tier `pot0 a` falls in:
    by_cases h0 : StoredStandaloneCont calls bAddr t E₀ g a
    · -- Tier 0: `pot0 a = (0, 1, 0, 0)`. Every `New` `UsedRef` is `StoredProj` at `(0, 0, 0, 0)`.
      rw [show pot0 a = (0, 1, 0, 0) from pot0G_tier0 h0]
      obtain ⟨⟨c', rc, hc', hrc⟩, B, rb, cs, advAs, hsf, hdc⟩ := h0
      have ec : c' = ca := Option.some.inj (hc'.symm.trans hcaE)
      subst ec
      obtain ⟨outs, -, -, -, ⟨ib, hposIb, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, -, hxx₁, hxib₁,
          evCr, hsubCr, -⟩, hcontRefs, -, houtsCls⟩ := hdc.unpack hC hbd
      obtain ⟨ib', ⟨h₃, h₄, xx', r', cs', b_ib', hxx', evRfb', hbRep', hbEq', hsubRfb'⟩, hrefs⟩ :=
        hcontRefs c' hcaE (Or.inl ⟨rc, hrc⟩)
      obtain ⟨v26, m29, cs37, evRfb1, hres1, hsub37⟩ :=
        check_container_rec_rec_family_block hC hbd hxx₁ hxib₁ evCr hsubCr
      have eib : ib' = ib := rec_family_block_det hC hbd hxx' hxx₁ evRfb' evRfb1
        hsubRfb' hsub37 ⟨b_ib', hbRep', hbEq'⟩ hres1
      subst eib
      have hstIb : StoredAtG calls bAddr t E₀ g ib' :=
        pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1 hposIb.toReach
      have hownSelf : Ix.Cert.ownerOf a c' = a := by simp [Ix.Cert.ownerOf, hrc]
      obtain ⟨-, -, -, -, hcls⟩ := hrefs x (by rw [hownSelf]; exact hu)
      rcases hcls with huIb | ⟨c₁, -, hc₁, hp₁, hown₁, -, -, -⟩ |
          ⟨blk, c₁, -, hposBlk, hc₁, hp₁, hown₁, -, -, -⟩ | ⟨hwX, cr, hcr, hnoR, hnoRP⟩
      · have hstX := pathReach_stored_of_usedClosed hrec_g hcl_g hstIb
          (PathReach.single (Or.inl huIb))
        rw [hnewX.2] at hstX; cases hstX
      · rw [show pot x = (0, 0, 0, 0) from potG_storedProj hc₁ hp₁ (hown₁ ▸ hstIb)]
        exact Or.inr ⟨rfl, Or.inl (by decide)⟩
      · have hstBlk := pathReach_stored_of_usedClosed hrec_g hcl_g hstIb hposBlk.toReach
        rw [show pot x = (0, 0, 0, 0) from potG_storedProj hc₁ hp₁ (hown₁ ▸ hstBlk)]
        exact Or.inr ⟨rfl, Or.inl (by decide)⟩
      · rcases houtsCls x hwX with ⟨ro, had, hlt, hk⟩ | ⟨hposX, -, -⟩ |
            ⟨-, ib₂, -, h₁₂, h₂₂, rc₁₂, xx₁₂, xib₁₂, r₁₂, cs₁₂, -, hxx₁₂, hxib₁₂, evCr₂,
              hsubCr₂, -⟩ | ⟨ib₂, c₁, -, hposIb₂, hc₁, hp₁, hown₁, -, -, -⟩
        · have hstX := halr_g x (basisRole_alreadyStoredRole hg6 had hlt hk)
          rw [StoredAtG, hnewX.2] at hstX; cases hstX
        · have hstX := pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1 hposX.toReach
          rw [hnewX.2] at hstX; cases hstX
        · rcases check_container_rec_shape hC hbd hxx₁₂ hxib₁₂ evCr₂ hsubCr₂ hcr with
            ⟨rc₂, hrc₂⟩ | ⟨rp₂, hrp₂⟩
          · exact (hnoR rc₂ hrc₂).elim
          · exact (hnoRP rp₂ hrp₂).elim
        · have hstIb₂ := pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1 hposIb₂.toReach
          rw [show pot x = (0, 0, 0, 0) from potG_storedProj hc₁ hp₁ (hown₁ ▸ hstIb₂)]
          exact Or.inr ⟨rfl, Or.inl (by decide)⟩
    · by_cases h1 : StoredAnchored calls bAddr t E₀ g a
      · -- Tier 1: `pot0 a = (1, tier1M a, tier1K a, 0)`.
        rw [show pot0 a = (1, tier1M calls bAddr t E₀ g a, tier1K calls bAddr t E₀ g a, 0) from
          pot0G_tier1 h0 h1]
        rcases tier1_spec h1 with
          ⟨B, rb, cs, advAs, k, hk, hsf, hEq, hq⟩ | ⟨B, cs, advAs, hsf, hq⟩
        · -- Subcase 1A: advice record at index `k` of `StoredFamCall B rb cs advAs`
          have hmEq : tier1M calls bAddr t E₀ g a = 2 * cs.length := congrArg Prod.fst hq
          have hkEq : tier1K calls bAddr t E₀ g a = k + 1 := congrArg Prod.snd hq
          rw [hmEq, hkEq]
          obtain ⟨outs, hU⟩ := hsf.2.2.unpack hC hbd
          have hfacts := hU.adviceFacts k hk
          rw [hEq] at hfacts
          obtain ⟨-, -, -, -, -, hrefs⟩ := hfacts
          obtain ⟨-, -, -, hcls⟩ := hrefs x hu
          rcases hcls with hS | hW | ⟨blk, c₁, -, hblkS, hc₁, hp₁, hown₁, -, -, -⟩
          · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hS
            obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hb
            have hjk : j < k := by rw [List.length_take] at hj; omega
            have hjL : j < advAs.length := Nat.lt_trans hjk hk
            have hbj : advAs[j]'hjL = b := by
              rw [← hgetj, List.getElem_take]
            by_cases hpx : IsProj cx
            · -- `x` is a projection advice record at index `j < k`: its owner is at `j' < j < k`
              have hfx := hU.adviceFacts j hjL
              rw [hbj] at hfx
              obtain ⟨-, c₂, hc₂, -, hkind₂, -⟩ := hfx
              have ec : c₂ = cx := Option.some.inj (hc₂.symm.trans hcxE)
              subst ec
              rcases hkind₂ with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms, hms, -⟩ | ⟨-, -, hownS, -⟩
              · exact (standalone_not_proj (Or.inl ⟨d, hd⟩) hpx).elim
              · exact (standalone_not_proj (Or.inr (Or.inl ⟨rc, hrc⟩)) hpx).elim
              · exact (proj_not_block hpx ⟨ms, hms⟩).elim
              · by_cases hstOwn : StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf (Core.ixAddr b) c₂)
                · rw [show pot (Core.ixAddr b) = (0, 0, 0, 0) from potG_storedProj hcxE hpx hstOwn]
                  exact Or.inl (by omega)
                · rw [show pot (Core.ixAddr b) = (pot0 (Ix.Cert.ownerOf (Core.ixAddr b) c₂)).bump from
                    potG_newProj hcxE hpx hstOwn]
                  obtain ⟨b', hb', hownEq⟩ := List.mem_map.mp hownS
                  obtain ⟨j', hj', hgetj'⟩ := List.mem_iff_getElem.mp hb'
                  have hj'j : j' < j := by rw [List.length_take] at hj'; omega
                  have hj'L : j' < advAs.length := Nat.lt_trans hj'j hjL
                  have hcand : StoredCand calls bAddr t E₀ g (Ix.Cert.ownerOf (Core.ixAddr b) c₂)
                      (2 * cs.length, j' + 1) :=
                    Or.inl ⟨B, rb, cs, advAs, j', hj'L, hsf, by
                      rw [← hownEq, ← hgetj', List.getElem_take], rfl⟩
                  exact potLt_of_tier1_bound_bump (pot0G_le_tier1 hcand)
                    (Or.inr ⟨rfl, by omega⟩)
            · rw [show pot (Core.ixAddr b) = pot0 (Core.ixAddr b) from potG_notProj hcxE hpx]
              have hcand : StoredCand calls bAddr t E₀ g (Core.ixAddr b) (2 * cs.length, j + 1) :=
                Or.inl ⟨B, rb, cs, advAs, j, hjL, hsf, by rw [hbj], rfl⟩
              exact potLt_of_tier1_bound (pot0G_le_tier1 hcand) (Or.inr ⟨rfl, by omega⟩)
          · exact PotLt.trans
              (hstored_wit_lt B rb cs advAs x hsf (hU.outsClassified x hW) hnewX)
              (potLt_third (by omega))
          · by_cases hstBlk : StoredAtG calls bAddr t E₀ g blk
            · rw [show pot x = (0, 0, 0, 0) from potG_storedProj hc₁ hp₁ (hown₁ ▸ hstBlk)]
              exact Or.inl (by omega)
            · rw [show pot x = (pot0 blk).bump from by
                dsimp only [pot, pot0]; rw [← hown₁]; exact potG_newProj hc₁ hp₁ (hown₁ ▸ hstBlk)]
              obtain ⟨b, hbMem, hblkEq⟩ := List.mem_map.mp hblkS
              obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hbMem
              have hjk : j < k := by rw [List.length_take] at hj; omega
              have hjL : j < advAs.length := Nat.lt_trans hjk hk
              have hcand : StoredCand calls bAddr t E₀ g blk (2 * cs.length, j + 1) :=
                Or.inl ⟨B, rb, cs, advAs, j, hjL, hsf, by
                  rw [← hblkEq, ← hgetj, List.getElem_take], rfl⟩
              exact potLt_of_tier1_bound_bump (pot0G_le_tier1 hcand) (Or.inr ⟨rfl, by omega⟩)
        · -- Subcase 1B: family record `a` of `StoredFamCall B a cs advAs`
          have hmEq : tier1M calls bAddr t E₀ g a = 2 * cs.length + 1 := congrArg Prod.fst hq
          have hkEq : tier1K calls bAddr t E₀ g a = 0 := congrArg Prod.snd hq
          rw [hmEq, hkEq]
          obtain ⟨outs, hU⟩ := hsf.2.2.unpack hC hbd
          obtain ⟨-, -, -, hcls⟩ := hU.famRefs x hu
          rcases hcls with huB | ⟨c₁, -, hc₁, hp₁, hown₁, -, -, -⟩ |
              ⟨blk, c₁, -, hposBlk, hc₁, hp₁, hown₁, -, -, -⟩ | hW
          · have hstX := pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1
              (PathReach.single (Or.inl huB))
            rw [hnewX.2] at hstX; cases hstX
          · rw [show pot x = (0, 0, 0, 0) from potG_storedProj hc₁ hp₁ (hown₁ ▸ hsf.1)]
            exact Or.inl (by omega)
          · have hstBlk := pathReach_stored_of_usedClosed hrec_g hcl_g hsf.1 hposBlk.toReach
            rw [show pot x = (0, 0, 0, 0) from potG_storedProj hc₁ hp₁ (hown₁ ▸ hstBlk)]
            exact Or.inl (by omega)
          · exact PotLt.trans
              (hstored_wit_lt B a cs advAs x hsf (hU.outsClassified x hW) hnewX)
              (Or.inr ⟨rfl, Or.inl (by dsimp only; omega)⟩)
      · by_cases h2 : NewRecAnch calls bAddr t E₀ g a
        · -- Tier ≥ 2 `NewRecAnch`: `pot0 a = (2 + walkRank recs B, 1, 0, 2)`.
          obtain ⟨B, cs, advAs, hnf⟩ := h2
          have huniq : ∀ B' cs' advAs', NewFamCall calls bAddr t E₀ g B' a cs' advAs' → B' = B :=
            fun B' cs' advAs' hnf' => familyCall_block_unique hC hbd hvl hvl
              (FamilyCallExact.toCall hnf'.2.2.2) (FamilyCallExact.toCall hnf.2.2.2)
          rw [show pot0 a = (2 + walkRank recs B, 1, 0, 2) from
            pot0G_newRec h0 h1 ⟨B, cs, advAs, hnf⟩ huniq]
          obtain ⟨outs, hU⟩ := hnf.2.2.2.unpack hC hbd
          obtain ⟨-, -, -, hcls⟩ := hU.famRefs x hu
          rcases hcls with huB | ⟨c₁, cb, hc₁, hp₁, hown₁, -, hcb, -⟩ |
              ⟨blk, c₁, -, hposBlk, hc₁, hp₁, hown₁, -, -, -⟩ | hW
          · exact Or.inl (hpathPos_lt B x hnf.2.1 (PathPos.single (Or.inl huB)) hnewX)
          · have hnsB : ¬ StoredAtG calls bAddr t E₀ g B := by
              rw [StoredAtG, hnf.1.2]; simp
            rw [show pot x = (pot0 B).bump from by
              dsimp only [pot, pot0]; rw [← hown₁]; exact potG_newProj hc₁ hp₁ (hown₁ ▸ hnsB)]
            have hBpot := hmodeled_pot B a cs hnf.1 hnf.2.2.1 (FamilyCallExact.toCall hnf.2.2.2)
            obtain ⟨cb', ms', hcb', hms', -, -⟩ :=
              familyCall_block_indc_nonempty hC.runStore hC.hashedStored
                (FamilyCallExact.toCall hnf.2.2.2)
            rw [show pot B = pot0 B from potG_notProj hcb' (fun hp => proj_not_block hp ⟨ms', hms'⟩)] at hBpot
            rw [hBpot]
            dsimp only [Pot.bump]
            exact potLt_fourth (by omega)
          · exact Or.inl (hpathPos_proj_lt B blk x c₁ hnf.2.1 hposBlk hc₁ hp₁ hown₁ hnewX)
          · exact (hnew_wit_bound B a cs advAs x hnf (hU.outsClassified x hW) hnewX).1.lt_block
        · -- Tier ≥ 2 ordinary (`AtMu` or `GroupReach` or `stdAxiom`).
          by_cases ha : ∃ p, AtMuG calls bAddr t E₀ g recs a p
          · rw [show pot0 a = (2 + muG calls bAddr t E₀ g recs a, 0,
                nuG calls bAddr t E₀ g recs a, 0) from pot0G_atMu h0 h1 h2 ha]
            obtain ⟨B, rb, cs, advAs, hnf, hloc, hBmu⟩ := nuG_spec ha
            rw [← hBmu]
            rcases hloc with ⟨hp0, ⟨c', rc, hc', hrc⟩, hdc⟩ | ⟨k, hk, hpk, hEq, -⟩
            · -- `p = 0`: standalone container recursor of `NewFamCall B rb cs advAs`
              have ec : c' = ca := Option.some.inj (hc'.symm.trans hcaE)
              subst ec
              obtain ⟨outs, -, -, -, ⟨ib, hposIb, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, -, hxx₁, hxib₁,
                  evCr, hsubCr, -⟩, hcontRefs, -, houtsCls⟩ := hdc.unpack hC hbd
              obtain ⟨ib', ⟨h₃, h₄, xx', r', cs', b_ib', hxx', evRfb', hbRep', hbEq', hsubRfb'⟩,
                  hrefs⟩ := hcontRefs c' hcaE (Or.inl ⟨rc, hrc⟩)
              obtain ⟨v26, m29, cs37, evRfb1, hres1, hsub37⟩ :=
                check_container_rec_rec_family_block hC hbd hxx₁ hxib₁ evCr hsubCr
              have eib : ib' = ib := rec_family_block_det hC hbd hxx' hxx₁ evRfb' evRfb1
                hsubRfb' hsub37 ⟨b_ib', hbRep', hbEq'⟩ hres1
              subst eib
              have hownSelf : Ix.Cert.ownerOf a c' = a := by simp [Ix.Cert.ownerOf, hrc]
              obtain ⟨-, -, -, -, hcls⟩ := hrefs x (by rw [hownSelf]; exact hu)
              rcases hcls with huIb | ⟨c₁, -, hc₁, hp₁, hown₁, -, -, -⟩ |
                  ⟨blk, c₁, -, hposBlk, hc₁, hp₁, hown₁, -, -, -⟩ | ⟨hW, cr, hcr, hnoR, hnoRP⟩
              · exact Or.inl (hpathPos_lt B x hnf.2.1 (hposIb.tail (Or.inl huIb)) hnewX)
              · exact Or.inl (hpathPos_proj_lt B ib' x c₁ hnf.2.1 hposIb hc₁ hp₁ hown₁ hnewX)
              · exact Or.inl (hpathPos_proj_lt B blk x c₁ hnf.2.1
                  (hposIb.trans_reach hposBlk.toReach) hc₁ hp₁ hown₁ hnewX)
              · exact Or.inl ((hnew_wit_bound B rb cs advAs x hnf (houtsCls x hW) hnewX).2
                  fun cw rc' hcw => by
                    rw [Option.some.inj (hcw.symm.trans hcr)]; exact hnoR rc')
            · -- `p = k + 1`: non-proj advice record at index `k` of `NewFamCall B rb cs advAs`
              rw [hpk]
              obtain ⟨outs, hU⟩ := hnf.2.2.2.unpack hC hbd
              have hfacts := hU.adviceFacts k hk
              rw [hEq] at hfacts
              obtain ⟨-, -, -, -, -, hrefs⟩ := hfacts
              obtain ⟨-, -, -, hcls⟩ := hrefs x hu
              rcases hcls with hS | hW | ⟨blk, c₁, -, hblkS, hc₁, hp₁, hown₁, -, -, -⟩
              · obtain ⟨b, hbMem, rfl⟩ := List.mem_map.mp hS
                obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hbMem
                have hjk : j < k := by rw [List.length_take] at hj; omega
                have hjL : j < advAs.length := Nat.lt_trans hjk hk
                have hbj : advAs[j]'hjL = b := by rw [← hgetj, List.getElem_take]
                by_cases hpx : IsProj cx
                · have hfx := hU.adviceFacts j hjL
                  rw [hbj] at hfx
                  obtain ⟨-, c₂, hc₂, -, hkind₂, -⟩ := hfx
                  have ec : c₂ = cx := Option.some.inj (hc₂.symm.trans hcxE)
                  subst ec
                  rcases hkind₂ with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms, hms, -⟩ | ⟨-, -, hownS, cb', hcb', hca'⟩
                  · exact (standalone_not_proj (Or.inl ⟨d, hd⟩) hpx).elim
                  · exact (standalone_not_proj (Or.inr (Or.inl ⟨rc, hrc⟩)) hpx).elim
                  · exact (proj_not_block hpx ⟨ms, hms⟩).elim
                  · by_cases hstOwn : StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf (Core.ixAddr b) c₂)
                    · rw [show pot (Core.ixAddr b) = (0, 0, 0, 0) from potG_storedProj hcxE hpx hstOwn]
                      exact Or.inl (by omega)
                    · rw [show pot (Core.ixAddr b) = (pot0 (Ix.Cert.ownerOf (Core.ixAddr b) c₂)).bump from
                        potG_newProj hcxE hpx hstOwn]
                      obtain ⟨b', hb', hownEq⟩ := List.mem_map.mp hownS
                      obtain ⟨j', hj', hgetj'⟩ := List.mem_iff_getElem.mp hb'
                      have hj'j : j' < j := by rw [List.length_take] at hj'; omega
                      have hj'L : j' < advAs.length := Nat.lt_trans hj'j hjL
                      have hnpOwn : ¬ IsProj cb' := by
                        rcases hca' with ⟨heq, hst'⟩ | ⟨ms', _, _, hms', -, -⟩
                        · exact fun hp' => standalone_not_proj hst' hp'
                        · exact fun hp' => proj_not_block hp' ⟨ms', hms'⟩
                      have hnewOwn : NewAtG calls bAddr t E₀ g (Ix.Cert.ownerOf (Core.ixAddr b) c₂) := by
                        obtain ⟨c₂R, hc₂R⟩ := Option.isSome_iff_exists.mp hnewX.1
                        have ec₂ : c₂R = c₂ := Option.some.inj
                          (((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc₂R).2.symm.trans hcxE)
                        subst ec₂
                        rcases hnew_or_stored_of_held' (Ix.Cert.ownerOf (Core.ixAddr b) c₂R)
                            (hcl'.1 _ _ hc₂R).1 with hn | hs
                        · exact hn
                        · exact absurd hs hstOwn
                      have hlocOwn : LocalAtG calls bAddr t E₀ g B rb cs advAs
                          (Ix.Cert.ownerOf (Core.ixAddr b) c₂) (j' + 1) :=
                        Or.inr ⟨j', hj'L, rfl, by rw [← hownEq, ← hgetj', List.getElem_take],
                          cb', hcb', hnpOwn⟩
                      have hlb := hlocal_bound B rb cs advAs (Ix.Cert.ownerOf (Core.ixAddr b) c₂)
                        (j' + 1) hnf hlocOwn hnewOwn
                      rw [show pot (Ix.Cert.ownerOf (Core.ixAddr b) c₂) =
                        pot0 (Ix.Cert.ownerOf (Core.ixAddr b) c₂) from potG_notProj hcb' hnpOwn] at hlb
                      exact hlb.bump.lt_local (by omega)
                · exact (hlocal_bound B rb cs advAs (Core.ixAddr b) (j + 1) hnf
                    (Or.inr ⟨j, hjL, rfl, by rw [hbj], cx, hcxE, hpx⟩) hnewX).lt_local (by omega)
              · exact (hnew_wit_bound B rb cs advAs x hnf (hU.outsClassified x hW) hnewX).1.lt_local
                  (by omega)
              · by_cases hstBlk : StoredAtG calls bAddr t E₀ g blk
                · rw [show pot x = (0, 0, 0, 0) from potG_storedProj hc₁ hp₁ (hown₁ ▸ hstBlk)]
                  exact Or.inl (by omega)
                · rw [show pot x = (pot0 blk).bump from by
                    dsimp only [pot, pot0]; rw [← hown₁]; exact potG_newProj hc₁ hp₁ (hown₁ ▸ hstBlk)]
                  obtain ⟨b, hbMem, hblkEq⟩ := List.mem_map.mp hblkS
                  obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hbMem
                  have hjk : j < k := by rw [List.length_take] at hj; omega
                  have hjL : j < advAs.length := Nat.lt_trans hjk hk
                  have hnewBlk : NewAtG calls bAddr t E₀ g blk := by
                    obtain ⟨c₁R, hc₁R⟩ := Option.isSome_iff_exists.mp hnewX.1
                    have ec₁ : c₁R = c₁ := Option.some.inj
                      (((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc₁R).2.symm.trans hc₁)
                    subst ec₁
                    have hown' := (hcl'.1 x c₁R hc₁R).1
                    rw [hown₁] at hown'
                    rcases hnew_or_stored_of_held' blk hown' with hn | hs
                    · exact hn
                    · exact absurd hs hstBlk
                  obtain ⟨-, -, -, haddX, -⟩ := new_groupStore hb hg6 hnewX
                  obtain ⟨cblk, hcblk', hca'⟩ := groupStore_projMember hC hb hax hP hg6 hw x c₁ hnewX
                    ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
                      ⟨storedBelow_of_adds hg6 haddX, hc₁⟩) hp₁
                  have hblkE : recordOf E₀ blk = some cblk := by
                    rw [← hown₁]; exact ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcblk').2
                  have hnpBlk : ¬ IsProj cblk := by
                    rcases hca' with ⟨_, hst'⟩ | ⟨ms', _, _, hms', -, -⟩
                    · exact fun hp' => standalone_not_proj hst' hp'
                    · exact fun hp' => proj_not_block hp' ⟨ms', hms'⟩
                  have hlocBlk : LocalAtG calls bAddr t E₀ g B rb cs advAs blk (j + 1) :=
                    Or.inr ⟨j, hjL, rfl, by rw [← hblkEq, ← hgetj, List.getElem_take],
                      cblk, hblkE, hnpBlk⟩
                  have hlb := hlocal_bound B rb cs advAs blk (j + 1) hnf hlocBlk hnewBlk
                  rw [show pot blk = pot0 blk from potG_notProj hblkE hnpBlk] at hlb
                  exact hlb.bump.lt_local (by omega)
          · -- `¬ ∃ p, AtMuG a p`: either `GroupReach g a` or `GroupAdds.stdAxiom`!
            rw [show pot0 a = (2 + muG calls bAddr t E₀ g recs a, 1, 0, 0) from
              pot0G_own h0 h1 h2 ha]
            have hnsX : ¬ AlreadyStoredRole t g x := by
              intro hst
              have h := halr_g x hst
              rw [StoredAtG, hnewX.2] at h; cases h
            by_cases hexA : ∃ k, AnchorG calls bAddr t E₀ g recs a k
            · rcases muG_spec hexA with ⟨hgrA, hmuEq⟩ | ⟨B, rb, cs, advAs, p, hnf, hloc, hmuEq⟩
              · rw [hmuEq]
                exact Or.inl (hpathPos_lt a x hgrA (PathPos.single (Or.inl hu)) hnewX)
              · exact (ha ⟨p, B, rb, cs, advAs, hnf, hloc, hmuEq.symm⟩).elim
            · rw [muG_none hexA]
              -- `a` has no anchor, so `a` cannot be `GroupReach`, `PayClass.famRec`, `directAdv`,
              -- `directCont`, or `IsProj`; hence `a` must be a standard axiom of group `g`!
              have hgrX : GroupReach t E₀ g x := by
                rcases groupAdds_cases hC hax hw haddA with ⟨hgrA, -⟩ |
                    ⟨-, -, -, -, p, hp', hproj, -⟩ | ⟨ro, hro, hs, had, -⟩ | hpay
                · exact (hexA ⟨walkRank recs a, Or.inl ⟨hgrA, rfl⟩⟩).elim
                · have ep : p = ca := Option.some.inj (hp'.symm.trans hcaE)
                  exact (hnpA (ep ▸ hproj)).elim
                · exact GroupReach.axiomRef hro hs had hu hnsX
                · exfalso
                  rcases payAdds_cases hP hpay with ⟨hpr, -⟩ | ⟨-, -, -, -, -, p, hp', hproj, -⟩
                  · cases payReach_payClass_of_run hC hbd hb hbr hax hpin hcheck hroots hstep
                        hvalAll hws hg6 hg77 hpr with
                    | stored hst => rw [hnewA.2] at hst; cases hst
                    | walked hgrA => exact hexA ⟨walkRank recs a, Or.inl ⟨hgrA, rfl⟩⟩
                    | @famRec B' _ cs' advAs' hB hmodB hex =>
                      rcases hB with hgrB | hstB
                      · by_cases hstB' : StoredAtG calls bAddr t E₀ g B'
                        · exact h1 ⟨2 * cs'.length + 1, 0, Or.inr ⟨B', cs', advAs', ⟨hstB', hmodB, hex⟩, rfl⟩⟩
                        · obtain ⟨cb, -, hcb, -, -, -⟩ := familyCall_block_indc_nonempty
                            hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
                          have hnewB : NewAtG calls bAddr t E₀ g B' := by
                            rcases hnew_or_stored_of_held' B'
                              (by rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
                                ⟨storedBelow_of_adds hg6 (GroupAdds.reach hgrB), hcb⟩]; rfl) with
                              hn | hs
                            · exact hn
                            · exact absurd hs hstB'
                          exact h2 ⟨B', cs', advAs', hnewB, hgrB, hmodB, hex⟩
                      · exact h1 ⟨2 * cs'.length + 1, 0, Or.inr ⟨B', cs', advAs', ⟨hstB, hmodB, hex⟩, rfl⟩⟩
                    | @directAdv B' rb' _ cs' advAs' hB hmodB hex hadv =>
                      obtain ⟨ab, habMem, habEq⟩ := hadv
                      obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
                      rcases hB with hgrB | hstB
                      · by_cases hstB' : StoredAtG calls bAddr t E₀ g B'
                        · exact h1 ⟨2 * cs'.length, k + 1, Or.inl ⟨B', rb', cs', advAs', k, hk,
                            ⟨hstB', hmodB, hex⟩, by rw [hgetk, habEq], rfl⟩⟩
                        · obtain ⟨cb, -, hcb, -, -, -⟩ := familyCall_block_indc_nonempty
                            hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
                          have hnewB : NewAtG calls bAddr t E₀ g B' := by
                            rcases hnew_or_stored_of_held' B'
                              (by rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
                                ⟨storedBelow_of_adds hg6 (GroupAdds.reach hgrB), hcb⟩]; rfl) with
                              hn | hs
                            · exact hn
                            · exact absurd hs hstB'
                          exact hexA ⟨walkRank recs B', Or.inr ⟨B', rb', cs', advAs', k + 1,
                            ⟨hnewB, hgrB, hmodB, hex⟩,
                            Or.inr ⟨k, hk, rfl, by rw [hgetk, habEq], ca, hcaE, hnpA⟩, rfl⟩⟩
                      · exact h1 ⟨2 * cs'.length, k + 1, Or.inl ⟨B', rb', cs', advAs', k, hk,
                          ⟨hstB, hmodB, hex⟩, by rw [hgetk, habEq], rfl⟩⟩
                    | @directCont B' rb' _ cs' advAs' hB hmodB hex hdc =>
                      obtain ⟨-, -, -, -, ⟨ib, -, h₁, h₂, rc₁, xx₁, xib₁, r₁, cs₁, -, hxx₁, hxib₁,
                          evCr, hsubCr, -⟩, -, -, -⟩ := hdc.unpack hC hbd
                      rcases check_container_rec_shape hC hbd hxx₁ hxib₁ evCr hsubCr hcaE with
                        ⟨rc, hrc⟩ | ⟨rp, hrp⟩
                      · rcases hB with hgrB | hstB
                        · by_cases hstB' : StoredAtG calls bAddr t E₀ g B'
                          · exact h0 ⟨⟨ca, rc, hcaE, hrc⟩, B', rb', cs', advAs', ⟨hstB', hmodB, hex⟩, hdc⟩
                          · obtain ⟨cb, -, hcb, -, -, -⟩ := familyCall_block_indc_nonempty
                              hC.runStore hC.hashedStored (FamilyCallExact.toCall hex)
                            have hnewB : NewAtG calls bAddr t E₀ g B' := by
                              rcases hnew_or_stored_of_held' B'
                                (by rw [(groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
                                  ⟨storedBelow_of_adds hg6 (GroupAdds.reach hgrB), hcb⟩]; rfl) with
                                hn | hs
                              · exact hn
                              · exact absurd hs hstB'
                            exact hexA ⟨walkRank recs B', Or.inr ⟨B', rb', cs', advAs', 0,
                              ⟨hnewB, hgrB, hmodB, hex⟩,
                              Or.inl ⟨rfl, ⟨ca, rc, hcaE, hrc⟩, hdc⟩, rfl⟩⟩
                        · exact h0 ⟨⟨ca, rc, hcaE, hrc⟩, B', rb', cs', advAs', ⟨hstB, hmodB, hex⟩, hdc⟩
                      · exact hnpA (Or.inr (Or.inr (Or.inr ⟨rp, hrp⟩)))
                    | checkedProj hc' hpr _ _ _ _ =>
                      have ec : _ = ca := Option.some.inj (hc'.symm.trans hcaE)
                      exact hnpA (ec ▸ hpr)
                  · have ep : p = ca := Option.some.inj (hp'.symm.trans hcaE)
                    exact hnpA (ep ▸ hproj)
              obtain ⟨y, hy, hyx⟩ := hgrX.listed hC.hashedStored hw
              have hle1 := hpot_fst_le_walkRank x hnewX hgrX
              have hle2 : walkRank recs x ≤ y.depth := by rw [← hyx]; exact walkRank_le hy
              have hle3 := depth_le_maxDepth hy
              exact Or.inl (by omega)
  -- Assemble all 6 fields of `GroupRanked` at `rank := potRank E₀.consts.keys pot`!
  refine ⟨rank, { used := ?_, owner := ?_, fam := ?_, advice := ?_, container := ?_, famRefs := ?_ }⟩
  · -- `used`
    intro a x hnewA hused'
    have hheldX := groupStore_used_held hC hb hbr hax hP hws hg6 hw a x hnewA hused'
    rcases hnew_or_stored_of_held' x hheldX with hnewX | hstX
    · left
      obtain ⟨c, i, hc', hi, hx⟩ := hused'
      have huE : UsedRef E₀ a x :=
        ⟨c, i, ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc').2, hi, hx⟩
      obtain ⟨cx, hcxE, -, -, -⟩ := new_groupStore hb hg6 hnewX
      exact ⟨hnewX, hltRank ⟨cx, hcxE⟩ (hused_potLt a x hnewA huE hnewX)⟩
    · exact Or.inr hstX
  · -- `owner`
    intro a c hnewA hc' hp
    have hE : recordOf E₀ a = some c := ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc').2
    obtain ⟨cb, hcb', hca⟩ := groupStore_projMember hC hb hax hP hg6 hw a c hnewA hc' hp
    have hcbE : recordOf E₀ (Ix.Cert.ownerOf a c) = some cb :=
      ((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcb').2
    rcases hnew_or_stored_of_held' (Ix.Cert.ownerOf a c) (by rw [hcb']; rfl) with hnewOwn | hstOwn
    · left
      have hnsOwn : ¬ StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf a c) := by
        rw [StoredAtG, hnewOwn.2]; simp
      have hnpOwn : ¬ IsProj cb := by
        rcases hca with ⟨_, hst'⟩ | ⟨ms, _, _, hms, -, -⟩
        · exact fun hp' => standalone_not_proj hst' hp'
        · exact fun hp' => proj_not_block hp' ⟨ms, hms⟩
      refine ⟨hnewOwn, hltRank ⟨cb, hcbE⟩ ?_⟩
      rw [show pot a = (pot0 (Ix.Cert.ownerOf a c)).bump from potG_newProj hE hp hnsOwn,
        show pot (Ix.Cert.ownerOf a c) = pot0 (Ix.Cert.ownerOf a c) from potG_notProj hcbE hnpOwn]
      exact potLt_bump _
    · exact Or.inr hstOwn
  · -- `fam`
    intro B rb hfam hnewB
    obtain ⟨-, hmodB, cs, hfc⟩ := runFamOf_spec hfam
    have hgrB := new_modeledBlock_groupReach hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll
      hws hg6 hg77 hnewB hmodB hfc
    obtain ⟨advAs, hex⟩ := familyCallExact_of_call hfc
    obtain ⟨cb, -, hcb, -, -, -⟩ := familyCall_block_indc_nonempty hC.runStore hC.hashedStored hfc
    refine hltRank ⟨cb, hcb⟩ ?_
    rw [hmodeled_pot B rb cs hnewB hmodB hfc,
      hnewRec_pot B rb cs advAs ⟨hnewB, hgrB, hmodB, hex⟩]
    exact potLt_fourth (by omega)
  · -- `advice`
    intro B rb a hfam hnewB hadv hnewA
    obtain ⟨-, hmodB, cs₀, hfc₀⟩ := runFamOf_spec hfam
    obtain ⟨rb', cs, advAs, hex, hin⟩ := hadv
    have hgrB := new_modeledBlock_groupReach hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll
      hws hg6 hg77 hnewB hmodB (FamilyCallExact.toCall hex)
    have hnf : NewFamCall calls bAddr t E₀ g B rb' cs advAs := ⟨hnewB, hgrB, hmodB, hex⟩
    obtain ⟨ca, hcaE, -, -, -⟩ := new_groupStore hb hg6 hnewA
    refine hltRank ⟨ca, hcaE⟩ ?_
    rw [hmodeled_pot B rb cs₀ hnewB hmodB hfc₀]
    obtain ⟨ab, habMem, habEq⟩ := hin
    obtain ⟨k, hk, hgetk⟩ := List.mem_iff_getElem.mp habMem
    by_cases hpa : IsProj ca
    · obtain ⟨outs, hU⟩ := hex.unpack hC hbd
      have hfacts := hU.adviceFacts k hk
      rw [hgetk, habEq] at hfacts
      obtain ⟨-, c₂, hc₂, -, hkind₂, -⟩ := hfacts
      have ec : c₂ = ca := Option.some.inj (hc₂.symm.trans hcaE)
      subst ec
      rcases hkind₂ with ⟨d, hd, -⟩ | ⟨rc, hrc, -⟩ | ⟨ms, hms, -⟩ | ⟨-, -, hownS, cb', hcb', hca'⟩
      · exact (standalone_not_proj (Or.inl ⟨d, hd⟩) hpa).elim
      · exact (standalone_not_proj (Or.inr (Or.inl ⟨rc, hrc⟩)) hpa).elim
      · exact (proj_not_block hpa ⟨ms, hms⟩).elim
      · by_cases hstOwn : StoredAtG calls bAddr t E₀ g (Ix.Cert.ownerOf a c₂)
        · rw [show pot a = (0, 0, 0, 0) from potG_storedProj hcaE hpa hstOwn]
          exact Or.inl (by omega)
        · rw [show pot a = (pot0 (Ix.Cert.ownerOf a c₂)).bump from potG_newProj hcaE hpa hstOwn]
          obtain ⟨b', hb', hownEq⟩ := List.mem_map.mp hownS
          obtain ⟨j', hj', hgetj'⟩ := List.mem_iff_getElem.mp hb'
          have hj'L : j' < advAs.length := by rw [List.length_take] at hj'; omega
          have hnpOwn : ¬ IsProj cb' := by
            rcases hca' with ⟨_, hst'⟩ | ⟨ms', _, _, hms', -, -⟩
            · exact fun hp' => standalone_not_proj hst' hp'
            · exact fun hp' => proj_not_block hp' ⟨ms', hms'⟩
          have hnewOwn : NewAtG calls bAddr t E₀ g (Ix.Cert.ownerOf a c₂) := by
            obtain ⟨c₂R, hc₂R⟩ := Option.isSome_iff_exists.mp hnewA.1
            have ec₂ : c₂R = c₂ := Option.some.inj
              (((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hc₂R).2.symm.trans hcaE)
            subst ec₂
            rcases hnew_or_stored_of_held' (Ix.Cert.ownerOf a c₂R) (hcl'.1 _ _ hc₂R).1 with
              hn | hs
            · exact hn
            · exact absurd hs hstOwn
          have hlb := hlocal_bound B rb' cs advAs (Ix.Cert.ownerOf a c₂) (j' + 1) hnf
            (Or.inr ⟨j', hj'L, rfl, by rw [← hownEq, ← hgetj', List.getElem_take],
              cb', hcb', hnpOwn⟩) hnewOwn
          rw [show pot (Ix.Cert.ownerOf a c₂) = pot0 (Ix.Cert.ownerOf a c₂) from
            potG_notProj hcb' hnpOwn] at hlb
          exact hlb.bump.lt_block
    · exact (hlocal_bound B rb' cs advAs a (k + 1) hnf
        (Or.inr ⟨k, hk, rfl, by rw [hgetk, habEq], ca, hcaE, hpa⟩) hnewA).lt_block
  · -- `container`
    intro B rb x hfam hnewB hcont hnewX
    obtain ⟨-, hmodB, cs₀, hfc₀⟩ := runFamOf_spec hfam
    obtain ⟨rb', cs, advAs, hex, hdc⟩ := hcont
    have hgrB := new_modeledBlock_groupReach hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll
      hws hg6 hg77 hnewB hmodB (FamilyCallExact.toCall hex)
    have hnf : NewFamCall calls bAddr t E₀ g B rb' cs advAs := ⟨hnewB, hgrB, hmodB, hex⟩
    obtain ⟨cx, hcxE, -, -, -⟩ := new_groupStore hb hg6 hnewX
    refine hltRank ⟨cx, hcxE⟩ ?_
    rw [hmodeled_pot B rb cs₀ hnewB hmodB hfc₀]
    obtain ⟨outs, hxMem, -, -, -, -, -, houtsCls⟩ := hdc.unpack hC hbd
    exact (hnew_wit_bound B rb' cs advAs x hnf (houtsCls x hxMem) hnewX).1.lt_block
  · -- `famRefs`
    intro B rb x hfam hu _ hnewX
    obtain ⟨hnewB, hmodB, cs, hfc⟩ := runFamOf_spec hfam
    have hgrB := new_modeledBlock_groupReach hC hbd hb hbr hax hpin hcheck hroots hstep hvalAll
      hws hg6 hg77 hnewB hmodB hfc
    obtain ⟨advAs, hex⟩ := familyCallExact_of_call hfc
    have hnf : NewFamCall calls bAddr t E₀ g B rb cs advAs := ⟨hnewB, hgrB, hmodB, hex⟩
    obtain ⟨outs, hU⟩ := hex.unpack hC hbd
    obtain ⟨-, -, -, hcls⟩ := hU.famRefs x hu
    obtain ⟨cx, hcxE, -, -, -⟩ := new_groupStore hb hg6 hnewX
    rcases hcls with huB | ⟨c₁, cb, hc₁, hp₁, hown₁, -, hcb, hca⟩ |
        ⟨blk, c₁, -, hposBlk, hc₁, hp₁, hown₁, -, -, -⟩ | hW
    · right
      refine hltRank ⟨cx, hcxE⟩ ?_
      rw [hmodeled_pot B rb cs hnewB hmodB hfc]
      exact Or.inl (hpathPos_lt B x hgrB (PathPos.single (Or.inl huB)) hnewX)
    · left
      obtain ⟨cb', hcb'⟩ := Option.isSome_iff_exists.mp hnewB.1
      have ecb : cb' = cb := Option.some.inj
        (((groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mp hcb').2.symm.trans hcb)
      subst ecb
      obtain ⟨crb, hcrbE, -⟩ := familyCall_record_facts hC.runStore hC.hashedStored hfc
      have hpayRb : PayReach t E₀ (runPayload calls bAddr t) g rb :=
        PayReach.payload hgrB ⟨hg6, hmodB, rb, cs, advAs, hex, Or.inl rfl⟩
      have hcrb' : recordOf (groupStore t E₀ (runPayload calls bAddr t) (g + 1)) rb = some crb :=
        (groupStore_recordOf hb (Nat.le_succ_of_le hg6)).mpr
          ⟨storedBelow_of_adds hg6 (GroupAdds.payReach hpayRb), hcrbE⟩
      exact ⟨cb', crb, hcb', hcrb', Or.inl hca⟩
    · right
      refine hltRank ⟨cx, hcxE⟩ ?_
      rw [hmodeled_pot B rb cs hnewB hmodB hfc]
      exact Or.inl (hpathPos_proj_lt B blk x c₁ hgrB hposBlk hc₁ hp₁ hown₁ hnewX)
    · right
      refine hltRank ⟨cx, hcxE⟩ ?_
      rw [hmodeled_pot B rb cs hnewB hmodB hfc]
      exact (hnew_wit_bound B rb cs advAs x hnf (hU.outsClassified x hW) hnewX).1.lt_block

end RankProof

end IxVM.Refinement.Binding
