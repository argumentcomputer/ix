import IxVMRefinement.FamilyGraph.Composition
import IxVMRefinement.Assembly.BlockRoute
import IxVMRefinement.Assembly.NativeFormerLength

/-! # The family check of a top-walked block on the modeled route, at the walk's limit

The walk checks every member of a top-walked block (`Claim.membersChecked_of_block`). The check
of a member of a block of inductive types loads the member's projection record, which
`Ingress::get_ci` returns as the member's inductive with the member's own unsafe flag
(`Claim.GetCIHead.iPrj`). For a block in Lean's logic the flag is `0`, so `check_const` takes one
of its two safe `Induct` arms: the native one, which the dispatch's non-zero answer on the
modeled route refutes, or the modeled one, which ends with `check_modeled_block` and so with the
family check of the record the block's payload names (`check_modeled_block_family`).

* `familyCallLim_of_member`: that family check, under the member check's role context at the
  walk's limit, its calls in the run;
* `familyCheck_of_walk`: the same for a top-walked non-empty block of inductive types in Lean's
  logic on the modeled route.

No premise on the run's size (`Bounded`): the projection record is identified by the run's
store, as in `Claim.MemberCheckedLimAt.dispatch`. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open FamilyAlias (FamilyCallAtLim)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **The family check the walk's check of a member of a modeled block ran, at the walk's
limit**: the member check of a block of inductive types in Lean's logic on the modeled route ran
`check_family [rc, B, rb]` for the family record `rb` its payload names, under its role context
at `lim`, with its calls in the run. -/
theorem familyCallLim_of_member {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {t : Ix.Kernel.RoleTable} {bAddr B : _root_.Address}
    {lim : Option Nat} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {i : Nat}
    (hrecB : recordOf E₀ B = some cb) (hmuts : cb.info = .muts ms) (hlogic : InLogic cb)
    (hall : ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B ms i lim)
    (hmod : ModeledRouteAt calls B) :
    ∃ rb cs, FamilyCallAtLim calls bAddr t B rb lim cs := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, -, hsub_pa,
    -, hrc_m, ev_ld, -, hsub_ld, hld, ev_chk, -, hsub_chk⟩ := hchk
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc, a', hget', ha', hproj, hhashed⟩ :=
    L1.projection_addr_hashed_spec hmem hb' ev_pa
  obtain ⟨iv, hiv⟩ : ∃ iv, ((i : F)).val = iv := ⟨_, rfl⟩
  rw [hiv] at hget' hproj hhashed
  obtain ⟨ind, rfl⟩ := hall mc (List.mem_of_getElem? hget')
  -- the projection record the walk loaded is the one `projection_addr` hashed
  obtain ⟨raw, cp, hsz, hh, hba, hx, -, hhead⟩ := Claim.get_ci_head ha' ev_ld
  have hX : Address.blake3Pure (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.indc ind), #[], #[], #[], #[]⟩) =
      Core.ixAddr a' := hproj.symm
  have hraw : raw = Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.indc ind), #[], #[], #[], #[]⟩ :=
    hS.hashed_inj (Core.hashed_mono hsub_ld hh) (Core.hashed_mono hsub_pa hhashed)
      (hba.trans hX.symm)
  have hwf : (⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b') iv (.indc ind),
      #[], #[], #[], #[]⟩ : Ixon.Constant).wireWF :=
    L1.projConstant_wireWF_iPrj iv.toUInt64 b'
  rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hx
  injection hx with hcp
  subst hcp
  obtain ⟨cb', ms', ind', hbl, hmem', -, nl, ty, np, ni, x_blk, b, hldI, hbrep, hbeq⟩ :=
    hhead.iPrj _ _ rfl
  rw [hld] at hldI
  injection hldI with hv
  subst hv
  -- the loaded inductive is a member of the block's record, so it is safe
  have hcb : cb' = cb := ((hbl.mono hsub_ld).record hS hrecB).1
  subst hcb
  have hms' : ms' = ms := Ixon.ConstantInfo.muts.inj (hbl.info.symm.trans hmuts)
  subst hms'
  have hsafe : ind'.isUnsafe = false := by
    have hl := hlogic
    simp only [IxVM.Consistency.InLogic, hmuts] at hl
    exact (hl (.indc ind') (List.mem_of_getElem? hmem')).1
  simp only [L1.repBoolField, hsafe, Bool.false_eq_true, ↓reduceIte] at ev_chk
  match Obs.«KernelCheck::check_const».obs ev_chk with
  | .Axiom_n1 (hv37 := hv) .. | .Axiom_other_n0 (hv37 := hv) ..
  | .Axiom_other_other (hv37 := hv) ..
  | .Defn (hv269 := hv) .. | .Thm (hv526 := hv) ..
  | .Opaque (hv825 := hv) .. | .Quot (hv1076 := hv) ..
  | .Ctor_n0_n0 (hv1989 := hv) .. | .Ctor_n0_other (hv1989 := hv) ..
  | .Ctor_other_n0 (hv1989 := hv) ..
  | .Ctor_other_other (hv1989 := hv) ..
  | .Rec_n0 (hv2727 := hv) .. | .Rec_other (hv2727 := hv) .. =>
    injection hv with _ htag _; exact absurd htag (by decide)
  | .Induct_n0 (m2 := m2) (x_ind_block := xblk)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (cs1503 := cs_mod)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (hc1634 := hc) .. =>
    -- the native arm: the dispatch answered `0`, against the modeled route
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with hblk _
    subst hblk
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_to_1470 : Heap.Extends m_chk m1470 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            ev_mk.heap_extends)))))))
    have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_1470 hbrep
    exact absurd rfl (hmod _ _ _ _ _ b ev_mod
      (fun cl hcl => hsub_chk cl (by rw [hc]; simp [hcl])) hbp hbeq)
  | .Induct_other_other (hv1240 := hv_ind) (hne1975 := hne_u) .. =>
    -- the unsafe arm: the flag is `0`
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with hiu _
    exact absurd hiu.symm hne_u
  | .Induct_other_n0 (m2 := m2) (x_ind_block := xblk)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (m1749 := m1701) (m1793 := m1745) (m1841 := m1793)
      (m1854 := m1806) (cs1955 := cs_mb)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_role)
      (ev1711 := ev_fa) (ev1759 := ev_tele)
      (hm1849 := hm1793) (ev1805 := ev_rsl) (ev1866 := ev_mc) (ev1957 := ev_mb)
      (hc1974 := hc) .. =>
    -- the modeled arm: `check_modeled_block` runs the family check
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with hblk _
    subst hblk
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1793 : Heap.Extends m1701 m1793 := by rw [hm1793]; exact Heap.Extends.snoc m1701 _
    have e_to_1806 : Heap.Extends m_chk m1806 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              (ev_role.heap_extends.trans
                (ev_fa.heap_extends.trans (ev_tele.heap_extends.trans
                  (e_1793.trans (ev_rsl.heap_extends.trans ev_mc.heap_extends))))))))))))))
    have hsub_mb : ∀ cl ∈ cs_mb, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    obtain ⟨x_rb, rb, m, cs_fam, e_m, hrb, ev_fam, hcl_fam, hsub_fam⟩ :=
      check_modeled_block_family ev_mb
    have e_all : Heap.Extends m_chk m := e_to_1806.trans e_m
    exact ⟨Core.ixAddr rb, cs_fam, m, _, rc, _, x_rb, _, Claim.RCLimRep.mono e_all hrc_m,
      ⟨b, Bytes.repAddressRef_heapMono₂ Core.addrTy e_all hbrep, hbeq⟩, ⟨rb, hrb, rfl⟩,
      ev_fam, hsub_mb _ hcl_fam, fun cl hcl => hsub_mb cl (hsub_fam cl hcl)⟩

/-- **The family check of a top-walked block on the modeled route, at the walk's binding and
limit**: a top-walked non-empty block of inductive types in Lean's logic that the run routes as
modeled had a family check, under the walk's role context at its limit, with its calls in the
run (the check of its first member, `familyCallLim_of_member`). -/
theorem familyCheck_of_walk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {seeds : List _root_.Address} {E₀ : Ixon.Env} {lim : Option Nat}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore calls bAddr t seeds E₀ lim Top rank) {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hT : Top B)
    (hcb : recordOf E₀ B = some cb) (hms : cb.info = .muts ms) (hpos : 0 < ms.size)
    (hall : ∀ m ∈ ms.toList, ∃ ind, m = Ixon.MutConst.indc ind) (hlog : InLogic cb)
    (hroute : ModeledRouteAt calls B) :
    ∃ rb cs, FamilyCallAtLim calls bAddr t B rb lim cs := by
  obtain ⟨c, hc, hchk⟩ := hW.checked B hT
  have e : c = cb := Option.some.inj (hc.symm.trans hcb)
  subst e
  exact familyCallLim_of_member hW.runStore hcb hms hlog hall
    (Claim.membersChecked_of_block hW.runStore hcb hms hchk 0 hpos) hroute

end IxVM.Refinement.Typing
