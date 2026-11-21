import IxVMRefinement.Assembly.NativeBlockReads
import IxVMRefinement.FamilyGraph.InnerChecked
import IxVMRefinement.FamilyAlias.Target
import IxVMRefinement.Binding.ReadsLocal
import IxVMRefinement.Binding.BasisAt

/-! # The readings of an advice block's constant addresses

A family check runs `KernelModeled::check_advice_record` on each advice record it lists. On a
block of one inductive type (`Decl.adviceBlock_shape`) the record's arm runs
`KernelClaim::check_muts_all`, whose first step, `check_muts_member_at` at position 0, loads the
former's projection record (`Ingress::get_ci` at the address `Ingress::projection_addr` computes)
and checks it (`KernelCheck::check_const`). The `Induct` arm of that check loads every constructor
of the block (`Ingress::get_ci_cprj`, `check_inductive_shape_ctors` on the native route). So the
former and each constructor have a reading over the run's store, and over every used-closed store
within it that holds the block and the run's blobs (`adviceBlock_reads`).

The role context of the advice check plays no part: a family check nested in another's calls runs
its own advice walk, and `runAdv` names its records too, under a context the run's records do not
pin. So the former's check is taken under any context (`FormerCheckObs`), and the constructor
slots and the readings are read off it as `Typing.ctorSlots_of_member` and `Typing.former_reads`
read them off a check under a known context (`ctorSlots_of_formerObs`, `former_reads_of_obs`).

No unit check covers these constructor projections: `check_muts_all` checks the block's members,
not its constructors. -/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **An observed check of the former of a block of one inductive type, under any role
context**: the load of the former's projection record (`Ingress::get_ci` at its address) and
`KernelCheck::check_const` on the loaded value, with their calls in the run. -/
def FormerCheckObs (calls : List (Call F)) (B : _root_.Address) (ind : Ixon.Inductive) : Prop :=
  ∃ (h_pre m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
    (cs_load cs_chk : List (Call F)),
    Core.BaseSeams.addr h_pre ap (memberAddr B 0 (.indc ind)) ∧
    ObsFn Obs.W "Ingress::get_ci" [ap] h_pre ptr m_chk cs_load ∧ (∀ cl ∈ cs_load, cl ∈ calls) ∧
    loadValue m_chk ptr = .ok v ∧
    ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
    (∀ cl ∈ cs_chk, cl ∈ calls)

section FormerObs

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}

private theorem idx_zero' (B : _root_.Address) :
    (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
  show ((0 : Nat).toUInt64).toNat = 0
  decide

/-- **The load of the former in its observed check**, at a bounded derivation
(`Ingress.get_ci_loadedRecords_spec`), as `Assembly.checkedAtFull_loadedRecords` reads it. -/
theorem FormerCheckObs.loaded (hbound : Bounded calls) (hobs : FormerCheckObs calls B ind) :
    ∃ (m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
      (cs_load cs_chk : List (Call F)) (bytes : ByteArray) (E_ld : Ixon.Env),
      Hashed cs_load bytes ∧ Address.blake3Pure bytes = memberAddr B 0 (.indc ind) ∧
      LoadedBy cs_load E_ld ∧ Ingress.LoadedRecords E_ld m_chk ptr bytes ∧
      (∀ cl ∈ cs_load, cl ∈ calls) ∧ loadValue m_chk ptr = .ok v ∧
      ObsFn Obs.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
      (∀ cl ∈ cs_chk, cl ∈ calls) := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, ⟨a', ha', he⟩, ev_ld,
    hsub_ld, hld, ev_chk, hsub_chk⟩ := hobs
  obtain ⟨-, bytes, E_ld, hhash, hblake, hloaded, hL1⟩ :=
    Ingress.get_ci_loadedRecords_spec (RomBound.bounded_mono hbound hsub_ld) ha' ev_ld
  exact ⟨m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, bytes, E_ld, hhash,
    hblake.trans he, hloaded, hL1, hsub_ld, hld, ev_chk, hsub_chk⟩

/-- **Every constructor slot of the block has its load**, from the former's check under any role
context: `ctorSlots_of_member` without the context. -/
theorem ctorSlots_of_formerObs (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : BlockUnitRecord E₀ B cb ind) (hobs : FormerCheckObs calls B ind) :
    ∃ b : Bytes.Address, Core.ixAddr b = B ∧ ind.lvls.toNat < 4294967296 ∧
      ind.params.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
      ∀ j < ind.ctors.size,
        CtorSlotLoaded calls b ((0 : Nat) : F) j ind.lvls.toNat ind.params.toNat := by
  obtain ⟨m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, hsub_chk⟩ := hobs.loaded hbound
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedRecords_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  unfold Ingress.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [idx_zero' B] at hms' raw
  have hind_eq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms'
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  obtain ⟨hlv, hnp, hni, hnc, -, tyPtr, blkPtr, b, hb_eq, hbp_m, hv, -⟩ := raw
  subst hv
  have hsafe : ind.isUnsafe = false := by
    have hl := hrec.logic
    simp only [IxVM.Consistency.InLogic, hrec.muts] at hl
    exact (hl (.indc ind) (by simp)).1
  simp only [Ingress.repBoolField, hsafe, Bool.false_eq_true, ↓reduceIte] at ev_chk
  refine ⟨b, hb_eq, hlv, hnp, hnc, ?_⟩
  intro j hj
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
  | .Induct_n0 (m2 := m2) (x_nlvls := xnl) (x_ty := xty)
      (x_n_params := xnp) (x_n_indices := xni) (x_num_ctors := xnc)
      (x_ind_is_unsafe := xiu) (x_ind_block := xblk) (x_ind_idx := xidx)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (cs1529 := cs_sh)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1531 := ev_sh) (hc1634 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp' hargs; injection hargs with hni' hargs
    injection hargs with hnc' hargs; injection hargs with hiu hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp' hni' hnc' hiu hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_to_1492 : Heap.Extends m_chk m1492 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans ev_mod.heap_extends))))))))
    have hsub_sh : ∀ cl ∈ cs_sh, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    cases Obs.«KernelCheck::check_inductive_shape».obs ev_sh with
    | run _ m2_sh _ _ m50_sh _ _ _ _ m63_sh _ _ cs135 _ hm58 ev14_sh ev75_sh _ ev145_sh ev137
        hc225 =>
      have e_50 : Heap.Extends m1492 m50_sh := by rw [hm58]; exact Heap.Extends.snoc m1492 _
      have e_to_63 : Heap.Extends m_chk m63_sh :=
        e_to_1492.trans (e_50.trans (ev14_sh.heap_extends.trans
          (ev75_sh.heap_extends.trans ev145_sh.heap_extends)))
      have hsub_ctors : ∀ cl ∈ cs135, cl ∈ calls := fun cl hcl =>
        hsub_sh cl (by rw [hc225]; simp [hcl])
      have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_63 hbp_m
      exact native_ctor_slots hnc ind.ctors.size 0 (by omega) rfl rfl hsub_ctors hbp ev137 j
        (Nat.zero_le _) hj
  | .Induct_other_other (hv1240 := hv_ind) (hne1975 := hne_u) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with _ hargs
    injection hargs with _ hargs; injection hargs with hiu _
    exact absurd hiu.symm hne_u
  | .Induct_other_n0 (m2 := m2) (x_nlvls := xnl) (x_ty := xty)
      (x_n_params := xnp) (x_n_indices := xni) (x_num_ctors := xnc)
      (x_ind_block := xblk) (x_ind_idx := xidx)
      (m1283 := m1283) (m1333 := m1333) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (m1427 := m1427) (m1440 := m1440) (m1470 := m1470)
      (m1492 := m1492) (m1749 := m1653) (m1793 := m1688) (m1841 := m1736)
      (cs1864 := cs_mc)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1663 := ev_fa) (ev1711 := ev_lead) (ev1759 := ev_tele)
      (hm1849 := hm1736) (ev1805 := ev_rsl) (ev1866 := ev_mc) (hc1974 := hc) .. =>
    injection hv_ind with _ _ hargs
    injection hargs with hnl hargs; injection hargs with hty hargs
    injection hargs with hnp' hargs; injection hargs with hni' hargs
    injection hargs with hnc' hargs; injection hargs with _ hargs
    injection hargs with hblk hargs; injection hargs with hidx _
    subst hnl hty hnp' hni' hnc' hblk hidx
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_1736 : Heap.Extends m1653 m1736 := by rw [hm1736]; exact Heap.Extends.snoc m1653 _
    have e_to_1688 : Heap.Extends m_chk m1688 :=
      ev_iu.heap_extends.trans (ev_ws.heap_extends.trans
        (e_1376.trans (e_1354.trans (ev_emb.heap_extends.trans
          (e_1427.trans (ev_es.heap_extends.trans (ev_saf.heap_extends.trans
            (ev_mk.heap_extends.trans (ev_mod.heap_extends.trans
              ((ev_fa.heap_extends.trans ev_lead.heap_extends).trans (ev_tele.heap_extends.trans
                (e_1736.trans ev_rsl.heap_extends))))))))))))
    have hsub_mc : ∀ cl ∈ cs_mc, cl ∈ calls := fun cl hcl =>
      hsub_chk cl (by rw [hc]; simp [hcl])
    have hbp := Bytes.repAddressRef_heapMono₂ Core.addrTy e_to_1688 hbp_m
    exact modeled_ctor_slots hnc ind.ctors.size 0 (by omega) rfl rfl hsub_mc hbp ev_mc j
      (Nat.zero_le _) hj

/-- **The reading of the former**, over the run's store, from its check under any role context:
`former_reads` without the context. -/
theorem former_reads_of_obs (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hobs : FormerCheckObs calls B ind) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ind.typ = .ok ty₀ ∧
      ∀ caps, Reads t E₀ (memberAddr B 0 (.indc ind))
        (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩
          caps) := by
  obtain ⟨m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, hsub_chk⟩ := hobs.loaded hbound
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨ms', ind', ty₀, h1, h2, -, hty, hreads, -⟩ :=
    LoadedReads.loadedRecords_ind_reads (p := ⟨(0 : Nat).toUInt64, B⟩) ht hS hload_ld hsub_ld hhash
      hblake hL1 hrecP rfl hrecB hrec.logic
  have hms : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (h1.symm.trans hrec.muts)
  subst hms
  rw [idx_zero' B] at h2
  have hind : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj h2
    exact (Ixon.MutConst.indc.inj e).symm
  subst hind
  exact ⟨ty₀, hty, hreads⟩

end FormerObs

/-! ## The former's check in an advice check -/

/-- **An observed advice-record check of a block of one inductive type checked the block's
former** (module docstring), under the advice check's role context. -/
theorem formerCheckObs_of_advice {calls cs : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀)
    {x_rc x_a x_aset x_wset r : SourceValue F} {h h' : Heap F} {ab : Bytes.Address}
    (ha : Bytes.RepAddressRef Core.addrTy h ab x_a)
    (ev : ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    {c : Ixon.Constant} (hc : recordOf E₀ (Core.ixAddr ab) = some c) {ind : Ixon.Inductive}
    (hms : c.info = .muts #[.indc ind]) :
    FormerCheckObs calls (Core.ixAddr ab) ind := by
  match Obs.«KernelModeled::check_advice_record».obs ev with
  | .run (m2 := m2) (cs12 := cs12) (x_info := x_info) (cs947 := cs947) (ev14 := ev14)
      (ev_yqjbwijz := ev_ord) (sg952 := sg952) (hc1011 := hc1011) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    have hsub947 : ∀ cl ∈ cs947, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc1011]; simp [hcl])
    obtain ⟨msPtr, hxm, hlist, -⟩ :=
      Decl.load_block_info hS (Bytes.repAddressRef_heapMono₂ Core.addrTy ev_ord.heap_extends ha)
        ev14 hsub12 hc hms
    have ext1 : Heap.Extends h m2 := ev_ord.heap_extends.trans ev14.heap_extends
    match sg952 with
    | .Defn_Definition_Safe (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Definition_other (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Theorem (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Defn_Opaque (hv81 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Recr (hv403 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .IPrj (hv790 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .CPrj (hv869 := hv) .. =>
      exact absurd (Value.construct.inj (hv.symm.trans hxm)).2.1 (by decide)
    | .Muts (x_members := xm) (cs742 := csm) (hv598 := hv) (ev629 := ev629) (ev649 := ev649)
        (ev683 := ev683) (ev723 := ev723) (ev744 := evm) (hc784 := hcs) .. =>
      have hxe : xm = msPtr := (List.cons.inj (Value.construct.inj (hv.symm.trans hxm)).2.2).1
      subst hxe
      have ext2 : Heap.Extends m2 _ := ev629.heap_extends.trans (ev649.heap_extends.trans
        (ev683.heap_extends.trans ev723.heap_extends))
      have hsubm : ∀ cl ∈ csm, cl ∈ calls := fun cl hcl => hsub947 cl (by rw [hcs]; simp [hcl])
      have hmems := Decl.membersRep_of_repMutConstList
        (RepLinkedList.mono Ingress.repMutConst_heapMono₂ ext2 hlist)
      have ha2 := Bytes.repAddressRef_heapMono₂ Core.addrTy (ext1.trans ext2) ha
      rcases Obs.«KernelClaim::check_muts_all».obs evm with
        ⟨ld12, -⟩ |
        ⟨x_m, x_rest, v42, m43, cs53, cs99, v106, ld12, ev55, op148, ev101, hc150⟩
      · cases Lib.rep_nil_of_load hmems ld12
      · have hsub53 : ∀ cl ∈ cs53, cl ∈ calls := fun cl hcl => hsubm cl (by rw [hc150]; simp [hcl])
        obtain ⟨v1, mpa, cspa, vci, mchk, pci, csld, cschk, evpa, evld, ldci, evchk, hcm⟩ :=
          Obs.«KernelClaim::check_muts_member_at».obs ev55
        have hsubpa : ∀ cl ∈ cspa, cl ∈ calls := fun cl hcl => hsub53 cl (by rw [hcm]; simp [hcl])
        have hsubld : ∀ cl ∈ csld, cl ∈ calls := fun cl hcl => hsub53 cl (by rw [hcm]; simp [hcl])
        have hsubchk : ∀ cl ∈ cschk, cl ∈ calls :=
          fun cl hcl => hsub53 cl (by rw [hcm]; simp [hcl])
        obtain ⟨-, -, -, mc, a', hget, ha', hproj, -⟩ := Ingress.projection_addr_hashed_spec hmems ha2 evpa
        have hz : ZMod.val (0 : F) = 0 := by simp
        rw [hz] at hget hproj
        have hmc : mc = .indc ind := (Option.some.inj hget).symm
        subst hmc
        exact ⟨mpa, mchk, _, x_rc, v1, pci, vci, _, csld, cschk,
          ⟨a', ha', hproj.trans (LoadedReads.memberAddr_eq_projAddr _ 0 _).symm⟩,
          evld, hsubld, ldci, evchk, hsubchk⟩

end IxVM.Refinement.Typing

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)

set_option linter.unusedVariables false

/-- **An observed advice-record check at `a`**, its calls among the run's. -/
def AdviceCheckObs (calls : List (Call F)) (a : _root_.Address) : Prop :=
  ∃ (x_rc x_a x_aset x_wset r : SourceValue F) (h h' : Heap F) (cs : List (Call F))
    (ab : Bytes.Address),
    Bytes.RepAddressRef Core.addrTy h ab x_a ∧ Core.ixAddr ab = a ∧
    ObsFn Obs.W "KernelModeled::check_advice_record" [x_rc, x_a, x_aset, x_wset] h r h' cs ∧
    ∀ cl ∈ cs, cl ∈ calls

/-- **An advice record of a family check had its advice-record check observed**: a call among an
observed derivation's calls has its own observation (`ObsFn.calls_observed`). -/
theorem adviceCheckObs_of_familyCall {calls cs : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {B rb : _root_.Address} {lim : Option Nat}
    (hfc : FamilyAlias.FamilyCallAtLim calls bAddr t B rb lim cs) {a : _root_.Address}
    (ha : AdviceIn cs a) : AdviceCheckObs calls a := by
  obtain ⟨h, h', rc, xb, xrb, r, -, -, -, ev, -, hsub⟩ := hfc
  obtain ⟨rc', xa, seen, wset, h₁, hmem, ab, hab, rfl⟩ := ha
  obtain ⟨r₁, h₁', cs₁, ev₁, hcs₁⟩ := ev.calls_observed _ hmem
  exact ⟨rc', xa, seen, wset, r₁, h₁, h₁', cs₁, ab, hab, rfl, ev₁,
    fun cl hcl => hsub cl (hcs₁ cl hcl)⟩

/-- **Every constant address of an advice block, held by a used-closed store within the run's
records that holds the run's blobs, reads over that store** (module docstring): the block is one
inductive type (`Decl.adviceBlock_shape`); the advice check checked its former
(`formerCheckObs_of_advice`), which reads over the run's store (`former_reads_of_obs`) and loaded
every constructor (`ctorSlots_of_formerObs`, `ctorSlot_reads`); each reading is one over the store
(`reads_of_closed_sub`). Premises on the block, each a field of `PayloadFacts` for a block the
payload reaches: its projection records are the run's (`blockMembers`) and it is in Lean's logic
(`logic`). -/
theorem adviceBlock_reads {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ R : Ixon.Env}
    (ht : t.check = .ok ()) (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hcl : UsedClosed R) (hsubR : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    (hblob : ∀ y b, E₀.blobs.get? y = some b → R.blobs.get? y = some b)
    {a : _root_.Address} {ca : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hE : recordOf E₀ a = some ca) (hms : ca.info = .muts ms) (hlog : InLogic ca)
    (hmemb : ∀ i m, ms[i]? = some m →
      recordOf E₀ (memberAddr a i m) = some (memberProjection a i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr a i j) = some (constructorProjection a i j))
    (hadv : AdviceCheckObs calls a) :
    ∀ x, ConstAddrOf a ca x → (recordOf R x).isSome = true → ∃ ci₀, Reads t R x ci₀ := by
  obtain ⟨x_rc, x_a, x_aset, x_wset, r, h, h', cs, ab, hab, rfl, ev, hcs⟩ := hadv
  intro x hx hxR
  rcases hx with ⟨-, hst⟩ | ⟨ms', i, m, hms', hm, hx⟩
  · exact (standalone_not_block hst ⟨ms, hms⟩).elim
  have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
  rw [e] at hm
  have h0 : ms.size ≠ 0 := by
    intro hz
    have hlt := (Array.getElem?_eq_some_iff.mp hm).1
    omega
  obtain ⟨ind, rfl⟩ := Decl.adviceBlock_shape (lim := none) hS hab ev hcs hE hms h0
  have hi : i = 0 ∧ m = .indc ind := by
    have hlt := (Array.getElem?_eq_some_iff.mp hm).1
    have hi0 : i = 0 := by simp at hlt; omega
    subst hi0
    exact ⟨rfl, (Option.some.inj hm).symm⟩
  obtain ⟨rfl, rfl⟩ := hi
  have hobs := formerCheckObs_of_advice hS hab ev hcs hE hms
  obtain ⟨hformE, hctorE⟩ := hmemb 0 (.indc ind) hm
  have hrec : BlockUnitRecord E₀ (Core.ixAddr ab) ca ind :=
    ⟨hE, hms, hlog, hformE, fun j hj => hctorE ind j rfl hj⟩
  rcases hx with rfl | ⟨ind', j, hind', hj, rfl⟩
  · obtain ⟨ty₀, -, hreads⟩ := former_reads_of_obs ht hbound hS hrec hobs
    exact ⟨_, reads_of_closed_sub ht (wf_of_check ht) hsubR hcl hblob hxR (hreads default)⟩
  · have e' : ind = ind' := Ixon.MutConst.indc.inj hind'
    subst e'
    obtain ⟨b, hb, hlv, hnp, hnc, hslots⟩ := ctorSlots_of_formerObs hbound hS hrec hobs
    obtain ⟨ct, ty₀, -, -, -, -, -, hreads⟩ :=
      ctorSlot_reads ht hbound hS hrec hb hlv hnp hj (by omega) (hslots j hj)
    exact ⟨_, reads_of_closed_sub ht (wf_of_check ht) hsubR hcl hblob hxR hreads⟩

end IxVM.Refinement.Binding
