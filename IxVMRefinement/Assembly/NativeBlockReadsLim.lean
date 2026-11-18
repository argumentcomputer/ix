import IxVMRefinement.Assembly.NativeBlockReads
import IxVMRefinement.Claim.TopDefn

/-! # The member check of a one-type block, read at either role context

The walk exports the check of a block's member under the role context of its validator: at a
group limit, or with the binding assumed (`Claim.MemberCheckedLimAt … lim`, `lim : Option
Nat`). The readings of a native block's member check were stated for a context at a group
limit only (`MutsMemberCheckedAtFullAt … n`). This module states them for either context,
beside the earlier ones, with the same proofs: none of them reads the role context's limit,
and the one that types the former does so at the context of the given limit.

* `Assembly.checkedLimAt_loadedL1`: a checked record's load, with the check on the loaded value.
* `memberCheckedLimAt_checkedLimAt`: a checked member is checked at its constant address.
* `ctorSlots_of_member_lim`, `former_reads_lim`, `blockReads_of_member_lim`,
  `blockReads_shape_lim`, `nativeParts_of_member_lim`, `former_scope_lim`, `member_bounds_lim`:
  the block's readings, the recognised parts at a former declared at its telescope, the scope
  of the former's type and the record's count bounds.
* `formerChecked_of_member_lim`: the former checked at the prefix, under the prefix invariant
  at the walk's limit.

At `lim = some n` each is the earlier statement.
-/

universe u

set_option maxHeartbeats 3200000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Assembly

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- Under `Bounded calls`, a check of the record at `a` under the role context at `lim` pairs
its `Ingress::get_ci` sub-derivation with `L1.get_ci_loadedL1_spec` to produce `LoadedL1`
alongside the `KernelCheck::check_const` call on the loaded heap value. -/
theorem checkedLimAt_loadedL1
    {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {a : _root_.Address} {lim : Option Nat}
    (hbound : IxVM.Consistency.Bounded calls)
    (hc : Claim.CheckedLimAt calls bAddr t a lim) :
    ∃ (_ : Option Nat) (h_pre m_chk h'_chk : Heap F) (rc ap ptr v r_chk : SourceValue F)
      (cs_load cs_chk : List (Call F)) (bytes : ByteArray) (E_ld : Ixon.Env),
      Claim.RCLimRep t bAddr lim h_pre rc ∧
      Claim.RCLimRep t bAddr lim m_chk rc ∧
      Core.S0.addr h_pre ap a ∧
      Core.S0.addr m_chk ap a ∧
      Hashed cs_load bytes ∧
      Address.blake3Pure bytes = a ∧
      IxVM.Consistency.LoadedBy cs_load E_ld ∧
      L1.LoadedL1 E_ld m_chk ptr bytes ∧
      (∀ cl ∈ cs_load, cl ∈ calls) ∧
      loadValue m_chk ptr = .ok v ∧
      ObsFn Core.W "KernelCheck::check_const" [rc, v, ap] m_chk r_chk h'_chk cs_chk ∧
      (⟨"KernelCheck::check_const", [rc, v, ap], m_chk⟩ : Call F) ∈ calls ∧
      (∀ cl ∈ cs_chk, cl ∈ calls) := by
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, ha_pre, ha_m, ev_ld, _hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hc
  obtain ⟨a', ha'_ref, rfl⟩ := ha_pre
  have hbound_ld : IxVM.Consistency.Bounded cs_load := RomBound.bounded_mono hbound hsub_ld
  obtain ⟨_ext, bytes, E_ld, hhash, hblake, hloaded, hL1⟩ :=
    L1.get_ci_loadedL1_spec hbound_ld ha'_ref ev_ld
  exact ⟨lim, h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, bytes, E_ld,
    hrc_pre, hrc_m, ⟨a', ha'_ref, rfl⟩, ha_m,
    hhash, hblake, hloaded, hL1, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩

end IxVM.Refinement.Assembly

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Consistency

section Checked

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)}

/-- **A checked block member is checked at its constant address, under the same role
context.** -/
theorem memberCheckedLimAt_checkedLimAt (hbound : Bounded calls) {bAddr B : _root_.Address}
    {ms : Array Ixon.MutConst} {k : Nat} {mc : Ixon.MutConst} {lim : Option Nat}
    (hm : Claim.MemberCheckedLimAt calls bAddr t B ms k lim) (hk : ms[k]? = some mc) :
    Claim.CheckedLimAt calls bAddr t (memberAddr B k mc) lim := by
  obtain ⟨h_pa, h_pre, m_chk, h'_chk, rc, x_members, x_block, ap, ptr, v, r_chk,
    cs_pa, cs_load, cs_chk, hmem, hblk, ev_pa, hcl_pa, hsub_pa,
    hrc_pre, hrc_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hm
  have hlen : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbound hcl_pa (List.Mem.head _) hmem
  have hk_lt : k < ms.toList.length := by
    have hk_sz : k < ms.size := (Array.getElem?_eq_some_iff.mp hk).1
    simpa using hk_sz
  have hk_val : ((k : F)).val = k :=
    ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨b', hb', rfl⟩ := hblk
  obtain ⟨-, -, -, mc', a', hget', ha', hproj, hhashed⟩ :=
    L1.projection_addr_hashed_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj hhashed
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  have haddr : Core.S0.addr h_pre ap (memberAddr (Core.ixAddr b') k mc) :=
    ⟨a', ha', hproj.trans (LoadedReads.memberAddr_eq_projAddr _ k mc).symm⟩
  exact ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, haddr, Core.S0.addr_mono ev_ld.heap_extends haddr,
    ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩

variable {E₀ : Ixon.Env}

end Checked

end IxVM.Refinement.Typing

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

section Member

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {lim : Option Nat}

private theorem idx_zero_lim (B : _root_.Address) :
    (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
  show ((0 : Nat).toUInt64).toNat = 0
  decide

/-- **Every constructor slot of the block has its load**, on either route of the `Induct` arm,
with the block's level and parameter counts and their bounds. -/
theorem ctorSlots_of_member_lim (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim) :
    ∃ b : Bytes.Address, Core.ixAddr b = B ∧ ind.lvls.toNat < 4294967296 ∧
      ind.params.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
      ∀ j < ind.ctors.size,
        CtorSlotLoaded calls b ((0 : Nat) : F) j ind.lvls.toNat ind.params.toNat := by
  have hchkA := memberCheckedLimAt_checkedLimAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedLimAt_loadedL1 hbound hchkA
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [idx_zero_lim B] at hms' raw
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
  simp only [L1.repBoolField, hsafe, Bool.false_eq_true, ↓reduceIte] at ev_chk
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

/-- **The reading of the former**, over the run's store. -/
theorem former_reads_lim (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim) :
    ∃ ty₀ : Ix.Kernel.Expr .anon,
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ind.typ = .ok ty₀ ∧
      ∀ caps, Reads t E₀ (memberAddr B 0 (.indc ind))
        (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩
          caps) := by
  have hchkA := memberCheckedLimAt_checkedLimAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedLimAt_loadedL1 hbound hchkA
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨ms', ind', ty₀, h1, h2, -, hty, hreads, -⟩ :=
    LoadedReads.loadedL1_ind_reads (p := ⟨(0 : Nat).toUInt64, B⟩) ht hS hload_ld hsub_ld hhash
      hblake hL1 hrecP rfl hrecB hrec.logic
  have hms : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (h1.symm.trans hrec.muts)
  subst hms
  rw [idx_zero_lim B] at h2
  have hind : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj h2
    exact (Ixon.MutConst.indc.inj e).symm
  subst hind
  exact ⟨ty₀, hty, hreads⟩

/-- **The reading of a constructor at a loaded slot**, over the run's store, with its stored
index, level count and parameter count pinned to the slot and the block's. -/

/-- **The declared block of the unit, read over the run's store**: the former, then one
constructor per slot, each with its reading; no pinned basis block; non-derived keys. The
former's capability record in the reading is any (`Reads` leaves it open). -/
theorem blockReads_of_member_lim (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim) :
    ∃ (ty₀ : Ix.Kernel.Expr .anon) (cs : List (ConstantInfo .anon)),
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ind.typ = .ok ty₀ ∧
      cs.length = ind.ctors.size ∧
      (∀ j c, cs[j]? = some c → ∃ (ct : Ixon.Constructor) (tyj : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
        ct.params.toNat = ind.params.toNat ∧
        (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
          ct.typ = .ok tyj ∧
        c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
          ct.params.toNat ct.fields.toNat ∧
        Reads t E₀ (ctorAddr B 0 j) c) ∧
      ∀ caps : Ix.Kernel.IndCaps .anon,
        BlockReadings t E₀ B ind (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)),
          List.range ind.lvls.toNat, ty₀⟩ caps :: cs) ∧
        Ix.Kernel.basisPinHit (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)),
          List.range ind.lvls.toNat, ty₀⟩ caps :: cs) = none ∧
        Decl.DeclNonAux (.indDecl (.indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)),
          List.range ind.lvls.toNat, ty₀⟩ caps :: cs) ind.params.toNat) := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨ty₀, hty, hfr⟩ := former_reads_lim ht hbound hS hrec hchk
  obtain ⟨b, hb, hlv, hnp, hnc, hslots⟩ := ctorSlots_of_member_lim hbound hS hrec hchk
  obtain ⟨cs, hlen, hcs⟩ := exists_list_of_forall (P := fun j c =>
    ∃ (ct : Ixon.Constructor) (tyj : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
      ct.params.toNat = ind.params.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ct.typ = .ok tyj ∧
      c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
        ct.params.toNat ct.fields.toNat ∧
      Reads t E₀ (ctorAddr B 0 j) c) ind.ctors.size (by
    intro j hj
    obtain ⟨ct, tyj, h1, h2, h3, h4, h5, h6⟩ :=
      ctorSlot_reads ht hbound hS hrec hb hlv hnp hj (by omega) (hslots j hj)
    exact ⟨_, ct, tyj, h1, h2, h3, h4, h5, rfl, h6⟩)
  refine ⟨ty₀, cs, hty, hlen, hcs, fun caps => ?_⟩
  -- the constructors are no recursors
  have hnorec : (ConstantInfo.indInfo
      ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps :: cs).any
      isRecInfo = false := by
    simp only [List.any_cons, isRecInfo, Bool.false_or, List.any_eq_false]
    intro c hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hj
    simp [isRecInfo]
  have hpin := basisPinHit_none_of_noRec hnorec
  -- distinct addresses, distinct keys
  have hjb : ∀ {j}, j < ind.ctors.size → j < UInt64.size := fun hj => by
    show _ < 18446744073709551616
    omega
  have hctor_ne : ∀ j, j < ind.ctors.size → ctorAddr B 0 j ≠ memberAddr B 0 (.indc ind) := by
    intro j hj he
    have h1 := hrec.ctors j hj
    rw [he, hrec.former] at h1
    have h2 : Ixon.ConstantInfo.iPrj ⟨(0 : Nat).toUInt64, B⟩ =
        .cPrj ⟨(0 : Nat).toUInt64, j.toUInt64, B⟩ :=
      congrArg Ixon.Constant.info (Option.some.inj h1)
    cases h2
  have hctor_inj : ∀ j j', j < ind.ctors.size → j' < ind.ctors.size →
      ctorAddr B 0 j = ctorAddr B 0 j' → j = j' :=
    ctorAddr_inj hrec (fun hj => hjb hj)
  have hname : ∀ j c, cs[j]? = some c → c.name = keyOf t (ctorAddr B 0 j) := by
    intro j c hc
    obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hc
    rfl
  have hlt : ∀ j c, cs[j]? = some c → j < ind.ctors.size := by
    intro j c hc
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have hndcs : (cs.map (·.name)).Nodup :=
    nodup_names_of_index hname (fun j j' hj hj' e => hctor_inj j j' (by omega) (by omega)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := ctorAddr B 0 j') htwf e))
  have hnd : ((ConstantInfo.indInfo
      ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps :: cs).map
      (·.name)).Nodup := by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, hndcs⟩
    obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hm
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    have e : keyOf t (ctorAddr B 0 j) = keyOf t (memberAddr B 0 (.indc ind)) :=
      (hname j c hj).symm.trans hcn
    exact hctor_ne j (hlt j c hj)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := memberAddr B 0 (.indc ind)) htwf e)
  refine ⟨⟨_, cs, rfl, hfr caps, hlen, fun j c hc => ?_⟩, hpin,
    declNonAux_indDecl_of hpin ?_ hnd⟩
  · obtain ⟨ct, tyj, -, -, -, -, -, -, hr⟩ := hcs j c hc
    exact hr
  · intro ci hci
    rcases List.mem_cons.mp hci with rfl | hc
    · exact ⟨nonAux_keyOf t _, read_refsIn_nonAux hty, trivial⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, tyj, -, -, -, -, htyj, rfl, -⟩ := hcs j ci hj
      exact ⟨nonAux_keyOf t _, read_refsIn_nonAux htyj, trivial⟩

/-- **Every block of readings at the unit's addresses is the read block**: the former's reading
up to its capability record, and the constructors' readings. -/
theorem blockReads_shape_lim (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk) :
    ∃ (ty₀ : Ix.Kernel.Expr .anon) (caps : Ix.Kernel.IndCaps .anon)
      (cs : List (ConstantInfo .anon)),
      blk = .indInfo ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps
        :: cs ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
        ind.typ = .ok ty₀ ∧
      cs.length = ind.ctors.size ∧
      ∀ j c, cs[j]? = some c → ∃ (ct : Ixon.Constructor) (tyj : Ix.Kernel.Expr .anon),
        ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
        ct.params.toNat = ind.params.toNat ∧
        (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
          ct.typ = .ok tyj ∧
        c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
          ct.params.toNat ct.fields.toNat ∧
        Reads t E₀ (ctorAddr B 0 j) c := by
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨fr, cs, rfl, hfr, hlen, hcs⟩ := hblk
  obtain ⟨ty₀, hty, hfr₀⟩ := former_reads_lim ht hbound hS hrec hchk
  obtain ⟨b, hb, hlv, hnp, hnc, hslots⟩ := ctorSlots_of_member_lim hbound hS hrec hchk
  have hsame := Reads.functional hroles hfr (hfr₀ {})
  obtain ⟨caps, hcaps⟩ : ∃ caps, fr = .indInfo
      ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩ caps := by
    rcases hsame with e | ⟨cv, v, h₁, h₂, -, e⟩ | ⟨cv, c₁, c₂, e₁, e₂⟩
    · exact ⟨{}, e⟩
    · cases e
    · injection e₂ with ecv
      exact ⟨c₁, by rw [e₁, ecv]⟩
  refine ⟨ty₀, caps, cs, by rw [hcaps], hty, hlen, fun j c hc => ?_⟩
  have hj : j < ind.ctors.size := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨ct, tyj, h1, h2, h3, h4, h5, h6⟩ :=
    ctorSlot_reads ht hbound hS hrec hb hlv hnp hj (by omega) (hslots j hj)
  have hsame' := Reads.functional hroles (hcs j c hc) h6
  have hceq : c = .ctorInfo ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩
      ct.params.toNat ct.fields.toNat := by
    rcases hsame' with e | ⟨cv, v, h₁, h₂, -, e⟩ | ⟨cv, c₁, c₂, -, e⟩
    · exact e
    · cases e
    · cases e
  exact ⟨ct, tyj, h1, h2, h3, h4, h5, hceq, hcs j c hc⟩

end Member

/-! ## The recognition of the block -/


/-- **The declared block is recognised without its recursor**, at a former declared at its
telescope, with distinct constructor names. -/
theorem nativeParts_of_member_lim (ht : t.check = .ok ()) (hbound : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (htele : FormerAtTele t E₀ B cb ind) {blk : List (ConstantInfo .anon)}
    (hblk : BlockReadings t E₀ B ind blk)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x)) :
    ∃ p₀, Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀ ∧
      (p₀.ctors.map (·.1.name)).Nodup := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape_lim ht hbound hS hrec hchk hblk
  obtain ⟨bs, s, hts⟩ := htele ty₀ hty
  have hfreeF : Decl.KeyFree (keyOf t (memberAddr B 0 (.indc ind))) :=
    hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreeC : ∀ j, j < ind.ctors.size → Decl.KeyFree (keyOf t (ctorAddr B 0 j)) :=
    fun j hj => hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hlt : ∀ j c, cs[j]? = some c → j < ind.ctors.size := by
    intro j c hc
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hc).1
  obtain ⟨p₀, hp₀⟩ := nativePartsNoRec?_isSome (caps := caps) (cs := cs)
    (cvT := ⟨keyOf t (memberAddr B 0 (.indc ind)), List.range ind.lvls.toNat, ty₀⟩) hts
    (Nat.le_add_right _ _) hfreeF.1 (by
      intro c hc
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, tyj, -, -, hl, hp, -, rfl, -⟩ := hcs j c hj
      exact ⟨_, _, by rw [hp], by simp [hl], (hfreeC j (hlt j _ hj)).1⟩)
  refine ⟨p₀, hp₀, ?_⟩
  obtain ⟨caps₀, hshape, -⟩ := Decl.nativePartsNoRec?_inv hp₀
  injection hshape with _ hcs'
  have hnames : p₀.ctors.map (·.1.name) = cs.map (·.name) := by
    rw [hcs', List.map_map]
    rfl
  rw [hnames]
  obtain ⟨-, -, -, -, hnc, -⟩ := ctorSlots_of_member_lim hbound hS hrec hchk
  have hjb : ∀ {j}, j < ind.ctors.size → j < UInt64.size := fun hj => by
    show _ < 18446744073709551616
    omega
  refine nodup_names_of_index (f := fun j => keyOf t (ctorAddr B 0 j)) (fun j c hc => ?_)
    (fun j j' hj hj' e => ctorAddr_inj hrec hjb j j' (by omega) (by omega)
      (Core.keyOf_inj (a₁ := ctorAddr B 0 j) (a₂ := ctorAddr B 0 j') htwf e))
  obtain ⟨ct, tyj, -, -, -, -, -, rfl, -⟩ := hcs j c hc
  rfl

/-! ## The former stage -/

/-- **The reading of the former's type is closed, with its level parameters defined and no free
variable**: the walked check validated its scope before anything else (`Induct` arm prelude). -/
theorem former_scope_lim (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    {blob : _root_.Address → Option ByteArray} {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t blob cb id (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀) :
    ty₀.looseBVarsBounded 0 = true ∧
      ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧ ty₀.hasFvar = false := by
  have hchkA := memberCheckedLimAt_checkedLimAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedLimAt_loadedL1 hbound hchkA
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [idx_zero_lim B] at hms' raw
  have hind_eq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms'
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  obtain ⟨hlv, -, -, -, -, tyPtr, blkPtr, b, -, -, hv, rty⟩ := raw
  subst hv
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec (cx := readCtx t blob)
    (self := blockSelf t B #[.indc ind]) hbound hlv rty prelude.initialExtended hty
    prelude.scopeRun (hsub_chk _ prelude.scopeMember)
  exact ⟨hlbb, hdef, Assembly.memberReader_read_noFvar hty⟩

/-- **The former's stage of IxC at the prefix** (T6): the recognised block's former is checked
against the prefix as its canonical annotation, at a telescope ending in the block's sort, and
stored at the native capability record of the completed shape, for either recursion flag. The
former's key is the key of its projection address. -/

/-- **The member check's load bounds the record's counts.** -/
theorem member_bounds_lim {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {lim : Option Nat}
    (hbound : Bounded calls) (hS : LoadedReads.RunStore calls E₀)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim) :
    ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56 := by
  have hchkA := memberCheckedLimAt_checkedLimAt (mc := .indc ind) hbound hchk rfl
  obtain ⟨_, _, m_chk, _, rc, ap, ptr, v, r_chk, cs_ld, cs_chk, bytes, E_ld,
    _, _, _, _, hhash, hblake, hload_ld, hL1, hsub_ld, hld, ev_chk, _, hsub_chk⟩ :=
    Assembly.checkedLimAt_loadedL1 hbound hchkA
  have hrecP : Ix.Cert.recordAt E₀ (memberAddr B 0 (.indc ind)) =
      some (memberProjection B 0 (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.former
  have hrecB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt _).symm.trans hrec.record
  obtain ⟨-, -, v', hld', hraw⟩ := LoadedReads.loadedL1_record hS hsub_ld hhash hblake hL1 hrecP
  have hvv : v' = v := Except.ok.inj (hld'.symm.trans hld)
  subst hvv
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  unfold L1.RawCIRep at hraw
  rw [hinfo] at hraw
  obtain ⟨-, lcB, cb', ms', ind', blobs, hgetB, -, -, hexB, -, hcb', hms', -, raw⟩ := hraw
  obtain ⟨hhB, haB⟩ := hload_ld.1 _ lcB hgetB
  have hcb_eq : cb' = cb := hS.record_eq hrecB (Core.hashed_mono hsub_ld hhB) haB hexB
  subst cb'
  have hms_eq : ms' = #[.indc ind] := Ixon.ConstantInfo.muts.inj (hcb'.symm.trans hrec.muts)
  subst ms'
  rw [idx_zero_lim B] at hms' raw
  have hind_eq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms'
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  obtain ⟨hlv, hnp, hni, hnc, -⟩ := raw
  have h256 : (2 : Nat) ^ 56 = 72057594037927936 := by norm_num
  rw [h256]
  exact ⟨hnp, hni, hnc⟩

end Member


/-! ## The former checked at the prefix -/

/-- **The former of a native block, checked at the prefix.** From the walked check of member `0`
of the block at `B` under the walk's role context at the limit `lim`: the canonical annotation `ty'`
of the reading `ty₀` of the former's type is checked against the prefix environment
(`ConstantValCheckJ`, at the prefix's keying, where the former's own address does not resolve), and
it is typed there as a sort. The inputs about the prefix are the invariant, the references the
block uses stored, the former's key fresh and free. -/
theorem formerChecked_of_member_lim {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {lim : Option Nat} {env : Ix.Kernel.Env .anon}
    (hst : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hfv : ty₀.hasFvar = false)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0))) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ =
        some ty' ∧ Annotates ty' ty₀ ∧
      Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ ∧
      ∃ sty u, Ix.Kernel.Rules.Infer env .full 0 ty' sty ∧
        Ix.Kernel.Rules.Red env 0 sty (.sort u) := by
  have hbound : Bounded calls := (hst.good env none).2
  have hchkA := memberCheckedLimAt_checkedLimAt (mc := .indc ind) hbound hchk (by rfl)
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre,
    ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchkA
  obtain ⟨a, ha, hax⟩ := ha_pre
  have hgood : Core.Good ⟨E, env, t, lim⟩ calls := hst.good env lim
  have hg_ld : Core.Good ⟨E, env, t, lim⟩ cs_load := hgood.sub hsub_ld
  have hg_chk : Core.Good ⟨E, env, t, lim⟩ cs_chk := hgood.sub hsub_chk
  have h0' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  -- the load of the member's projection record, traced
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrec : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hproj
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B 0 (.indc ind) := by
    rw [hb, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts))
  subst hmsEq
  rw [h0'] at hms planned hraw
  have hiEq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst typePtr
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hg_ld.1 hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon_exact ht hlvls (LoadedReads.blockSelf_key t B #[.indc ind])
      hagree rty built planned trace hty hty_lbb hty_def
  -- the prelude of the check
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  -- the references the block uses are stored in the prefix
  have used : ∀ x, L1.RefUsed cb.refs.toList cb.sharing.toList ind.typ x →
      ∃ ci, env.find? (Core.keyOf t x) = some ci := by
    have hmem' : Ixon.MutConst.indc ind ∈ (#[.indc ind] : Array Ixon.MutConst).toList :=
      List.mem_singleton.mpr rfl
    intro x hu
    obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      rw [hmuts]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.indc ind, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
  let κP := (Core.Ctx.stored ⟨E, env, t, lim⟩).κ
  have hextM : Heap.Extends m_chk prelude.mentionsBefore :=
    prelude.initialExtended.trans prelude.scope_to_mentions
  have hagreeP : ∀ a', Core.AddrIn m_chk tyPtr a' →
      κP (Core.ixAddr a') = Core.keyOf t (Core.ixAddr a') := by
    intro a' hin
    rcases rty.addrIn_used a' hin with hu | hr
    · obtain ⟨ci, hci⟩ := used _ hu
      exact Core.Ctx.stored_key_of_find (c := ⟨E, env, t, lim⟩) hci
    · exfalso
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨m, hm, hxm⟩ := LoadedReads.blockRecurAddrs_get hk
      have hk0 : k = 0 := by
        have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
        omega
      subst hk0
      have hmm : m = .indc ind := by simpa using hm.symm
      subst hmm
      rw [LoadedReads.memberAddr_indc] at hxm
      have hxm' : Core.ixAddr a' = Core.iprjAddr B 0 := hxm
      have hscan := mentions_block_cells (c := ⟨E, env, t, lim⟩) hst.decoded hblock hmuts hproj
        hb_eq hin hextM (prelude.blocksRep hb_rep) prelude.mentionsRun
        (hg_chk.sub prelude.mentionsSubset)
      rcases hscan with hp | hne
      · obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
        rw [hxm', hfresh] at hci
        cases hci
      · exact hne hxm'
  have hpermP : ∀ a', Core.ProjIn m_chk tyPtr a' →
      Core.ProjPermitted (Core.keyOf t) (Core.ixAddr a') → Core.ProjPermitted κP (Core.ixAddr a') := by
    intro a' hp _
    obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
    exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, lim⟩) hci
  have htmP : Decl.TmCExact κP m_chk (Core.posOf (List.range ind.lvls.toNat) ty') tyPtr :=
    TmCExact.rekey htmT hagreeP hpermP
  have hvP : Decl.ValRepExact κP m_chk (.field (ind.lvls.toNat : F)) tyPtr
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ :=
    ⟨by simp, by simpa using hlvls, by simp, htmP⟩
  have hgS : Core.CoreGood (Core.Ctx.stored ⟨E, env, t, lim⟩) prelude.sortCalls :=
    Core.CoreGood.ofRaw (hg_chk.sub prelude.sortSubset) (fun _ _ => trivial)
  obtain ⟨checked, sty, u, ℓ, inferred, reduced, -, -⟩ :=
    Decl.constantValCheckJ_of_scoped (c := Core.Ctx.stored ⟨E, env, t, lim⟩)
      (cv := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩)
      (cv' := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩)
      ⟨rfl, rfl, hannT⟩ (hvP.mono prelude.initialExtended) hty_lbb hfv hfresh hfree.1
      (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) hinv.store.store
      (Decl.PosSortLift.of_range rfl) prelude.scopeRun prelude.scope_to_sort
      (hrc_m.toRCRep.mono (prelude.initialExtended.trans prelude.scope_to_sort))
      (prelude.typesRep κP (fun _ => default)) hinv.scopedCoreFacts.1 hinv.loads hgS
      prelude.sortRun
  rw [Decl.posOf_range] at inferred
  exact ⟨ty', hcT, hannT, checked, sty, u, inferred, reduced⟩

/-- **IxC's former stage at a syntactic telescope**: the checked former is the telescope constant
and the stored former; the record is completed with the sort the telescope ends in, and the
former is stored at the capability record of that completed record. -/
end IxVM.Refinement.Typing
