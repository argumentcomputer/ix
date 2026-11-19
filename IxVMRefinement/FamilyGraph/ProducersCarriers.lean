import IxVMRefinement.FamilyGraph.ProducersGraph
import IxVMRefinement.Assembly.NativeFormerLength
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Binding.BlockSafety
import IxVMRefinement.Binding.FamilyOf
import IxVMRefinement.Binding.PayloadDirectLoads
import IxVMRefinement.Claim.TopSeed
import IxVMRefinement.FamilyAlias.CallLists
import IxVMRefinement.L1.Ingress
import IxVMRefinement.Obs.Convert1
import IxVMRefinement.Obs.Ingress0
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelModeled0
import IxVMRefinement.Obs.KernelModeled2
import IxVMRefinement.Obs.KernelModeled3
import IxVMRefinement.Obs.KernelModeled4
import IxVMRefinement.Obs.KernelModeled5
import IxVMRefinement.Obs.KernelTypes0

/-! # Carrier extraction, logic safety, and block uniqueness from `check_family`

Extracts structural facts from any observed `KernelModeled::check_family` run without requiring
run-level bounds or collision-freedom beyond `TopWalkCore`:

* `motiveCarrierAt_usedRef`: the constant at the head of a motive carrier read by
  `Binding.FamilyOf.motiveCarrierAt` is a used reference of the family record;
* `get_ci_rprj_raw_uncond` and `get_ci_of_rPrj_raw`: unconditional raw expression representation
  of a recursor projection loaded by `Ingress::get_ci`;
* `rawConvExpr_node`, `peel_n_foralls_raw`, `last_binder_dom_raw`, `collect_spine_raw`,
  `check_carriers_raw_head`: connects `KernelModeled::check_carriers` on a raw converted recursor
  type both to `Binding.FamilyOf.motiveCarrierAt` at motive `0` and to a `KExprSub` witness for
  its head `Const` cell;
* `safe_refs_only_raw_sub`: boolean dichotomy and subexpression descent for
  `KernelCheck::safe_refs_only` on any `L1.RawConvExpr`, yielding `ind₀.isUnsafe = false` from
  `KernelCheck::assert_safety` on a family recursor type;
* `assert_no_role_spec`: `KernelModeled::assert_no_role` certifies that no listed recursor
  projection address is bound to any role;
* `FamRunCtx.check_family_carriers`: bundles the block/record facts, first-type projection hash,
  role-freeness, motive-0 carrier, and member-0 safety of any `FamCheck B rb`;
* `FamRunCtx.inLogic_of` and `FamRunCtx.blockOf_of`: discharge the `inLogic` and `blockOf`
  obligations of `BatchGives`.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-! ## `motiveCarrierAt` yields a used reference of the family record -/

private def CarrierExprRefsIn (c : Ixon.Constant) (e : Ixon.Expr) : Prop :=
  ∀ i ∈ S0.exprRefIdxs e, i ∈ S0.usedRefIdxs c

private theorem carrierExprRefsIn_sharing (c : Ixon.Constant) {i : Nat} {e : Ixon.Expr}
    (h : c.sharing[i]? = some e) : CarrierExprRefsIn c e := by
  intro j hj
  unfold S0.usedRefIdxs
  apply List.mem_append_left
  rw [List.mem_flatMap]
  refine ⟨e, ?_, hj⟩
  have hL : c.sharing.toList[i]? = some e := by rw [Array.getElem?_toList]; exact h
  exact List.mem_of_getElem? hL

private theorem carrierExprRefsIn_unshare (c : Ixon.Constant) :
    ∀ (k : Nat) (e : Ixon.Expr),
      CarrierExprRefsIn c e → CarrierExprRefsIn c (Binding.FamilyOf.unshare c k e)
  | 0, _, h => h
  | k + 1, .share i, _ => by
    unfold Binding.FamilyOf.unshare
    cases hs : c.sharing[i.toNat]? with
    | none => intro j hj; cases hj
    | some e' => exact carrierExprRefsIn_unshare c k e' (carrierExprRefsIn_sharing c hs)
  | _ + 1, .sort _, h | _ + 1, .var _, h | _ + 1, .ref _ _, h | _ + 1, .recur _ _, h
  | _ + 1, .prj _ _ _, h | _ + 1, .str _, h | _ + 1, .nat _, h | _ + 1, .app _ _, h
  | _ + 1, .lam _ _, h | _ + 1, .all _ _, h | _ + 1, .letE _ _ _ _ _, h => h

private theorem carrierExprRefsIn_node (c : Ixon.Constant) {e : Ixon.Expr}
    (h : CarrierExprRefsIn c e) : CarrierExprRefsIn c (Binding.FamilyOf.node c e) :=
  carrierExprRefsIn_unshare c (c.sharing.size + 1) e h

private theorem carrierExprRefsIn_peel (c : Ixon.Constant) :
    ∀ (n : Nat) {e e' : Ixon.Expr},
      CarrierExprRefsIn c e → Binding.FamilyOf.peel c n e = some e' → CarrierExprRefsIn c e'
  | 0, _, _, h, hp => by cases hp; exact h
  | n + 1, e, _, h, hp => by
    unfold Binding.FamilyOf.peel at hp
    have hn := carrierExprRefsIn_node c h
    cases hnd : Binding.FamilyOf.node c e with
    | all d b =>
      rw [hnd] at hp hn
      exact carrierExprRefsIn_peel c n (fun j hj => hn j (List.mem_append_right _ hj)) hp
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
    | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hp; cases hp

private theorem carrierExprRefsIn_domOf (c : Ixon.Constant) {e d : Ixon.Expr}
    (h : CarrierExprRefsIn c e) (hd : Binding.FamilyOf.domOf c e = some d) :
    CarrierExprRefsIn c d := by
  unfold Binding.FamilyOf.domOf at hd
  have hn := carrierExprRefsIn_node c h
  cases hnd : Binding.FamilyOf.node c e with
  | all d' b =>
    rw [hnd] at hd hn
    cases hd
    exact fun j hj => hn j (List.mem_append_left _ hj)
  | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
  | letE _ _ _ _ _ | share _ =>
    rw [hnd] at hd; cases hd

private theorem carrierExprRefsIn_lastDom (c : Ixon.Constant) :
    ∀ (n : Nat) {e d : Ixon.Expr},
      CarrierExprRefsIn c e → Binding.FamilyOf.lastDom c n e = some d → CarrierExprRefsIn c d
  | 0, _, _, _, hl => by simp [Binding.FamilyOf.lastDom] at hl
  | n + 1, e, d, h, hl => by
    unfold Binding.FamilyOf.lastDom at hl
    have hn := carrierExprRefsIn_node c h
    cases hnd : Binding.FamilyOf.node c e with
    | all d' b =>
      rw [hnd] at hl hn
      cases hb : Binding.FamilyOf.node c b with
      | all _ _ =>
        rw [hb] at hl
        exact carrierExprRefsIn_lastDom c n (fun j hj => hn j (List.mem_append_right _ hj)) hl
      | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
      | letE _ _ _ _ _ | share _ =>
        rw [hb] at hl
        cases hl
        exact fun j hj => hn j (List.mem_append_left _ hj)
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
    | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hl; cases hl

private theorem carrierExprRefsIn_spineHead (c : Ixon.Constant) :
    ∀ (n : Nat) (e : Ixon.Expr),
      CarrierExprRefsIn c e → CarrierExprRefsIn c (Binding.FamilyOf.spineHead c n e)
  | 0, e, h => carrierExprRefsIn_node c h
  | n + 1, e, h => by
    unfold Binding.FamilyOf.spineHead
    have hn := carrierExprRefsIn_node c h
    cases hnd : Binding.FamilyOf.node c e with
    | app f a =>
      rw [hnd] at hn
      exact carrierExprRefsIn_spineHead c n f (fun j hj => hn j (List.mem_append_left _ hj))
    | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | lam _ _ | all _ _
    | letE _ _ _ _ _ | share _ =>
      rw [hnd] at hn; exact hn

/-- **The head constant of a recursor's motive carrier is a used reference of its block record.** -/
theorem motiveCarrierAt_usedRef {E₀ : Ixon.Env} {rb a : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} {k i n : Nat} {r : Ixon.Recursor}
    (hrec : recordOf E₀ rb = some crb) (hmuts : crb.info = .muts rs)
    (hr : rs[k]? = some (.recr r))
    (hmot : Binding.FamilyOf.motiveCarrierAt crb r i n = some a) :
    UsedRef E₀ rb a := by
  have htyp : CarrierExprRefsIn crb r.typ := by
    intro j hj
    unfold S0.usedRefIdxs
    rw [hmuts]
    apply List.mem_append_right
    rw [List.mem_flatMap]
    refine ⟨.recr r, ?_, List.mem_append_left _ hj⟩
    have hL : rs.toList[k]? = some (.recr r) := by rw [Array.getElem?_toList]; exact hr
    exact List.mem_of_getElem? hL
  unfold Binding.FamilyOf.motiveCarrierAt at hmot
  cases hp : Binding.FamilyOf.peel crb (r.params.toNat + i) r.typ with
  | none => rw [hp] at hmot; simp at hmot
  | some e =>
    rw [hp] at hmot
    dsimp only [bind, Option.bind] at hmot
    cases hd : Binding.FamilyOf.domOf crb e with
    | none => rw [hd] at hmot; simp at hmot
    | some m =>
      rw [hd] at hmot
      dsimp only [bind, Option.bind] at hmot
      cases hl : Binding.FamilyOf.lastDom crb n m with
      | none => rw [hl] at hmot; simp at hmot
      | some d =>
        rw [hl] at hmot
        dsimp only [bind, Option.bind] at hmot
        have hsp := carrierExprRefsIn_spineHead crb n d
          (carrierExprRefsIn_lastDom crb n
            (carrierExprRefsIn_domOf crb (carrierExprRefsIn_peel crb _ htyp hp) hd) hl)
        unfold Binding.FamilyOf.refHeadAt at hmot
        cases hsh : Binding.FamilyOf.spineHead crb n d with
        | ref idx _ =>
          rw [hsh] at hmot hsp
          refine ⟨crb, idx.toNat, hrec, ?_, hmot⟩
          rw [← Assembly.usedRefIdxs_eq]
          exact hsp idx.toNat (List.mem_singleton_self _)
        | sort _ | var _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _ | all _ _
        | letE _ _ _ _ _ | share _ =>
          rw [hsh] at hmot; cases hmot

/-! ## Unconditional raw conversion of a recursor projection -/

private theorem val_cast_lt_u56 {n : Nat} (hn : n < 72057594037927936) :
    ((n : F)).val = n := by
  have hlt : n < Aiur.Library.U32.Goldilocks.modulus := by
    change n < 18446744069414584321
    omega
  change (n : ZMod Aiur.Library.U32.Goldilocks.modulus).val = n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

private theorem val_cast_le_u56 {n : Nat} (hn : n ≤ 72057594037927936) :
    ((n : F)).val = n := by
  have hlt : n < Aiur.Library.U32.Goldilocks.modulus := by
    change n < 18446744069414584321
    omega
  change (n : ZMod Aiur.Library.U32.Goldilocks.modulus).val = n
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

private theorem get_ci_rprj_raw_uncond {b : Bytes.Address} {idx : F}
    {x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn Obs.W "Ingress::get_ci_rprj" [x_block_addr, .field idx] h r h' calls) :
    Heap.Extends h h' ∧
      idx.val < 72057594037927936 ∧
      ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
        (rc : Ixon.Recursor) (blobs : List (_root_.Address × ByteArray)) (v : SourceValue F),
        Hashed calls blkBytes ∧
        _root_.Address.blake3Pure blkBytes = Core.ixAddr b ∧
        Ixon.deConstantExact blkBytes = .ok cb ∧
        cb.info = .muts ms ∧
        ms.toList[idx.val]? = some (.recr rc) ∧
        loadValue h' r = .ok v ∧
        L1.RawRecrValRep cb.refs.toList (L1.blockRecurAddrs (Core.ixAddr b) ms.toList)
          cb.univs.toList cb.sharing.toList blobs h' rc (Core.ixAddr b) idx.val v := by
  obtain ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_members,
      m86, cs96, x_r, v136, m137, cs147, v166, m167, cs174,
      v184, v185, m236, cs244, m256, cs264,
      ev14, ev98, ev149, he170, hm169, ev246, ev266, ev176, hc283⟩ :=
    Obs.«Ingress::get_ci_rprj».obs ev
  obtain ⟨ext1, blkList, cb, hlen_blk, hhash_blk, haddr_blk, hexact_blk, -,
      -, -, -, hbd32, -, cRep⟩ :=
    L1.load_verified_constant_decode_bounded hb ev14
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
  subst infoVal shPtr rfPtr unPtr bdPtr
  obtain ⟨ms, hcb_info, hms⟩ := L1.repConstantInfo_muts_inv hinfo
  obtain ⟨hm86, hidx_lt_ms, mc, hmc_get, hmc_rep⟩ := L1.muts_member_at_spec hms ev98
  subst m86
  have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound ⟨blkList.toArray⟩ cb hexact_blk
  have hms_le := Claim.muts_size_le hcb_info
  have hidx56 : idx.val < 72057594037927936 := by
    simp only [ByteArray.size, List.size_toArray] at hres
    rw [Array.length_toList] at hidx_lt_ms
    omega
  have hrecr : ∃ rc : Ixon.Recursor, mc = .recr rc ∧ L1.RepRecursor m2 rc x_r := by
    cases mc with
    | recr rc =>
      obtain ⟨rv, hrv_eq, hrv⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hrv_eq
      rcases hrv_eq with ⟨_, _, rfl⟩
      exact ⟨rc, rfl, hrv⟩
    | defn _ => obtain ⟨dv, hdv, _⟩ := hmc_rep; simp at hdv
    | indc _ => obtain ⟨iv, hiv, _⟩ := hmc_rep; simp at hiv
  obtain ⟨rc, rfl, hrc_rep⟩ := hrecr
  have hb2 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb
  obtain ⟨ext2, hrecs⟩ := L1.build_recur_addrs_ixon_spec hms hb2 ev149
  obtain ⟨ext3, htbl⟩ := L1.binder_table_spec (hbd.mono L1.repBinderBlock_heapMono₂ ext2) hbd32 ev246
  have ext23 := ext2.trans ext3
  obtain ⟨_, _, hm256⟩ := L1.muts_root_offset_spec (hms.mono L1.repMutConst_heapMono₂ ext23) ev266
  subst m256
  have ev176' : ObsFn Obs.W "Convert::convert_recursor"
      [x_r, x_block_addr, .field ((idx.val : Nat) : F), x_sharing, x_refs, v136,
       x_univs, v184, v185] m236 v166 m167 cs174 := by
    rwa [ZMod.natCast_zmod_val idx]
  obtain ⟨ext4, blobs, -, hraw⟩ :=
    L1.convert_recursor_spec
      (hrc_rep.mono ext23)
      ((L1.core_to_repIxonAddressRef hb2).mono ext23)
      hidx56
      (L1.RepShareVec.mono ext23 hsh)
      (hrf.mono L1.repIxonAddressRef_heapMono₂ ext23)
      (hrecs.mono L1.repIxonAddressRef_heapMono₂ ext3)
      (hun.mono L1.repUnivPtr_heapMono₂ ext23)
      htbl ev176'
  rw [he170, hm169]
  have ext_snoc := Heap.Extends.snoc m167 v166
  exact ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), hidx56,
    ⟨blkList.toArray⟩, cb, ms, rc, blobs, v166,
    Core.hashed_mono (by rw [hc283]; intro x hx; simp [hx]) hhash_blk,
    haddr_blk, hexact_blk, hcb_info, hmc_get,
    Claim.loadValue_snoc_self m167 v166,
    hraw.mono ext_snoc (fun _ hm => hm)⟩

private theorem get_ci_of_rPrj_raw {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {ab : Bytes.Address} {x_r ptr v : SourceValue F} {h h' : Heap F}
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    {k : Nat} {rc : Ixon.Recursor}
    (hS : LoadedReads.RunStore calls E₀)
    (hrb : FamRecRecord E₀ rb crb rs)
    (hk : rs[k]? = some (.recr rc))
    (hk_lt : k < 72057594037927936)
    (hab : Bytes.RepAddressRef Core.addrTy h ab x_r)
    (hix : Core.ixAddr ab = memberAddr rb k (.recr rc))
    (ev : ObsFn Obs.W "Ingress::get_ci" [x_r] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (hld : loadValue h' ptr = .ok v) :
    ∃ blobs,
      L1.RawRecrValRep crb.refs.toList (L1.blockRecurAddrs rb rs.toList)
        crb.univs.toList crb.sharing.toList blobs h' rc rb k v := by
  have hprojRec : recordOf E₀ (Core.ixAddr ab) = some (memberProjection rb k (.recr rc)) := by
    rw [hix]
    exact hrb.members k (.recr rc) hk
  match Obs.«Ingress::get_ci».obs ev with
  | .RPrj (cs12 := cs12) (cs894 := cs894) (ev14 := ev14) (ev917 := ev917) (ev896 := ev896)
      (hc926 := hcs) .. =>
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    have hsub894 : ∀ cl ∈ cs894, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨-, rawList, c, -, hhash, haddr, hexact, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    have hc_eq_proj : c = memberProjection rb k (.recr rc) :=
      hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hprojRec)
        (Core.hashed_mono hsub12 hhash) haddr hexact
    subst c
    obtain ⟨infoVal, _, _, _, _, hc_mk, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_mk
    rcases hc_mk with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hp_eq, hx_idx, hblk_ix⟩ := L1.repConstantInfo_rPrj_inv hinfo
    have hp_val : p = ⟨k.toUInt64, rb⟩ := Ixon.ConstantInfo.rPrj.inj hp_eq.symm
    subst hp_val
    subst hx_idx
    obtain ⟨hidx56, hv898, hm907⟩ :=
      Lib.u64_to_field_spec (L1.Deserialize.repU64_u64Value _ k.toUInt64) ev917
    subst hv898 hm907
    obtain ⟨b_blk, hb_eq, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    obtain ⟨-, -, blkBytes, cb, ms, rc', blobs, v',
        hhash_blk, haddr_blk, hexact_blk, hcb_info, hmc_get, hld', hraw⟩ :=
      get_ci_rprj_raw_uncond hb_rep ev896
    have hv_eq : v' = v := Except.ok.inj (hld'.symm.trans hld)
    subst hv_eq
    have hcb_eq : cb = crb :=
      hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans (hb_eq ▸ hrb.record))
        (Core.hashed_mono hsub894 hhash_blk) haddr_blk hexact_blk
    subst cb
    have hms_eq : ms = rs := Ixon.ConstantInfo.muts.inj (hcb_info.symm.trans hrb.muts)
    subst ms
    have hk_u64 : k.toUInt64.toNat = k :=
      Ixon.Verify.TagN.toUInt64_toNat_of_lt (Nat.lt_trans hk_lt (by decide))
    have hidx_val : ((k.toUInt64.toNat : F)).val = k := by
      rw [hk_u64]
      exact val_cast_lt_u56 hk_lt
    rw [hidx_val] at hmc_get hraw
    rw [hb_eq] at hraw
    have hkL : rs.toList[k]? = some (.recr rc) := by rw [Array.getElem?_toList]; exact hk
    have hrc_eq : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj (hmc_get.symm.trans hkL))
    subst rc'
    exact ⟨blobs, hraw⟩
  | .Defn_n0 (cs12 := cs12) (ev14 := ev14) (hc302 := hcs) ..
  | .Defn_other (cs12 := cs12) (ev14 := ev14) (hc423 := hcs) ..
  | .Axio (cs12 := cs12) (ev14 := ev14) (hc515 := hcs) ..
  | .Quot (cs12 := cs12) (ev14 := ev14) (hc606 := hcs) ..
  | .DPrj (cs12 := cs12) (ev14 := ev14) (hc675 := hcs) ..
  | .IPrj (cs12 := cs12) (ev14 := ev14) (hc750 := hcs) ..
  | .CPrj (cs12 := cs12) (ev14 := ev14) (hc851 := hcs) ..
  | .Recr (cs12 := cs12) (ev14 := ev14) (hc1071 := hcs) .. =>
    exfalso
    have hsub12 : ∀ cl ∈ cs12, cl ∈ calls := fun cl hcl => hsub cl (by rw [hcs]; simp [hcl])
    obtain ⟨-, raw1, c1, -, hh1, hba1, -, hde1, cRep1, -⟩ :=
      Claim.load_verified_constant_de ⟨ab, hab, rfl⟩ ev14
    have hc1 : c1 = memberProjection rb k (.recr rc) :=
      hS.record_eq ((hS.recordOf_eq_recordAt _).symm.trans hprojRec)
        (Claim.hashed_mono hsub12 hh1) hba1 hde1
    subst c1
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := cRep1
    have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
    obtain ⟨pv, hpv, -⟩ := hinfoRep
    exact absurd (Value.construct.inj (hinfo_eq.trans hpv)).2.1 (by decide)

/-! ## Subexpression relation and raw-expression bridge for `check_carriers` -/

/-- Structural subexpression reachability along `Forall` (domain or body) and `App` (function)
edges in a converted `KExprNode` heap. -/
inductive KExprSub (h : Heap F) : SourceValue F → SourceValue F → Prop where
  | refl (p : SourceValue F) : KExprSub h p p
  | forallDom {p d b bi q : SourceValue F} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Forall" [d, b, bi]) →
      KExprSub h d q → KExprSub h p q
  | forallBody {p d b bi q : SourceValue F} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "Forall" [d, b, bi]) →
      KExprSub h b q → KExprSub h p q
  | appFn {p f a q : SourceValue F} :
      loadValue h p = .ok (.construct "KernelTypes::KExprNode" "App" [f, a]) →
      KExprSub h f q → KExprSub h p q

theorem KExprSub.mono {h h' : Heap F} (ext : Heap.Extends h h') {p q : SourceValue F}
    (hs : KExprSub h p q) : KExprSub h' p q := by
  induction hs with
  | refl p => exact .refl p
  | forallDom ld _ ih => exact .forallDom (loadValue_mono ext ld) ih
  | forallBody ld _ ih => exact .forallBody (loadValue_mono ext ld) ih
  | appFn ld _ ih => exact .appFn (loadValue_mono ext ld) ih

theorem KExprSub.trans {h : Heap F} {p q r : SourceValue F}
    (h1 : KExprSub h p q) (h2 : KExprSub h q r) : KExprSub h p r := by
  induction h1 with
  | refl _ => exact h2
  | forallDom ld _ ih => exact .forallDom ld (ih h2)
  | forallBody ld _ ih => exact .forallBody ld (ih h2)
  | appFn ld _ ih => exact .appFn ld (ih h2)

private theorem rawConvExpr_unshare {c : Ixon.Constant} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp) :
    ∀ k, (bound ≤ k ∨ c.sharing.size ≤ k) →
      ∃ b', L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b'
        (Binding.FamilyOf.unshare c k e) kp ∧
        (∀ i, Binding.FamilyOf.unshare c k e ≠ .share i) := by
  induction raw with
  | @share bound idx s kp hidx hsh rs ih =>
    intro k hk
    have hlt_sz : idx.toNat < c.sharing.size := by
      have := (List.getElem?_eq_some_iff.mp hsh).1
      simpa only [Array.length_toList] using this
    have hlt_k : idx.toNat < k := by rcases hk with h1 | h2 <;> omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hget : c.sharing[idx.toNat]? = some s := by simpa only [Array.getElem?_toList] using hsh
    simp only [Binding.FamilyOf.unshare, hget]
    exact ih k' (Or.inl (by omega))
  | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | recur _ _ _ _ _ _ _
  | prj _ _ _ _ _ _ _ | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _
  | app _ _ _ | lam _ _ _ _ | all _ _ _ _ | letE _ _ _ _ =>
    rename_i bound' _
    intro k _
    cases k <;> exact ⟨_, by assumption, fun _ h => by cases h⟩

private theorem rawConvExpr_node {c : Ixon.Constant} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp) :
    ∃ b', L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b'
      (Binding.FamilyOf.node c e) kp ∧
      (∀ i, Binding.FamilyOf.node c e ≠ .share i) :=
  rawConvExpr_unshare raw (c.sharing.size + 1) (Or.inr (Nat.le_succ _))

private theorem rawConvExpr_forall_inv {c : Ixon.Constant} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp d b bi : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok (.construct "KernelTypes::KExprNode" "Forall" [d, b, bi])) :
    ∃ b' ed eb, Binding.FamilyOf.node c e = .all ed eb ∧
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b' ed d ∧
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b' eb b := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node raw
  cases raw' with
  | all _ rt rb cell =>
    have hxs := (Core.load_cell cell ld).2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl, rfl⟩ := hxs
    exact ⟨b', _, _, rfl, rt, rb⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ cell | sort _ _ _ cell | ref _ _ _ _ _ _ cell | recur _ _ _ _ _ _ cell
  | prj _ _ _ _ _ _ cell | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell
  | app _ _ cell | lam _ _ _ cell | letE _ _ _ cell =>
    exact (Core.load_cell_ne cell ld (by decide)).elim

private theorem rawConvExpr_not_forall_inv {c : Ixon.Constant}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat}
    {e : Ixon.Expr} {kp v : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 →
      v ≠ .construct "KernelTypes::KExprNode" "Forall" vs) :
    ∀ ed eb, Binding.FamilyOf.node c e ≠ .all ed eb := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node raw
  cases raw' with
  | all _ _ _ cell =>
    rw [Core.loadValue_enum_cell cell] at ld
    exact fun _ _ _ => hne [_, _, _] rfl (Except.ok.inj ld).symm
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ _ | sort _ _ _ _ | ref _ _ _ _ _ _ _ | recur _ _ _ _ _ _ _
  | prj _ _ _ _ _ _ _ | str _ _ _ _ _ _ | nat _ _ _ _ _ _ _ _
  | app _ _ _ | lam _ _ _ _ | letE _ _ _ _ =>
    intro _ _ he; cases he

private theorem rawConvExpr_app_inv {c : Ixon.Constant} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp f a : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok (.construct "KernelTypes::KExprNode" "App" [f, a])) :
    ∃ b' ef ea, Binding.FamilyOf.node c e = .app ef ea ∧
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b' ef f ∧
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b' ea a := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node raw
  cases raw' with
  | app rf ra cell =>
    have hxs := (Core.load_cell cell ld).2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact ⟨b', _, _, rfl, rf, ra⟩
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ cell | sort _ _ _ cell | ref _ _ _ _ _ _ cell | recur _ _ _ _ _ _ cell
  | prj _ _ _ _ _ _ cell | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell
  | lam _ _ _ cell | all _ _ _ cell | letE _ _ _ cell =>
    exact (Core.load_cell_ne cell ld (by decide)).elim

private theorem rawConvExpr_const_inv {c : Ixon.Constant} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {kp x_c w : SourceValue F}
    (raw : L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp)
    (ld : loadValue h kp = .ok (.construct "KernelTypes::KExprNode" "Const" [x_c, w])) :
    ∃ rIdx uIdxs a d, Binding.FamilyOf.node c e = .ref rIdx uIdxs ∧
      c.refs[rIdx.toNat]? = some a ∧
      Core.ixAddr d = a ∧
      Bytes.RepAddressRef Core.addrTy h d x_c := by
  obtain ⟨b', raw', hns⟩ := rawConvExpr_node raw
  cases raw' with
  | ref _ href hd ra _ _ cell =>
    have hxs := (Core.load_cell cell ld).2
    simp only [List.cons.injEq, and_true] at hxs
    obtain ⟨rfl, rfl⟩ := hxs
    exact ⟨_, _, _, _, rfl, by simpa only [Array.getElem?_toList] using href, hd, ra⟩
  | recur _ hrec _ _ _ _ _ => simp at hrec
  | share _ _ _ => exact (hns _ rfl).elim
  | var _ cell | sort _ _ _ cell | prj _ _ _ _ _ _ cell | str _ _ _ _ _ cell
  | nat _ _ _ _ _ _ _ cell | app _ _ cell | lam _ _ _ cell | all _ _ _ cell | letE _ _ _ cell =>
    exact (Core.load_cell_ne cell ld (by decide)).elim

private theorem peel_n_foralls_raw {c : Ixon.Constant} {blobs : List (_root_.Address × ByteArray)} :
    ∀ (n : Nat) {bound : Nat} {e : Ixon.Expr} {kp r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      n < 72057594037927936 →
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp →
      ObsFn Obs.W "KernelCheck::peel_n_foralls" [kp, .field (n : F)] h r h' cs →
      h' = h ∧ KExprSub h kp r ∧
        ∃ b' e', Binding.FamilyOf.peel c n e = some e' ∧
          L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b' e' r
  | 0, bound, e, kp, r, h, h', cs, _, raw, ev => by
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (he16 := hr) (he17 := hh) .. =>
      subst hr hh
      exact ⟨rfl, .refl kp, bound, e, rfl, raw⟩
    | .other (hne19 := hne) .. => exact (hne (by simp)).elim
  | n + 1, bound, e, kp, r, h, h', cs, hlt, raw, ev => by
    have hne0 : (.field ((n + 1 : Nat) : F) : SourceValue F) ≠ .field 0 := by
      intro he
      have hv := congrArg ZMod.val (Value.field.inj he)
      rw [val_cast_lt_u56 hlt] at hv
      simp at hv
    match Obs.«KernelCheck::peel_n_foralls».obs ev with
    | .n0 (hv14 := hv) .. => exact (hne0 hv).elim
    | .other (x_body := x_body) (v66 := v66) (ld34 := ld) (op87 := op) (ev64 := ev64) .. =>
      have hv66 : v66 = .field (n : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op
        rw [← op]
        push_cast
        ring_nf
      subst hv66
      obtain ⟨b₁, ed, eb, hnd, -, raw_b⟩ := rawConvExpr_forall_inv raw ld
      obtain ⟨hh, hsub, b₂, e', hpeel, raw'⟩ :=
        peel_n_foralls_raw n (by omega) raw_b ev64
      refine ⟨hh, .forallBody ld hsub, b₂, e', ?_, raw'⟩
      simp only [Binding.FamilyOf.peel, hnd]
      exact hpeel

private theorem last_binder_dom_raw_aux {c : Ixon.Constant}
    {blobs : List (_root_.Address × ByteArray)} :
    ∀ (m : Nat) {bound : Nat} {e : Ixon.Expr} {kp r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      cs.length ≤ m →
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp →
      ObsFn Obs.W "KernelModeled::last_binder_dom" [kp] h r h' cs →
      h' = h ∧ KExprSub h kp r ∧
        ∃ n b' ed, Binding.FamilyOf.lastDom c n e = some ed ∧
          L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h b' ed r
  | 0, bound, e, kp, r, h, h', cs, hlen, raw, ev => by
    match Obs.«KernelModeled::last_binder_dom».obs ev with
    | .Forall (hc87 := hc) .. => simp [hc] at hlen
    | .other (ld12 := ld12) (ld47 := ld47) (hne88 := hne) (he93 := hr) (he94 := hh) .. =>
      subst hr hh
      obtain ⟨b₁, ed, eb, hnd, raw_d, raw_b⟩ := rawConvExpr_forall_inv raw ld12
      have hnb := rawConvExpr_not_forall_inv raw_b ld47 hne
      refine ⟨rfl, .forallDom ld12 (.refl _), 1, b₁, ed, ?_, raw_d⟩
      simp only [Binding.FamilyOf.lastDom, hnd]
      cases hnb' : Binding.FamilyOf.node c eb with
      | all _ _ => exact (hnb _ _ hnb').elim
      | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
      | letE _ _ _ _ _ | share _ => rfl
  | m + 1, bound, e, kp, r, h, h', cs, hlen, raw, ev => by
    match Obs.«KernelModeled::last_binder_dom».obs ev with
    | .Forall (ld12 := ld12) (ld47 := ld47) (ev78 := ev78) (hc87 := hc) .. =>
      have hlen' : _ ≤ m := by rw [hc] at hlen; simp at hlen; omega
      obtain ⟨b₁, ed, eb, hnd, -, raw_b⟩ := rawConvExpr_forall_inv raw ld12
      obtain ⟨_, _, _, hnb, -, -⟩ := rawConvExpr_forall_inv raw_b ld47
      obtain ⟨hh, hsub, n, b₂, ed', hld, raw'⟩ := last_binder_dom_raw_aux m hlen' raw_b ev78
      refine ⟨hh, .forallBody ld12 hsub, n + 1, b₂, ed', ?_, raw'⟩
      simp only [Binding.FamilyOf.lastDom, hnd, hnb]
      exact hld
    | .other (ld12 := ld12) (ld47 := ld47) (hne88 := hne) (he93 := hr) (he94 := hh) .. =>
      subst hr hh
      obtain ⟨b₁, ed, eb, hnd, raw_d, raw_b⟩ := rawConvExpr_forall_inv raw ld12
      have hnb := rawConvExpr_not_forall_inv raw_b ld47 hne
      refine ⟨rfl, .forallDom ld12 (.refl _), 1, b₁, ed, ?_, raw_d⟩
      simp only [Binding.FamilyOf.lastDom, hnd]
      cases hnb' : Binding.FamilyOf.node c eb with
      | all _ _ => exact (hnb _ _ hnb').elim
      | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
      | letE _ _ _ _ _ | share _ => rfl

private theorem collect_spine_raw_aux {c : Ixon.Constant}
    {blobs : List (_root_.Address × ByteArray)} :
    ∀ (m : Nat) {bound : Nat} {e : Ixon.Expr} {kp hd sp : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      cs.length ≤ m →
      L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h bound e kp →
      ObsFn Obs.W "KernelTypes::collect_spine" [kp] h (.tuple [hd, sp]) h' cs →
      Heap.Extends h h' ∧ KExprSub h kp hd ∧
        ∃ n b',
          L1.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h' b'
            (Binding.FamilyOf.spineHead c n e) hd ∧
          (∀ i, Binding.FamilyOf.spineHead c n e ≠ .share i)
  | 0, bound, e, kp, hd, sp, h, h', cs, hlen, raw, ev => by
    match Obs.«KernelTypes::collect_spine».obs ev with
    | .App (hc106 := hc) .. => simp [hc] at hlen
    | .other (he115 := hr) (hm132 := hm) (he136 := hh) .. =>
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
      obtain ⟨rfl, -⟩ := hr
      have ext : Heap.Extends h h' := by rw [hh, hm]; exact Heap.Extends.snoc h _
      obtain ⟨b', raw', hns⟩ := rawConvExpr_node raw
      exact ⟨ext, .refl kp, 0, b', raw'.mono ext (fun _ hm => hm), hns⟩
  | m + 1, bound, e, kp, hd, sp, h, h', cs, hlen, raw, ev => by
    match Obs.«KernelTypes::collect_spine».obs ev with
    | .App (ld12 := ld12) (ev43 := ev43) (he69 := hr) (ev88 := ev88) (he105 := hh)
        (hc106 := hc) .. =>
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
      obtain ⟨rfl, -⟩ := hr
      have hlen' : _ ≤ m := by
        rw [hc] at hlen
        simp only [List.length_cons, List.length_append] at hlen
        omega
      obtain ⟨b₁, ef, ea, hnd, raw_f, -⟩ := rawConvExpr_app_inv raw ld12
      obtain ⟨ext1, hsub, n, b₂, raw', hns⟩ := collect_spine_raw_aux m hlen' raw_f ev43
      have ext2 : Heap.Extends _ h' := by rw [hh]; exact ev88.heap_extends
      refine ⟨ext1.trans ext2, .appFn ld12 hsub, n + 1, b₂, ?_, ?_⟩
      · simp only [Binding.FamilyOf.spineHead, hnd]
        exact raw'.mono ext2 (fun _ hm => hm)
      · simp only [Binding.FamilyOf.spineHead, hnd]
        exact hns
    | .other (he115 := hr) (hm132 := hm) (he136 := hh) .. =>
      simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hr
      obtain ⟨rfl, -⟩ := hr
      have ext : Heap.Extends h h' := by rw [hh, hm]; exact Heap.Extends.snoc h _
      obtain ⟨b', raw', hns⟩ := rawConvExpr_node raw
      exact ⟨ext, .refl kp, 0, b', raw'.mono ext (fun _ hm => hm), hns⟩

private theorem node_of_not_share {c : Ixon.Constant} {e : Ixon.Expr}
    (hns : ∀ i, e ≠ .share i) : Binding.FamilyOf.node c e = e := by
  unfold Binding.FamilyOf.node
  cases e with
  | share i => exact (hns i rfl).elim
  | sort _ | var _ | ref _ _ | recur _ _ | prj _ _ _ | str _ | nat _ | app _ _ | lam _ _
  | all _ _ | letE _ _ _ _ _ => rfl

/-- **`KernelModeled::check_carriers` on a raw converted recursor type**: connects motive `0` to
`Binding.FamilyOf.motiveCarrierAt` and produces a `KExprSub` witness for the head `Const` cell. -/
private theorem check_carriers_raw_head {crb : Ixon.Constant} {rc : Ixon.Recursor}
    {blobs : List (_root_.Address × ByteArray)} {b₀ : Bytes.Address} {bs : List Bytes.Address}
    {x_ty x_ta r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnp : rc.params.toNat < 72057594037927936)
    (raw : L1.RawConvExpr crb.refs.toList [] crb.univs.toList crb.sharing.toList blobs h
      4294967295 rc.typ x_ty)
    (hta : RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h (b₀ :: bs) x_ta)
    (ev : ObsFn Obs.W "KernelModeled::check_carriers"
      [x_ty, .field (rc.params.toNat : F), x_ta] h r h' cs) :
    (∃ n, Binding.FamilyOf.motiveCarrierAt crb rc 0 n = some (Core.ixAddr b₀)) ∧
      ∃ x_head x_c w145, KExprSub h' x_ty x_head ∧
        loadValue h' x_head = .ok (.construct "KernelTypes::KExprNode" "Const" [x_c, w145]) ∧
        Bytes.RepAddressRef Core.addrTy h' b₀ x_c := by
  match Obs.«KernelModeled::check_carriers».obs ev with
  | .run (ev20 := ev20) (ev6 := ev6) .. =>
    obtain ⟨rfl, hsub_peel, b₁, e₁, hpeel, raw₁⟩ := peel_n_foralls_raw rc.params.toNat hnp raw ev20
    match Obs.«KernelModeled::check_carriers_go».obs ev6 with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hta ld
    | .Cons (x_t := x_t) (x_mdom := x_mdom) (x_head := x_head) (x_c := x_c) (w145 := w145)
        (ld12 := ld12) (ld53 := ld53) (ev103 := ev103) (ev90 := ev90) (ld137 := ld137)
        (ev180 := ev180) (heq203 := heq203) (ev209 := ev209) .. =>
      obtain ⟨_, _, hcons, ht_rep, -⟩ := Lib.rep_cons_of_load hta ld12
      injection hcons with hb_eq _
      subst hb_eq
      obtain ⟨b₂, ed, eb, hnd₁, raw_d, -⟩ := rawConvExpr_forall_inv raw₁ ld53
      obtain ⟨rfl, hsub_ld, n₁, b₃, ed', hld, raw_d'⟩ :=
        last_binder_dom_raw_aux _ (Nat.le_refl _) raw_d ev103
      obtain ⟨ext_sp, hsub_sp, n₂, b₄, raw_sp, hns_sp⟩ :=
        collect_spine_raw_aux _ (Nat.le_refl _) raw_d' ev90
      obtain ⟨rIdx, uIdxs, a_c, d_c, hnd_sp, href_c, hd_c, hra_c⟩ :=
        rawConvExpr_const_inv raw_sp ld137
      rw [node_of_not_share hns_sp] at hnd_sp
      have ht_sp := Bytes.repAddressRef_heapMono₂ Core.addrTy ext_sp ht_rep
      obtain ⟨heq_c, rfl⟩ := Lib.address_eq_spec ev180 hra_c ht_sp
      have hd_eq : d_c = b₀ := by
        by_cases hdb : d_c = b₀
        · exact hdb
        · rw [if_neg hdb] at heq_c
          exact absurd (Value.field.inj (heq203.symm.trans heq_c)) (by decide)
      subst hd_eq
      have ext_tail : Heap.Extends _ h' := ev209.heap_extends
      refine ⟨⟨max n₁ n₂, ?_⟩, x_head, x_c, w145, ?_, loadValue_mono ext_tail ld137,
        Bytes.repAddressRef_heapMono₂ Core.addrTy ext_tail hra_c⟩
      · unfold Binding.FamilyOf.motiveCarrierAt
        rw [Nat.add_zero, hpeel]
        dsimp only [bind, Option.bind]
        have hdom : Binding.FamilyOf.domOf crb e₁ = some ed := by
          simp only [Binding.FamilyOf.domOf, hnd₁]
        rw [hdom]
        dsimp only [bind, Option.bind]
        rw [Binding.FamilyOf.lastDom_mono crb ed' n₁ (max n₁ n₂) ed hld (Nat.le_max_left _ _)]
        dsimp only [bind, Option.bind]
        have hrefAt : Binding.FamilyOf.refHeadAt crb n₂ ed' = some (Core.ixAddr d_c) := by
          unfold Binding.FamilyOf.refHeadAt
          rw [hnd_sp, hd_c]
          exact href_c
        exact Binding.FamilyOf.refHeadAt_mono hrefAt (Nat.le_max_right _ _)
      · have hsub_all : KExprSub _ x_ty x_head :=
          hsub_peel.trans (.forallDom ld53 (hsub_ld.trans hsub_sp))
        exact hsub_all.mono (ext_sp.trans ext_tail)

/-! ## `safe_refs_only` boolean dichotomy and subexpression descent -/

private theorem repBoolField_dichot (b : Bool) :
    L1.repBoolField b = .field 0 ∨ L1.repBoolField b = .field 1 := by
  cases b <;> simp [L1.repBoolField]

private theorem is_unsafe_ci_of_convert_definition_bool
    {x_d x_sh x_rf x_ra x_un x_ht x_tb x_bs ci r : SourceValue F}
    {h h1 h1' h2 : Heap F} {cs1 cs2 : List (Call F)}
    (ev_c : ObsFn Obs.W "Convert::convert_definition"
      [x_d, x_sh, x_rf, x_ra, x_un, x_ht, x_tb, x_bs] h ci h1 cs1)
    (ev_u : ObsFn Obs.W "KernelCheck::is_unsafe_ci" [ci] h1' r h2 cs2) :
    r = .field 0 ∨ r = .field 1 := by
  match Obs.«Convert::convert_definition».obs ev_c with
  | .Definition (he242 := hci) .. =>
    subst hci
    match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Defn_Safe (he90 := hr) .. => exact Or.inl hr
    | .Defn_other (he97 := hr) .. => exact Or.inr hr
    | .Axiom (hv15 := hv) .. | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) ..
    | .Quot (hv167 := hv) .. | .Induct (hv195 := hv) .. | .Ctor (hv253 := hv) ..
    | .Rec (hv311 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)
  | .Theorem (he373 := hci) .. =>
    subst hci
    match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Thm (he125 := hr) .. => exact Or.inl hr
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) .. | .Induct (hv195 := hv) ..
    | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)
  | .Opaque (sg321 := sg) (he329 := hci) .. =>
    subst hci
    match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Opaque (hv133 := hv) (he159 := hr) .. =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      obtain ⟨_, _, _, _, _, hxu⟩ := hv
      rw [hr, ← hxu]
      cases sg with
      | Unsafe _ he _ _ => exact Or.inr he
      | other _ he _ _ => exact Or.inl he
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Quot (hv167 := hv) .. | .Induct (hv195 := hv) ..
    | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)

private theorem is_unsafe_ci_of_bool_field {ci r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {b : Bool}
    (ev_u : ObsFn Obs.W "KernelCheck::is_unsafe_ci" [ci] h r h' cs)
    (hci : (∃ a1 a2, ci = .construct "KernelTypes::KConstantInfo" "Axiom"
              [a1, a2, L1.repBoolField b]) ∨
           (∃ a1 a2 a3, ci = .construct "KernelTypes::KConstantInfo" "Quot" [a1, a2, a3]) ∨
           (∃ a1 a2 a3 a4 a5 a6 a7, ci = .construct "KernelTypes::KConstantInfo" "Induct"
              [a1, a2, a3, a4, a5, L1.repBoolField b, a6, a7]) ∨
           (∃ a1 a2 a3 a4 a5 a6 a7, ci = .construct "KernelTypes::KConstantInfo" "Ctor"
              [a1, a2, a3, a4, a5, a6, a7, L1.repBoolField b]) ∨
           (∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, ci = .construct "KernelTypes::KConstantInfo" "Rec"
              [a1, a2, a3, a4, a5, a6, a7, a8, L1.repBoolField b, a9, a10])) :
    r = .field 0 ∨ r = .field 1 := by
  rcases hci with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Axiom (hv15 := hv) (he35 := hr) .. =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rw [hr, ← hv.2.2.2.2]; exact repBoolField_dichot b
    | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) .. | .Thm (hv105 := hv) ..
    | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) .. | .Induct (hv195 := hv) ..
    | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Quot (he187 := hr) .. => exact Or.inl hr
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Induct (hv195 := hv) ..
    | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Induct (hv195 := hv) (he245 := hr) .. =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rw [hr, ← hv.2.2.2.2.2.2.2.1]; exact repBoolField_dichot b
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) ..
    | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Ctor (hv253 := hv) (he303 := hr) .. =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rw [hr, ← hv.2.2.2.2.2.2.2.2.2]; exact repBoolField_dichot b
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) ..
    | .Induct (hv195 := hv) .. | .Rec (hv311 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)
  · match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
    | .Rec (hv311 := hv) (he379 := hr) .. =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
      rw [hr, ← hv.2.2.2.2.2.2.2.2.2.2.1]; exact repBoolField_dichot b
    | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
    | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) ..
    | .Induct (hv195 := hv) .. | .Ctor (hv253 := hv) .. =>
      exact absurd (Value.construct.inj hv).2.1 (by decide)

private theorem get_ci_is_unsafe_bool {ab : Bytes.Address} {x_addr ptr ci r : SourceValue F}
    {h h1 h2 : Heap F} {cs1 cs2 : List (Call F)}
    (hab : Bytes.RepAddressRef Core.addrTy h ab x_addr)
    (ev_ci : ObsFn Obs.W "Ingress::get_ci" [x_addr] h ptr h1 cs1)
    (hld : loadValue h1 ptr = .ok ci)
    (ev_u : ObsFn Obs.W "KernelCheck::is_unsafe_ci" [ci] h1 r h2 cs2) :
    r = .field 0 ∨ r = .field 1 := by
  match Obs.«Ingress::get_ci».obs ev_ci with
  | .Defn_n0 (v215 := v) (m216 := m) (he219 := he) (hm218 := hm) (ev225 := evc) .. =>
    rw [he, hm, Claim.loadValue_snoc_self m v] at hld
    have hv : v = ci := Except.ok.inj hld
    subst hv
    exact is_unsafe_ci_of_convert_definition_bool evc ev_u
  | .Defn_other (v336 := v) (m337 := m) (he340 := he) (hm339 := hm) (ev346 := evc) .. =>
    rw [he, hm, Claim.loadValue_snoc_self m v] at hld
    have hv : v = ci := Except.ok.inj hld
    subst hv
    exact is_unsafe_ci_of_convert_definition_bool evc ev_u
  | .DPrj (ev650 := evdp) .. =>
    match Obs.«Ingress::get_ci_dprj».obs evdp with
    | .run (v226 := v) (m227 := m) (he230 := he) (hm229 := hm) (ev236 := evc) .. =>
      rw [he, hm, Claim.loadValue_snoc_self m v] at hld
      have hv : v = ci := Except.ok.inj hld
      subst hv
      exact is_unsafe_ci_of_convert_definition_bool evc ev_u
  | .Axio (m438 := m) (ev14 := ev14) (he441 := he) (hm440 := hm) (ev447 := conv) .. =>
    obtain ⟨-, _, c, -, -, -, -, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨ax, -, _, hav, -⟩ := L1.repConstantInfo_axio_inv hinfo
    match Obs.«Convert::convert_axiom».obs conv with
    | .run (hv15 := hx) (he107 := hcv) .. =>
      have hu := hav.symm.trans hx
      injection hu with _ _ hargs
      injection hargs with hflag _
      rw [he, hm, Claim.loadValue_snoc_self m _, hcv, ← hflag] at hld
      exact is_unsafe_ci_of_bool_field (b := ax.isUnsafe) ev_u
        (Or.inl ⟨_, _, (Except.ok.inj hld).symm⟩)
  | .Quot (m529 := m) (he532 := he) (hm531 := hm) (ev538 := conv) .. =>
    match Obs.«Convert::convert_quotient».obs conv with
    | .run (he107 := hcv) .. =>
      rw [he, hm, Claim.loadValue_snoc_self m _, hcv] at hld
      exact is_unsafe_ci_of_bool_field (b := false) ev_u
        (Or.inr (Or.inl ⟨_, _, _, (Except.ok.inj hld).symm⟩))
  | .IPrj (ev14 := ev14) (ev741 := ev741) (ev720 := ev720) .. =>
    obtain ⟨-, _, c, -, -, -, -, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, -, hx_idx, hblk_ix⟩ := L1.repConstantInfo_iPrj_inv hinfo
    subst hx_idx
    obtain ⟨-, hv722, hm731⟩ :=
      Lib.u64_to_field_spec (L1.Deserialize.repU64_u64Value _ p.idx) ev741
    subst hv722 hm731
    obtain ⟨b_blk, -, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    obtain ⟨_, _, ind, -, -, _, _, _, _, hld'⟩ := Claim.get_ci_iprj_head hb_rep ev720
    exact is_unsafe_ci_of_bool_field (b := ind.isUnsafe) ev_u
      (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _, Except.ok.inj (hld.symm.trans hld')⟩)))
  | .CPrj (ev14 := ev14) (ev822 := ev822) (ev842 := ev842) (ev800 := ev800) .. =>
    obtain ⟨-, _, c, -, -, -, -, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, -, hx_idx, hx_cidx, hblk_ix⟩ := L1.repConstantInfo_cPrj_inv hinfo
    subst hx_idx hx_cidx
    obtain ⟨-, hv802, hm812⟩ :=
      Lib.u64_to_field_spec (L1.Deserialize.repU64_u64Value _ p.idx) ev822
    subst hv802 hm812
    obtain ⟨-, hv803, hm832⟩ :=
      Lib.u64_to_field_spec (L1.Deserialize.repU64_u64Value _ p.cidx) ev842
    subst hv803 hm832
    obtain ⟨b_blk, -, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    obtain ⟨_, _, _, -, -, -, ct, -, _, _, _, _, _, hld'⟩ := Claim.get_ci_cprj_head hb_rep ev800
    exact is_unsafe_ci_of_bool_field (b := ct.isUnsafe) ev_u
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, _, _, _, _, _, _,
        Except.ok.inj (hld.symm.trans hld')⟩))))
  | .RPrj (ev14 := ev14) (ev917 := ev917) (ev896 := ev896) .. =>
    obtain ⟨-, _, c, -, -, -, -, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, -, hx_idx, hblk_ix⟩ := L1.repConstantInfo_rPrj_inv hinfo
    subst hx_idx
    obtain ⟨-, hv898, hm907⟩ :=
      Lib.u64_to_field_spec (L1.Deserialize.repU64_u64Value _ p.idx) ev917
    subst hv898 hm907
    obtain ⟨b_blk, -, hb_rep⟩ := L1.repIxonAddressRef_to_core_ing hblk_ix
    obtain ⟨_, _, rc, -, -, _, _, _, _, _, _, _, _, hld'⟩ := Claim.get_ci_rprj_head hb_rep ev896
    exact is_unsafe_ci_of_bool_field (b := rc.isUnsafe) ev_u
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, _, _, _,
        Except.ok.inj (hld.symm.trans hld')⟩))))
  | .Recr (m978 := m) (ev14 := ev14) (he981 := he) (hm980 := hm) (ev987 := conv) .. =>
    obtain ⟨-, _, c, -, -, -, -, -, -, -, -, -, -, cRep⟩ :=
      L1.load_verified_constant_decode_bounded hab ev14
    obtain ⟨infoVal, _, _, _, _, hc_eq, hinfo, -, -, -, -⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨rc, -, _, _, hrv, -⟩ := L1.repConstantInfo_recr_inv hinfo
    match Obs.«Convert::convert_recursor».obs conv with
    | .run (hv15 := hx) (he237 := hcv) .. =>
      have hu := hrv.symm.trans hx
      injection hu with _ _ hargs
      injection hargs with _ hargs
      injection hargs with hflag _
      rw [he, hm, Claim.loadValue_snoc_self m _, hcv, ← hflag] at hld
      exact is_unsafe_ci_of_bool_field (b := rc.isUnsafe) ev_u
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, _, _, _, _,
          (Except.ok.inj hld).symm⟩))))

private theorem mul_bool_spec {x y r : SourceValue F}
    (hx : x = .field 0 ∨ x = .field 1) (hy : y = .field 0 ∨ y = .field 1)
    (op : evalBinOp .mul x y = .ok r) :
    (r = .field 0 ∨ r = .field 1) ∧ (r = .field 1 → x = .field 1 ∧ y = .field 1) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp only [evalBinOp, Except.ok.injEq] at op <;> subst op
  · exact ⟨Or.inl (by simp), fun h => absurd (Value.field.inj h) (by decide)⟩
  · exact ⟨Or.inl (by simp), fun h => absurd (Value.field.inj h) (by decide)⟩
  · exact ⟨Or.inl (by simp), fun h => absurd (Value.field.inj h) (by decide)⟩
  · exact ⟨Or.inr (by simp), fun _ => ⟨rfl, rfl⟩⟩

private theorem sub_one_bool_spec {y r : SourceValue F}
    (hy : y = .field 0 ∨ y = .field 1)
    (op : evalBinOp .sub (.field 1) y = .ok r) :
    (r = .field 0 ∨ r = .field 1) ∧ (r = .field 1 → y = .field 0) := by
  rcases hy with rfl | rfl <;> simp only [evalBinOp, Except.ok.injEq] at op <;> subst op
  · exact ⟨Or.inr (by simp), fun _ => rfl⟩
  · exact ⟨Or.inl (by simp), fun h => absurd (Value.field.inj h) (by decide)⟩

/-- **`KernelCheck::safe_refs_only` on a raw converted expression**: always returns `0` or `1`,
and when it returns `1`, every `KExprSub`-reachable subexpression also has an observed
`safe_refs_only` call returning `1` among its subcalls. -/
private theorem safe_refs_only_raw_sub {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ} {sharing : List Ixon.Expr}
    {blobs : List (_root_.Address × ByteArray)} {h₀ : Heap F} {bound : Nat}
    {e : Ixon.Expr} {kp : SourceValue F}
    (raw : L1.RawConvExpr refs recurAddrs univs sharing blobs h₀ bound e kp) :
    ∀ {h h' : Heap F} {r : SourceValue F} {cs : List (Call F)},
      Heap.Extends h₀ h →
      ObsFn Obs.W "KernelCheck::safe_refs_only" [kp] h r h' cs →
      (r = .field 0 ∨ r = .field 1) ∧
      (r = .field 1 → ∀ q, KExprSub h kp q →
        ∃ h1 h2 cs1, Heap.Extends h h1 ∧ (∀ cl ∈ cs1, cl ∈ cs) ∧
          ObsFn Obs.W "KernelCheck::safe_refs_only" [q] h1 (.field 1) h2 cs1) := by
  induction raw with
  | var _ cell =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .BVar (he26 := hr) .. =>
      subst hr
      refine ⟨Or.inr rfl, fun _ q hsub => ?_⟩
      cases hsub with
      | refl _ => exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld _ | forallBody ld _ | appFn ld _ =>
        exact (Core.load_cell_ne cell_h ld (by decide)).elim
    | .Srt (ld12 := ld) .. | .Const (ld12 := ld) .. | .App (ld12 := ld) ..
    | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) .. | .Let (ld12 := ld) ..
    | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | sort _ _ _ cell =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .Srt (he42 := hr) .. =>
      subst hr
      refine ⟨Or.inr rfl, fun _ q hsub => ?_⟩
      cases hsub with
      | refl _ => exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld _ | forallBody ld _ | appFn ld _ =>
        exact (Core.load_cell_ne cell_h ld (by decide)).elim
    | .BVar (ld12 := ld) .. | .Const (ld12 := ld) .. | .App (ld12 := ld) ..
    | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) .. | .Let (ld12 := ld) ..
    | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | str _ _ _ _ _ cell | nat _ _ _ _ _ _ _ cell =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .Lit (he379 := hr) .. =>
      subst hr
      refine ⟨Or.inr rfl, fun _ q hsub => ?_⟩
      cases hsub with
      | refl _ => exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld _ | forallBody ld _ | appFn ld _ =>
        exact (Core.load_cell_ne cell_h ld (by decide)).elim
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App (ld12 := ld) .. | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) ..
    | .Let (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | ref _ _ _ ra _ _ cell | recur _ _ _ ra _ _ cell =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .Const (ld12 := ld) (ev79 := ev_ci) (ld73 := hld) (ev101 := ev_u) (op95 := op) .. =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      have hy := get_ci_is_unsafe_bool (Bytes.repAddressRef_heapMono₂ Core.addrTy ext ra)
        ev_ci hld ev_u
      obtain ⟨hrb, -⟩ := sub_one_bool_spec hy op
      refine ⟨hrb, fun hr1 q hsub => ?_⟩
      cases hsub with
      | refl _ =>
        subst hr1
        exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld' _ | forallBody ld' _ | appFn ld' _ =>
        exact (Core.load_cell_ne cell_h ld' (by decide)).elim
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .App (ld12 := ld) ..
    | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) .. | .Let (ld12 := ld) ..
    | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | prj _ _ _ _ ra _ cell ih =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .Proj (ld12 := ld) (ev421 := ev_ci) (ld415 := hld) (ev451 := ev_u) (op445 := op1)
        (ev465 := ev_e1) (op437 := op2) .. =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, -, rfl⟩ := hxs
      have hy := get_ci_is_unsafe_bool (Bytes.repAddressRef_heapMono₂ Core.addrTy ext ra)
        ev_ci hld ev_u
      obtain ⟨hx_b, -⟩ := sub_one_bool_spec hy op1
      obtain ⟨he1_b, -⟩ := ih (ext.trans (ev_ci.heap_extends.trans ev_u.heap_extends)) ev_e1
      obtain ⟨hrb, -⟩ := mul_bool_spec hx_b he1_b op2
      refine ⟨hrb, fun hr1 q hsub => ?_⟩
      cases hsub with
      | refl _ =>
        subst hr1
        exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld' _ | forallBody ld' _ | appFn ld' _ =>
        exact (Core.load_cell_ne cell_h ld' (by decide)).elim
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App (ld12 := ld) .. | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) ..
    | .Let (ld12 := ld) .. | .Lit (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | lam _ _ _ cell iht ihb =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .Lam (ld12 := ld) (ev201 := ev_t) (ev215 := ev_b) (op195 := op) .. =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      obtain ⟨ht_b, -⟩ := iht ext ev_t
      obtain ⟨hb_b, -⟩ := ihb (ext.trans ev_t.heap_extends) ev_b
      obtain ⟨hrb, -⟩ := mul_bool_spec ht_b hb_b op
      refine ⟨hrb, fun hr1 q hsub => ?_⟩
      cases hsub with
      | refl _ =>
        subst hr1
        exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld' _ | forallBody ld' _ | appFn ld' _ =>
        exact (Core.load_cell_ne cell_h ld' (by decide)).elim
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App (ld12 := ld) .. | .Forall (ld12 := ld) .. | .Let (ld12 := ld) ..
    | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | letE _ _ _ cell iht ihv ihb =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .Let (ld12 := ld) (ev328 := ev_t) (ev342 := ev_v) (op322 := op1)
        (ev356 := ev_b) (op314 := op2) .. =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      obtain ⟨ht_b, -⟩ := iht ext ev_t
      obtain ⟨hv_b, -⟩ := ihv (ext.trans ev_t.heap_extends) ev_v
      obtain ⟨htv_b, -⟩ := mul_bool_spec ht_b hv_b op1
      obtain ⟨hb_b, -⟩ := ihb (ext.trans (ev_t.heap_extends.trans ev_v.heap_extends)) ev_b
      obtain ⟨hrb, -⟩ := mul_bool_spec htv_b hb_b op2
      refine ⟨hrb, fun hr1 q hsub => ?_⟩
      cases hsub with
      | refl _ =>
        subst hr1
        exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld' _ | forallBody ld' _ | appFn ld' _ =>
        exact (Core.load_cell_ne cell_h ld' (by decide)).elim
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App (ld12 := ld) .. | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) ..
    | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | app _ _ cell ihf iha =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .App (cs139 := cs139) (ld12 := ld) (ev141 := ev_f) (ev155 := ev_a) (op135 := op)
        (hc164 := hc) .. =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      obtain ⟨hf_b, hf_sub⟩ := ihf ext ev_f
      obtain ⟨ha_b, -⟩ := iha (ext.trans ev_f.heap_extends) ev_a
      obtain ⟨hrb, hr_imp⟩ := mul_bool_spec hf_b ha_b op
      refine ⟨hrb, fun hr1 q hsub => ?_⟩
      cases hsub with
      | refl _ =>
        subst hr1
        exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | appFn ld' hsub_f =>
        have hxs' := (Core.load_cell cell_h ld').2
        simp only [List.cons.injEq, and_true] at hxs'
        obtain ⟨rfl, rfl⟩ := hxs'
        obtain ⟨h1, h2, cs1, ext1, sub1, ev1⟩ := hf_sub (hr_imp hr1).1 q hsub_f
        exact ⟨h1, h2, cs1, ext1, fun cl hcl => by rw [hc]; simp [sub1 cl hcl], ev1⟩
      | forallDom ld' _ | forallBody ld' _ =>
        exact (Core.load_cell_ne cell_h ld' (by decide)).elim
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) .. | .Let (ld12 := ld) ..
    | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | all _ _ _ cell iht ihb =>
    intro h h' r cs ext ev
    have cell_h := ext.getElem?_eq cell
    match Obs.«KernelCheck::safe_refs_only».obs ev with
    | .Forall (cs259 := cs259) (cs273 := cs273) (ld12 := ld) (ev261 := ev_t) (ev275 := ev_b)
        (op255 := op) (hc284 := hc) .. =>
      have hxs := (Core.load_cell cell_h ld).2
      simp only [List.cons.injEq, and_true] at hxs
      obtain ⟨rfl, rfl, rfl⟩ := hxs
      obtain ⟨ht_b, ht_sub⟩ := iht ext ev_t
      obtain ⟨hb_b, hb_sub⟩ := ihb (ext.trans ev_t.heap_extends) ev_b
      obtain ⟨hrb, hr_imp⟩ := mul_bool_spec ht_b hb_b op
      refine ⟨hrb, fun hr1 q hsub => ?_⟩
      cases hsub with
      | refl _ =>
        subst hr1
        exact ⟨h, h', cs, Heap.Extends.refl h, fun _ hcl => hcl, ev⟩
      | forallDom ld' hsub_t =>
        have hxs' := (Core.load_cell cell_h ld').2
        simp only [List.cons.injEq, and_true] at hxs'
        obtain ⟨rfl, rfl, rfl⟩ := hxs'
        obtain ⟨h1, h2, cs1, ext1, sub1, ev1⟩ := ht_sub (hr_imp hr1).1 q hsub_t
        exact ⟨h1, h2, cs1, ext1, fun cl hcl => by rw [hc]; simp [sub1 cl hcl], ev1⟩
      | forallBody ld' hsub_b =>
        have hxs' := (Core.load_cell cell_h ld').2
        simp only [List.cons.injEq, and_true] at hxs'
        obtain ⟨rfl, rfl, rfl⟩ := hxs'
        obtain ⟨h1, h2, cs1, ext1, sub1, ev1⟩ :=
          hb_sub (hr_imp hr1).2 q (hsub_b.mono ev_t.heap_extends)
        exact ⟨h1, h2, cs1, ev_t.heap_extends.trans ext1,
          fun cl hcl => by rw [hc]; simp [sub1 cl hcl], ev1⟩
      | appFn ld' _ =>
        exact (Core.load_cell_ne cell_h ld' (by decide)).elim
    | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .Const (ld12 := ld) ..
    | .App (ld12 := ld) .. | .Lam (ld12 := ld) .. | .Let (ld12 := ld) ..
    | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
      exact (Core.load_cell_ne cell_h ld (by decide)).elim
  | share _ _ _ ih =>
    intro h h' r cs ext ev
    exact ih ext ev

private theorem safe_refs_only_const_ind0_safe {calls cs : List (Call F)} {E₀ : Ixon.Env}
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind₀ : Ixon.Inductive}
    {b_blk b₀ : Bytes.Address} {q x_c w : SourceValue F} {h h' : Heap F}
    (hS : LoadedReads.RunStore calls E₀)
    (hBrec : recordOf E₀ B = some cb) (hBmuts : cb.info = .muts ms)
    (hind0 : ms[0]? = some (.indc ind₀))
    (hb_blk : Core.ixAddr b_blk = B)
    (hb0_eq : Core.ixAddr b₀ = Core.iprjAddr B 0)
    (hhash0 : Hashed calls (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind₀), #[], #[], #[], #[]⟩))
    (hldq : loadValue h q = .ok (.construct "KernelTypes::KExprNode" "Const" [x_c, w]))
    (hb0_rep : Bytes.RepAddressRef Core.addrTy h b₀ x_c)
    (ev : ObsFn Obs.W "KernelCheck::safe_refs_only" [q] h (.field 1) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ind₀.isUnsafe = false := by
  match Obs.«KernelCheck::safe_refs_only».obs ev with
  | .Const (cs77 := cs77) (ld12 := ld) (ev79 := ev_ci) (ld73 := hld) (ev101 := ev_u)
      (op95 := op) (hc110 := hc) .. =>
    have hq_eq := Except.ok.inj (hldq.symm.trans ld)
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hq_eq
    obtain ⟨_, _, rfl, rfl⟩ := hq_eq
    have hsub77 : ∀ cl ∈ cs77, cl ∈ calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨raw, cp, -, hh, hba, hx, -, hhead⟩ := Claim.get_ci_head hb0_rep ev_ci
    have hproj_eq : _root_.Address.blake3Pure (Ixon.serConstant
        ⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind₀), #[], #[], #[], #[]⟩) =
        Core.iprjAddr B 0 := rfl
    have hraw : raw = Ixon.serConstant
        ⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind₀), #[], #[], #[], #[]⟩ :=
      hS.hashed_inj (Core.hashed_mono hsub77 hh) hhash0 (hba.trans (hb0_eq.trans hproj_eq.symm))
    have hwf : (⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind₀), #[], #[], #[], #[]⟩ :
        Ixon.Constant).wireWF := by
      have hB' : Core.ixAddr b_blk = B := hb_blk
      rw [← hB']
      exact L1.projConstant_wireWF_iPrj (0 : Nat).toUInt64 b_blk
    rw [hraw, Ixon.Verify.deConstantExact_serConstant _ hwf] at hx
    injection hx with hcp
    subst hcp
    obtain ⟨cb', ms', ind', hbl, hmem', -, _, _, _, _, _, _, hldv, -, -⟩ :=
      hhead.iPrj (0 : Nat).toUInt64 B rfl
    have hcb_eq : cb' = cb := ((hbl.mono hsub77).record hS hBrec).1
    have hms_eq : ms' = ms := by
      have e1 : cb.info = .muts ms' := by rw [← hcb_eq]; exact hbl.info
      exact Ixon.ConstantInfo.muts.inj (e1.symm.trans hBmuts)
    subst ms'
    have hm0L : ms.toList[0]? = some (.indc ind₀) := by rw [Array.getElem?_toList]; exact hind0
    have hind_eq : ind' = ind₀ := by
      change ms.toList[0]? = some (.indc ind') at hmem'
      exact Ixon.MutConst.indc.inj (Option.some.inj (hmem'.symm.trans hm0L))
    subst hind_eq
    have hv63 : _ = .construct "KernelTypes::KConstantInfo" "Induct" _ :=
      Except.ok.inj (hld.symm.trans hldv)
    rw [hv63] at ev_u
    have hy0 : _ = L1.repBoolField ind₀.isUnsafe := by
      match Obs.«KernelCheck::is_unsafe_ci».obs ev_u with
      | .Induct (hv195 := hv) (he245 := hr) .. =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv
        rw [hr, ← hv.2.2.2.2.2.2.2.1]
      | .Axiom (hv15 := hv) .. | .Defn_Safe (hv43 := hv) .. | .Defn_other (hv43 := hv) ..
      | .Thm (hv105 := hv) .. | .Opaque (hv133 := hv) .. | .Quot (hv167 := hv) ..
      | .Ctor (hv253 := hv) .. | .Rec (hv311 := hv) .. =>
        exact absurd (Value.construct.inj hv).2.1 (by decide)
    rw [hy0] at op
    have hzero := (sub_one_bool_spec (repBoolField_dichot ind₀.isUnsafe) op).2 rfl
    exact Assembly.repBoolField_zero_false hzero
  | .BVar (ld12 := ld) .. | .Srt (ld12 := ld) .. | .App (ld12 := ld) ..
  | .Lam (ld12 := ld) .. | .Forall (ld12 := ld) .. | .Let (ld12 := ld) ..
  | .Lit (ld12 := ld) .. | .Proj (ld12 := ld) .. =>
    exact absurd (Value.construct.inj (Except.ok.inj (hldq.symm.trans ld))).2.1 (by decide)

/-! ## `assert_no_role` and `build_recur_addrs` hashing -/

/-- **`KernelModeled::assert_no_role`**: no address in the checked list is bound to any role. -/
theorem assert_no_role_spec {t : Ix.Kernel.RoleTable} {bAddr : _root_.Address} {lim : Option Nat} :
    ∀ (as : List Bytes.Address) {x_rc x_xs r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Claim.RCLimRep t bAddr lim h x_rc →
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h as x_xs →
      ObsFn Obs.W "KernelModeled::assert_no_role" [x_rc, x_xs] h r h' cs →
      h' = h ∧ ∀ a ∈ as, ∀ ro, t.addressOf? ro ≠ some (Core.ixAddr a)
  | [], _, _, _, _, _, _, _, has, ev => by
    match Obs.«KernelModeled::assert_no_role».obs ev with
    | .Nil (he_gcukvwpy := hh) .. => exact ⟨hh, fun _ hm => nomatch hm⟩
    | .Cons (ld_bolbylmd := ld) .. =>
      obtain ⟨_, _, he, -, -⟩ := Lib.rep_cons_of_load has ld
      cases he
  | a :: rest, _, _, _, _, _, _, hrc, has, ev => by
    match Obs.«KernelModeled::assert_no_role».obs ev with
    | .Nil (ld_bolbylmd := ld) .. => cases Lib.rep_nil_of_load has ld
    | .Cons (ld_bolbylmd := ld) (ev_bpdlygwe := ev_ri) (heq_qeodfzug := h0)
        (ev_ilgjjknx := ev_rest) .. =>
      obtain ⟨_, _, he, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load has ld
      injection he with ha_eq hrest_eq
      subst ha_eq hrest_eq
      obtain ⟨rfl, hcases⟩ := Claim.role_index_of_lim_spec hrc ⟨a, ha_rep, rfl⟩ ev_ri
      have hno : ∀ ro, t.addressOf? ro ≠ some (Core.ixAddr a) := by
        rcases hcases with ⟨-, hno⟩ | ⟨ro, hro, -⟩
        · exact hno
        · exact absurd (Value.field.inj (h0.symm.trans hro)).symm
            (RolesAux.roleNum_add_one_ne_zero ro)
      obtain ⟨hh, htl⟩ := assert_no_role_spec rest hrc hrest_rep ev_rest
      refine ⟨hh, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hno
      · exact htl x hmem

private theorem mutShape_mono_local : HeapMono₂ Core.Specs.Callees.MutShape :=
  fun _ _ _ _ _ rep => rep

private theorem build_recur_addrs_walk_hashed {ms : List Ixon.MutConst} {b : Bytes.Address} :
    ∀ (cur : List Ixon.MutConst) {k : Nat} {x_all x_blk x_cur r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      k ≤ 72057594037927936 →
      Core.Specs.Callees.MembersRep h ms x_all →
      Bytes.RepAddressRef Core.addrTy h b x_blk →
      Core.Specs.Callees.MembersRep h cur x_cur →
      (∀ j m', cur[j]? = some m' → ms[k + j]? = some m') →
      ObsFn Obs.W "Ingress::build_recur_addrs_walk" [x_all, x_blk, x_cur, .field (k : F)]
        h r h' cs →
      ∀ j m', cur[j]? = some m' → Hashed cs (Ixon.serConstant
        ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) (k + j) m', #[], #[], #[], #[]⟩)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by intro _ _ hj; simp at hj
  | m :: rest, k, x_all, x_blk, x_cur, r, h, h', cs, hk, hms, hb, hcur, hsuf, ev => by
    rcases Obs.«Ingress::build_recur_addrs_walk».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨w36, x_rest, v55, v56, m58, cs66, m94, cs102, v108,
        ld12, he51, hm50, ev68, op143, ev104, hc145⟩
    · cases Lib.rep_nil_of_load hcur ld12
    · obtain ⟨m', rest', he, _, hrest⟩ := Lib.rep_cons_of_load hcur ld12
      injection he with hm_eq hrest_eq
      subst m' rest'
      obtain ⟨ext1, -, -, mc, -, hget_mc, -, -, hhash⟩ :=
        L1.projection_addr_hashed_spec hms hb ev68
      rw [val_cast_le_u56 hk] at hget_mc hhash
      have hmc_eq : mc = m := by
        have h0 := hsuf 0 m rfl
        rw [Nat.add_zero, hget_mc] at h0
        exact Option.some.inj h0
      subst mc
      simp only [evalBinOp, Except.ok.injEq] at op143
      have hv108 : v108 = .field (((k + 1 : Nat) : F)) := by
        rw [← op143]; push_cast; rfl
      rw [hv108] at ev104
      have htl := build_recur_addrs_walk_hashed rest (k := k + 1) (by omega)
        (hms.mono mutShape_mono_local ext1)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy ext1 hb)
        (hrest.mono mutShape_mono_local ext1)
        (fun j m' hj => by
          have hstep := hsuf (j + 1) m' hj
          have hadd : k + 1 + j = k + (j + 1) := by omega
          rwa [hadd])
        ev104
      intro j m' hj
      cases j with
      | zero =>
        obtain rfl : m = m' := by simpa using hj
        exact Core.hashed_mono (fun cl hcl => by rw [hc145]; simp [hcl]) hhash
      | succ j =>
        have h1 := htl j m' (by simpa using hj)
        rw [show k + 1 + j = k + (j + 1) by omega] at h1
        exact Core.hashed_mono (fun cl hcl => by rw [hc145]; simp [hcl]) h1

private theorem build_recur_addrs_hashed {ms : List Ixon.MutConst} {b : Bytes.Address}
    {x_members x_block r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hms : Core.Specs.Callees.MembersRep h ms x_members)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block)
    (ev : ObsFn Obs.W "Ingress::build_recur_addrs" [x_members, x_block] h r h' cs) :
    ∀ i m, ms[i]? = some m → Hashed cs (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo (Core.ixAddr b) i m, #[], #[], #[], #[]⟩) := by
  obtain ⟨cs4, ev6, hc38⟩ := Obs.«Ingress::build_recur_addrs».obs ev
  have ev6' : ObsFn Obs.W "Ingress::build_recur_addrs_walk"
      [x_members, x_block, x_members, .field ((0 : Nat) : F)] h r h' cs4 := by
    simpa using ev6
  intro i m hm
  have h1 := build_recur_addrs_walk_hashed ms (k := 0) (Nat.zero_le _) hms hb hms
    (fun j m' hj => by simpa using hj) ev6' i m hm
  rw [Nat.zero_add] at h1
  exact Core.hashed_mono (fun cl hcl => by rw [hc38]; simp [hcl]) h1

/-! ## Extracting `check_carriers` and `assert_safety` from `check_recs` -/

private theorem check_recs_member_checks :
    ∀ (as : List Bytes.Address) {x_rc x_ta x_recs x_models x_src x_dst x_aset x_s x_n x_k x_np
      x_uo x_bnl x_fam x_form r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList Core.addrListEnum (Bytes.RepAddressRef Core.addrTy) h as x_recs →
      ObsFn Obs.W "KernelModeled::check_recs"
        [x_rc, x_ta, x_recs, x_models, x_src, x_dst, x_aset, x_s, x_n, x_k, x_np,
         x_uo, x_bnl, x_fam, x_form] h r h' cs →
      ∀ a ∈ as,
        ∃ (x_r p x_nl x_ty x_rnp x_ni x_nmot x_nmin x_rules x_kf x_runs w107 w108
           v472 v639 : SourceValue F)
          (h1 m67 m391 m473 m596 m640 : Heap F) (cs80 cs483 cs650 : List (Call F)),
          Heap.Extends h h1 ∧
          Bytes.RepAddressRef Core.addrTy h1 a x_r ∧
          ObsFn Obs.W "Ingress::get_ci" [x_r] h1 p m67 cs80 ∧
          loadValue m67 p = .ok (.construct "KernelTypes::KConstantInfo" "Rec"
            [x_nl, x_ty, x_rnp, x_ni, x_nmot, x_nmin, x_rules, x_kf, x_runs, w107, w108]) ∧
          Heap.Extends m67 m391 ∧
          ObsFn Obs.W "KernelModeled::check_carriers" [x_ty, x_rnp, x_ta] m391 v472 m473 cs483 ∧
          Heap.Extends m473 m596 ∧
          ObsFn Obs.W "KernelCheck::assert_safety" [.field 0, x_ty] m596 v639 m640 cs650 ∧
          (∀ cl ∈ cs80, cl ∈ cs) ∧
          (∀ cl ∈ cs483, cl ∈ cs) ∧
          (∀ cl ∈ cs650, cl ∈ cs)
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by intro _ ha; nomatch ha
  | a :: rest, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, cs, hrep, ev => by
    match Obs.«KernelModeled::check_recs».obs ev with
    | .Nil (ld12 := ld) .. => cases Lib.rep_nil_of_load hrep ld
    | .Cons (x_r := x_r) (x_rest := x_rest) (p74 := p74) (m67 := m67) (cs80 := cs80)
        (x_ty := x_ty) (x_rnp := x_rnp) (m391 := m391) (m473 := m473) (cs483 := cs483)
        (m596 := m596) (m640 := m640) (cs650 := cs650) (cs1014 := cs1014)
        (ld12 := ld12) (ev82 := ev82) (ld76 := ld76)
        (ev298 := ev298) (ev359 := ev359) (ev345 := ev345) (ev403 := ev403)
        (ev485 := ev485) (ev523 := ev523) (ev571 := ev571)
        (hm_odcsfbbr := hm_od) (ev_uprevpxl := ev_up) (ev_svgicqcr := ev_sv)
        (hm_owdmgqhw := hm_ow) (ev_oqkxxxxs := ev_oq) (ev_eejlfykm := ev_ee)
        (ev_uoyvrvop := ev_uo) (ev_akrqpecc := ev_ak) (hm635 := hm635)
        (ev608 := ev608) (ev652 := ev652) (ev681 := ev681) (ev710 := ev710)
        (ev_uoummlhs := ev_uou) (ev_tjosvhyt := ev_tj) (ev850 := ev850) (ev904 := ev904)
        (ev1016 := ev1016) (hc1137 := hcc) .. =>
      obtain ⟨_, _, he, ha_rep, hrest_rep⟩ := Lib.rep_cons_of_load hrep ld12
      injection he with ha_eq hrest_eq
      subst ha_eq hrest_eq
      have ext_67_391 : Heap.Extends m67 m391 :=
        ev298.heap_extends.trans (ev359.heap_extends.trans
          (ev345.heap_extends.trans ev403.heap_extends))
      have ext_473_596 : Heap.Extends m473 m596 :=
        ev523.heap_extends.trans (ev571.heap_extends.trans
          ((by rw [hm_od]; exact Heap.Extends.snoc _ _ : Heap.Extends _ _).trans
          (ev_up.heap_extends.trans (ev_sv.heap_extends.trans
          ((by rw [hm_ow]; exact Heap.Extends.snoc _ _ : Heap.Extends _ _).trans
          (ev_oq.heap_extends.trans (ev_ee.heap_extends.trans
          (ev_uo.heap_extends.trans (ev_ak.heap_extends.trans
          ((by rw [hm635]; exact Heap.Extends.snoc _ _ : Heap.Extends _ _).trans
          ev608.heap_extends))))))))))
      have ext_step : Heap.Extends h _ :=
        ev82.heap_extends.trans (ext_67_391.trans (ev485.heap_extends.trans
          (ext_473_596.trans (ev652.heap_extends.trans (ev681.heap_extends.trans
          (ev710.heap_extends.trans (ev_uou.heap_extends.trans (ev_tj.heap_extends.trans
          (ev850.heap_extends.trans ev904.heap_extends)))))))))
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hmem
      · exact ⟨x_r, p74, _, x_ty, x_rnp, _, _, _, _, _, _, _, _, _, _,
          h, m67, m391, m473, m596, m640, cs80, cs483, cs650,
          Heap.Extends.refl h, ha_rep, ev82, ld76, ext_67_391, ev485, ext_473_596, ev652,
          fun cl hcl => by rw [hcc]; simp [hcl],
          fun cl hcl => by rw [hcc]; simp [hcl],
          fun cl hcl => by rw [hcc]; simp [hcl]⟩
      · obtain ⟨x_r', p', nl', ty', rnp', ni', nmot', nmin', rules', kf', runs', w1', w2',
          v4', v6', h1, m67', m391', m473', m596', m640', cs80', cs483', cs650',
          ext1, hb_rep, ev82', ld76', e1, ev485', e2, ev652', s1, s2, s3⟩ :=
          check_recs_member_checks rest
            (repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ Core.addrTy) ext_step hrest_rep)
            ev1016 b hmem
        exact ⟨x_r', p', nl', ty', rnp', ni', nmot', nmin', rules', kf', runs', w1', w2',
          v4', v6', h1, m67', m391', m473', m596', m640', cs80', cs483', cs650',
          ext_step.trans ext1, hb_rep, ev82', ld76', e1, ev485', e2, ev652',
          fun cl hcl => by rw [hcc]; simp [s1 cl hcl],
          fun cl hcl => by rw [hcc]; simp [s2 cl hcl],
          fun cl hcl => by rw [hcc]; simp [s3 cl hcl]⟩

/-! ## Master carrier & safety extraction from `FamCheck B rb` -/

/-- Structural facts extracted from an observed `KernelModeled::check_family` call on `(B, rb)`. -/
structure FamCheckCarriers (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (B rb : _root_.Address) (cb crb : Ixon.Constant)
    (ms rs : Array Ixon.MutConst) : Prop where
  blockBytes : ∃ b : Bytes.Address, Core.ixAddr b = B
  blockRec : recordOf E₀ B = some cb
  blockMuts : cb.info = .muts ms
  recRec : FamRecRecord E₀ rb crb rs
  ind0 : ∃ ind₀, ms[0]? = some (Ixon.MutConst.indc ind₀)
  hashedIPrj0 : ∀ ind₀, ms[0]? = some (Ixon.MutConst.indc ind₀) →
    Hashed calls (Ixon.serConstant
      ⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind₀), #[], #[], #[], #[]⟩)
  noRole : ∀ k (m : Ixon.MutConst), rs[k]? = some m →
    ∀ ro, t.addressOf? ro ≠ some (memberAddr rb k m)
  carrier : ∀ k (rc : Ixon.Recursor), rs[k]? = some (Ixon.MutConst.recr rc) →
    ∃ n, Binding.FamilyOf.motiveCarrierAt crb rc 0 n = some (Core.iprjAddr B 0)
  ind0Safe : 0 < rs.size → ∀ ind₀, ms[0]? = some (Ixon.MutConst.indc ind₀) → ind₀.isUnsafe = false

private theorem check_family_seg1_extends {e0 e1 e2 r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (sg : Obs.«KernelModeled::check_family».Seg1 e0 e1 e2 h r h' cs) :
    Heap.Extends h h' := by
  cases sg with
  | Nil _ _ ev _ hh _ => rw [hh]; exact ev.heap_extends
  | Node _ _ _ _ _ _ _ ev _ _ hh _ => rw [hh]; exact ev.heap_extends

/-- **Master extraction from `K.FamCheck B rb`**: yields the block record, family record, non-empty
member `0` inductive, projection hash for `iprjAddr B 0`, role-freeness of every recursor member,
motive-0 carrier `iprjAddr B 0` in every recursor member, and `ind₀.isUnsafe = false` whenever the
family record is non-empty. -/
theorem FamRunCtx.check_family_carriers {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {B rb : _root_.Address} (hfc : K.FamCheck B rb) :
    ∃ cb crb ms rs, FamCheckCarriers K.calls K.t K.E₀ B rb cb crb ms rs := by
  obtain ⟨crb, rs, hrb⟩ := FamRunCtx.record_of hW B rb hfc
  obtain ⟨cs, h₀, h₀', rc₀, xb₀, xrb₀, r₀, hrc₀, hB₀, hrb₀, ev_fam, hsub_fam⟩ := hfc
  match Obs.«KernelModeled::check_family».obs ev_fam with
  | .run (m453 := m453) (m501 := m501) (cs511 := cs511) (x_members := x_members)
      (m624 := m624) (m652 := m652) (v673 := v673) (m674 := m674) (cs684 := cs684)
      (m784 := m784) (v839 := v839) (m840 := m840) (cs850 := cs850) (m1293 := m1293)
      (cs1341 := cs1341)
      (sg112 := sg112) (ev126 := ev126) (ev148 := ev148) (ev194 := ev194)
      (ev_yqjbwijz := ev_ord) (ev231 := ev231) (ev266 := ev266) (ev309 := ev309)
      (ev344 := ev344) (ev403 := ev403) (ev435 := ev435) (ev465 := ev465)
      (ev513 := ev513) (ev601 := ev601) (ev634 := ev634) (ev664 := ev664)
      (ev686 := ev686) (ev716 := ev716) (ev759 := ev759) (ev817 := ev817)
      (ev796 := ev796) (ev852 := ev852) (ev_ursqbimm := ev_norole) (ev874 := ev874)
      (ev896 := ev896) (ev960 := ev960) (ev939 := ev939) (ev1011 := ev1011)
      (ev990 := ev990) (ev_edyzsqzv := ev_mv1) (ev_gkddqxhv := ev_cat)
      (ev_ittpynob := ev_mv2) (ev_biaifgpd := ev_mv3) (ev1203 := ev1203)
      (ev_cwwgzxtj := ev_flat) (ev1246 := ev1246) (ev_mitevvsv := ev_lenf)
      (ev_rqpeovbn := ev_z1) (ev_xrhmaojz := ev_z2) (ev_whimdwjd := ev_vg)
      (ev1305 := ev1305) (ev1343 := ev_cr) (hc1474 := hcf) .. =>
    have ext_0_453 : Heap.Extends h₀ m453 :=
      (check_family_seg1_extends sg112).trans (ev126.heap_extends.trans
        (ev148.heap_extends.trans (ev194.heap_extends.trans (ev_ord.heap_extends.trans
        (ev231.heap_extends.trans (ev266.heap_extends.trans (ev309.heap_extends.trans
        (ev344.heap_extends.trans (ev403.heap_extends.trans (ev435.heap_extends.trans
        ev465.heap_extends))))))))))
    have ext_501_624 : Heap.Extends m501 m624 :=
      ev601.heap_extends.trans ev634.heap_extends
    have ext_501_652 : Heap.Extends m501 m652 :=
      ext_501_624.trans ev664.heap_extends
    have ext_674_784 : Heap.Extends m674 m784 :=
      ev716.heap_extends.trans (ev759.heap_extends.trans
        (ev817.heap_extends.trans ev796.heap_extends))
    have ext_840_1293 : Heap.Extends m840 m1293 :=
      ev_norole.heap_extends.trans (ev874.heap_extends.trans (ev896.heap_extends.trans
        (ev960.heap_extends.trans (ev939.heap_extends.trans (ev1011.heap_extends.trans
        (ev990.heap_extends.trans (ev_mv1.heap_extends.trans (ev_cat.heap_extends.trans
        (ev_mv2.heap_extends.trans (ev_mv3.heap_extends.trans (ev1203.heap_extends.trans
        (ev_flat.heap_extends.trans (ev1246.heap_extends.trans (ev_lenf.heap_extends.trans
        (ev_z1.heap_extends.trans (ev_z2.heap_extends.trans (ev_vg.heap_extends.trans
        ev1305.heap_extends)))))))))))))))))
    have ext_674_1293 : Heap.Extends m674 m1293 :=
      ext_674_784.trans (ev852.heap_extends.trans ext_840_1293)
    have hsub511 : ∀ cl ∈ cs511, cl ∈ K.calls :=
      fun cl hcl => hsub_fam cl (by rw [hcf]; simp [hcl])
    have hsub684 : ∀ cl ∈ cs684, cl ∈ K.calls :=
      fun cl hcl => hsub_fam cl (by rw [hcf]; simp [hcl])
    have hsub850 : ∀ cl ∈ cs850, cl ∈ K.calls :=
      fun cl hcl => hsub_fam cl (by rw [hcf]; simp [hcl])
    have hsub_cr : ∀ cl ∈ cs1341, cl ∈ K.calls :=
      fun cl hcl => hsub_fam cl (by rw [hcf]; simp [hcl])
    obtain ⟨b_blk, hb_blk_rep, hb_blk_ix⟩ := hB₀
    obtain ⟨b_rb, hb_rb_rep, hb_rb_ix⟩ := hrb₀
    -- Block load at `ev513`
    obtain ⟨cb, ms, hbl, hms_rep⟩ :=
      Claim.load_block_head (Bytes.repAddressRef_heapMono₂ Core.addrTy ext_0_453 hb_blk_rep) ev513
    obtain ⟨hBrec_blk, hBmuts⟩ := (hbl.mono hsub511).stored hW.hashedStored
    have hBrec : recordOf K.E₀ B = some cb := hb_blk_ix ▸ hBrec_blk
    -- Member 0 is an inductive (`block_nparams`)
    have hind0 : ∃ ind₀, ms[0]? = some (.indc ind₀) := by
      have hms624 := repList_heapMono₂ _ (fun _ _ _ _ ext r => L1.RepMutConst.mono ext r)
        ext_501_624 hms_rep
      match Obs.«KernelModeled::block_nparams».obs ev664 with
      | .run (ld12 := ld12) .. =>
        obtain ⟨m0, rest, hms_cons, hm0_rep, -⟩ := Lib.rep_cons_of_load hms624 ld12
        cases m0 with
        | indc ind₀ =>
          refine ⟨ind₀, ?_⟩
          rw [← Array.getElem?_toList, hms_cons]
          rfl
        | defn _ => obtain ⟨dv, hdv, -⟩ := hm0_rep; simp at hdv
        | recr _ => obtain ⟨rv, hrv, -⟩ := hm0_rep; simp at hrv
    -- Type address list (`build_recur_addrs`) and hash of `iprjAddr B 0`
    have hmems652 : Core.Specs.Callees.MembersRep m652 ms.toList x_members :=
      Route.membersRep_of_repMutConstList
        (repList_heapMono₂ _ (fun _ _ _ _ ext r => L1.RepMutConst.mono ext r) ext_501_652 hms_rep)
    have hb_blk652 : Bytes.RepAddressRef Core.addrTy m652 b_blk xb₀ :=
      Bytes.repAddressRef_heapMono₂ Core.addrTy
        (ext_0_453.trans (ev513.heap_extends.trans ext_501_652)) hb_blk_rep
    obtain ⟨-, as_ty, has_ty, hmap_ty⟩ := L1.build_recur_addrs_spec hmems652 hb_blk652 ev686
    have hhash_ty := build_recur_addrs_hashed hmems652 hb_blk652 ev686
    have hhashIPrj0 : ∀ ind₀, ms[0]? = some (.indc ind₀) →
        Hashed K.calls (Ixon.serConstant
          ⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind₀), #[], #[], #[], #[]⟩) := by
      intro ind₀ hm0
      have hm0L : ms.toList[0]? = some (.indc ind₀) := by rw [Array.getElem?_toList]; exact hm0
      have hh := Core.hashed_mono hsub684 (hhash_ty 0 (.indc ind₀) hm0L)
      rwa [hb_blk_ix] at hh
    -- Extract the head `b_i0` of `as_ty` with `Core.ixAddr b_i0 = Core.iprjAddr B 0`
    obtain ⟨ind₀, hind₀⟩ := hind0
    have hty_head : ∃ b_i0 bs_ty, as_ty = b_i0 :: bs_ty ∧ Core.ixAddr b_i0 = Core.iprjAddr B 0 := by
      have hm0L : ms.toList[0]? = some (.indc ind₀) := by rw [Array.getElem?_toList]; exact hind₀
      have h0 : (as_ty.map Core.ixAddr)[0]? = some (Core.iprjAddr B 0) := by
        rw [hmap_ty, List.getElem?_mapIdx, hm0L, hb_blk_ix]
        rfl
      cases as_ty with
      | nil => simp at h0
      | cons b_i0 bs_ty =>
        simp only [List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at h0
        exact ⟨b_i0, bs_ty, rfl, h0⟩
    obtain ⟨b_i0, bs_ty, rfl, hb_i0_eq⟩ := hty_head
    -- Family recursors list (`family_recs`)
    have ext_0_784 : Heap.Extends h₀ m784 :=
      ext_0_453.trans (ev513.heap_extends.trans (ext_501_652.trans
        (ev686.heap_extends.trans ext_674_784)))
    have hb_rb784 : Bytes.RepAddressRef Core.addrTy m784 b_rb xrb₀ :=
      Bytes.repAddressRef_heapMono₂ Core.addrTy ext_0_784 hb_rb_rep
    obtain ⟨as_rc, has_rc, hmap_rc⟩ :=
      FamilyAlias.family_recs_list hW.hashedStored hb_rb784 ev852 hsub850 (hb_rb_ix ▸ hrb)
    -- `assert_no_role` on `as_rc`
    have hno_as_rc : ∀ a ∈ as_rc, ∀ ro, K.t.addressOf? ro ≠ some (Core.ixAddr a) :=
      (assert_no_role_spec as_rc
        (hrc₀.mono (ext_0_784.trans ev852.heap_extends)) has_rc ev_norole).2
    have hnoRole : ∀ k (m : Ixon.MutConst), rs[k]? = some m →
        ∀ ro, K.t.addressOf? ro ≠ some (memberAddr rb k m) := by
      intro k m hk
      have hkL : rs.toList[k]? = some m := by rw [Array.getElem?_toList]; exact hk
      have h1 : (as_rc.map Core.ixAddr)[k]? =
          some (Core.projAddr (Core.Specs.Callees.memberProjInfo rb k m)) := by
        rw [hmap_rc, List.getElem?_mapIdx, hkL, hb_rb_ix]
        rfl
      rw [List.getElem?_map] at h1
      obtain ⟨a_k, ha_k, ha_k_eq⟩ := Option.map_eq_some_iff.mp h1
      rw [LoadedReads.memberAddr_eq_projAddr, ← ha_k_eq]
      exact hno_as_rc a_k (List.mem_of_getElem? ha_k)
    -- `check_recs` on every member `k < rs.size`
    have has_rc1293 := repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ Core.addrTy)
      ext_840_1293 has_rc
    have has_ty1293 := repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ Core.addrTy)
      ext_674_1293 has_ty
    have hcr_all := check_recs_member_checks as_rc has_rc1293 ev_cr
    -- Helper: for any `k` with `rs[k]? = some (.recr rc)`, extract carrier AND `ind₀.isUnsafe = false`
    have hmem_both : ∀ k (rc : Ixon.Recursor), rs[k]? = some (.recr rc) →
        (∃ n, Binding.FamilyOf.motiveCarrierAt crb rc 0 n = some (Core.iprjAddr B 0)) ∧
        ind₀.isUnsafe = false := by
      intro k rc hk
      have hkL : rs.toList[k]? = some (.recr rc) := by rw [Array.getElem?_toList]; exact hk
      have h1 : (as_rc.map Core.ixAddr)[k]? = some (memberAddr rb k (.recr rc)) := by
        rw [hmap_rc, List.getElem?_mapIdx, hkL, hb_rb_ix, LoadedReads.memberAddr_eq_projAddr]
        rfl
      rw [List.getElem?_map] at h1
      obtain ⟨a_k, ha_k, ha_k_eq⟩ := Option.map_eq_some_iff.mp h1
      obtain ⟨x_r, p, x_nl, x_ty, x_rnp, x_ni, x_nmot, x_nmin, x_rules, x_kf, x_runs, w107, w108,
        v472, v639, h1, m67, m391, m473, m596, m640, cs80, cs483, cs650,
        ext_h1, ha_k_rep, ev82, ld76, ext_67_391, ev485, ext_473_596, ev652,
        hsub80, -, hsub650⟩ := hcr_all a_k (List.mem_of_getElem? ha_k)
      -- `k < 72057594037927936` from `a_k`'s `rPrj` load via `Claim.get_ci_head`
      have hk_lt : k < 72057594037927936 := by
        have hlt_rs : k < rs.size := (Array.getElem?_eq_some_iff.mp hk).1
        obtain ⟨raw_rb, crb', hsz_rb, hh_rb, hba_rb, hde_rb, -, -⟩ :=
          Claim.get_ci_head ha_k_rep ev82
        -- Instead use `rb`'s own resource bound from `family_recs` via `ev852`
        have hsub80' : ∀ cl ∈ cs80, cl ∈ K.calls := fun cl hcl => hsub_cr cl (hsub80 cl hcl)
        have hrec_ak : recordOf K.E₀ (Core.ixAddr a_k) = some (memberProjection rb k (.recr rc)) := by
          rw [ha_k_eq]; exact hrb.members k (.recr rc) hk
        have hcp_eq : crb' = memberProjection rb k (.recr rc) :=
          hW.runStore.record_eq ((hW.runStore.recordOf_eq_recordAt _).symm.trans hrec_ak)
            (Core.hashed_mono hsub80' hh_rb) hba_rb hde_rb
        subst crb'
        -- Obtain `rb`'s resource bound from `Obs.«KernelModeled::family_recs».obs ev852`
        match Obs.«KernelModeled::family_recs».obs ev852 with
        | .Muts (cs12 := cs_fr12) (ev14 := ev_fr14) (hc165 := hfr_c) .. =>
          have hsub_fr12 : ∀ cl ∈ cs_fr12, cl ∈ K.calls :=
            fun cl hcl => hsub850 cl (by rw [hfr_c]; simp [hcl])
          obtain ⟨-, raw_l, crb_l, hsz_l, hh_l, hba_l, hde_l, -, -, -, -, -, -, -⟩ :=
            L1.load_verified_constant_decode_bounded hb_rb784 ev_fr14
          have hcrb_eq : crb_l = crb :=
            hW.runStore.record_eq ((hW.runStore.recordOf_eq_recordAt _).symm.trans (hb_rb_ix ▸ hrb.record))
              (Core.hashed_mono hsub_fr12 hh_l) hba_l hde_l
          subst crb_l
          have hres := Ixon.Verify.ConstantBounds.deConstantExact_resource_bound ⟨raw_l.toArray⟩ crb hde_l
          have hms_le := Claim.muts_size_le hrb.muts
          simp only [ByteArray.size, List.size_toArray] at hres
          omega
        | .Recr (cs12 := cs_fr12) (ev14 := ev_fr14) (hc209 := hfr_c) .. =>
          exfalso
          have hsub_fr12 : ∀ cl ∈ cs_fr12, cl ∈ K.calls :=
            fun cl hcl => hsub850 cl (by rw [hfr_c]; simp [hcl])
          obtain ⟨-, raw_l, crb_l, -, hh_l, hba_l, hde_l, -, -, -, -, -, -, cRep_l⟩ :=
            L1.load_verified_constant_decode_bounded hb_rb784 ev_fr14
          have hcrb_eq : crb_l = crb :=
            hW.runStore.record_eq ((hW.runStore.recordOf_eq_recordAt _).symm.trans (hb_rb_ix ▸ hrb.record))
              (Core.hashed_mono hsub_fr12 hh_l) hba_l hde_l
          subst crb_l
          obtain ⟨infoVal, _, _, _, _, hc_eq, hinfoRep, -, -, -, -⟩ := cRep_l
          have hinfo_eq := (List.cons.inj (Value.construct.inj hc_eq).2.2).1
          rw [hrb.muts] at hinfoRep
          obtain ⟨mv, hmv, -⟩ := hinfoRep
          exact absurd (Value.construct.inj (hinfo_eq.trans hmv)).2.1 (by decide)
      obtain ⟨blobs, hraw⟩ := get_ci_of_rPrj_raw hW.runStore hrb hk hk_lt ha_k_rep ha_k_eq
        ev82 (fun cl hcl => hsub_cr cl (hsub80 cl hcl)) ld76
      obtain ⟨-, hnp, -, -, -, -, tyPtr, _, _, _, _, _, hrec_mk, hraw_ty, -⟩ := hraw
      simp only [Core.kciEnum, Value.construct.injEq, List.cons.injEq, and_true] at hrec_mk
      rcases hrec_mk with ⟨_, _, _, hty_eq, hrnp_eq, _⟩
      subst hty_eq hrnp_eq
      have hraw_391 := hraw_ty.mono ext_67_391 (fun _ hm => hm)
      have hta_391 := repList_heapMono₂ _ (Bytes.repAddressRef_heapMono₂ Core.addrTy)
        (ext_h1.trans (ev82.heap_extends.trans ext_67_391)) has_ty1293
      obtain ⟨hmot, x_head, x_c, w145, hsub_head, hld_head, hb0_473⟩ :=
        check_carriers_raw_head hnp hraw_391 hta_391 ev485
      rw [hb_i0_eq] at hmot
      refine ⟨hmot, ?_⟩
      obtain ⟨cs_sr, ev_sr, hcs650⟩ := Assembly.assert_safety_zero_spec ev652
      have ext_67_596 : Heap.Extends m67 m596 :=
        ext_67_391.trans (ev485.heap_extends.trans ext_473_596)
      obtain ⟨-, hsr_sub⟩ := safe_refs_only_raw_sub hraw_ty ext_67_596 ev_sr
      obtain ⟨h_q1, h_q2, cs_q, ext_q, sub_q, ev_q⟩ :=
        hsr_sub rfl x_head (hsub_head.mono ext_473_596)
      have hsub_q_all : ∀ cl ∈ cs_q, cl ∈ K.calls := fun cl hcl =>
        hsub_cr cl (hsub650 cl (by rw [hcs650]; simp [sub_q cl hcl]))
      exact safe_refs_only_const_ind0_safe hW.runStore hBrec hBmuts hind₀ hb_blk_ix hb_i0_eq
        (hhashIPrj0 ind₀ hind₀)
        (loadValue_mono (ext_473_596.trans ext_q) hld_head)
        (Bytes.repAddressRef_heapMono₂ Core.addrTy (ext_473_596.trans ext_q) hb0_473)
        ev_q hsub_q_all
    refine ⟨cb, crb, ms, rs,
      ⟨⟨b_blk, hb_blk_ix⟩, hBrec, hBmuts, hrb, ⟨ind₀, hind₀⟩, hhashIPrj0, hnoRole,
        fun k rc hk => (hmem_both k rc hk).1, ?_⟩⟩
    intro hpos ind₀' hind₀'
    have hind_eq : ind₀' = ind₀ := Ixon.MutConst.indc.inj (Option.some.inj (hind₀'.symm.trans hind₀))
    subst hind_eq
    have h0mem : rs[0] ∈ rs.toList := by
      have hL : rs.toList[0]? = some rs[0] := by
        rw [Array.getElem?_toList, Array.getElem?_eq_getElem hpos]
      exact List.mem_of_getElem? hL
    obtain ⟨rc₀, hrc₀⟩ := hrb.recrs rs[0] h0mem
    have hget0 : rs[0]? = some (.recr rc₀) := by rw [Array.getElem?_eq_getElem hpos, hrc₀]
    exact (hmem_both 0 rc₀ hget0).2

/-! ## Discharging `BatchGives.inLogic` and `BatchGives.blockOf` -/

/-- **`BatchGives.inLogic`**: the block a twin is a second family record of is in Lean's logic. -/
theorem FamRunCtx.inLogic_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {rb' B : _root_.Address} (htw : K.twin rb' = some B)
    {cb : Ixon.Constant} (hcb : recordOf K.E₀ B = some cb) :
    InLogic cb := by
  have hfacts : K.Top B ∧ RecBlock K.E₀ rb' ∧ K.FamCheck B rb' := by
    rcases K.twin_some htw with ⟨-, hRB, -, -, hFC, hTB, -, -⟩ |
      ⟨⟨-, hRB, -, -⟩, hTB, -, -, -, -, _, _, cs', hfc', -⟩
    · exact ⟨hTB, hRB, hFC⟩
    · exact ⟨hTB, hRB, cs', hfc'⟩
  obtain ⟨hTB, hRB, hFC⟩ := hfacts
  obtain ⟨cb', crb, ms, rs, hcar⟩ := FamRunCtx.check_family_carriers hW hFC
  have hcb_eq : cb' = cb := Option.some.inj (hcar.blockRec.symm.trans hcb)
  subst cb'
  obtain ⟨crb', rs', hrb_rec, hrb_muts, hrb_pos, -⟩ := hRB
  have hcrb_eq : crb' = crb := Option.some.inj (hrb_rec.symm.trans hcar.recRec.record)
  subst crb'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hrb_muts.symm.trans hcar.recRec.muts)
  subst rs'
  obtain ⟨ind₀, hind₀⟩ := hcar.ind0
  have hsafe0 : ind₀.isUnsafe = false := hcar.ind0Safe hrb_pos ind₀ hind₀
  have h0lt : 0 < ms.size := (Array.getElem?_eq_some_iff.mp hind₀).1
  have hchk := Claim.membersChecked_of_block hW.runStore hcb hcar.blockMuts (hW.checked B hTB)
  obtain ⟨x, rr, h₁, h₂, cs₁, hx, evk, hsubk⟩ :=
    Claim.MemberCheckObs.block_kinds hW.runStore (hchk 0 h0lt).obs
  have hmem0 : Ixon.MutConst.indc ind₀ ∈ ms.toList := by
    have hL : ms.toList[0]? = some (.indc ind₀) := by rw [Array.getElem?_toList]; exact hind₀
    exact List.mem_of_getElem? hL
  exact Assembly.block_inLogic_of_member_kinds hW.runStore hx evk hsubk
    ((hW.runStore.recordOf_eq_recordAt _).symm.trans hcb) hcar.blockMuts
    ⟨.indc ind₀, hmem0, Or.inl hsafe0⟩

/-- **`BatchGives.blockOf`**: a family record with a constant address is the family record of
at most one block. -/
theorem FamRunCtx.blockOf_of {K : FamRunCtx} {seeds : List _root_.Address}
    {rank : _root_.Address → Nat}
    (hW : Claim.TopWalkCore K.calls K.bAddr K.t seeds K.E₀ K.lim K.Top rank)
    {B B' rb : _root_.Address} {crb : Ixon.Constant} {x : _root_.Address}
    (h1 : K.FamCheck B rb) (h2 : K.FamCheck B' rb)
    (hrec : recordOf K.E₀ rb = some crb) (hx : ConstAddrOf rb crb x) :
    B = B' := by
  obtain ⟨cb1, crb1, ms1, rs1, hcar1⟩ := FamRunCtx.check_family_carriers hW h1
  obtain ⟨cb2, crb2, ms2, rs2, hcar2⟩ := FamRunCtx.check_family_carriers hW h2
  have hcrb1 : crb1 = crb := Option.some.inj (hcar1.recRec.record.symm.trans hrec)
  have hcrb2 : crb2 = crb := Option.some.inj (hcar2.recRec.record.symm.trans hrec)
  subst crb1 crb2
  have hrs2 : rs2 = rs1 := Ixon.ConstantInfo.muts.inj (hcar2.recRec.muts.symm.trans hcar1.recRec.muts)
  subst rs2
  have hpos : 0 < rs1.size := by
    rcases hx with ⟨hnb, -⟩ | ⟨ms', i, m', hmuts', hget', -⟩
    · exact (hnb rs1 hcar1.recRec.muts).elim
    · have hms_eq : ms' = rs1 := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hcar1.recRec.muts)
      subst hms_eq
      exact Nat.lt_of_le_of_lt (Nat.zero_le i) (Array.getElem?_eq_some_iff.mp hget').1
  have h0mem : rs1[0] ∈ rs1.toList := by
    have hL : rs1.toList[0]? = some rs1[0] := by
      rw [Array.getElem?_toList, Array.getElem?_eq_getElem hpos]
    exact List.mem_of_getElem? hL
  obtain ⟨rc₀, hrc₀⟩ := hcar1.recRec.recrs rs1[0] h0mem
  have hget0 : rs1[0]? = some (.recr rc₀) := by rw [Array.getElem?_eq_getElem hpos, hrc₀]
  obtain ⟨n1, hmot1⟩ := hcar1.carrier 0 rc₀ hget0
  obtain ⟨n2, hmot2⟩ := hcar2.carrier 0 rc₀ hget0
  have hiprj_eq : Core.iprjAddr B 0 = Core.iprjAddr B' 0 :=
    Binding.FamilyOf.motiveCarrierAt_unique hmot1 hmot2
  obtain ⟨ind1, hind1⟩ := hcar1.ind0
  obtain ⟨ind2, hind2⟩ := hcar2.ind0
  have hh1 := hcar1.hashedIPrj0 ind1 hind1
  have hh2 := hcar2.hashedIPrj0 ind2 hind2
  have hser_eq :
      Ixon.serConstant ⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind1), #[], #[], #[], #[]⟩ =
      Ixon.serConstant ⟨Core.Specs.Callees.memberProjInfo B' 0 (.indc ind2), #[], #[], #[], #[]⟩ :=
    hW.runStore.hashed_inj hh1 hh2 hiprj_eq
  have hwf1 : (⟨Core.Specs.Callees.memberProjInfo B 0 (.indc ind1), #[], #[], #[], #[]⟩ :
      Ixon.Constant).wireWF := by
    obtain ⟨b1, hb1⟩ := hcar1.blockBytes
    rw [← hb1]
    exact L1.projConstant_wireWF_iPrj (0 : Nat).toUInt64 b1
  have hwf2 : (⟨Core.Specs.Callees.memberProjInfo B' 0 (.indc ind2), #[], #[], #[], #[]⟩ :
      Ixon.Constant).wireWF := by
    obtain ⟨b2, hb2⟩ := hcar2.blockBytes
    rw [← hb2]
    exact L1.projConstant_wireWF_iPrj (0 : Nat).toUInt64 b2
  have hde := congrArg Ixon.deConstantExact hser_eq
  rw [Ixon.Verify.deConstantExact_serConstant _ hwf1,
      Ixon.Verify.deConstantExact_serConstant _ hwf2] at hde
  have hc_eq := Except.ok.inj hde
  have hinfo_eq := congrArg Ixon.Constant.info hc_eq
  exact congrArg Ixon.InductiveProj.block (Ixon.ConstantInfo.iPrj.inj hinfo_eq)

end IxVM.Refinement.Typing
