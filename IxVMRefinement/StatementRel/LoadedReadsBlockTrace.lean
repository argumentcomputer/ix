import IxVMRefinement.StatementRel.LoadedReadsTrace

/-! # The binder plans of a loaded inductive type or constructor

`Ingress::get_ci` loads an inductive-projection record through `Ingress::get_ci_iprj` and a
constructor-projection record through `Ingress::get_ci_cprj`: the block is loaded, the member
(and constructor) is selected, and its type is converted with `Convert::convert_root` in the
binder tree built from the block's binder blocks, at the member's root (an inductive type at
the member's root offset, constructor `j` at that offset plus `1 + j`). This module retains the
binder plan of that root through the load, as `LoadedReadsTrace` does for definitions:

* `get_ci_block_trace_spec`: every `Ingress::get_ci` run, for an inductive-projection or a
  constructor-projection record (`GetCIBlockTraceResult`). The record has valid tables, so a
  projection record is the canonical one.
-/

set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library Aiur.Library.List

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement.TagN (u64Value)
open IxVM.Refinement.Deserialize
open Ixon.Verify.Codec
open Ixon.Verify.Codec.ConstantTables
open Ixon.Verify.Codec.NonrecursiveConstant

local notation "W" => IxVM.Refinement.Obs.W

/-- **What `Ingress::get_ci` returns for an inductive-projection or constructor-projection
record, with the binder plan of the converted type.** The block the record names was loaded
(hashed bytes at its address, decoded exactly); the member is an inductive (for a constructor
record, its constructor at the record's constructor index is `ct`); the type was converted in
the tree built from the block's binder blocks, at the member's root (`mutsRootOffset`) or, for
constructor `j`, at that root plus `1 + j`. Other record kinds are not described here. -/
def GetCIBlockTraceResult (calls : List (Call F)) (h : Heap F) (a : _root_.Address)
    (c : Ixon.Constant) (r : SourceValue F) : Prop :=
  match c.info with
  | .iPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive) (blobs : List (_root_.Address × ByteArray))
      (tree : BinderTreeData) (plan : List Core.KLevel) (v : SourceValue F),
      Hashed calls blkBytes ∧
      Address.blake3Pure blkBytes = p.block ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.indc ind) ∧
      HashedPairs calls blobs ∧
      BinderTreeBuilt (binderLeavesData cb.binders.toList) tree ∧
      binderRootPlan tree cb.sharing.toList ((mutsRootOffset ms.toList p.idx.toNat : Nat) : F)
        ind.typ = some plan ∧
      loadValue h r = .ok v ∧
      RawInductValRep cb.refs.toList (blockRecurAddrs p.block ms.toList) cb.univs.toList
        cb.sharing.toList blobs h ind p.block p.idx.toNat v ∧
      CITypeBinderLevels "Induct" h v plan
  | .cPrj p =>
    p.idx.toNat < 72057594037927936 ∧ p.cidx.toNat < 72057594037927936 ∧
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (ind : Ixon.Inductive) (ct : Ixon.Constructor) (blobs : List (_root_.Address × ByteArray))
      (tree : BinderTreeData) (plan : List Core.KLevel) (v : SourceValue F),
      Hashed calls blkBytes ∧
      Address.blake3Pure blkBytes = p.block ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.indc ind) ∧
      ind.ctors.toList[p.cidx.toNat]? = some ct ∧
      HashedPairs calls blobs ∧
      BinderTreeBuilt (binderLeavesData cb.binders.toList) tree ∧
      binderRootPlan tree cb.sharing.toList
        (((mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1 + ((p.cidx.toNat : Nat) : F))
        ct.typ = some plan ∧
      loadValue h r = .ok v ∧
      RawCtorValRep cb.refs.toList (blockRecurAddrs p.block ms.toList) cb.univs.toList
        cb.sharing.toList blobs h ct p.block p.idx.toNat v ∧
      CITypeBinderLevels "Ctor" h v plan
  | .defn _ => True
  | .axio _ => True
  | .quot _ => True
  | .recr _ => True
  | .dPrj _ => True
  | .rPrj _ => True
  | .muts _ => True

/-- **`Ingress::get_ci` with the binder plan of a loaded inductive type or constructor**: the
run hashed bytes `rawBytes` at `ixAddr a` that decode exactly to a record `c` with valid tables,
and for an inductive-projection or constructor-projection record the returned pointer holds
the converted value together with the binder plan of its type (`GetCIBlockTraceResult`). -/
theorem get_ci_block_trace_spec {a : Bytes.Address} {x_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded calls)
    (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn W "Ingress::get_ci" [x_addr] h r h' calls) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
      Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = Core.ixAddr a ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      ConstantTablesValid c ∧
      GetCIBlockTraceResult calls h' (Core.ixAddr a) c r := by
  rcases «Ingress::get_ci».obs ev with
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, v85, m86, cs96, m116,
      x_kind, x_safety, w139, w140, w141, w142, m174, cs185,
      v215, m216, cs223, v232, m277, cs285,
      ev14, ev98, ev187, hm211, he219, hm218, ev287, ev225, hc302⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, v85, m86, cs96, m116,
      x_kind, x_safety, w139, w140, w141, w142, v173, m174, cs185, m324,
      v336, m337, cs344, v353, m398, cs406,
      ev14, ev98, ev187, hne303, hm310, hm332, he340, hm339, ev408, ev346, hc423⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_axio,
      v437, m438, cs445, v453, m476, m496, cs504,
      ev14, he441, hm440, hm484, ev506, ev447, hc515⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_quot,
      v528, m529, cs536, v544, m567, m587, cs595,
      ev14, he532, hm531, hm575, ev597, ev538, hc606⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_block_addr, cs648,
      ev14, ev650, hc675⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_block_addr, cs718,
      v722, m731, cs739, ev14, ev741, ev720, hc750⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_cidx, x_block_addr, cs798,
      v802, v803, m812, cs820, m832, cs840, ev14, ev822, ev842, ev800, hc851⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_idx, x_block_addr, cs894,
      v898, m907, cs915, ev14, ev917, ev896, hc926⟩ |
    ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_recr, m941, m965,
      v977, m978, cs985, v995, m1046, cs1054,
      ev14, hm951, hm973, he981, hm980, ev1056, ev987, hc1071⟩
  · -- `Defn_n0`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal
    obtain ⟨d, hc_info, hd_rep⟩ := repConstantInfo_defn_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc302]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
  · -- `Defn_other`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal
    obtain ⟨d, hc_info, hd_rep⟩ := repConstantInfo_defn_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc423]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
  · -- `Axio`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal
    obtain ⟨ax, hc_info, hax_rep⟩ := repConstantInfo_axio_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc515]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
  · -- `Quot`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal
    obtain ⟨q, hc_info, hq_rep⟩ := repConstantInfo_quot_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc606]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
  · -- `DPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := repConstantInfo_dPrj_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc675]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
  · -- `IPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := repConstantInfo_iPrj_inv hinfo
    subst x_idx
    obtain ⟨hidx56, hv722, hm731⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 p.idx) ev741
    subst v722 m731
    obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core_ing hblk_ix
    have hbounded718 : IxVM.Consistency.Bounded cs718 :=
      RomBound.bounded_mono hbounded (by rw [hc750]; intro x hx; simp [hx])
    obtain ⟨ext2, _, blkBytes, cb, ms, ind, blobs, v,
        hhash_blk, haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hhp, hld, hraw,
        tree, plan, built, planned, levels⟩ :=
      get_ci_iprj_origin_spec hbounded718 hb_rep ev720
    rw [val_cast_u56_ing hidx56] at hmc_get hraw planned
    rw [hb_eq] at haddr_blk hraw
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc750]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
    exact ⟨hidx56, blkBytes, cb, ms, ind, blobs, tree, plan, v,
      hashed_sub hhash_blk (by rw [hc750]; intro x hx; simp [hx]),
      haddr_blk, hexact_blk, hcb_info, hmc_get,
      hhp.sub (by rw [hc750]; intro x hx; simp [hx]), built, planned, hld, hraw, levels⟩
  · -- `CPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hc_info, hx_idx, hx_cidx, hblk_ix⟩ := repConstantInfo_cPrj_inv hinfo
    subst x_idx x_cidx
    obtain ⟨hidx56, hv802, hm812⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 p.idx) ev822
    subst v802 m812
    obtain ⟨hcidx56, hv803, hm832⟩ :=
      Lib.u64_to_field_spec (Deserialize.repU64_u64Value m2 p.cidx) ev842
    subst v803 m832
    obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core_ing hblk_ix
    have hbounded798 : IxVM.Consistency.Bounded cs798 :=
      RomBound.bounded_mono hbounded (by rw [hc851]; intro x hx; simp [hx])
    obtain ⟨ext2, _, _, blkBytes, cb, ms, ind, ct, blobs, v,
        hhash_blk, haddr_blk, hexact_blk, hde_blk, hcb_info, hmc_get, hct_get, hhp, hld, hraw,
        tree, plan, built, planned, levels⟩ :=
      get_ci_cprj_origin_spec hbounded798 hb_rep ev800
    rw [val_cast_u56_ing hidx56] at hmc_get hraw planned
    rw [val_cast_u56_ing hcidx56] at hct_get
    rw [hb_eq] at haddr_blk hraw
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc851]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
    exact ⟨hidx56, hcidx56, blkBytes, cb, ms, ind, ct, blobs, tree, plan, v,
      hashed_sub hhash_blk (by rw [hc851]; intro x hx; simp [hx]),
      haddr_blk, hexact_blk, hcb_info, hmc_get, hct_get,
      hhp.sub (by rw [hc851]; intro x hx; simp [hx]), built, planned, hld, hraw, levels⟩
  · -- `RPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := repConstantInfo_rPrj_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc926]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]
  · -- `Recr`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal
    obtain ⟨rc, hc_info, hrc_rep⟩ := repConstantInfo_recr_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc1071]; intro x hx; simp [hx]),
      haddr, hexact, htables, ?_⟩
    simp only [GetCIBlockTraceResult, hc_info]

end IxVM.Refinement.L1
