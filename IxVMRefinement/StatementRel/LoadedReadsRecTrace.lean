import IxVMRefinement.StatementRel.LoadedReadsTrace

/-! # The binder plans of a converted recursor

`Convert::convert_recursor` converts a recursor's type at root `base`, with no `recur` address in
scope, and its rules with `Convert::convert_rec_rules`, rule `j`'s right-hand side at root
`base + 1 + j` (`Convert.lean`: `convert_rec_rules(…, 0, tbl, base + 1)`, each rule passing
`ridx + 1` on). This module retains those plans, in the style of `LoadedReadsTrace`:

* `RulesTraceRep`: the raw converted rule list (`RawRulesRep`) together with the binder plan of
  each rule's right-hand side; `convert_rec_rules_trace_spec`.
* `RecrTraceRep`: the raw converted recursor value (`RawRecrValRep`) together with the plans
  of its type and rules; `convert_recursor_trace_spec`.
* `get_ci_rprj_trace_spec`: `Ingress::get_ci_rprj` with the plans, at the member's root offset.
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

namespace IxVM.Refinement.Ingress

open IxVM (F)
open IxVM.Refinement.Obs
open IxVM.Refinement.TagN (u64Value)
open IxVM.Refinement.Deserialize
open Ixon.Verify.Codec
open Ixon.Verify.Codec.ConstantTables
open Ixon.Verify.Codec.NonrecursiveConstant

local notation "W" => IxVM.Refinement.Obs.W

/-! ## Converted rules and recursors with their binder plans -/

/-- **A converted rule list with the binder plans of its right-hand sides**, from rule index
`j` and root `root`: each cell holds rule `j`'s constructor index, field count and converted
right-hand side, which carries the plan of its root; the next rule is at `j + 1`, `root + 1`. -/
inductive RulesTraceRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (tree : BinderTreeData) (h : Heap F) :
    Nat → F → List Ixon.RecursorRule → SourceValue F → Prop where
  | nil {j : Nat} {root : F} {addr : Nat}
      (cell : h[addr]? = some (.construct Core.krrListEnum "Nil" [])) :
      RulesTraceRep refs recurAddrs univs sharing blobs tree h j root []
        (.ptr (.enum Core.krrListEnum) addr)
  | cons {j : Nat} {root : F} {addr : Nat} {rhsPtr rest : SourceValue F}
      {ru : Ixon.RecursorRule} {rus : List Ixon.RecursorRule} {plan : List Core.KLevel}
      (cell : h[addr]? = some (.construct Core.krrListEnum "Cons"
        [.construct Core.krrEnum "Mk" [.field (j : F), .field (ru.fields.toNat : F), rhsPtr],
          rest]))
      (hf : ru.fields.toNat < 72057594037927936)
      (raw : RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 ru.rhs rhsPtr)
      (planned : binderRootPlan tree sharing root ru.rhs = some plan)
      (levels : HeapBinderLevels h rhsPtr plan)
      (rs : RulesTraceRep refs recurAddrs univs sharing blobs tree h (j + 1) (root + 1) rus
        rest) :
      RulesTraceRep refs recurAddrs univs sharing blobs tree h j root (ru :: rus)
        (.ptr (.enum Core.krrListEnum) addr)

theorem RulesTraceRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {h₁ h₂ : Heap F} {j : Nat} {root : F}
    {rus : List Ixon.RecursorRule} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ q ∈ blobs₁, q ∈ blobs₂)
    (r : RulesTraceRep refs recurAddrs univs sharing blobs₁ tree h₁ j root rus p) :
    RulesTraceRep refs recurAddrs univs sharing blobs₂ tree h₂ j root rus p := by
  induction r with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | cons cell hf raw planned levels _ ih =>
    exact .cons (ext.getElem?_eq cell) hf (raw.mono ext hsub) planned
      (HeapBinderLevels.mono ext levels) ih

/-- The raw converted rule list, forgetting the plans. -/
theorem RulesTraceRep.toRaw {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {h : Heap F} {j : Nat} {root : F}
    {rus : List Ixon.RecursorRule} {p : SourceValue F}
    (r : RulesTraceRep refs recurAddrs univs sharing blobs tree h j root rus p) :
    RawRulesRep refs recurAddrs univs sharing blobs h j rus p := by
  induction r with
  | nil cell => exact .nil cell
  | cons cell hf raw _ _ _ ih => exact .cons cell ⟨hf, _, rfl, raw⟩ ih

/-- **A converted recursor value with the binder plans of its roots**: the raw converted value
(`RawRecrValRep`), where the type pointer carries the plan of root `root` and rule `j`'s
right-hand side the plan of root `root + 1 + j`, in the binder tree `tree`. -/
def RecrTraceRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (tree : BinderTreeData) (root : F) (h : Heap F) (rc : Ixon.Recursor)
    (blkAddr : _root_.Address) (recIdx : Nat) (v : SourceValue F) : Prop :=
  rc.lvls.toNat < 4294967296 ∧
  rc.params.toNat < 72057594037927936 ∧
  rc.indices.toNat < 72057594037927936 ∧
  rc.motives.toNat < 72057594037927936 ∧
  rc.minors.toNat < 72057594037927936 ∧
  recIdx < 72057594037927936 ∧
  ∃ (tyPtr rulesPtr blkPtr : SourceValue F) (b : Bytes.Address) (planT : List Core.KLevel),
    Core.ixAddr b = blkAddr ∧
    Bytes.RepAddressRef Core.addrTy h b blkPtr ∧
    v = .construct Core.kciEnum "Rec"
      [.field (rc.lvls.toNat : F), tyPtr,
       .field (rc.params.toNat : F), .field (rc.indices.toNat : F),
       .field (rc.motives.toNat : F), .field (rc.minors.toNat : F),
       rulesPtr, repBoolField rc.k, repBoolField rc.isUnsafe,
       blkPtr, .field (recIdx : F)] ∧
    RawConvExpr refs [] univs sharing blobs h 4294967295 rc.typ tyPtr ∧
    binderRootPlan tree sharing root rc.typ = some planT ∧
    HeapBinderLevels h tyPtr planT ∧
    RulesTraceRep refs recurAddrs univs sharing blobs tree h 0 (root + 1) rc.rules.toList rulesPtr

theorem RecrTraceRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {root : F} {h₁ h₂ : Heap F} {rc : Ixon.Recursor}
    {blkAddr : _root_.Address} {recIdx : Nat} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hsub : ∀ q ∈ blobs₁, q ∈ blobs₂)
    (rep : RecrTraceRep refs recurAddrs univs sharing blobs₁ tree root h₁ rc blkAddr recIdx v) :
    RecrTraceRep refs recurAddrs univs sharing blobs₂ tree root h₂ rc blkAddr recIdx v := by
  obtain ⟨hlvls, hp, hi, hm, hmi, hidx, tyPtr, rulesPtr, blkPtr, b, planT, hb, hblk, rfl, hty,
    hpT, hlT, hrls⟩ := rep
  obtain ⟨n, cellv, rfl, cell, hv⟩ := hblk
  exact ⟨hlvls, hp, hi, hm, hmi, hidx, tyPtr, rulesPtr, _, b, planT, hb,
    ⟨n, cellv, rfl, ext.getElem?_eq cell, hv⟩, rfl, hty.mono ext hsub, hpT,
    HeapBinderLevels.mono ext hlT, hrls.mono ext hsub⟩

/-- The raw converted recursor value, forgetting the plans. -/
theorem RecrTraceRep.toRaw {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {root : F} {h : Heap F} {rc : Ixon.Recursor}
    {blkAddr : _root_.Address} {recIdx : Nat} {v : SourceValue F}
    (rep : RecrTraceRep refs recurAddrs univs sharing blobs tree root h rc blkAddr recIdx v) :
    RawRecrValRep refs recurAddrs univs sharing blobs h rc blkAddr recIdx v := by
  obtain ⟨hlvls, hp, hi, hm, hmi, hidx, tyPtr, rulesPtr, blkPtr, b, planT, hb, hblk, hv, hty,
    hpT, hlT, hrls⟩ := rep
  exact ⟨hlvls, hp, hi, hm, hmi, hidx, tyPtr, rulesPtr, blkPtr, b, hb, hblk, hv, hty,
    hrls.toRaw⟩

/-! ## `Convert::convert_rec_rules` and `Convert::convert_recursor` with their plans -/

/-- **`Convert::convert_rec_rules` with the binder plans of the right-hand sides**: rule `j`
from root `root`, each next rule at the next root. -/
theorem convert_rec_rules_trace_spec {rus : List Ixon.RecursorRule} {tree : BinderTreeData} :
    ∀ {j : Nat} {root : F} {sharing : List Ixon.Expr}
      {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
      {x_rs shPtr refsPtr recPtr univsPtr tbl r : SourceValue F}
      {h h' : Heap F} {calls : List (Call F)},
      RepList recursorRuleListEnum RepRecursorRule h rus x_rs →
      RepShareVec h sharing shPtr →
      RepList addressListEnum RepIxonAddressRef h refs refsPtr →
      RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr →
      RepList univListEnum RepUnivPtr h univs univsPtr →
      RepBinderTreeData h tree tbl →
      RepBinderTree 4294967296 h tbl →
      ObsFn W "Convert::convert_rec_rules"
        [x_rs, shPtr, refsPtr, recPtr, univsPtr, .field (j : F), tbl, .field root] h r h' calls →
      Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
        HashedPairs calls blobs ∧
        RulesTraceRep refs recurAddrs univs sharing blobs tree h' j root rus r := by
  induction rus with
  | nil =>
    intro j root sharing refs recurAddrs univs x_rs shPtr refsPtr recPtr univsPtr tbl r h h' calls
      hrus _ _ _ _ _ _ ev
    rcases «Convert::convert_rec_rules».obs ev with
      ⟨_, he24, hm23, _⟩ |
      ⟨x_rest, x_fields, x_rhs, _, _, _, _, _, _, _, _, _, _, _, ld12, _, _, _, _, _, _, _, _⟩
    · subst r h'
      exact ⟨Heap.Extends.snoc h _, [], HashedPairs.nil, .nil (by simp)⟩
    · obtain ⟨_, _, he, _, _⟩ := Lib.rep_cons_of_load hrus ld12
      cases he
  | cons ru rest ih =>
    intro j root sharing refs recurAddrs univs x_rs shPtr refsPtr recPtr univsPtr tbl r h h' calls
      hrus hsh hrefs hrecs hunivs represented htbl ev
    rcases «Convert::convert_rec_rules».obs ev with
      ⟨ld12, _, _, _⟩ |
      ⟨x_rest, x_fields, x_rhs, v72, m73, cs83, v151, v162, m172, cs180, m199, cs207,
        v215, v217, ld12, ev85, he146, hm145, ev182, op266, op288, ev209, hc290⟩
    · have he := Lib.rep_nil_of_load hrus ld12
      cases he
    · obtain ⟨ru', rest', he, hru, hrest⟩ := Lib.rep_cons_of_load hrus ld12
      injection he with h1 h2; subst ru' rest'
      obtain ⟨rhsPtr, hru_eq, hrhs⟩ := hru
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hru_eq
      rcases hru_eq with ⟨_, _, hf_eq, hrhs_eq⟩
      subst x_fields x_rhs
      obtain ⟨ext1, blobs1, hhp1, hraw_rhs, plan, planned, levels⟩ :=
        convert_root_trace_spec hrhs hsh hrefs hrecs hunivs represented htbl ev85
      obtain ⟨hf56, hv162, hm172⟩ :=
        Lib.u64_to_field_spec (Deserialize.repU64_u64Value m73 ru.fields) ev182
      subst v162 m172
      simp only [evalBinOp, Except.ok.injEq] at op266
      have hv215 : v215 = .field (((j + 1 : Nat) : F)) := by
        rw [← op266]; push_cast; rfl
      simp only [evalBinOp, Except.ok.injEq] at op288
      subst v217
      rw [hv215] at ev209
      obtain ⟨ext2, blobs2, hhp2, hraw_rest⟩ :=
        ih (hrest.mono repRecursorRule_heapMono₂ ext1)
          (RepShareVec.mono ext1 hsh)
          (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
          (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
          (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
          (RepBinderTreeData.mono ext1 represented)
          (htbl.mono ext1) ev209
      subst r h'
      have ext_fin := Heap.Extends.snoc m199
        (.construct Core.krrListEnum "Cons"
          [.construct Core.krrEnum "Mk" [.field (j : F), .field (ru.fields.toNat : F), v72], v151])
      refine ⟨(ext1.trans ext2).trans ext_fin, blobs1 ++ blobs2,
        HashedPairs.append
          (hhp1.sub (by rw [hc290]; intro c hc; simp [hc]))
          (hhp2.sub (by rw [hc290]; intro c hc; simp [hc])),
        .cons (by simp) hf56
          (hraw_rhs.mono (ext2.trans ext_fin) (fun _ hm => List.mem_append_left _ hm))
          planned (HeapBinderLevels.mono (ext2.trans ext_fin) levels)
          (hraw_rest.mono ext_fin (fun _ hm => List.mem_append_right _ hm))⟩

/-- **`Convert::convert_recursor` with the binder plans of its roots**: the type at root
`root` (with no `recur` address in scope), rule `j` at root `root + 1 + j`. -/
theorem convert_recursor_trace_spec {rc : Ixon.Recursor} {blkAddr : _root_.Address}
    {recIdx : Nat} {sharing : List Ixon.Expr} {refs recurAddrs : List _root_.Address}
    {univs : List Ixon.Univ}
    {x_r x_block_addr shPtr refsPtr recPtr univsPtr tbl r : SourceValue F} {root : F}
    {h h' : Heap F} {calls : List (Call F)}
    (hrc : RepRecursor h rc x_r)
    (hblk : RepIxonAddressRef h blkAddr x_block_addr)
    (hrecIdx : recIdx < 72057594037927936)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    {tree : BinderTreeData} (represented : RepBinderTreeData h tree tbl)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_recursor"
      [x_r, x_block_addr, .field (recIdx : F), shPtr, refsPtr, recPtr, univsPtr, tbl,
        .field root] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      RecrTraceRep refs recurAddrs univs sharing blobs tree root h' rc blkAddr recIdx r := by
  obtain ⟨typPtr, rulesPtr, rfl, htyp, hrules⟩ := hrc
  obtain ⟨x_k, x_is_unsafe, x_lvls, x_params, x_indices, x_motives, x_minors, x_typ, x_rules,
      v62, m63, cs73, m105, v138, m139, cs149, v159,
      v226, v228, v229, v230, v231,
      m239, cs247, m266, cs274, m286, cs294, m306, cs314, m326, cs334,
      hv15, hm113, ev75, op221, ev151, he237,
      ev249, ev276, ev296, ev316, ev336, he380, hc381⟩ :=
    «Convert::convert_recursor».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hk_eq, hu_eq, hlvls_eq, hp_eq, hi_eq, hm_eq, hmi_eq, htyp_eq, hrules_eq⟩
  subst x_k x_is_unsafe x_lvls x_params x_indices x_motives x_minors x_typ x_rules
  have ext0 : Heap.Extends h m105 := by
    rw [hm113]; exact Heap.Extends.snoc h _
  have hm105' : m105 = h ++ [.construct addressListEnum "Nil" []] := by
    rw [addressListEnum_eq]; exact hm113
  have hnil_rec : RepList addressListEnum RepIxonAddressRef m105 []
      (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») h.length) := by
    rw [hm105', ← addressListEnum_eq]
    exact Lib.rep_store_nil h
  obtain ⟨ext1, blobs1, hhp1, hraw_ty, planT, plannedT, levelsT⟩ :=
    convert_root_trace_spec (htyp.mono ext0) (RepShareVec.mono ext0 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext0 hrefs)
      hnil_rec
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext0 hunivs)
      (RepBinderTreeData.mono ext0 represented) (htbl.mono ext0) ev75
  have ext01 := ext0.trans ext1
  simp only [evalBinOp, Except.ok.injEq] at op221
  subst v159
  obtain ⟨ext2, blobs2, hhp2, hraw_rules⟩ :=
    convert_rec_rules_trace_spec
      (hrules.mono repRecursorRule_heapMono₂ ext01)
      (RepShareVec.mono ext01 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext01 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext01 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext01 hunivs)
      (RepBinderTreeData.mono ext01 represented)
      (htbl.mono ext01) ev151
  obtain ⟨hlvls32, hv226, hm239⟩ := lvls_to_field_spec rc.lvls.toNat_lt ev249
  subst v226 m239
  obtain ⟨hp56, hv228, hm266⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.params) ev276
  subst v228 m266
  obtain ⟨hi56, hv229, hm286⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.indices) ev296
  subst v229 m286
  obtain ⟨hm56, hv230, hm306⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.motives) ev316
  subst v230 m306
  obtain ⟨hmi56, hv231, hm326⟩ :=
    Lib.u64_to_field_spec (Deserialize.repU64_u64Value m139 rc.minors) ev336
  rw [he380, hm326]; subst v231
  have ext_all := ext01.trans ext2
  obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core_ing (hblk.mono ext_all)
  exact ⟨ext_all, blobs1 ++ blobs2,
    HashedPairs.append
      (hhp1.sub (by rw [hc381]; intro c hc; simp [hc]))
      (hhp2.sub (by rw [hc381]; intro c hc; simp [hc])),
    hlvls32, hp56, hi56, hm56, hmi56, hrecIdx, v62, v138, x_block_addr, b, planT, hb_eq, hb_rep,
    he237,
    hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm), plannedT,
    HeapBinderLevels.mono ext2 levelsT,
    hraw_rules.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm)⟩

/-! ## `Ingress::get_ci_rprj` with the plans -/

/-- **`Ingress::get_ci_rprj` with the binder plans of the member's roots.** The parent block
`cb` at `ixAddr b` is loaded, member `idx` is a recursor `rc`, and `rc` is converted in the
binder tree built from the block's binder blocks, at the member's root offset in the block. -/
theorem get_ci_rprj_trace_spec {b : Bytes.Address} {idx : F}
    {x_block_addr r : SourceValue F} {h h' : Heap F} {calls : List (Call F)}
    (hbounded : IxVM.Consistency.Bounded calls)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::get_ci_rprj" [x_block_addr, .field idx] h r h' calls) :
    Heap.Extends h h' ∧ idx.val < 72057594037927936 ∧
      ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
        (rc : Ixon.Recursor) (blobs : List (_root_.Address × ByteArray)) (tree : BinderTreeData)
        (v : SourceValue F),
        Hashed calls blkBytes ∧
        Address.blake3Pure blkBytes = Core.ixAddr b ∧
        Ixon.deConstantExact blkBytes = .ok cb ∧
        cb.info = .muts ms ∧
        ms.toList[idx.val]? = some (.recr rc) ∧
        HashedPairs calls blobs ∧
        BinderTreeBuilt (binderLeavesData cb.binders.toList) tree ∧
        loadValue h' r = .ok v ∧
        RecrTraceRep cb.refs.toList (blockRecurAddrs (Core.ixAddr b) ms.toList)
          cb.univs.toList cb.sharing.toList blobs tree
          ((mutsRootOffset ms.toList idx.val : Nat) : F) h' rc (Core.ixAddr b) idx.val v := by
  obtain ⟨m2, cs12, x_sharing, x_refs, x_univs, x_binders, x_members,
      m86, cs96, x_r, v136, m137, cs147, v166, m167, cs174,
      v184, v185, m236, cs244, m256, cs264,
      ev14, ev98, ev149, he170, hm169, ev246, ev266, ev176, hc283⟩ :=
    «Ingress::get_ci_rprj».obs ev
  obtain ⟨ext1, blkList, cb, hhash_blk, haddr_blk, hexact_blk, hde_blk,
      _, _, _, hbd32, _, cRep⟩ :=
    load_verified_constant_decode hb ev14
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
  subst infoVal shPtr rfPtr unPtr bdPtr
  obtain ⟨ms, hcb_info, hms⟩ := repConstantInfo_muts_inv hinfo
  obtain ⟨hm86, hidx_lt_ms, mc, hmc_get, hmc_rep⟩ := muts_member_at_spec hms ev98
  subst m86
  have hcall_muts : (⟨"Ingress::muts_member_at", [x_members, .field idx], m2⟩ : Call F) ∈ calls := by
    rw [hc283]; simp
  have hms_len39 : ms.toList.length < 2 ^ 39 :=
    RomBound.bounded_length_lt hbounded hcall_muts (by simp) hms
  have hidx56 : idx.val < 72057594037927936 := by omega
  have hrecr : ∃ rc : Ixon.Recursor, mc = .recr rc ∧ RepRecursor m2 rc x_r := by
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
  obtain ⟨ext2, hrecs⟩ := build_recur_addrs_ixon_spec hms hb2 ev149
  obtain ⟨ext3, tree, built, represented, _, htbl⟩ :=
    binder_table_data_bounded_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev246
  have ext23 := ext2.trans ext3
  obtain ⟨_, baseEq, hm256⟩ := muts_root_offset_spec (hms.mono repMutConst_heapMono₂ ext23) ev266
  subst m256
  have ev176' : ObsFn W "Convert::convert_recursor"
      [x_r, x_block_addr, .field ((idx.val : Nat) : F), x_sharing, x_refs, v136,
       x_univs, v184, .field ((mutsRootOffset ms.toList idx.val : Nat) : F)] m236 v166 m167
        cs174 := by
    rw [← baseEq]
    rwa [ZMod.natCast_zmod_val idx]
  obtain ⟨ext4, blobs, hhp, htrace⟩ :=
    convert_recursor_trace_spec
      (hrc_rep.mono ext23)
      ((core_to_repIxonAddressRef hb2).mono ext23)
      hidx56
      (RepShareVec.mono ext23 hsh)
      (hrf.mono repIxonAddressRef_heapMono₂ ext23)
      (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
      (hun.mono repUnivPtr_heapMono₂ ext23)
      represented htbl ev176'
  rw [he170, hm169]
  have ext_snoc := Heap.Extends.snoc m167 v166
  refine ⟨(((ext1.trans ext23).trans ext4).trans ext_snoc), hidx56,
    ⟨blkList.toArray⟩, cb, ms, rc, blobs, tree, v166,
    hashed_sub hhash_blk (by rw [hc283]; intro c hc; simp [hc]),
    haddr_blk, hexact_blk, hcb_info, hmc_get,
    hhp.sub (by rw [hc283]; intro c hc; simp [hc]),
    built, loadValue_snoc m167 v166,
    htrace.mono ext_snoc (fun _ hm => hm)⟩

end IxVM.Refinement.Ingress
