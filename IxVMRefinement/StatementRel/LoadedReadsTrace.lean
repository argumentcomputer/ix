import IxVMRefinement.L1.Ingress

/-! # The binder plans of a loaded definition, axiom or definition projection

`Ingress::get_ci` converts a record's expressions with `Convert::convert_root`, which annotates
each binder of the converted term with a level read from the record's binder blocks. The raw
conversion relation (`RawConvExpr`) leaves that level unconstrained, so it cannot compare two
loads of one record. The conversion's own trace can: the levels a root carries are the binder
plan of the root (`binderRootPlan`), a function of the record's binder blocks, its sharing table,
the root's number and the expression.

This module retains that plan through the record conversions and the load:

* `convert_definition_trace_spec`, `convert_axiom_trace_spec`: the converted value with the
  plans of its roots (a definition converts its type at root `base` and its value at
  `base + 1`; an axiom converts its type at root `0`);
* `get_ci_dprj_trace_spec`: the load of a definition member of a block, whose base is the
  member's root offset in the block;
* `get_ci_trace_spec`: every `Ingress::get_ci` run, for a definition, axiom or
  definition-projection record.

The binder tree is the one built from the decoded record's own binder blocks
(`BinderTreeBuilt`, which determines it).
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

/-! ## Converted values with their binder plans -/

/-- **A converted definition value with the binder plans of its two roots**: the raw converted
value (`RawDefnValRep`), where the type pointer carries the plan of root `root` and the value
pointer the plan of root `root + 1`, in the binder tree `tree`. -/
def DefnTraceRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (tree : BinderTreeData) (root : F) (h : Heap F) (d : Ixon.Definition)
    (v : SourceValue F) : Prop :=
  d.lvls.toNat < 4294967296 ∧
  ∃ (tyPtr valPtr hint : SourceValue F) (planT planV : List Core.KLevel),
    v = defnValShape d tyPtr valPtr hint ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 d.typ tyPtr ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 d.value valPtr ∧
    binderRootPlan tree sharing root d.typ = some planT ∧
    binderRootPlan tree sharing (root + 1) d.value = some planV ∧
    HeapBinderLevels h tyPtr planT ∧ HeapBinderLevels h valPtr planV

theorem DefnTraceRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {root : F} {h₁ h₂ : Heap F} {d : Ixon.Definition}
    {v : SourceValue F} (ext : Heap.Extends h₁ h₂)
    (rep : DefnTraceRep refs recurAddrs univs sharing blobs tree root h₁ d v) :
    DefnTraceRep refs recurAddrs univs sharing blobs tree root h₂ d v := by
  obtain ⟨hl, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := rep
  exact ⟨hl, tyPtr, valPtr, hint, planT, planV, hv, rty.mono ext (fun _ hm => hm),
    rval.mono ext (fun _ hm => hm), hpT, hpV, HeapBinderLevels.mono ext hlT,
    HeapBinderLevels.mono ext hlV⟩

/-- The raw converted value, forgetting the plans. -/
theorem DefnTraceRep.toRaw {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {root : F} {h : Heap F} {d : Ixon.Definition}
    {v : SourceValue F}
    (rep : DefnTraceRep refs recurAddrs univs sharing blobs tree root h d v) :
    RawDefnValRep refs recurAddrs univs sharing blobs h d v := by
  obtain ⟨hl, tyPtr, valPtr, hint, planT, planV, hv, rty, rval, hpT, hpV, hlT, hlV⟩ := rep
  exact ⟨hl, tyPtr, valPtr, hint, hv, rty, rval⟩

/-- **A converted axiom value with the binder plan of its type**, converted at root `0`. -/
def AxioTraceRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (tree : BinderTreeData) (h : Heap F) (ax : Ixon.Axiom) (v : SourceValue F) : Prop :=
  ax.lvls.toNat < 4294967296 ∧
  ∃ (tyPtr : SourceValue F) (plan : List Core.KLevel),
    v = .construct Core.kciEnum "Axiom"
      [.field (ax.lvls.toNat : F), tyPtr, repBoolField ax.isUnsafe] ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 ax.typ tyPtr ∧
    binderRootPlan tree sharing 0 ax.typ = some plan ∧
    HeapBinderLevels h tyPtr plan

theorem AxioTraceRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {h₁ h₂ : Heap F} {ax : Ixon.Axiom} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (rep : AxioTraceRep refs recurAddrs univs sharing blobs tree h₁ ax v) :
    AxioTraceRep refs recurAddrs univs sharing blobs tree h₂ ax v := by
  obtain ⟨hl, tyPtr, plan, hv, rty, hp, hlv⟩ := rep
  exact ⟨hl, tyPtr, plan, hv, rty.mono ext (fun _ hm => hm), hp, HeapBinderLevels.mono ext hlv⟩

/-- The raw converted value, forgetting the plan. -/
theorem AxioTraceRep.toRaw {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {h : Heap F} {ax : Ixon.Axiom} {v : SourceValue F}
    (rep : AxioTraceRep refs recurAddrs univs sharing blobs tree h ax v) :
    RawAxioValRep refs recurAddrs univs sharing blobs h ax v := by
  obtain ⟨hl, tyPtr, plan, hv, rty, hp, hlv⟩ := rep
  exact ⟨hl, tyPtr, hv, rty⟩

/-- **A converted quotient value with the binder plan of its type**, converted at root `0`. -/
def QuotTraceRep (refs recurAddrs : List _root_.Address) (univs : List Ixon.Univ)
    (sharing : List Ixon.Expr) (blobs : List (_root_.Address × ByteArray))
    (tree : BinderTreeData) (h : Heap F) (q : Ixon.Quotient) (v : SourceValue F) : Prop :=
  q.lvls.toNat < 4294967296 ∧
  ∃ (tyPtr : SourceValue F) (plan : List Core.KLevel),
    v = .construct Core.kciEnum "Quot"
      [.field (q.lvls.toNat : F), tyPtr, repQuotKindVal q.kind] ∧
    RawConvExpr refs recurAddrs univs sharing blobs h 4294967295 q.typ tyPtr ∧
    binderRootPlan tree sharing 0 q.typ = some plan ∧
    HeapBinderLevels h tyPtr plan

theorem QuotTraceRep.mono {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {sharing : List Ixon.Expr} {blobs : List (_root_.Address × ByteArray)}
    {tree : BinderTreeData} {h₁ h₂ : Heap F} {q : Ixon.Quotient} {v : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (rep : QuotTraceRep refs recurAddrs univs sharing blobs tree h₁ q v) :
    QuotTraceRep refs recurAddrs univs sharing blobs tree h₂ q v := by
  obtain ⟨hl, tyPtr, plan, hv, rty, hp, hlv⟩ := rep
  exact ⟨hl, tyPtr, plan, hv, rty.mono ext (fun _ hm => hm), hp, HeapBinderLevels.mono ext hlv⟩

/-! ## `Convert::convert_definition` and `Convert::convert_axiom` with their plans -/

/-- **`Convert::convert_definition` with the binder plans of its roots.** The type is converted
at root `root` and the value at root `root + 1` of the binder tree the table holds. -/
theorem convert_definition_trace_spec {d : Ixon.Definition} {sharing : List Ixon.Expr}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_d shPtr refsPtr recPtr univsPtr x_hint tbl r : SourceValue F} {root : F}
    {h h' : Heap F} {calls : List (Call F)}
    (hd : RepDefinition h d x_d)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    {tree : BinderTreeData} (represented : RepBinderTreeData h tree tbl)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_definition"
      [x_d, shPtr, refsPtr, recPtr, univsPtr, x_hint, tbl, .field root] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      DefnTraceRep refs recurAddrs univs sharing blobs tree root h' d r := by
  obtain ⟨typPtr, valPtr, rfl, htyp, hval⟩ := hd
  rcases «Convert::convert_definition».obs ev with
    ⟨x_safety, w17, x_lvls, x_typ, x_value, v48, m49, cs59, v118, m119, cs129, v138,
      v196, m197, cs207, hv15, ev61, op194, ev131, ev209, he242, he278, hc279⟩ |
    ⟨x_safety, w17, x_lvls, x_typ, x_value, v48, m49, cs59, v118, m119, cs129, v138,
      v196, m197, cs207, v313, m314, cs316,
      hv15, ev61, op194, ev131, ev209, sg321, he329, he358, hc359⟩ |
    ⟨x_safety, w17, x_lvls, x_typ, x_value, v48, m49, cs59, v118, m119, cs129, v138,
      v196, m197, cs207, hv15, ev61, op194, ev131, ev209, he373, he395, hc396⟩
  · -- Definition
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hkind, hsaf, _, hlvls_eq, htyp_eq, hval_eq⟩
    subst x_safety x_lvls x_typ x_value
    have hdk : d.kind = .defn := by
      cases hk : d.kind <;> simp [repDefKindVal, hk] at hkind; rfl
    simp only [evalBinOp, Except.ok.injEq] at op194
    subst v138
    obtain ⟨ext1, blobs1, hhp1, hraw_ty, planT, plannedT, levelsT⟩ :=
      convert_root_trace_spec htyp hsh hrefs hrecs hunivs represented htbl ev61
    obtain ⟨ext2, blobs2, hhp2, hraw_val, planV, plannedV, levelsV⟩ :=
      convert_root_trace_spec (hval.mono ext1) (RepShareVec.mono ext1 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
      (RepBinderTreeData.mono ext1 represented) (htbl.mono ext1) ev131
    obtain ⟨hlvls32, hv196, hm197⟩ := lvls_to_field_spec d.lvls.toNat_lt ev209
    rw [he278, hm197]; subst v196
    refine ⟨ext1.trans ext2, blobs1 ++ blobs2,
      HashedPairs.append
        (hhp1.sub (by rw [hc279]; intro c hc; simp [hc]))
        (hhp2.sub (by rw [hc279]; intro c hc; simp [hc])),
      hlvls32, v48, v118, x_hint, planT, planV, ?_,
      hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm),
      hraw_val.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm),
      plannedT, plannedV, HeapBinderLevels.mono ext2 levelsT, levelsV⟩
    simp [defnValShape, hdk, he242]
  · -- Opaque
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hkind, hsaf, _, hlvls_eq, htyp_eq, hval_eq⟩
    subst x_safety x_lvls x_typ x_value
    have hdk : d.kind = .opaq := by
      cases hk : d.kind <;> simp [repDefKindVal, hk] at hkind; rfl
    simp only [evalBinOp, Except.ok.injEq] at op194
    subst v138
    obtain ⟨ext1, blobs1, hhp1, hraw_ty, planT, plannedT, levelsT⟩ :=
      convert_root_trace_spec htyp hsh hrefs hrecs hunivs represented htbl ev61
    obtain ⟨ext2, blobs2, hhp2, hraw_val, planV, plannedV, levelsV⟩ :=
      convert_root_trace_spec (hval.mono ext1) (RepShareVec.mono ext1 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
      (RepBinderTreeData.mono ext1 represented) (htbl.mono ext1) ev131
    obtain ⟨hlvls32, hv196, hm197⟩ := lvls_to_field_spec d.lvls.toNat_lt ev209
    subst v196 m197
    have hv313 : v313 = repBoolField (d.safety == .unsaf) ∧ m314 = m119 := by
      rcases sg321 with ⟨hv301, rfl, rfl, _⟩ | ⟨hne306, rfl, rfl, _⟩
      · refine ⟨?_, rfl⟩
        cases hs : d.safety <;> simp [repDefSafetyVal, hs] at hv301
        rfl
      · refine ⟨?_, rfl⟩
        cases hs : d.safety
        · exact (hne306 [] rfl (by simp [repDefSafetyVal, hs])).elim
        · rfl
        · rfl
    rcases hv313 with ⟨hv313_eq, hm314⟩
    rw [he358, hm314]; subst v313
    refine ⟨ext1.trans ext2, blobs1 ++ blobs2,
      HashedPairs.append
        (hhp1.sub (by rw [hc359]; intro c hc; simp [hc]))
        (hhp2.sub (by rw [hc359]; intro c hc; simp [hc])),
      hlvls32, v48, v118, x_hint, planT, planV, ?_,
      hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm),
      hraw_val.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm),
      plannedT, plannedV, HeapBinderLevels.mono ext2 levelsT, levelsV⟩
    simp [defnValShape, hdk, he329]
  · -- Theorem
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
    rcases hv15 with ⟨_, _, hkind, hsaf, _, hlvls_eq, htyp_eq, hval_eq⟩
    subst x_safety x_lvls x_typ x_value
    have hdk : d.kind = .thm := by
      cases hk : d.kind <;> simp [repDefKindVal, hk] at hkind; rfl
    simp only [evalBinOp, Except.ok.injEq] at op194
    subst v138
    obtain ⟨ext1, blobs1, hhp1, hraw_ty, planT, plannedT, levelsT⟩ :=
      convert_root_trace_spec htyp hsh hrefs hrecs hunivs represented htbl ev61
    obtain ⟨ext2, blobs2, hhp2, hraw_val, planV, plannedV, levelsV⟩ :=
      convert_root_trace_spec (hval.mono ext1) (RepShareVec.mono ext1 hsh)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrefs)
      (repList_heapMono₂ _ repIxonAddressRef_heapMono₂ ext1 hrecs)
      (repList_heapMono₂ _ repUnivPtr_heapMono₂ ext1 hunivs)
      (RepBinderTreeData.mono ext1 represented) (htbl.mono ext1) ev131
    obtain ⟨hlvls32, hv196, hm197⟩ := lvls_to_field_spec d.lvls.toNat_lt ev209
    rw [he395, hm197]; subst v196
    refine ⟨ext1.trans ext2, blobs1 ++ blobs2,
      HashedPairs.append
        (hhp1.sub (by rw [hc396]; intro c hc; simp [hc]))
        (hhp2.sub (by rw [hc396]; intro c hc; simp [hc])),
      hlvls32, v48, v118, x_hint, planT, planV, ?_,
      hraw_ty.mono ext2 (fun _ hm => List.mem_append_left _ hm),
      hraw_val.mono (Heap.Extends.refl _) (fun _ hm => List.mem_append_right _ hm),
      plannedT, plannedV, HeapBinderLevels.mono ext2 levelsT, levelsV⟩
    simp [defnValShape, hdk, he373]

/-- **`Convert::convert_axiom` with the binder plan of its type**, converted at root `0`. -/
theorem convert_axiom_trace_spec {ax : Ixon.Axiom} {sharing : List Ixon.Expr}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_a shPtr refsPtr recPtr univsPtr tbl r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hax : RepAxiom h ax x_a)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    {tree : BinderTreeData} (represented : RepBinderTreeData h tree tbl)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_axiom"
      [x_a, shPtr, refsPtr, recPtr, univsPtr, tbl] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      AxioTraceRep refs recurAddrs univs sharing blobs tree h' ax r := by
  obtain ⟨typPtr, rfl, htyp⟩ := hax
  obtain ⟨x_is_unsafe, x_lvls, x_typ, v32, m33, cs43, v104, m109, cs117,
      hv15, ev45, he107, ev119, he142, hc143⟩ :=
    «Convert::convert_axiom».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hu_eq, hlvls_eq, htyp_eq⟩
  subst x_is_unsafe x_lvls x_typ
  obtain ⟨ext1, blobs, hhp, hraw_ty, plan, planned, levels⟩ :=
    convert_root_trace_spec htyp hsh hrefs hrecs hunivs represented htbl ev45
  obtain ⟨hlvls32, hv104, hm109⟩ := lvls_to_field_spec ax.lvls.toNat_lt ev119
  rw [he142, hm109]; subst v104
  exact ⟨ext1, blobs, hhp.sub (by rw [hc143]; intro c hc; simp [hc]),
    hlvls32, v32, plan, he107, hraw_ty, planned, levels⟩

/-- **`Convert::convert_quotient` with the binder plan of its type**, converted at root `0`. -/
theorem convert_quotient_trace_spec {q : Ixon.Quotient} {sharing : List Ixon.Expr}
    {refs recurAddrs : List _root_.Address} {univs : List Ixon.Univ}
    {x_q shPtr refsPtr recPtr univsPtr tbl r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hq : RepQuotient h q x_q)
    (hsh : RepShareVec h sharing shPtr)
    (hrefs : RepList addressListEnum RepIxonAddressRef h refs refsPtr)
    (hrecs : RepList addressListEnum RepIxonAddressRef h recurAddrs recPtr)
    (hunivs : RepList univListEnum RepUnivPtr h univs univsPtr)
    {tree : BinderTreeData} (represented : RepBinderTreeData h tree tbl)
    (htbl : RepBinderTree 4294967296 h tbl)
    (ev : ObsFn W "Convert::convert_quotient"
      [x_q, shPtr, refsPtr, recPtr, univsPtr, tbl] h r h' calls) :
    Heap.Extends h h' ∧ ∃ blobs : List (_root_.Address × ByteArray),
      HashedPairs calls blobs ∧
      QuotTraceRep refs recurAddrs univs sharing blobs tree h' q r := by
  obtain ⟨typPtr, rfl, htyp⟩ := hq
  obtain ⟨x_kind, x_lvls, x_typ, v32, m33, cs43, v104, m109, cs117,
      hv15, ev45, he107, ev119, he142, hc143⟩ :=
    «Convert::convert_quotient».obs ev
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hv15
  rcases hv15 with ⟨_, _, hk_eq, hlvls_eq, htyp_eq⟩
  subst x_kind x_lvls x_typ
  obtain ⟨ext1, blobs, hhp, hraw_ty, plan, planned, levels⟩ :=
    convert_root_trace_spec htyp hsh hrefs hrecs hunivs represented htbl ev45
  obtain ⟨hlvls32, hv104, hm109⟩ := lvls_to_field_spec q.lvls.toNat_lt ev119
  rw [he142, hm109]; subst v104
  exact ⟨ext1, blobs, hhp.sub (by rw [hc143]; intro c hc; simp [hc]),
    hlvls32, v32, plan, he107, hraw_ty, planned, levels⟩

/-! ## The loads with their plans -/

/-- **`Ingress::get_ci_dprj` with the binder plans of the member's roots.** The parent block
`cb` at `ixAddr b` is loaded, member `idx` is a definition `d`, and `d` is converted in the
binder tree built from the block's binder blocks, at the member's root offset in the block. -/
theorem get_ci_dprj_trace_spec {b : Bytes.Address} {idx : Nat}
    {x_dprj_addr x_idx x_block_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (hidx_lt : idx < 18446744073709551616)
    (hx_idx : x_idx = u64Value idx)
    (hb : Bytes.RepAddressRef Core.addrTy h b x_block_addr)
    (ev : ObsFn W "Ingress::get_ci_dprj" [x_dprj_addr, x_idx, x_block_addr] h r h' calls) :
    Heap.Extends h h' ∧ idx < 72057594037927936 ∧
      ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
        (d : Ixon.Definition) (blobs : List (_root_.Address × ByteArray))
        (tree : BinderTreeData) (v : SourceValue F),
        Hashed calls blkBytes ∧
        Address.blake3Pure blkBytes = Core.ixAddr b ∧
        Ixon.deConstantExact blkBytes = .ok cb ∧
        cb.info = .muts ms ∧
        ms.toList[idx]? = some (.defn d) ∧
        HashedPairs calls blobs ∧
        BinderTreeBuilt (binderLeavesData cb.binders.toList) tree ∧
        loadValue h' r = .ok v ∧
        DefnTraceRep cb.refs.toList (defnMemberRecurAddrs d (Core.ixAddr b) ms.toList)
          cb.univs.toList cb.sharing.toList blobs tree
          ((mutsRootOffset ms.toList idx : Nat) : F) h' d v := by
  subst x_idx
  obtain ⟨v1, m2, cs12, m24, cs34, x_sharing, x_refs, x_univs, x_binders, x_members,
      m108, cs118, x_d, v158, m159, cs169, v188, m189, cs199,
      v226, m227, cs234, v243, v244, m288, cs296, m308, cs316, v320, m329, cs337,
      ev14, ev36, ev120, ev171, ev201, he230, hm229, ev298, ev339, ev318, ev236, hc348⟩ :=
    «Ingress::get_ci_dprj».obs ev
  have ext0 := ev14.heap_extends
  have hb2 := Bytes.repAddressRef_heapMono₂ Core.addrTy ext0 hb
  obtain ⟨ext1, blkList, cb, hhash_blk, haddr_blk, hexact_blk, hde_blk,
      _, _, _, hbd32, _, cRep⟩ :=
    load_verified_constant_decode hb2 ev36
  obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
  simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
  rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
  subst infoVal shPtr rfPtr unPtr bdPtr
  obtain ⟨ms, hcb_info, hms⟩ := repConstantInfo_muts_inv hinfo
  rw [← Names.«WordLists::lookup_u64<Ixon::MutConst>».symbol] at ev120
  have hms_inst : RepList (Instance.mk "Lists::Node" [.named "Ixon::MutConst" []]).symbol
      RepMutConst m24 ms.toList x_members := by
    rwa [Names.«Lists::Node<Ixon::MutConst>».symbol]
  obtain ⟨⟨mc, hmc_get, hmc_rep⟩, hm108⟩ := Lib.lookup_u64_spec hidx_lt rfl ev120 hms_inst
  subst m108
  have hdefn : ∃ d : Ixon.Definition, mc = .defn d ∧ RepDefinition m24 d x_d := by
    cases mc with
    | defn d =>
      obtain ⟨dv, hdv_eq, hdv⟩ := hmc_rep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hdv_eq
      rcases hdv_eq with ⟨_, _, rfl⟩
      exact ⟨d, rfl, hdv⟩
    | indc _ => obtain ⟨iv, hiv, _⟩ := hmc_rep; simp at hiv
    | recr _ => obtain ⟨rv, hrv, _⟩ := hmc_rep; simp at hrv
  obtain ⟨d, rfl, hd_rep⟩ := hdefn
  have ext2 := ev171.heap_extends
  have hb159 := Bytes.repAddressRef_heapMono₂ Core.addrTy (ext0.trans (ext1.trans ext2)) hb
  obtain ⟨ext3, hrecs⟩ :=
    defn_member_recur_addrs_spec (hd_rep.mono ext2) (hms.mono repMutConst_heapMono₂ ext2)
      hb159 ev201
  have ext23 := ext2.trans ext3
  obtain ⟨ext4, tree, built, represented, _, htbl⟩ :=
    binder_table_data_bounded_spec (hbd.mono repBinderBlock_heapMono₂ ext23) hbd32 ev298
  have ext24 := ext23.trans ext4
  obtain ⟨hidx56, hv320, hm329⟩ :=
    Lib.u64_to_field_spec (Lib.repU64_ofNatLT m288 hidx_lt) ev339
  simp only [UInt64.toNat_ofNatLT] at hidx56 hv320
  subst v320 m329
  obtain ⟨_, hbase, hm308⟩ :=
    muts_root_offset_spec (hms.mono repMutConst_heapMono₂ ext24) ev318
  subst m308
  rw [val_cast_u56_ing hidx56] at hbase
  subst v244
  obtain ⟨ext5, blobs, hhp, htrace⟩ :=
    convert_definition_trace_spec
      (hd_rep.mono ext24)
      (RepShareVec.mono ext24 hsh)
      (hrf.mono repIxonAddressRef_heapMono₂ ext24)
      (hrecs.mono repIxonAddressRef_heapMono₂ ext4)
      (hun.mono repUnivPtr_heapMono₂ ext24)
      represented htbl ev236
  rw [he230, hm229]
  have ext_snoc := Heap.Extends.snoc m227 v226
  have ext_all := (((ext0.trans ext1).trans ext24).trans ext5).trans ext_snoc
  refine ⟨ext_all, hidx56, ⟨blkList.toArray⟩, cb, ms, d, blobs, tree, v226,
    hashed_sub hhash_blk (by rw [hc348]; intro c hc; simp [hc]),
    haddr_blk, hexact_blk, hcb_info, hmc_get,
    hhp.sub (by rw [hc348]; intro c hc; simp [hc]),
    built, loadValue_snoc m227 v226,
    htrace.mono ext_snoc⟩

/-- **What `Ingress::get_ci` returns for a definition, axiom or definition-projection record,
with the binder plans of the converted roots.** The tree is built from the binder blocks of
the record whose expressions are converted: the record itself, or the block of a projection. A
standalone definition is converted at base root `0`; a member at its root offset in the block.
Other record kinds are not described here. -/
def GetCITraceResult (calls : List (Call F)) (h : Heap F) (a : _root_.Address)
    (c : Ixon.Constant) (r : SourceValue F) : Prop :=
  match c.info with
  | .defn d =>
    ∃ (blobs : List (_root_.Address × ByteArray)) (tree : BinderTreeData) (v : SourceValue F),
      HashedPairs calls blobs ∧
      BinderTreeBuilt (binderLeavesData c.binders.toList) tree ∧
      loadValue h r = .ok v ∧
      DefnTraceRep c.refs.toList (defnRecurAddrs d a) c.univs.toList c.sharing.toList blobs
        tree 0 h d v
  | .axio ax =>
    ∃ (blobs : List (_root_.Address × ByteArray)) (tree : BinderTreeData) (v : SourceValue F),
      HashedPairs calls blobs ∧
      BinderTreeBuilt (binderLeavesData c.binders.toList) tree ∧
      loadValue h r = .ok v ∧
      AxioTraceRep c.refs.toList [] c.univs.toList c.sharing.toList blobs tree h ax v
  | .dPrj p =>
    p.idx.toNat < 72057594037927936 ∧
    ∃ (blkBytes : ByteArray) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (d : Ixon.Definition) (blobs : List (_root_.Address × ByteArray))
      (tree : BinderTreeData) (v : SourceValue F),
      Hashed calls blkBytes ∧
      Address.blake3Pure blkBytes = p.block ∧
      Ixon.deConstantExact blkBytes = .ok cb ∧
      cb.info = .muts ms ∧
      ms.toList[p.idx.toNat]? = some (.defn d) ∧
      HashedPairs calls blobs ∧
      BinderTreeBuilt (binderLeavesData cb.binders.toList) tree ∧
      loadValue h r = .ok v ∧
      DefnTraceRep cb.refs.toList (defnMemberRecurAddrs d p.block ms.toList)
        cb.univs.toList cb.sharing.toList blobs tree
        ((mutsRootOffset ms.toList p.idx.toNat : Nat) : F) h d v
  | .quot q =>
    ∃ (blobs : List (_root_.Address × ByteArray)) (tree : BinderTreeData) (v : SourceValue F),
      HashedPairs calls blobs ∧
      BinderTreeBuilt (binderLeavesData c.binders.toList) tree ∧
      loadValue h r = .ok v ∧
      QuotTraceRep c.refs.toList [] c.univs.toList c.sharing.toList blobs tree h q v
  | .recr _ => True
  | .iPrj _ => True
  | .cPrj _ => True
  | .rPrj _ => True
  | .muts _ => True

/-- **`Ingress::get_ci` with the binder plans of the converted roots**: the run hashed bytes
`rawBytes` at `ixAddr a` that decode exactly to a record `c`, and for a definition, axiom or
definition-projection record the returned pointer holds the converted value together with the
binder plans of its roots (`GetCITraceResult`). -/
theorem get_ci_trace_spec {a : Bytes.Address} {x_addr r : SourceValue F}
    {h h' : Heap F} {calls : List (Call F)}
    (ha : Bytes.RepAddressRef Core.addrTy h a x_addr)
    (ev : ObsFn W "Ingress::get_ci" [x_addr] h r h' calls) :
    ∃ (rawBytes : ByteArray) (c : Ixon.Constant),
      Hashed calls rawBytes ∧
      Address.blake3Pure rawBytes = Core.ixAddr a ∧
      Ixon.deConstantExact rawBytes = .ok c ∧
      GetCITraceResult calls h' (Core.ixAddr a) c r := by
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
    subst infoVal shPtr rfPtr unPtr bdPtr
    let dv := Value.construct "Ixon::Definition" "Mk" [x_kind, x_safety, w139, w140, w141, w142]
    obtain ⟨d, hc_info, hd_rep⟩ := repConstantInfo_defn_inv hinfo
    have ⟨_, _, hd_mk, _, _⟩ := hd_rep
    have hks : x_kind = repDefKindVal d.kind ∧ x_safety = repDefSafetyVal d.safety := by
      simp only [dv, Value.construct.injEq, List.cons.injEq, and_true] at hd_mk
      rcases hd_mk with ⟨_, _, hk_eq, hs_eq, _, _, _, _⟩
      exact ⟨hk_eq, hs_eq⟩
    have ext2 := ev98.heap_extends
    rw [hks.1, hks.2] at ev187
    obtain ⟨hf0, hm174⟩ := defn_is_unsafe_ci_spec (d := d) ev187
    subst m174
    have hfalse : defnIsUnsafeCI d = false := by
      cases hu : defnIsUnsafeCI d <;> simp [repBoolField, hu] at hf0
      rfl
    have ext3 : Heap.Extends m86 m116 := by rw [hm211]; exact Heap.Extends.snoc m86 _
    have hrecs : RepList addressListEnum RepIxonAddressRef m116
        (defnRecurAddrs d (Core.ixAddr a))
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m86.length) := by
      simp only [defnRecurAddrs, hfalse, Bool.false_eq_true, ↓reduceIte]
      rw [hm211, addressListEnum_eq]
      exact Lib.rep_store_nil m86
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, tree, built, represented, _, htbl⟩ :=
      binder_table_data_bounded_spec (hbd.mono repBinderBlock_heapMono₂ ext23) hbd32 ev287
    have ext24 := ext23.trans ext4
    obtain ⟨ext5, blobs, hhp, htrace⟩ :=
      convert_definition_trace_spec
        (hd_rep.mono ext24)
        (RepShareVec.mono ext24 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext24)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext4)
        (hun.mono repUnivPtr_heapMono₂ ext24)
        represented htbl ev225
    rw [he219, hm218]
    have ext_snoc := Heap.Extends.snoc m216 v215
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc302]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
    exact ⟨blobs, tree, v215, hhp.sub (by rw [hc302]; intro x hx; simp [hx]), built,
      loadValue_snoc m216 v215, htrace.mono ext_snoc⟩
  · -- `Defn_other`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    let dv := Value.construct "Ixon::Definition" "Mk" [x_kind, x_safety, w139, w140, w141, w142]
    obtain ⟨d, hc_info, hd_rep⟩ := repConstantInfo_defn_inv hinfo
    have ⟨_, _, hd_mk, _, _⟩ := hd_rep
    have hks : x_kind = repDefKindVal d.kind ∧ x_safety = repDefSafetyVal d.safety := by
      simp only [dv, Value.construct.injEq, List.cons.injEq, and_true] at hd_mk
      rcases hd_mk with ⟨_, _, hk_eq, hs_eq, _, _, _, _⟩
      exact ⟨hk_eq, hs_eq⟩
    have ext2 := ev98.heap_extends
    rw [hks.1, hks.2] at ev187
    obtain ⟨hv173, hm174⟩ := defn_is_unsafe_ci_spec (d := d) ev187
    subst m174
    have htrue : defnIsUnsafeCI d = true := by
      cases hu : defnIsUnsafeCI d
      · simp [repBoolField, hu] at hv173
        exact (hne303 hv173).elim
      · rfl
    have ext3a : Heap.Extends m86 m324 := by rw [hm332]; exact Heap.Extends.snoc m86 _
    have ext3b : Heap.Extends m324 m116 := by rw [hm310]; exact Heap.Extends.snoc m324 _
    have ext3 := ext3a.trans ext3b
    have hnil324 : RepList Names.«Lists::Node<&[Field; 32]>» RepIxonAddressRef m324 []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m86.length) := by
      rw [hm332]; exact Lib.rep_store_nil m86
    have ha324 : RepIxonAddressRef m324 (Core.ixAddr a) x_addr :=
      (core_to_repIxonAddressRef ha).mono ((ext1.trans ext2).trans ext3a)
    have hrecs : RepList addressListEnum RepIxonAddressRef m116
        (defnRecurAddrs d (Core.ixAddr a))
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m324.length) := by
      simp only [defnRecurAddrs, htrue, ↓reduceIte]
      rw [hm310, addressListEnum_eq]
      exact Lib.rep_store_cons repIxonAddressRef_heapMono₂ ha324 hnil324
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, tree, built, represented, _, htbl⟩ :=
      binder_table_data_bounded_spec (hbd.mono repBinderBlock_heapMono₂ ext23) hbd32 ev408
    have ext24 := ext23.trans ext4
    obtain ⟨ext5, blobs, hhp, htrace⟩ :=
      convert_definition_trace_spec
        (hd_rep.mono ext24)
        (RepShareVec.mono ext24 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext24)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext4)
        (hun.mono repUnivPtr_heapMono₂ ext24)
        represented htbl ev346
    rw [he340, hm339]
    have ext_snoc := Heap.Extends.snoc m337 v336
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc423]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
    exact ⟨blobs, tree, v336, hhp.sub (by rw [hc423]; intro x hx; simp [hx]), built,
      loadValue_snoc m337 v336, htrace.mono ext_snoc⟩
  · -- `Axio`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    obtain ⟨ax, hc_info, hax_rep⟩ := repConstantInfo_axio_inv hinfo
    have ext2 : Heap.Extends m2 m476 := by rw [hm484]; exact Heap.Extends.snoc m2 _
    have hrecs : RepList addressListEnum RepIxonAddressRef m476 []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m2.length) := by
      rw [hm484, addressListEnum_eq]
      exact Lib.rep_store_nil m2
    obtain ⟨ext3, tree, built, represented, _, htbl⟩ :=
      binder_table_data_bounded_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev506
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, blobs, hhp, htrace⟩ :=
      convert_axiom_trace_spec
        (hax_rep.mono ext23)
        (RepShareVec.mono ext23 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext23)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
        (hun.mono repUnivPtr_heapMono₂ ext23)
        represented htbl ev447
    rw [he441, hm440]
    have ext_snoc := Heap.Extends.snoc m438 v437
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc515]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
    exact ⟨blobs, tree, v437, hhp.sub (by rw [hc515]; intro x hx; simp [hx]), built,
      loadValue_snoc m438 v437, htrace.mono ext_snoc⟩
  · -- `Quot`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    obtain ⟨q, hc_info, hq_rep⟩ := repConstantInfo_quot_inv hinfo
    have ext2 : Heap.Extends m2 m567 := by rw [hm575]; exact Heap.Extends.snoc m2 _
    have hrecs : RepList addressListEnum RepIxonAddressRef m567 []
        (.ptr (.enum Names.«Lists::Node<&[Field; 32]>») m2.length) := by
      rw [hm575, addressListEnum_eq]
      exact Lib.rep_store_nil m2
    obtain ⟨ext3, tree, built, represented, _, htbl⟩ :=
      binder_table_data_bounded_spec (hbd.mono repBinderBlock_heapMono₂ ext2) hbd32 ev597
    have ext23 := ext2.trans ext3
    obtain ⟨ext4, blobs, hhp, htrace⟩ :=
      convert_quotient_trace_spec
        (hq_rep.mono ext23)
        (RepShareVec.mono ext23 hsh)
        (hrf.mono repIxonAddressRef_heapMono₂ ext23)
        (hrecs.mono repIxonAddressRef_heapMono₂ ext3)
        (hun.mono repUnivPtr_heapMono₂ ext23)
        represented htbl ev538
    rw [he532, hm531]
    have ext_snoc := Heap.Extends.snoc m529 v528
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc606]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
    exact ⟨blobs, tree, v528, hhp.sub (by rw [hc606]; intro x hx; simp [hx]), built,
      loadValue_snoc m529 v528, htrace.mono ext_snoc⟩
  · -- `DPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := repConstantInfo_dPrj_inv hinfo
    obtain ⟨b, hb_eq, hb_rep⟩ := repIxonAddressRef_to_core_ing hblk_ix
    obtain ⟨ext2, hidx56, blkBytes, cb, ms, d, blobs, tree, v,
        hhash_blk, haddr_blk, hexact_blk, hcb_info, hmc_get, hhp, built, hld, htrace⟩ :=
      get_ci_dprj_trace_spec p.idx.toNat_lt hx_idx hb_rep ev650
    rw [hb_eq] at haddr_blk htrace
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc675]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
    exact ⟨hidx56, blkBytes, cb, ms, d, blobs, tree, v,
      hashed_sub hhash_blk (by rw [hc675]; intro x hx; simp [hx]),
      haddr_blk, hexact_blk, hcb_info, hmc_get,
      hhp.sub (by rw [hc675]; intro x hx; simp [hx]), built, hld, htrace⟩
  · -- `IPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hc_info, hx_idx, hblk_ix⟩ := repConstantInfo_iPrj_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc750]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
  · -- `CPrj`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, _, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, _, _, _, _⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, _, _, _, _⟩
    subst infoVal
    obtain ⟨p, hc_info, hx_idx, hx_cidx, hblk_ix⟩ := repConstantInfo_cPrj_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc851]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
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
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]
  · -- `Recr`
    obtain ⟨ext1, rawList, c, hhash, haddr, hexact, hde, _, _, _, hbd32, htables, cRep⟩ :=
      load_verified_constant_decode ha ev14
    obtain ⟨infoVal, shPtr, rfPtr, unPtr, bdPtr, hc_eq, hinfo, hsh, hrf, hun, hbd⟩ := cRep
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hc_eq
    rcases hc_eq with ⟨_, _, hinfo_eq, hsh_eq, hrf_eq, hun_eq, hbd_eq⟩
    subst infoVal shPtr rfPtr unPtr bdPtr
    obtain ⟨rc, hc_info, hrc_rep⟩ := repConstantInfo_recr_inv hinfo
    refine ⟨⟨rawList.toArray⟩, c,
      hashed_sub hhash (by rw [hc1071]; intro x hx; simp [hx]),
      haddr, hexact, ?_⟩
    simp only [GetCITraceResult, hc_info]

end IxVM.Refinement.L1
