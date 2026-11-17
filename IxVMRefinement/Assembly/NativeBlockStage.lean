import IxVMRefinement.Decl.StagedLoads
import IxVMRefinement.Decl.NativeStage
import IxVMRefinement.StatementRel.LoadedReadsCanonCtor
import IxVMRefinement.Assembly.TypingBasisProj
import IxVMRefinement.Assembly.NativeCapabilities

/-! # The stages of a native inductive block: their load contracts

A native inductive block of one member (the type former) and its constructors, without its
recursor, is checked in two typed stages over the prefix environment `env`:

* **the former stage**: the former's type is checked against the prefix, so its load contract
  is the prefix's (`Decl.stagedLoads_former`);
* **the constructor stage**: the constructors' types are checked against the prefix with the
  former stored (`Decl.ctorStage`). Its load contract is `Decl.stagedLoads_cons_former`'s, from
  the facts at the staged former (`Decl.FormerLoads`) and the absence of a stored key at the
  marker of the former's address.

This file produces both inputs from the block record:

* `formerLoads_of_block`: the six `FormerLoads` facts. A load at the former's key represents the
  canonical former under the stage's keying; a member or constructor load at a block whose
  member key is the former's is a load at this block (the records the store holds at the
  projection addresses of a hashed block are those projections, `HashedBlockProjectionsHeld`);
  the record facts are the held record's; the capability record is unit-like where the record
  says so.
* `HashKeyed`, the store clause behind the marker input: every stored key that is the key of an
  address is the key of an address of 32 bytes. It is not a consequence of `Decl.PrefixInv`
  (nothing there constrains a stored key at an address no record can have), so the block step
  reads it from the extra clause of the fold.
* `ctorStageLoads_of_block`, `ctorStageCoreFacts_of_block`: the constructor stage's load contract
  and its scoped core facts.

The representation lemmas are the canonical ones of `LoadedReadsCanonInd`/`LoadedReadsCanonCtor`
stated at any keying that agrees with the table's on the cells a record can use
(`ind_value_at`, `ctor_value_at`, `get_ci_iprj_at`, `get_ci_iprj_load_at`, `get_ci_cprj_load_at`):
the stage's keying resolves the former but not the constructors.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-! ## Converted terms and values at any keying -/

/-- **A converted term of a record is represented under any keying** that resolves the
references the record uses and the `recur` addresses of the conversion as the table does, and
permits a projection at those references. -/
theorem tmC_at_of_used {t : Ix.Kernel.RoleTable} {κ : _root_.Address → Core.KKey}
    {c : Ixon.Constant} {recurAddrs : List _root_.Address}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {bound : Nat} {e : Ixon.Expr}
    {p : SourceValue F} {X : Core.KExpr}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h
      bound e p)
    (he : ∀ i, i ∈ exprRefIdxs e → i ∈ usedRefIdxs c)
    (hused : ∀ i ∈ usedRefIdxs c, ∀ x, c.refs.toList[i]? = some x →
      κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x)
    (hrecur : ∀ x ∈ recurAddrs, κ x = Core.keyOf t x)
    (rep : Core.TmC (Core.keyOf t) h X p) : Core.TmC κ h X p := by
  have used : ∀ x, L1.RefUsed c.refs.toList c.sharing.toList e x →
      κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x := by
    intro x hu
    obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
    · exact hused i (he i hi) x hr
    · have hmem : i ∈ usedRefIdxs c := by
        unfold usedRefIdxs
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
      exact hused i hmem x hr
  refine raw.tmC_rekey rep (fun x hu => ?_) (fun x hu => (used x hu).2)
  rcases hu with hu | hr
  · exact (used x hu).1
  · exact hrecur x hr

section At

variable {t : Ix.Kernel.RoleTable}

/-- **`ind_value_canon` at any keying**: the traced conversion of an inductive member represents
the canonical constant under every keying that agrees with the table's on the references the
block uses (with the projection permission there) and on the block's member addresses. -/
theorem ind_value_at (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
    {B : _root_.Address} {k : Nat} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} (hmuts : cb.info = .muts ms) (hmem : ms[k]? = some (.indc ind))
    {blobs : List (_root_.Address × ByteArray)}
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    {tree : L1.BinderTreeData}
    (built : L1.BinderTreeBuilt (L1.binderLeavesData cb.binders.toList) tree)
    {plan : List Core.KLevel}
    (planned : L1.binderRootPlan tree cb.sharing.toList ((L1.mutsRootOffset ms.toList k : Nat) : F)
      ind.typ = some plan)
    {h : Heap F} {v : SourceValue F}
    (raw : L1.RawInductValRep cb.refs.toList (L1.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h ind B k v)
    (levels : L1.CITypeBinderLevels "Induct" h v plan)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t blob cb id (blockSelf t B ms)).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ind.lvls.toNat) ((L1.mutsRootOffset ms.toList k : Nat) : F)
        ind.typ ty₀ = some ty' ∧ Annotates ty' ty₀ ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs B ms.toList, κ x = Core.keyOf t x) →
        ∀ caps : Ix.Kernel.IndCaps .anon, Core.CIRep κ h v
          (.indInfo ⟨Core.keyOf t (Core.iprjAddr B k), List.range ind.lvls.toNat, ty'⟩ caps) := by
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := raw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := levels
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst htp
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon_range ht hlvls (blockSelf_key t B ms) hagree rty built planned trace hty
      hty_lbb hty_def
  refine ⟨ty', hcT, hannT, fun κ hused hrecur caps => ?_⟩
  have hmem' : Ixon.MutConst.indc ind ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  have heT : ∀ i, i ∈ exprRefIdxs ind.typ → i ∈ usedRefIdxs cb := by
    intro i hi
    unfold usedRefIdxs
    rw [hmuts]
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨.indc ind, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
  have hκ : κ (Core.iprjAddr B k) = Core.keyOf t (Core.iprjAddr B k) := by
    have hin := memberAddr_mem_blockRecurAddrs (B := B) hmem
    rw [memberAddr_indc] at hin
    exact hrecur _ hin
  exact .induct (valRep_range hlvls (tmC_at_of_used rty heT hused hrecur htmT))
    ⟨ind.params.toNat, ind.indices.toNat, ind.ctors.size, rfl, rfl, rfl, hp56, hi56, hc56⟩
    ⟨b, ((k : Nat) : F), hb_rep, rfl, by rw [hb_eq, L1.val_cast_u56_ing hidx56, hκ]⟩

/-- **`ctor_value_canon` at any keying**: the traced conversion of a constructor represents the
canonical constant under every keying that agrees with the table's on the references the block
uses (with the projection permission there) and on the block's member addresses. The
constructor's name is the keying's at its own address, which need not resolve. -/
theorem ctor_value_at (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
    {B : _root_.Address} {k j : Nat} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} {ct : Ixon.Constructor} (hmuts : cb.info = .muts ms)
    (hmem : ms[k]? = some (.indc ind)) (hctm : ct ∈ ind.ctors.toList) (hcidx : ct.cidx.toNat = j)
    {blobs : List (_root_.Address × ByteArray)}
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    {tree : L1.BinderTreeData}
    (built : L1.BinderTreeBuilt (L1.binderLeavesData cb.binders.toList) tree)
    {plan : List Core.KLevel}
    (planned : L1.binderRootPlan tree cb.sharing.toList
      (((L1.mutsRootOffset ms.toList k : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ = some plan)
    {h : Heap F} {v : SourceValue F}
    (raw : L1.RawCtorValRep cb.refs.toList (L1.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h ct B k v)
    (levels : L1.CITypeBinderLevels "Ctor" h v plan)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t blob cb id (blockSelf t B ms)).read ct.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList k : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ ty₀ =
        some ty' ∧ Annotates ty' ty₀ ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs B ms.toList, κ x = Core.keyOf t x) →
        Core.CIRep κ h v
          (.ctorInfo ⟨κ (Core.cprjAddr B k j), List.range ct.lvls.toNat, ty'⟩
            ct.params.toNat ct.fields.toNat) := by
  obtain ⟨hlvls, hcidx56, hp56, hf56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := raw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := levels
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst htp
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon_range ht hlvls (blockSelf_key t B ms) hagree rty built planned trace hty
      hty_lbb hty_def
  refine ⟨ty', hcT, hannT, fun κ hused hrecur => ?_⟩
  have hmem' : Ixon.MutConst.indc ind ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  have heT : ∀ i, i ∈ exprRefIdxs ct.typ → i ∈ usedRefIdxs cb := by
    intro i hi
    unfold usedRefIdxs
    rw [hmuts]
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨.indc ind, hmem', by
        unfold mutRefIdxs
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ct, hctm, hi⟩)⟩)
  exact .ctor (valRep_range hlvls (tmC_at_of_used rty heT hused hrecur htmT)) rfl rfl
    ⟨hp56, hf56⟩
    ⟨b, ((k : Nat) : F), ((ct.cidx.toNat : Nat) : F), hb_rep, rfl, rfl, by
      rw [hb_eq, L1.val_cast_u56_ing hidx56, L1.val_cast_u56_ing hcidx56, hcidx]⟩

/-- **`get_ci_iprj_canon` at any keying**: a `get_ci` at a held inductive-projection record
represents the canonical constant under every keying that agrees with the table's on the
references the block uses and on the block's member addresses. -/
theorem get_ci_iprj_at (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {a : Aiur.Library.Bytes.Address} {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c cb : Ixon.Constant}
    {p : Ixon.InductiveProj} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hrec : recordOf E (Core.ixAddr a) = some c) (hinfo : c.info = .iPrj p)
    (hblock : recordOf E p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.indc ind)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t p.block ms)).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) ind.typ ty₀ = some ty' ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs p.block ms.toList, κ x = Core.keyOf t x) →
        ∀ caps : Ix.Kernel.IndCaps .anon, Core.CIPtrRep κ h' ptr
          (.indInfo ⟨keyOf t (Core.ixAddr a), List.range ind.lvls.toNat, ty'⟩ caps) := by
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hbound ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  have haddr' : Core.ixAddr a = memberAddr p.block p.idx.toNat (.indc ind) :=
    haddr.symm.trans (iprj_canonical ind hex htv hinfo).2
  have hkey : keyOf t (Core.ixAddr a) = Core.keyOf t (Core.iprjAddr p.block p.idx.toNat) := by
    rw [haddr', memberAddr_indc, keyOf_eq]
  unfold L1.GetCIBlockTraceResult at hres
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  have hms' : ms[p.idx.toNat]? = some (.indc ind') := by
    rw [← Array.getElem?_toList]
    exact hms
  have hiEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hms'))
  subst hiEq
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, -, hrepS⟩ :=
    ind_value_at ht hmuts hmem hagree built planned hraw hlev hty hty_lbb hty_def
  rw [hkey]
  exact ⟨ty', hcT, fun κ hused hrecur caps => ⟨_, hld, hrepS κ hused hrecur caps⟩⟩

/-- **`get_ci_iprj_load_canon` at any keying**: a direct member load on a held block. -/
theorem get_ci_iprj_load_at (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {b : Aiur.Library.Bytes.Address} {blkArg ptr : SourceValue F} {i : F} {h h' : Heap F}
    (hb : Aiur.Library.Bytes.RepAddressRef Core.addrTy h b blkArg)
    (ev : ObsFn Core.W "Ingress::get_ci_iprj" [blkArg, .field i] h ptr h' cs)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hblock : recordOf E (Core.ixAddr b) = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i.val]? = some (.indc ind)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t (Core.ixAddr b) ms)).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList i.val : Nat) : F) ind.typ ty₀ = some ty' ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) ms.toList, κ x = Core.keyOf t x) →
        ∀ caps : Ix.Kernel.IndCaps .anon, Core.CIPtrRep κ h' ptr
          (.indInfo ⟨Core.keyOf t (Core.iprjAddr (Core.ixAddr b) i.val),
            List.range ind.lvls.toNat, ty'⟩ caps) := by
  obtain ⟨-, -, blkBytes, cb', ms', ind', blobs, v, hhB, haB, hexB, -, hcb, hms, hhp, hld,
    hraw, tree, plan, built, planned, hlev⟩ := L1.get_ci_iprj_origin_spec hbound hb ev
  obtain ⟨lcB, hgetB, hdecB⟩ := recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  have hms' : ms[i.val]? = some (.indc ind') := by
    rw [← Array.getElem?_toList]
    exact hms
  have hiEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hms'))
  subst hiEq
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, -, hrepS⟩ :=
    ind_value_at ht hmuts hmem hagree built planned hraw hlev hty hty_lbb hty_def
  exact ⟨ty', hcT, fun κ hused hrecur caps => ⟨_, hld, hrepS κ hused hrecur caps⟩⟩

/-- **A direct constructor load on a held block represents the canonical constructor at any
keying** that agrees with the table's on the references the block uses and on the block's member
addresses, where every constructor of the member has its position as stored index and a reading
of its type. The constructor named by the load is in the record. -/
theorem get_ci_cprj_load_at (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {b : Aiur.Library.Bytes.Address} {blkArg ptr : SourceValue F} {i j : F} {h h' : Heap F}
    (hb : Aiur.Library.Bytes.RepAddressRef Core.addrTy h b blkArg)
    (ev : ObsFn Core.W "Ingress::get_ci_cprj" [blkArg, .field i, .field j] h ptr h' cs)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hblock : recordOf E (Core.ixAddr b) = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i.val]? = some (.indc ind))
    (hctys : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty ∧
        cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    ∃ (ct : Ixon.Constructor) (ty' : Ix.Kernel.Expr .anon), ind.ctors[j.val]? = some ct ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) ms.toList, κ x = Core.keyOf t x) →
        Core.CIPtrRep κ h' ptr
          (.ctorInfo ⟨κ (Core.cprjAddr (Core.ixAddr b) i.val j.val),
            List.range ct.lvls.toNat, ty'⟩ ct.params.toNat ct.fields.toNat) := by
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct, blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    hhp, hld, hraw, tree, plan, built, planned, hlev⟩ := L1.get_ci_cprj_origin_spec hbound hb ev
  rw [← ZMod.natCast_zmod_val j] at planned
  obtain ⟨lcB, hgetB, hdecB⟩ := recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hnc blkBytes hhB haB
  have hcB : cb = cb' := by
    rw [hbB, hdecB] at hexB
    exact Except.ok.inj hexB
  subst hcB
  have hmsEq : ms = ms' := Ixon.ConstantInfo.muts.inj (hmuts.symm.trans hcb)
  subst hmsEq
  have hms' : ms[i.val]? = some (.indc ind') := by
    rw [← Array.getElem?_toList]
    exact hms
  have hiEq : ind = ind' := Ixon.MutConst.indc.inj (Option.some.inj (hmem.symm.trans hms'))
  subst hiEq
  have hct : ind.ctors[j.val]? = some ct := by
    rw [← Array.getElem?_toList]
    exact hcts
  have hctm : ct ∈ ind.ctors.toList := List.mem_of_getElem? hcts
  obtain ⟨hcidx, cty, hty, hty_lbb, hty_def⟩ := hctys j.val ct hct
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', -, -, hrepS⟩ :=
    ctor_value_at ht hmuts hmem hctm hcidx hagree built planned hraw hlev hty hty_lbb hty_def
  exact ⟨ct, ty', hct, fun κ hused hrecur => ⟨_, hld, hrepS κ hused hrecur⟩⟩

end At

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency

/-! ## The store clause behind the marker input -/

/-- **Every key the environment stores that is the key of an address is the key of an address
of 32 bytes.** Role keys are keys of the table's addresses; an `.id` key is the key of the
address itself. The fold stores constants only at the keys of record addresses (hashes) and at
derived keys, so the clause is a fact about the fold's store, not about any one prefix. -/
def HashKeyed (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ ci ∈ env.consts, ∀ y : _root_.Address, ci.name = Core.keyOf t y → y.hash.size = 32

/-- The marker input of the constructor stage, from the store clause. -/
theorem HashKeyed.marker_none {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    (h : HashKeyed t env) (f : _root_.Address) :
    env.find? (Core.keyOf t (Core.projMarker f)) = none :=
  Decl.find?_projMarker_none h f

/-- **The store clause is kept by constants at the keys of 32-byte addresses and at keys of no
address.** -/
theorem HashKeyed.append {t : Ix.Kernel.RoleTable} (htwf : t.wf = true)
    {env : Ix.Kernel.Env .anon} (h : HashKeyed t env) {new : List (Ix.Kernel.ConstantInfo .anon)}
    (hnew : ∀ ci ∈ new, (∃ x : _root_.Address, ci.name = Core.keyOf t x ∧ x.hash.size = 32) ∨
      ∀ y : _root_.Address, ci.name ≠ Core.keyOf t y) :
    HashKeyed t ⟨new ++ env.consts⟩ := by
  intro ci hci y hy
  rcases List.mem_append.mp hci with hn | ho
  · rcases hnew ci hn with ⟨x, hx, hsz⟩ | hno
    · have hxy : x = y := Core.keyOf_inj htwf (hx.symm.trans hy)
      rw [← hxy]
      exact hsz
    · exact absurd hy (hno y)
  · exact h ci ho y hy

/-! ## Small facts -/

private theorem toUInt64_toNat_b {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

theorem val_lt_uint64 (i : F) : ZMod.val i < UInt64.size :=
  Nat.lt_trans (ZMod.val_lt i) (by decide)

theorem recordAt_of_recordOf {E : Ixon.Env} (hdec : L1.EnvDecoded E) {a : _root_.Address}
    {c : Ixon.Constant} (h : recordOf E a = some c) : Ix.Cert.recordAt E a = some c :=
  (recordOf_eq_recordAt_of_decoded hdec a).symm.trans h

/-- The exact decoding at an address of the store, in the form the L1 record lemmas take. -/
theorem decoded_at_of_recordOf {E : Ixon.Env} {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf E a = some c) :
    ∀ lc, E.consts.get? a = some lc → Ixon.deConstantExact lc.rawBytes = .ok c := by
  intro lc hlc
  obtain ⟨lc₀, hlc₀, hex⟩ := LoadedReads.recordOf_inv h
  rw [hlc₀] at hlc
  cases hlc
  exact hex

/-- The canonical record at an address of a decoded store. -/
theorem canonicalRecord_of_recordOf {E : Ixon.Env} (hdec : L1.EnvDecoded E) {a : _root_.Address}
    {c : Ixon.Constant} (h : recordOf E a = some c) : Nonempty (L1.CanonicalRecordAt E a) := by
  obtain ⟨lc, hlc, hex⟩ := LoadedReads.recordOf_inv h
  obtain ⟨c', hc', hce⟩ := hdec a lc hlc
  exact ⟨⟨lc, c', hlc, hc', hce⟩⟩

/-- **A member key of a hashed block that is the key of the former is the former's**: where the
store holds the inductive projection of member `0` of `B` at its address, a block a run hashed
whose member `i` has that key is `B`, and `i = 0`. -/
theorem iprj_key_block {t : Ix.Kernel.RoleTable} (htwf : t.wf = true) {E : Ixon.Env}
    (hdec : L1.EnvDecoded E) (hP : HashedBlockProjectionsHeld E) {B b : _root_.Address}
    {ind : Ixon.Inductive}
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hbh : Core.HashedBlockAt E b) {i : Nat} (hi : i < UInt64.size)
    (hkey : Core.keyOf t (Core.iprjAddr b i) = Core.keyOf t (Core.iprjAddr B 0)) :
    b = B ∧ i = 0 := by
  have hx : Core.iprjAddr b i = Core.iprjAddr B 0 := Core.keyOf_inj htwf hkey
  have hrec : Ix.Cert.recordAt E (Core.iprjAddr b i) = some (memberProjection B 0 (.indc ind)) := by
    rw [hx]
    exact recordAt_of_recordOf hdec hproj
  have hinfo := (hP b hbh).1 i _ hrec
  have h0 : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  rw [h0] at hinfo
  injection hinfo with hp
  injection hp with hidx hblk
  refine ⟨hblk.symm, ?_⟩
  have e := congrArg UInt64.toNat hidx
  rw [toUInt64_toNat_b (by decide : (0 : Nat) < UInt64.size), toUInt64_toNat_b hi] at e
  exact e.symm

/-! ## The keying of the constructor stage -/

section Stage

variable {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {t : Ix.Kernel.RoleTable}
  {lim : Option Nat} {cvF : Ix.Kernel.ConstantVal .anon} {caps : Ix.Kernel.IndCaps .anon}

/-- A key the prefix stores resolves at the constructor stage as the table keys it, and a
projection is permitted there. -/
theorem ctorStage_of_find (hfresh : env.find? cvF.name = none)
    (hnt : ∀ T : Core.KKey, cvF.name ≠ Ix.Kernel.projTableName T) {x : _root_.Address}
    {ci : Ix.Kernel.ConstantInfo .anon} (hf : env.find? (Core.keyOf t x) = some ci) :
    (Decl.ctorStage ⟨E, env, t, lim⟩ cvF caps).κ x = Core.keyOf t x ∧
      Core.ProjPermitted (Decl.ctorStage ⟨E, env, t, lim⟩ cvF caps).κ x := by
  have hext := Decl.consCtx_ext (c := ⟨E, env, t, lim⟩) (cn := .indInfo cvF caps) hfresh hnt
  exact ⟨Core.Ctx.stagedOver_key_of_find (c := Decl.consCtx ⟨E, env, t, lim⟩ (.indInfo cvF caps))
      (pre := env) (hext.find hf),
    Core.Ctx.stagedOver_projPermitted_of_find
      (c := Decl.consCtx ⟨E, env, t, lim⟩ (.indInfo cvF caps)) (pre := env) hf⟩

/-- The former's address resolves at the constructor stage as the table keys it. -/
theorem ctorStage_former {f : _root_.Address} (hname : cvF.name = Core.keyOf t f) :
    (Decl.ctorStage ⟨E, env, t, lim⟩ cvF caps).κ f = Core.keyOf t f := by
  have hf : (Decl.consCtx ⟨E, env, t, lim⟩ (.indInfo cvF caps)).env.find? (Core.keyOf t f) =
      some (.indInfo cvF caps) := by
    rw [← hname]
    exact Ix.Kernel.Env.find?_cons_self (Ix.Kernel.ConstantInfo.indInfo cvF caps) env
  exact Core.Ctx.stagedOver_key_of_find (c := Decl.consCtx ⟨E, env, t, lim⟩ (.indInfo cvF caps))
    (pre := env) hf

end Stage

/-! ## The load facts at the staged former -/

/-- **The six load facts at the staged former, from the block record.** The store `E` (decoded)
holds the block `cb` at `B`, a block of one member, the inductive `ind`, and its inductive
projection at the former's address; the projections the store holds at a hashed block's
projection addresses are those projections (`hP`); `ty₀` is the reading of the former's type and
every constructor has its position as stored index and a reading of its type, over `E`'s blobs;
the prefix stores the references the block uses and not the former's key. The staged former is
the canonical one (`hcanon`); its capability record is unit-like where the record has one
constructor, with no field, and no index (`hunit`); its key is no reserved basis name. -/
theorem formerLoads_of_block {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat} (hdec : L1.EnvDecoded E)
    (hP : HashedBlockProjectionsHeld E)
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hbounds : ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hctys : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
        cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb)
    {ty' : Ix.Kernel.Expr .anon}
    (hcanon : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ = some ty')
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {caps : Ix.Kernel.IndCaps .anon}
    (hunit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
      (∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0) →
      caps.unitlike = true ∧ caps.unitParams = ind.params.toNat)
    (hfree : Ix.Kernel.reservedBasisNames.contains (Core.keyOf t (Core.iprjAddr B 0)) = false) :
    Decl.FormerLoads ⟨E, env, t, lim⟩
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have h0 : ((0 : Nat).toUInt64).toNat = 0 := toUInt64_toNat_b (by decide)
  have h0' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := h0
  -- the stage's keying on the cells of the block
  have hnt : ∀ T : Core.KKey, Core.keyOf t (Core.iprjAddr B 0) ≠ Ix.Kernel.projTableName T :=
    fun _ => Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  let κS := (Decl.ctorStage ⟨E, env, t, lim⟩
    ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps).κ
  have hused : ∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
      κS x = Core.keyOf t x ∧ Core.ProjPermitted κS x := by
    intro i hi x hx
    obtain ⟨ci, hci⟩ := hstored i hi x hx
    exact ctorStage_of_find (cvF := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩)
      hfresh hnt hci
  have hrecur : ∀ x ∈ L1.blockRecurAddrs B (#[.indc ind] : Array Ixon.MutConst).toList,
      κS x = Core.keyOf t x := by
    intro x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨m, hm, rfl⟩ := LoadedReads.blockRecurAddrs_get hk
    have hk0 : k = 0 := by
      cases k with
      | zero => rfl
      | succ k => simp at hm
    subst hk0
    have hmm : m = .indc ind := by simpa using hm.symm
    subst hmm
    rw [LoadedReads.memberAddr_indc]
    exact ctorStage_former (cvF := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩) rfl
  have hmem0 : (#[.indc ind] : Array Ixon.MutConst)[((0 : Nat).toUInt64).toNat]? =
      some (.indc ind) := by
    rw [h0]
    rfl
  -- a load at the former's projection record
  have formerLoad : ∀ {addr ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
      {a : Bytes.Address}, ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
      Core.Good ⟨E, env, t, lim⟩ cs → Bytes.RepAddressRef Core.addrTy h a addr →
      Core.keyOf t (Core.ixAddr a) = Core.keyOf t (Core.iprjAddr B 0) →
      Core.ixAddr a = Core.iprjAddr B 0 ∧
        Core.CIPtrRep κS h' ptr
          (.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps) := by
    intro addr ptr h h' cs a ev good ha hkey
    have hx : Core.ixAddr a = Core.iprjAddr B 0 := Core.keyOf_inj htwf hkey
    have hrec : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
      rw [hx]
      exact hproj
    obtain ⟨ty'', hcT, hrep⟩ := LoadedReads.get_ci_iprj_at (p := ⟨(0 : Nat).toUInt64, B⟩) ht
      good.1 good.2 ha ev hrec rfl hblock hmuts hmem0 hty hty_lbb hty_def
    rw [h0'] at hcT
    have e : ty'' = ty' := Option.some.inj (hcT.symm.trans hcanon)
    subst e
    have hr := hrep κS hused hrecur caps
    have hk : keyOf t (Core.ixAddr a) = Core.keyOf t (Core.iprjAddr B 0) := hkey
    rw [hk] at hr
    exact ⟨hx, hr⟩
  -- the block of a member load whose member key is the former's
  have memberBlock : ∀ {b : Bytes.Address} {i : F}, Core.HashedBlockAt E (Core.ixAddr b) →
      Core.keyOf t (Core.iprjAddr (Core.ixAddr b) (ZMod.val i)) =
        Core.keyOf t (Core.iprjAddr B 0) →
      Core.ixAddr b = B ∧ ZMod.val i = 0 :=
    fun hbh hkey => iprj_key_block htwf hdec hP hproj hbh (val_lt_uint64 _) hkey
  refine
    { getCI := ?_, getIprj := ?_, getCprj := ?_, inductRecord := ?_, inductBlock := ?_,
      unitLikeRaw := ?_ }
  · intro addr ptr h h' cs a ev good ha hkey
    exact (formerLoad ev good ha hkey).2
  · intro bp ptr i h h' cs b ev good hb hkey
    obtain ⟨hbB, hi0⟩ := memberBlock (L1.hashedBlockAt_of_get_ci_iprj good hb ev) hkey
    have hblock' : recordOf E (Core.ixAddr b) = some cb := by
      rw [hbB]
      exact hblock
    have hmem' : (#[.indc ind] : Array Ixon.MutConst)[i.val]? = some (.indc ind) := by
      show (#[.indc ind] : Array Ixon.MutConst)[ZMod.val i]? = some (.indc ind)
      rw [hi0]
      rfl
    have hty' : (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t (Core.ixAddr b) #[.indc ind])).read ind.typ = .ok ty₀ := by
      rw [hbB]
      exact hty
    obtain ⟨ty'', hcT, hrep⟩ := LoadedReads.get_ci_iprj_load_at ht good.1 good.2 hb ev hblock'
      hmuts hmem' hty' hty_lbb hty_def
    have hcT' : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ = some ty'' := by
      have hv : i.val = 0 := hi0
      rw [hv] at hcT
      exact hcT
    have e : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcanon)
    subst e
    have hrecur' : ∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) (#[.indc ind] : Array Ixon.MutConst).toList,
        κS x = Core.keyOf t x := by
      rw [hbB]
      exact hrecur
    have hr := hrep κS hused hrecur' caps
    have hk : Core.keyOf t (Core.iprjAddr (Core.ixAddr b) i.val) =
        Core.keyOf t (Core.iprjAddr B 0) := hkey
    rw [hk] at hr
    exact hr
  · intro bp ptr i j h h' cs b ev good hb hkey
    obtain ⟨hbB, hi0⟩ := memberBlock (L1.hashedBlockAt_of_get_ci_cprj good hb ev) hkey
    have hblock' : recordOf E (Core.ixAddr b) = some cb := by
      rw [hbB]
      exact hblock
    have hmem' : (#[.indc ind] : Array Ixon.MutConst)[i.val]? = some (.indc ind) := by
      show (#[.indc ind] : Array Ixon.MutConst)[ZMod.val i]? = some (.indc ind)
      rw [hi0]
      rfl
    have hctys' : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
        ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
          (exprReader t (fun x => E.blobs.get? x) cb id
            (blockSelf t (Core.ixAddr b) #[.indc ind])).read ct.typ = .ok cty ∧
          cty.looseBVarsBounded 0 = true ∧
          cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true := by
      rw [hbB]
      exact hctys
    have hrecur' : ∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) (#[.indc ind] : Array Ixon.MutConst).toList,
        κS x = Core.keyOf t x := by
      rw [hbB]
      exact hrecur
    obtain ⟨ct, ty'', -, hrep⟩ := LoadedReads.get_ci_cprj_load_at ht good.1 good.2 hb ev hblock'
      hmuts hmem' hctys'
    exact ⟨_, hrep κS hused hrecur'⟩
  · intro addr ptr h h' cs a nl ty np ni nc u blk idx ev good ha hkey hld
    have hx : Core.ixAddr a = Core.iprjAddr B 0 := Core.keyOf_inj htwf hkey
    obtain ⟨rawBytes, blkBytes, cm, cb', xs, ind', b, i, hhA, haA, hexA, -, hhB, haB, hexB, -,
      hbrep, hidx, -, hinfo, hcb, hxs⟩ := L1.inductRecord_raw_of_get_ci ev good.2 ha hld
    have hrecA : Ix.Cert.recordAt E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
      rw [hx]
      exact recordAt_of_recordOf hdec hproj
    have hcm : cm = memberProjection B 0 (.indc ind) := record_escape hdec good.1 hrecA hhA haA hexA
    subst hcm
    exact ⟨_, b, i, hrecA, hbrep, hidx, hinfo⟩
  · intro addr ptr h h' cs a b nl ty np ni nc u blk i ev good ha hkey hld hblk
    have hx : Core.ixAddr a = Core.iprjAddr B 0 := Core.keyOf_inj htwf hkey
    obtain ⟨rawBytes, blkBytes, cm, cb', xs, ind', b', i', hhA, haA, hexA, -, hhB, haB, hexB, -,
      hbrep, hidx, -, hinfo, hcb, hxs⟩ := L1.inductRecord_raw_of_get_ci ev good.2 ha hld
    have hbb : b = b' := Bytes.repAddressRef_inj U32.Goldilocks.compatible hblk hbrep
    subst hbb
    have hii : i = i' := Value.field.inj hidx
    subst hii
    have hrecA : Ix.Cert.recordAt E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
      rw [hx]
      exact recordAt_of_recordOf hdec hproj
    have hcm : cm = memberProjection B 0 (.indc ind) := record_escape hdec good.1 hrecA hhA haA hexA
    subst hcm
    have hinfo0 : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
    rw [hinfo0] at hinfo
    injection hinfo with hp
    injection hp with _ hbB
    have hrecB : Ix.Cert.recordAt E (Core.ixAddr b) = some cb := by
      rw [← hbB]
      exact recordAt_of_recordOf hdec hblock
    have hcbEq : cb' = cb := record_escape hdec good.1 hrecB hhB haB hexB
    subst hcbEq
    exact ⟨cb', xs, ind', hrecB, hcb, hxs⟩
  · intro ap ptr h h' cs a nl ty u blk p i b ev good ha hkey hld hb hfew hz hn
    obtain ⟨hx, -⟩ := formerLoad ev good ha hkey
    have hrecA : Ix.Cert.recordAt E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
      rw [hx]
      exact recordAt_of_recordOf hdec hproj
    have hdecA : ∀ lc, E.consts.get? (Core.ixAddr a) = some lc →
        Ixon.deConstantExact lc.rawBytes = .ok (memberProjection B 0 (.indc ind)) := by
      rw [hx]
      exact decoded_at_of_recordOf hproj
    obtain ⟨nl', ty'', u', blk', b', hld', hb', hbB', -, -⟩ :=
      L1.indRecord_of_deConstantExact (c := ⟨E, env, t, lim⟩) (p := ⟨(0 : Nat).toUInt64, B⟩)
        hdecA (decoded_at_of_recordOf hblock) ev good ha hrecA rfl
        (recordAt_of_recordOf hdec hblock) hmuts hmem0
    rw [hld'] at hld
    have same := Except.ok.inj hld
    simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at same
    obtain ⟨-, -, hpEq, hiEq, hcEq, -, hblkEq, hidxEq⟩ := same
    obtain ⟨hp56, hi56, hc56⟩ := hbounds
    have hindices : ind.indices.toNat = 0 :=
      Decl.nat_eq_of_field_eq_bounded (Nat.lt_trans hi56 (by decide)) (by decide) hiEq
    have hone : ind.ctors.size = 1 :=
      Decl.nat_eq_of_field_eq_bounded (Nat.lt_trans hc56 (by decide)) (by decide) hcEq
    have hpv : ind.params.toNat = ZMod.val p := by
      have fieldValues := congrArg ZMod.val (Value.field.inj hpEq)
      simpa only [ZMod.val_natCast_of_lt (Nat.lt_trans hp56 (by decide))] using fieldValues
    have hi0 : ZMod.val i = 0 := by
      have fieldValues := congrArg ZMod.val (Value.field.inj hidxEq)
      rw [h0'] at fieldValues
      simpa using fieldValues.symm
    rw [hblkEq] at hb'
    have hbb : b = b' := Bytes.repAddressRef_inj U32.Goldilocks.compatible hb hb'
    subst hbb
    have hblock' : recordOf E (Core.ixAddr b) = some cb := by
      rw [hbB']
      exact hblock
    obtain ⟨source⟩ := canonicalRecord_of_recordOf hdec hblock'
    have hsrc : source.value = cb := by
      have e := source.recordAt.symm.trans (recordAt_of_recordOf hdec hblock')
      exact Option.some.inj e
    have hshape : source.value.info = .muts #[.indc ind] := by
      rw [hsrc]
      exact hmuts
    have hmemAt : (#[.indc ind] : Array Ixon.MutConst).toList[ZMod.val i]? = some (.indc ind) := by
      rw [hi0]
      rfl
    obtain ⟨ctor, hctor, hzero⟩ :=
      Assembly.native_zero_field_metadata (context := Decl.ctorStage ⟨E, env, t, lim⟩
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps)
        source hshape hmemAt hz
    have hfields : ∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0 := by
      intro ct hct
      have hct' : ind.ctors.toList[0]? = some ct := by
        rw [Array.getElem?_toList]
        exact hct
      rw [hctor] at hct'
      cases hct'
      exact hzero
    obtain ⟨hu1, hu2⟩ := hunit hindices hone hfields
    exact ⟨hu1, hu2.trans hpv, .inl hfree⟩

/-! ## The constructor stage -/

/-- **The load contract of the constructor stage of a native block**, over a prefix that keeps
the invariant: the inputs of `formerLoads_of_block`, the freshness of the former's key, and the
store clause (`HashKeyed`, for the key of the former's marker). -/
theorem ctorStageLoads_of_block {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ()) {E : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat} (hinv : Decl.PrefixInv E t lim env)
    (hdec : L1.EnvDecoded E) (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hbounds : ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hctys : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
        cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb)
    {ty' : Ix.Kernel.Expr .anon}
    (hcanon : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ = some ty')
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {caps : Ix.Kernel.IndCaps .anon}
    (hunit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
      (∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0) →
      caps.unitlike = true ∧ caps.unitParams = ind.params.toNat)
    (hfree : Ix.Kernel.reservedBasisNames.contains (Core.keyOf t (Core.iprjAddr B 0)) = false) :
    Core.ScopedLoadFacts (Decl.ctorStage ⟨E, env, t, lim⟩
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ caps) :=
  hinv.ctorStageLoads (f := Core.iprjAddr B 0) rfl hfresh (hkeys.marker_none _)
    (fun _ => Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _))
    (formerLoads_of_block ht hdec hP hblock hmuts hproj hbounds hty hty_lbb hty_def hctys hstored
      hcanon hfresh hunit hfree)

/-- **The scoped core facts of the constructor stage**: its environment facts (the prefix's, with
the former stored at the native capability record, `Decl.coreEnvFacts_consNativeCapsAt`) and its
load contract. The former's type is closed, well scoped, its constants resolve in the prefix, and
it is a telescope of the parameters and indices: the former stage's outputs. -/
theorem ctorStageCoreFacts_of_block {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {E : Ixon.Env} {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    (hinv : Decl.PrefixInv E t lim env)
    (hdec : L1.EnvDecoded E) (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hbounds : ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hctys : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
        cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb)
    {ty' : Ix.Kernel.Expr .anon}
    (hcanon : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀ = some ty')
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {p : Ix.Kernel.InductiveShape .anon} {isRec : Bool}
    (hunit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
      (∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0) →
      (Ix.Kernel.nativeCapsAt p isRec).unitlike = true ∧
        (Ix.Kernel.nativeCapsAt p isRec).unitParams = ind.params.toNat)
    (hfree : Ix.Kernel.reservedBasisNames.contains (Core.keyOf t (Core.iprjAddr B 0)) = false)
    (htype : ty'.hasFvar = false ∧ ty'.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
      ty'.constsResolve env = true ∧ ty'.looseBVarsBounded 0 = true)
    {binders : List (Core.KExpr × Ix.Kernel.BinderMeta)} {body : Core.KExpr}
    (htele : ty'.stripPis (p.nP + p.nIdx) = some (binders, body)) :
    Core.ScopedCoreFacts (Decl.ctorStage ⟨E, env, t, lim⟩
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
      (Ix.Kernel.nativeCapsAt p isRec)) :=
  ⟨Decl.coreEnvFacts_consNativeCapsAt (c := ⟨E, env, t, lim⟩)
      (cv := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩)
      hinv.scopedCoreFacts.1 hfresh
      (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) htype htele,
    ctorStageLoads_of_block ht hinv hdec hP hkeys hblock hmuts hproj hbounds hty hty_lbb hty_def
      hctys hstored hcanon hfresh hunit hfree⟩

end IxVM.Refinement.Typing
