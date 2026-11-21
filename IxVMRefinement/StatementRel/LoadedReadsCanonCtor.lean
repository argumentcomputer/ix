import IxVMRefinement.StatementRel.LoadedReadsCanonInd

/-! # The canonical annotated constant of a constructor, and its reloads

The analogue of `LoadedReadsCanonInd` for a constructor-projection record: constructor `j`
(`ct`) of inductive member `k` (`ind`) of a block record `cb`. Its reading is the kernel
reader's conversion `ty₀` of its type in the block (`CtorReads`). The circuit converts the type
at root `mutsRootOffset ms k + 1 + j` (`Ingress::get_ci_cprj`), so the stored constant is the
canonical annotation of `ty₀` at that root, with the record's parameter and field counts.

* `canonCtor key cb base ct ty₀`: the constructor under the key `key`, with the canonical
  annotation of `ty₀` at root `base` and the counts of `ct`. A function of the block record,
  the root (of the member and constructor indices) and the reading.
* `ctor_value_canon`: the pure step from a traced conversion to the representation. The
  heap value names the constructor by its stored index (`ct.cidx`); the reading names it by its
  position `j`, so the step takes `ct.cidx.toNat = j` (as `ctor_reading` and `Reads` do).
* `get_ci_cprj_canon` (a `get_ci` at the constructor's projection record) and
  `get_ci_cprj_load_canon` (a direct `Ingress::get_ci_cprj` on the block and the two indices,
  the way the checker reaches constructors): every load in calls with no hashed collision with
  the store represents the canonical constant.
* `reloadsAs_ctor`, `reloadsAs_ctor_cons`: `Decl.ReloadsAs` for the canonical constant.
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

private theorem toUInt64_toNat_k {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- **The canonical annotated constant of a constructor**: the constructor under the key
`key`, with the canonical annotation of its read type `ty₀` at root `base` in the block record
`cb` (constructor `j` of member `k`: `base = mutsRootOffset ms.toList k + 1 + j`), and the
record's parameter and field counts. -/
noncomputable def canonCtor (key : Ix.Kernel.Key .anon) (cb : Ixon.Constant) (base : F)
    (ct : Ixon.Constructor) (ty₀ : Ix.Kernel.Expr .anon) :
    Option (Ix.Kernel.ConstantInfo .anon) :=
  (canonAnn cb (List.range ct.lvls.toNat) base ct.typ ty₀).map fun ty' =>
    .ctorInfo ⟨key, List.range ct.lvls.toNat, ty'⟩ ct.params.toNat ct.fields.toNat

theorem canonCtor_eq {key : Ix.Kernel.Key .anon} {cb : Ixon.Constant} {base : F}
    {ct : Ixon.Constructor} {ty₀ ty' : Ix.Kernel.Expr .anon}
    (hT : canonAnn cb (List.range ct.lvls.toNat) base ct.typ ty₀ = some ty') :
    canonCtor key cb base ct ty₀ =
      some (.ctorInfo ⟨key, List.range ct.lvls.toNat, ty'⟩ ct.params.toNat ct.fields.toNat) := by
  unfold canonCtor
  rw [hT]
  rfl

theorem canonCtor_inv {key : Ix.Kernel.Key .anon} {cb : Ixon.Constant} {base : F}
    {ct : Ixon.Constructor} {ty₀ : Ix.Kernel.Expr .anon} {cn : Ix.Kernel.ConstantInfo .anon}
    (h : canonCtor key cb base ct ty₀ = some cn) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ct.lvls.toNat) base ct.typ ty₀ = some ty' ∧
      cn = .ctorInfo ⟨key, List.range ct.lvls.toNat, ty'⟩ ct.params.toNat ct.fields.toNat := by
  unfold canonCtor at h
  cases hT : canonAnn cb (List.range ct.lvls.toNat) base ct.typ ty₀ with
  | none =>
    rw [hT] at h
    have h' : (none : Option (Ix.Kernel.ConstantInfo .anon)) = some cn := h
    cases h'
  | some ty' =>
    rw [hT] at h
    have h' : some (Ix.Kernel.ConstantInfo.ctorInfo ⟨key, List.range ct.lvls.toNat, ty'⟩
        ct.params.toNat ct.fields.toNat) = some cn := h
    exact ⟨ty', rfl, (Option.some.inj h').symm⟩

section Ctor

variable {t : Ix.Kernel.RoleTable}

/-- **A traced conversion of a constructor represents its canonical constant.** Constructor
`ct` of the inductive member `k` (`ind`) of the block record `cb` (members `ms`, at `B`), whose
stored index is `j`, was converted in the tree of the block's binder blocks at the root
`mutsRootOffset ms k + 1 + j`, with the plan on the heap; its type reads as `ty₀` (well scoped);
the literal bytes the conversion hashed agree with the reading's blobs. Then the canonical
annotation is defined, annotates the reading, and the value represents the constructor with
that type and the record's counts: under the table's keying, and under the keying of any prefix
that stores the references the block uses, the block's members and the constructor's key. -/
theorem ctor_value_canon (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
    {B : _root_.Address} {k j : Nat} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    {ind : Ixon.Inductive} {ct : Ixon.Constructor} (hmuts : cb.info = .muts ms)
    (hmem : ms[k]? = some (.indc ind)) (hctm : ct ∈ ind.ctors.toList) (hcidx : ct.cidx.toNat = j)
    {blobs : List (_root_.Address × ByteArray)}
    (hagree : Ingress.BlobReadAgreement (readCtx t blob).blob blobs)
    {tree : Ingress.BinderTreeData}
    (built : Ingress.BinderTreeBuilt (Ingress.binderLeavesData cb.binders.toList) tree)
    {plan : List Core.KLevel}
    (planned : Ingress.binderRootPlan tree cb.sharing.toList
      (((Ingress.mutsRootOffset ms.toList k : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ = some plan)
    {h : Heap F} {v : SourceValue F}
    (raw : Ingress.RawCtorValRep cb.refs.toList (Ingress.blockRecurAddrs B ms.toList) cb.univs.toList
      cb.sharing.toList blobs h ct B k v)
    (levels : Ingress.CITypeBinderLevels "Ctor" h v plan)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t blob cb id (blockSelf t B ms)).read ct.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ct.lvls.toNat)
        (((Ingress.mutsRootOffset ms.toList k : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ ty₀ =
        some ty' ∧ Annotates ty' ty₀ ∧
      Core.CIRep (Core.keyOf t) h v
        (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B k j), List.range ct.lvls.toNat, ty'⟩
          ct.params.toNat ct.fields.toNat) ∧
      (∀ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon) (lim : Option Nat),
        Decl.UsedRefsStored t env cb → BlockStored t env B ms →
        (∃ ci, env.find? (Core.keyOf t (Core.cprjAddr B k j)) = some ci) →
          Core.CIRep (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ h v
            (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr B k j), List.range ct.lvls.toNat, ty'⟩
              ct.params.toNat ct.fields.toNat)) := by
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
  have hkey : ∀ κ : _root_.Address → Core.KKey,
      κ (Core.cprjAddr B k j) = Core.keyOf t (Core.cprjAddr B k j) →
      ∃ (b' : Aiur.Library.Bytes.Address) (i j' : F),
        Aiur.Library.Bytes.RepAddressRef Core.addrTy h b' blkPtr ∧
        (Value.field ((k : Nat) : F) : SourceValue F) = .field i ∧
        (Value.field ((ct.cidx.toNat : Nat) : F) : SourceValue F) = .field j' ∧
        Core.keyOf t (Core.cprjAddr B k j) =
          κ (Core.cprjAddr (Core.ixAddr b') (ZMod.val i) (ZMod.val j')) := by
    intro κ hκ
    refine ⟨b, ((k : Nat) : F), ((ct.cidx.toNat : Nat) : F), hb_rep, rfl, rfl, ?_⟩
    rw [hb_eq, Ingress.val_cast_u56_ing hidx56, Ingress.val_cast_u56_ing hcidx56, hcidx, hκ]
  refine ⟨ty', hcT, hannT, ?_, fun E₀ env lim hstored hblk hself => ?_⟩
  · exact .ctor (valRep_range hlvls htmT) rfl rfl ⟨hp56, hf56⟩ (hkey (Core.keyOf t) rfl)
  · have hmem' : Ixon.MutConst.indc ind ∈ ms.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
    have heT : ∀ i, i ∈ exprRefIdxs ct.typ → i ∈ usedRefIdxs cb := by
      intro i hi
      unfold usedRefIdxs
      rw [hmuts]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.indc ind, hmem', by
          unfold mutRefIdxs
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ct, hctm, hi⟩)⟩)
    have hκ : (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (Core.cprjAddr B k j) =
        Core.keyOf t (Core.cprjAddr B k j) := by
      obtain ⟨ci, hci⟩ := hself
      exact Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
    exact .ctor (valRep_range hlvls (tmC_stored_of_used rty heT hstored hblk htmT)) rfl rfl
      ⟨hp56, hf56⟩ (hkey _ hκ)

/-- **Every load of a held constructor-projection record represents its canonical
constant.** The store `E` holds the record `c` at the address and the block `cb` at the block
address it names (exact decodings); the member is the inductive `ind`, its constructor at the
record's constructor index is `ct`, whose stored index is that position; `ty₀` is the reading of
its type in the block over `E`'s blobs, well scoped. Then for a `get_ci` at the address in
bounded calls that hash no collision with `E`, the address is the constructor's constant
address, the canonical annotation is defined, and the returned pointer represents the canonical
constant: under the table's keying, and under the keying of any prefix that stores the
references the block uses, the block's members and the constructor's key. -/
theorem get_ci_cprj_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {a : Aiur.Library.Bytes.Address} {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c cb : Ixon.Constant}
    {p : Ixon.ConstructorProj} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    {ct : Ixon.Constructor}
    (hrec : recordOf E (Core.ixAddr a) = some c) (hinfo : c.info = .cPrj p)
    (hblock : recordOf E p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.indc ind)) (hct : ind.ctors[p.cidx.toNat]? = some ct)
    (hcidx : ct.cidx.toNat = p.cidx.toNat) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t p.block ms)).read ct.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    Core.ixAddr a = ctorAddr p.block p.idx.toNat p.cidx.toNat ∧
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ct.lvls.toNat)
        (((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1 + ((p.cidx.toNat : Nat) : F))
        ct.typ ty₀ = some ty' ∧
      Annotates ty' ty₀ ∧
      Core.CIPtrRep (Core.keyOf t) h' ptr
        (.ctorInfo ⟨keyOf t (Core.ixAddr a), List.range ct.lvls.toNat, ty'⟩ ct.params.toNat
          ct.fields.toNat) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env cb →
        BlockStored t env p.block ms →
        (∃ ci, env.find? (keyOf t (Core.ixAddr a)) = some ci) →
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (.ctorInfo ⟨keyOf t (Core.ixAddr a), List.range ct.lvls.toNat, ty'⟩ ct.params.toNat
              ct.fields.toNat)) := by
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := Ingress.get_ci_block_trace_spec hbound ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  have haddr' : Core.ixAddr a = ctorAddr p.block p.idx.toNat p.cidx.toNat :=
    haddr.symm.trans (cprj_canonical hex htv hinfo).2
  have hkey : keyOf t (Core.ixAddr a) =
      Core.keyOf t (Core.cprjAddr p.block p.idx.toNat p.cidx.toNat) := by
    rw [haddr', ctorAddr_eq_cprjAddr, keyOf_eq]
  unfold Ingress.GetCIBlockTraceResult at hres
  rw [hinfo] at hres
  obtain ⟨hidx, hcidx56, blkBytes, cb', ms', ind', ct', blobs, tree, plan, v, hhB, haB, hexB,
    hcb, hms, hcts, hhp, built, planned, hld, hraw, hlev⟩ := hres
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
  have hct' : ind.ctors.toList[p.cidx.toNat]? = some ct := by
    rw [Array.getElem?_toList]
    exact hct
  have hcEq : ct = ct' := Option.some.inj (hct'.symm.trans hcts)
  subst hcEq
  have hctm : ct ∈ ind.ctors.toList := List.mem_of_getElem? hct'
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, hrepT, hrepS⟩ :=
    ctor_value_canon ht hmuts hmem hctm hcidx hagree built planned hraw hlev hty hty_lbb hty_def
  rw [hkey]
  exact ⟨haddr', ty', hcT, hannT, ⟨_, hld, hrepT⟩,
    fun env lim hstored hblk hself => ⟨_, hld, hrepS E env lim hstored hblk hself⟩⟩

/-- **Every direct load of a constructor represents its canonical constant**: a
`Ingress::get_ci_cprj` on the block at `ixAddr b`, the member index `i` and the constructor
index `j` (how the checker reaches a constructor), in bounded calls that hash no collision with
a store `E` holding the block (exact decoding), where member `i` is the inductive `ind`, its
constructor `j` is `ct` with stored index `j`, and `ct`'s type reads as `ty₀` over `E`'s blobs,
well scoped. -/
theorem get_ci_cprj_load_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {b : Aiur.Library.Bytes.Address} {blkArg ptr : SourceValue F} {i j : F} {h h' : Heap F}
    (hb : Aiur.Library.Bytes.RepAddressRef Core.addrTy h b blkArg)
    (ev : ObsFn Core.W "Ingress::get_ci_cprj" [blkArg, .field i, .field j] h ptr h' cs)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    {ct : Ixon.Constructor}
    (hblock : recordOf E (Core.ixAddr b) = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i.val]? = some (.indc ind)) (hct : ind.ctors[j.val]? = some ct)
    (hcidx : ct.cidx.toNat = j.val) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ct.lvls.toNat)
        (((Ingress.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + ((j.val : Nat) : F))
        ct.typ ty₀ = some ty' ∧
      Annotates ty' ty₀ ∧
      Core.CIPtrRep (Core.keyOf t) h' ptr
        (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr (Core.ixAddr b) i.val j.val),
          List.range ct.lvls.toNat, ty'⟩ ct.params.toNat ct.fields.toNat) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env cb →
        BlockStored t env (Core.ixAddr b) ms →
        (∃ ci, env.find? (Core.keyOf t (Core.cprjAddr (Core.ixAddr b) i.val j.val)) = some ci) →
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (.ctorInfo ⟨Core.keyOf t (Core.cprjAddr (Core.ixAddr b) i.val j.val),
              List.range ct.lvls.toNat, ty'⟩ ct.params.toNat ct.fields.toNat)) := by
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    hhp, hld, hraw, tree, plan, built, planned, hlev⟩ := Ingress.get_ci_cprj_origin_spec hbound hb ev
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
  have hct' : ind.ctors.toList[j.val]? = some ct := by
    rw [Array.getElem?_toList]
    exact hct
  have hcEq : ct = ct' := Option.some.inj (hct'.symm.trans hcts)
  subst hcEq
  have hctm : ct ∈ ind.ctors.toList := List.mem_of_getElem? hct'
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, hrepT, hrepS⟩ :=
    ctor_value_canon ht hmuts hmem hctm hcidx hagree built planned hraw hlev hty hty_lbb hty_def
  exact ⟨ty', hcT, hannT, ⟨_, hld, hrepT⟩,
    fun env lim hstored hblk hself => ⟨_, hld, hrepS E env lim hstored hblk hself⟩⟩

/-- **The canonical constant of a constructor reloads** at every store `E'` that holds the
constructor's projection record `c` at `a` and the block `cb` at the block address it names
(exact decodings), and over whose blobs the constructor's type reads as `ty₀`, under the keying
of any prefix `env` that stores the references the block uses, the block's members and the
constructor's key. -/
theorem reloadsAs_ctor (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c cb : Ixon.Constant} {p : Ixon.ConstructorProj}
    {ms : Array Ixon.MutConst} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .cPrj p)
    (hblock : recordOf E' p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.indc ind)) (hct : ind.ctors[p.cidx.toNat]? = some ct)
    (hcidx : ct.cidx.toNat = p.cidx.toNat) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) cb id
      (blockSelf t p.block ms)).read ct.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb) (hblk : BlockStored t env p.block ms)
    (hself : ∃ ci, env.find? (Core.keyOf t a) = some ci)
    {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonCtor (keyOf t a) cb
      (((Ingress.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1 + ((p.cidx.toNat : Nat) : F))
      ct ty₀ = some cn) :
    Decl.ReloadsAs E' t env cn := by
  obtain ⟨ty', hcT, hcn'⟩ := canonCtor_inv hcn
  subst hcn'
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a := hkey
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk
  subst haddr
  obtain ⟨-, ty'', hcT', -, -, hrep⟩ :=
    get_ci_cprj_canon ht hgood.1 hgood.2 ha ev hrec hinfo hblock hmuts hmem hct hcidx hty
      hty_lbb hty_def
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  subst e1
  exact hrep env none hstored hblk hself

/-- **The reload a step needs, for constructor `j` of inductive member `k` of the block at
`B`**: the canonical constant reloads under the keying of the prefix that stores it, where the
prefix before it stores the references the block uses and the block's members, at every store
`E'` that holds the constructor's projection record at its constant address, the block at `B`,
and at least the blobs of a store `E` over which the constructor's type reads as `ty₀`. -/
theorem reloadsAs_ctor_cons (ht : t.check = .ok ()) {E E' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {k j : Nat} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hk64 : k < UInt64.size) (hj64 : j < UInt64.size)
    (hproj : recordOf E' (ctorAddr B k j) = some (constructorProjection B k j))
    (hblock : recordOf E' B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[k]? = some (.indc ind)) (hct : ind.ctors[j]? = some ct)
    (hcidx : ct.cidx.toNat = j)
    (hblobs : ∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read ct.typ =
      .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb) (hblk : BlockStored t env B ms)
    {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonCtor (keyOf t (ctorAddr B k j)) cb
      (((Ingress.mutsRootOffset ms.toList k : Nat) : F) + 1 + ((j : Nat) : F)) ct ty₀ = some cn) :
    Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  have hkk : k.toUInt64.toNat = k := toUInt64_toNat_k hk64
  have hjj : j.toUInt64.toNat = j := toUInt64_toNat_k hj64
  have hinfo : (constructorProjection B k j).info = .cPrj ⟨k.toUInt64, j.toUInt64, B⟩ := rfl
  have hmem' : ms[(⟨k.toUInt64, j.toUInt64, B⟩ : Ixon.ConstructorProj).idx.toNat]? =
      some (.indc ind) := by
    show ms[k.toUInt64.toNat]? = some (.indc ind)
    rw [hkk]
    exact hmem
  have hct' : ind.ctors[(⟨k.toUInt64, j.toUInt64, B⟩ : Ixon.ConstructorProj).cidx.toNat]? =
      some ct := by
    show ind.ctors[j.toUInt64.toNat]? = some ct
    rw [hjj]
    exact hct
  have hcidx' : ct.cidx.toNat = (⟨k.toUInt64, j.toUInt64, B⟩ : Ixon.ConstructorProj).cidx.toNat := by
    show ct.cidx.toNat = j.toUInt64.toNat
    rw [hjj]
    exact hcidx
  have hcn' : canonCtor (keyOf t (ctorAddr B k j)) cb
      (((Ingress.mutsRootOffset ms.toList
        (⟨k.toUInt64, j.toUInt64, B⟩ : Ixon.ConstructorProj).idx.toNat : Nat) : F) + 1 +
        (((⟨k.toUInt64, j.toUInt64, B⟩ : Ixon.ConstructorProj).cidx.toNat : Nat) : F))
      ct ty₀ = some cn := by
    show canonCtor (keyOf t (ctorAddr B k j)) cb
      (((Ingress.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) + 1 +
        ((j.toUInt64.toNat : Nat) : F)) ct ty₀ = some cn
    rw [hkk, hjj]
    exact hcn
  have hname : cn.name = Core.keyOf t (ctorAddr B k j) := by
    obtain ⟨ty', -, hcneq⟩ := canonCtor_inv hcn
    subst hcneq
    rfl
  exact reloadsAs_ctor (p := ⟨k.toUInt64, j.toUInt64, B⟩) ht hproj hinfo hblock hmuts hmem' hct'
    hcidx'
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hty)
    hty_lbb hty_def (usedRefsStored_cons cn hstored) (blockStored_cons cn hblk)
    ⟨cn, by rw [Ix.Kernel.Env.find?_cons, ite_eq_left hname]⟩ hcn'

end Ctor

end IxVM.Refinement.LoadedReads
