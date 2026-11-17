import IxVMRefinement.StatementRel.LoadedReadsCanon
import IxVMRefinement.StatementRel.LoadedReadsBlockTrace

/-! # The canonical annotated constant of an inductive type, and its reloads

The analogue of `LoadedReadsCanon` for an inductive-projection record: member `k` of a block
record `cb` is an inductive type `ind`; its reading is the kernel reader's conversion `ty₀` of
its type in the block (`IndReads`). The circuit converts the type at the member's root offset
in the block (`Ingress::get_ci_iprj`), so the stored constant is the canonical annotation of
`ty₀` at that root, a function of the block record, the member's root and the reading.

* `canonAnn_gen`: `annotation_canon` for any level parameters and any table of `recur`
  addresses whose reading keys are the table's.
* `BlockStored t env B ms`: the key of every member of the block at `B` is stored in `env`.
  A member of an inductive block is converted with the block's member addresses as its
  `recur` addresses (`L1.blockRecurAddrs`); under the keying of a prefix those cells resolve
  only where the members are stored. A definition member has none (a safe definition is
  converted with no `recur` address), so the definition case has no such hypothesis.
* `canonInd key cb base ind ty₀ caps`: the inductive type under the key `key`, with the
  canonical annotation of `ty₀` at root `base`, and the capability record `caps` (free: the
  kernel computes it, and neither `StoredAs` nor the loaded value constrains it).
* `ind_value_canon`: the pure step from a traced conversion to the representation.
* `get_ci_iprj_canon` (a `get_ci` at the projection record's address) and
  `get_ci_iprj_load_canon` (a direct `Ingress::get_ci_iprj` on the block and index): every load
  in calls with no hashed collision with the store represents the canonical constant, under the
  table's keying and under the keying of a prefix that stores the references the block uses
  and the block's members.
* `reloadsAs_ind`, `reloadsAs_ind_cons`: `Decl.ReloadsAs` for the canonical constant.
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

private theorem toUInt64_toNat_i {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-! ## The canonical annotation, for any level parameters and `recur` table -/

/-- **A converted root represents the canonical annotation of its reading**, as
`annotation_canon`, for level parameters `ps` (some order of the positions) and a table of
`recur` addresses whose reading keys are the table's keys of those addresses. -/
theorem annotation_canon_gen {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {ps : List Ix.Kernel.LevelParam}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {E_rd : Ix.Kernel.Expr .anon} {root : F} {tree : L1.BinderTreeData}
    {plan : List Core.KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hps : ps.length < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hread : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read e = .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined ps = true) :
    ∃ E' : Ix.Kernel.Expr .anon,
      canonAnn src ps root e E_rd = some E' ∧ Annotates E' E_rd ∧
      Core.TmC (Core.keyOf t) h (Core.posOf ps E') kp := by
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam ps) self).read e = .ok E_rd := hread
  obtain ⟨E', hann, htm, htrace⟩ :=
    raw.toTmCExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := ps) hperm hps
      (readCtx_keyAt_inv ht blob) hselfk hagree hread' hlbb hdef
  have hap := htrace plan levels []
  rw [List.append_nil] at hap
  refine ⟨E', ?_, hann, htm.toTmC⟩
  unfold canonAnn
  rw [canonTree_eq built, planned]
  show (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel ps level))
    E_rd plan).map Prod.fst = some E'
  rw [hap]
  rfl

/-- `annotation_canon_gen` at the level parameters `List.range n`, read with the identity. -/
theorem annotation_canon_range {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {n : Nat}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {E_rd : Ix.Kernel.Expr .anon} {root : F} {tree : L1.BinderTreeData}
    {plan : List Core.KLevel}
    (hn : n < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hread : (exprReader t blob src id self).read e = .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined (List.range n) = true) :
    ∃ E' : Ix.Kernel.Expr .anon,
      canonAnn src (List.range n) root e E_rd = some E' ∧ Annotates E' E_rd ∧
      Core.TmC (Core.keyOf t) h (Core.posOf (List.range n) E') kp := by
  have hread' : (exprReader t blob src (Ix.Kernel.Reader.recParam (List.range n)) self).read e =
      .ok E_rd := by
    rw [Assembly.recParam_range]
    exact hread
  exact annotation_canon_gen ht (by simp) (by simpa using hn) hselfk hagree raw built planned
    levels hread' hlbb hdef

/-! ## The members of a block, stored -/

/-- **The members of the block at `B` are stored in `env`**: the key of every member's
constant address (the circuit's table of the block's `recur` addresses) has a constant. -/
def BlockStored (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon) (B : _root_.Address)
    (ms : Array Ixon.MutConst) : Prop :=
  ∀ x ∈ L1.blockRecurAddrs B ms.toList, ∃ ci, env.find? (Core.keyOf t x) = some ci

/-- A member's constant address is in the block's table of `recur` addresses. -/
theorem memberAddr_mem_blockRecurAddrs {B : _root_.Address} {ms : Array Ixon.MutConst}
    {k : Nat} {m : Ixon.MutConst} (hm : ms[k]? = some m) :
    memberAddr B k m ∈ L1.blockRecurAddrs B ms.toList := by
  have h1 : ms.toList[k]? = some m := by
    rw [Array.getElem?_toList]
    exact hm
  have h2 : (L1.blockRecurAddrs B ms.toList)[k]? = some (memberAddr B k m) := by
    rw [L1.blockRecurAddrs_eq_mapIdx, List.getElem?_mapIdx, h1, memberAddr_eq_projAddr]
    rfl
  exact List.mem_of_getElem? h2

/-- `BlockStored` in terms of the members: the key of every member's constant address is
stored. -/
theorem blockStored_of_members {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {B : _root_.Address} {ms : Array Ixon.MutConst}
    (h : ∀ k m, ms[k]? = some m → ∃ ci, env.find? (Core.keyOf t (memberAddr B k m)) = some ci) :
    BlockStored t env B ms := by
  intro x hx
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
  obtain ⟨m, hm, rfl⟩ := blockRecurAddrs_get hk
  exact h k m hm

/-- The members stay stored when one more constant is stored. -/
theorem blockStored_cons {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {B : _root_.Address} {ms : Array Ixon.MutConst} (cn : Ix.Kernel.ConstantInfo .anon)
    (h : BlockStored t env B ms) : BlockStored t ⟨cn :: env.consts⟩ B ms := by
  intro x hx
  obtain ⟨ci, hci⟩ := h x hx
  by_cases hk : cn.name = Core.keyOf t x
  · exact ⟨cn, by rw [Ix.Kernel.Env.find?_cons, ite_eq_left hk]⟩
  · exact ⟨ci, by rw [Ix.Kernel.Env.find?_cons, ite_eq_right hk]; exact hci⟩

/-- **Storing member `k` after the others stores the block**: where `env` stores every other
member of the block and `cn` is at member `k`'s key. For a block of one member the first
condition is empty. -/
theorem blockStored_cons_member {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon}
    {B : _root_.Address} {ms : Array Ixon.MutConst} {k : Nat} {m₀ : Ixon.MutConst}
    {cn : Ix.Kernel.ConstantInfo .anon} (hm₀ : ms[k]? = some m₀)
    (hname : cn.name = Core.keyOf t (memberAddr B k m₀))
    (hothers : ∀ j m, ms[j]? = some m → j ≠ k →
      ∃ ci, env.find? (Core.keyOf t (memberAddr B j m)) = some ci) :
    BlockStored t ⟨cn :: env.consts⟩ B ms := by
  apply blockStored_of_members
  intro j m hm
  by_cases hjk : j = k
  · subst hjk
    have hmm : m = m₀ := Option.some.inj (hm.symm.trans hm₀)
    subst hmm
    exact ⟨cn, by rw [Ix.Kernel.Env.find?_cons, ite_eq_left hname]⟩
  · obtain ⟨ci, hci⟩ := hothers j m hm hjk
    by_cases hc : cn.name = Core.keyOf t (memberAddr B j m)
    · exact ⟨cn, by rw [Ix.Kernel.Env.find?_cons, ite_eq_left hc]⟩
    · exact ⟨ci, by rw [Ix.Kernel.Env.find?_cons, ite_eq_right hc]; exact hci⟩

/-- **A converted term of a record is represented under the keying of a prefix** that stores
the references the record uses and every `recur` address of the conversion. -/
theorem tmC_stored_of_used {E₀ : Ixon.Env} {t : Ix.Kernel.RoleTable}
    {env : Ix.Kernel.Env .anon} {lim : Option Nat} {c : Ixon.Constant}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap F} {bound : Nat} {e : Ixon.Expr} {p : SourceValue F} {X : Core.KExpr}
    (raw : L1.RawConvExpr c.refs.toList recurAddrs c.univs.toList c.sharing.toList blobs h
      bound e p)
    (he : ∀ i, i ∈ exprRefIdxs e → i ∈ usedRefIdxs c)
    (hstored : Decl.UsedRefsStored t env c)
    (hrecur : ∀ x ∈ recurAddrs, ∃ ci, env.find? (Core.keyOf t x) = some ci)
    (rep : Core.TmC (Core.keyOf t) h X p) :
    Core.TmC (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ h X p := by
  have used : ∀ x, L1.RefUsed c.refs.toList c.sharing.toList e x →
      ∃ ci, env.find? (Core.keyOf t x) = some ci := by
    intro x hu
    obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
    · exact hstored i (he i hi) x hr
    · have hmem : i ∈ usedRefIdxs c := by
        unfold usedRefIdxs
        exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
      exact hstored i hmem x hr
  refine raw.tmC_rekey rep (fun x hu => ?_) (fun x hu => ?_)
  · rcases hu with hu | hr
    · obtain ⟨ci, hci⟩ := used x hu
      exact Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
    · obtain ⟨ci, hci⟩ := hrecur x hr
      exact Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
  · obtain ⟨ci, hci⟩ := used x hu
    exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E₀, env, t, lim⟩) hci

/-! ## The canonical inductive type -/

/-- **The canonical annotated constant of an inductive member**: the inductive type under the
key `key`, with the canonical annotation of its read type `ty₀` at root `base` in the block
record `cb` (member `k` of a block with members `ms`: `base = mutsRootOffset ms.toList k`),
and the capability record `caps`. -/
noncomputable def canonInd (key : Ix.Kernel.Key .anon) (cb : Ixon.Constant) (base : F)
    (ind : Ixon.Inductive) (ty₀ : Ix.Kernel.Expr .anon) (caps : Ix.Kernel.IndCaps .anon) :
    Option (Ix.Kernel.ConstantInfo .anon) :=
  (canonAnn cb (List.range ind.lvls.toNat) base ind.typ ty₀).map fun ty' =>
    .indInfo ⟨key, List.range ind.lvls.toNat, ty'⟩ caps

theorem canonInd_eq {key : Ix.Kernel.Key .anon} {cb : Ixon.Constant} {base : F}
    {ind : Ixon.Inductive} {ty₀ ty' : Ix.Kernel.Expr .anon} {caps : Ix.Kernel.IndCaps .anon}
    (hT : canonAnn cb (List.range ind.lvls.toNat) base ind.typ ty₀ = some ty') :
    canonInd key cb base ind ty₀ caps =
      some (.indInfo ⟨key, List.range ind.lvls.toNat, ty'⟩ caps) := by
  unfold canonInd
  rw [hT]
  rfl

theorem canonInd_inv {key : Ix.Kernel.Key .anon} {cb : Ixon.Constant} {base : F}
    {ind : Ixon.Inductive} {ty₀ : Ix.Kernel.Expr .anon} {caps : Ix.Kernel.IndCaps .anon}
    {cn : Ix.Kernel.ConstantInfo .anon} (h : canonInd key cb base ind ty₀ caps = some cn) :
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ind.lvls.toNat) base ind.typ ty₀ = some ty' ∧
      cn = .indInfo ⟨key, List.range ind.lvls.toNat, ty'⟩ caps := by
  unfold canonInd at h
  cases hT : canonAnn cb (List.range ind.lvls.toNat) base ind.typ ty₀ with
  | none =>
    rw [hT] at h
    have h' : (none : Option (Ix.Kernel.ConstantInfo .anon)) = some cn := h
    cases h'
  | some ty' =>
    rw [hT] at h
    have h' : some (Ix.Kernel.ConstantInfo.indInfo ⟨key, List.range ind.lvls.toNat, ty'⟩ caps) =
        some cn := h
    exact ⟨ty', rfl, (Option.some.inj h').symm⟩

section Ind

variable {t : Ix.Kernel.RoleTable}

/-- **A traced conversion of an inductive member represents its canonical constant.** The
member `k` (`ind`) of the block record `cb` (members `ms`, at `B`) was converted in the tree
of the block's binder blocks at the member's root offset, with the plan on the heap; its type
reads as `ty₀` (well scoped); the literal bytes the conversion hashed agree with the reading's
blobs. Then the canonical annotation is defined, annotates the reading, and the value
represents the inductive with that type under every capability record: under the table's
keying, and under the keying of any prefix that stores the references the block uses and the
block's members. -/
theorem ind_value_canon (ht : t.check = .ok ()) {blob : _root_.Address → Option ByteArray}
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
      (∀ caps : Ix.Kernel.IndCaps .anon, Core.CIRep (Core.keyOf t) h v
        (.indInfo ⟨Core.keyOf t (Core.iprjAddr B k), List.range ind.lvls.toNat, ty'⟩ caps)) ∧
      (∀ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon) (lim : Option Nat),
        Decl.UsedRefsStored t env cb → BlockStored t env B ms →
        ∀ caps : Ix.Kernel.IndCaps .anon,
          Core.CIRep (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ h v
            (.indInfo ⟨Core.keyOf t (Core.iprjAddr B k), List.range ind.lvls.toNat, ty'⟩
              caps)) := by
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
  have hkey : ∀ κ : _root_.Address → Core.KKey,
      κ (Core.iprjAddr B k) = Core.keyOf t (Core.iprjAddr B k) →
      ∃ (b' : Aiur.Library.Bytes.Address) (i : F),
        Aiur.Library.Bytes.RepAddressRef Core.addrTy h b' blkPtr ∧
        (Value.field ((k : Nat) : F) : SourceValue F) = .field i ∧
        Core.keyOf t (Core.iprjAddr B k) = κ (Core.iprjAddr (Core.ixAddr b') (ZMod.val i)) := by
    intro κ hκ
    refine ⟨b, ((k : Nat) : F), hb_rep, rfl, ?_⟩
    rw [hb_eq, L1.val_cast_u56_ing hidx56, hκ]
  refine ⟨ty', hcT, hannT, fun caps => ?_, fun E₀ env lim hstored hblk caps => ?_⟩
  · exact .induct (valRep_range hlvls htmT)
      ⟨ind.params.toNat, ind.indices.toNat, ind.ctors.size, rfl, rfl, rfl, hp56, hi56, hc56⟩
      (hkey (Core.keyOf t) rfl)
  · have hmem' : Ixon.MutConst.indc ind ∈ ms.toList :=
      List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
    have heT : ∀ i, i ∈ exprRefIdxs ind.typ → i ∈ usedRefIdxs cb := by
      intro i hi
      unfold usedRefIdxs
      rw [hmuts]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.indc ind, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
    have hκ : (Core.Ctx.stored ⟨E₀, env, t, lim⟩).κ (Core.iprjAddr B k) =
        Core.keyOf t (Core.iprjAddr B k) := by
      have hin := memberAddr_mem_blockRecurAddrs (B := B) hmem
      rw [memberAddr_indc] at hin
      obtain ⟨ci, hci⟩ := hblk _ hin
      exact Core.Ctx.stored_key_of_find (c := ⟨E₀, env, t, lim⟩) hci
    exact .induct (valRep_range hlvls (tmC_stored_of_used rty heT hstored hblk htmT))
      ⟨ind.params.toNat, ind.indices.toNat, ind.ctors.size, rfl, rfl, rfl, hp56, hi56, hc56⟩
      (hkey _ hκ)

/-- **Every load of a held inductive-projection record represents its canonical constant.**
The store `E` holds the record `c` at the address and the block `cb` at the block address it
names (exact decodings); the member is the inductive `ind`; `ty₀` is the reading of its type in
the block over `E`'s blobs, well scoped. Then for a `get_ci` at the address in bounded calls
that hash no collision with `E`, the address is the member's constant address, and the
canonical annotation (at the member's root offset) is defined and the returned pointer
represents the canonical constant under every capability record: under the table's keying,
and under the keying of any prefix that stores the references the block uses and the block's
members. -/
theorem get_ci_iprj_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
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
    Core.ixAddr a = memberAddr p.block p.idx.toNat (.indc ind) ∧
    ∃ ty' : Ix.Kernel.Expr .anon,
      canonAnn cb (List.range ind.lvls.toNat)
        ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) ind.typ ty₀ = some ty' ∧
      Annotates ty' ty₀ ∧
      (∀ caps : Ix.Kernel.IndCaps .anon, Core.CIPtrRep (Core.keyOf t) h' ptr
        (.indInfo ⟨keyOf t (Core.ixAddr a), List.range ind.lvls.toNat, ty'⟩ caps)) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env cb →
        BlockStored t env p.block ms → ∀ caps : Ix.Kernel.IndCaps .anon,
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (.indInfo ⟨keyOf t (Core.ixAddr a), List.range ind.lvls.toNat, ty'⟩ caps)) := by
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
  obtain ⟨ty', hcT, hannT, hrepT, hrepS⟩ :=
    ind_value_canon ht hmuts hmem hagree built planned hraw hlev hty hty_lbb hty_def
  rw [hkey]
  exact ⟨haddr', ty', hcT, hannT, fun caps => ⟨_, hld, hrepT caps⟩,
    fun env lim hstored hblk caps => ⟨_, hld, hrepS E env lim hstored hblk caps⟩⟩

/-- **Every direct load of an inductive member represents its canonical constant**: a
`Ingress::get_ci_iprj` on the block at `ixAddr b` and the member index `i`, in bounded calls
that hash no collision with a store `E` holding the block (exact decoding), where member `i` is
the inductive `ind` whose type reads as `ty₀` over `E`'s blobs, well scoped. -/
theorem get_ci_iprj_load_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
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
      Annotates ty' ty₀ ∧
      (∀ caps : Ix.Kernel.IndCaps .anon, Core.CIPtrRep (Core.keyOf t) h' ptr
        (.indInfo ⟨Core.keyOf t (Core.iprjAddr (Core.ixAddr b) i.val),
          List.range ind.lvls.toNat, ty'⟩ caps)) ∧
      (∀ (env : Ix.Kernel.Env .anon) (lim : Option Nat), Decl.UsedRefsStored t env cb →
        BlockStored t env (Core.ixAddr b) ms → ∀ caps : Ix.Kernel.IndCaps .anon,
          Core.CIPtrRep (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h' ptr
            (.indInfo ⟨Core.keyOf t (Core.iprjAddr (Core.ixAddr b) i.val),
              List.range ind.lvls.toNat, ty'⟩ caps)) := by
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
  obtain ⟨ty', hcT, hannT, hrepT, hrepS⟩ :=
    ind_value_canon ht hmuts hmem hagree built planned hraw hlev hty hty_lbb hty_def
  exact ⟨ty', hcT, hannT, fun caps => ⟨_, hld, hrepT caps⟩,
    fun env lim hstored hblk caps => ⟨_, hld, hrepS E env lim hstored hblk caps⟩⟩

/-- **The canonical constant of an inductive member reloads** at every store `E'` that holds
the member's projection record `c` at `a` and the block `cb` at the block address it names
(exact decodings), and over whose blobs the member's type reads as `ty₀`, under the keying of
any prefix `env` that stores the references the block uses and the block's members. -/
theorem reloadsAs_ind (ht : t.check = .ok ()) {E' : Ixon.Env} {env : Ix.Kernel.Env .anon}
    {a : _root_.Address} {c cb : Ixon.Constant} {p : Ixon.InductiveProj}
    {ms : Array Ixon.MutConst} {ind : Ixon.Inductive}
    (hrec : recordOf E' a = some c) (hinfo : c.info = .iPrj p)
    (hblock : recordOf E' p.block = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[p.idx.toNat]? = some (.indc ind)) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E'.blobs.get? x) cb id
      (blockSelf t p.block ms)).read ind.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb) (hblk : BlockStored t env p.block ms)
    {caps : Ix.Kernel.IndCaps .anon} {cn : Ix.Kernel.ConstantInfo .anon}
    (hcn : canonInd (keyOf t a) cb ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) ind
      ty₀ caps = some cn) :
    Decl.ReloadsAs E' t env cn := by
  obtain ⟨ty', hcT, hcn'⟩ := canonInd_inv hcn
  subst hcn'
  intro addr ptr h h' cs a' ev hgood ha hkey
  have hk : Core.keyOf t (Core.ixAddr a') = Core.keyOf t a := hkey
  have haddr : Core.ixAddr a' = a := Assembly.keyOf_injective ht hk
  subst haddr
  obtain ⟨-, ty'', hcT', -, -, hrep⟩ :=
    get_ci_iprj_canon ht hgood.1 hgood.2 ha ev hrec hinfo hblock hmuts hmem hty hty_lbb hty_def
  have e1 : ty'' = ty' := Option.some.inj (hcT'.symm.trans hcT)
  subst e1
  exact hrep env none hstored hblk caps

/-- **The reload a step needs, for inductive member `k` of the block at `B`**: the canonical
constant reloads under the keying of the prefix that stores it, where the prefix before it
stores the references the block uses and the prefix with it stores the block's members, at
every store `E'` that holds the member's projection record at its constant address, the block
at `B`, and at least the blobs of a store `E` over which the member's type reads as `ty₀`. -/
theorem reloadsAs_ind_cons (ht : t.check = .ok ()) {E E' : Ixon.Env}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {k : Nat} {cb : Ixon.Constant}
    {ms : Array Ixon.MutConst} {ind : Ixon.Inductive} (hk64 : k < UInt64.size)
    (hproj : recordOf E' (memberAddr B k (.indc ind)) = some (memberProjection B k (.indc ind)))
    (hblock : recordOf E' B = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[k]? = some (.indc ind))
    (hblobs : ∀ x b, E.blobs.get? x = some b → E'.blobs.get? x = some b)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read ind.typ =
      .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true)
    (hstored : Decl.UsedRefsStored t env cb)
    {caps : Ix.Kernel.IndCaps .anon} {cn : Ix.Kernel.ConstantInfo .anon}
    (hblk : BlockStored t ⟨cn :: env.consts⟩ B ms)
    (hcn : canonInd (keyOf t (memberAddr B k (.indc ind))) cb
      ((L1.mutsRootOffset ms.toList k : Nat) : F) ind ty₀ caps = some cn) :
    Decl.ReloadsAs E' t ⟨cn :: env.consts⟩ cn := by
  have hkk : k.toUInt64.toNat = k := toUInt64_toNat_i hk64
  have hinfo : (memberProjection B k (.indc ind)).info = .iPrj ⟨k.toUInt64, B⟩ := rfl
  have hmem' : ms[(⟨k.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat]? = some (.indc ind) := by
    show ms[k.toUInt64.toNat]? = some (.indc ind)
    rw [hkk]
    exact hmem
  have hcn' : canonInd (keyOf t (memberAddr B k (.indc ind))) cb
      ((L1.mutsRootOffset ms.toList (⟨k.toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat : Nat) : F)
      ind ty₀ caps = some cn := by
    show canonInd (keyOf t (memberAddr B k (.indc ind))) cb
      ((L1.mutsRootOffset ms.toList k.toUInt64.toNat : Nat) : F) ind ty₀ caps = some cn
    rw [hkk]
    exact hcn
  exact reloadsAs_ind (p := ⟨k.toUInt64, B⟩) ht hproj hinfo hblock hmuts hmem'
    (ReaderReads.exprReader_mono (blob := fun x => E.blobs.get? x)
      (blob' := fun x => E'.blobs.get? x) hblobs hty)
    hty_lbb hty_def (usedRefsStored_cons cn hstored) hblk hcn'

end Ind

end IxVM.Refinement.LoadedReads
