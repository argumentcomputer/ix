import IxVMRefinement.Assembly.NativeAliasSort
import IxVMRefinement.Assembly.NativeAliasFormer
import IxVMRefinement.Assembly.NativeBlockFormer
import IxVMRefinement.Assembly.TypingDefnStep
import IxVMRefinement.Claim.TopProj
import IxVMRefinement.Claim.TopDefn

/-! # A native former that reads as a telescope has the record's length

The reading of the former of a one-type block is a syntactic telescope of the record's
parameter and index counts (`FormerAtTele`), no syntactic telescope into a sort
(`FormerAtAlias`), or a syntactic telescope into a sort of another length (`FormerTeleOther`).
On the native route the third case does not occur. The shape stage of the member's check starts
with the result-sort walk `get_result_sort_level(rc, ty, n_params + n_indices, [])`, which
head-normalizes before each binder and at the end; the structural head returns a `∀` and a sort
unchanged, so the walk accepts a syntactic telescope into a sort only at its own length
(`Decl.get_result_sort_level_tele_len`). The walk runs on the heap term of the former's type,
which represents the canonical annotation of the reading under the prefix's keying; an
annotation keeps the telescope.

* `Claim.membersChecked_of_block`, `Claim.checked_of_not_block`: the walk exports "every member
  of a block checked, or the record checked"; a block record is never checked directly, so each
  kind of record has one of the two;
* `memberCheckedLim_checkedLim`: the walk's check of a block member is a check at the member's
  address, at the walk's limit;
* `Decl.NativeShapeCalls.teleLength`: the length the shape stage's result-sort walk accepts;
* `formerTele_length`: at the walk's limit, on the native route, a former whose reading is a
  syntactic telescope into a sort has the record's parameter and index counts as its length;
* `formerTeleOther_false`, `unitStep_formerTeleOther`: the third case is empty, so the step of
  such a unit holds for every carried clause.

Everything is at the walk's limit `lim : Option Nat`.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace IxVM.Refinement.Claim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)

/-- **The walk's check of a block record is the check of each of its members**: the walk
exports that every member of a block was checked or that the record was checked, and a block
record is never checked directly (`checked_not_block`). -/
theorem membersChecked_of_block {calls : List (Call F)} {E₀ : Ixon.Env}
    (hS : LoadedReads.RunStore calls E₀) {bAddr a : _root_.Address} {t : Ix.Kernel.RoleTable}
    {lim : Option Nat} {c : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hc : recordOf E₀ a = some c) (hms : c.info = .muts ms)
    (hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → MemberCheckedLimAt calls bAddr t a ms k lim) ∨
      CheckedLimAt calls bAddr t a lim) :
    ∀ k, k < ms.size → MemberCheckedLimAt calls bAddr t a ms k lim := by
  rcases hchk with ⟨ms', hms', h⟩ | h
  · have e : ms' = ms := Ixon.ConstantInfo.muts.inj (hms'.symm.trans hms)
    subst e
    exact h
  · exact (checked_not_block hS hc hms h).elim

/-- **The walk's check of a record that is no block is the check of the record.** -/
theorem checked_of_not_block {calls : List (Call F)} {bAddr a : _root_.Address}
    {t : Ix.Kernel.RoleTable} {lim : Option Nat} {c : Ixon.Constant}
    (hnb : ∀ ms, c.info ≠ .muts ms)
    (hchk : (∃ ms, c.info = .muts ms ∧
        ∀ k, k < ms.size → MemberCheckedLimAt calls bAddr t a ms k lim) ∨
      CheckedLimAt calls bAddr t a lim) :
    CheckedLimAt calls bAddr t a lim := by
  rcases hchk with ⟨ms, hms, -⟩ | h
  · exact (hnb ms hms).elim
  · exact h

end IxVM.Refinement.Claim

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam)
open Ix.Kernel.Rules (Red DefEq Infer)

/-- **The telescope length the shape stage accepts**: at a scoped context whose load contract
and environment facts hold and which allows the result-sort run's children, a type that is a
syntactic telescope into a sort has the length the shape stage walks, the parameter count plus
the index count. -/
theorem NativeShapeCalls.teleLength {c : ScopedCtx}
    {rc typePtr blockArg index safety : SourceValue F}
    {params indices count levels : Nat} {initial : Heap F} {calls : List (Call F)}
    (shape : NativeShapeCalls rc typePtr blockArg index safety params indices count levels initial
      calls)
    {type : KExpr} (bound : params + indices < 18446744069414584321)
    (roles : RCRep c.t c.lim initial rc)
    (represented : Tm c.κ 0 (fun _ => default) initial 0 type typePtr)
    (facts : CoreEnvFacts c.toCtx) (good : CoreGood c shape.sortCalls)
    (loads : ScopedLoadFacts c) :
    ∀ k binders sort, type.stripPis k = some (binders, .sort sort) → k = params + indices := by
  have types : TypesRep c.κ (fun _ => default) shape.sortBefore 0
      (.ptr (.enum kexprListEnum) initial.length) := by
    rw [shape.nilTypes]
    exact typesRep_alloc_nil c.κ (fun _ => default) initial
  exact get_result_sort_level_tele_len (c := c) (params + indices) bound
    (roles.mono shape.initial_to_sort) types (ghostScoped_zero _) facts loads good
    (represented.mono shape.initial_to_sort) shape.sortRun

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency

/-- **A checked block member is checked at its constant address, at the walk's limit**
(`mutsMemberAt_checkedAt` at a limit that may be absent). -/
theorem memberCheckedLim_checkedLim {t : Ix.Kernel.RoleTable} {calls : List (Call F)}
    (hbound : Bounded calls) {bAddr B : _root_.Address}
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
    Ingress.projection_addr_hashed_spec hmem hb' ev_pa
  rw [hk_val] at hget' hproj hhashed
  have hget_list : ms.toList[k]? = some mc := by simpa using hk
  rw [hget_list] at hget'
  cases hget'
  have haddr : Core.BaseSeams.addr h_pre ap (memberAddr (Core.ixAddr b') k mc) :=
    ⟨a', ha', hproj.trans (LoadedReads.memberAddr_eq_projAddr _ k mc).symm⟩
  exact ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk,
    hrc_pre, hrc_m, haddr, Core.BaseSeams.addr_mono ev_ld.heap_extends haddr,
    ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩

/-- **On the native route, a former whose reading is a syntactic telescope into a sort has the
record's length**, at the walk's limit. From the walked check of member `0` of the block at `B`
under the walk's role context: the heap term of the former's type represents the canonical
annotation of the reading under the prefix's keying (the scan `expr_mentions_block` excludes the
former's own address, every other cell is a reference the block uses, which the prefix stores);
the dispatch answers `0`, so the shape stage runs; its result-sort walk accepts a syntactic
telescope into a sort only at the parameter count plus the index count. The inputs about the
prefix are the invariant, the references the block uses stored, and the former's key fresh. -/
theorem formerTele_length {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {lim : Option Nat} {env : Ix.Kernel.Env .anon}
    (hst : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {ty₀ : Ix.Kernel.Expr .anon}
    (hty₀ : (exprReader t (fun x => E₀.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀)
    {bs : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)} {s : Ix.Kernel.Level}
    (hpb : ty₀.piBinders = (bs, .sort s)) :
    bs.length = ind.params.toNat + ind.indices.toNat := by
  have hbound : Bounded calls := (hst.good env none).2
  have hblock : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  have hmuts := hrec.muts
  have hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀ :=
    ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty₀
  have hchkA := memberCheckedLim_checkedLim (mc := .indc ind) hbound hchk (by rfl)
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
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := Ingress.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hproj
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrecA
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B 0 (.indc ind) := by
    rw [hb, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold Ingress.GetCIBlockTraceResult at hres
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
  obtain ⟨count, typePtr, fields, shape₀, trace⟩ := hlev
  injection shape₀ with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst typePtr
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hg_ld.1 hhp t
  -- the prelude of the check, and the scope of the reading
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  obtain ⟨-, hty_lbb, hty_def⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E.blobs.get? x)) (self := blockSelf t B #[.indc ind]) hbound
    hlvls rty prelude.initialExtended hty prelude.scopeRun (hsub_chk _ prelude.scopeMember)
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    LoadedReads.annotation_canon_exact ht hlvls (LoadedReads.blockSelf_key t B #[.indc ind])
      hagree rty built planned trace hty hty_lbb hty_def
  -- the references the block uses are stored in the prefix
  have used : ∀ x, Ingress.RefUsed cb.refs.toList cb.sharing.toList ind.typ x →
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
  have htmP : Decl.TmCExact κP m_chk ty' tyPtr := by
    have h := TmCExact.rekey htmT hagreeP hpermP
    rw [Decl.posOf_range] at h
    exact h
  -- the dispatch is native, so the shape stage runs
  rcases Decl.native_induct_dispatch ev_chk with hnative | modeled
  rotate_left
  · exfalso
    obtain ⟨before, result, after, children, obs, hne, hext, -, hsubc⟩ := modeled
    exact hne (hnat blkPtr result before after children b obs
      (fun cl hcl => hsub_chk cl (hsubc cl hcl))
      (Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb_rep) hb_eq)
  obtain ⟨native⟩ := hnative
  obtain ⟨shape⟩ := Decl.native_shape_calls native.observed native.subset
  have hgS : Core.CoreGood (Core.Ctx.stored ⟨E, env, t, lim⟩) shape.sortCalls :=
    Core.CoreGood.ofRaw (hg_chk.sub shape.sortSubset) (fun _ _ => trivial)
  have hlen := Decl.NativeShapeCalls.teleLength (c := Core.Ctx.stored ⟨E, env, t, lim⟩) shape
    (type := ty') (by omega)
    ((Claim.RCLimRep.toRCRep hrc_m).mono native.initialToShape)
    (((htmP 0 (fun _ => default)).toTm).mono native.initialToShape)
    hinv.scopedCoreFacts.1 hgS hinv.loads
  -- an annotation keeps the telescope
  have hst₀ := Decl.stripPis_of_piBinders_sort ty₀ hpb
  obtain ⟨bs', hst', -⟩ := Decl.stripPis_sort_of_annotates _ hannT hst₀
  exact hlen _ _ _ hst'

/-- **No one-type native block has a former that reads as a telescope of another length**
than its parameter and index counts, where the walk checked its member. -/
theorem formerTeleOther_false {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    (ht : t.check = .ok ()) {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {lim : Option Nat} {env : Ix.Kernel.Env .anon}
    (hst : StepStore calls t E₀ E) (hinv : Decl.PrefixInv.{u} E t lim env)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hother : FormerTeleOther t E₀ B cb ind) : False := by
  obtain ⟨ty₀, bs, s, hty, hpb, hne⟩ := hother
  exact hne (formerTele_length.{u} ht hst hinv hrec hchk hnat hstored hfresh hty hpb)

/-- **The step of a one-type native block whose former reads as a telescope of another
length**, for every carried clause and at the walk's limit: no environment the step is asked at
exists, since the circuit refuses the block (`formerTeleOther_false`). The premises are those a
top-walked unit of this kind is handed: the table's check, the run store, the step's store, the
unit's record, the walk's check of it, the dispatch, the reading, the inert clause and the
cover clause. -/
theorem unitStep_formerTeleOther {X : Ix.Kernel.Env .anon → Prop} {calls : List (Call F)}
    {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {lim : Option Nat} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : (∃ ms, cb.info = .muts ms ∧
        ∀ k, k < ms.size → Claim.MemberCheckedLimAt calls bAddr t B ms k lim) ∨
      Claim.CheckedLimAt calls bAddr t B lim)
    (hnat : NativeRouteAt calls B) (hother : FormerTeleOther t E₀ B cb ind)
    (hinert : InertClause t cb)
    (hcover : ∀ env, HandedRefs t envT E₀ B cb env → CoverAt t env cb) :
    UnitStep.{u} X t envT E₀ E lim B cb := by
  intro env hext hnd hinv hXe href hfresh
  exfalso
  have hstored : Decl.UsedRefsStored t env cb :=
    usedRefsStored_of_cover (hcover env ⟨hext, href, hfresh⟩) hinert
  have hm : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim :=
    Claim.membersChecked_of_block hS hrec.record hrec.muts hchk 0 (by simp)
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  exact formerTeleOther_false.{u} ht hst hinv hrec hm hnat hstored hfreshT hother

end IxVM.Refinement.Typing
