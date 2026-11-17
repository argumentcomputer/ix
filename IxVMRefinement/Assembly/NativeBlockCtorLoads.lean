import IxVMRefinement.Assembly.NativeBlockFormer
import IxVMRefinement.Assembly.NativeBlockCtorRuns
import IxVMRefinement.Assembly.NativeCtorReads

/-! # The constructor loads of a native block at the constructor stage's keying

The constructor loop of a native block loads each constructor from the block record
(`get_ci_cprj`). Every such load in a run that hashes no collision with the store reads the one
record the store holds, so it represents one constant for each slot: the canonical annotation of
the slot's reading, with the raw image of the reading under the same binder plan. The heap term
of the type uses only references the block uses and the block's member addresses, so it
represents the annotation under any keying that agrees with the table's there, the constructor
stage's included.

* `LoadedReads.canonRawAnn`: the raw image of a reading under the record's binder plan;
* `LoadedReads.ctor_load_canon`: one constructor load, read exactly;
* `Typing.stagedCtorLoads_of_block`: the family `Decl.StagedCtorLoads` of the loop, at every
  such keying, from one load per slot.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

/-- **The raw image of a reading** under the binder plan of root `root` in the tree of the
record's binder blocks (`canonAnn`'s companion: the raw binder trace instead of the annotated
one). -/
noncomputable def canonRawAnn (src : Ixon.Constant) (ps : List Ix.Kernel.LevelParam) (root : F)
    (e : Ixon.Expr) (E_rd : Ix.Kernel.Expr .anon) : Option (Ix.Kernel.Expr .anon) :=
  (L1.binderRootPlan (canonTree src.binders.toList) src.sharing.toList root e).bind fun plan =>
    (L1.applyRawBinderTrace (fun level => Core.bmeta (L1.invPosLevel ps level)) E_rd plan).map
      Prod.fst

section
variable {t : Ix.Kernel.RoleTable}

/-- **A constructor load on a held block, read exactly.** A `get_ci_cprj` run at member `i` and
slot `j` of the block at `b`, in calls that hash no collision with the store: the loaded value is
the constructor record of the slot; its type pointer represents the canonical annotation of the
slot's reading, with the raw image as its raw syntax, under the table's keying, and the
annotation under every keying that agrees with the table's on the references the block uses
(with the projection permission there) and on the block's member addresses. -/
theorem ctor_load_canon (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) (hbound : Bounded cs)
    {b : Aiur.Library.Bytes.Address} {blkArg ptr : SourceValue F} {i j : F} {h h' : Heap F}
    (hb : Aiur.Library.Bytes.RepAddressRef Core.addrTy h b blkArg)
    (ev : ObsFn Core.W "Ingress::get_ci_cprj" [blkArg, .field i, .field j] h ptr h' cs)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hblock : recordOf E (Core.ixAddr b) = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i.val]? = some (.indc ind)) (hct : ind.ctors[j.val]? = some ct)
    (hcidx : ct.cidx.toNat = j.val) {cty : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty)
    (hlbb : cty.looseBVarsBounded 0 = true)
    (hdef : cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true) :
    ∃ (tyPtr blkPtr : SourceValue F) (b' : Aiur.Library.Bytes.Address)
      (ty' R' : Ix.Kernel.Expr .anon),
      loadValue h' ptr = .ok (.construct Core.kciEnum "Ctor"
        [.field (ct.lvls.toNat : F), tyPtr, blkPtr, .field i, .field j,
          .field (ct.params.toNat : F), .field (ct.fields.toNat : F),
          L1.repBoolField ct.isUnsafe]) ∧
      Aiur.Library.Bytes.RepAddressRef Core.addrTy h' b' blkPtr ∧
      Core.ixAddr b' = Core.ixAddr b ∧
      ct.lvls.toNat < 4294967296 ∧ ct.params.toNat < 72057594037927936 ∧
      ct.fields.toNat < 72057594037927936 ∧
      canonAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + j) ct.typ cty = some ty' ∧
      canonRawAnn cb (List.range ct.lvls.toNat)
        (((L1.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + j) ct.typ cty = some R' ∧
      Annotates ty' cty ∧
      (∀ d Γ, Decl.RawTmExact (Core.keyOf t) d Γ h' 0
        (Core.posOf (List.range ct.lvls.toNat) R') (Core.posOf (List.range ct.lvls.toNat) ty')
        tyPtr) ∧
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b) ms.toList, κ x = Core.keyOf t x) →
        Decl.TmCExact κ h' (Core.posOf (List.range ct.lvls.toNat) ty') tyPtr := by
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    hhp, hld, hraw, tree, plan, built, planned, hlev⟩ := L1.get_ci_cprj_origin_spec hbound hb ev
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
  have hct' : ind.ctors[j.val]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hcts
  have hctEq : ct = ct' := Option.some.inj (hct.symm.trans hct')
  subst hctEq
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨hlvls, -, hp56, hf56, -, tyPtr, blkPtr, b', hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst htp
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E.blobs.get? x)) cb
      (Ix.Kernel.Reader.recParam (List.range ct.lvls.toNat))
      (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty := by
    have h1 : (exprReader t (fun x => E.blobs.get? x) cb
        (Ix.Kernel.Reader.recParam (List.range ct.lvls.toNat))
        (blockSelf t (Core.ixAddr b) ms)).read ct.typ = .ok cty := by
      rw [Assembly.recParam_range]
      exact hty
    exact h1
  obtain ⟨R', E', hann, hrawE, htrace, hrtrace⟩ :=
    rty.toRawTmCExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := List.range ct.lvls.toNat)
      (by simp) (by simpa using hlvls) (readCtx_keyAt_inv ht _)
      (blockSelf_key t (Core.ixAddr b) ms) hagree hread' hlbb hdef
  have hap := htrace plan trace []
  rw [List.append_nil] at hap
  have hrap := hrtrace plan trace []
  rw [List.append_nil] at hrap
  have hcanon : canonAnn cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + j) ct.typ cty = some E' := by
    unfold canonAnn
    rw [canonTree_eq built, planned]
    show (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel (List.range ct.lvls.toNat)
      level)) cty plan).map Prod.fst = some E'
    rw [hap]
    rfl
  have hrcanon : canonRawAnn cb (List.range ct.lvls.toNat)
      (((L1.mutsRootOffset ms.toList i.val : Nat) : F) + 1 + j) ct.typ cty = some R' := by
    unfold canonRawAnn
    rw [canonTree_eq built, planned]
    show (L1.applyRawBinderTrace (fun level =>
      Core.bmeta (L1.invPosLevel (List.range ct.lvls.toNat) level)) cty plan).map Prod.fst =
      some R'
    rw [hrap]
    rfl
  have hmem' : Ixon.MutConst.indc ind ∈ ms.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hmem)
  have hctm : ct ∈ ind.ctors.toList := List.mem_of_getElem? hcts
  have heT : ∀ i, i ∈ exprRefIdxs ct.typ → i ∈ usedRefIdxs cb := by
    intro i hi
    unfold usedRefIdxs
    rw [hmuts]
    exact List.mem_append_right _
      (List.mem_flatMap.mpr ⟨.indc ind, hmem', by
        unfold mutRefIdxs
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨ct, hctm, hi⟩)⟩)
  refine ⟨tyPtr, blkPtr, b', E', R', ?_, hb_rep, hb_eq, hlvls, hp56, hf56, hcanon, hrcanon, hann,
    hrawE, ?_⟩
  · rw [hld, hcidx, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  · intro κ hused hrecur d Γ
    have usedOf : ∀ x, L1.RefUsed cb.refs.toList cb.sharing.toList ct.typ x →
        κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x := by
      intro x hu
      obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
      · exact hused i (heT i hi) x hr
      · have hmem2 : i ∈ usedRefIdxs cb := by
          unfold usedRefIdxs
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
        exact hused i hmem2 x hr
    refine Typing.TmExact.rekey (hrawE d Γ).toTmExact (fun a hin => ?_) (fun a hp _ => ?_)
    · rcases rty.addrIn_used a hin with hu | hr
      · exact (usedOf _ hu).1
      · exact hrecur _ hr
    · exact (usedOf _ (rty.projIn_used a hp)).2

/-- **A constructor the loop scoped has a closed reading**: the loop loads the constructor of
the slot and validates the scope of its type (`validate_expr_well_scoped` at the record's level
count), so the reading of the type has no loose variable and only the declared level
parameters. -/
theorem ctor_scope_closed (ht : t.check = .ok ()) {c : Core.Ctx} {cs_root : List (Call F)}
    (hgood : Core.Good c cs_root) {block : Aiur.Library.Bytes.Address} {i j safety : F}
    {params levels : Nat}
    (checked : Assembly.CtorScopeRead block i j safety params levels cs_root)
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} {ind : Ixon.Inductive} {ct : Ixon.Constructor}
    (hblock : recordOf c.E (Core.ixAddr block) = some cb) (hmuts : cb.info = .muts ms)
    (hmem : ms[i.val]? = some (.indc ind)) (hct : ind.ctors[j.val]? = some ct)
    {cty : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => c.E.blobs.get? x) cb id
      (blockSelf t (Core.ixAddr block) ms)).read ct.typ = .ok cty) :
    cty.looseBVarsBounded 0 = true ∧
      cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true := by
  have hg := hgood.sub checked.loadSubset
  obtain ⟨-, -, -, blkBytes, cb', ms', ind', ct', blobs, v, hhB, haB, hexB, -, hcb, hms, hcts,
    hhp, hld, hraw, -⟩ := L1.get_ci_cprj_origin_spec hg.2 checked.blockRep checked.loaded
  obtain ⟨lcB, hgetB, hdecB⟩ := recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg.1 blkBytes hhB haB
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
  have hct' : ind.ctors[j.val]? = some ct' := by
    rw [← Array.getElem?_toList]
    exact hcts
  have hctEq : ct = ct' := Option.some.inj (hct.symm.trans hct')
  subst hctEq
  obtain ⟨hlvls, -, -, -, -, tyPtr, blkPtr, b', -, -, hv, rty⟩ := hraw
  subst hv
  have hval := Except.ok.inj (hld.symm.trans checked.tag)
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hval
  obtain ⟨hnl, hty_eq, -⟩ := hval
  have hrun := checked.scopeRun
  have hmemb := checked.scopeMember
  rw [← hnl, ← hty_eq] at hrun hmemb
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => c.E.blobs.get? x)) (self := blockSelf t (Core.ixAddr block) ms)
    hgood.2 hlvls rty checked.extended hty hrun hmemb
  exact ⟨hlbb, hdef⟩

end

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open LoadedReads (canonAnn canonRawAnn)

/-- **The constructor family of a native block at any keying that agrees with the table's on the
block's cells.** The store holds the block of one inductive member at `b₀`, whose constructors
are safe; `ctors` are the readings of the constructors in order (each at its slot's stored index,
parameter count `nP`, level parameters and field count, closed), and every slot has a load in
`cs_root`. The annotated constructors `ctorsA` and their raw types are chosen once, from the
record; the family holds at every keying that resolves the references the block uses (with the
projection permission) and the block's member addresses as the table does. -/
theorem stagedCtorLoads_of_block {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {c : Core.Ctx} {cs_root : List (Call F)} (hgood : Core.Good c cs_root)
    {b₀ : Bytes.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf c.E (Core.ixAddr b₀) = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hsafe : ∀ ct ∈ ind.ctors.toList, ct.isUnsafe = false)
    (hcount : ind.ctors.size < 72057594037927936)
    {nP : Nat} {ctors : List (Ix.Kernel.ConstantVal .anon × Nat)}
    (hlen : ctors.length = ind.ctors.size)
    (hctors : ∀ j cv, ctors[j]? = some cv → ∃ ct : Ixon.Constructor,
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.params.toNat = nP ∧
      cv.1.levelParams = List.range ct.lvls.toNat ∧ cv.2 = ct.fields.toNat ∧
      (exprReader t (fun x => c.E.blobs.get? x) cb id
        (blockSelf t (Core.ixAddr b₀) #[.indc ind])).read ct.typ = .ok cv.1.type ∧
      cv.1.type.looseBVarsBounded 0 = true ∧
      cv.1.type.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hslots : ∀ j < ind.ctors.size, ∃ (bp ptr : SourceValue F) (h h' : Heap F)
      (cs : List (Call F)),
      ObsFn Core.W "Ingress::get_ci_cprj" [bp, .field 0, .field (j : F)] h ptr h' cs ∧
      (∀ cl ∈ cs, cl ∈ cs_root) ∧ Bytes.RepAddressRef Core.addrTy h b₀ bp) :
    ∃ (ctorsA : List (Ix.Kernel.ConstantVal .anon × Nat))
      (rawTypes : List (Ix.Kernel.Expr .anon)),
      ∀ κ : _root_.Address → Core.KKey,
        (∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
          κ x = Core.keyOf t x ∧ Core.ProjPermitted κ x) →
        (∀ x ∈ L1.blockRecurAddrs (Core.ixAddr b₀) (#[.indc ind] : Array Ixon.MutConst).toList,
          κ x = Core.keyOf t x) →
        Decl.StagedCtorLoads κ t b₀ nP 0 cs_root ctors ctorsA rawTypes := by
  let root : Nat → F := fun j =>
    ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList (ZMod.val (0 : F)) : Nat) : F)
      + 1 + ((j : Nat) : F)
  let annOf : Nat → Ix.Kernel.ConstantVal .anon × Nat → Ix.Kernel.Expr .anon := fun j cv =>
    ((ind.ctors[j]?).bind fun ct => canonAnn cb cv.1.levelParams (root j) ct.typ cv.1.type).getD
      default
  let rawOf : Nat → Ix.Kernel.ConstantVal .anon × Nat → Ix.Kernel.Expr .anon := fun j cv =>
    Core.posOf cv.1.levelParams (((ind.ctors[j]?).bind fun ct =>
      canonRawAnn cb cv.1.levelParams (root j) ct.typ cv.1.type).getD default)
  refine ⟨ctors.mapIdx fun j cv => (⟨cv.1.name, cv.1.levelParams, annOf j cv⟩, cv.2),
    ctors.mapIdx rawOf, fun κ hused hrecur => ⟨by simp, fun j hj => ?_⟩⟩
  obtain ⟨cv, hc⟩ : ∃ cv, ctors[j]? = some cv := ⟨ctors[j], List.getElem?_eq_getElem hj⟩
  obtain ⟨ct, hct, hcidx, hnp, hlps, hnf, hty, hlbb, hdef⟩ := hctors j cv hc
  rcases cv with ⟨⟨cn, clp, cty⟩, cnf⟩
  dsimp only at hlps hnf hty hlbb hdef
  subst hlps hnf
  have hjsize : j < ind.ctors.size := by
    rw [← hlen]
    exact hj
  have hjval : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (show j < 72057594037927936 by omega) (by decide))
  have hmem : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val (0 : F)]? = some (.indc ind) := by
    rw [ZMod.val_zero]
    rfl
  have hct' : ind.ctors[ZMod.val ((j : Nat) : F)]? = some ct := by
    rw [hjval]
    exact hct
  have hcidx' : ct.cidx.toNat = ZMod.val ((j : Nat) : F) := by
    rw [hjval]
    exact hcidx
  have hctm : ct ∈ ind.ctors.toList :=
    List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hct)
  -- the slot's annotation and raw image, from one load of the slot
  obtain ⟨bp₀, ptr₀, h₀, h₀', cs₀, ev₀, hsub₀, hbp₀⟩ := hslots j hjsize
  have hg₀ := hgood.sub hsub₀
  obtain ⟨-, -, -, ty'₀, R'₀, -, -, -, -, -, -, hcanon₀, hrcanon₀, hann₀, -, -⟩ :=
    LoadedReads.ctor_load_canon ht hg₀.1 hg₀.2 hbp₀ ev₀ hblock hmuts hmem hct' hcidx' hty hlbb hdef
  have hann_eq : annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat) = ty'₀ := by
    show ((ind.ctors[j]?).bind fun ct' => canonAnn cb (List.range ct.lvls.toNat) (root j) ct'.typ
      cty).getD default = ty'₀
    rw [hct]
    show (canonAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty).getD default = ty'₀
    have hcanon₀' : canonAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty = some ty'₀ :=
      hcanon₀
    rw [hcanon₀']
    rfl
  have hraw_eq : rawOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat) =
      Core.posOf (List.range ct.lvls.toNat) R'₀ := by
    show Core.posOf (List.range ct.lvls.toNat) (((ind.ctors[j]?).bind fun ct' =>
      canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct'.typ cty).getD default) = _
    rw [hct]
    show Core.posOf (List.range ct.lvls.toNat)
      ((canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty).getD default) = _
    have hrcanon₀' : canonRawAnn cb (List.range ct.lvls.toNat) (root j) ct.typ cty = some R'₀ :=
      hrcanon₀
    rw [hrcanon₀']
    rfl
  have hgetRaw : (ctors.mapIdx rawOf).getD j default =
      rawOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, hc]
    rfl
  refine ⟨_, ⟨cn, List.range ct.lvls.toNat,
    annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat)⟩, hc, ?_, ⟨rfl, rfl, ?_⟩, ?_⟩
  · rw [List.getElem?_mapIdx, hc]
    rfl
  · rw [hann_eq]
    exact hann₀
  intro bp ptr h h' cs hsub hbp ev
  have hg := hgood.sub hsub
  obtain ⟨tyPtr, blkPtr, b', ty', R', hld, hb', hbeq, hlv, hp56, hf56, hcanon, hrcanon, -,
    hrawE, hκ⟩ :=
    LoadedReads.ctor_load_canon ht hg.1 hg.2 hbp ev hblock hmuts hmem hct' hcidx' hty hlbb hdef
  have hty'eq : ty' = ty'₀ := Option.some.inj (hcanon.symm.trans hcanon₀)
  have hR'eq : R' = R'₀ := Option.some.inj (hrcanon.symm.trans hrcanon₀)
  rw [hty'eq, hR'eq] at hrawE
  rw [hty'eq] at hκ
  refine ⟨.field (ct.lvls.toNat : F), tyPtr, blkPtr, .field (ct.params.toNat : F),
    .field (ct.fields.toNat : F), b', ?_, hb', hbeq, ?_, ?_, ?_, rfl⟩
  · rw [hld, hsafe ct hctm]
    rfl
  · intro d Γ
    rw [hgetRaw, hraw_eq]
    show Decl.RawTmExact (Core.keyOf t) d Γ h' 0 _
      (Core.posOf (List.range ct.lvls.toNat)
        (annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat))) tyPtr
    rw [hann_eq]
    exact hrawE d Γ
  · refine ⟨by simp, by simpa using hlv, by simp, ?_⟩
    show Decl.TmCExact κ h' (Core.posOf (List.range ct.lvls.toNat)
      (annOf j (⟨cn, List.range ct.lvls.toNat, cty⟩, ct.fields.toNat))) tyPtr
    rw [hann_eq]
    exact hκ κ hused hrecur
  · rw [hnp]

end IxVM.Refinement.Typing
