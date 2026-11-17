import IxVMRefinement.Assembly.NativeAliasZeroFields
import IxVMRefinement.Assembly.NativeAliasTeleStable
import IxVMRefinement.Assembly.NativeBlockCtorOuts
import IxVMRefinement.Assembly.NativeAliasTele

/-! # Both typed stages of a native block at a former declared at a definition

`ctorOuts_of_member` reads the former stage and the constructor stage of a native block off the
walked check of its member where the former is declared at its telescope (`FormerAtTele`); the
constructor stage there is staged at the recogniser's result sort. At a former declared at a
definition (an alias former) the recogniser's result sort is a placeholder: the stage's sort is
the one the former stage chooses, the end sort of the telescope the circuit builds. Two separate
inversions of the shape stage cannot be identified (there is no determinism lemma for observed
derivations), so `aliasOuts_of_member` reads both stages on one inversion:

* `native_shape_calls_tele`: `Decl.native_shape_calls` with the telescope's typing call
  (`KernelCheck::former_tele_typed`) kept, at the same result-sort pointer;
* `ctorStageCoreFacts_of_block_indexed`: the constructor stage's scoped core facts at a family
  with an index, where the former need not be a syntactic telescope
  (`Decl.coreEnvFacts_consNativeCapsAt_indexed`);
* `aliasOuts_of_member`: over the named input `FormerTeleConv` (the regenerated path of
  `former_tele_typed`), the former checked at the prefix, the telescope constant of the former
  stage (`AliasTele`) with its sort `s`, its parameters opened as the declared former's at a family
  with a constructor, and at every recursion flag the constructors' outputs at the constructor
  stage staged at `s`, with IxC's later-use condition. At a former declared at its telescope the
  telescope constant is the declared former and `s` its sort; otherwise `s` is the level the
  result-sort walk left at the pointer the constructor loop reads (`RepKLevel.det`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

universe u

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## The shape stage with its telescope call -/

/-- **The shape stage's calls, with the telescope's typing call**: `Decl.native_shape_calls`,
keeping the call `KernelCheck::former_tele_typed` between the guard and the constructor loop, at
the result-sort pointer the loop reads. -/
theorem native_shape_calls_tele {rc typePtr blockArg index safety result : SourceValue F}
    {params indices count levels : Nat} {h h' : Heap F} {calls rootCalls : List (Call F)}
    (observed : ObsFn Core.W "KernelCheck::check_inductive_shape"
      [rc, typePtr, .field (params : F), .field (indices : F), .field (count : F),
        .field (levels : F), blockArg, index, safety] h result h' calls)
    (subset : ∀ call ∈ calls, call ∈ rootCalls) :
    ∃ (shape : Decl.NativeShapeCalls rc typePtr blockArg index safety params indices count levels
        h rootCalls) (teleResult : SourceValue F) (teleCalls : List (Call F)),
      ObsFn Core.W "KernelCheck::former_tele_typed"
        [rc, typePtr, .field ((params + indices : Nat) : F), .field (levels : F), shape.sortLevel]
        shape.guardAfter teleResult shape.ctorBefore teleCalls ∧
      ∀ call ∈ teleCalls, call ∈ rootCalls := by
  match Obs.«KernelCheck::check_inductive_shape».obs observed with
  | .run (v1 := level) (m2 := sortAfter) (cs12 := sortCalls) (m50 := sortBefore)
      (v62 := guardResult) (m63 := guardAfter) (m133 := ctorBefore) (cs73 := guardCalls)
      (v132 := teleResult) (cs143 := teleCalls) (cs198 := ctorCalls)
      (op46 := sum) (op178 := sumT) (hm58 := nilTypes) (ev14 := sortRun) (ev75 := guardRun)
      (ev145 := teleRun) (ev200 := ctorRun) (hc288 := allCalls) .. =>
    rw [Decl.evalBinOp_add_nat params indices sum] at sortRun
    rw [Decl.evalBinOp_add_nat params indices sumT] at teleRun
    exact ⟨{
      sortBefore := sortBefore, sortAfter := sortAfter, sortLevel := level, sortCalls := sortCalls
      nilTypes := nilTypes, sortRun := sortRun, guardResult := guardResult, guardAfter := guardAfter
      ctorBefore := ctorBefore, guardToCtors := teleRun.heap_extends
      guardCalls := guardCalls, guardRun := guardRun, result := result, after := h',
      ctorCalls := ctorCalls, ctorRun := ctorRun
      sortSubset := fun call member => subset call (by rw [allCalls]; simp [member])
      guardSubset := fun call member => subset call (by rw [allCalls]; simp [member])
      ctorSubset := fun call member => subset call (by rw [allCalls]; simp [member]) },
      teleResult, teleCalls, teleRun,
      fun call member => subset call (by rw [allCalls]; simp [member])⟩

/-! ## The constructor stage at a family with an index -/

/-- **The scoped core facts of the constructor stage at a family with an index**:
`ctorStageCoreFacts_of_block` with the former's telescope replaced by a nonzero index count
(`Decl.coreEnvFacts_consNativeCapsAt_indexed`: an indexed family has no eta or unit-like
capability, so its declared former need not be a syntactic telescope). -/
theorem ctorStageCoreFacts_of_block_indexed {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
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
    (hidx : p.nIdx ≠ 0) :
    Core.ScopedCoreFacts (Decl.ctorStage ⟨E, env, t, lim⟩
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
      (Ix.Kernel.nativeCapsAt p isRec)) :=
  ⟨Decl.coreEnvFacts_consNativeCapsAt_indexed (c := ⟨E, env, t, lim⟩)
      (cv := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩)
      hinv.scopedCoreFacts.1 hfresh
      (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) htype hidx,
    ctorStageLoads_of_block ht hinv hdec hP hkeys hblock hmuts hproj hbounds hty hty_lbb hty_def
      hctys hstored hcanon hfresh hunit hfree⟩

/-! ## Both stages on one reading -/

/-- The alias former guard and its canonical constructor loads, retained from the same
member-check inversion that supplies both typed stages. This is actual observed evidence;
its result level is related to the telescope stage's level. -/
def AliasGuardAt (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (env : Ix.Kernel.Env .anon) (n : Nat) (B : _root_.Address) (p₀ : Ix.Kernel.NativeParts .anon)
    (cvS : ConstantVal .anon) (ctorsA : List (ConstantVal .anon × Nat))
    (rawTypes : List (Ix.Kernel.Expr .anon)) (s : Ix.Kernel.Level) : Prop :=
  ValStored cvS p₀.cvT ∧ p₀.nP + p₀.nIdx < 18446744069414584321 ∧
  p₀.ctors.length < 549755813888 ∧
  ∃ (b : Bytes.Address) (root guardCalls : List (Call F)) (h h' : Heap F)
    (tyPtr blkPtr levelPtr result : SourceValue F) (level : Ix.Kernel.Level),
    Core.ixAddr b = B ∧ p₀.cvT.name = Core.keyOf t (Core.iprjAddr B 0) ∧
    Decl.StagedCtorLoads (Core.keyOf t) t b p₀.nP 0 root p₀.ctors ctorsA rawTypes ∧
    (∀ c ∈ p₀.ctors, c.1.levelParams = List.range c.1.levelParams.length) ∧
    (∀ cl ∈ root, cl ∈ calls) ∧ Core.Good ⟨E, env, t, some n⟩ root ∧
    (∀ cl ∈ guardCalls, cl ∈ root) ∧
    Decl.TmExact (Core.keyOf t) 0 (fun _ => default) h 0 cvS.type tyPtr ∧
    Bytes.RepAddressRef Core.addrTy h b blkPtr ∧ KernelLevels.RepKLevel h level levelPtr ∧
    Core.LvEq s level ∧
    ObsFn Core.W "KernelCheck::former_decl_ok"
      [tyPtr, .field (p₀.nP : F), .field (p₀.nIdx : F), .field (p₀.ctors.length : F),
        blkPtr, .field 0, levelPtr] h result h' guardCalls



/-- **The former stage and the constructor stage of a native block at a former declared at a
definition, from its walked check** (over the named input `FormerTeleConv`): the former checked at
the prefix as `cvS`; the telescope constant `cvTa` of the former stage (`AliasTele`) with its sort
`s`, opening its parameters as `cvS` does at a family with a constructor; and at every recursion
flag the constructors' outputs at the constructor stage staged at `s`, with IxC's later-use
condition on the annotated constructors. Both stages are read on one inversion of the shape
stage, so `s` is the sort at which the constructor loop compares the fields. -/
theorem aliasOuts_of_member_checked {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Model.nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀)
    (hnIdx : p₀.nIdx = ind.indices.toNat) (hn : ind.indices.toNat ≠ 0)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : L1.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    ∃ (cvS cvTa : ConstantVal .anon) (s : Ix.Kernel.Level)
      (ctorsA : List (ConstantVal .anon × Nat)) (rawTypes : List (Ix.Kernel.Expr .anon)),
      Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT cvS ∧
      AliasTele env p₀.cvT cvS cvTa (p₀.nP + p₀.nIdx) s ∧
      cvS.name = p₀.cvT.name ∧ cvTa.name = cvS.name ∧ cvTa.levelParams = cvS.levelParams ∧
      ctorsA.length = p₀.ctors.length ∧
      (p₀.ctors ≠ [] → ∀ tfvs r₁, Ix.Kernel.openPisAtFvars p₀.nP cvS.type 0 = some (tfvs, r₁) →
        ∃ r₂, Ix.Kernel.openPisAtFvars p₀.nP cvTa.type 0 = some (tfvs, r₂)) ∧
      (∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
        sortss.length = p₀.ctors.length ∧
        ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
          sortss[j]? = some sorts ∧
          Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
              (p₀.toInductiveShape.withSort s) isRec) :: env.consts⟩
            p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx s cvS.type
            (rawTypes.getD j default) c cA sorts) ∧
      AliasGuardAt calls t E env n B p₀ cvS ctorsA rawTypes s ∧
      (cvTa = cvS ∨ ∀ cA ∈ ctorsA,
        Ix.Kernel.Semantics.ctorZeroOk p₀.cvT.name (Ix.Kernel.Level.zeronessOf s) cA.1.type = true) ∧
      (∀ cA ∈ ctorsA, ∀ cbs body, cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
        ∀ i < cA.2,
          (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
           Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
          Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) := by
  have hconv : FormerTeleConv := formerTeleConv_of_program
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  obtain ⟨hlbb, hdef, hfv⟩ := former_scope hbound hS hrec hchk hty
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hprojE : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  have htyE : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀ :=
    ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreeT : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0)) :=
    hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hinlogic : ind.isUnsafe = false ∧ ∀ ct ∈ ind.ctors.toList, ct.isUnsafe = false := by
    have h := hrec.logic
    unfold InLogic at h
    rw [hrec.muts] at h
    exact h (.indc ind) (by simp)
  -- the recogniser at the record's index count
  obtain ⟨caps₀, hshape, hnP, -, -, hlps_ctors, -⟩ := nativePartsAt?_inv hp₀
  injection hshape with hhead hcs_eq
  injection hhead with hcv _
  have hcvT : p₀.cvT = ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩ :=
    hcv.symm
  have hlenP : p₀.ctors.length = ind.ctors.size := by
    rw [← hlen, hcs_eq, List.length_map]
  have hctor : ∀ j c, p₀.ctors[j]? = some c → ∃ ct : Ixon.Constructor,
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧ ct.lvls.toNat = ind.lvls.toNat ∧
      ct.params.toNat = ind.params.toNat ∧
      c.1 = ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, c.1.type⟩ ∧
      c.2 = ct.fields.toNat ∧
      (exprReader t (fun x => E₀.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ct.typ = .ok c.1.type := by
    intro j c hc
    have hcsj : cs[j]? = some (.ctorInfo c.1 p₀.nP c.2) := by
      rw [hcs_eq]
      simp [hc]
    obtain ⟨ct, tyj, h1, h2, h3, h4, h5, hceq, -⟩ := hcs j _ hcsj
    injection hceq with hc1 _ hc3
    refine ⟨ct, h1, h2, h3, h4, ?_, hc3, ?_⟩
    · rw [hc1]
    · rw [hc1]
      exact h5
  have hjlt : ∀ {j c}, p₀.ctors[j]? = some c → j < ind.ctors.size := fun {j c} hc => by
    rw [← hlenP]
    exact (List.getElem?_eq_some_iff.mp hc).1
  -- the navigation of the member's check
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk (by rfl)
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre,
    ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchkA
  obtain ⟨a, ha, hax⟩ := ha_pre
  have hg_ld : Core.Good ⟨E, env, t, some n⟩ cs_load := hgood.sub hsub_ld
  have hg_chk : Core.Good ⟨E, env, t, some n⟩ cs_chk := hgood.sub hsub_chk
  have h0' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hprojE
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrecA
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
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblockE
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj (hcb.symm.trans hrec.muts))
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
  obtain ⟨ty'₁, hcT₁, -, htmT⟩ :=
    LoadedReads.annotation_canon_exact ht hlvls (LoadedReads.blockSelf_key t B #[.indc ind])
      hagree rty built planned trace htyE hlbb hdef
  -- the former, checked at the prefix
  obtain ⟨ty', hcT, hann, hcheck, -⟩ := formerChecked_of_member ht hst hinv hblockE hrec.muts
    hprojE hchk htyE hlbb hdef hfv hstored hfreshT hfreeT
  have hty'₁ : ty'₁ = ty' := Option.some.inj (hcT₁.symm.trans hcT)
  rw [hty'₁] at htmT
  have hcheckT : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ := by
    rw [hcvT]
    exact hcheck
  obtain ⟨ty'', ⟨-, -, -, -, -, -, -, hlpd', hcr', -⟩, hcv'⟩ := id hcheck
  have hty'' : ty' = ty'' := congrArg Ix.Kernel.ConstantVal.type hcv'
  have htype : ty'.hasFvar = false ∧
      ty'.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
      ty'.constsResolve env = true ∧ ty'.looseBVarsBounded 0 = true := by
    refine ⟨Decl.annotates_hasFvar_false hann hfv, ?_, ?_,
      Decl.annotates_looseBVarsBounded hann 0 hlbb⟩
    · rw [hty'']
      exact hlpd'
    · rw [hty'']
      exact hcr'
  -- the former's type at the prefix's keying (the former stage's context)
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  have used : ∀ x, L1.RefUsed cb.refs.toList cb.sharing.toList ind.typ x →
      ∃ ci, env.find? (Core.keyOf t x) = some ci := by
    have hmem' : Ixon.MutConst.indc ind ∈ (#[.indc ind] : Array Ixon.MutConst).toList :=
      List.mem_singleton.mpr rfl
    intro x hu
    obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      rw [hrec.muts]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.indc ind, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
  let cP : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some n⟩
  let κP := cP.κ
  have hextM : Heap.Extends m_chk prelude.mentionsBefore :=
    prelude.initialExtended.trans prelude.scope_to_mentions
  have hagreeP : ∀ a', Core.AddrIn m_chk tyPtr a' →
      κP (Core.ixAddr a') = Core.keyOf t (Core.ixAddr a') := by
    intro a' hin
    rcases rty.addrIn_used a' hin with hu | hr
    · obtain ⟨ci, hci⟩ := used _ hu
      exact Core.Ctx.stored_key_of_find (c := ⟨E, env, t, some n⟩) hci
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
      have hscan := mentions_block_cells (c := ⟨E, env, t, some n⟩) hst.decoded hblockE hrec.muts
        hprojE hb_eq hin hextM (prelude.blocksRep hb_rep) prelude.mentionsRun
        (hg_chk.sub prelude.mentionsSubset)
      rcases hscan with hp | hne
      · obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
        rw [hxm', hfreshT] at hci
        cases hci
      · exact hne hxm'
  have hpermP : ∀ a', Core.ProjIn m_chk tyPtr a' →
      Core.ProjPermitted (Core.keyOf t) (Core.ixAddr a') → Core.ProjPermitted κP (Core.ixAddr a') := by
    intro a' hp _
    obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
    exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, some n⟩) hci
  have htmP : Decl.TmCExact κP m_chk (Core.posOf (List.range ind.lvls.toNat) ty') tyPtr :=
    TmCExact.rekey htmT hagreeP hpermP
  rw [Decl.posOf_range] at htmP
  -- the dispatch is native
  have hsafeF : L1.repBoolField ind.isUnsafe = .field 0 := by
    rw [hinlogic.1]
    rfl
  rw [hsafeF, Nat.cast_zero] at ev_chk
  rcases Decl.native_induct_dispatch ev_chk with hnative | modeled
  rotate_left
  · exfalso
    obtain ⟨before, result, after, children, obs, hne, hext, -, hsubc⟩ := modeled
    exact hne (hnat blkPtr result before after children b obs
      (fun cl hcl => hsub_chk cl (hsubc cl hcl))
      (Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb_rep) hb_eq)
  obtain ⟨native⟩ := hnative
  -- one inversion of the shape stage, read by both typed stages
  obtain ⟨shape, teleResult, teleCalls, teleRun, hteleSub⟩ :=
    native_shape_calls_tele native.observed native.subset
  have e_sort : Heap.Extends m_chk native.before := native.initialToShape
  have e_ctor : Heap.Extends m_chk shape.ctorBefore :=
    native.initialToShape.trans shape.initial_to_ctors
  have ctorRun₀ := shape.ctorRun
  have hbRepCtor : Bytes.RepAddressRef Core.addrTy shape.ctorBefore b blkPtr :=
    Bytes.repAddressRef_heapMono₂ Core.addrTy e_ctor hb_rep
  have hblockB : recordOf E (Core.ixAddr b) = some cb := by
    rw [hb_eq]
    exact hblockE
  -- the former stage: the telescope constant and its sort
  have hgS : ∀ cs', (∀ x ∈ cs', x ∈ cs_chk) → Core.CoreGood cP cs' := fun cs' hs =>
    Core.CoreGood.ofRaw (hg_chk.sub hs) (fun _ _ => trivial)
  have hrcP : Core.RCRep t (some n) m_chk rc := hrc_m.toRCRep
  have hef := hinv.scopedCoreFacts.1
  have hlf := hinv.loads
  have hPI : ind.params.toNat + ind.indices.toNat < 18446744069414584321 := by omega
  have e_sb : Heap.Extends m_chk shape.sortBefore :=
    native.initialToShape.trans shape.initial_to_sort
  have e_ga : Heap.Extends m_chk shape.guardAfter :=
    (native.initialToShape.trans shape.initial_to_guard).trans shape.guardRun.heap_extends
  obtain ⟨ℓ, hℓ, hℓTele⟩ := Decl.get_result_sort_level_any_spec (c := cP)
    (ind.params.toNat + ind.indices.toNat) hPI (hrcP.mono e_sb)
    (by rw [shape.nilTypes]; exact Decl.typesRep_alloc_nil κP (fun _ => default) native.before)
    (Decl.ghostScoped_zero _) hef hlf (hgS _ shape.sortSubset)
    ((htmP 0 (fun _ => default)).toTm.mono e_sb) shape.sortRun
  have hstage : ∃ (cvTa : ConstantVal .anon) (s : Ix.Kernel.Level),
      AliasTele env ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ cvTa
        (ind.params.toNat + ind.indices.toNat) s ∧
      (ind.ctors.size ≠ 0 →
        ∀ tfvs r₁, Ix.Kernel.openPisAtFvars ind.params.toNat ty' 0 = some (tfvs, r₁) →
          ∃ r₂, Ix.Kernel.openPisAtFvars ind.params.toNat cvTa.type 0 = some (tfvs, r₂)) ∧
      ((∃ bs, ty'.stripPis (ind.params.toNat + ind.indices.toNat) = some (bs, .sort s)) ∨
        KernelLevels.RepKLevel shape.ctorBefore s shape.sortLevel) ∧
      (cvTa = ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ ∨
        ∃ testResult testAfter testCalls,
          ObsFn Core.W "KernelCheck::former_is_tele"
            [tyPtr, .field ((ind.params.toNat + ind.indices.toNat : Nat) : F)]
            shape.guardAfter testResult testAfter testCalls ∧ testResult ≠ .field 1) := by
    rcases hconv _ _ _ _ _ _ _ _ _ teleRun with
      ⟨m2, cs13, evIs, -, -, -⟩ |
      ⟨v1, m2, cs13, tele, m46, cs56, v105, m106, cs116, v142, m143, cs153, mD, csD,
        evIs, hne1, evAt, evWs, evSort, evDq, -, hhD, hcsT⟩
    · -- a former declared at its telescope: its own telescope constant, at its own sort
      obtain ⟨-, bs, s, hstT, -⟩ := Decl.former_is_tele_one_bounded_spec
        (ind.params.toNat + ind.indices.toNat) hPI ((htmP 0 (fun _ => default)).mono e_ga) evIs
      exact ⟨_, s, aliasTele_of_tele hcheck hstT, fun _ tfvs r₁ hop => ⟨r₁, hop⟩,
        Or.inl ⟨bs, hstT⟩, Or.inl rfl⟩
    · -- a former declared at a definition: the built telescope, ending in the walk's level
      have e_m2 : Heap.Extends m_chk (m2 ++ [.construct Core.kexprListEnum "Nil" []]) :=
        e_ga.trans (evIs.heap_extends.trans (Heap.Extends.snoc _ _))
      obtain ⟨⟨R, hR⟩, hshapeT, hcells⟩ := Decl.former_tele_at_spec (c := cP)
        (ind.params.toNat + ind.indices.toNat) hPI (hrcP.mono e_m2)
        (Decl.typesRep_alloc_nil κP (fun _ => default) m2) (Decl.ghostScoped_zero _) hef hlf
        (hgS cs56 (fun x hx => hteleSub x (by rw [hcsT]; simp [hx])))
        ((htmP 0 (fun _ => default)).toTm.mono e_m2)
        (hℓ.mono (shape.guardRun.heap_extends.trans
          (evIs.heap_extends.trans (Heap.Extends.snoc _ _)))) evAt
      obtain ⟨E', hE'⟩ := Decl.Tm.exactify hR
      have e_ws : Heap.Extends m46 (m106 ++ [.construct Core.kexprListEnum "Nil" []]) :=
        evWs.heap_extends.trans (Heap.Extends.snoc _ _)
      have e_dq : Heap.Extends m46 (m143 ++ [.construct Core.kexprListEnum "Nil" []]) :=
        e_ws.trans (evSort.heap_extends.trans (Heap.Extends.snoc _ _))
      have e_end : Heap.Extends m46 shape.ctorBefore := by
        rw [hhD]
        exact e_dq.trans evDq.heap_extends
      have e_m46 : Heap.Extends m_chk m46 := e_m2.trans evAt.heap_extends
      -- its shape and its end sort
      obtain ⟨bs, l, hstE, hlrep⟩ := Decl.TeleShape.stripPis_exact
        (ind.params.toNat + ind.indices.toNat) hshapeT hE'
      -- checked from scratch at the prefix
      have hlbbE : E'.looseBVarsBounded 0 = true := hE'.toTm.looseBVarsBounded
      have hfvE : E'.hasFvar = false := Decl.Tm.hasFvar_false hE'.toTm
      have hannE : Annotates E' E' := Decl.annotates_refl_of_noLetExpr
        (hE'.noLet (fun _ hlt => absurd hlt (Nat.not_lt_zero _)))
      have hvE : Decl.ValRepExact κP m46 (.field (ind.lvls.toNat : F)) tele
          ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩ := by
        refine ⟨by simp, by simpa using hlvls, by simp, ?_⟩
        show Decl.TmCExact κP m46 (Core.posOf (List.range ind.lvls.toNat) E') tele
        rw [Decl.posOf_range]
        exact fun d Γ => hE'.of_depth_zero d
      obtain ⟨checkedT, -⟩ := Decl.constantValCheckJ_of_scoped (c := cP)
        (cv := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩)
        (cv' := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩)
        ⟨rfl, rfl, hannE⟩ hvE hlbbE hfvE hfreshT hfreeT.1
        (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) hinv.store.store
        (Decl.PosSortLift.of_range rfl) evWs e_ws (hrcP.mono (e_m46.trans e_ws))
        (Decl.typesRep_alloc_nil κP (fun _ => default) m106) hef hlf
        (hgS cs153 (fun x hx => hteleSub x (by rw [hcsT]; simp [hx]))) evSort
      -- convertible with the declared former's annotated type
      have hdq : Ix.Kernel.Rules.DefEq env 0 ty' E' :=
        Decl.scoped_core_defeq (c := cP) (hrcP.mono (e_m46.trans e_dq))
          (Decl.typesRep_alloc_nil κP (fun _ => default) m143) (Decl.ghostScoped_zero _) hef hlf
          (hgS csD (fun x hx => hteleSub x (by rw [hcsT]; simp [hx]))) evDq
          ((htmP 0 (fun _ => default)).toTm.mono (e_m46.trans e_dq))
          (hE'.toTm.mono e_dq)
      refine ⟨⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩, l,
        ⟨⟨E', checkedT⟩, ⟨bs, hstE⟩, hdq⟩, ?_, Or.inr (hlrep.mono e_end), Or.inr ⟨v1, m2, cs13, evIs, hne1⟩⟩
      -- the parameters, at a family with a constructor
      intro hnc tfvs r₁ hop
      obtain ⟨H, hH, hfc⟩ := Decl.check_inductive_shape_ctors_param_cells hnc (by omega)
        (by omega) ctorRun₀
      have hTC := hcells ind.params.toNat H (by omega) (e_end.trans hH) hfc
      have hpre := Decl.TeleCells.prefixEq ind.params.toNat hTC
        ((htmP 0 (fun _ => default)).mono (e_ctor.trans hH)) (hE'.mono (e_end.trans hH))
      exact Decl.PrefixEq.openPisAtFvars ind.params.toNat hpre hop
  obtain ⟨cvTa, s, hAT, hparam, hsortRel, hchoice⟩ := hstage
  obtain ⟨⟨tyT, htyT⟩, -, -⟩ := id hAT
  -- the constructor count, from the former's direct load
  obtain ⟨srcA, hsrcA⟩ := canonicalRecord_value hst.decoded hrecA
  have hshapeA : srcA.value.info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := by
    rw [hsrcA]
    rfl
  obtain ⟨par, parArg, mid, inner, hparEq, -, hparRep, hdirect, hinner, -⟩ :=
    L1.get_ci_iPrj_subcall (base := ⟨E, env, t, some n⟩) srcA hshapeA ha hg_ld ev_ld
  rw [h0', Nat.cast_zero] at hdirect
  have hblockPar : recordOf E (Core.ixAddr par) = some cb := by
    rw [hparEq]
    exact hblockE
  obtain ⟨srcB, hsrcB⟩ := canonicalRecord_value hst.decoded hblockPar
  obtain ⟨-, -, -, hc39⟩ := L1.get_ci_iprj_header_bounds (base := ⟨E, env, t, some n⟩) (i := 0)
    (members := #[.indc ind]) srcB (by rw [hsrcB]; exact hrec.muts)
    (by rw [ZMod.val_zero]; rfl) (hg_ld.sub hinner) hparRep hdirect
  -- each slot of the loop loads its constructor and scopes its type
  have hscope : ∀ j < ind.ctors.size, Nonempty (Assembly.CtorScopeRead b 0 ((j : Nat) : F) 0
      ind.params.toNat ind.lvls.toNat cs_chk) := by
    intro j hj
    simpa only [Nat.zero_add] using
      Assembly.native_ctor_scope_reads hc39 ind.ctors.size 0 (by omega) hbRepCtor
        shape.ctorSubset ctorRun₀ j hj
  have hjval : ∀ {j : Nat}, j < ind.ctors.size → ZMod.val ((j : Nat) : F) = j := fun {j} hj =>
    ZMod.val_natCast_of_lt (Nat.lt_trans (show j < 72057594037927936 by omega) (by decide))
  have hmem0 : (#[.indc ind] : Array Ixon.MutConst)[ZMod.val (0 : F)]? = some (.indc ind) := by
    rw [ZMod.val_zero]
    rfl
  have hclosed : ∀ j (ct : Ixon.Constructor) (cty : Ix.Kernel.Expr .anon), j < ind.ctors.size →
      ind.ctors[j]? = some ct →
      (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ct.typ = .ok cty →
      cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true := by
    intro j ct cty hj hct hcty
    obtain ⟨checked⟩ := hscope j hj
    exact LoadedReads.ctor_scope_closed ht hg_chk checked hblockB hrec.muts hmem0
      (by rw [hjval hj]; exact hct) (by rw [hb_eq]; exact hcty)
  have hctysE : ∀ (k : Nat) (ct : Ixon.Constructor), ind.ctors[k]? = some ct →
      ct.cidx.toNat = k ∧ ∃ cty : Ix.Kernel.Expr .anon,
        (exprReader t (fun x => E.blobs.get? x) cb id
          (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
        cty.looseBVarsBounded 0 = true ∧
        cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true := by
    intro k ct hct
    have hk : k < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
    have hkc : k < cs.length := by
      rw [hlen]
      exact hk
    obtain ⟨ct', tyj, h1, h2, -, -, h5, -, -⟩ := hcs k cs[k] (List.getElem?_eq_getElem hkc)
    have hctEq : ct' = ct := Option.some.inj (h1.symm.trans hct)
    rw [hctEq] at h2 h5
    have h5E := ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5
    exact ⟨h2, tyj, h5E, hclosed k ct tyj hk hct h5E⟩
  -- the constructor family, chosen once
  obtain ⟨ctorsA, rawTypes, hcload_gen⟩ := stagedCtorLoads_of_block (nP := p₀.nP) ht hg_chk
    hblockB hrec.muts hinlogic.2 hc56 hlenP (by
      intro j cv hcv
      obtain ⟨ct, h1, h2, -, h4, hc1, hc2, h5⟩ := hctor j cv hcv
      have h5E := ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5
      obtain ⟨hl, hd⟩ := hclosed j ct cv.1.type (hjlt hcv) h1 h5E
      refine ⟨ct, h1, h2, h4.trans hnP.symm, congrArg ConstantVal.levelParams hc1, hc2, ?_, hl, hd⟩
      rw [hb_eq]
      exact h5E)
    (fun j hj => by
      obtain ⟨checked⟩ := hscope j hj
      exact ⟨_, _, _, _, _, checked.loaded, checked.loadSubset, checked.blockRep⟩)
  have hcloadT := hcload_gen (Core.keyOf t) (fun i hi x hx => ⟨rfl, inferInstance⟩)
    (fun x hx => rfl)
  -- the stage's keying on the block's cells
  have hnt : ∀ T : Core.KKey, Core.keyOf t (Core.iprjAddr B 0) ≠ Ix.Kernel.projTableName T :=
    fun _ => Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  let cvS : ConstantVal .anon := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
  have hused : ∀ caps₁ : Ix.Kernel.IndCaps .anon, ∀ i ∈ usedRefIdxs cb, ∀ x,
      cb.refs.toList[i]? = some x →
      (Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁).κ x = Core.keyOf t x ∧
        Core.ProjPermitted (Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁).κ x := by
    intro caps₁ i hi x hx
    obtain ⟨ci, hci⟩ := hstored i hi x hx
    exact ctorStage_of_find (cvF := cvS) hfreshT hnt hci
  have hrecur : ∀ caps₁ : Ix.Kernel.IndCaps .anon,
      ∀ x ∈ L1.blockRecurAddrs B (#[.indc ind] : Array Ixon.MutConst).toList,
      (Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁).κ x = Core.keyOf t x := by
    intro caps₁ x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨m, hm, rfl⟩ := LoadedReads.blockRecurAddrs_get hk
    have hk0 : k = 0 := by
      have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
      omega
    subst hk0
    have hmm : m = .indc ind := by simpa using hm.symm
    subst hmm
    rw [LoadedReads.memberAddr_indc]
    exact ctorStage_former (cvF := cvS) rfl
  have hTname : p₀.cvT.name = Core.keyOf t (Core.iprjAddr B 0) := by
    rw [hcvT]
  have hbaseT : p₀.cvT.name.base = p₀.cvT.name := by
    rw [hTname]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hfnTbl : env.find? (Ix.Kernel.projTableName p₀.cvT.name) = none :=
    haux.fresh_of_base_none (by
      show env.find? p₀.cvT.name.base = none
      rw [hbaseT, hTname]
      exact hfreshT)
  -- the constructors' keys
  have hT_ctor : ∀ j, j < ind.ctors.size →
      Core.keyOf t (Core.iprjAddr B 0) ≠ keyOf t (ctorAddr B 0 j) := by
    intro j hj e
    have ha' : ctorAddr B 0 j = memberAddr B 0 (.indc ind) := (Core.keyOf_inj htwf e).symm
    have h1 := hrec.ctors j hj
    rw [ha', hrec.former] at h1
    have hinfo' := congrArg Ixon.Constant.info (Option.some.inj h1)
    simp [memberProjection, constructorProjection] at hinfo'
  -- the raw facts of the walked trace, at the prefix's store
  have hcovChk : L1.CanonicalHashCoverage E cs_chk := fun bytes value hh hsz hdec =>
    hcov bytes value (Core.hashed_mono hsub_chk hh) hsz hdec
  have hraw_at : ∀ env' : Ix.Kernel.Env .anon,
      Core.RawRecordFacts (L1.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk) ∧
      Decl.OneTypePeerReads (L1.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk) b p₀.cvT.name
        p₀.cvT.levelParams.length p₀.nP p₀.nIdx p₀.ctors.length 0 := by
    intro env'
    refine ⟨L1.rawRecordFacts_of_hashed_trace (base := ⟨E, env', t, some n⟩) ev_chk hg_chk hcovChk,
      ?_⟩
    obtain ⟨srcF, hsrcF⟩ := canonicalRecord_value hst.decoded
      (show recordOf E (Core.iprjAddr (Core.ixAddr b) (ZMod.val (0 : F))) =
        some (memberProjection B 0 (.indc ind)) by rw [ZMod.val_zero, hb_eq]; exact hprojE)
    obtain ⟨srcB', hsrcB'⟩ := canonicalRecord_value hst.decoded hblockB
    have hpeer := Assembly.native_peer_reads (raw := L1.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk)
      (block := b) (i := 0) srcB' srcF
      (by rw [hsrcF, ZMod.val_zero, hb_eq]; rfl) (by rw [hsrcB']; exact hrec.muts) hmem0
      (Assembly.native_inductives_singleton (Nat.le_of_eq rfl) hmem0) htwf
    have hT : (L1.traceRecordCtx ⟨E, env', t, some n⟩ cs_chk).κ
        (Core.iprjAddr (Core.ixAddr b) (ZMod.val (0 : F))) = p₀.cvT.name := by
      rw [hcvT, ZMod.val_zero, hb_eq]
      rfl
    have hL : ind.lvls.toNat = p₀.cvT.levelParams.length := by
      rw [hcvT]
      simp
    rw [hT, hL, ← hnP, ← hnIdx, ← hlenP] at hpeer
    exact hpeer
  -- the constructors' outputs at the stage, at every recursion flag
  have hlpsL : ind.lvls.toNat = p₀.cvT.levelParams.length := by
    rw [hcvT]
    simp
  have hrun_at : ∀ a₁ a₂ a₃ a₄ : Nat, a₁ = ind.params.toNat → a₂ = ind.indices.toNat →
      a₃ = ind.ctors.size → a₄ = ind.lvls.toNat →
      ObsFn Core.W "KernelCheck::check_inductive_shape_ctors"
        [rc, tyPtr, .field (a₁ : F), .field (a₂ : F), .field (a₃ : F), .field (a₄ : F), blkPtr,
          .field 0, shape.sortLevel, .field 0, .field 0]
        shape.ctorBefore shape.result shape.after shape.ctorCalls := by
    intro a₁ a₂ a₃ a₄ h₁ h₂ h₃ h₄
    subst h₁ h₂ h₃ h₄
    exact ctorRun₀
  have ctorRun := hrun_at p₀.nP p₀.nIdx p₀.ctors.length p₀.cvT.levelParams.length hnP hnIdx
    hlenP hlpsL.symm
  have h256 : (2 : Nat) ^ 56 = 72057594037927936 := by norm_num
  have hidxS : ∀ s' : Ix.Kernel.Level, (p₀.toInductiveShape.withSort s').nIdx ≠ 0 := by
    intro s'
    show p₀.nIdx ≠ 0
    rw [hnIdx]
    exact hn
  have houts : ∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
      sortss.length = p₀.ctors.length ∧
      ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
        sortss[j]? = some sorts ∧
        Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort s) isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx s cvS.type
          (rawTypes.getD j default) c cA sorts := by
    intro isRec
    have hunit : ind.indices.toNat = 0 → ind.ctors.size = 1 →
        (∀ ct, ind.ctors[0]? = some ct → ct.fields.toNat = 0) →
        (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec).unitlike =
          true ∧
        (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec).unitParams =
          ind.params.toNat := fun h0 => absurd h0 hn
    have hcore := ctorStageCoreFacts_of_block_indexed (p := p₀.toInductiveShape.withSort s)
      (isRec := isRec) ht hinv hst.decoded hP hkeys hblockE hrec.muts hprojE
      ⟨by rw [h256]; exact hp56, by rw [h256]; exact hi56, by rw [h256]; exact hc56⟩
      htyE hlbb hdef hctysE hstored hcT hfreshT hunit hfreeT.1 htype (hidxS s)
    let caps₁ := Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec
    let cS := Decl.ctorStage ⟨E, env, t, some n⟩ cvS caps₁
    have hcload := hcload_gen cS.κ (hused caps₁) (by rw [hb_eq]; exact hrecur caps₁)
    -- the former's type at the stage
    have htmS : Decl.TmCExact cS.κ m_chk (Core.posOf (List.range ind.lvls.toNat) ty') tyPtr := by
      refine TmCExact.rekey htmT (fun a' hin => ?_) (fun a' hp _ => ?_)
      · rcases rty.addrIn_used a' hin with hu | hr
        · obtain ⟨i, hi | ⟨s₁, hs, his⟩, hr⟩ := hu
          · refine (hused caps₁ i ?_ _ hr).1
            unfold usedRefIdxs
            rw [hrec.muts]
            exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.indc ind,
              List.mem_singleton.mpr rfl, by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
          · refine (hused caps₁ i ?_ _ hr).1
            unfold usedRefIdxs
            exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s₁, hs, his⟩)
        · exact hrecur caps₁ _ hr
      · obtain ⟨i, hi | ⟨s₁, hs, his⟩, hr⟩ := rty.projIn_used a' hp
        · refine (hused caps₁ i ?_ _ hr).2
          unfold usedRefIdxs
          rw [hrec.muts]
          exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨.indc ind,
            List.mem_singleton.mpr rfl, by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
        · refine (hused caps₁ i ?_ _ hr).2
          unfold usedRefIdxs
          exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s₁, hs, his⟩)
    have hformer : Core.Tm cS.κ 0 (fun _ => default) m_chk 0 ty' tyPtr := by
      have h := (htmS 0 (fun _ => default)).toTm
      rwa [Decl.posOf_range] at h
    -- the result sort, at the pointer the former stage read
    obtain ⟨ind_lvl, hlvRep, hsame⟩ := shape.resultSort_staged (c := cS) (type := ty')
      (by omega) (hrc_m.toRCRep.mono e_sort) (hformer.mono e_sort) hcore.1
      (Core.CoreGood.ofRaw (hg_chk.sub shape.sortSubset) (fun _ _ => trivial)) hcore.2
    have hlveq : Core.LvEq s ind_lvl := by
      rcases hsortRel with ⟨bs, hstS⟩ | hrep
      · exact hsame bs s hstS
      · rw [KernelLevels.RepKLevel.det hrep hlvRep]
        exact Core.LvEq.refl _
    -- the loop at the stage
    have hfnF : ∀ c ∈ p₀.ctors, c.2 < 72057594037927936 := by
      intro c hc
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
      obtain ⟨ct, h1, h2, -, -, hc1, hc2, h5⟩ := hctor j c hj
      have hjs := hjlt hj
      obtain ⟨checked⟩ := hscope j hjs
      have h5E := ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5
      obtain ⟨hl, hd⟩ := hclosed j ct c.1.type hjs h1 h5E
      have hg := hg_chk.sub checked.loadSubset
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hf56, -⟩ :=
        LoadedReads.ctor_load_canon ht hg.1 hg.2 checked.blockRep checked.loaded hblockB
          hrec.muts hmem0 (by rw [hjval hjs]; exact h1) (by rw [hjval hjs]; exact h2)
          (by rw [hb_eq]; exact h5E) hl hd
      rw [hc2]
      exact hf56
    obtain ⟨sortss, hlen_s, hout⟩ := Decl.native_ctor_staged IxVM.Refinement.Levels.levels
      (cS := cS) (fun _ => trivial) (T := p₀.cvT.name) (lps := p₀.cvT.levelParams)
      (nP := p₀.nP) (nIdx := p₀.nIdx) (ta := ty') (resSort := s) (ind_lvl := ind_lvl)
      (cs_root := cs_chk) (ctors := p₀.ctors) (ctorsA := ctorsA) (ctorRawTypes := rawTypes)
      (indIndex := 0) (b₀ := b)
      (by rw [hcvT]; simp) (by rw [hcvT]; simpa using hlvls) (by rw [hnP]; exact hp56)
      (by rw [hnIdx]; exact hi56) (by rw [hlenP]; exact hc39) hfnF hlveq hcload
      (fun c hc => (hlps_ctors c hc).1)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, h1, -, -, -, -, -, h5⟩ := hctor j c hj
        exact (hclosed j ct c.1.type (hjlt hj) h1
          (ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) h5)).1)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, -, -, h5⟩ := hctor j c hj
        exact Assembly.memberReader_read_noFvar h5)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, hc1, -, -⟩ := hctor j c hj
        show (Ix.Kernel.Env.mk (ConstantInfo.indInfo cvS caps₁ :: env.consts)).find? c.1.name = none
        rw [Decl.find?_cons_ne (by rw [hc1]; exact hT_ctor j (hjlt hj)), hc1]
        exact hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl,
          Or.inr ⟨ind, j, rfl, hjlt hj, rfl⟩⟩))
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, hc1, -, -⟩ := hctor j c hj
        rw [hc1]
        exact (hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl,
          Or.inr ⟨ind, j, rfl, hjlt hj, rfl⟩⟩)).1)
      (fun c hc => by
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
        obtain ⟨ct, -, -, -, -, hc1, -, -⟩ := hctor j c hj
        rw [hc1]
        exact Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _))
      (fun i => Ix.Kernel.Env.findProj?_none_of_fresh (by
        show (Ix.Kernel.Env.mk (ConstantInfo.indInfo cvS caps₁ :: env.consts)).find?
          (Ix.Kernel.projTableName p₀.cvT.name) = none
        rw [Decl.find?_cons_ne (by rw [hcvT]; exact hnt _)]
        exact hfnTbl) i)
      hcore.1.store hcore.1 hcore.2
      (hraw_at ⟨ConstantInfo.indInfo cvS caps₁ :: env.consts⟩).1
      (hraw_at ⟨ConstantInfo.indInfo cvS caps₁ :: env.consts⟩).2 shape.ctorSubset
      (hg_chk.sub shape.ctorSubset) (hrc_m.toRCRep.mono e_ctor) (hformer.mono e_ctor)
      hbRepCtor hlvRep ctorRun
    exact ⟨sortss, hlen_s, hout⟩
  -- the former stage's outputs, at the recogniser's counts
  have hparam' : p₀.ctors ≠ [] → ∀ tfvs r₁,
      Ix.Kernel.openPisAtFvars p₀.nP cvS.type 0 = some (tfvs, r₁) →
      ∃ r₂, Ix.Kernel.openPisAtFvars p₀.nP cvTa.type 0 = some (tfvs, r₂) := by
    intro hne tfvs r₁ hop
    have hsz : ind.ctors.size ≠ 0 := by
      rw [← hlenP]
      exact fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
    rw [hnP] at hop ⊢
    exact hparam hsz tfvs r₁ hop
  have hAT' : AliasTele env p₀.cvT cvS cvTa (p₀.nP + p₀.nIdx) s := by
    rw [hcvT, hnP, hnIdx]
    exact hAT
  have hguardAt : AliasGuardAt calls t E env n B p₀ cvS ctorsA rawTypes s := by
    have hvalS : ValStored cvS p₀.cvT := by
      rw [hcvT]
      exact ⟨rfl, rfl, hann⟩
    have hlevel : Core.LvEq s ℓ := by
      rcases hsortRel with ⟨bs, hstS⟩ | hrep
      · exact hℓTele bs s hstS
      · have he := (hℓ.mono (shape.guardRun.heap_extends.trans shape.guardToCtors)).det hrep
        rw [he]
        exact Core.LvEq.refl _
    have htmGuard := htmT 0 (fun _ => default)
    rw [Decl.posOf_range] at htmGuard
    have hguard := shape.guardRun
    refine ⟨hvalS, by rw [hnP, hnIdx]; exact hPI, by rw [hlenP]; exact hc39,
      b, cs_chk, shape.guardCalls, shape.sortAfter, shape.guardAfter, tyPtr, blkPtr,
      shape.sortLevel, shape.guardResult, ℓ, hb_eq, hTname, hcloadT, ?_, hsub_chk,
      hg_chk, shape.guardSubset,
      htmGuard.mono (native.initialToShape.trans shape.initial_to_guard),
      Bytes.repAddressRef_heapMono₂ Core.addrTy
        (native.initialToShape.trans shape.initial_to_guard) hb_rep,
      hℓ, hlevel, by simpa only [hnP, hnIdx, hlenP] using hguard⟩
    intro c hc
    rw [(hlps_ctors c hc).1, hcvT]
    simp
  have hzeroChoice : cvTa = cvS ∨ ∀ cA ∈ ctorsA,
      Ix.Kernel.Semantics.ctorZeroOk p₀.cvT.name (Ix.Kernel.Level.zeronessOf s) cA.1.type = true := by
    rcases hchoice with same | ⟨testResult, testAfter, testCalls, secondTest, notTele⟩
    · exact Or.inl same
    · right
      obtain ⟨sortss, -, houtFalse⟩ := houts false
      have hfields : ∀ j < p₀.ctors.length, ∀ c cvCa,
          p₀.ctors[j]? = some c → ctorsA[j]? = some (cvCa, c.2) →
          ∃ rcbs rargs cbs eargs us,
            (rawTypes.getD j default).stripPis (p₀.nP + c.2) =
              some (rcbs, Ix.Kernel.Expr.mkAppN (.const p₀.cvT.name us) rargs) ∧
            cvCa.type.stripPis (p₀.nP + c.2) =
              some (cbs, Ix.Kernel.Expr.mkAppN (.const p₀.cvT.name us) eargs) ∧
            ∀ idx, p₀.nP ≤ idx → idx < p₀.nP + c.2,
              Ix.Kernel.Semantics.famHead p₀.cvT.name (cbs.getD idx default).1 = false ∨
                Decl.RawRecSpine p₀.cvT.name (rcbs.getD idx default).1 (cbs.getD idx default).1 := by
        intro j hj c cvCa hc hcA
        obtain ⟨c', cA', sorts, hc', hcA', -, ho⟩ := houtFalse j hj
        have ec : c' = c := Option.some.inj (hc'.symm.trans hc)
        have eA : cA' = (cvCa, c.2) := Option.some.inj (hcA'.symm.trans hcA)
        subst c' cA'
        obtain ⟨rcbs, rargs, cbs, es, hsR, -, hsE, -, -, -, -, hsp⟩ := ho.residual
        refine ⟨rcbs, rargs, cbs, Ix.Kernel.structPsAt c.2 p₀.nP ++ es,
          p₀.cvT.levelParams.map .param, hsR, hsE, ?_⟩
        intro idx hlo hhi
        have hi : idx - p₀.nP < c.2 := by omega
        have he : idx = p₀.nP + (idx - p₀.nP) := by omega
        rw [he]
        rcases hsp (idx - p₀.nP) hi with hno | hrecsp
        · exact Or.inl (Decl.famHead_eq_false_of_mentionsConst_false hno)
        · exact Or.inr hrecsp
      have htmGuard := htmT 0 (fun _ => default)
      rw [Decl.posOf_range] at htmGuard
      have hlevel : Core.LvEq s ℓ := by
        rcases hsortRel with ⟨bs, hstS⟩ | hrep
        · exact hℓTele bs s hstS
        · have he := (hℓ.mono (shape.guardRun.heap_extends.trans shape.guardToCtors)).det hrep
          rw [he]
          exact Core.LvEq.refl _
      have hguard := Decl.former_decl_ok_observed_from_fields (c := ⟨E, env, t, some n⟩)
        htwf (by rw [hnP, hnIdx]; exact hPI) (by rw [hlenP]; exact hc39) hg_chk.2
        (by rw [hb_eq]; exact hTname)
        (fun c hc => by rw [(hlps_ctors c hc).1, hcvT]; simp)
        hcloadT hfields shape.guardSubset (hg_chk.sub shape.guardSubset)
        (htmGuard.mono (native.initialToShape.trans shape.initial_to_guard))
        (Bytes.repAddressRef_heapMono₂ Core.addrTy
          (native.initialToShape.trans shape.initial_to_guard) hb_rep)
        hℓ (by simpa only [hnP, hnIdx, hlenP] using shape.guardRun)
      rcases hguard with ⟨firstAfter, firstCalls, firstTest⟩ | ⟨-, hzeros⟩
      · have firstTest' : ObsFn Core.W "KernelCheck::former_is_tele"
            [tyPtr, .field ((ind.params.toNat + ind.indices.toNat : Nat) : F)]
            shape.sortAfter (.field 1) firstAfter firstCalls := by
          simpa only [hnP, hnIdx] using firstTest
        exact (notTele (Decl.former_is_tele_one_stable hPI shape.guardRun.heap_extends
          firstTest' secondTest)).elim
      · intro cA hcA
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcA
        have hz := hzeros j (List.getElem?_eq_some_iff.mp hj).1 cA hj
        rw [← Core.zeronessOf_congr hlevel] at hz
        exact hz
  refine ⟨cvS, cvTa, s, ctorsA, rawTypes, hcheckT, hAT', hTname.symm, htyT.name_eq,
    htyT.levelParams_eq, hcloadT.1, hparam', houts, hguardAt, hzeroChoice, ?_⟩
  -- the later-use condition, from the loop's positivity scans
  intro cA hcA cbs body hstrip i hi hkind
  obtain ⟨j, hjA⟩ := List.mem_iff_getElem?.mp hcA
  have hjP : j < p₀.ctors.length := by
    rw [← hcloadT.1]
    exact (List.getElem?_eq_some_iff.mp hjA).1
  obtain ⟨c, cvCa₀, hc, hcA', hvs, hload⟩ := hcloadT.2 j hjP
  rw [hjA] at hcA'
  injection hcA' with hcAeq
  subst hcAeq
  obtain ⟨sortss, -, hout⟩ := houts false
  obtain ⟨c', cA', sorts, hc', hcA'', -, hout_j⟩ := hout j hjP
  rw [hc] at hc'
  injection hc' with hceq
  subst hceq
  rw [hjA] at hcA''
  injection hcA'' with hcAeq'
  subst hcAeq'
  obtain ⟨rcbs, rargs, cbs', es, hstR, -, hstA, -, -, -, -, -⟩ := hout_j.residual
  have hstrip' : (cvCa₀, c.2).1.type.stripPis (p₀.nP + c.2) = some (cbs, body) := hstrip
  rw [hstA] at hstrip'
  injection hstrip' with hcbs
  injection hcbs with hcbs _
  subst hcbs
  have hmen : (cbs'.getD (p₀.nP + i) default).1.mentionsConst p₀.cvT.name = true := by
    cases hm : (cbs'.getD (p₀.nP + i) default).1.mentionsConst p₀.cvT.name with
    | true => rfl
    | false =>
      exfalso
      have hord : Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs'.getD (p₀.nP + i) default).1 = .ordinary := by
        unfold Ix.Kernel.recFieldKind
        rw [hm]
        simp
      rcases hkind with h | h <;> rw [hord] at h <;> cases h
  have hjs : j < ind.ctors.size := by
    rw [← hlenP]
    exact hjP
  obtain ⟨bp, ptr', h1, h1', cs1, nl, tyv, pb, mi, sl, np, nf, us, h2, h2', r, cs2, ev_load,
    hsub1, hbp, hldv, e12, ev_pos, hsub2⟩ :=
    Decl.native_ctor_positivity_slots (b := b) (nP := ind.params.toNat) (i := 0) hc56
      ind.ctors.size 0 (by omega) shape.ctorSubset hbRepCtor ctorRun₀ j (Nat.zero_le _) hjs
  obtain ⟨nl', cty, cblk, cnp, cnf, b_c, hld', -, -, hrawT, -, -, -⟩ :=
    hload bp ptr' h1 h1' cs1 hsub1 hbp ev_load
  have hval := Except.ok.inj (hldv.symm.trans hld')
  simp only [Value.construct.injEq, List.cons.injEq, true_and, and_true] at hval
  obtain ⟨-, htyv, -⟩ := hval
  have hlpsA : cvCa₀.levelParams = List.range ind.lvls.toNat := by
    rw [hvs.2.1, (hlps_ctors c (List.mem_of_getElem? hc)).1, hcvT]
  have hcty : Decl.RawTmExact (L1.traceRecordCtx ⟨E, env, t, some n⟩ cs_chk).κ 0
      (fun _ => default) h2 0 (rawTypes.getD j default) cvCa₀.type tyv := by
    have h := (hrawT 0 (fun _ => default)).mono e12
    rw [hlpsA, Decl.posOf_range, ← htyv] at h
    exact h
  rw [← hnP] at ev_pos
  exact Decl.check_positivity_later_spec (c := L1.traceRecordCtx ⟨E, env, t, some n⟩ cs_chk)
    (by rw [hnP]; omega) (hraw_at env).2 (hraw_at env).1 (hg_chk.sub hsub2)
    (L1.traceRecordCtx_coverage _ hsub2) hcty hout_j.noProj hstR hstA
    (Bytes.repAddressRef_heapMono₂ Core.addrTy (ev_load.heap_extends.trans e12) hbp) ev_pos
    i hi hmen


/-- The retained-guard result, forgetting only the newly produced zero-ness alternative. -/
theorem aliasOuts_of_member_guard {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hconv : FormerTeleConv)
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Model.nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀)
    (hnIdx : p₀.nIdx = ind.indices.toNat) (hn : ind.indices.toNat ≠ 0)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : L1.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    ∃ (cvS cvTa : ConstantVal .anon) (s : Ix.Kernel.Level)
      (ctorsA : List (ConstantVal .anon × Nat)) (rawTypes : List (Ix.Kernel.Expr .anon)),
      Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT cvS ∧
      AliasTele env p₀.cvT cvS cvTa (p₀.nP + p₀.nIdx) s ∧
      cvS.name = p₀.cvT.name ∧ cvTa.name = cvS.name ∧ cvTa.levelParams = cvS.levelParams ∧
      ctorsA.length = p₀.ctors.length ∧
      (p₀.ctors ≠ [] → ∀ tfvs r₁, Ix.Kernel.openPisAtFvars p₀.nP cvS.type 0 = some (tfvs, r₁) →
        ∃ r₂, Ix.Kernel.openPisAtFvars p₀.nP cvTa.type 0 = some (tfvs, r₂)) ∧
      (∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
        sortss.length = p₀.ctors.length ∧
        ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
          sortss[j]? = some sorts ∧
          Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
              (p₀.toInductiveShape.withSort s) isRec) :: env.consts⟩
            p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx s cvS.type
            (rawTypes.getD j default) c cA sorts) ∧
      AliasGuardAt calls t E env n B p₀ cvS ctorsA rawTypes s ∧
      (∀ cA ∈ ctorsA, ∀ cbs body, cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
        ∀ i < cA.2,
          (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
           Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
          Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) := by
  obtain ⟨cvS, cvTa, s, ctorsA, rawTypes, hcheck, htele, hnS, hnT, hlT, hlen,
    hparam, houts, hguard, -, hunused⟩ := aliasOuts_of_member_checked ht hS hst hrec hchk
      hnat hblk hp₀ hnIdx hn hinv hstored hP hkeys hfresh hfree hcov haux
  exact ⟨cvS, cvTa, s, ctorsA, rawTypes, hcheck, htele, hnS, hnT, hlT, hlen,
    hparam, houts, hguard, hunused⟩

/-- The original two-stage result, forgetting only the retained guard observation. -/
theorem aliasOuts_of_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hconv : FormerTeleConv)
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Model.nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀)
    (hnIdx : p₀.nIdx = ind.indices.toNat) (hn : ind.indices.toNat ≠ 0)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : L1.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    ∃ (cvS cvTa : ConstantVal .anon) (s : Ix.Kernel.Level)
      (ctorsA : List (ConstantVal .anon × Nat)) (rawTypes : List (Ix.Kernel.Expr .anon)),
      Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT cvS ∧
      AliasTele env p₀.cvT cvS cvTa (p₀.nP + p₀.nIdx) s ∧
      cvS.name = p₀.cvT.name ∧ cvTa.name = cvS.name ∧ cvTa.levelParams = cvS.levelParams ∧
      ctorsA.length = p₀.ctors.length ∧
      (p₀.ctors ≠ [] → ∀ tfvs r₁, Ix.Kernel.openPisAtFvars p₀.nP cvS.type 0 = some (tfvs, r₁) →
        ∃ r₂, Ix.Kernel.openPisAtFvars p₀.nP cvTa.type 0 = some (tfvs, r₂)) ∧
      (∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
        sortss.length = p₀.ctors.length ∧
        ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
          sortss[j]? = some sorts ∧
          Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
              (p₀.toInductiveShape.withSort s) isRec) :: env.consts⟩
            p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx s cvS.type
            (rawTypes.getD j default) c cA sorts) ∧
      (∀ cA ∈ ctorsA, ∀ cbs body, cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
        ∀ i < cA.2,
          (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
           Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
             (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
          Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) := by
  obtain ⟨cvS, cvTa, s, ctorsA, rawTypes, hcheck, htele, hnS, hnT, hlT, hlen,
    hparam, houts, -, hunused⟩ := aliasOuts_of_member_guard hconv ht hS hst hrec hchk hnat hblk
      hp₀ hnIdx hn hinv hstored hP hkeys hfresh hfree hcov haux
  exact ⟨cvS, cvTa, s, ctorsA, rawTypes, hcheck, htele, hnS, hnT, hlT, hlen,
    hparam, houts, hunused⟩

end IxVM.Refinement.Typing
