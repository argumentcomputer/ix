import IxVMRefinement.Assembly.NativeBlockOutsNamedLim
import IxVMRefinement.Assembly.NativeBlockOutsRawLim
import IxVMRefinement.Assembly.NativeBlockInstallOf
import IxVMRefinement.Assembly.NativeBlockRetHead
import IxVMRefinement.Assembly.NativeBlockNoProjOf
import IxVMRefinement.Assembly.NativeBlockCertOf

/-! # The install of a native block read off the member check, at either role context

The walk exports the check of a block's member under the role context of its validator: at a
group limit, or with the binding assumed (`Claim.MemberCheckedLimAt … lim`, `lim : Option
Nat`). The constructor stage and the install of a one-type native block whose former is
declared at its telescope were stated for a context at a group limit only. This module states
them for either context, beside the earlier ones, with the same proofs: none of them reads the
role context's limit, and each runs the scoped specifications at the context of the given
limit. At `lim = some n` each is the earlier statement.

* `nativeNoRecFacts_of_outs_named_with_lim`: IxC's no-recursor install from the two stages'
  outputs, with a property of the recursion flag and the sorts handed through.
* `InstallSortsCheckedLim`, `nativeInstallOut_of_member_checked_lim`: the new constants of the
  install, and the table stage ran at sorts the classifier checked. The limit index of the
  bundle it concludes is free: the bundle reads the limit nowhere.
* `blockCert_of_reading_lim`: the certificate of the new projection table from them and the
  reading of the checked field loop over a store, which need not be the store of the check.
* `blockRawRetHead_of_member_lim`: the constructors' raw types return literally.
* `blockFamCtorNoProj_of_member_lim`: no stored constructor type projects out of the family.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open Ix.Kernel.Semantics (NativeFam)
open LoadedReads (canonAnn canonRawAnn)

universe u

/-- **IxC's no-recursor install of the block, from the outputs of its two stages, with the family named and a property of the sorts handed through, at either role context**: `nativeNoRecFacts_of_outs_named_with` with the member's check read under the
role context of the limit `lim : Option Nat` (`Claim.MemberCheckedLimAt`) and the prefix
invariant at that limit; the same proof. -/
theorem nativeNoRecFacts_of_outs_named_with_lim {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {lim : Option Nat} (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon} {Q : Bool → List (List Ix.Kernel.Level) → Prop}
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t lim env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (haux : Decl.AuxRootSynced env)
    {cvS : ConstantVal .anon} {bsT : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)}
    {ctorsA : List (ConstantVal .anon × Nat)} {rawTypes : List (Ix.Kernel.Expr .anon)}
    (hcheckT : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT cvS)
    (hstS : cvS.type.stripPis (p₀.nP + p₀.nIdx) = some (bsT, .sort p₀.resSort))
    (hnameS : cvS.name = p₀.cvT.name) (hlenA : ctorsA.length = p₀.ctors.length)
    (hout : ∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
      sortss.length = p₀.ctors.length ∧
      (∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
        sortss[j]? = some sorts ∧
        Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx p₀.resSort cvS.type
          (rawTypes.getD j default) c cA sorts) ∧ Q isRec sortss)
    (hunused : ∀ cA ∈ ctorsA, ∀ cbs body,
      cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2,
        (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
        Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) :
    ∃ (env₂ : Ix.Kernel.Env .anon) (p : Ix.Kernel.NativeParts .anon),
      NativeNoRecFacts env env₂ blk ind.params.toNat p₀ ⟨p, cvS, cvS, ctorsA⟩ ∧
      ∃ (isRec : Bool) (sortss : List (List Ix.Kernel.Level)), Q isRec sortss ∧
        Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss
          (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩) = .ok env₂ ∧
        p.resSort = p₀.resSort := by
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape_lim ht hbound hS hrec hchk hblk
  obtain ⟨caps₀, hshape, -, -, -, -, -, -⟩ := Decl.nativePartsNoRec?_inv hp₀
  injection hshape with hhead hcs_eq
  injection hhead with hcv _
  have hTname : p₀.cvT.name = keyOf t (memberAddr B 0 (.indc ind)) := by
    rw [← hcv]
  -- each constructor of the recognised block is a constructor reading at its address
  have hctor : ∀ c ∈ p₀.ctors, ∃ j, j < ind.ctors.size ∧
      ∃ (ct : Ixon.Constructor) (tyj : Ix.Kernel.Expr .anon),
        c.1 = ⟨keyOf t (ctorAddr B 0 j), List.range ct.lvls.toNat, tyj⟩ ∧
        (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read
          ct.typ = .ok tyj := by
    intro c hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    have hcsj : cs[j]? = some (.ctorInfo c.1 p₀.nP c.2) := by
      rw [hcs_eq]
      simp [hj]
    have hjlt : j < ind.ctors.size := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.mp hcsj).1
    obtain ⟨ct, tyj, -, -, -, -, htyj, hceq, -⟩ := hcs j _ hcsj
    injection hceq with hc1 _ _
    exact ⟨j, hjlt, ct, tyj, hc1, htyj⟩
  have hfresh_ctors : ∀ c ∈ p₀.ctors, env.find? c.1.name = none := by
    intro c hc
    obtain ⟨j, hj, ct, tyj, hc1, -⟩ := hctor c hc
    rw [hc1]
    exact hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hfv_ctors : ∀ c ∈ p₀.ctors, c.1.type.hasFvar = false := by
    intro c hc
    obtain ⟨j, hj, ct, tyj, hc1, htyj⟩ := hctor c hc
    rw [hc1]
    exact Assembly.memberReader_read_noFvar htyj
  have hshape_ctors : ∀ c ∈ p₀.ctors, c.1.name.isProjFnShape = false := by
    intro c hc
    obtain ⟨j, hj, ct, tyj, hc1, -⟩ := hctor c hc
    rw [hc1]
    exact Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hT_ctors : ∀ c ∈ p₀.ctors, c.1.name ≠ p₀.cvT.name := by
    intro c hc e
    obtain ⟨j, hj, ct, tyj, hc1, -⟩ := hctor c hc
    rw [hc1, hTname] at e
    have ha : ctorAddr B 0 j = memberAddr B 0 (.indc ind) := Core.keyOf_inj htwf e
    have h1 := hrec.ctors j hj
    rw [ha, hrec.former] at h1
    have hinfo := congrArg Ixon.Constant.info (Option.some.inj h1)
    simp [memberProjection, constructorProjection] at hinfo
  -- the family's key and its projection names are fresh in the prefix
  have hfreshT : env.find? p₀.cvT.name = none := by
    rw [hTname]
    exact hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hbaseT : p₀.cvT.name.base = p₀.cvT.name := by
    rw [hTname]
    exact Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hfn : ∀ j, env.find? (Ix.Kernel.projFnName p₀.cvT.name j) = none := fun j =>
    haux.fresh_of_base_none (by
      show env.find? p₀.cvT.name.base = none
      rw [hbaseT]
      exact hfreshT)
  have htbl : env.find? (Ix.Kernel.projTableName p₀.cvT.name) = none :=
    haux.fresh_of_base_none (by
      show env.find? p₀.cvT.name.base = none
      rw [hbaseT]
      exact hfreshT)
  have hshapeT : cvS.name.isProjFnShape = false := by
    rw [hnameS, hTname]
    exact Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  exact Decl.nativeNoRecFacts_of_stage_named_with hp₀ hnd hinv.store.store hcheckT hstS hnameS
    (by rw [hnameS]; exact hfreshT) hshapeT hlenA hout hfv_ctors hfresh_ctors hshape_ctors
    hT_ctors hfn htbl hunused


/-- **The table stage of a native block's install ran at sorts the classifier checked, at either role context**: `InstallSortsChecked` with
the stage's facts at the context of the limit `lim : Option Nat` (`StageSortsCheckedLim`). -/
def InstallSortsCheckedLim (calls : List (Call F)) (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (lim : Option Nat)
    (env : Ix.Kernel.Env .anon) (B : _root_.Address) (cvS : ConstantVal .anon)
    (p₀ : Ix.Kernel.NativeParts .anon) (new : List (ConstantInfo .anon))
    (p : Ix.Kernel.NativeParts .anon) (ctorsA : List (ConstantVal .anon × Nat)) : Prop :=
  ∃ (isRec : Bool) (sortss : List (List Ix.Kernel.Level)),
    StageSortsCheckedLim calls t E lim env B cvS p₀ ctorsA isRec sortss ∧
    Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss
      (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
        (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩) =
      .ok ⟨new ++ env.consts⟩ ∧
    p.resSort = p₀.resSort


/-- **The new constants of a native block's install, read off the member check, with the sorts of its table stage, at either role context**: `nativeInstallOut_of_member_checked` with the member's check read under the
role context of the limit `lim : Option Nat` (`Claim.MemberCheckedLimAt`) and the prefix
invariant at that limit; the same proof. -/
theorem nativeInstallOut_of_member_checked_lim {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} {lim : Option Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t lim env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env)
    (hndE : (env.consts.map (·.name)).Nodup) :
    ∃ (new : List (ConstantInfo .anon)) (p : Ix.Kernel.NativeParts .anon)
      (ty' : Ix.Kernel.Expr .anon) (ctorsA : List (ConstantVal .anon × Nat))
      (caps : IndCaps .anon),
      NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps ∧
      InstallSortsCheckedLim calls t E lim env B
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA := by
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  obtain ⟨ty₀, ty', cvS, bsT, ctorsA, rawTypes, hty, hlbb, hdef, hcT, hcvT, hcvS, hnP₀, hnIdx₀,
    hlenP, hper, hT, hstT, hname, hlenA, hout, hun⟩ :=
    ctorOuts_of_member_named_checked_lim ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP
      hkeys hfresh hfree hcov haux
  obtain ⟨p₀', hp₀', hnd₀⟩ := nativeParts_of_member_lim ht hbound hS hrec hchk htele hblk hfree
  rw [hp₀] at hp₀'
  injection hp₀' with e
  subst e
  obtain ⟨env₂, p, hf, isRecQ, sortssQ, hQ, htabQ, hresQ⟩ := nativeNoRecFacts_of_outs_named_with_lim
    (Q := StageSortsCheckedLim calls t E lim env B cvS p₀ ctorsA) ht hS hst hrec hchk hblk hp₀ hnd₀
    hinv hfresh haux hT hstT hname hlenA hout hun
  subst hcvS
  obtain ⟨isRec, s, kinds, caps, tbls, hpEq, hcapsAt, hcapsP, henv₂, htbls⟩ := hf.named_env
  subst henv₂
  -- the family's counts and key
  have hpcvT : p.cvT = p₀.cvT := by rw [hpEq]; rfl
  have hpnP : p.nP = p₀.nP := by rw [hpEq]; rfl
  have hpnIdx : p.nIdx = p₀.nIdx := by rw [hpEq]; rfl
  have hlenA' : ctorsA.length = ind.ctors.size := hlenA.trans hlenP
  have hfreshT : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none :=
    hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)
  have hfreshC : ∀ j < ind.ctors.size, env.find? (keyOf t (ctorAddr B 0 j)) = none :=
    fun j hj => hfresh _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩)
  have hbaseT : (Core.keyOf t (Core.iprjAddr B 0)).base = Core.keyOf t (Core.iprjAddr B 0) :=
    Decl.base_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have htbl : env.find? (Ix.Kernel.projTableName (Core.keyOf t (Core.iprjAddr B 0))) = none :=
    haux.fresh_of_base_none (by
      show env.find? (Core.keyOf t (Core.iprjAddr B 0)).base = none
      rw [hbaseT]; exact hfreshT)
  have hTC : ∀ j < ind.ctors.size,
      keyOf t (ctorAddr B 0 j) ≠ Core.keyOf t (Core.iprjAddr B 0) := by
    intro j hj e
    have ha : ctorAddr B 0 j = memberAddr B 0 (.indc ind) := Core.keyOf_inj htwf e
    have h1 := hrec.ctors j hj
    rw [ha, hrec.former] at h1
    have hinfo := congrArg Ixon.Constant.info (Option.some.inj h1)
    simp [memberProjection, constructorProjection] at hinfo
  -- the constructors
  have hcOf : ∀ j < ind.ctors.size, ∃ c, p₀.ctors[j]? = some c := fun j hj =>
    ⟨p₀.ctors[j], List.getElem?_eq_getElem (by omega)⟩
  have hctorMem : ∀ cA ∈ ctorsA, ∃ j c, j < ind.ctors.size ∧ p₀.ctors[j]? = some c ∧
      ctorsA[j]? = some cA := by
    intro cA hcA
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hcA
    have hjlt : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjp : j < p₀.ctors.length := by omega
    exact ⟨j, p₀.ctors[j], by omega, List.getElem?_eq_getElem hjp, hj⟩
  have hnames : p₀.ctors.map (·.1.name) = ctorsA.map (·.1.name) := by
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_map, List.getElem?_map]
    cases hc : p₀.ctors[j]? with
    | none =>
      have h0 : ctorsA[j]? = none := by
        rw [List.getElem?_eq_none_iff] at hc ⊢
        omega
      rw [h0]
    | some c =>
      obtain ⟨ct, cty', -, -, -, -, -, -, -, -, -, -, -, hA⟩ := hper j c hc
      rw [hA]
      rfl
  -- every new constructor is a canonical constructor of the block
  have hrevMem : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse,
      ∃ j c cty', j < ind.ctors.size ∧ p₀.ctors[j]? = some c ∧
        ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) ∧
        ci = .ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 := by
    intro ci hci
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hci)
    obtain ⟨j, c, hj, hc, hA⟩ := hctorMem cA hcA
    obtain ⟨ct, cty', -, -, -, -, -, -, -, -, -, -, -, hA'⟩ := hper j c hc
    rw [hA] at hA'
    injection hA' with hA'
    subst hA'
    exact ⟨j, c, cty', hj, hc, hA, rfl⟩
  have hrevName : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse,
      ∃ j < ind.ctors.size, ci.name = keyOf t (ctorAddr B 0 j) := by
    intro ci hci
    obtain ⟨j, c, cty', hj, hc, -, rfl⟩ := hrevMem ci hci
    obtain ⟨ct, cty'', -, -, -, -, hcn, -⟩ := hper j c hc
    exact ⟨j, hj, hcn⟩
  -- distinct names, fresh in the prefix
  have hndRev : ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse.map
      (·.name)).Nodup := by
    rw [List.map_reverse, List.nodup_reverse, List.map_map]
    have hf : ((·.name) ∘ fun c : ConstantVal .anon × Nat => ConstantInfo.ctorInfo c.1 p.nP c.2) =
        fun c => c.1.name := rfl
    rw [hf, ← hnames]
    exact hnd₀
  have hndL1 : (([ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0),
      List.range ind.lvls.toNat, ty'⟩ caps] ++ env.consts).map (·.name)).Nodup := by
    refine nodup_names_append (by simp) hndE ?_
    intro a ha b hb
    rw [List.mem_singleton.mp ha]
    exact (name_ne_of_find_none hfreshT b hb).symm
  have hndL2 : (((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      ([ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0),
      List.range ind.lvls.toNat, ty'⟩ caps] ++ env.consts)).map (·.name)).Nodup := by
    refine nodup_names_append hndRev hndL1 ?_
    intro a ha b hb
    obtain ⟨j, hj, hn⟩ := hrevName a ha
    rw [hn]
    rcases List.mem_append.mp hb with hb | hb
    · rw [List.mem_singleton.mp hb]
      exact hTC j hj
    · exact (name_ne_of_find_none (hfreshC j hj) b hb).symm
  have hndAll : (((tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        caps])) ++ env.consts).map (·.name)).Nodup := by
    rw [List.append_assoc, List.append_assoc]
    rcases htbls with rfl | ⟨tbl, rfl, hsn⟩
    · simpa using hndL2
    · refine nodup_names_append (by simp) hndL2 ?_
      intro a ha b hb
      rw [List.mem_singleton.mp ha]
      show Ix.Kernel.projTableName tbl.structName ≠ b.name
      rw [hsn, hpcvT, hcvT]
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨j, hj, hn⟩ := hrevName b hb
        rw [hn]
        exact (Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)).symm
      · rcases List.mem_append.mp hb with hb | hb
        · rw [List.mem_singleton.mp hb]
          exact (Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)).symm
        · exact (name_ne_of_find_none htbl b hb).symm
  have hfind : ∀ ci ∈ tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        caps]),
      (⟨(tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
          caps])) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? ci.name = some ci :=
    fun ci hci => find_of_mem_nodup hndAll (List.mem_append_left _ hci)
  have hmemF : ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat,
      ty'⟩ caps ∈ tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
        caps]) := by simp
  have hmemC : ∀ (j : Nat) (c : ConstantVal .anon × Nat) (cty' : Ix.Kernel.Expr .anon),
      p₀.ctors[j]? = some c →
      ctorsA[j]? = some (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) →
      ConstantInfo.ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 ∈
        tbls ++ ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [ConstantInfo.indInfo ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩
          caps]) := by
    intro j c cty' hc hA
    have h1 : ((⟨c.1.name, c.1.levelParams, cty'⟩, c.2) : ConstantVal .anon × Nat) ∈ ctorsA :=
      List.mem_of_getElem? hA
    have h2 : ConstantInfo.ctorInfo ⟨c.1.name, c.1.levelParams, cty'⟩ p.nP c.2 ∈
        ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2) :=
      List.mem_map.mpr ⟨_, h1, rfl⟩
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.mpr h2))
  -- the block's readings
  obtain ⟨fr, cs, hblkEq, hfrR, hlenC, hcsR⟩ := id hblk
  obtain ⟨caps₀, hshape, -, -, -, -, -, -⟩ := Decl.nativePartsNoRec?_inv hp₀
  rw [hshape] at hblkEq
  injection hblkEq with hfr hcs
  subst hfr hcs
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  refine ⟨_, p, ty', ctorsA, caps, {
    facts := hf
    install := ?_
    caps_eq := hcapsP
    nodup := ?_
    fresh := ?_
    reads := ?_
    named := ?_
    ctors := ?_
    lenA := hlenA'
    nP := hpnP.trans hnP₀
    nIdx := hpnIdx.trans hnIdx₀
    nP₀ := hnP₀
    nIdx₀ := hnIdx₀
    cvT := hpcvT
    cvT₀ := by rw [hcvT]; exact ⟨rfl, rfl⟩
    ctorNames := hnames
    formerFind := hfind _ hmemF
    ctorFind := fun cA hcA => hfind (.ctorInfo cA.1 p.nP cA.2)
      (List.mem_append_right _ (List.mem_append_left _
        (List.mem_reverse.mpr (List.mem_map.mpr ⟨cA, hcA, rfl⟩))))
    tableName := ?_ }, isRecQ, sortssQ, hQ, htabQ, hresQ⟩
  · -- the new constants as the store reads them
    obtain ⟨hp56, hi56, hc56⟩ := member_bounds_lim hbound hS hrec hchk
    exact {
      check := ht
      decoded := hst.decoded
      held := hP
      block := hblockE
      muts := hrec.muts
      formerRec := (recordOf_eq_recordAt_of_decoded hst.decoded _).trans
        (hst.runRecord _ _ hrec.former)
      ctorRec := fun j hj => (recordOf_eq_recordAt_of_decoded hst.decoded _).trans
        (hst.runRecord _ _ (hrec.ctors j hj))
      bounds := ⟨hp56, hi56, hc56⟩
      used := usedRefsStored_append hstored _
      former := ⟨ty₀, ty', hty, hlbb, hdef, hcT, hfind _ hmemF⟩
      ctor := by
        intro j hj
        obtain ⟨c, hc⟩ := hcOf j hj
        obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
          hper j c hc
        rw [ZMod.val_zero] at hcan
        refine ⟨ct, c.1.type, cty', hct, hcidx, hrd, hclbb, hcdef, hcan, ?_⟩
        have hf' := hfind _ (hmemC j c cty' hc hA)
        have hnP' : p.nP = ct.params.toNat := hpnP.trans (hnP₀.trans hcp.symm)
        rw [hcn, hclp, hc2] at hf'
        rw [← hnP']
        exact hf'
      newName := by
        intro ci hci
        rcases List.mem_append.mp hci with hci | hci
        · rcases htbls with rfl | ⟨tbl, rfl, -⟩
          · simp at hci
          · exact Or.inr (Or.inr ⟨tbl, List.mem_singleton.mp hci⟩)
        · rcases List.mem_append.mp hci with hci | hci
          · obtain ⟨j, hj, hn⟩ := hrevName ci hci
            exact Or.inr (Or.inl ⟨j, hj, hn⟩)
          · rw [List.mem_singleton.mp hci]
            exact Or.inl rfl
      newFind := hfind
      unit := by
        intro hi0 hsz hf0
        obtain ⟨c, hc1⟩ := List.length_eq_one_iff.mp (hlenP.trans hsz)
        have hc0 : p₀.ctors[0]? = some c := by rw [hc1]; rfl
        obtain ⟨ct, cty', hct, -, -, -, -, -, hc2, -⟩ := hper 0 c hc0
        have hcf : c.2 = 0 := hc2.trans (hf0 ct hct)
        have hcs1 : (p₀.toInductiveShape.withSort s).ctors = [c] := hc1
        rw [hcapsAt]
        unfold Ix.Kernel.nativeCapsAt
        rw [hcs1]
        have hidx : (p₀.toInductiveShape.withSort s).nIdx = 0 := hnIdx₀.trans hi0
        have hnp : (p₀.toInductiveShape.withSort s).nP = ind.params.toNat := hnP₀
        simp [hidx, hnp, hcf, hnIdx₀, hi0, hnP₀]
      free := (hfree _ (Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩)).1 }
  · have h := hndAll
    rw [List.map_append] at h
    exact (List.nodup_append.mp h).1
  · intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · rcases htbls with rfl | ⟨tbl, rfl, hsn⟩
      · simp at hci
      · rw [List.mem_singleton.mp hci]
        show env.find? (Ix.Kernel.projTableName tbl.structName) = none
        rw [hsn, hpcvT, hcvT]
        exact htbl
    · rcases List.mem_append.mp hci with hci | hci
      · obtain ⟨j, hj, hn⟩ := hrevName ci hci
        rw [hn]
        exact hfreshC j hj
      · rw [List.mem_singleton.mp hci]
        exact hfreshT
  · intro x hx
    rcases hx with ⟨-, hs⟩ | ⟨ms', i, mi, hms', hmi, hx⟩
    · exact (standalone_not_block hs ⟨_, hrec.muts⟩).elim
    · rw [hrec.muts] at hms'
      have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj hms').symm
      subst hmsEq
      have hi : i = 0 := by
        have := (Array.getElem?_eq_some_iff.mp hmi).1
        simp at this
        omega
      subst hi
      have hmiEq : mi = .indc ind := by simpa using hmi.symm
      subst hmiEq
      rcases hx with rfl | ⟨ind', j, hind', hj, rfl⟩
      · refine ⟨_, hmemF, _, rfl, hfrR, ?_⟩
        unfold StoredAs
        refine ⟨?_, trivial⟩
        unfold ValStored
        rw [hcvT]
        exact ⟨rfl, rfl, canonAnn_annotates hcT⟩
      · injection hind' with hind'
        subst hind'
        obtain ⟨c, hc⟩ := hcOf j hj
        obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
          hper j c hc
        have hcsj : (p₀.ctors.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2))[j]? =
            some (.ctorInfo c.1 p₀.nP c.2) := by
          rw [List.getElem?_map, hc]
          rfl
        refine ⟨_, hmemC j c cty' hc hA, _, hcn, hcsR j _ hcsj, ?_⟩
        unfold StoredAs
        refine ⟨?_, hpnP, rfl⟩
        unfold ValStored
        exact ⟨rfl, rfl, canonAnn_annotates hcan⟩
  · intro ci hci
    rcases List.mem_append.mp hci with hci | hci
    · rcases htbls with rfl | ⟨tbl, rfl, -⟩
      · simp at hci
      · rw [List.mem_singleton.mp hci]
        exact Or.inr ⟨tbl.structName, .projTable, rfl⟩
    · rcases List.mem_append.mp hci with hci | hci
      · obtain ⟨j, hj, hn⟩ := hrevName ci hci
        exact Or.inl ⟨ctorAddr B 0 j,
          Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inr ⟨ind, j, rfl, hj, rfl⟩⟩, hn⟩
      · rw [List.mem_singleton.mp hci]
        exact Or.inl ⟨memberAddr B 0 (.indc ind),
          Or.inr ⟨_, 0, .indc ind, hrec.muts, rfl, Or.inl rfl⟩, rfl⟩
  · intro j hj
    obtain ⟨c, hc⟩ := hcOf j hj
    obtain ⟨ct, cty', hct, hcidx, hcp, hcl, hcn, hclp, hc2, hrd, hclbb, hcdef, hcan, hA⟩ :=
      hper j c hc
    refine ⟨ct, cty', hct, hcl, hcp, ?_⟩
    rw [hA, hcn, hclp, hc2]
    rfl
  · intro tbl htm
    rcases List.mem_append.mp htm with h | h
    · rcases htbls with rfl | ⟨tbl', rfl, hsn⟩
      · simp at h
      · have e : tbl = tbl' := by
          have h' := List.mem_singleton.mp h
          injection h'
        rw [e, hsn, hpcvT, hcvT]
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨j, c, cty', -, -, -, he⟩ := hrevMem _ h
        exact nomatch he
      · exact nomatch List.mem_singleton.mp h


/-- **The new table's certificate over a store, from the install's output, the sorts of its table stage and the reading of the checked field loop over that store, at either role context**: `blockCert_of_reading` with the stage's facts at the context of the limit `lim : Option Nat`
(`InstallSortsCheckedLim`) and the reading over any store `Er`; the same proof. The limit index
of the install's output is free. -/
theorem blockCert_of_reading_lim
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env} {n : Nat} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} {B : _root_.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)}
    {caps : IndCaps .anon}
    {Er : Ixon.Env} (hfields : Guard.CheckedSortsReadingAtBlock calls Er B)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps)
    (hS : InstallSortsCheckedLim calls t E lim env B
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ p₀ new p ctorsA)
    (h1 : ind.ctors.size = 1) (h0 : ind.indices.toNat = 0)
    (hz : Ix.Kernel.Level.isEquiv p.resSort .zero = some true) :
    BlockCert t Er ⟨new ++ env.consts⟩ B := by
  intro tbl htbl hprop
  obtain ⟨isRec, sortss, hQ, htab, hres⟩ := hS
  have hlenP : p₀.ctors.length = 1 := by
    have h := congrArg List.length hO.ctorNames
    simp only [List.length_map] at h
    rw [h, hO.lenA]
    exact h1
  have hzero : ∀ φ : Ix.Kernel.LevelParam → Nat, Ix.Kernel.Level.eval φ p₀.resSort = 0 := by
    intro φ
    rw [← hres]
    exact Decl.eval_zero_of_isEquiv_zero (by rw [hz]; rfl) φ
  obtain ⟨b, u, cA, sorts, hbB, hcA, hsorts, hcS, hchk⟩ := hQ hlenP (hO.nIdx₀.trans h0) hzero
  subst hcA hsorts
  -- the loop's reading at the sorts the table stage ran at
  obtain ⟨sigs, fuel, raw, hraw, hsig, hzeros⟩ := hfields _ hchk hbB
  have hv0 : ZMod.val (0 : F) = 0 := ZMod.val_zero
  rw [hbB, hv0] at hraw
  rw [hO.nP₀, ← hO.nP] at hsig
  -- the table the stage stores, with its certificate
  obtain ⟨tbl', -, hfind', -, -, -, hlps', cert⟩ :=
    Guard.projGuardCert_of_checkNativeTable (hO.nIdx.trans h0) htab hsig hzeros
  rw [hO.cvT, hO.cvT₀.1] at hfind'
  rw [hfind'] at htbl
  injection htbl with htbl
  injection htbl with htbl
  subst htbl
  -- the stored constructor
  obtain ⟨ct, cty', -, -, -, hA0⟩ := hO.ctors 0 (by omega)
  have hcAeq : cA = (⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat, cty'⟩,
      ct.fields.toNat) := by
    have h : some cA = some ((⟨Core.keyOf t (Core.cprjAddr B 0 0), List.range ct.lvls.toNat,
        cty'⟩, ct.fields.toNat) : ConstantVal .anon × Nat) := hA0
    exact Option.some.inj h
  have hctor := hO.ctorFind cA (List.mem_singleton.mpr rfl)
  have hname : cA.1.name = Core.keyOf t (Core.cprjAddr B 0 0) := by rw [hcAeq]
  rw [hname] at hctor
  refine ⟨cA.1, p.nP, cA.2, raw, hctor, hraw, ?_, cert⟩
  rw [hlps', hO.cvT, hO.cvT₀.2, List.length_range]


/-- **The constructors' raw types return literally, from the block step's member check, at either role context**: `blockRawRetHead_of_member` with the member's check read under the
role context of the limit `lim : Option Nat` (`Claim.MemberCheckedLimAt`) and the prefix
invariant at that limit; the same proof. -/
theorem blockRawRetHead_of_member_lim {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {lim : Option Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t lim env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    BlockRawRetHead t E B ind cb := by
  obtain ⟨ty₀, ty', cvS, bsT, ctorsA, rawTypes, hty, hlbb, hdef, hcT, hcvT, hcvS, hnP₀, hnIdx₀,
    hlenP, hper, hT, hstT, hname, hlenA, hout, hun, hc56, hrawL, -⟩ :=
    ctorOuts_of_member_raw_lim ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP hkeys
      hfresh hfree hcov haux
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hprojE : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  obtain ⟨sortss, -, houts⟩ := hout false
  refine ⟨hblockE, hprojE, hrec.muts, hc56, fun j hj => ?_⟩
  have hjP : j < p₀.ctors.length := by
    rw [hlenP]
    exact hj
  obtain ⟨c, cA, sorts, hc, -, -, hout_j⟩ := houts j hjP
  obtain ⟨ct, cty', hct, hcidx, -, -, -, -, hcf, hread, hl, hd, -, -⟩ := hper j c hc
  obtain ⟨ct', R', hct', hrc, hrj⟩ := hrawL j c hc
  have hctEq : ct' = ct := Option.some.inj (hct'.symm.trans hct)
  rw [hctEq] at hrc hrj
  obtain ⟨rcbs, rargs, -, -, hstR, -⟩ := hout_j.residual
  have hget : rawTypes.getD j default = Core.posOf (List.range ct.lvls.toNat) R' := by
    rw [List.getD_eq_getElem?_getD, hrj]
    rfl
  rw [hget, hnP₀, hcf, hcvT] at hstR
  exact ⟨ct, c.1.type, R', rcbs, rargs, hct, hcidx, hread, hl, hd, hrc, hstR⟩


/-- **No stored constructor type of the installed family projects out of it, at either role context**: `blockFamCtorNoProj_of_member` with the member's check read under the
role context of the limit `lim : Option Nat` (`Claim.MemberCheckedLimAt`) and the prefix
invariant at that limit; the same proof. -/
theorem blockFamCtorNoProj_of_member_lim {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} {lim : Option Nat} {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {p₀ p : Ix.Kernel.NativeParts .anon} {new : List (ConstantInfo .anon)}
    {ty' : Ix.Kernel.Expr .anon} {ctorsA : List (ConstantVal .anon × Nat)} {caps : IndCaps .anon}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : Claim.MemberCheckedLimAt calls bAddr t B #[.indc ind] 0 lim)
    (hnat : NativeRouteAt calls B) (htele : FormerAtTele t E₀ B cb ind)
    (hblk : BlockReadings t E₀ B ind blk)
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hinv : Decl.PrefixInv.{u} E t lim env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : Ingress.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env)
    (hO : NativeInstallOut t E₀ E n env B cb ind blk p₀ new p ty' ctorsA caps) :
    BlockFamCtorNoProj
      ⟨p, ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩,
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, ctorsA⟩ := by
  obtain ⟨ty₀', tyR, cvS, bsT, ctorsR, rawTypes, -, -, -, -, -, -, -, -, hlenP, hper, -, -, -, -,
    hout, -, -, -, -⟩ :=
    ctorOuts_of_member_raw_lim ht hS hst hrec hchk hnat htele hblk hp₀ hinv hstored hP hkeys hfresh
      hfree hcov haux
  obtain ⟨sortss, -, hsorts⟩ := hout false
  have hI := hO.install
  intro j cA hcA
  have hjI : j < ind.ctors.size := by
    have h := (List.getElem?_eq_some_iff.mp hcA).1
    rw [hO.lenA] at h
    exact h
  have hjP : j < p₀.ctors.length := by
    rw [hlenP]
    exact hjI
  -- the admission at slot `j`
  obtain ⟨c, cR, sorts, hc, hcR, -, hNCO⟩ := hsorts j hjP
  obtain ⟨ct, cty', hct, hcidx, -, -, -, -, -, hread, -, -, hcanonR, hcRj⟩ := hper j c hc
  have hcReq : cR = (⟨c.1.name, c.1.levelParams, cty'⟩, c.2) :=
    Option.some.inj (hcR.symm.trans hcRj)
  have hnp := hNCO.noProj
  rw [hcReq] at hnp
  -- the install's constructor at slot `j`
  obtain ⟨ctI, ctyI, ctyI', hctI, -, hreadI, -, -, hcanonI, hfindI⟩ := hI.ctor j hjI
  have e1 : ctI = ct := Option.some.inj (hctI.symm.trans hct)
  subst e1
  have e2 : ctyI = c.1.type := Except.ok.inj (hreadI.symm.trans hread)
  subst e2
  rw [ZMod.val_zero] at hcanonR
  have e3 : ctyI' = cty' := Option.some.inj (hcanonI.symm.trans hcanonR)
  subst e3
  obtain ⟨ct₀, cty₀, -, -, -, hA⟩ := hO.ctors j hjI
  rw [hA] at hcA
  injection hcA with hcA
  subst hcA
  have hfindA := hO.ctorFind _ (List.mem_of_getElem? hA)
  have hEq := Option.some.inj (hfindA.symm.trans hfindI)
  injection hEq with hcv hnP' hnF'
  have h3 : cty₀ = ctyI' := congrArg ConstantVal.type hcv
  show Decl.noProjAt p.cvT.name cty₀ = true
  rw [hO.cvT, h3]
  exact hnp


end IxVM.Refinement.Typing
