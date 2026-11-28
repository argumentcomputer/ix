import IxVMRefinement.Assembly.NativeBlockCtorStage

/-! # The no-recursor install of a native block, with its family named

`Decl.nativeNoRecFacts_of_stage` and `Typing.nativeNoRecFacts_of_outs` conclude IxCK's
no-recursor install with the family's summary hidden. The theorems here are the same proofs with
the summary named: the telescope constant is the stored former `cvS` and the stored constructors
are `ctorsA` (the ones the stages were given), so the caller can read the new constants off its
own construction (`LateFamAt.tele`, the load contract at the new environment).

* `Decl.nativeNoRecFacts_of_stage_named`;
* `Typing.nativeNoRecFacts_of_outs_named`.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM.Refinement.Core
open Ix.Kernel (ConstantInfo ConstantVal Expr Level LevelParam Env NativeParts)
open Ix.Kernel.Rules (Red DefEq Infer)
open Ix.Kernel.Semantics (ConstantValCheckJ SumIndRunJ SumCtorsRunJ SumCtorRunJ FieldSortsJ
  FormerReadJ nativePartsNoRec?)
open Ix.Kernel.Model (rulesJ)
open IxVM.Refinement.Typing (NativeNoRecFacts)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- **The no-recursor install of a native block, from its two stages, with the family named and
the sorts of the table stage kept**: the constructor outputs carry any property `Q` of the
recursion flag and the field sorts; the install's table stage is run at sorts that have it. -/
theorem nativeNoRecFacts_of_stage_named_with {env : Env .anon} {blk : List KConstantInfo} {nP : Nat}
    {p₀ : NativeParts .anon} {Q : Bool → List (List KLevel) → Prop}
    (hp₀ : nativePartsNoRec? nP blk = some p₀) (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    (hstore : Ix.Kernel.Open.StoreInv env)
    {cvS : KConstantVal} {bsT : List (KExpr × Ix.Kernel.BinderMeta)}
    (hcheckT : ConstantValCheckJ rulesJ env p₀.cvT cvS)
    (hstS : cvS.type.stripPis (p₀.nP + p₀.nIdx) = some (bsT, .sort p₀.resSort))
    (hnameS : cvS.name = p₀.cvT.name)
    (hfreshT : env.find? cvS.name = none)
    (hshapeT : cvS.name.isProjFnShape = false)
    {ctorsA : List (KConstantVal × Nat)} {rawTypes : List KExpr}
    (hlenA : ctorsA.length = p₀.ctors.length)
    (hout : ∀ isRec : Bool, ∃ sortss : List (List KLevel), sortss.length = p₀.ctors.length ∧
      (∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
        sortss[j]? = some sorts ∧
        NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx p₀.resSort cvS.type
          (rawTypes.getD j default) c cA sorts) ∧ Q isRec sortss)
    (hfv_ctors : ∀ c ∈ p₀.ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ p₀.ctors, env.find? c.1.name = none)
    (hshape_ctors : ∀ c ∈ p₀.ctors, c.1.name.isProjFnShape = false)
    (hT_ctors : ∀ c ∈ p₀.ctors, c.1.name ≠ p₀.cvT.name)
    (hfn : ∀ j, env.find? (Ix.Kernel.projFnName p₀.cvT.name j) = none)
    (htbl : env.find? (Ix.Kernel.projTableName p₀.cvT.name) = none)
    (hunused : ∀ cA ∈ ctorsA, ∀ cbs body,
      cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2,
        (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
        Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) :
    ∃ (env₂ : Env .anon) (p : NativeParts .anon),
      NativeNoRecFacts env env₂ blk nP p₀ ⟨p, cvS, cvS, ctorsA⟩ ∧
      ∃ (isRec : Bool) (sortss : List (List KLevel)), Q isRec sortss ∧
        Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss
          (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩) = .ok env₂ ∧
        p.resSort = p₀.resSort := by
  obtain ⟨caps₀, hblk, hnP_eq, hlarge, hbasis_T, hctor_basis, ⟨bs₀, hst_raw⟩, hisProp⟩ :=
    nativePartsNoRec?_inv hp₀
  let p₁ : Ix.Kernel.InductiveShape .anon := p₀.toInductiveShape.withSort p₀.resSort
  have hbasis_S : Ix.Kernel.reservedBasisNames.contains cvS.name = false := by
    rw [hnameS]
    exact hbasis_T
  obtain ⟨tbs, tbody, _, hst_S_P, _, _, _⟩ := stripPis_split p₀.nP p₀.nIdx hstS
  obtain ⟨tfvsP, trestP, hopT_P⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome p₀.nP 0 (by rw [hst_S_P]; rfl)
  -- each constructor at the stage of any recursion flag
  have hctor_stage : ∀ (isRec : Bool) (j : Nat) (c cA : KConstantVal × Nat)
      (sorts : List KLevel),
      p₀.ctors[j]? = some c → ctorsA[j]? = some cA →
      NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx p₀.resSort cvS.type
          (rawTypes.getD j default) c cA sorts →
      cA.2 = c.2 ∧
      SumCtorRunJ rulesJ ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩
          ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
          p₀.resSort p₀.isProp false c.1 c.2 cvS cA.1 sorts ∧
      ∃ ks, Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx cA = some ks ∧
        ks.length = cA.2 ∧
        (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
        Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
          cA.1.type cA.2 ks = true := by
    intro isRec j c cA sorts hc hcA hout_j
    have hcA_mem : cA ∈ ctorsA := List.mem_of_getElem? hcA
    obtain ⟨_, _, cbs, es, _, _, hstrip_c, hcbs_len, hes_len, hes_noT, hpos_c, _⟩ :=
      hout_j.residual
    obtain ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hidx_len, hxFvs_res, hidx_res, hfsorts₀⟩ :=
      hout_j.opened
    obtain ⟨cbsP, cbodyP, _, hst_c_P, _, _, _⟩ := stripPis_split p₀.nP c.2 hstrip_c
    have hfsorts :
        FieldSortsJ rulesJ ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩
          p₀.isProp false p₀.resSort p₀.nP xFvs idxArgs c.2 sorts := by
      rw [hisProp]
      exact hfsorts₀
    have hfv_c : cA.1.type.hasFvar = false :=
      annotates_hasFvar_false hout_j.stored.2.2 (hfv_ctors c (List.mem_of_getElem? hc))
    have hsum_c :
        SumCtorRunJ rulesJ ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩
          ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
          p₀.resSort p₀.isProp false c.1 c.2 cvS cA.1 sorts :=
      ⟨⟨cA.1, hout_j.cvCheck, Or.inl rfl⟩,
        ⟨cbs, es, hstrip_c, hes_len⟩,
        fvsP, crest, tfvsP, trestP, xFvs, idxArgs,
        hopP, hopT_P, Or.inr (hout_j.domsShared.toSharedPins hopT_P hopP hst_S_P hst_c_P hfv_c),
        hopF, hidx_len, hxFvs_res, hidx_res, hfsorts⟩
    obtain ⟨sty_c, _, hinf_c, _⟩ := hout_j.inferSort
    have hres_c : cA.1.type.constsResolve
        ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec) :: env.consts⟩ = true := by
      obtain ⟨ty', ⟨_, _, _, _, _, _, _, _, hcr, _⟩, hcv⟩ := hout_j.cvCheck
      have hty_eq : cA.1.type = ty' := by rw [hcv]
      rwa [hty_eq]
    have hlit_c : litResolve env cA.1.type = true :=
      litResolve_of_infer_cons_former (ci := .indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec))
        hstore rfl hbasis_S ⟨p₀.nP + p₀.nIdx, bsT, p₀.resSort, hstS⟩ hinf_c hfv_c
    have hstrip_c' :
        cA.1.type.stripPis (p₀.nP + cA.2) =
          some (cbs, Expr.mkAppN (.const p₀.cvT.name (p₀.cvT.levelParams.map .param))
            (Ix.Kernel.structPsAt cA.2 p₀.nP ++ es)) := by
      rwa [hout_j.nF_eq]
    have hpos_c' : ∀ i < cA.2,
        Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs.getD (p₀.nP + i) default).1 ≠ .negative ∧
        Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs.getD (p₀.nP + i) default).1 ≠ .unsupported := by
      rw [hout_j.nF_eq]
      exact hpos_c
    have hunused_c := hunused cA hcA_mem cbs _ hstrip_c'
    obtain ⟨ks, hrck, hks_len, hks_ok, hopen_ok⟩ :=
      recCtorKinds_and_nativeOpenedOk (ci := .indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec))
        rfl hnameS hstrip_c' hes_len hes_noT hfv_c hres_c hlit_c hpos_c' hunused_c
    exact ⟨hout_j.nF_eq, hsum_c, ks, hrck, hks_len, hks_ok, hopen_ok⟩
  -- the kinds of the fields, read at the stage of either flag
  obtain ⟨sortss₀, -, hout₀, -⟩ := hout false
  have hk_ex : ∀ idx : Fin ctorsA.length, ∃ ks,
      Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx ctorsA[idx.1] =
        some ks ∧
      ks.length = ctorsA[idx.1].2 ∧
      (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
      Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
        ctorsA[idx.1].1.type ctorsA[idx.1].2 ks = true := by
    intro ⟨j, hjA⟩
    have hj : j < p₀.ctors.length := by rwa [← hlenA]
    obtain ⟨c, cA, sorts, hc, hcA, -, hout_j⟩ := hout₀ j hj
    rw [List.getElem?_eq_getElem hjA] at hcA
    injection hcA with hcA_eq
    cases hcA_eq
    obtain ⟨-, -, ks, hrck, hkl, hkok, hopok⟩ :=
      hctor_stage false j c ctorsA[j] sorts hc (List.getElem?_eq_getElem hjA) hout_j
    exact ⟨ks, hrck, hkl, hkok, hopok⟩
  let kinds : List (List Ix.Kernel.RecFieldKind) :=
    (List.finRange ctorsA.length).map fun i => Classical.choose (hk_ex i)
  have hall_kinds :
      List.Forall₂
        (fun cA ks =>
          Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx cA = some ks ∧
          ks.length = cA.2 ∧
          (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
          Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
            cA.1.type cA.2 ks = true)
        ctorsA kinds := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [kinds], fun j hj₁ hj₂ => ?_⟩
    have hspec := Classical.choose_spec (hk_ex ⟨j, hj₁⟩)
    have hget : kinds[j] = Classical.choose (hk_ex ⟨j, hj₁⟩) := by
      simp [kinds]
    simpa [hget] using hspec
  obtain ⟨hclassify, hfields_ok⟩ := classifyFixKinds_and_nativeFieldsOk hall_kinds
  -- the recursion flag, the parts, the capability record
  let isRec : Bool := Ix.Kernel.nativeIsRec kinds
  let p : NativeParts .anon := (p₀.complete p₁).withKinds kinds
  let caps : Ix.Kernel.IndCaps .anon := Ix.Kernel.nativeCapsAt p₁ isRec
  let env₁ : Env .anon := ⟨.indInfo cvS caps :: env.consts⟩
  obtain ⟨sortss, hslen, hout₁, hQ⟩ := hout isRec
  have hsum_ctors₀ :
      SumCtorsRunJ rulesJ env₁ env₁ p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
        p₀.resSort p₀.isProp false cvS p₀.ctors ctorsA sortss := by
    refine ⟨hlenA, hslen, fun j c cA hc hcA => ?_⟩
    have hj : j < p₀.ctors.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hc
      exact nomatch hc
    obtain ⟨c', cA', sorts, hc', hcA', hs, hout_j⟩ := hout₁ j hj
    rw [hc] at hc'
    injection hc' with hc_eq
    cases hc_eq
    rw [hcA] at hcA'
    injection hcA' with hcA_eq
    cases hcA_eq
    obtain ⟨hnF, hsc, -⟩ := hctor_stage isRec j c cA sorts hc hcA hout_j
    exact ⟨hnF, sorts, hs, hsc⟩
  have hsum_ctors₁ :
      SumCtorsRunJ rulesJ env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx
        p.resSort p.isProp p.large cvS p.ctors ctorsA sortss := by
    simpa [p, p₁, hlarge, hisProp] using hsum_ctors₀
  -- the index sorts, from the former's check
  have hext_env₁ : Ix.Kernel.EnvExt env env₁ :=
    envExt_cons_nonProj hfreshT (ne_projTableName_of_isProjFnShape_false hshapeT)
  obtain ⟨tfvs_all, isorts, hop_all, hisorts⟩ :=
    index_fieldSortsJ_of_former hcheckT hstS hext_env₁
  -- the projection table
  let env_base := Ix.Kernel.consSumCtors p.nP ctorsA env₁
  have hctorsA_names : ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < p₀.ctors.length
    · obtain ⟨c, cA, sorts, hc, hcA, -, hout_j⟩ := hout₁ j hj
      simp [hc, hcA, hout_j.stored.1]
    · have hjA : ¬ j < ctorsA.length := by rw [hlenA]; exact hj
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hj),
        List.getElem?_eq_none (Nat.le_of_not_lt hjA)]
  have hname_mem : ∀ cA ∈ ctorsA, ∃ c ∈ p₀.ctors, c.1.name = cA.1.name := by
    intro cA hcA
    have hm : cA.1.name ∈ p₀.ctors.map (·.1.name) := by
      rw [← hctorsA_names]
      exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
    exact List.mem_map.mp hm
  have hnd_ctorsA : (ctorsA.map (·.1.name)).Nodup := by
    rw [hctorsA_names]
    exact hnd
  have hshape_ctorsA : ∀ cA ∈ ctorsA, cA.1.name.isProjFnShape = false := by
    intro cA hcA
    obtain ⟨c, hc_mem, hname_eq⟩ := hname_mem cA hcA
    rw [← hname_eq]
    exact hshape_ctors c hc_mem
  have hfresh_ctorsA_env₁ : ∀ cA ∈ ctorsA, env₁.find? cA.1.name = none := by
    intro cA hcA
    obtain ⟨c, hc_mem, hname_eq⟩ := hname_mem cA hcA
    have hne : cvS.name ≠ cA.1.name := by
      rw [hnameS, ← hname_eq]
      exact fun heq => hT_ctors c hc_mem heq.symm
    show (Env.mk (.indInfo cvS caps :: env.consts)).find? cA.1.name = none
    rw [find?_cons_indInfo_ne _ _ _ hne, ← hname_eq]
    exact hfresh_ctors c hc_mem
  have hext_ctors : Ix.Kernel.EnvExt env₁ env_base :=
    envExt_consSumCtors p.nP ctorsA hnd_ctorsA hfresh_ctorsA_env₁ hshape_ctorsA
  have hT_ne_ctorsA : ∀ cA ∈ ctorsA, cA.1.name ≠ p.cvT.name := by
    intro cA hcA heq
    obtain ⟨c, hc_mem, hname_eq⟩ := hname_mem cA hcA
    exact hT_ctors c hc_mem (hname_eq.trans heq)
  have hself : env₁.find? cvS.name = some (.indInfo cvS caps) :=
    Ix.Kernel.Env.find?_cons_self (ConstantInfo.indInfo cvS caps) env
  have hT_in_base : (env_base.find? p.cvT.name).isSome = true := by
    rw [find?_consSumCtors_ne p.nP ctorsA env₁ hT_ne_ctorsA]
    have hpT : p.cvT.name = cvS.name := hnameS.symm
    rw [hpT, hself]
    rfl
  have hc_wf_base : ∀ cA ∈ ctorsA,
      (cA.1.type.stripPis (p.nP + cA.2)).isSome = true ∧
      cA.1.type.hasFvar = false ∧
      cA.1.type.allLevelParamsDefined p.cvT.levelParams = true ∧
      cA.1.type.constsResolve env_base = true ∧
      cA.1.type.looseBVarsBounded 0 = true := by
    intro cA hcA
    obtain ⟨j, hjA, rfl⟩ := List.getElem_of_mem hcA
    have hj : j < p₀.ctors.length := by rwa [← hlenA]
    obtain ⟨c, cA', _, hc, hcA', _, hout_j⟩ := hout₁ j hj
    rw [List.getElem?_eq_getElem hjA] at hcA'
    injection hcA' with hcA_eq
    cases hcA_eq
    obtain ⟨_, _, cbs, es, _, _, hstrip_c, _⟩ := hout_j.residual
    have hst_some : (ctorsA[j].1.type.stripPis (p.nP + ctorsA[j].2)).isSome = true := by
      have hpN : p.nP = p₀.nP := rfl
      rw [hpN, hout_j.nF_eq, hstrip_c]
      rfl
    obtain ⟨ty', ⟨_, _, _, _, hlbd₀, hfv₀, _, hlpd', hcr₀, _⟩, hcv⟩ := hout_j.cvCheck
    have hty_eq : ctorsA[j].1.type = ty' := by rw [hcv]
    have hfv' : ctorsA[j].1.type.hasFvar = false :=
      annotates_hasFvar_false hout_j.stored.2.2 hfv₀
    have hlbd' : ctorsA[j].1.type.looseBVarsBounded 0 = true :=
      annotates_looseBVarsBounded hout_j.stored.2.2 0 hlbd₀
    have hlpd'' : ctorsA[j].1.type.allLevelParamsDefined p.cvT.levelParams = true := by
      have hpL : p.cvT.levelParams = c.1.levelParams :=
        ((hctor_basis c (List.mem_of_getElem? hc)).1).symm
      rwa [hpL, hty_eq]
    have hcr₁ : ctorsA[j].1.type.constsResolve env₁ = true := by
      rw [hty_eq]
      exact hcr₀
    have hcr_base : ctorsA[j].1.type.constsResolve env_base = true :=
      Ix.Kernel.Expr.constsResolve_le
        (fun k hk => by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
          rw [hext_ctors.find hci]
          rfl)
        hcr₁
    exact ⟨hst_some, hfv', hlpd'', hcr_base, hlbd'⟩
  have hfn_fresh_base : ∀ j, env_base.find? (Ix.Kernel.projFnName p.cvT.name j) = none := by
    intro j
    rw [find?_consSumCtors_ne p.nP ctorsA env₁
      (fun cA hcA => ne_projFnName_of_isProjFnShape_false (hshape_ctorsA cA hcA) _ _)]
    show (Env.mk (.indInfo cvS caps :: env.consts)).find?
      (Ix.Kernel.projFnName p₀.cvT.name j) = none
    rw [find?_cons_indInfo_ne _ _ _ (ne_projFnName_of_isProjFnShape_false hshapeT _ _)]
    exact hfn j
  have htbl_fresh_base : env_base.find? (Ix.Kernel.projTableName p.cvT.name) = none := by
    rw [find?_consSumCtors_ne p.nP ctorsA env₁
      (fun cA hcA => ne_projTableName_of_isProjFnShape_false (hshape_ctorsA cA hcA) _)]
    show (Env.mk (.indInfo cvS caps :: env.consts)).find?
      (Ix.Kernel.projTableName p₀.cvT.name) = none
    rw [find?_cons_indInfo_ne _ _ _ (ne_projTableName_of_isProjFnShape_false hshapeT _)]
    exact htbl
  obtain ⟨env₂, htable_ok, -⟩ :=
    checkNativeTable_ok (sortss := sortss) hT_in_base hc_wf_base hfn_fresh_base htbl_fresh_base
  refine ⟨env₂, p, ⟨hp₀, hnd, isRec, cvS, cvS, caps, p₁, p, ctorsA, sortss,
    kinds, tfvs_all, .sort p₀.resSort, isorts, rfl, ?_, rfl, hsum_ctors₁, ?_, rfl, ?_, ?_, ?_,
    ?_, htable_ok⟩, isRec, sortss, hQ, htable_ok, rfl⟩
  · exact ⟨cvS, p₀.resSort, bsT, cvS, hcheckT, Or.inl rfl, hstS, Or.inl rfl, rfl, rfl⟩
  · simpa [p, p₁] using hclassify
  · simpa [p, p₁] using hop_all
  · simpa [p, p₁] using hisorts
  · simpa [p, p₁] using hfields_ok
  · refine Or.inl ⟨caps, ?_⟩
    have hpT : p.cvT.name = cvS.name := hnameS.symm
    rw [hpT]
    exact hself

/-- **The no-recursor install of a native block, from its two stages, with the family named**:
`nativeNoRecFacts_of_stage` with the telescope constant the stored former `cvS` and the stored
constructors `ctorsA`. -/
theorem nativeNoRecFacts_of_stage_named {env : Env .anon} {blk : List KConstantInfo} {nP : Nat}
    {p₀ : NativeParts .anon}
    (hp₀ : nativePartsNoRec? nP blk = some p₀) (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    (hstore : Ix.Kernel.Open.StoreInv env)
    {cvS : KConstantVal} {bsT : List (KExpr × Ix.Kernel.BinderMeta)}
    (hcheckT : ConstantValCheckJ rulesJ env p₀.cvT cvS)
    (hstS : cvS.type.stripPis (p₀.nP + p₀.nIdx) = some (bsT, .sort p₀.resSort))
    (hnameS : cvS.name = p₀.cvT.name)
    (hfreshT : env.find? cvS.name = none)
    (hshapeT : cvS.name.isProjFnShape = false)
    {ctorsA : List (KConstantVal × Nat)} {rawTypes : List KExpr}
    (hlenA : ctorsA.length = p₀.ctors.length)
    (hout : ∀ isRec : Bool, ∃ sortss : List (List KLevel), sortss.length = p₀.ctors.length ∧
      ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
        sortss[j]? = some sorts ∧
        NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx p₀.resSort cvS.type
          (rawTypes.getD j default) c cA sorts)
    (hfv_ctors : ∀ c ∈ p₀.ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ p₀.ctors, env.find? c.1.name = none)
    (hshape_ctors : ∀ c ∈ p₀.ctors, c.1.name.isProjFnShape = false)
    (hT_ctors : ∀ c ∈ p₀.ctors, c.1.name ≠ p₀.cvT.name)
    (hfn : ∀ j, env.find? (Ix.Kernel.projFnName p₀.cvT.name j) = none)
    (htbl : env.find? (Ix.Kernel.projTableName p₀.cvT.name) = none)
    (hunused : ∀ cA ∈ ctorsA, ∀ cbs body,
      cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2,
        (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
        Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) :
    ∃ (env₂ : Env .anon) (p : NativeParts .anon),
      NativeNoRecFacts env env₂ blk nP p₀ ⟨p, cvS, cvS, ctorsA⟩ := by
  obtain ⟨env₂, p, hf, -⟩ := nativeNoRecFacts_of_stage_named_with (Q := fun _ _ => True) hp₀ hnd
    hstore hcheckT hstS hnameS hfreshT hshapeT hlenA
    (fun isRec => by
      obtain ⟨sortss, hl, ho⟩ := hout isRec
      exact ⟨sortss, hl, ho, trivial⟩)
    hfv_ctors hfresh_ctors hshape_ctors hT_ctors hfn htbl hunused
  exact ⟨env₂, p, hf⟩

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

universe u

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **IxCK's no-recursor install of the block, from the outputs of its two stages, with the family
named and the sorts of the table stage kept**: `nativeNoRecFacts_of_outs` with the telescope
constant the stored former `cvS` and the stored constructors `ctorsA`; the constructor outputs
carry any property `Q` of the recursion flag and the field sorts, and the table stage is run at
sorts that have it. -/
theorem nativeNoRecFacts_of_outs_named_with {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon} {Q : Bool → List (List Ix.Kernel.Level) → Prop}
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t (some n) env)
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
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape ht hbound hS hrec hchk hblk
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

/-- **The no-recursor install of a native block, from its walked check, with the stored constants
named** (the form without the sorts of the table stage). -/
theorem nativeNoRecFacts_of_outs_named {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp₀ : Ix.Kernel.Semantics.nativePartsNoRec? ind.params.toNat blk = some p₀)
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (haux : Decl.AuxRootSynced env)
    {cvS : ConstantVal .anon} {bsT : List (Ix.Kernel.Expr .anon × Ix.Kernel.BinderMeta)}
    {ctorsA : List (ConstantVal .anon × Nat)} {rawTypes : List (Ix.Kernel.Expr .anon)}
    (hcheckT : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT cvS)
    (hstS : cvS.type.stripPis (p₀.nP + p₀.nIdx) = some (bsT, .sort p₀.resSort))
    (hnameS : cvS.name = p₀.cvT.name) (hlenA : ctorsA.length = p₀.ctors.length)
    (hout : ∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
      sortss.length = p₀.ctors.length ∧
      ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
        sortss[j]? = some sorts ∧
        Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort p₀.resSort) isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx p₀.resSort cvS.type
          (rawTypes.getD j default) c cA sorts)
    (hunused : ∀ cA ∈ ctorsA, ∀ cbs body,
      cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2,
        (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
        Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) :
    ∃ (env₂ : Ix.Kernel.Env .anon) (p : Ix.Kernel.NativeParts .anon),
      NativeNoRecFacts env env₂ blk ind.params.toNat p₀ ⟨p, cvS, cvS, ctorsA⟩ := by
  obtain ⟨env₂, p, hf, -⟩ := nativeNoRecFacts_of_outs_named_with (Q := fun _ _ => True) ht hS hst
    hrec hchk hblk hp₀ hnd hinv hfresh haux hcheckT hstS hnameS hlenA
    (fun isRec => by
      obtain ⟨sortss, hl, ho⟩ := hout isRec
      exact ⟨sortss, hl, ho, trivial⟩)
    hunused
  exact ⟨env₂, p, hf⟩

end IxVM.Refinement.Typing
