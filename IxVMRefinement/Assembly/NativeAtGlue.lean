import IxVMRefinement.Assembly.NativeAtFacts
import IxVMRefinement.Assembly.NativeBlockInv

/-! # The declaration layer's invariants along a step over the routes with an index count

`Ix.Kernel.Model.IndRoutesAJ` is `IndRoutesJ` or the native route without a recursor record at a
given index count (`NativeAtRunJ`), which reads a former declared at a definition. This module
gives the declaration layer's invariants along a step of `DeclRunJ` over these routes, each
reduced to its `IndRoutesJ` version through `Ix.Kernel.Model.declRunJA_cases`, the new route
handled as the no-recursor route is:

* `nativePartsAt?_block_eq`: the block the recogniser at a given index count reads is the former
  followed by its constructors (as `nativePartsNoRec?_block_eq`);
* `strongEnvProps_declRunJA_generic`, `strongEnvProps_declRunJA`;
* `etaShape_declRunJA_generic`, `etaShape_declRunJA`;
* `foldStoreInv_step_declRunJA`, `foldInv_step_declRunJA`, `foldInv_step_indNativeAt`;
* `auxRootSynced_step_declRunJA_generic`, `auxRootSynced_step_declRunJA`,
  `fullDeclInv_step_declRunJA`;
* `installStep_glue_indNativeAt`: the install's shape;
* for `Typing.NativeAtFacts`: `.foldInv`, `.fullDeclInv`, `.foldStoreInv`, `.installStep`,
  `.shape`, and `PrefixInv.nativeAt` (the prefix invariant after the install, given its two
  clauses that read the new family, as `PrefixInv.nativeNoRec`).
-/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Mode Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule
  BasisKind QuotKind IndCaps NativeParts InductiveShape ProjTable Env EnvExt)
open Ix.Kernel.Rules (Annot Red DefEq Infer Grade)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ ValueFrontRunJ
  DeclDefnRunJ DeclThmRunJ DeclOpaqueRunJ DeclAxiomRunJ DeclBasisRun DeclRunJ DeclsRunJ
  IndRoutesJ DeclIndRunJ IndMembersRunJ ProvisionRecsRunJ IndRecsFoldRunJ IndRecsRunJ
  DeclNativeRunJ DeclNativeNoRecRunJ DeclRecTwinRunJ TwinRecPart twinModels twinProv twinRecs
  SumIndRunJ SumCtorsRunJ SumCtorRunJ FormerStoredJ nativePartsNoRec? letFree)
open Ix.Kernel.Model (rulesJ EnvModel EnvModelM EnvModelT EnvModelOk JudgeFrames NewSat NotProj
  TableBodies ThmTyped RecK EtaTowers RecShape nativePartsAt? NativeAtRunJ IndRoutesAJ)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## The block the recogniser reads -/

/-- Exact member decomposition of a block accepted by `nativePartsAt?`. -/
theorem nativePartsAt?_block_eq {nPd nIdx : Nat} {block : List (ConstantInfo .anon)}
    {p₀ : NativeParts .anon}
    (h : nativePartsAt? nPd nIdx block = some p₀) :
    ∃ (caps : IndCaps .anon) (cs : List (ConstantVal .anon × Nat × Nat)),
      block = .indInfo p₀.cvT caps :: (cs.map fun c => .ctorInfo c.1 c.2.1 c.2.2) ∧
      p₀.ctors = cs.map (fun c => (c.1, c.2.2)) := by
  obtain ⟨caps₀, hblk, -⟩ := IxVM.Refinement.Typing.nativePartsAt?_inv h
  refine ⟨caps₀, p₀.ctors.map (fun c => (c.1, p₀.nP, c.2)), ?_, ?_⟩
  · rw [hblk, List.map_map]
    try rfl
  · simp [List.map_map, Function.comp_def]

/-- Extract constructor-key `NonAuxKey` from `nativePartsAt?` on a block of `NonAuxKey` members. -/
theorem nonAuxKey_ctors_of_nativePartsAt {nPd nIdx : Nat} {block : List (ConstantInfo .anon)}
    {p₀ : NativeParts .anon}
    (hblk : ∀ ci ∈ block, NonAuxKey ci.name)
    (hparts : nativePartsAt? nPd nIdx block = some p₀) :
    ∀ c ∈ p₀.ctors, NonAuxKey c.1.name := by
  obtain ⟨caps, cs, hblk_eq, hctors_eq⟩ := nativePartsAt?_block_eq hparts
  intro c hc
  rw [hctors_eq] at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
  refine hblk (.ctorInfo c'.1 c'.2.1 c'.2.2) ?_
  rw [hblk_eq]
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', rfl⟩)

/-! ## `StrongEnvProps` -/

private theorem nativeTable_newProj_ctor_nonAuxA {J : Judgements .anon}
    {envO env₁ X env₂ : Ix.Kernel.Env .anon} {p : NativeParts .anon}
    {cvTa : ConstantVal .anon} {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hCtors : SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss)
    (hCna : ∀ c ∈ p.ctors, NonAuxKey c.1.name)
    (hX : NewSat envO X NotProj)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    ∀ n tbl, env₂.find? n = some (.projInfo tbl) → envO.find? n = none →
      NonAuxKey tbl.ctor := by
  intro n tbl hf hn
  have hold : ∀ {t : ProjTable .anon}, X.find? n = some (.projInfo t) → False := by
    intro t hx
    rcases hX _ _ hx with h1 | h1
    · rw [h1] at hn; exact nomatch hn
    · exact h1 t rfl
  rcases Ix.Kernel.Model.nativeTable_cases hTbl with rfl | ⟨cA, sorts, bodies, rfl, rfl, -, -, rfl⟩
  · exact (hold hf).elim
  · rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · obtain rfl := ConstantInfo.projInfo.inj (Option.some.inj hf)
      obtain ⟨hlA, -, hall⟩ := id hCtors
      cases hpc : p.ctors with
      | nil => rw [hpc] at hlA; simp at hlA
      | cons c rest =>
        obtain ⟨_, _, _, hCtor⟩ := hall 0 c cA (by rw [hpc]; rfl) rfl
        have hc_mem : c ∈ p.ctors := by rw [hpc]; exact List.mem_cons_self
        have hname_eq : cA.1.name = c.1.name := by
          obtain ⟨cvCa₀, hchk₀, hcases⟩ := hCtor.1
          rcases hcases with rfl | ⟨ty', hchk'⟩
          · exact hchk₀.name_eq
          · exact hchk'.name_eq
        show NonAuxKey cA.1.name
        rw [hname_eq]
        exact hCna c hc_mem
    · exact (hold hf).elim

/-- `StrongEnvProps` preservation across any step over the routes with an index count when any
unpinned `.indDecl` block has `NonAuxKey` member names (in particular under `DeclNonAux d`). -/
theorem strongEnvProps_declRunJA_generic {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {d : Declaration .anon}
    (h : StrongEnvProps env) (htb : Ix.Kernel.Model.TableBodies env₂)
    (hna : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∀ ci ∈ block, NonAuxKey ci.name)
    (hrun : DeclRunJ J (IndRoutesAJ J env) env d env₂) :
    StrongEnvProps env₂ := by
  have hext := Ix.Kernel.Model.declRunJA_envExt hrun
  rcases Ix.Kernel.Model.declRunJA_cases hrun with h' | ⟨block, nP, rfl, hpin, nIdx, p₀, hdp, hN⟩
  · exact strongEnvProps_declRunJ_generic h htb hna h'
  · have hblk_na := hna block nP rfl hpin
    refine strongEnvProps_step hext.find h htb fun n tbl hf hn => Or.inl ?_
    obtain ⟨_, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd, hp, hCtors,
      _, _, _, _, _, hTbl, _⟩ := hN
    obtain ⟨_, _, _, _, _, _, _, _, hp₁, henv₁⟩ := hInd
    have h1 : NewSat env env₁ NotProj := by
      rw [henv₁]; exact NewSat.cons (fun _ heq => nomatch heq)
    have hXno : NewSat env (Ix.Kernel.consSumCtors p.nP ctorsA env₁) NotProj :=
      h1.trans (Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq))
    have hp_ctors : p.ctors = p₀.ctors := by
      rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
    exact nativeTable_newProj_ctor_nonAuxA hCtors
      (by rw [hp_ctors]; exact nonAuxKey_ctors_of_nativePartsAt hblk_na hdp)
      hXno hTbl n tbl hf hn

/-- Raw derivations supply the table-body premise from their store invariant. -/
theorem strongEnvProps_declRunJA {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hS : Ix.Kernel.Open.StoreInv env) (h : StrongEnvProps env)
    (hna : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∀ ci ∈ block, NonAuxKey ci.name)
    (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    StrongEnvProps env₂ := by
  exact strongEnvProps_declRunJA_generic h
    (Ix.Kernel.Model.tableBodies_declRunJA hS h.1 hrun) hna hrun

/-! ## `EtaShape` -/

private theorem levelParam_nodup_iffA :
    ∀ (lps : List LevelParam), LevelParam.nodup lps = true ↔ lps.Nodup
  | [] => by simp [LevelParam.nodup]
  | p :: ps => by
    simp [LevelParam.nodup, Bool.and_eq_true, List.nodup_cons, levelParam_nodup_iffA ps]

private theorem nativeCapsAt_eta_fullA {p : InductiveShape .anon} {isRec : Bool}
    (h : (Ix.Kernel.nativeCapsAt p isRec).eta = true) :
    ∃ c, p.ctors = [c] ∧ p.nIdx = 0 ∧
      (Ix.Kernel.nativeCapsAt p isRec).etaCtor = some c.1.name ∧
      (Ix.Kernel.nativeCapsAt p isRec).etaParams = p.nP ∧
      (Ix.Kernel.nativeCapsAt p isRec).etaFields = c.2 ∧
      (Ix.Kernel.nativeCapsAt p isRec).sortZ = Ix.Kernel.Level.zeronessOf p.resSort := by
  unfold Ix.Kernel.nativeCapsAt at h ⊢
  split at h
  · next c hc =>
    rw [hc]
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨c, rfl, h.1.1, rfl, rfl, rfl, rfl⟩
  · exact nomatch h

private theorem native_etaShape_newA {J : Judgements .anon} {env env₁ X env₂ : Ix.Kernel.Env .anon}
    {p₀ p : NativeParts .anon} {isRec : Bool} {cvTa : ConstantVal .anon} {p₁ : InductiveShape .anon}
    {kinds : List (List Ix.Kernel.RecFieldKind)} {ctorsA : List (ConstantVal .anon × Nat)}
    {sortss : List (List KLevel)}
    (hrc : Ix.Kernel.Model.NativeRecog p₀)
    (hInd : SumIndRunJ J env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      env₁ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss)
    (hX : NewSat env₁ X (fun x => ∀ cv caps, x ≠ .indInfo cv caps))
    (hCkeep : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
      env₂.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2))
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    ∀ T cvT caps, env₂.find? T = some (.indInfo cvT caps) → env.find? T = none →
      caps.eta = true →
      (∀ kc, caps.etaCtor = some kc → (env₂.find? kc).isSome = true) ∧
      (∃ bs l, cvT.type.stripPis caps.etaParams = some (bs, .sort l) ∧
        caps.sortZ = Ix.Kernel.Level.zeronessOf l) ∧
      ∀ kc cvc nP nF, caps.etaCtor = some kc →
        env₂.find? kc = some (.ctorInfo cvc nP nF) →
        cvc.levelParams.Nodup ∧
        cvc.levelParams = cvT.levelParams ∧
        nP = caps.etaParams ∧
        nF = caps.etaFields ∧
        ∃ cbs, cvc.type.stripPis (nP + nF) = some (cbs,
          Ix.Kernel.Expr.mkAppN (.const T (cvc.levelParams.map .param))
            (Ix.Kernel.structPsAt nF nP)) := by
  obtain ⟨cvTa₀, s, bs, cvS, hchk₀, hTa_cases, hstripT, hFS, hp₁, henv₁⟩ := hInd
  intro T cvT caps hf hn he
  have hT₁ : env₁.find? T = some (.indInfo cvT caps) := by
    rcases (hX.trans (Ix.Kernel.Model.nativeTable_newSat
        (Q := fun x => ∀ cv caps, x ≠ .indInfo cv caps)
        (fun _ _ _ heq => nomatch heq) hTbl)) _ _ hf with h1 | h1
    · exact h1
    · exact absurd rfl (h1 cvT caps)
  rw [henv₁, Ix.Kernel.Env.find?_cons] at hT₁
  split at hT₁
  · next hname =>
    obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hT₁)
    obtain ⟨c, hc, hI, hCtorOpt, hParams, hFields, hSortZ⟩ := nativeCapsAt_eta_fullA he
    have hI₀ : p₀.nIdx = 0 := by subst hp₁; simpa [InductiveShape.withSort] using hI
    have hcvS_eq : cvS = cvTa := by
      rcases hFS with rfl | ⟨_, _, hne⟩
      · rfl
      · exact absurd hI₀ hne
    have hp_nP : p₀.nP = (Ix.Kernel.nativeCapsAt p₁ isRec).etaParams := by
      rw [hParams]; subst hp₁; rfl
    have hp_sort : s = p₁.resSort := by subst hp₁; rfl
    have hsort_part :
        ∃ bs' l, cvS.type.stripPis (Ix.Kernel.nativeCapsAt p₁ isRec).etaParams =
          some (bs', Expr.sort l) ∧
          (Ix.Kernel.nativeCapsAt p₁ isRec).sortZ = Ix.Kernel.Level.zeronessOf l := by
      refine ⟨bs, s, ?_, ?_⟩
      · rw [hcvS_eq, ← hp_nP]
        simpa [hI₀] using hstripT
      · rw [hSortZ, hp_sort]
    have hc₀ : p₀.ctors = [c] := by subst hp₁; simpa [InductiveShape.withSort] using hc
    have hpc : p.ctors = [c] := by
      rw [hp, hp₁]; simpa [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort] using hc₀
    obtain ⟨hlA, -, hall⟩ := id hCtors
    rw [hpc] at hlA
    obtain ⟨cA, rfl⟩ : ∃ cA, ctorsA = [cA] := by
      match ctorsA, hlA with
      | [cA], _ => exact ⟨cA, rfl⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    obtain ⟨hnF, sorts, _, hCtorRun⟩ := hall 0 c cA (by rw [hpc]; rfl) rfl
    have hcA_name : cA.1.name = c.1.name := by
      obtain ⟨cvCa₀, hcc₀, hcc⟩ := hCtorRun.1
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.name_eq
      · exact hcc'.name_eq
    have hcA_c_lps : cA.1.levelParams = c.1.levelParams := by
      obtain ⟨cvCa₀, hcc₀, hcc⟩ := hCtorRun.1
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.levelParams_eq
      · exact hcc'.levelParams_eq
    have hcA_nd : cA.1.levelParams.Nodup := by
      obtain ⟨cvCa₀, ⟨_, hrunC, _⟩, _⟩ := hCtorRun.1
      rw [hcA_c_lps]
      exact (levelParam_nodup_iffA c.1.levelParams).mp hrunC.2.2.2.1
    have hcA_find : env₂.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) := hCkeep 0 cA rfl
    have hT_eq : T = p.cvT.name := by
      have hTa_name : cvTa.name = p₀.cvT.name := by
        rcases hTa_cases with rfl | ⟨_, hTa'⟩
        · exact hchk₀.name_eq
        · exact hTa'.name_eq
      have hp_name : p.cvT.name = p₀.cvT.name := by
        rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
      have hcvS_name : cvS.name = T := hname
      rw [← hcvS_name, hcvS_eq, hTa_name, hp_name]
    have h1_lps : cvTa.levelParams = p₀.cvT.levelParams := by
      rcases hTa_cases with rfl | ⟨_, hTa'⟩
      · exact hchk₀.levelParams_eq
      · exact hTa'.levelParams_eq
    have hTa_lps : cvTa.levelParams = p.cvT.levelParams := by
      have h2 : p.cvT.levelParams = p₀.cvT.levelParams := by
        rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
      rw [h1_lps, h2]
    have hcA_lps : cA.1.levelParams = cvS.levelParams := by
      have hc_lps : c.1.levelParams = p₀.cvT.levelParams :=
        (hrc.1 c (by rw [hc₀]; exact List.mem_cons_self)).1
      rw [hcA_c_lps, hc_lps, hcvS_eq, h1_lps]
    refine ⟨fun kc hkc => ?_, hsort_part, fun kc cvc nP nF hkc hfc => ?_⟩
    · rw [hCtorOpt] at hkc
      injection hkc with hkc_eq
      rw [← hkc_eq, ← hcA_name, hcA_find]
      rfl
    · rw [hCtorOpt] at hkc
      injection hkc with hkc_eq
      rw [← hkc_eq, ← hcA_name, hcA_find] at hfc
      obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj hfc)
      obtain ⟨cbs, es, hstripC, hes_len⟩ := hCtorRun.2.1
      have hp_I : p.nIdx = 0 := by
        rw [hp, hp₁]; simpa [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort] using hI₀
      have hes_nil : es = [] := List.eq_nil_of_length_eq_zero (hes_len.trans hp_I)
      rw [hes_nil, List.append_nil] at hstripC
      have hp_nP' : p.nP = (Ix.Kernel.nativeCapsAt p₁ isRec).etaParams := by
        rw [← hp_nP, hp, hp₁]
        simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
      refine ⟨hcA_nd, hcA_lps, hp_nP', hnF.trans hFields.symm, cbs, ?_⟩
      rw [hnF, hT_eq, hcA_lps, hcvS_eq, hTa_lps]
      exact hstripC
  · rw [hT₁] at hn; cases hn

/-- Every step over the routes with an index count preserves `EtaCtorStored` and `EtaShape`. -/
theorem etaShape_declRunJA_generic {J : Judgements .anon}
    (hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames J e) {env env₂ : Ix.Kernel.Env .anon}
    {d : Declaration .anon}
    (hS : Ix.Kernel.Open.StoreInv env)
    (hcs : EtaCtorStored env) (h : EtaShape env)
    (hrun : DeclRunJ J (IndRoutesAJ J env) env d env₂) :
    EtaCtorStored env₂ ∧ EtaShape env₂ := by
  have hext := Ix.Kernel.Model.declRunJA_envExt hrun
  rcases Ix.Kernel.Model.declRunJA_cases hrun with h' | ⟨block, nP, rfl, hpin, nIdx, p₀, hdp, hN⟩
  · exact etaShape_declRunJ_generic hfr hS hcs h h'
  · obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd, hp, hCtors,
      _, _, _, _, _, hTbl, _⟩ := hN
    have hF := Ix.Kernel.Model.nativeFront hfr hS (Ix.Kernel.Model.nativeRecog_at hdp)
      hnd hInd hp hCtors
    have hX : NewSat env₁ (Ix.Kernel.consSumCtors p.nP ctorsA env₁)
        (fun x => ∀ cv caps, x ≠ .indInfo cv caps) :=
      Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ _ heq => nomatch heq)
    have hCkeep : ∀ (j : Nat) (cA : ConstantVal .anon × Nat), ctorsA[j]? = some cA →
        env₂.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) :=
      fun j cA hj => Ix.Kernel.Model.nativeTable_keep hTbl (hF.ctor j cA hj).1
    have hnew := native_etaShape_newA (Ix.Kernel.Model.nativeRecog_at hdp)
      hInd hp hCtors hX hCkeep hTbl
    refine ⟨?_, etaShape_step hext h ?_ (fun T cvT caps hf hn he =>
      (hnew T cvT caps hf hn he).2)⟩
    · intro T cvT caps kc hf he hkc
      cases hold : env.find? T with
      | none => exact (hnew T cvT caps hf hold he).1 kc hkc
      | some c =>
        have h2 := hext.find hold
        rw [hf] at h2
        obtain rfl := Option.some.inj h2
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
        rw [hext.find hci]; rfl
    · intro T cvT caps kc cvc nP' nF' hold he hkc hfc₂
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hcs T cvT caps kc hold he hkc)
      have hci₂ := hext.find hci
      rw [hfc₂] at hci₂
      obtain rfl := Option.some.inj hci₂
      exact hci

/-- Compatibility with the raw rules judgement package. -/
theorem etaShape_declRunJA {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hS : Ix.Kernel.Open.StoreInv env)
    (hcs : EtaCtorStored env) (h : EtaShape env)
    (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    EtaCtorStored env₂ ∧ EtaShape env₂ := by
  exact etaShape_declRunJA_generic (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e)
    hS hcs h hrun

/-! ## `FoldStoreInv` and `FoldInv` -/

/-- One-step preservation of `FoldStoreInv` along any step over the routes with an index count
when any unpinned `.indDecl` block has `NonAuxKey` member names. -/
theorem foldStoreInv_step_declRunJA {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (h : FoldStoreInv env)
    (hna : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    FoldStoreInv env₂ := by
  have heta := etaShape_declRunJA h.store h.etaCtorStored h.etaShape hd
  refine
    { store :=
        Ix.Kernel.Model.storeInv_declRunJA
          (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e) h.store hd
      thmTyped := Ix.Kernel.Model.thmTyped_declRunJA h.thmTyped hd
      recK := Ix.Kernel.Model.recK_declRunJA h.store h.recK hd
      etaTowers := Ix.Kernel.Model.etaTowers_declRunJA h.etaTowers hd
      strongProps := strongEnvProps_declRunJA h.store h.strongProps hna hd
      recShape := Ix.Kernel.Model.recShape_declRunJA h.store h.recShape hd
      etaCtorStored := heta.1
      etaShape := heta.2 }

/-- Uniform one-step preservation of `FoldInv` along a step over the routes with an index
count. -/
theorem foldInv_step_declRunJA {env env₂ : Ix.Kernel.Env .anon} {d : Declaration .anon}
    (hna : ∀ block nP, d = .indDecl block nP → Ix.Kernel.basisPinHit block = none →
      ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  fun _ _ h => ⟨Ix.Kernel.Model.foldRulesRoutesA (.cons hd .nil) h.model,
    foldStoreInv_step_declRunJA h.store hna hd⟩

/-- `FoldInv` along the native route without a recursor record at a given index count. -/
theorem foldInv_step_indNativeAt {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP nIdx : Nat} {p₀ : NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hdp : nativePartsAt? nP nIdx block = some p₀)
    (hN : DeclNativeNoRecRunJ rulesJ env p₀ env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ := by
  have hd : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env (.indDecl block nP) env₂ := by
    simp only [DeclRunJ, hpin]
    exact Or.inr ⟨nIdx, p₀, hdp, hN⟩
  exact foldInv_step_declRunJA
    (fun blk _ heq _ => by injection heq with hblk _; subst hblk; exact hna) hd

/-! ## `AuxRootSynced` and `FullDeclInv` -/

private theorem auxRootSynced_of_base_prependA {env : Env .anon} {new : List (ConstantInfo .anon)}
    (h : AuxRootSynced env) (hbase : ∀ ci ∈ new, isBaseKey ci.name = true) :
    AuxRootSynced ⟨new ++ env.consts⟩ :=
  h.of_prepend fun ci hci => by
    rw [base_of_isBaseKey (hbase ci hci)]
    exact env_find?_isSome_of_mem_prefix hci

private theorem sumCtorsRunJ_names_eqA {J : Judgements .anon}
    {env env₁ : Env .anon} {T : KKey} {lps : List LevelParam} {nP nIdx : Nat}
    {resSort : KLevel} {isProp large : Bool} {cvTa : ConstantVal .anon}
    {ctors ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hCtors : SumCtorsRunJ J env env₁ T lps nP nIdx resSort isProp large cvTa ctors ctorsA sortss) :
    ctorsA.map (·.1.name) = ctors.map (·.1.name) := by
  obtain ⟨hlA, -, hall⟩ := id hCtors
  apply List.ext_getElem
  · simp [hlA]
  · intro j h1 h2
    simp only [List.length_map] at h1 h2
    obtain ⟨_, _, _, hC⟩ := hall j ctors[j] ctorsA[j] (List.getElem?_eq_getElem h2)
      (List.getElem?_eq_getElem h1)
    obtain ⟨cvCa₀, hcc₀, hcc⟩ := hC.1
    simp only [List.getElem_map]
    rcases hcc with rfl | ⟨_, hcc'⟩
    · exact hcc₀.name_eq
    · exact hcc'.name_eq

private theorem consSumCtors_consts_appendA (nP : Nat) :
    ∀ (cs : List (ConstantVal .anon × Nat)) (consts : List (ConstantInfo .anon)),
      (Ix.Kernel.consSumCtors nP cs ⟨consts⟩).consts =
        (cs.reverse.map fun c => ConstantInfo.ctorInfo c.1 nP c.2) ++ consts
  | [], consts => rfl
  | c :: cs, consts => by
    simp [Ix.Kernel.consSumCtors, consSumCtors_consts_appendA nP cs (.ctorInfo c.1 nP c.2 :: consts),
      List.reverse_cons, List.map_append, List.append_assoc]

private theorem checkNativeTable_env_casesA {p : NativeParts .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    {envX env₂ : Env .anon}
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss envX =
      .ok env₂) :
    env₂ = envX ∨ ∃ tbl : ProjTable .anon,
      tbl.structName = p.cvT.name ∧ env₂ = ⟨.projInfo tbl :: envX.consts⟩ := by
  rcases IxVM.Refinement.Typing.checkNativeTable_shape hTbl with heq | ⟨tbl, heq, hsn⟩
  · exact Or.inl heq
  · exact Or.inr ⟨tbl, hsn, heq⟩

/-- Auxiliary-root synchronization along a step over the routes with an index count, at any
judgement package. -/
theorem auxRootSynced_step_declRunJA_generic {J : Judgements .anon} {env env₂ : Env .anon}
    {d : Declaration .anon}
    (haux : AuxRootSynced env) (hna : DeclNonAux d)
    (hrun : DeclRunJ J (IndRoutesAJ J env) env d env₂) :
    AuxRootSynced env₂ := by
  rcases Ix.Kernel.Model.declRunJA_cases hrun with h' | ⟨block, nP, rfl, hpin, nIdx, p₀, hdp, hN⟩
  · exact auxRootSynced_step_declRunJ_generic haux hna h'
  · have hblk_base : ∀ ci₀ ∈ block, isBaseKey ci₀.name = true := by
      intro ci₀ hci₀
      have hm : ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP) := by
        simpa [IxVM.Consistency.installs, hpin] using hci₀
      exact isBaseKey_of_nonAuxKey (hna.1 ci₀ hm).1
    obtain ⟨caps₀, cs, hblk_eq, hctors₀⟩ := nativePartsAt?_block_eq hdp
    obtain ⟨_, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd,
      hp, hCtors, _, _, _, _, _, hTbl, _⟩ := hN
    obtain ⟨_, _, _, cvS, hchkT, hTa_cases, _, hFS, hp₁, henv₁⟩ := hInd
    have hcvS_name : cvS.name = p₀.cvT.name := by
      have hTa_name : cvTa.name = p₀.cvT.name := by
        rcases hTa_cases with rfl | ⟨_, hTa'⟩
        · exact hchkT.name_eq
        · exact hTa'.name_eq
      rcases hFS with rfl | ⟨rfl, -⟩
      · exact hTa_name
      · exact hchkT.name_eq
    have hp_cvT : p.cvT = p₀.cvT := by
      rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
    have hp_ctors : p.ctors = p₀.ctors := by
      rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
    have hctorsA_names : ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) := by
      rw [sumCtorsRunJ_names_eqA hCtors, hp_ctors]
    let indCI : ConstantInfo .anon := .indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)
    let newCtors : List (ConstantInfo .anon) :=
      ctorsA.reverse.map fun c => .ctorInfo c.1 p.nP c.2
    let coreNew : List (ConstantInfo .anon) := newCtors ++ [indCI]
    have henvX : Ix.Kernel.consSumCtors p.nP ctorsA env₁ = ⟨coreNew ++ env.consts⟩ := by
      rw [henv₁]
      exact congrArg Env.mk (by rw [consSumCtors_consts_appendA]; simp [coreNew, newCtors, indCI])
    have hcore_base : ∀ c ∈ coreNew, isBaseKey c.name = true := by
      intro c hc
      rcases List.mem_append.mp hc with hct | hind
      · have hk : c.name ∈ p₀.ctors.map (·.1.name) := by
          obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp hct
          have hk' : cA.1.name ∈ ctorsA.map (·.1.name) :=
            List.mem_map_of_mem (List.mem_reverse.mp hcA)
          rwa [hctorsA_names] at hk'
        rw [hctors₀] at hk
        obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hk
        obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
        have hmemC : ConstantInfo.ctorInfo c'.1 c'.2.1 c'.2.2 ∈ block := by
          rw [hblk_eq]
          exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', rfl⟩)
        rw [← hxeq]
        exact hblk_base _ hmemC
      · obtain rfl := List.mem_singleton.mp hind
        have hmemT : ConstantInfo.indInfo p₀.cvT caps₀ ∈ block := by
          rw [hblk_eq]; exact List.mem_cons_self
        show isBaseKey cvS.name = true
        rw [hcvS_name]
        exact hblk_base _ hmemT
    have hauxX : AuxRootSynced ⟨coreNew ++ env.consts⟩ :=
      auxRootSynced_of_base_prependA haux hcore_base
    rcases checkNativeTable_env_casesA hTbl with rfl | ⟨tbl, hsn, rfl⟩
    · rw [henvX]; exact hauxX
    · rw [henvX] at *
      refine hauxX.cons_of_root_stored (Or.inr ?_)
      have hbT : isBaseKey p₀.cvT.name = true := by
        have hmemT : ConstantInfo.indInfo p₀.cvT caps₀ ∈ block := by
          rw [hblk_eq]; exact List.mem_cons_self
        exact hblk_base _ hmemT
      have hbase_tbl : (ConstantInfo.projInfo tbl).name.base = cvS.name := by
        show (Ix.Kernel.projTableName tbl.structName).base = cvS.name
        rw [hsn, hp_cvT, hcvS_name]
        exact base_of_isBaseKey hbT
      rw [hbase_tbl]
      have hind_mem : indCI ∈ coreNew :=
        List.mem_append_right _ List.mem_cons_self
      exact env_find?_isSome_of_mem_prefix hind_mem

/-- Rules-tier steps over the routes with an index count preserve auxiliary-root
synchronization. -/
theorem auxRootSynced_step_declRunJA {env env₂ : Env .anon} {d : Declaration .anon}
    (haux : AuxRootSynced env) (hna : DeclNonAux d)
    (hrun : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    AuxRootSynced env₂ :=
  auxRootSynced_step_declRunJA_generic haux hna hrun

/-- Uniform one-step preservation of `FullDeclInv` along a step over the routes with an index
count, on any `DeclNonAux` declaration. -/
theorem fullDeclInv_step_declRunJA {env env₂ : Env .anon} {d : Declaration .anon}
    (hna : DeclNonAux d)
    (hd : DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env d env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  refine FullDeclInv.step_of_foldInv_aux (foldInv_step_declRunJA ?_ hd)
    (fun haux => auxRootSynced_step_declRunJA haux hna hd)
  intro block nP heq hpin ci hci
  subst heq
  have hm : ci ∈ IxVM.Consistency.installs (.indDecl block nP) := by
    simpa [IxVM.Consistency.installs, hpin] using hci
  exact (hna.1 ci hm).1

/-! ## The install's shape -/

private theorem consSumCtors_consts_eqA (nP : Nat) :
    ∀ (ctorsA : List (ConstantVal .anon × Nat)) (e : Ix.Kernel.Env .anon),
      (Ix.Kernel.consSumCtors nP ctorsA e).consts =
        (ctorsA.reverse.map fun c => .ctorInfo c.1 nP c.2) ++ e.consts
  | [], e => rfl
  | c :: cs, e => by
    simp [Ix.Kernel.consSumCtors, consSumCtors_consts_eqA nP cs, List.reverse_cons,
      List.map_append, List.append_assoc]

private theorem sumCtorsRunJ_names_freshA {J : Judgements .anon}
    {env env₁ : Ix.Kernel.Env .anon} {T : KKey} {lps : List LevelParam} {nP nIdx : Nat}
    {resSort : KLevel} {isProp large : Bool} {cvTa : ConstantVal .anon}
    {ctors ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hCtors : SumCtorsRunJ J env env₁ T lps nP nIdx resSort isProp large cvTa ctors ctorsA sortss) :
    ctorsA.map (·.1.name) = ctors.map (·.1.name) ∧
      ∀ cA ∈ ctorsA, env₁.find? cA.1.name = none := by
  obtain ⟨hlA, -, hall⟩ := id hCtors
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem
    · simp [hlA]
    · intro j h1 h2
      simp only [List.length_map] at h1 h2
      obtain ⟨_, _, _, hC⟩ := hall j ctors[j] ctorsA[j] (List.getElem?_eq_getElem h2)
        (List.getElem?_eq_getElem h1)
      obtain ⟨cvCa₀, hcc₀, hcc⟩ := hC.1
      simp only [List.getElem_map]
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.name_eq
      · exact hcc'.name_eq
  · intro cA hcA
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcA
    have hj_c : j < ctors.length := by omega
    obtain ⟨_, _, _, hC⟩ := hall j ctors[j] ctorsA[j] (List.getElem?_eq_getElem hj_c)
      (List.getElem?_eq_getElem hj)
    obtain ⟨cvCa₀, hcc₀, hcc⟩ := hC.1
    have hname : ctorsA[j].1.name = ctors[j].1.name := by
      rcases hcc with rfl | ⟨_, hcc'⟩
      · exact hcc₀.name_eq
      · exact hcc'.name_eq
    rw [hname]
    exact hcc₀.fresh

private theorem checkNativeTable_freshChainA {env X env₂ : Ix.Kernel.Env .anon}
    {newX : List (ConstantInfo .anon)} {p : NativeParts .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hcX : FreshChain env newX X)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    ∃ new₂, FreshChain env new₂ env₂ ∧
      (new₂ = newX ∨ ∃ tbl : ProjTable .anon, new₂ = .projInfo tbl :: newX ∧
        (.projInfo tbl : ConstantInfo .anon).name = .aux p.cvT.name .projTable) := by
  unfold Ix.Kernel.checkNativeTable at hTbl
  split at hTbl
  · next cA sorts =>
    split at hTbl
    · obtain ⟨bodies, -, -, -, hfrT, rfl⟩ := Ix.Kernel.checkStructProjTable_inv hTbl
      let tbl : ProjTable .anon :=
        ⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort, bodies,
          Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩
      have hc₂ := freshChain_cons (x := .projInfo tbl) hcX hfrT
      exact ⟨.projInfo tbl :: newX, hc₂, Or.inr ⟨tbl, rfl, rfl⟩⟩
    · injection hTbl with hX_eq
      subst hX_eq
      exact ⟨newX, hcX, Or.inl rfl⟩
  · injection hTbl with hX_eq
    subst hX_eq
    exact ⟨newX, hcX, Or.inl rfl⟩

/-- The install of a native block without its recursor record at a given index count, with the
declared constants stored as declared, is an `InstallStep`. -/
theorem installStep_glue_indNativeAt {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP nIdx : Nat} {p₀ : NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hdp : nativePartsAt? nP nIdx block = some p₀)
    (hN : DeclNativeNoRecRunJ J env p₀ env₂)
    (hstored : ∀ ci₀ ∈ block,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ := by
  obtain ⟨caps₀, cs, hblk_eq, hctors₀⟩ := nativePartsAt?_block_eq hdp
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd, hp, hCtors,
    _, _, _, _, _, hTbl, _⟩ := hN
  obtain ⟨cvTa₀, s, bs, cvS, hchkT, hTa_cases, _, hFS, hp₁, henv₁⟩ := hInd
  have hcvS_name : cvS.name = p₀.cvT.name := by
    have hTa_name : cvTa.name = p₀.cvT.name := by
      rcases hTa_cases with rfl | ⟨_, hTa'⟩
      · exact hchkT.name_eq
      · exact hTa'.name_eq
    rcases hFS with rfl | ⟨rfl, -⟩
    · exact hTa_name
    · exact hchkT.name_eq
  have hc₁ : FreshChain env [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)] env₁ := by
    rw [henv₁]
    exact freshChain_cons (freshChain_nil env)
      (by show env.find? cvS.name = none; rw [hcvS_name]; exact hchkT.fresh)
  obtain ⟨hctorsA_names, hctorsA_fr⟩ := sumCtorsRunJ_names_freshA hCtors
  have hp_ctors : p.ctors = p₀.ctors := by
    rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
  let newCtors : List (ConstantInfo .anon) := ctorsA.reverse.map fun c => .ctorInfo c.1 p.nP c.2
  have hnewCtors_names : newCtors.map (·.name) = (p₀.ctors.map (·.1.name)).reverse := by
    simp [newCtors, List.map_map, Function.comp_def, ConstantInfo.name, ConstantInfo.toConstantVal,
      hctorsA_names, hp_ctors]
  have hcCtors : FreshChain env (newCtors ++ [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)])
      (Ix.Kernel.consSumCtors p.nP ctorsA env₁) := by
    have heqC : Ix.Kernel.consSumCtors p.nP ctorsA env₁ = ⟨newCtors ++ env₁.consts⟩ := by
      cases env₁; exact congrArg Ix.Kernel.Env.mk (consSumCtors_consts_eqA p.nP ctorsA _)
    rw [heqC]
    refine freshChain_prepend hc₁ (by rw [hnewCtors_names]; exact List.nodup_reverse.mpr hnd) ?_
    intro x hx
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp hx
    exact hctorsA_fr cA (List.mem_reverse.mp hcA)
  obtain ⟨new₂, hc₂, htbl_cases⟩ := checkNativeTable_freshChainA hcCtors hTbl
  have hinst : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hpin]
  have hcore_cov : ∀ c ∈ (newCtors ++ [.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)]),
      ∃ ci₀ ∈ block, ci₀.name = c.name := by
    intro c hc_mem
    rcases List.mem_append.mp hc_mem with hct | hind
    · have hk : c.name ∈ p₀.ctors.map (·.1.name) := by
        have hk' : c.name ∈ (p₀.ctors.map (·.1.name)).reverse := by
          rw [← hnewCtors_names]; exact List.mem_map_of_mem hct
        exact List.mem_reverse.mp hk'
      rw [hctors₀] at hk
      obtain ⟨x, hx, hxeq⟩ := List.mem_map.mp hk
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hx
      refine ⟨.ctorInfo c'.1 c'.2.1 c'.2.2, ?_, hxeq⟩
      rw [hblk_eq]
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨c', hc', rfl⟩)
    · obtain rfl := List.mem_singleton.mp hind
      exact ⟨.indInfo p₀.cvT caps₀, by rw [hblk_eq]; exact List.mem_cons_self, hcvS_name.symm⟩
  have hcore_names : ∀ ci₀ ∈ block,
      ci₀.name ∈ (newCtors ++
        [ConstantInfo.indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)]).map (·.name) := by
    intro ci₀ hci₀
    rw [hblk_eq] at hci₀
    rcases List.mem_cons.mp hci₀ with rfl | hcs
    · simp [ConstantInfo.name, ConstantInfo.toConstantVal, hcvS_name]
    · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hcs
      have hk : c'.1.name ∈ newCtors.map (·.name) := by
        rw [hnewCtors_names, List.mem_reverse, hctors₀]
        exact List.mem_map.mpr ⟨(c'.1, c'.2.2), List.mem_map.mpr ⟨c', hc', rfl⟩, rfl⟩
      rw [List.map_append]
      exact List.mem_append_left _ hk
  refine installStep_glue_of_freshChain hc₂ ?_ ?_ ?_
  · intro c hc_mem
    rcases htbl_cases with rfl | ⟨tbl, rfl, htbl_name⟩
    · obtain ⟨ci₀, hci₀, hnm⟩ := hcore_cov c hc_mem
      exact Or.inl ⟨ci₀, by rw [hinst]; exact hci₀, hnm⟩
    · rcases List.mem_cons.mp hc_mem with rfl | hc_old
      · exact Or.inr ⟨_, _, htbl_name⟩
      · obtain ⟨ci₀, hci₀, hnm⟩ := hcore_cov c hc_old
        exact Or.inl ⟨ci₀, by rw [hinst]; exact hci₀, hnm⟩
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    rcases htbl_cases with rfl | ⟨tbl, rfl, -⟩
    · exact hcore_names ci₀ hci₀
    · exact List.mem_cons_of_mem _ (hcore_names ci₀ hci₀)
  · intro ci₀ hci₀
    rw [hinst] at hci₀
    exact hstored ci₀ hci₀

end IxVM.Refinement.Decl

namespace IxVM.Refinement.Typing

open Ix.Kernel (Env ConstantInfo ConstantVal NativeParts InductiveShape IndCaps Level Expr
  RecFieldKind Declaration EnvExt)
open Ix.Kernel.Semantics (DeclNativeNoRecRunJ SumIndRunJ SumCtorsRunJ FieldSortsJ FormerReadJ
  NativeFam DeclRunJ)
open Ix.Kernel.Model (nativePartsAt? NativeAtRunJ IndRoutesAJ rulesJ)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## The install of a native block at a given index count -/

section

variable {env env₂ : Env .anon} {blk : List (ConstantInfo .anon)} {nP nIdx : Nat}
  {p₀ : NativeParts .anon} {fam : NativeFam .anon}

/-- The recogniser reads the block. -/
theorem NativeAtFacts.recognised (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    nativePartsAt? nP nIdx blk = some p₀ := by
  obtain ⟨hdp, -⟩ := h
  exact hdp

/-- **IxC's record of the install, at the recognised parts.** -/
theorem NativeAtFacts.noRecRunJ (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    DeclNativeNoRecRunJ rulesJ env p₀ env₂ := by
  obtain ⟨-, hnd, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, -,
    hInd, hp, hCtors, hK, hcaps, hop, hsorts, hFOk, hFR, hTbl⟩ := h
  exact ⟨hnd, isRec, _, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hInd, hp, hCtors,
    hK, hcaps, hop, hsorts, hFOk, hTbl, hFR⟩

/-- **The declaration layer's fold invariant at the new environment.** -/
theorem NativeAtFacts.foldInv (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name) (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FoldInv V env → Decl.FoldInv V env₂ :=
  Decl.foldInv_step_indNativeAt hpin hna h.recognised h.noRecRunJ

/-- **The full declaration invariant at the new environment**, where the declared constants'
keys and the keys their types name are not derived and the declared names are distinct. -/
theorem NativeAtFacts.fullDeclInv (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : Decl.DeclNonAux (.indDecl blk nP)) (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FullDeclInv V env → Decl.FullDeclInv V env₂ :=
  Decl.fullDeclInv_step_declRunJA hna (h.declRunJ hpin)

/-- **The store part of the invariant at the new environment.** -/
theorem NativeAtFacts.foldStoreInv (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name) (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam)
    (hS : Decl.FoldStoreInv env) : Decl.FoldStoreInv env₂ :=
  Decl.foldStoreInv_step_declRunJA hS
    (fun blk' _ heq _ => by injection heq with hblk _; subst hblk; exact hna) (h.declRunJ hpin)

/-- **The install's shape**, where every declared constant is stored as declared. -/
theorem NativeAtFacts.installStep (hpin : Ix.Kernel.basisPinHit blk = none)
    (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam)
    (hstored : ∀ ci₀ ∈ blk,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl blk nP) env₂ :=
  Decl.installStep_glue_indNativeAt hpin h.recognised h.noRecRunJ hstored

/-- **The constants the install adds**: the former, the constructors and, at a structure-like
block, the projection table of the family; no recursor. -/
theorem NativeAtFacts.shape (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    ∃ new : List (ConstantInfo .anon), env₂ = ⟨new ++ env.consts⟩ ∧
      ∀ ci ∈ new, (∃ cv caps, ci = .indInfo cv caps) ∨ (∃ cv nP' nF, ci = .ctorInfo cv nP' nF) ∨
        ∃ tbl : Ix.Kernel.ProjTable .anon, ci = .projInfo tbl := by
  obtain ⟨-, -, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, -,
    -, -, -, -, -, -, -, -, -, hTbl⟩ := h
  have hc : (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩).consts =
      ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
        [.indInfo cvS caps]) ++ env.consts := by
    rw [Decl.consts_consSumCtors_eq]
    simp
  have hmem : ∀ ci ∈ (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps],
      (∃ cv caps, ci = .indInfo cv caps) ∨ (∃ cv nP' nF, ci = .ctorInfo cv nP' nF) ∨
        ∃ tbl : Ix.Kernel.ProjTable .anon, ci = .projInfo tbl := by
    intro ci hci
    rcases List.mem_append.mp hci with hct | hind
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hct)
      exact Or.inr (Or.inl ⟨_, _, _, rfl⟩)
    · rw [List.mem_singleton.mp hind]
      exact Or.inl ⟨_, _, rfl⟩
  rcases checkNativeTable_shape hTbl with heq | ⟨tbl, heq, -⟩
  · refine ⟨_, ?_, hmem⟩
    rw [heq]
    exact congrArg Ix.Kernel.Env.mk hc
  · refine ⟨.projInfo tbl :: ((ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p.nP c.2)).reverse ++
      [.indInfo cvS caps]), ?_, ?_⟩
    · rw [heq, hc]
      rfl
    · intro ci hci
      rcases List.mem_cons.mp hci with rfl | hold
      · exact Or.inr (Or.inr ⟨tbl, rfl⟩)
      · exact hmem ci hold

end

/-- **The prefix invariant after the install of a native block at a given index count**, given
its two clauses that read the new family (the load contract at the new environment and η
stability) and that every key stored new resolves. Every other clause is the declaration layer's
step, the table, or kept by constants that are no recursor. -/
theorem PrefixInv.nativeAt {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env env₂ : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)} {nP nIdx : Nat}
    {p₀ : Ix.Kernel.NativeParts .anon} {fam : NativeFam .anon}
    (h : Decl.PrefixInv.{u} E t lim env) (hfacts : NativeAtFacts env env₂ blk nP nIdx p₀ fam)
    (hpin : Ix.Kernel.basisPinHit blk = none) (hna : Decl.DeclNonAux (.indDecl blk nP))
    (hres : ∀ (k : Core.KKey) (ci : ConstantInfo .anon), env₂.find? k = some ci →
      env.find? k = none → k ≠ Core.unresolvedKey)
    (hloads : Core.ScopedLoadFacts (Core.Ctx.stored ⟨E, env₂, t, lim⟩))
    (heta : Decl.EtaStable env₂) :
    Decl.PrefixInv.{u} E t lim env₂ := by
  have hext : Ix.Kernel.EnvExt env env₂ := hfacts.envExt
  have hunres : env₂.find? Core.unresolvedKey = none := by
    cases hf : env₂.find? Core.unresolvedKey with
    | none => rfl
    | some ci => exact absurd rfl (hres _ ci hf h.unresolved)
  have hnaKeys : ∀ ci ∈ blk, Decl.NonAuxKey ci.name := fun ci hci =>
    (hna.1 ci (by simpa [IxVM.Consistency.installs, hpin] using hci)).1
  have hdecl := hfacts.fullDeclInv hpin hna
  have hstore := hfacts.foldStoreInv hpin hnaKeys h.store
  obtain ⟨new, rfl, hkind⟩ := hfacts.shape
  have hnorec : ∀ ci ∈ new, ∀ cv mI rP rls, ci ≠ .recInfo cv mI rP rls := by
    intro ci hci cv mI rP rls he
    rcases hkind ci hci with ⟨cv', caps, h'⟩ | ⟨cv', nP', nF, h'⟩ | ⟨tbl, h'⟩ <;>
      (rw [h'] at he; cases he)
  exact
    { decl := fun V _ => hdecl V (h.decl V)
      store := hstore
      unresolved := hunres
      tableWf := h.tableWf
      companions := CoreCompanions.append_noRec (c := ⟨E, env, t, lim⟩) h.companions
        h.store.store hext hnorec
      loads := hloads
      etaStable := heta }

end IxVM.Refinement.Typing
