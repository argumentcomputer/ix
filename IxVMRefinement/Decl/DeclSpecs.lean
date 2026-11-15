import IxVMRefinement.Core.AllSteps
import IxVMRefinement.RoleVal.LookupSpec
import IxVMRefinement.Decl.Modeled
import IxVMRefinement.Decl.DeclsGlue

/-! # Unconditional role/callee specifications and unified declaration fold invariant

Provides the foundational specifications and combined invariant for the declaration fold:

* **`rolesSpec`**: discharges `RolesSpec` unconditionally from `IxVMRefinement.RoleVal.LookupSpec`
  (backed by `IxVMRefinement.Roles.Steps`).
* **`calleesSpec`**: discharges `CalleesSpec` (all 15 functions of `Specs.Callees.Fn` under
  `CoreFacts c`) unconditionally from `IxVMRefinement.Core.AllSteps`.
* **`FullDeclInv`**: combines `DeclInvM` (`DeclInv` + `AuxRootSynced`) with `StrongEnvProps`,
  `EtaCtorStored`, and `EtaShape` (`FoldInv`), proving initialization on `Env.empty`, projection to
  `EnvModelOk V .verified env ∧ StrongEnvProps env`, conversions to/from `FoldInv`, and uniform
  preservation across every `DeclRunJ rulesJ (IndRoutesJ rulesJ env)` step on `DeclNonAux`
  declarations. -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Mode Expr Level LevelParam ConstantVal ConstantInfo Declaration RecRule
  BasisKind QuotKind IndCaps NativeParts InductiveShape ProjTable Env EnvExt Key)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ ValueFrontRunJ
  DeclDefnRunJ DeclThmRunJ DeclOpaqueRunJ DeclAxiomRunJ DeclBasisRun BasisInstallRun
  DeclRunJ DeclsRunJ IndRoutesJ DeclIndRunJ IndMembersRunJ ProvisionRecsRunJ IndRecsFoldRunJ
  DeclNativeRunJ DeclNativeNoRecRunJ DeclRecTwinRunJ TwinRecPart twinModels twinRecs
  SumCtorsRunJ nativePartsNoRec?)
open Ix.Kernel.Model (rulesJ EnvModelT EnvModelOk)

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Section 1: Unconditional `RolesSpec` and `CalleesSpec` -/

/-- `RolesSpec` holds unconditionally whenever `c.t.wf = true`. -/
theorem rolesSpec : RolesSpec :=
  fun c hwf f args h r h' calls ev =>
    IxVM.Refinement.RoleVal.roles_fn_spec c hwf f args h r h' calls ev

/-- `CalleesSpec` holds unconditionally from `Core.all_steps` and `Registry.induction`. -/
theorem calleesSpec : CalleesSpec :=
  fun c hc f args h r h' calls ev =>
    Registry.induction c (all_steps c hc) (.callees f) args h r h' calls ev

/-- Unconditional soundness of `KernelCheck::projection_addr_ctor` (independent of `CoreFacts c`). -/
theorem projectionAddrCtorSpec (c : Ctx) {args : List (SourceValue F)} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelCheck::projection_addr_ctor" args h r h' calls) :
    Specs.Callees.projection_addr_ctor c args h r h' calls :=
  projection_addr_ctor_step c ev

/-! ## Section 2: `FullDeclInv` and `FoldInv` / `DeclInvM` bridges -/

/-- Unified declaration fold invariant combining `DeclInvM` (`DeclInv` + `AuxRootSynced`) with
`StrongEnvProps`, `EtaCtorStored`, and `EtaShape`. -/
structure FullDeclInv (V : Type u) [Ix.Kernel.SetTheory V] (env : Env .anon) : Prop where
  declInvM : DeclInvM V env
  strongProps : StrongEnvProps env
  etaCtorStored : EtaCtorStored env
  etaShape : EtaShape env

/-- `FullDeclInv` holds of the empty environment in every set theory. -/
theorem FullDeclInv.empty : ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V Env.empty :=
  fun V _ => ⟨DeclInvM.empty V, strongEnvProps_empty, EtaCtorStored.empty, EtaShape.empty⟩

/-- `FullDeclInv` projects to `EnvModelOk V .verified env ∧ StrongEnvProps env`. -/
theorem FullDeclInv.ok :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V] (env : Env .anon),
      FullDeclInv V env → EnvModelOk V .verified env ∧ StrongEnvProps env :=
  fun _ _ _ h => ⟨h.declInvM.toEnvModelOk, h.strongProps⟩

/-- `FullDeclInv` projects to `FoldStoreInv`. -/
theorem FullDeclInv.toFoldStoreInv {V : Type u} [Ix.Kernel.SetTheory V] {env : Env .anon}
    (h : FullDeclInv V env) : FoldStoreInv env where
  store := h.declInvM.inv.store.store
  thmTyped := h.declInvM.inv.store.thmTyped
  recK := h.declInvM.inv.store.recK
  etaTowers := h.declInvM.inv.store.etaTowers
  strongProps := h.strongProps
  recShape := h.declInvM.inv.store.recShape
  etaCtorStored := h.etaCtorStored
  etaShape := h.etaShape

/-- `FullDeclInv` projects to `FoldInv`. -/
theorem FullDeclInv.toFoldInv {V : Type u} [Ix.Kernel.SetTheory V] {env : Env .anon}
    (h : FullDeclInv V env) : FoldInv V env :=
  ⟨h.declInvM.inv.model, h.toFoldStoreInv⟩

/-- Reconstruct `DeclStoreInv` from `FoldStoreInv`. -/
theorem declStoreInv_of_foldStoreInv {env : Env .anon} (h : FoldStoreInv env) :
    DeclStoreInv env where
  store := h.store
  thmTyped := h.thmTyped
  recK := h.recK
  etaTowers := h.etaTowers
  tableBodies := h.tableBodies
  recShape := h.recShape

/-- Reconstruct `FullDeclInv` from `FoldInv` and `AuxRootSynced`. -/
theorem FullDeclInv.ofFoldInv {V : Type u} [Ix.Kernel.SetTheory V] {env : Env .anon}
    (hf : FoldInv V env) (haux : AuxRootSynced env) : FullDeclInv V env where
  declInvM := ⟨⟨hf.model, declStoreInv_of_foldStoreInv hf.store⟩, haux⟩
  strongProps := hf.store.strongProps
  etaCtorStored := hf.store.etaCtorStored
  etaShape := hf.store.etaShape

/-- Lift a `FoldInv` step paired with `AuxRootSynced` preservation to `FullDeclInv`. -/
theorem FullDeclInv.step_of_foldInv_aux {env env₂ : Env .anon}
    (hfold : ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂)
    (haux : AuxRootSynced env → AuxRootSynced env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ :=
  fun V _ h => FullDeclInv.ofFoldInv (hfold V h.toFoldInv) (haux h.declInvM.auxSynced)

/-- Lift a `FoldInv` step paired with `CleanInstallStep` to `FullDeclInv`. -/
theorem FullDeclInv.step_of_foldInv_clean {d : Declaration .anon} {env env₂ : Env .anon}
    (hclean : CleanInstallStep env d env₂)
    (hfold : ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ :=
  FullDeclInv.step_of_foldInv_aux hfold hclean.auxSynced

/-! ## Section 3: `AuxRootSynced` and `FullDeclInv` preservation along `DeclRunJ` -/

theorem isBaseKey_iff_nonAuxKey {k : KKey} : isBaseKey k = true ↔ NonAuxKey k := by
  cases k <;> simp [isBaseKey, NonAuxKey]

theorem isBaseKey_of_nonAuxKey {k : KKey} (h : NonAuxKey k) : isBaseKey k = true :=
  isBaseKey_iff_nonAuxKey.mpr h

theorem isBaseKey_of_declNonAux_axiom {cv : ConstantVal .anon}
    (hna : DeclNonAux (.axiomDecl cv)) : isBaseKey cv.name = true := by
  by_cases hskip : cv.name = Ix.Kernel.quotSoundName ∨ IxVM.Consistency.inertKey cv.name = true
  · rcases hskip with heq | hinert
    · rw [heq]; rfl
    · cases hname : cv.name with
      | role _ => rfl
      | id _ => rw [hname] at hinert; exact nomatch hinert
      | aux _ _ => rw [hname] at hinert; exact nomatch hinert
  · have hmem : ConstantInfo.axiomInfo cv ∈ IxVM.Consistency.installs (.axiomDecl cv) := by
      simp [IxVM.Consistency.installs, hskip]
    exact isBaseKey_of_nonAuxKey (hna.1 (.axiomInfo cv) hmem).1

private theorem basisInstallRun_env_eq {env env₂ : Env .anon} :
    ∀ (decls : List (ConstantInfo .anon)),
      BasisInstallRun env decls env₂ → env₂ = ⟨decls.reverse ++ env.consts⟩
  | [], h => by
    change env₂ = env at h
    simpa using h
  | ci :: rest, ⟨_, hrest⟩ => by
    have heq := basisInstallRun_env_eq rest hrest
    simpa [List.reverse_cons, List.append_assoc] using heq

private theorem auxRootSynced_of_base_prepend {env : Env .anon} {new : List (ConstantInfo .anon)}
    (h : AuxRootSynced env) (hbase : ∀ ci ∈ new, isBaseKey ci.name = true) :
    AuxRootSynced ⟨new ++ env.consts⟩ :=
  h.of_prepend fun ci hci => by
    rw [base_of_isBaseKey (hbase ci hci)]
    exact env_find?_isSome_of_mem_prefix hci

private theorem indMembersRunJ_consts_eq {J : Judgements .anon} {blockNames : List KKey}
    {caps : IndCaps .anon} :
    ∀ (ms : List (ConstantInfo .anon)) {acc envM : Env .anon},
      IndMembersRunJ J blockNames caps acc ms envM →
      ∃ newM, envM = ⟨newM ++ acc.consts⟩ ∧ newM.map (·.name) = ms.reverse.map (·.name)
  | [], acc, envM, h => ⟨[], by subst h; rfl, rfl⟩
  | ci :: rest, acc, envM, ⟨cvA, hmv, hrest⟩ => by
    obtain ⟨type', _, rfl, _⟩ := hmv
    cases ci with
    | indInfo cvI _ =>
      obtain ⟨newM, heq, hnames⟩ := indMembersRunJ_consts_eq rest hrest
      refine ⟨newM ++ [.indInfo ⟨cvI.name, cvI.levelParams, type'⟩ caps], ?_, ?_⟩
      · simpa [List.append_assoc, ConstantInfo.toConstantVal] using heq
      · rw [List.map_append, List.reverse_cons, List.map_append, hnames]; rfl
    | ctorInfo cvC nP nF =>
      obtain ⟨newM, heq, hnames⟩ := indMembersRunJ_consts_eq rest hrest
      refine ⟨newM ++ [.ctorInfo ⟨cvC.name, cvC.levelParams, type'⟩ nP nF], ?_, ?_⟩
      · simpa [List.append_assoc, ConstantInfo.toConstantVal] using heq
      · rw [List.map_append, List.reverse_cons, List.map_append, hnames]; rfl
    | axiomInfo _ | defnInfo _ _ _ | thmInfo _ _ | recInfo _ _ _ _ | projInfo _ =>
      exact hrest.elim

private theorem provisionRecsRunJ_names_eq {J : Judgements .anon} {blockNames : List KKey} :
    ∀ (recs : List (ConstantInfo .anon)) {acc envSelf : Env .anon}
      {checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon))},
      ProvisionRecsRunJ J blockNames acc recs envSelf checked →
      checked.map (·.1.name) = recs.map (·.name)
  | [], _, _, _, ⟨_, hchk⟩ => by subst hchk; rfl
  | ci :: rest, _, _, _, ⟨_, _, _, _, _, _, ⟨_, _, rfl, _⟩, hprov, hchk⟩ => by
    subst hchk
    have hci_name : ci.name = ci.toConstantVal.name := by cases ci <;> rfl
    simp [provisionRecsRunJ_names_eq rest hprov, hci_name]

private theorem indRecsFoldRunJ_consts_eq {J : Judgements .anon} {blockNames : List KKey}
    {envBase envSelf : Env .anon} :
    ∀ (checked : List (ConstantVal .anon × Nat × Nat × List (RecRule .anon)))
      {done : List (ConstantInfo .anon)} {acc out : Env .anon},
      IndRecsFoldRunJ J blockNames envBase envSelf ⟨done ++ acc.consts⟩ checked out →
      ∃ newR, out = ⟨(newR ++ done) ++ acc.consts⟩ ∧
        newR.map (·.name) = checked.reverse.map (·.1.name)
  | [], done, acc, out, h => ⟨[], by subst h; rfl, rfl⟩
  | c :: rest, done, acc, out, ⟨rules', _, hfold⟩ => by
    have hfold' :
        IndRecsFoldRunJ J blockNames envBase envSelf
          ⟨(.recInfo c.1 c.2.1 c.2.2.1 rules' :: done) ++ acc.consts⟩ rest out := hfold
    obtain ⟨newR, hout, hnames⟩ := indRecsFoldRunJ_consts_eq rest hfold'
    refine ⟨newR ++ [.recInfo c.1 c.2.1 c.2.2.1 rules'], ?_, ?_⟩
    · simpa [List.append_assoc] using hout
    · rw [List.map_append, List.reverse_cons, List.map_append, hnames]
      rfl

private theorem sumCtorsRunJ_names_eq {J : Judgements .anon}
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

private theorem consSumCtors_consts_append (nP : Nat) :
    ∀ (cs : List (ConstantVal .anon × Nat)) (consts : List (ConstantInfo .anon)),
      (Ix.Kernel.consSumCtors nP cs ⟨consts⟩).consts =
        (cs.reverse.map fun c => ConstantInfo.ctorInfo c.1 nP c.2) ++ consts
  | [], consts => rfl
  | c :: cs, consts => by
    simp [Ix.Kernel.consSumCtors, consSumCtors_consts_append nP cs (.ctorInfo c.1 nP c.2 :: consts),
      List.reverse_cons, List.map_append, List.append_assoc]

private theorem checkNativeTable_env_cases {p : NativeParts .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    {envX env₂ : Env .anon}
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss envX =
      .ok env₂) :
    env₂ = envX ∨ ∃ tbl : ProjTable .anon,
      tbl.structName = p.cvT.name ∧ env₂ = ⟨.projInfo tbl :: envX.consts⟩ := by
  unfold Ix.Kernel.checkNativeTable at hTbl
  cases ctorsA with
  | nil =>
    simp only at hTbl
    injection hTbl with heq
    exact Or.inl heq.symm
  | cons cA cs =>
    cases cs with
    | cons _ _ =>
      simp only at hTbl
      injection hTbl with heq
      exact Or.inl heq.symm
    | nil =>
      cases sortss with
      | nil =>
        simp only at hTbl
        injection hTbl with heq
        exact Or.inl heq.symm
      | cons sorts srest =>
        cases srest with
        | cons _ _ =>
          simp only at hTbl
          injection hTbl with heq
          exact Or.inl heq.symm
        | nil =>
          simp only at hTbl
          split at hTbl
          · obtain ⟨bodies, -, -, -, -, rfl⟩ := Ix.Kernel.checkStructProjTable_inv hTbl
            exact Or.inr ⟨⟨p.cvT.name, p.cvT.levelParams, p.nP, cA.1.name, cA.2, p.resSort,
              bodies, Ix.Kernel.structProjGuards cA.1.type p.nP cA.2 sorts, 1⟩, rfl, rfl⟩
          · injection hTbl with heq
            exact Or.inl heq.symm

/-- Every `DeclRunJ rulesJ (IndRoutesJ rulesJ env)` step on a `DeclNonAux` declaration preserves
`AuxRootSynced`. -/
theorem auxRootSynced_step_declRunJ {env env₂ : Env .anon} {d : Declaration .anon}
    (haux : AuxRootSynced env) (hna : DeclNonAux d)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    AuxRootSynced env₂ := by
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', _, -, rfl, -, -⟩ := hrun
    have hb : isBaseKey cv.name = true :=
      isBaseKey_of_nonAuxKey (hna.1 (.defnInfo cv value hint) (List.mem_singleton.mpr rfl)).1
    exact haux.cons_of_root_stored (Or.inl (base_of_isBaseKey hb))
  | thmDecl cv value =>
    obtain ⟨type', value', _, -, -, rfl⟩ := hrun
    have hb : isBaseKey cv.name = true :=
      isBaseKey_of_nonAuxKey (hna.1 (.thmInfo cv value) (List.mem_singleton.mpr rfl)).1
    exact haux.cons_of_root_stored (Or.inl (base_of_isBaseKey hb))
  | opaqueDecl cv value =>
    obtain ⟨type', value', _, -, rfl⟩ := hrun
    have hb : isBaseKey cv.name = true :=
      isBaseKey_of_nonAuxKey (hna.1 (.axiomInfo cv) (List.mem_singleton.mpr rfl)).1
    exact haux.cons_of_root_stored (Or.inl (base_of_isBaseKey hb))
  | axiomDecl cv =>
    have hb : isBaseKey cv.name = true := isBaseKey_of_declNonAux_axiom hna
    rcases hrun with ⟨-, rfl⟩ | ⟨type', _, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
    · exact haux
    · exact haux.cons_of_root_stored (Or.inl (base_of_isBaseKey hb))
    · exact haux
  | basisDecl kind =>
    rw [basisInstallRun_env_eq kind.declsA hrun.2]
    exact auxRootSynced_of_base_prepend haux fun ci hci =>
      List.all_eq_true.mp (basis_declsA_isBaseKey kind) ci (List.mem_reverse.mp hci)
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · rw [basisInstallRun_env_eq BasisKind.quotK.declsA hrun.2]
      exact auxRootSynced_of_base_prepend haux fun ci hci =>
        List.all_eq_true.mp (basis_declsA_isBaseKey .quotK) ci (List.mem_reverse.mp hci)
    · subst hrun; exact haux
  | indDecl block nP =>
    cases hpin : Ix.Kernel.basisPinHit block with
    | some kind =>
      have hrun' : DeclBasisRun env kind env₂ := by simpa [DeclRunJ, hpin] using hrun
      rw [basisInstallRun_env_eq kind.declsA hrun'.2]
      exact auxRootSynced_of_base_prepend haux fun ci hci =>
        List.all_eq_true.mp (basis_declsA_isBaseKey kind) ci (List.mem_reverse.mp hci)
    | none =>
      have hblk_base : ∀ ci₀ ∈ block, isBaseKey ci₀.name = true := by
        intro ci₀ hci₀
        have hm : ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP) := by
          simpa [IxVM.Consistency.installs, hpin] using hci₀
        exact isBaseKey_of_nonAuxKey (hna.1 ci₀ hm).1
      have hroutes : IndRoutesJ rulesJ env block nP env₂ := by simpa [DeclRunJ, hpin] using hrun
      rcases hroutes with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩ | hT
      · obtain ⟨caps₀, cs, mI₀, rP₀, rules₀, hblk_eq, hctors₀⟩ := nativeParts?_block_eq hdp
        obtain ⟨_, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, _, _, _, hInd,
          hp, hCtors, _, _, _, _, _, _, _, hRec, hTbl, _⟩ := hN
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
        have hp_cvR : p.cvR = p₀.cvR := by
          rw [hp, hp₁]; simp [NativeParts.withKinds, NativeParts.complete, InductiveShape.withSort]
        have hctorsA_names : ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) := by
          rw [sumCtorsRunJ_names_eq hCtors, hp_ctors]
        obtain ⟨hnR, -, -, -⟩ := hRec.recursor
        let indCI : ConstantInfo .anon := .indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)
        let newCtors : List (ConstantInfo .anon) :=
          ctorsA.reverse.map fun c => .ctorInfo c.1 p.nP c.2
        let recCI : ConstantInfo .anon :=
          .recInfo cvRa p.majorIdx p.rulePrefix
            (Ix.Kernel.sumRules (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP
              p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        let coreNew : List (ConstantInfo .anon) := recCI :: newCtors ++ [indCI]
        have henvX :
            (⟨recCI :: (Ix.Kernel.consSumCtors p.nP ctorsA env₁).consts⟩ : Env .anon) =
              ⟨coreNew ++ env.consts⟩ := by
          rw [henv₁, consSumCtors_consts_append]
          simp [coreNew, newCtors, indCI, List.append_assoc]
        have hcore_base : ∀ c ∈ coreNew, isBaseKey c.name = true := by
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hrest
          · have hmemR : ConstantInfo.recInfo p₀.cvR mI₀ rP₀ rules₀ ∈ block := by
              rw [hblk_eq]
              exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
            have hnameR : recCI.name = p₀.cvR.name := by
              show cvRa.name = p₀.cvR.name
              rw [hnR, hp_cvR]
            rw [hnameR]
            exact hblk_base _ hmemR
          · rcases List.mem_append.mp hrest with hct | hind
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
                exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨c', hc', rfl⟩))
              rw [← hxeq]
              exact hblk_base _ hmemC
            · obtain rfl := List.mem_singleton.mp hind
              have hmemT : ConstantInfo.indInfo p₀.cvT caps₀ ∈ block := by
                rw [hblk_eq]; exact List.mem_cons_self
              show isBaseKey cvS.name = true
              rw [hcvS_name]
              exact hblk_base _ hmemT
        have hauxX : AuxRootSynced ⟨coreNew ++ env.consts⟩ :=
          auxRootSynced_of_base_prepend haux hcore_base
        rcases checkNativeTable_env_cases hTbl with rfl | ⟨tbl, hsn, rfl⟩
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
            List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
          exact env_find?_isSome_of_mem_prefix hind_mem
      · obtain ⟨hblk_split, envM, hmem, hrecs⟩ := hM
        obtain ⟨newM, heqM, hnamesM⟩ := indMembersRunJ_consts_eq _ hmem
        have hbaseM : ∀ c ∈ newM, isBaseKey c.name = true := by
          intro c hc
          have hk : c.name ∈ newM.map (·.name) := List.mem_map_of_mem hc
          rw [hnamesM] at hk
          obtain ⟨ci₀, hci₀, hnm⟩ := List.mem_map.mp hk
          rw [← hnm]
          exact hblk_base ci₀ (by rw [hblk_split]; exact List.mem_append_left _ (List.mem_reverse.mp hci₀))
        have hauxM : AuxRootSynced envM := by
          rw [heqM]; exact auxRootSynced_of_base_prepend haux hbaseM
        rcases hrecs with ⟨_, rfl⟩ | ⟨_, _, envSelf, checked, hprov, hfold⟩
        · exact hauxM
        · have hfold' :
              IndRecsFoldRunJ rulesJ (block.map (·.name)) envM envSelf ⟨[] ++ envM.consts⟩
                checked env₂ := hfold
          obtain ⟨newR, hout, hnamesR⟩ := indRecsFoldRunJ_consts_eq checked hfold'
          simp only [List.append_nil] at hout
          rw [hout]
          refine auxRootSynced_of_base_prepend hauxM fun c hc => ?_
          have hk : c.name ∈ newR.map (·.name) := List.mem_map_of_mem hc
          rw [hnamesR, List.map_reverse] at hk
          have hk' : c.name ∈ checked.map (·.1.name) := List.mem_reverse.mp hk
          rw [provisionRecsRunJ_names_eq _ hprov] at hk'
          obtain ⟨ci₀, hci₀, hnm⟩ := List.mem_map.mp hk'
          rw [← hnm]
          exact hblk_base ci₀ (by rw [hblk_split]; exact List.mem_append_right _ hci₀)
      · obtain ⟨caps₀, cs, hblk_eq, hctors₀⟩ := nativePartsNoRec?_block_eq hdp
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
          rw [sumCtorsRunJ_names_eq hCtors, hp_ctors]
        let indCI : ConstantInfo .anon := .indInfo cvS (Ix.Kernel.nativeCapsAt p₁ isRec)
        let newCtors : List (ConstantInfo .anon) :=
          ctorsA.reverse.map fun c => .ctorInfo c.1 p.nP c.2
        let coreNew : List (ConstantInfo .anon) := newCtors ++ [indCI]
        have henvX : Ix.Kernel.consSumCtors p.nP ctorsA env₁ = ⟨coreNew ++ env.consts⟩ := by
          rw [henv₁]
          exact congrArg Env.mk (by rw [consSumCtors_consts_append]; simp [coreNew, newCtors, indCI])
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
          auxRootSynced_of_base_prepend haux hcore_base
        rcases checkNativeTable_env_cases hTbl with rfl | ⟨tbl, hsn, rfl⟩
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
      · obtain ⟨ws, _, _, hblk_ws, henv₂, _, _, _, hmembers⟩ := hT
        have henv₂' : env₂ = ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ := by
          simpa [List.append_assoc] using henv₂
        rw [henv₂']
        refine haux.of_prepend fun ci hci => ?_
        rcases List.mem_append.mp hci with hrec | hmod
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
          have hw_name : w.cvW'.name = w.cvW.name := (hmembers w hw).1.name_eq
          have hmemW : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ block := by
            rw [hblk_ws]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
          have hbW : isBaseKey w.cvW'.name = true := by
            rw [hw_name]; exact hblk_base _ hmemW
          have hc_mem :
              ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' ∈ twinRecs ws ++ twinModels ws :=
            List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
          show (Env.find? ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ w.cvW'.name.base).isSome =
            true
          rw [base_of_isBaseKey hbW]
          exact env_find?_isSome_of_mem_prefix hc_mem
        · obtain ⟨w, hw, hmi⟩ := List.mem_filterMap.mp hmod
          unfold TwinRecPart.modelInfo? at hmi
          obtain ⟨⟨cvm, mval, hint⟩, _, rfl⟩ := Option.map_eq_some_iff.mp hmi
          have hw_name : w.cvW'.name = w.cvW.name := (hmembers w hw).1.name_eq
          have hmemW : ConstantInfo.recInfo w.cvW w.mI w.rP w.rulesW ∈ block := by
            rw [hblk_ws]; exact List.mem_map.mpr ⟨w, hw, rfl⟩
          have hbW : isBaseKey w.cvW.name = true := hblk_base _ hmemW
          have hbase_mod : (Ix.Kernel.auxKey w.cvW.name .model).base = w.cvW'.name := by
            show w.cvW.name.base = w.cvW'.name
            rw [base_of_isBaseKey hbW, hw_name]
          show (Env.find? ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩
            (Ix.Kernel.auxKey w.cvW.name .model).base).isSome = true
          rw [hbase_mod]
          have hc_mem :
              ConstantInfo.recInfo w.cvW' w.mI w.rP w.rulesW' ∈ twinRecs ws ++ twinModels ws :=
            List.mem_append_left _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
          exact env_find?_isSome_of_mem_prefix hc_mem

/-- Uniform one-step preservation of `FullDeclInv` along `DeclRunJ rulesJ (IndRoutesJ rulesJ env)`
on any `DeclNonAux` declaration. -/
theorem fullDeclInv_step_declRunJ {env env₂ : Env .anon} {d : Declaration .anon}
    (hna : DeclNonAux d)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  refine FullDeclInv.step_of_foldInv_aux (foldInv_step_declRunJ ?_ hd)
    (fun haux => auxRootSynced_step_declRunJ haux hna hd)
  intro block nP heq hpin ci hci
  subst heq
  have hm : ci ∈ IxVM.Consistency.installs (.indDecl block nP) := by
    simpa [IxVM.Consistency.installs, hpin] using hci
  exact (hna.1 ci hm).1

end IxVM.Refinement.Decl
