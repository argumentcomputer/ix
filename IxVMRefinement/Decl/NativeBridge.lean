import IxVMRefinement.Decl.Modeled
import IxVMRefinement.Decl.Native
import IxVMRefinement.Decl.TwinRec
import IxVMRefinement.Decl.DeclSpecs

/-! # Native declaration steps in the shared fold invariant

Native and twin recursor steps preserve the auxiliary-root and projection-table properties
required by `CleanInstallStep`, as well as the shared declaration fold invariant. The projection
table argument uses the native stages' freshness checks: a new table belongs to the new former.
-/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Env Expr Key Level ConstantVal ConstantInfo NativeParts)
open Ix.Kernel.Semantics (Judgements DeclRunJ IndRoutesJ DeclNativeRunJ DeclNativeNoRecRunJ
  DeclRecTwinRunJ TwinRecPart twinModels twinRecs)
open Ix.Kernel.Model (rulesJ)

private theorem noNewProj_cons {env X : Env .anon} {ci : KConstantInfo}
    (hX : NoNewProjForOld env X) (hshape : ci.name.isProjFnShape = false) :
    NoNewProjForOld env ⟨ci :: X.consts⟩ := by
  intro T hT
  rw [Ix.Kernel.EnvExt.find?_cons_ne
    (Ix.Kernel.Semantics.ne_projTableName_of_shape hshape T)]
  exact hX T hT

private theorem noNewProj_consSumCtors (nP : Nat) :
    ∀ (ctors : List (KConstantVal × Nat)) {env X : Env .anon},
      NoNewProjForOld env X →
      (∀ c ∈ ctors, c.1.name.isProjFnShape = false) →
      NoNewProjForOld env (Ix.Kernel.consSumCtors nP ctors X)
  | [], _, _, hX, _ => hX
  | c :: cs, _, _, hX, hshape =>
    noNewProj_consSumCtors nP cs
      (noNewProj_cons hX (hshape c List.mem_cons_self))
      (fun c' hc' => hshape c' (List.mem_cons_of_mem _ hc'))

private theorem noNewProj_nativeTable {env X env₂ : Env .anon} {p : NativeParts .anon}
    {ctorsA : List (KConstantVal × Nat)} {sortss : List (List Level)}
    (hX : NoNewProjForOld env X) (hfresh : env.find? p.cvT.name = none)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon)
      p ctorsA sortss X = .ok env₂) :
    NoNewProjForOld env env₂ := by
  rcases Ix.Kernel.Model.nativeTable_cases hTbl with rfl | ⟨cA, sorts, bodies, _, _, _, _, rfl⟩
  · exact hX
  · intro T hT
    have hne : p.cvT.name ≠ T := by
      intro heq
      rw [← heq, hfresh] at hT
      exact nomatch hT
    rw [Ix.Kernel.EnvExt.find?_cons_ne (by
      show Ix.Kernel.projTableName p.cvT.name ≠ Ix.Kernel.projTableName T
      intro heq
      change Key.aux p.cvT.name .projTable = Key.aux T .projTable at heq
      injection heq with hname
      exact hne hname)]
    exact hX T hT

/-- A native block adds no projection table for a previously stored key. -/
theorem noNewProj_declNativeRunJ {J : Judgements .anon} {env env₂ : Env .anon}
    {p₀ : NativeParts .anon} (h : DeclNativeRunJ J env p₀ env₂) :
    NoNewProjForOld env env₂ := by
  obtain ⟨_, isRec, env₁, cvTt, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, _, _, _,
    hInd, rfl, hCtors, _, _, _, _, _, _, hRec, hTbl, _⟩ := h
  obtain ⟨hTn, _, hfT, hTsh⟩ := hInd.former
  obtain ⟨cvTa₀, s, bs, cvTa, hc₀, _, _, hSt, rfl, rfl⟩ := hInd
  replace hTn : cvTa.name = p₀.cvT.name := by
    rcases hSt with rfl | ⟨rfl, _, _⟩
    · exact hTn
    · exact hc₀.name_eq
  try dsimp only at hCtors hRec hTbl
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [Ix.Kernel.NativeParts.withKinds]
  generalize hp : (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds = p
    at hCtors hRec hTbl hpT
  have hX₁ : NoNewProjForOld env
      ⟨.indInfo cvTa (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec) :: env.consts⟩ :=
    noNewProj_cons (.refl env) (by rw [hTn]; exact hTsh)
  obtain ⟨hlen, _, hall⟩ := hCtors
  have hshC : ∀ c ∈ ctorsA, c.1.name.isProjFnShape = false := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨_, _, _, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hCn, _, _, hshape⟩ := hrun.names
    rw [hCn]
    exact hshape
  have hX₂ := noNewProj_consSumCtors p.nP ctorsA hX₁ hshC
  obtain ⟨hnR, _, _, hshR⟩ := hRec.recursor
  exact noNewProj_nativeTable
    (noNewProj_cons hX₂ (by show cvRa.name.isProjFnShape = false; rw [hnR]; exact hshR))
    (by rw [hpT]; exact hfT) hTbl

/-- The native route without a recursor has the same projection-table preservation property. -/
theorem noNewProj_declNativeNoRecRunJ {J : Judgements .anon} {env env₂ : Env .anon}
    {p₀ : NativeParts .anon} (h : DeclNativeNoRecRunJ J env p₀ env₂) :
    NoNewProjForOld env env₂ := by
  obtain ⟨_, isRec, env₁, cvTt, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd, rfl,
    hCtors, _, _, _, _, _, hTbl, _⟩ := h
  obtain ⟨hTn, _, hfT, hTsh⟩ := hInd.former
  obtain ⟨cvTa₀, s, bs, cvTa, hc₀, _, _, hSt, rfl, rfl⟩ := hInd
  replace hTn : cvTa.name = p₀.cvT.name := by
    rcases hSt with rfl | ⟨rfl, _, _⟩
    · exact hTn
    · exact hc₀.name_eq
  try dsimp only at hCtors hTbl
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [Ix.Kernel.NativeParts.withKinds]
  generalize hp : (p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds = p
    at hCtors hTbl hpT
  have hX₁ : NoNewProjForOld env
      ⟨.indInfo cvTa (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec) :: env.consts⟩ :=
    noNewProj_cons (.refl env) (by rw [hTn]; exact hTsh)
  obtain ⟨hlen, _, hall⟩ := hCtors
  have hshC : ∀ c ∈ ctorsA, c.1.name.isProjFnShape = false := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨_, _, _, hrun⟩ := hall j (p.ctors[j]) c (List.getElem?_eq_getElem hj') hj
    obtain ⟨hCn, _, _, hshape⟩ := hrun.names
    rw [hCn]
    exact hshape
  exact noNewProj_nativeTable (noNewProj_consSumCtors p.nP ctorsA hX₁ hshC)
    (by rw [hpT]; exact hfT) hTbl

/-- Twin recursor declarations add recursors and model companions, so preserve all old tables. -/
theorem noNewProj_declRecTwinRunJ {J : Judgements .anon} {env env₂ : Env .anon}
    {block : List KConstantInfo} (h : DeclRecTwinRunJ J env block env₂) :
    NoNewProjForOld env env₂ := by
  obtain ⟨ws, _, _, _, rfl, _, _, _, hall⟩ := h
  rw [← List.append_assoc]
  apply NoNewProjForOld.prepend_nonProjTable
  intro ci hci T
  apply Ix.Kernel.Semantics.ne_projTableName_of_shape ?_ T
  rcases List.mem_append.mp hci with hrec | hmod
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hrec
    have hcv := (hall w hw).1
    show w.cvW'.name.isProjFnShape = false
    rw [hcv.name_eq]
    exact hcv.shape
  · obtain ⟨w, _, hw⟩ := List.mem_filterMap.mp hmod
    unfold TwinRecPart.modelInfo? at hw
    obtain ⟨⟨cvm, mval, hint⟩, _, rfl⟩ := Option.map_eq_some_iff.mp hw
    rfl

private theorem cleanInstallStep_of_run {env env₂ : Env .anon} {d : Ix.Kernel.Declaration .anon}
    (hna : DeclNonAux d) (hinst : IxVM.Consistency.InstallStep env d env₂)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂)
    (hproj : NoNewProjForOld env env₂) : CleanInstallStep env d env₂ where
  step := hinst
  auxSynced haux := auxRootSynced_step_declRunJ haux hna hrun
  noNewProj := hproj
  monoSome _ hk := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
    rw [Ix.Kernel.Model.declRunJ_envExt_routes hrun |>.find hci]
    rfl

private theorem nativeInd_clean_run (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {block : List KConstantInfo} {nP : Nat}
    (hna : DeclNonAux (.indDecl block nP)) (hS : DeclStoreInv env)
    (extra : NativeCheckedExtra calls env block nP) :
    ∃ env₂, CleanInstallStep env (.indDecl block nP) env₂ ∧
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
  rcases extra with ⟨p₀, hpin, hparts, hex⟩ | ⟨p₀, hpin, hparts, hex⟩
  · obtain ⟨env₂, hinst, hrun⟩ := nativeWithRec_step hLevels hCore hpin hparts hS hex
    have hd := declRunJ_of_native hpin hparts hrun
    exact ⟨env₂, cleanInstallStep_of_run hna hinst hd (noNewProj_declNativeRunJ hrun), hd⟩
  · obtain ⟨env₂, hinst, hrun⟩ := nativeNoRec_step hLevels hCore hpin hparts hS hex
    have hd := declRunJ_of_nativeNoRec hpin hparts hrun
    exact ⟨env₂, cleanInstallStep_of_run hna hinst hd (noNewProj_declNativeNoRecRunJ hrun), hd⟩

/-- The native declaration result supplies the native seam of the modeled declaration fold. -/
theorem nativeIndStep_of_native (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {block : List KConstantInfo} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hna : DeclNonAux (.indDecl block nP))
    (hfresh : ∀ ci ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci.name = none)
    (extra : NativeCheckedExtra calls env block nP) : NativeIndStep.{u} calls env block nP :=
  declsM_step_of_store hchk hna.2 hfresh (fun hS => nativeInd_clean_run hLevels hCore hna hS extra)

/-- Native blocks preserve the full reader-fold invariant at the same clean installation. -/
theorem nativeInd_full_step (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {block : List KConstantInfo} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hna : DeclNonAux (.indDecl block nP))
    (hfresh : ∀ ci ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci.name = none)
    (extra : NativeCheckedExtra calls env block nP) :
    ∃ env₂, CleanInstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  by_cases hS : DeclStoreInv env
  · obtain ⟨env₂, hclean, hrun⟩ := nativeInd_clean_run hLevels hCore hna hS extra
    exact ⟨env₂, hclean, fullDeclInv_step_declRunJ hna hrun⟩
  · obtain ⟨env₂, hclean⟩ := cleanInstallStep_of_checked_fresh hchk hna.2 hfresh
    exact ⟨env₂, hclean, fun _ _ h => absurd h.declInvM.inv.store hS⟩

private theorem twinRec_clean_run (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {block : List KConstantInfo} {nP : Nat}
    (hna : DeclNonAux (.indDecl block nP)) (hS : DeclStoreInv env)
    (wb : TwinBlockWitness calls env block)
    (hlift : ∀ d ∈ wb.ds, PosSortLift env d.cvW')
    (hNative : NativeTwinInputs rulesJ env (mkTwinRecParts env wb.ds))
    (hModeled : ModeledTwinInputs rulesJ env (mkTwinRecParts env wb.ds)) :
    ∃ env₂, CleanInstallStep env (.indDecl block nP) env₂ ∧
      DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
  obtain ⟨hinst, hrun, hd, _⟩ := twinRec_step_rulesJ hCore nP hS wb hlift hNative hModeled
  exact ⟨_, cleanInstallStep_of_run hna hinst hd (noNewProj_declRecTwinRunJ hrun), hd⟩

/-- Twin recursor blocks also supply the native seam of the modeled declaration fold. -/
theorem nativeIndStep_of_twinRec (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {block : List KConstantInfo} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hna : DeclNonAux (.indDecl block nP))
    (hfresh : ∀ ci ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci.name = none)
    (wb : TwinBlockWitness calls env block)
    (hlift : ∀ d ∈ wb.ds, PosSortLift env d.cvW')
    (hNative : NativeTwinInputs rulesJ env (mkTwinRecParts env wb.ds))
    (hModeled : ModeledTwinInputs rulesJ env (mkTwinRecParts env wb.ds)) :
    NativeIndStep.{u} calls env block nP :=
  declsM_step_of_store hchk hna.2 hfresh
    (fun hS => twinRec_clean_run hCore hna hS wb hlift hNative hModeled)

/-- Twin recursor blocks preserve the full reader-fold invariant. -/
theorem twinRec_full_step (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Env .anon} {block : List KConstantInfo} {nP : Nat}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hna : DeclNonAux (.indDecl block nP))
    (hfresh : ∀ ci ∈ IxVM.Consistency.installs (.indDecl block nP), env.find? ci.name = none)
    (wb : TwinBlockWitness calls env block)
    (hlift : ∀ d ∈ wb.ds, PosSortLift env d.cvW')
    (hNative : NativeTwinInputs rulesJ env (mkTwinRecParts env wb.ds))
    (hModeled : ModeledTwinInputs rulesJ env (mkTwinRecParts env wb.ds)) :
    ∃ env₂, CleanInstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ := by
  by_cases hS : DeclStoreInv env
  · obtain ⟨env₂, hclean, hrun⟩ := twinRec_clean_run hCore hna hS wb hlift hNative hModeled
    exact ⟨env₂, hclean, fullDeclInv_step_declRunJ hna hrun⟩
  · obtain ⟨env₂, hclean⟩ := cleanInstallStep_of_checked_fresh hchk hna.2 hfresh
    exact ⟨env₂, hclean, fun _ _ h => absurd h.declInvM.inv.store hS⟩

/-- Equivalent universe levels are accepted by the semantic wrapper relation. -/
theorem wrapRel_zero_max_zero (find? : KKey → Option KConstantInfo) :
    Ix.Kernel.Semantics.WrapRel find? (.sort .zero) (.sort (.max .zero .zero)) :=
  .sort (fun _ => rfl)

end IxVM.Refinement.Decl
