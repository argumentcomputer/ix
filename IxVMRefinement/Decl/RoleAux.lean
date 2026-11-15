import IxVMRefinement.Decl.DeclSpecs

/-! # Auxiliary declaration groups

Generated model declarations precede the base declaration that owns them. Their intermediate
states need the fold invariant, while auxiliary-root synchronization is restored at the group
boundary. Projection tables of auxiliary structures satisfy the restriction invariant because
the structures themselves are removed from the claimed environment.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open IxVM.Refinement.Core

universe u

private theorem auxiliary_ind_not_kept {env : Env .anon} {k : KKey}
    {cv : ConstantVal .anon} {caps : IndCaps .anon}
    (haux : ∃ root tag, k = .aux root tag)
    (hf : env.find? k = some (.indInfo cv caps)) :
    ¬ IxVM.Consistency.KeptKey env k := by
  obtain ⟨root, tag, rfl⟩ := haux
  intro hk
  have hname : cv.name = .aux root tag := Ix.Kernel.Semantics.Env.find?_name hf
  have hkept := hk (.indInfo cv caps) hf
  simp [IxVM.Consistency.isModelAux, ConstantInfo.name, ConstantInfo.toConstantVal, hname] at hkept

private theorem nativeTable_newProj_not_kept
    {env₀ X env₂ : Env .anon} {p : NativeParts .anon}
    {ctorsA : List (ConstantVal .anon × Nat)} {sortss : List (List KLevel)}
    (hX : NewSat env₀ X NotProj)
    (haux : ∃ root tag, p.cvT.name = .aux root tag)
    (hformer : ∃ cv caps, X.find? p.cvT.name = some (.indInfo cv caps))
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss X = .ok env₂) :
    ∀ n tbl, env₂.find? n = some (.projInfo tbl) → env₀.find? n = none →
      ¬ IxVM.Consistency.KeptKey env₂ tbl.structName := by
  intro n tbl hf hn
  have hold : ∀ {t : ProjTable .anon}, X.find? n = some (.projInfo t) → False := by
    intro t hx
    rcases hX _ _ hx with old | added
    · rw [old] at hn; cases hn
    · exact added t rfl
  rcases Ix.Kernel.Model.nativeTable_cases hTbl with rfl | ⟨cA, sorts, bodies, rfl, rfl, _, _, rfl⟩
  · exact (hold hf).elim
  · rw [Ix.Kernel.Env.find?_cons] at hf
    split at hf
    · obtain rfl := ConstantInfo.projInfo.inj (Option.some.inj hf)
      obtain ⟨cv, caps, hcv⟩ := hformer
      apply auxiliary_ind_not_kept haux
      rw [Ix.Kernel.Env.find?_cons]
      split
      · next heq => exact (auxKey_ne_self p.cvT.name .projTable heq).elim
      · exact hcv
    · exact (hold hf).elim

/-- An all-auxiliary inductive block keeps projection restriction facts. -/
theorem strongEnvProps_auxIndRunJ {env env₂ : Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hS : Ix.Kernel.Open.StoreInv env) (h : StrongEnvProps env)
    (haux : ∀ ci ∈ block, ∃ root tag, ci.name = .aux root tag)
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hrun : IndRoutesJ rulesJ env block nP env₂) :
    StrongEnvProps env₂ := by
  have hext := Ix.Kernel.Semantics.indRoutesJ_envExt hrun
  have hdecl : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env (.indDecl block nP) env₂ := by
    simpa only [DeclRunJ, hpin] using hrun
  have htb := Ix.Kernel.Model.tableBodies_declRunJ hS h.1 hdecl
  rcases hrun with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩ | hT
  · obtain ⟨caps₀, cs, mI₀, rP₀, rules₀, hblk, _⟩ := nativeParts?_block_eq hdp
    have haux₀ : ∃ root tag, p₀.cvT.name = .aux root tag :=
      haux (.indInfo p₀.cvT caps₀) (by rw [hblk]; exact List.mem_cons_self)
    obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, _, _, _, hInd,
      hp, hCtors, _, _, _, _, _, _, hRec, hTbl, _⟩ := hN
    have front := Ix.Kernel.Model.nativeFront (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e)
      hS (Ix.Kernel.Model.nativeRecog_of hdp) hnd hInd hp hCtors
    have hpT : p.cvT = p₀.cvT := by
      obtain ⟨_, s, _, _, _, hp₁, _, _⟩ := hInd.shape
      rw [hp, hp₁]
      rfl
    obtain ⟨cvS, caps, hfT, _, _⟩ := front.former
    obtain ⟨hnR, _, hfR, _⟩ := hRec.recursor
    have hfreshR : (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name = none := by
      rw [hnR]; exact hfR
    refine strongEnvProps_step hext.find h htb fun n tbl hf hn => Or.inr ?_
    apply nativeTable_newProj_not_kept (hTbl := hTbl) ?_ (by simpa only [hpT] using haux₀) ?_ n tbl hf hn
    · obtain ⟨_, _, _, cvS₁, _, _, _, _, _, henv₁⟩ := hInd
      have h₁ : NewSat env env₁ NotProj := by
        rw [henv₁]; exact NewSat.cons (fun _ heq => nomatch heq)
      exact h₁.trans
        ((Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq)).trans
          (NewSat.cons (fun _ heq => nomatch heq)))
    · exact ⟨cvS, caps, Ix.Kernel.Env.find?_cons_of_fresh hfreshR hfT⟩
  · exact strongEnvProps_step_noProj hext.find h
      (Ix.Kernel.Model.modeled_newSat (fun _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hM)
  · obtain ⟨caps₀, cs, hblk, _⟩ := nativePartsNoRec?_block_eq hdp
    have haux₀ : ∃ root tag, p₀.cvT.name = .aux root tag :=
      haux (.indInfo p₀.cvT caps₀) (by rw [hblk]; exact List.mem_cons_self)
    obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, _, _, _, hInd,
      hp, hCtors, _, _, _, _, _, hTbl, _⟩ := hN
    have front := Ix.Kernel.Model.nativeFront (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e)
      hS (Ix.Kernel.Model.nativeRecog_noRec hdp) hnd hInd hp hCtors
    have hpT : p.cvT = p₀.cvT := by
      obtain ⟨_, s, _, _, _, hp₁, _, _⟩ := hInd.shape
      rw [hp, hp₁]
      rfl
    obtain ⟨cvS, caps, hfT, _, _⟩ := front.former
    refine strongEnvProps_step hext.find h htb fun n tbl hf hn => Or.inr ?_
    apply nativeTable_newProj_not_kept (hTbl := hTbl) ?_ (by simpa only [hpT] using haux₀) ⟨cvS, caps, hfT⟩ n tbl hf hn
    obtain ⟨_, _, _, cvS₁, _, _, _, _, _, henv₁⟩ := hInd
    have h₁ : NewSat env env₁ NotProj := by
      rw [henv₁]; exact NewSat.cons (fun _ heq => nomatch heq)
    exact h₁.trans (Ix.Kernel.Model.consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq))
  · exact strongEnvProps_step_noProj hext.find h
      (Ix.Kernel.Model.twin_newSat (fun _ _ _ _ heq => nomatch heq)
        (fun _ _ _ _ _ heq => nomatch heq) hT)

/-- All-auxiliary generated declarations preserve projection restriction facts, including
native auxiliary inductives with their own projection tables. -/
theorem strongEnvProps_auxDeclRunJ {env env₂ : Env .anon} {d : Declaration .anon}
    (hS : Ix.Kernel.Open.StoreInv env) (h : StrongEnvProps env)
    (haux : ∀ ci ∈ IxVM.Consistency.installs d, ∃ root tag, ci.name = .aux root tag)
    (hrun : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    StrongEnvProps env₂ := by
  cases d with
  | indDecl block nP =>
    cases hpin : Ix.Kernel.basisPinHit block with
    | none =>
      have hblock : ∀ ci ∈ block, ∃ root tag, ci.name = .aux root tag := by
        simpa only [IxVM.Consistency.installs, hpin] using haux
      have hroutes : IndRoutesJ rulesJ env block nP env₂ := by
        simpa only [DeclRunJ, hpin] using hrun
      exact strongEnvProps_auxIndRunJ hS h hblock hpin hroutes
    | some kind =>
      apply strongEnvProps_declRunJ hS h ?_ hrun
      intro block' nP' heq hnone
      cases heq
      rw [hpin] at hnone
      cases hnone
  | defnDecl cv value hint =>
    apply strongEnvProps_declRunJ hS h ?_ hrun
    intro _ _ heq
    cases heq
  | thmDecl cv value =>
    apply strongEnvProps_declRunJ hS h ?_ hrun
    intro _ _ heq
    cases heq
  | opaqueDecl cv value =>
    apply strongEnvProps_declRunJ hS h ?_ hrun
    intro _ _ heq
    cases heq
  | axiomDecl cv =>
    apply strongEnvProps_declRunJ hS h ?_ hrun
    intro _ _ heq
    cases heq
  | basisDecl kind =>
    apply strongEnvProps_declRunJ hS h ?_ hrun
    intro _ _ heq
    cases heq
  | quotDecl kind cv =>
    apply strongEnvProps_declRunJ hS h ?_ hrun
    intro _ _ heq
    cases heq

/-- The store invariant survives an auxiliary model declaration before its owning base
constant has been installed; auxiliary-root synchronization is not needed at this stage. -/
theorem foldStoreInv_step_auxDeclRunJ {env env₂ : Env .anon} {d : Declaration .anon}
    (h : FoldStoreInv env)
    (haux : ∀ ci ∈ IxVM.Consistency.installs d, ∃ root tag, ci.name = .aux root tag)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    FoldStoreInv env₂ := by
  have heta := etaShape_declRunJ h.store h.etaCtorStored h.etaShape hd
  exact
    { store := Ix.Kernel.Model.storeInv_declRunJ
        (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e)
        (fun hI => Ix.Kernel.Model.storeInv_indRoutesJ
          (fun e => Ix.Kernel.Model.judgeFrames_rulesJ e) h.store hI)
        h.store hd
      thmTyped := Ix.Kernel.Model.thmTyped_declRunJ h.thmTyped hd
      recK := Ix.Kernel.Model.recK_declRunJ h.store h.recK hd
      etaTowers := Ix.Kernel.Model.etaTowers_declRunJ h.etaTowers hd
      strongProps := strongEnvProps_auxDeclRunJ h.store h.strongProps haux hd
      recShape := Ix.Kernel.Model.recShape_declRunJ h.store h.recShape hd
      etaCtorStored := heta.1
      etaShape := heta.2 }

/-- Auxiliary model declarations preserve the semantic fold invariant. -/
theorem foldInv_step_auxDeclRunJ {env env₂ : Env .anon} {d : Declaration .anon}
    (haux : ∀ ci ∈ IxVM.Consistency.installs d, ∃ root tag, ci.name = .aux root tag)
    (hd : DeclRunJ rulesJ (IndRoutesJ rulesJ env) env d env₂) :
    ∀ (V : Type u) [SetTheory V], FoldInv V env → FoldInv V env₂ :=
  fun _ _ h => ⟨Ix.Kernel.Model.foldRulesRoutes (.cons hd .nil) h.model,
    foldStoreInv_step_auxDeclRunJ h.store haux hd⟩

/-- A complete auxiliary prefix preserves the fold invariant before the bare declaration. -/
theorem foldInv_auxDeclsRunJ {env env₂ : Env .anon} {ds : List (Declaration .anon)}
    (haux : ∀ d ∈ ds, ∀ ci ∈ IxVM.Consistency.installs d,
      ∃ root tag, ci.name = .aux root tag)
    (run : DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env₂) :
    ∀ (V : Type u) [SetTheory V], FoldInv V env → FoldInv V env₂ := by
  revert haux
  induction run with
  | nil => exact fun _ _ _ h => h
  | cons step _ ih =>
    intro haux V _ h
    apply ih (fun d hd => haux d (List.mem_cons_of_mem _ hd)) V
    exact foldInv_step_auxDeclRunJ (haux _ List.mem_cons_self) step V h

end IxVM.Refinement.Decl
