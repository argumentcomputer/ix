import IxVMRefinement.Decl.NativeRecRules

/-! # Native positional steps preserve the declaration invariant -/

universe u

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Semantics Ix.Kernel.Model
open Core (KConstantInfo)

/-- Native storage companions depend on the checked stages and annotation frames, so they
also hold for the positional judgement package. -/
theorem DeclStoreInv.step_nativeJ {J : Judgements .anon}
    (frames : ∀ env : Env .anon, JudgeFrames J env)
    {env after : Env .anon} {block : List (ConstantInfo .anon)} {nP : Nat}
    {parts : NativeParts .anon} (hparts : nativeParts? nP block = some parts)
    (h : DeclStoreInv env) (run : DeclNativeRunJ J env parts after) : DeclStoreInv after := by
  have hext := declNativeRunJ_envExt run
  have recog := nativeRecog_of hparts
  refine
    { store := storeInv_declNativeRunJ frames recog h.store run
      thmTyped := thmTyped_step_noThm hext h.thmTyped
        (native_newSat (fun _ _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ _ heq => nomatch heq)
          (fun _ _ _ heq => nomatch heq) run)
      recK := recK_step h.store h.recK hext.find ?_
      etaTowers := etaTowers_step hext h.etaTowers ?_
      tableBodies := tableBodies_step hext.find h.tableBodies ?_
      recShape := recShape_step h.store h.recShape hext.find
        (native_recShape_new frames recog h.store run) }
  · intro n cv mI rP rules hf hn
    obtain ⟨h1, h2⟩ := native_recK_new frames recog h.store run n cv mI rP rules hf hn
    exact ⟨h1, fun _ => h2⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hInd, hp,
      hCtors, _, _, _, _, _, _, _, hTbl, _⟩ := run
    exact nativeFormer_towers hInd hp hCtors
      ((consSumCtors_newSat (fun _ _ _ _ _ heq => nomatch heq)).trans
        (NewSat.cons (c := .recInfo _ _ _ _) (fun _ _ heq => nomatch heq))) hTbl
  · obtain ⟨hnd, _, env₁, _, _, p, ctorsA, _, _, cvRa, rhss, _, _, _, hInd,
      hp, hCtors, _, _, _, _, _, _, hRec, hTbl, _⟩ := run
    have front := nativeFront frames h.store recog hnd hInd hp hCtors
    obtain ⟨hnR, _, hfR, _⟩ := hRec.recursor
    have hfreshR : (consSumCtors p.nP ctorsA env₁).find? cvRa.name = none := by
      rw [hnR]; exact hfR
    obtain ⟨_, _, _, _, _, _, ⟨_, henv₁, _⟩, _, _⟩ := hInd.shape
    have noTables : NewSat env ⟨.recInfo cvRa p.majorIdx p.rulePrefix
        (sumRules (consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP
          p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
        :: (consSumCtors p.nP ctorsA env₁).consts⟩ NotProj := by
      subst henv₁
      exact (NewSat.cons (fun _ heq => nomatch heq)).trans
        ((consSumCtors_newSat (fun _ _ _ _ heq => nomatch heq)).trans
          (NewSat.cons (fun _ heq => nomatch heq)))
    exact nativeTable_bodies hCtors
      (fun j cA hj => Env.find?_cons_of_fresh hfreshR (front.ctor j cA hj).1) noTables hTbl

/-- A positional native run preserves both the model and the concrete store companions. -/
theorem DeclInv.step_nativePos {V : Type u} [SetTheory V]
    {env after : Env .anon} {block : List (ConstantInfo .anon)} {nP : Nat}
    {parts : NativeParts .anon} (hparts : nativeParts? nP block = some parts)
    (run : DeclNativeRunJ nativePosRulesJ env parts after)
    (h : DeclInv V env) : DeclInv V after :=
  ⟨envModelT_step_nativePos hparts run h.model,
    h.store.step_nativeJ judgeFrames_nativePosRulesJ hparts run⟩

/-- The actual native observations yield an invariant-preserving install without an extra
universe-renaming premise. Raw load and constructor-use evidence remains in `NativeWithRecData`. -/
theorem nativeWithRec_declInv_step_pos
    (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {env : Env .anon}
    {block : List KConstantInfo} {nP : Nat} {parts : NativeParts .anon}
    (hpin : basisPinHit block = none) (hparts : nativeParts? nP block = some parts)
    (store : DeclStoreInv env) (data : NativeWithRecData calls env block parts) :
    ∃ after, IxVM.Consistency.InstallStep env (.indDecl block nP) after ∧
      ∀ (V : Type u) [SetTheory V], DeclInv V env → DeclInv V after := by
  obtain ⟨after, installed, run⟩ := nativeWithRec_step_pos hLevels hCore hpin hparts store data
  exact ⟨after, installed, fun _ _ h => h.step_nativePos hparts run⟩

end IxVM.Refinement.Decl
