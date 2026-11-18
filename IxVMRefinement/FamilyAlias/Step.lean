import IxVMRefinement.Decl.FamilyDeclInv
import IxC.Kernel.Model.NoRecBlock

/-! # The fold invariant across a family on the renamed route, at any sound package

`IxVMRefinement/Decl/FamilyDeclInv.lean` steps the declaration layer's invariant across
`DeclIndRenRunJ rulesJ`. This file restates its store and model steps for an arbitrary judgement
package with scoping annotations (`JudgeFrames`) that is sound at every model (`JudgeSound`), the
hypotheses of `Ix.Kernel.Model.declIndRenJ`. The step is at `FoldInv`, not `FullDeclInv`: the
environment the block is installed in may store model aliases at derived keys whose roots (the
block's members) are stored only by the step itself. -/

universe u

namespace IxVM.Refinement.Decl.FamilyAlias

open Ix.Kernel (ConstantInfo Declaration EnvExt)
open Ix.Kernel.Semantics (Judgements DeclRunJ DeclsRunJ IndRoutesJ DeclIndRunJ DeclIndRenRunJ
  shapeJ)
open Ix.Kernel.Model (rulesJ EnvModelM EnvModelT JudgeFrames JudgeSound NewSat)

set_option linter.unusedVariables false

/-- The shape package of a block's renamed record over a package `J`. -/
abbrev shapeOf (J : Judgements .anon) (block : List (ConstantInfo .anon)) : Judgements .anon :=
  shapeJ (fun n => if (block.map (·.name)).contains n then Ix.Kernel.auxKey n .model else n) J

/-- **The store invariant across a family installed on the renamed route, at any package with
scoping annotations.** -/
theorem foldStoreInv_step_declIndRenJ {J : Judgements .anon}
    (hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames J e)
    {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} (h : FoldStoreInv env)
    (hpin : Ix.Kernel.basisPinHit block = none) (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclIndRenRunJ J env block env₂) :
    FoldStoreInv env₂ := by
  have hfrS : ∀ e : Ix.Kernel.Env .anon, JudgeFrames (shapeOf J block) e :=
    fun e => Ix.Kernel.Model.judgeFrames_shapeJ (hfr e)
  have hM : DeclIndRunJ (shapeOf J block) env block env₂ := hd.shape
  have hext : EnvExt env env₂ := Ix.Kernel.Semantics.declIndRenRunJ_envExt hd
  have hrunS : DeclRunJ (shapeOf J block) (IndRoutesJ (shapeOf J block) env) env
      (.indDecl block nP) env₂ := by
    simp only [DeclRunJ, hpin]
    exact Or.inr (Or.inl hd.shape)
  have hna' : ∀ block' nP', (Declaration.indDecl block nP : Declaration .anon) =
      .indDecl block' nP' → Ix.Kernel.basisPinHit block' = none →
      ∀ ci ∈ block', NonAuxKey ci.name := by
    intro block' nP' heq _
    injection heq with hb _
    subst hb
    exact hna
  have htb : Ix.Kernel.Model.TableBodies env₂ :=
    Ix.Kernel.Model.tableBodies_step_noProj hext.find h.strongProps.1
      (Ix.Kernel.Model.modeled_newSat (fun _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ heq => nomatch heq) hM)
  have heta := etaShape_declRunJ_generic hfrS h.store
    h.etaCtorStored h.etaShape hrunS
  exact
    { store := Ix.Kernel.Model.storeInv_declIndRunJ hfrS h.store hM
      thmTyped := Ix.Kernel.Model.thmTyped_step_noThm hext h.thmTyped
        (Ix.Kernel.Model.modeled_newSat (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) hM)
      recK := Ix.Kernel.Model.recK_step h.store h.recK hext.find
        (Ix.Kernel.Model.modeled_recK_new hM)
      etaTowers := Ix.Kernel.Model.etaTowers_step_noEta hext h.etaTowers
        (Ix.Kernel.Model.modeled_newSat (fun _ _ _ heq he => by
            obtain ⟨-, rfl⟩ := ConstantInfo.indInfo.inj heq
            simp at he)
          (fun _ _ _ _ _ heq => nomatch heq) (fun _ _ _ _ _ _ heq => nomatch heq) hM)
      strongProps := strongEnvProps_declRunJ_generic h.strongProps htb hna' hrunS
      recShape := Ix.Kernel.Model.recShape_step h.store h.recShape hext.find
        (Ix.Kernel.Model.modeled_recShape_new hM)
      etaCtorStored := heta.1
      etaShape := heta.2 }

/-- **The set-theoretic fold invariant across a family installed on the renamed route, at any
package that is sound at every model**: the model by `Ix.Kernel.Model.declIndStepRenJ`, the store
by `foldStoreInv_step_declIndRenJ`. -/
theorem foldInv_step_declIndRenJ {J : Judgements .anon}
    (hfr : ∀ e : Ix.Kernel.Env .anon, JudgeFrames J e)
    (hJ : ∀ (V : Type u) [Ix.Kernel.SetTheory V] {e : Ix.Kernel.Env .anon}
      (m : EnvModelM V .verified e), JudgeSound J m.base2)
    {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none) (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclIndRenRunJ J env block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ := by
  intro V _ h
  obtain ⟨⟨mp, hT⟩, hE⟩ := h.model
  obtain ⟨hE₂, mp₂, hext⟩ :=
    Ix.Kernel.Model.declIndStepRenJ hfr (fun m => hJ V m) mp hE hd
  exact ⟨⟨⟨mp₂, hT.of_ext hext⟩, hE₂⟩,
    foldStoreInv_step_declIndRenJ (nP := nP) hfr h.store hpin hna hd⟩

/-- **Every recursor the renamed record stores carries a model companion**, at any package. -/
theorem hasModel_declIndRenJ {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} (hd : DeclIndRenRunJ J env block env₂)
    {n : Ix.Kernel.Key .anon} {cv : Ix.Kernel.ConstantVal .anon} {mI rP : Nat}
    {rules : List (Ix.Kernel.RecRule .anon)}
    (hf : env₂.find? n = some (.recInfo cv mI rP rules)) (hn : env.find? n = none) :
    Ix.Kernel.Model.HasModel env₂ n :=
  Ix.Kernel.Model.declIndRunJ_hasModel hd.shape hf hn

end IxVM.Refinement.Decl.FamilyAlias
