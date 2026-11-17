import IxVMRefinement.Decl.DeclSpecs
import IxC.Kernel.Model.DeclIndRen
import IxC.Kernel.Model.IndRenJudge

/-! # The declaration layer's invariants across a family installed on the renamed route

A mutual or nested block is installed in full (its types, its constructors and the recursors of
its family record) by IxC's renamed record `DeclIndRenRunJ` (`IxC/Kernel/Model/IndRenRecord.lean`):
the block's rules and front doors may be typed on the terms renamed to the block's model. This
module carries the declaration layer's invariant `FullDeclInv` across such a step, at the
derivation package `rulesJ`, the package every refinement of the circuit's judgements targets.

* The model: `Ix.Kernel.Model.foldRulesRen`, the fold at `rulesJ` with every inductive block on
  the renamed route, at a one-declaration stream (`foldInv_step_declIndRen`).
* The store: `DeclIndRenRunJ.shape` reads the step as `DeclIndRunJ` at the shape package
  (`famShapeJ`), whose judgements are those of `rulesJ` or of the renaming, every conversion
  holding. Every store lemma of the modeled route is generic in its package, so each store field
  is stepped by the modeled route's own lemma at `famShapeJ` (`foldStoreInv_step_declIndRen`).
  Where the existing lemma is stated over `DeclRunJ J (IndRoutesJ J env)` for a generic `J`
  (`strongEnvProps_declRunJ_generic`, `etaShape_declRunJ_generic`,
  `auxRootSynced_step_declRunJ_generic`), the step is presented as the unpinned inductive kind
  of `DeclRunJ` at `famShapeJ` (`declRunJ_shape_of_ren`).

Nothing here reads the circuit. The hypotheses are the step itself, that its block hits no basis
pin, and that its names are not derived keys (`DeclNonAux`), as for
`fullDeclInv_step_declRunJ`. -/

universe u

namespace IxVM.Refinement.Decl

open Ix.Kernel (ConstantInfo Declaration EnvExt)
open Ix.Kernel.Semantics (Judgements DeclRunJ DeclsRunJ IndRoutesJ DeclIndRunJ DeclIndRenRunJ
  shapeJ)
open Ix.Kernel.Model (rulesJ EnvModelT JudgeFrames NewSat)

/-- **The shape package of a block's renamed record**: `rulesJ`'s judgement of a subject or of
its renaming to the block's model, every conversion holding (`shapeJ` at the block renaming). -/
abbrev famShapeJ (block : List (ConstantInfo .anon)) : Judgements .anon :=
  shapeJ (fun n => if (block.map (·.name)).contains n then Ix.Kernel.auxKey n .model else n)
    rulesJ

/-- The shape package keeps the derivation package's annotations, so their scoping. -/
theorem judgeFrames_famShapeJ (block : List (ConstantInfo .anon))
    (e : Ix.Kernel.Env .anon) : JudgeFrames (famShapeJ block) e :=
  Ix.Kernel.Model.judgeFrames_shapeJ (Ix.Kernel.Model.judgeFrames_rulesJ e)

/-- **The renamed step, at the shape package, as the unpinned inductive kind of `DeclRunJ`.** -/
theorem declRunJ_shape_of_ren {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none) (h : DeclIndRenRunJ rulesJ env block env₂) :
    DeclRunJ (famShapeJ block) (IndRoutesJ (famShapeJ block) env) env (.indDecl block nP)
      env₂ := by
  simp only [DeclRunJ, hpin]
  exact Or.inr (Or.inl h.shape)

/-- **The renamed step as the inductive kind of a declaration stream on the renamed route**
(the form `Ix.Kernel.Model.foldRulesRen` reads). -/
theorem declRunJ_ren {env env₂ : Ix.Kernel.Env .anon} {block : List (ConstantInfo .anon)}
    {nP : Nat} (hpin : Ix.Kernel.basisPinHit block = none)
    (h : DeclIndRenRunJ rulesJ env block env₂) :
    DeclRunJ rulesJ (fun b _ e₂ => DeclIndRenRunJ rulesJ env b e₂) env (.indDecl block nP)
      env₂ := by
  simp only [DeclRunJ, hpin]
  exact h

/-- The names of an unpinned block whose declaration is `DeclNonAux` are not derived keys. -/
theorem nonAux_of_declNonAux {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none) (hna : DeclNonAux (.indDecl block nP)) :
    ∀ ci ∈ block, NonAuxKey ci.name := by
  intro ci hci
  have hm : ci ∈ IxVM.Consistency.installs (.indDecl block nP) := by
    simpa [IxVM.Consistency.installs, hpin] using hci
  exact (hna.1 ci hm).1

/-- **The store invariant across a family installed on the renamed route.** Each field is
stepped by the modeled route's own lemma at the shape package. -/
theorem foldStoreInv_step_declIndRen {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} (h : FoldStoreInv env)
    (hpin : Ix.Kernel.basisPinHit block = none) (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclIndRenRunJ rulesJ env block env₂) :
    FoldStoreInv env₂ := by
  have hM : DeclIndRunJ (famShapeJ block) env block env₂ := hd.shape
  have hext : EnvExt env env₂ := Ix.Kernel.Semantics.declIndRenRunJ_envExt hd
  have hrunS := declRunJ_shape_of_ren (nP := nP) hpin hd
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
  have heta := etaShape_declRunJ_generic (judgeFrames_famShapeJ block) h.store
    h.etaCtorStored h.etaShape hrunS
  exact
    { store := Ix.Kernel.Model.storeInv_declIndRunJ (judgeFrames_famShapeJ block) h.store hM
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

/-- **The set-theoretic fold invariant across a family installed on the renamed route**: the
model by `foldRulesRen` at a one-declaration stream, the store by
`foldStoreInv_step_declIndRen`. -/
theorem foldInv_step_declIndRen {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none) (hna : ∀ ci ∈ block, NonAuxKey ci.name)
    (hd : DeclIndRenRunJ rulesJ env block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FoldInv V env → FoldInv V env₂ :=
  fun _ _ h =>
    ⟨Ix.Kernel.Model.foldRulesRen
        (DeclsRunJ.cons (d := .indDecl block nP) (declRunJ_ren hpin hd) .nil) h.model,
      foldStoreInv_step_declIndRen (nP := nP) h.store hpin hna hd⟩

/-- **Auxiliary roots stay stored across a family installed on the renamed route.** -/
theorem auxRootSynced_step_declIndRen {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat} (haux : AuxRootSynced env)
    (hpin : Ix.Kernel.basisPinHit block = none) (hna : DeclNonAux (.indDecl block nP))
    (hd : DeclIndRenRunJ rulesJ env block env₂) :
    AuxRootSynced env₂ :=
  auxRootSynced_step_declRunJ_generic haux hna (declRunJ_shape_of_ren hpin hd)

/-- **The declaration layer's invariant across a family installed on the renamed route**
(`fullDeclInv_step_declRunJ` for `DeclIndRenRunJ`). -/
theorem fullDeclInv_step_declIndRen {env env₂ : Ix.Kernel.Env .anon}
    {block : List (ConstantInfo .anon)} {nP : Nat}
    (hpin : Ix.Kernel.basisPinHit block = none) (hna : DeclNonAux (.indDecl block nP))
    (hd : DeclIndRenRunJ rulesJ env block env₂) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], FullDeclInv V env → FullDeclInv V env₂ :=
  FullDeclInv.step_of_foldInv_aux
    (foldInv_step_declIndRen (nP := nP) hpin (nonAux_of_declNonAux hpin hna) hd)
    (fun haux => auxRootSynced_step_declIndRen haux hpin hna hd)

end IxVM.Refinement.Decl
