import IxVMRefinement.Decl.DeclSpecs
import IxCK.Kernel.Model.FoldLate

/-! # The no-recursor install of a native block, in IxCK's terms

`NativeNoRecFacts env env₂ blk nP p₀ fam` is what a native block step concludes about IxCK: the
recogniser reads the declared block `blk` as `p₀` (`nativePartsNoRec?`), and the stages of
`DeclNativeNoRecRunJ` hold with the family's summary `fam` named, so that the hypotheses of
`Ix.Kernel.Model.EnvModelN.nativeCore` (no-recursor tail) are available to the caller. From it:

* `NativeNoRecFacts.runJ`: IxCK's record `DeclNativeNoRecRunJ rulesJ env p₀ env₂`;
* `NativeNoRecFacts.declRunJ`: the declaration step `DeclRunJ` of `.indDecl blk nP`;
* `NativeNoRecFacts.register`: the model step with the family registered
  (`EnvModelN.nativeCore`'s conclusion, in IxCK's own terms, at every registry);
* `NativeNoRecFacts.foldInv`, `NativeNoRecFacts.fullDeclInv`, `NativeNoRecFacts.foldStoreInv`:
  the declaration layer's invariants at the new environment;
* `NativeNoRecFacts.installStep`: the install's shape (`InstallStep`).
-/

namespace IxVM.Refinement.Typing

open Ix.Kernel (Env ConstantInfo ConstantVal NativeParts InductiveShape IndCaps Level Expr
  RecFieldKind Declaration)
open Ix.Kernel.Semantics (DeclNativeNoRecRunJ SumIndRunJ SumCtorsRunJ FieldSortsJ FormerReadJ
  NativeFam nativePartsNoRec? DeclRunJ IndRoutesJ)

universe u w

/-- **The no-recursor install of a native block, in IxCK's terms** (module docstring). The former
is stored at `cvS` with the capability record `caps`, the constructors at `ctorsA`; `fam` is the
family's summary. -/
def NativeNoRecFacts (env env₂ : Env .anon) (blk : List (ConstantInfo .anon)) (nP : Nat)
    (p₀ : NativeParts .anon) (fam : NativeFam .anon) : Prop :=
  nativePartsNoRec? nP blk = some p₀ ∧ (p₀.ctors.map (·.1.name)).Nodup ∧
  ∃ (isRec : Bool) (cvS cvTa : ConstantVal .anon) (caps : IndCaps .anon)
    (p₁ : InductiveShape .anon) (p : NativeParts .anon) (ctorsA : List (ConstantVal .anon × Nat))
    (sortss : List (List Level)) (kinds : List (List RecFieldKind)) (tfvs : List (Expr .anon))
    (trest : Expr .anon) (isorts : List Level),
    fam = ⟨p, cvS, cvTa, ctorsA⟩ ∧
    SumIndRunJ Ix.Kernel.Model.rulesJ env p₀.toInductiveShape
      (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec) ⟨.indInfo cvS caps :: env.consts⟩ cvTa p₁ ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    SumCtorsRunJ Ix.Kernel.Model.rulesJ ⟨.indInfo cvS caps :: env.consts⟩
      ⟨.indInfo cvS caps :: env.consts⟩ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss ∧
    Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) p.cvT.name p.cvT.levelParams p.nP
      p.nIdx ctorsA = .ok kinds ∧
    Ix.Kernel.nativeCaps p = Ix.Kernel.nativeCapsAt p₁ isRec ∧
    Ix.Kernel.openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    FieldSortsJ Ix.Kernel.Model.rulesJ ⟨.indInfo cvS caps :: env.consts⟩ true false p.resSort
      p.nP (tfvs.drop p.nP) [] p.nIdx isorts ∧
    Ix.Kernel.nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    FormerReadJ ⟨.indInfo cvS caps :: env.consts⟩ p cvTa ctorsA ∧
    Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss
      (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩) = .ok env₂

section

variable {env env₂ : Env .anon} {blk : List (ConstantInfo .anon)} {nP : Nat}
  {p₀ : NativeParts .anon} {fam : NativeFam .anon}

/-- The recogniser reads the block. -/
theorem NativeNoRecFacts.recognised (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    nativePartsNoRec? nP blk = some p₀ := by
  obtain ⟨hdp, -⟩ := h
  exact hdp

/-- **IxCK's record of the install.** -/
theorem NativeNoRecFacts.runJ (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    DeclNativeNoRecRunJ Ix.Kernel.Model.rulesJ env p₀ env₂ := by
  obtain ⟨-, hnd, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, -,
    hInd, hp, hCtors, hK, hcaps, hop, hsorts, hFOk, hFR, hTbl⟩ := h
  exact ⟨hnd, isRec, _, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, hInd, hp, hCtors,
    hK, hcaps, hop, hsorts, hFOk, hTbl, hFR⟩

/-- **The declaration step of the block.** -/
theorem NativeNoRecFacts.declRunJ (hpin : Ix.Kernel.basisPinHit blk = none)
    (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    DeclRunJ Ix.Kernel.Model.rulesJ (IndRoutesJ Ix.Kernel.Model.rulesJ env) env
      (.indDecl blk nP) env₂ := by
  simp only [DeclRunJ, hpin]
  exact Or.inr (Or.inr (Or.inl ⟨p₀, h.recognised, h.runJ⟩))

/-- **The model step with the family registered**: the conclusion of
`Ix.Kernel.Model.EnvModelN.nativeCore` for this block, at every registry `R`. -/
theorem NativeNoRecFacts.register (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (V : Type w) [Ix.Kernel.SetTheory V] {μ : Ix.Kernel.CheckMode}
    {R : NativeFam .anon → Prop} (hR : Ix.Kernel.Model.EnvModelN V μ env R) :
    Ix.Kernel.Model.EnvModelN V μ env₂ (fun f => R f ∨ f = fam) := by
  obtain ⟨hdp, hnd, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts,
    hfam, hInd, hp, hCtors, hK, hcaps, hop, hsorts, hFOk, hFR, hTbl⟩ := h
  subst hfam
  obtain ⟨blk', hdp'⟩ : ∃ blk', Ix.Kernel.nativeParts? nP blk' = some p₀ := by
    unfold nativePartsNoRec? at hdp
    split at hdp
    · split at hdp
      · exact ⟨_, hdp⟩
      · exact nomatch hdp
    · exact nomatch hdp
  exact Ix.Kernel.Model.EnvModelN.nativeCore V hR hdp' hnd hInd hp hCtors hK hcaps hop hsorts
    hFOk hFR (Or.inr hTbl)

/-- **The declaration layer's fold invariant at the new environment.** -/
theorem NativeNoRecFacts.foldInv (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FoldInv V env → Decl.FoldInv V env₂ :=
  Decl.foldInv_step_indNativeNoRec hpin hna h.recognised h.runJ

/-- **The full declaration invariant at the new environment**, where the declared constants'
keys and the keys their types name are not derived and the declared names are distinct. -/
theorem NativeNoRecFacts.fullDeclInv (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : Decl.DeclNonAux (.indDecl blk nP)) (h : NativeNoRecFacts env env₂ blk nP p₀ fam) :
    ∀ (V : Type u) [Ix.Kernel.SetTheory V], Decl.FullDeclInv V env → Decl.FullDeclInv V env₂ :=
  Decl.fullDeclInv_step_declRunJ hna (h.declRunJ hpin)

/-- **The store part of the invariant at the new environment.** -/
theorem NativeNoRecFacts.foldStoreInv (hpin : Ix.Kernel.basisPinHit blk = none)
    (hna : ∀ ci ∈ blk, Decl.NonAuxKey ci.name) (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hS : Decl.FoldStoreInv env) : Decl.FoldStoreInv env₂ :=
  Decl.foldStoreInv_step_declRunJ hS
    (fun blk' _ heq _ => by injection heq with hblk _; subst hblk; exact hna) (h.declRunJ hpin)

/-- **The install's shape**, where every declared constant is stored as declared. -/
theorem NativeNoRecFacts.installStep (hpin : Ix.Kernel.basisPinHit blk = none)
    (h : NativeNoRecFacts env env₂ blk nP p₀ fam)
    (hstored : ∀ ci₀ ∈ blk,
      ∃ ci, env₂.find? ci₀.name = some ci ∧ IxVM.Consistency.StoredAs ci ci₀) :
    IxVM.Consistency.InstallStep env (.indDecl blk nP) env₂ :=
  Decl.installStep_glue_indNativeNoRec hpin h.recognised h.runJ hstored

end

end IxVM.Refinement.Typing
