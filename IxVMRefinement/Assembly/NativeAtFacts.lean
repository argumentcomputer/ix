import IxVMRefinement.Assembly.NativeAliasFormer

/-! # The install of a native block at a given index count, in IxC's terms

`NativeAtFacts env env₂ blk nP nIdx p₀ fam` is `NativeNoRecFacts` (`NativeBlockFacts.lean`) with
the block recognised at the index count `nIdx` (`Ix.Kernel.Model.nativePartsAt?`), which also
reads a former declared at a definition. It is what the native block step concludes about IxC at
an alias former, where the former's stage is `sumIndRunJ_of_alias`'s. From it:

* `NativeAtFacts.runJ`: IxC's record `NativeAtRunJ rulesJ env blk nP env₂`;
* `NativeAtFacts.declRunJ`: the declaration step over the routes `IndRoutesAJ`;
* `NativeAtFacts.register`: the model step with the family registered;
* `NativeAtFacts.envExt`: the environment extends.

The declaration layer's invariants along a step of `IndRoutesAJ` (`FullDeclInv`, `FoldStoreInv`,
`InstallStep`) are not restated here: their IxC store parts are in
`IxC/Kernel/Model/Inductives/NativeAt.lean`; the IxVM parts (`StrongEnvProps`, `EtaShape`,
`AuxRootSynced`, the install's shape) are the next step.
-/

namespace IxVM.Refinement.Typing

open Ix.Kernel (Env ConstantInfo ConstantVal NativeParts InductiveShape IndCaps Level Expr
  RecFieldKind Declaration EnvExt)
open Ix.Kernel.Semantics (SumIndRunJ SumCtorsRunJ FieldSortsJ FormerReadJ NativeFam DeclRunJ)
open Ix.Kernel.Model (nativePartsAt? NativeAtRunJ IndRoutesAJ rulesJ)

universe w

/-- **The install of a native block at a given index count, in IxC's terms** (module
docstring). The former is stored at `cvS` with the capability record `caps`, the telescope
constant the later stages read is `cvTa`, the constructors are stored at `ctorsA`; `fam` is the
family's summary. -/
def NativeAtFacts (env env₂ : Env .anon) (blk : List (ConstantInfo .anon)) (nP nIdx : Nat)
    (p₀ : NativeParts .anon) (fam : NativeFam .anon) : Prop :=
  nativePartsAt? nP nIdx blk = some p₀ ∧ (p₀.ctors.map (·.1.name)).Nodup ∧
  ∃ (isRec : Bool) (cvS cvTa : ConstantVal .anon) (caps : IndCaps .anon)
    (p₁ : InductiveShape .anon) (p : NativeParts .anon) (ctorsA : List (ConstantVal .anon × Nat))
    (sortss : List (List Level)) (kinds : List (List RecFieldKind)) (tfvs : List (Expr .anon))
    (trest : Expr .anon) (isorts : List Level),
    fam = ⟨p, cvS, cvTa, ctorsA⟩ ∧
    SumIndRunJ rulesJ env p₀.toInductiveShape
      (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec) ⟨.indInfo cvS caps :: env.consts⟩ cvTa p₁ ∧
    p = (p₀.complete p₁).withKinds kinds ∧
    SumCtorsRunJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩
      ⟨.indInfo cvS caps :: env.consts⟩ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss ∧
    Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) p.cvT.name p.cvT.levelParams p.nP
      p.nIdx ctorsA = .ok kinds ∧
    Ix.Kernel.nativeCaps p = Ix.Kernel.nativeCapsAt p₁ isRec ∧
    Ix.Kernel.openPisAtFvars (p.nP + p.nIdx) cvTa.type 0 = some (tfvs, trest) ∧
    FieldSortsJ rulesJ ⟨.indInfo cvS caps :: env.consts⟩ true false p.resSort
      p.nP (tfvs.drop p.nP) [] p.nIdx isorts ∧
    Ix.Kernel.nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds = true ∧
    FormerReadJ ⟨.indInfo cvS caps :: env.consts⟩ p cvTa ctorsA ∧
    Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM .anon) p ctorsA sortss
      (Ix.Kernel.consSumCtors p.nP ctorsA ⟨.indInfo cvS caps :: env.consts⟩) = .ok env₂

section

variable {env env₂ : Env .anon} {blk : List (ConstantInfo .anon)} {nP nIdx : Nat}
  {p₀ : NativeParts .anon} {fam : NativeFam .anon}

/-- **IxC's record of the install.** -/
theorem NativeAtFacts.runJ (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    NativeAtRunJ rulesJ env blk nP env₂ := by
  obtain ⟨hdp, hnd, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts, -,
    hInd, hp, hCtors, hK, hcaps, hop, hsorts, hFOk, hFR, hTbl⟩ := h
  exact ⟨nIdx, p₀, hdp, hnd, isRec, _, cvTa, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts,
    hInd, hp, hCtors, hK, hcaps, hop, hsorts, hFOk, hTbl, hFR⟩

/-- **The declaration step of the block, over the routes with the index count given.** -/
theorem NativeAtFacts.declRunJ (hpin : Ix.Kernel.basisPinHit blk = none)
    (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    DeclRunJ rulesJ (IndRoutesAJ rulesJ env) env (.indDecl blk nP) env₂ := by
  simp only [DeclRunJ, hpin]
  exact Or.inr h.runJ

/-- The environment extends. -/
theorem NativeAtFacts.envExt (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam) :
    EnvExt env env₂ :=
  Ix.Kernel.Model.nativeAtRunJ_envExt h.runJ

/-- **The model step with the family registered**, at every registry `R`. -/
theorem NativeAtFacts.register (h : NativeAtFacts env env₂ blk nP nIdx p₀ fam)
    (V : Type w) [Ix.Kernel.SetTheory V] {μ : Ix.Kernel.CheckMode}
    {R : NativeFam .anon → Prop} (hR : Ix.Kernel.Model.EnvModelN V μ env R) :
    Ix.Kernel.Model.EnvModelN V μ env₂ (fun f => R f ∨ f = fam) := by
  obtain ⟨hdp, hnd, isRec, cvS, cvTa, caps, p₁, p, ctorsA, sortss, kinds, tfvs, trest, isorts,
    hfam, hInd, hp, hCtors, hK, hcaps, hop, hsorts, hFOk, hFR, hTbl⟩ := h
  subst hfam
  exact Ix.Kernel.Model.EnvModelN.nativeAt V hR hdp hnd hInd hp hCtors hK hcaps hop hsorts hFOk
    hFR hTbl

end

end IxVM.Refinement.Typing
