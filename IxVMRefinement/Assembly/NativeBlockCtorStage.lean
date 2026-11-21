import IxVMRefinement.Assembly.NativeBlockAssemble
import IxVMRefinement.Assembly.NativeBlockReads

/-! # The no-recursor install of a native block, from the outputs of its walked check

`nativeNoRecFacts_of_outs` reads IxC's no-recursor install of the block (`NativeNoRecFacts`) off
the outputs of the block's two typed stages, as the circuit's check of the block produces them
(the former checked against the prefix as `cvS`, and the constructors' outputs at the
constructor stage of every recursion flag, with the later-use condition of IxC's field check),
through `Decl.nativeNoRecFacts_of_stage`. The remaining inputs of that assembly are read off the
block's readings and keys:

* the constructors' readings have no free variable, their keys are fresh in the prefix, not
  derived, and distinct from the former's (the store holds different records at the member's and
  at a constructor's projection address);
* the projection names of the family are fresh in the prefix, as its key is and as every derived
  key the prefix stores has its root stored (`Decl.AuxRootSynced`).
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

universe u

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **IxC's no-recursor install of the block, from the outputs of its two stages** (module
docstring). -/
theorem nativeNoRecFacts_of_outs {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
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
    ∃ env₂ fam, NativeNoRecFacts env env₂ blk ind.params.toNat p₀ fam := by
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
  exact Decl.nativeNoRecFacts_of_stage hp₀ hnd hinv.store.store hcheckT hstS hnameS
    (by rw [hnameS]; exact hfreshT) hshapeT hlenA hout hfv_ctors hfresh_ctors hshape_ctors
    hT_ctors hfn htbl hunused

end IxVM.Refinement.Typing
