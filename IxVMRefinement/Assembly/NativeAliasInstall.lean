import IxVMRefinement.Assembly.NativeAliasAssemble
import IxVMRefinement.Assembly.NativeAliasCtorOuts
import IxVMRefinement.Assembly.NativeAliasKeys

/-! # Actual alias installation at a typing prefix

The actual member check produces both typed stages and the constructor zero-ness alternative.
The full table and prefix freshness supply the remaining literal-key separation. No complete
registry update or unchecked conversion event is an input.
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

/-- Assemble the native alias install from its observed stage outputs and typing-prefix facts. -/
theorem nativeAtFacts_of_alias_outs {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E R : Ixon.Env} {envT : Ix.Kernel.Env .anon} {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    {n : Nat} (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀)
    (hst : StepStore calls t E₀ E) (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp₀ : Ix.Kernel.Model.nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀)
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    (hindexed : p₀.nIdx ≠ 0)
    (shape : TableShape.{u} t (fun _ => True) R envT)
    {env : Ix.Kernel.Env .anon}
    (prefixExtension : ∀ ci ∈ envT.consts, ci ∈ env.consts)
    (distinct : (env.consts.map (·.name)).Nodup) (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (haux : Decl.AuxRootSynced env)
    {cvS cvTa : ConstantVal .anon} {s : Ix.Kernel.Level}
    {ctorsA : List (ConstantVal .anon × Nat)} {rawTypes : List (Ix.Kernel.Expr .anon)}
    (hcheckT : Ix.Kernel.Semantics.ConstantValCheckJ Ix.Kernel.Model.rulesJ env p₀.cvT cvS)
    (htele : AliasTele env p₀.cvT cvS cvTa (p₀.nP + p₀.nIdx) s)
    (hparam : p₀.ctors ≠ [] → ∀ tfvs residual,
      Ix.Kernel.openPisAtFvars p₀.nP cvS.type 0 = some (tfvs, residual) →
      ∃ residual', Ix.Kernel.openPisAtFvars p₀.nP cvTa.type 0 = some (tfvs, residual'))
    (hformerRead : cvTa = cvS ∨ ∀ ctor ∈ ctorsA,
      Ix.Kernel.Semantics.ctorZeroOk p₀.cvT.name s.zeronessOf ctor.1.type = true)
    (hnameS : cvS.name = p₀.cvT.name) (hlenA : ctorsA.length = p₀.ctors.length)
    (hout : ∀ isRec : Bool, ∃ sortss : List (List Ix.Kernel.Level),
      sortss.length = p₀.ctors.length ∧
      ∀ j < p₀.ctors.length, ∃ c cA sorts, p₀.ctors[j]? = some c ∧ ctorsA[j]? = some cA ∧
        sortss[j]? = some sorts ∧
        Decl.NativeCtorOut ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt
            (p₀.toInductiveShape.withSort s) isRec) :: env.consts⟩
          p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx s cvS.type
          (rawTypes.getD j default) c cA sorts)
    (hunused : ∀ cA ∈ ctorsA, ∀ cbs body,
      cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2,
        (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
        Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false) :
    ∃ env₂ p, NativeAtFacts env env₂ blk ind.params.toNat ind.indices.toNat p₀
      ⟨p, cvS, cvTa, ctorsA⟩ := by
  have hbound : Bounded calls := (hst.good env none).2
  have htwf : t.wf = true := hinv.tableWf
  obtain ⟨ty₀, caps, cs, rfl, hty, hlen, hcs⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  obtain ⟨caps₀, hshape, -, -, -, -, -⟩ := nativePartsAt?_inv hp₀
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
  have hliterals := alias_literal_keys_distinct htwf shape prefixExtension distinct
    (by rw [← hTname]; exact hfreshT)
  rw [← hTname, ← hnameS] at hliterals
  exact Decl.nativeAtFacts_of_alias_stage hp₀ hnd hinv.store.store hcheckT htele hindexed
    hparam hliterals hnameS (by rw [hnameS]; exact hfreshT) hshapeT hlenA hformerRead hout
    hfv_ctors hfresh_ctors hshape_ctors hT_ctors hfn htbl hunused

/-- The actual alias member check constructs its native install and named family. -/
theorem nativeAtFacts_of_alias_member {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {E₀ E R : Ixon.Env} {envT : Ix.Kernel.Env .anon}
    {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}
    {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B) (hblk : BlockReadings t E₀ B ind blk)
    (halias : FormerAtAlias t E₀ B cb ind)
    (shape : TableShape.{u} t (fun _ => True) R envT)
    (prefixExtension : ∀ ci ∈ envT.consts, ci ∈ env.consts)
    (distinct : (env.consts.map (·.name)).Nodup)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hP : HashedBlockProjectionsHeld E) (hkeys : HashKeyed t env)
    (hfresh : ∀ x, ConstAddrOf B cb x → env.find? (keyOf t x) = none)
    (hfree : ∀ x, ConstAddrOf B cb x → Decl.KeyFree (keyOf t x))
    (hcov : L1.CanonicalHashCoverage E calls) (haux : Decl.AuxRootSynced env) :
    ∃ p₀ env₂ fam, NativeAtFacts env env₂ blk ind.params.toNat ind.indices.toNat p₀ fam := by
  obtain ⟨p₀, recognised, constructorNames, indices⟩ :=
    nativePartsAt_of_member ht (hst.good env none).2 hS hrec hchk halias hblk hfree
  obtain ⟨cvS, cvTa, s, ctorsA, rawTypes, checked, tele, named, _, _, count,
    parameters, outputs, _, zero, indexed, unused⟩ := aliasOuts_of_member_checked ht hS hst hrec hchk
      hnat hblk recognised indices (.inr halias) hinv hstored hP hkeys hfresh hfree hcov haux
  obtain ⟨env₂, parts, installed⟩ := nativeAtFacts_of_alias_outs ht hS hst hrec hchk hblk
    recognised constructorNames (by rw [indices]; exact indexed) shape prefixExtension distinct hinv hfresh haux
    checked tele parameters zero named count outputs unused
  exact ⟨p₀, env₂, ⟨parts, cvS, cvTa, ctorsA⟩, installed⟩


end IxVM.Refinement.Typing
