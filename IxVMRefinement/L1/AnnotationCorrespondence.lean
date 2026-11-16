import IxVMRefinement.L1.ConvertExpr

/-! # Agreement of repeated reader annotations

The common annotation is derived from the serialized root plan and actual heap traces.
Reader key, self-reference, blob, and scope correspondences remain explicit.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

/-- The closed reader bridge also retains the exact annotation selected by the heap trace. -/
theorem RawConvExpr.toTmCExactTrace {κ : _root_.Address → Core.KKey}
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {e : Ixon.Expr} {kp : SourceValue F} {E_rd : Core.KExpr}
    (raw : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read e =
      .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined ps = true) :
    ∃ E' : Core.KExpr,
      IxVM.Consistency.Annotates E' E_rd ∧
      Decl.TmCExact κ h (Core.posOf ps E') kp ∧
      (∀ (plan : List Core.KLevel), HeapBinderLevels h kp plan →
        ∀ tail, applyBinderTrace (fun level => Core.bmeta (invPosLevel ps level))
          E_rd (plan ++ tail) = some (E', tail)) := by
  obtain ⟨hecx, htbl⟩ := memberReader_mk'_eq cx src (Ix.Kernel.Reader.recParam ps) self
  unfold Ix.Kernel.Reader.MemberReader.read at hread
  rw [hecx, htbl, ← List.take_length (l := src.sharing.toList)] at hread
  exact raw.toTmExactTrace hperm hps_lt rfl (by simp) hkeyAt hself hblob
    (Nat.le_refl _) (Nat.min_le_right _ _) hread hlbb hdef

/-- Two conversions of one reader root and serialized plan admit one common exact annotation. -/
theorem same_annotation_of_root_plans {κ : _root_.Address → Core.KKey}
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs₁ blobs₂ : List (_root_.Address × ByteArray)}
    (hkeyAt : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (hself : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (hblob₁ : ∀ a bs, (a, bs) ∈ blobs₁ → cx.blob a = some bs)
    (hblob₂ : ∀ a bs, (a, bs) ∈ blobs₂ → cx.blob a = some bs)
    {h₁ h₂ : Heap F} {e : Ixon.Expr} {kp₁ kp₂ : SourceValue F} {E_rd : Core.KExpr}
    (raw₁ : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs₁
      h₁ 4294967295 e kp₁)
    (raw₂ : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs₂
      h₂ 4294967295 e kp₂)
    {tree : BinderTreeData} {root : F} {plan₁ plan₂ : List Core.KLevel}
    (planned₁ : binderRootPlan tree src.sharing.toList root e = some plan₁)
    (planned₂ : binderRootPlan tree src.sharing.toList root e = some plan₂)
    (levels₁ : HeapBinderLevels h₁ kp₁ plan₁) (levels₂ : HeapBinderLevels h₂ kp₂ plan₂)
    (hread : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read e =
      .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined ps = true) :
    ∃ E', IxVM.Consistency.Annotates E' E_rd ∧
      Decl.TmCExact κ h₁ (Core.posOf ps E') kp₁ ∧
      Decl.TmCExact κ h₂ (Core.posOf ps E') kp₂ := by
  have samePlan := Option.some.inj (planned₁.symm.trans planned₂)
  cases samePlan
  obtain ⟨left, annotates, first, firstTrace⟩ :=
    raw₁.toTmCExactTrace hperm hps_lt hkeyAt hself hblob₁ hread hlbb hdef
  obtain ⟨right, _, second, secondTrace⟩ :=
    raw₂.toTmCExactTrace hperm hps_lt hkeyAt hself hblob₂ hread hlbb hdef
  have firstRead := firstTrace plan₁ levels₁ []
  have secondRead := secondTrace plan₁ levels₂ []
  have same := (applyBinderTrace_unique firstRead secondRead).1
  cases same
  exact ⟨left, annotates, first, second⟩

end IxVM.Refinement.L1
