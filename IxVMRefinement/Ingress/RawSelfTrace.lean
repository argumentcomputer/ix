import IxVMRefinement.Ingress.RawSelfReads
import IxVMRefinement.Ingress.AnnotationCorrespondence

/-! # Exact annotation traces from reached self reads

The actual reader result is preserved when only its reached recursive-reference callbacks
are replaced by their core keys. Reusing the exact conversion bridge then retains both the
raw and semantic binder traces without requiring names for unused members.
-/

namespace IxVM.Refinement.Ingress

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open Ix.Kernel.Reader

/-- The reached self-read bridge preserves the raw syntax, semantic annotation and both
serialized binder traces of the existing exact conversion theorem. -/
theorem RawConvExpr.toRawTmCExactTrace_of_selfReads {κ : _root_.Address → Core.KKey} [∀ a, Core.Resolved (κ a)]
    {ps : List Ix.Kernel.LevelParam}
    (permutation : ps.Perm (List.range ps.length)) (paramsBound : ps.length < 4294967296)
    {cx : Ctx .anon} {source : Ixon.Constant}
    {self : Nat → Option (ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (keyAt : ∀ address key, cx.keyAt address = .ok key → key = κ address)
    {heap : Heap F} {expression : Ixon.Expr} {pointer : SourceValue F} {readExpr : Core.KExpr}
    (raw : RawConvExpr source.refs.toList recurAddrs source.univs.toList source.sharing.toList blobs
      heap 4294967295 expression pointer)
    (selfReads : ∀ index address computation key,
      RecurUsed source.sharing.toList index expression → recurAddrs[index]? = some address →
      self index = some computation → computation = .ok key → key = κ address)
    (blob : BlobReadAgreement cx.blob blobs)
    (read : (MemberReader.mk' cx source (recParam ps) self).read expression = .ok readExpr)
    (varsBounded : readExpr.looseBVarsBounded 0 = true)
    (levels : readExpr.allLevelParamsDefined ps = true) :
    ∃ rawSyntax annotated : Core.KExpr,
      IxVM.Consistency.Annotates annotated readExpr ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ heap 0 (Core.posOf ps rawSyntax) (Core.posOf ps annotated) pointer) ∧
      (∀ plan, HeapBinderLevels heap pointer plan → ∀ tail,
        applyBinderTrace (fun level => Core.bmeta (invPosLevel ps level))
          readExpr (plan ++ tail) = some (annotated, tail)) ∧
      (∀ plan, HeapBinderLevels heap pointer plan → ∀ tail,
        applyRawBinderTrace (fun level => Core.bmeta (invPosLevel ps level))
          readExpr (plan ++ tail) = some (rawSyntax, tail)) := by
  let canonicalSelf : Nat → Option (ReadM Core.KKey) :=
    fun index => recurAddrs[index]?.map fun address => .ok (κ address)
  have canonicalRead : (MemberReader.mk' cx source (recParam ps) canonicalSelf).read expression = .ok readExpr := by
    apply raw.memberReader_self_mono _ read
    intro index used key succeeded
    obtain ⟨address, found⟩ := raw.recur_used_address used
    have named := selfReads index address (.ok key) key used found succeeded rfl
    simp only [canonicalSelf, found, Option.map_some, named]
  apply raw.toRawTmCExactTrace_of_blobAgreement permutation paramsBound keyAt (self := canonicalSelf) _ blob
    canonicalRead varsBounded levels
  intro index address computation key found selected succeeded
  have same : computation = .ok (κ address) := by
    simpa only [canonicalSelf, found, Option.map_some, Option.some.injEq] using selected.symm
  exact Except.ok.inj (succeeded.symm.trans same)

/-- The semantic annotation trace needs the same reached self reads, with its chosen
annotation kept identical to the raw-trace witness. -/
theorem RawConvExpr.toTmCExactTrace_of_selfReads {κ : _root_.Address → Core.KKey} [∀ a, Core.Resolved (κ a)]
    {ps : List Ix.Kernel.LevelParam}
    (permutation : ps.Perm (List.range ps.length)) (paramsBound : ps.length < 4294967296)
    {cx : Ctx .anon} {source : Ixon.Constant}
    {self : Nat → Option (ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (keyAt : ∀ address key, cx.keyAt address = .ok key → key = κ address)
    {heap : Heap F} {expression : Ixon.Expr} {pointer : SourceValue F} {readExpr : Core.KExpr}
    (raw : RawConvExpr source.refs.toList recurAddrs source.univs.toList source.sharing.toList blobs
      heap 4294967295 expression pointer)
    (selfReads : ∀ index address computation key,
      RecurUsed source.sharing.toList index expression → recurAddrs[index]? = some address →
      self index = some computation → computation = .ok key → key = κ address)
    (blob : BlobReadAgreement cx.blob blobs)
    (read : (MemberReader.mk' cx source (recParam ps) self).read expression = .ok readExpr)
    (varsBounded : readExpr.looseBVarsBounded 0 = true)
    (levels : readExpr.allLevelParamsDefined ps = true) :
    ∃ annotated : Core.KExpr, IxVM.Consistency.Annotates annotated readExpr ∧
      Decl.TmCExact κ heap (Core.posOf ps annotated) pointer ∧
      ∀ plan, HeapBinderLevels heap pointer plan → ∀ tail,
        applyBinderTrace (fun level => Core.bmeta (invPosLevel ps level))
          readExpr (plan ++ tail) = some (annotated, tail) := by
  obtain ⟨_, annotated, annotates, represented, trace, _⟩ :=
    raw.toRawTmCExactTrace_of_selfReads permutation paramsBound keyAt selfReads blob read varsBounded levels
  exact ⟨annotated, annotates, fun d Γ => (represented d Γ).toTmExact, trace⟩

end IxVM.Refinement.Ingress
