import IxVMRefinement.Ingress.AnnotationCorrespondence
import IxVMRefinement.Ingress.RawAnnotationErasure

/-! # Canonical raw annotation from a serialized binder plan

This low-level function depends only on the serialized record, root, and reader expression.
An actual built tree and converted root produce its answer, with retained lets and exact binder
metadata. Reader closure and universe coverage remain explicit in the representation bridge.
-/

namespace IxVM.Refinement.Ingress

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)

open Classical in
/-- The unique tree built from a serialized binder-block list, or the empty tree if no build
exists. Actual successful table construction supplies the former case. -/
noncomputable def canonicalRawTree (blocks : List Ixon.BinderBlock) : BinderTreeData :=
  if existsTree : ∃ tree, BinderTreeBuilt (binderLeavesData blocks) tree then
    Classical.choose existsTree
  else .empty

theorem canonicalRawTree_of_built {blocks : List Ixon.BinderBlock} {tree : BinderTreeData}
    (built : BinderTreeBuilt (binderLeavesData blocks) tree) : canonicalRawTree blocks = tree := by
  have existsTree : ∃ tree, BinderTreeBuilt (binderLeavesData blocks) tree := ⟨tree, built⟩
  unfold canonicalRawTree
  rw [dite_eq_left existsTree]
  exact (Classical.choose_spec existsTree).unique built

/-- A deterministic raw annotation of the reader expression at one serialized root. -/
noncomputable def canonicalRawAnnotation (source : Ixon.Constant)
    (parameters : List Ix.Kernel.LevelParam) (root : F) (expression : Ixon.Expr)
    (reader : Core.KExpr) : Option Core.KExpr := do
  let plan ← binderRootPlan (canonicalRawTree source.binders.toList) source.sharing.toList root expression
  let (raw, _) ← applyRawBinderTrace (fun level => Core.bmeta (invPosLevel parameters level)) reader plan
  pure raw

/-- A canonical raw annotation preserves the complete metadata-erased reader expression. -/
theorem canonicalRawAnnotation_erased {source : Ixon.Constant}
    {parameters : List Ix.Kernel.LevelParam} {root : F} {expression : Ixon.Expr}
    {reader raw : Core.KExpr}
    (annotated : canonicalRawAnnotation source parameters root expression reader = some raw) :
    raw.eraseMeta = reader.eraseMeta := by
  obtain ⟨plan, _, later⟩ := Option.bind_eq_some_iff.mp annotated
  obtain ⟨⟨value, rest⟩, read, result⟩ := Option.bind_eq_some_iff.mp later
  have equal := Option.some.inj result
  cases equal
  exact applyRawBinderTrace_eraseMeta reader read

/-- The actual raw conversion and its serialized binder plan produce the canonical raw answer.
The keying and self-reference correspondence are independent of a validation limit. -/
theorem RawConvExpr.canonical_raw {κ : _root_.Address → Core.KKey} [∀ a, Core.Resolved (κ a)]
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobAgreement : ∀ a bs, (a, bs) ∈ blobs → cx.blob a = some bs)
    {h : Heap F} {e : Ixon.Expr} {kp : SourceValue F} {reader : Core.KExpr}
    (converted : RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    {tree : BinderTreeData} {root : F} {plan : List Core.KLevel}
    (built : BinderTreeBuilt (binderLeavesData src.binders.toList) tree)
    (planned : binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : HeapBinderLevels h kp plan)
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read e =
      .ok reader)
    (varsBounded : reader.looseBVarsBounded 0 = true)
    (levelsDefined : reader.allLevelParamsDefined ps = true) :
    ∃ raw semantic, canonicalRawAnnotation src ps root e reader = some raw ∧
      IxVM.Consistency.Annotates semantic reader ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h 0 (Core.posOf ps raw) (Core.posOf ps semantic) kp) ∧
      raw.eraseMeta = reader.eraseMeta := by
  obtain ⟨raw, semantic, annotates, represented, _, rawTrace⟩ :=
    converted.toRawTmCExactTrace hperm hps_lt keyed selfKeyed blobAgreement read varsBounded levelsDefined
  have traced := rawTrace plan levels []
  rw [List.append_nil] at traced
  have canonical : canonicalRawAnnotation src ps root e reader = some raw := by
    unfold canonicalRawAnnotation
    rw [canonicalRawTree_of_built built, planned]
    change (applyRawBinderTrace (fun level => Core.bmeta (invPosLevel ps level)) reader plan).bind
      (fun result => some result.1) = some raw
    rw [traced]
    rfl
  exact ⟨raw, semantic, canonical, annotates, represented, applyRawBinderTrace_eraseMeta reader traced⟩

end IxVM.Refinement.Ingress
