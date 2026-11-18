import IxVMRefinement.Assembly.GuardRawLookup
import IxVMRefinement.L1.RawDataPlan

/-! # Actual physical roots agree with the address-keyed raw dictionary

The data reader is related directly to RawConvExpr and an exact physical raw reading. The
metadata-preserving reader additionally uses the serialized binder plan. Neither bridge asks
for reader closure or declared-universe coverage.
-/

namespace IxVM.Refinement.GuardRaw

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Consistency
open Ix.Kernel (Expr Level)

/-- A successful dictionary reading is exactly the physical root with metadata erased. -/
theorem readRoot_exact {blob : Blobs} {root : Root}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap IxVM.F} {p : SourceValue IxVM.F} {readValue R E : Expr .anon}
    {Γ : Nat → Core.KExpr} {k : Nat}
    (converted : L1.RawConvExpr root.source.refs.toList recurAddrs root.source.univs.toList
      root.source.sharing.toList blobs h 4294967295 root.expression p)
    (selfKeyed : ∀ i a m key, recurAddrs[i]? = some a → root.self i = some m →
      m = .ok key → key = Core.keyOf addressTable a)
    (blobAgreement : ∀ a bytes, (a, bytes) ∈ blobs → blob a = some bytes)
    (physical : Decl.RawTmExact (Core.keyOf addressTable) 0 Γ h k R E p)
    (read : readRoot blob root = some readValue) : readValue = R.eraseMeta := by
  obtain ⟨reader, readerRead, rfl⟩ := Option.map_eq_some_iff.mp read
  have sourceRead := Typing.toOption_eq_some readerRead
  have data := converted.memberReader_rawData (LoadedReads.readCtx_keyAt_inv addressTable_check blob)
    selfKeyed blobAgreement sourceRead
  exact data.det (L1.rawData_of_exact physical)

/-- Exact root identification commutes with the dictionary's literal universe substitution. -/
theorem answer_exact {blob : Blobs} {root : Root} {R : Expr .anon} {ps : List Level}
    (read : readRoot blob root = some R.eraseMeta) (arity : ps.length = root.levels) :
    answer blob (some root) ps =
      some (R.instantiateLevelParams (List.range ps.length) ps).eraseMeta := by
  unfold answer
  change (if ps.length = root.levels then
    (readRoot blob root).map (fun e => e.instantiateLevelParams (List.range root.levels) ps)
    else none) = _
  rw [ite_eq_left arity, read, ← arity]
  simp only [Option.map_some, Ix.Kernel.GuardClassifier.eraseMeta_instantiateLevelParams]

/-- The rich root reader keeps exactly the serialized binder metadata and raw let cells. -/
noncomputable def readCanonicalRoot (blob : Blobs) (root : Root) : Option (Expr .anon) := do
  let reader ← (exprReader addressTable blob root.source id root.self).read root.expression |>.toOption
  L1.canonicalRawAnnotation root.source (List.range root.levels) (root.offset : IxVM.F)
    root.expression reader

/-- Positive literal-store extension preserves the rich canonical raw reading. -/
theorem readCanonicalRoot_mono {blob blob' : Blobs}
    (extension : ∀ a bytes, blob a = some bytes → blob' a = some bytes)
    {root : Root} {R : Expr .anon} (read : readCanonicalRoot blob root = some R) :
    readCanonicalRoot blob' root = some R := by
  obtain ⟨reader, sourceRead, annotated⟩ := Option.bind_eq_some_iff.mp read
  have source := Typing.toOption_eq_some sourceRead
  have source' := ReaderReads.exprReader_mono extension source
  unfold readCanonicalRoot
  rw [source']
  exact annotated

/-- An actual converted root with its serialized binder plan supplies the exact rich dictionary
answer, at arbitrary local variable bounds and arbitrary positional universe counts. -/
theorem readCanonicalRoot_exact {blob : Blobs} {root : Root}
    {recurAddrs : List _root_.Address} {blobs : List (_root_.Address × ByteArray)}
    {h : Heap IxVM.F} {p : SourceValue IxVM.F} {reader R E : Expr .anon}
    {Γ : Nat → Core.KExpr} {k : Nat}
    (converted : L1.RawConvExpr root.source.refs.toList recurAddrs root.source.univs.toList
      root.source.sharing.toList blobs h 4294967295 root.expression p)
    (selfKeyed : ∀ i a m key, recurAddrs[i]? = some a → root.self i = some m →
      m = .ok key → key = Core.keyOf addressTable a)
    (blobAgreement : ∀ a bytes, (a, bytes) ∈ blobs → blob a = some bytes)
    (physical : Decl.RawTmExact (Core.keyOf addressTable) 0 Γ h k R E p)
    {tree : L1.BinderTreeData} {plan : List Core.KLevel}
    (built : L1.BinderTreeBuilt (L1.binderLeavesData root.source.binders.toList) tree)
    (planned : L1.binderRootPlan tree root.source.sharing.toList (root.offset : IxVM.F)
      root.expression = some plan)
    (levels : L1.HeapBinderLevels h p plan)
    (read : (exprReader addressTable blob root.source id root.self).read root.expression = .ok reader) :
    readCanonicalRoot blob root = some R := by
  have canonical := converted.canonical_raw_exact (LoadedReads.readCtx_keyAt_inv addressTable_check blob)
    selfKeyed blobAgreement built planned levels read physical root.levels
  unfold readCanonicalRoot
  rw [read]
  exact canonical.1

end IxVM.Refinement.GuardRaw
