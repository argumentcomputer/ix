import IxVMRefinement.L1.RawRootAgreement
import IxVMRefinement.L1.Records
import IxVMRefinement.StatementRel.LoadedReadsTrace

/-! # Actual definition loads retain serialized value-root plans

The origin exposes the standalone source or definition-block owner, physical value pointer,
serialized root offset, actual conversion and binder plan, and hashed memberships. Its payload
is reusable for store-based comparison; only extraction's byte identification uses the supplied
collision escape and containing trace.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core

private theorem defn_kind {d : Ixon.Definition} {tp vp hint nl ty value flag hintPtr : SourceValue F}
    (shape : defnValShape d tp vp hint = .construct kciEnum "Defn" [nl, ty, value, flag, hintPtr]) :
    d.kind = .defn := by
  cases kind : d.kind with
  | defn => rfl
  | thm => simp [defnValShape, kind] at shape
  | opaq => simp [defnValShape, kind] at shape

/-- The selected value root, with its actual binder plan and physical payload pointer. -/
def DefinitionValueTrace (calls : List (Call F)) (h : Heap F) (address : _root_.Address)
    (record : Ixon.Constant) (nl value : SourceValue F) : Prop :=
  match record.info with
  | .defn definition =>
    ∃ (blobs : List (_root_.Address × ByteArray)) (tree : BinderTreeData) (plan : List KLevel),
      definition.kind = .defn ∧ definition.lvls.toNat < 4294967296 ∧
      nl = .field (definition.lvls.toNat : F) ∧
      HashedPairs calls blobs ∧ BinderTreeBuilt (binderLeavesData record.binders.toList) tree ∧
      RawConvExpr record.refs.toList (defnRecurAddrs definition address) record.univs.toList
        record.sharing.toList blobs h 4294967295 definition.value value ∧
      binderRootPlan tree record.sharing.toList (0 + 1) definition.value = some plan ∧
      HeapBinderLevels h value plan
  | .dPrj projection =>
    projection.idx.toNat < 72057594037927936 ∧
    ∃ (ownerBytes : ByteArray) (owner : Ixon.Constant) (members : Array Ixon.MutConst)
      (definition : Ixon.Definition) (blobs : List (_root_.Address × ByteArray))
      (tree : BinderTreeData) (plan : List KLevel),
      Hashed calls ownerBytes ∧ Address.blake3Pure ownerBytes = projection.block ∧
      Ixon.deConstantExact ownerBytes = .ok owner ∧ owner.info = .muts members ∧
      members.toList[projection.idx.toNat]? = some (.defn definition) ∧
      definition.kind = .defn ∧ definition.lvls.toNat < 4294967296 ∧
      nl = .field (definition.lvls.toNat : F) ∧
      HashedPairs calls blobs ∧ BinderTreeBuilt (binderLeavesData owner.binders.toList) tree ∧
      RawConvExpr owner.refs.toList (defnMemberRecurAddrs definition projection.block members.toList)
        owner.univs.toList owner.sharing.toList blobs h 4294967295 definition.value value ∧
      binderRootPlan tree owner.sharing.toList ((mutsRootOffset members.toList projection.idx.toNat : F) + 1)
        definition.value = some plan ∧ HeapBinderLevels h value plan
  | _ => False

/-- An actual raw Defn payload can only come from a standalone definition or a definition
projection. The runtime tag excludes all other serialized constant kinds. -/
theorem RawCIRep.defn_compatible {E : Ixon.Env} {h : Heap F} {address : _root_.Address}
    {record : Ixon.Constant} {nl ty value flag hint : SourceValue F}
    (raw : RawCIRep E h address record (.construct kciEnum "Defn" [nl, ty, value, flag, hint])) :
    (∃ d, record.info = .defn d) ∨ ∃ p, record.info = .dPrj p := by
  cases info : record.info with
  | defn d => exact .inl ⟨d, info⟩
  | dPrj p => exact .inr ⟨p, info⟩
  | axio ax | quot ax =>
    rw [RawCIRep, info] at raw
    obtain ⟨_, _, _, _, shape, _⟩ := raw
    simp at shape
  | recr rc =>
    rw [RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, shape, _, _⟩ := raw
    simp at shape
  | iPrj p =>
    rw [RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, shape, _⟩ := raw
    simp at shape
  | cPrj p =>
    rw [RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, shape, _⟩ := raw
    simp at shape
  | rPrj p =>
    rw [RawCIRep, info] at raw
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, shape, _, _⟩ := raw
    simp at shape
  | muts members =>
    rw [RawCIRep, info] at raw
    exact raw.elim

/-- A successful actual definition load supplies its source, owner (if any), value pointer and
serialized binder plan. No modeled-definition or closed-reader premise is assumed. -/
theorem get_ci_definition_trace {env : Ixon.Env} {rootCalls calls : List (Call F)}
    (noCollision : ¬ View.HashedCollision { env := env } [] rootCalls)
    (bounded : IxVM.Consistency.Bounded calls) (subset : ∀ call ∈ calls, call ∈ rootCalls)
    {address : Aiur.Library.Bytes.Address} {ap ptr nl ty value flag hint : SourceValue F}
    {h h' : Heap F} (addressRep : Aiur.Library.Bytes.RepAddressRef addrTy h address ap)
    (observed : ObsFn W "Ingress::get_ci" [ap] h ptr h' calls)
    (shape : loadValue h' ptr = .ok (.construct kciEnum "Defn" [nl, ty, value, flag, hint])) :
    ∃ (bytes : ByteArray) (record : Ixon.Constant),
      Hashed calls bytes ∧ Address.blake3Pure bytes = ixAddr address ∧
      Ixon.deConstantExact bytes = .ok record ∧ DefinitionValueTrace calls h' (ixAddr address) record nl value := by
  obtain ⟨bytes, record, hashed, hashEq, decoded, trace⟩ := get_ci_trace_spec addressRep observed
  obtain ⟨_, bytes', loadedEnv, hashed', hashEq', _, record', decoded', _, _, actual,
    loaded, raw⟩ := get_ci_loadedL1_spec bounded addressRep observed
  have bytesEq : bytes' = bytes := hashed_bytes_unique noCollision
    (hashed_mono subset hashed') hashEq' (hashed_mono subset hashed) hashEq
  subst bytes'
  have recordEq : record' = record := Except.ok.inj (decoded'.symm.trans decoded)
  subst record'
  have actualEq : actual = .construct kciEnum "Defn" [nl, ty, value, flag, hint] :=
    Except.ok.inj (loaded.symm.trans shape)
  subst actual
  rcases raw.defn_compatible with ⟨definition, info⟩ | ⟨projection, info⟩
  · rw [GetCITraceResult, info] at trace
    obtain ⟨blobs, tree, actual, hashedBlobs, built, loaded', definitionTrace⟩ := trace
    have actualEq := Except.ok.inj (loaded'.symm.trans shape)
    subst actual
    obtain ⟨bound, tp, vp, hint', typePlan, valuePlan, definitionShape, _, converted,
      _, planned, levels, valueLevels⟩ := definitionTrace
    have kind := defn_kind definitionShape.symm
    have fields := definitionShape.symm
    simp only [defnValShape, kind, Value.construct.injEq, List.cons.injEq, and_true, true_and] at fields
    obtain ⟨countEq, _, valueEq, _, _⟩ := fields
    cases valueEq
    refine ⟨bytes, record, hashed, hashEq, decoded, ?_⟩
    rw [DefinitionValueTrace, info]
    exact ⟨blobs, tree, valuePlan, kind, bound, countEq.symm, hashedBlobs, built, converted, planned, valueLevels⟩
  · rw [GetCITraceResult, info] at trace
    obtain ⟨indexBound, ownerBytes, owner, members, definition, blobs, tree, actual,
      ownerHashed, ownerHash, ownerDecoded, ownerInfo, selected, hashedBlobs, built, loaded', definitionTrace⟩ := trace
    have actualEq := Except.ok.inj (loaded'.symm.trans shape)
    subst actual
    obtain ⟨bound, tp, vp, hint', typePlan, valuePlan, definitionShape, _, converted,
      _, planned, levels, valueLevels⟩ := definitionTrace
    have kind := defn_kind definitionShape.symm
    have fields := definitionShape.symm
    simp only [defnValShape, kind, Value.construct.injEq, List.cons.injEq, and_true, true_and] at fields
    obtain ⟨countEq, _, valueEq, _, _⟩ := fields
    cases valueEq
    refine ⟨bytes, record, hashed, hashEq, decoded, ?_⟩
    rw [DefinitionValueTrace, info]
    exact ⟨indexBound, ownerBytes, owner, members, definition, blobs, tree, valuePlan,
      ownerHashed, ownerHash, ownerDecoded, ownerInfo, selected, kind, bound, countEq.symm,
      hashedBlobs, built, converted, planned, valueLevels⟩

end IxVM.Refinement.L1
