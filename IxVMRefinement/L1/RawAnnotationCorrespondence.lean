import IxVMRefinement.L1.AnnotationCorrespondence

/-! # Common raw syntax from actual repeated root conversion

The serialized binder plan fixes both exact metadata and retained let syntax. These
producers keep the existing closed-reader and level-coverage hypotheses explicit.
They do not identify a semantic let-erased annotation with its raw physical syntax.
-/

namespace IxVM.Refinement.L1

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Refinement.Deserialize

/-- Two conversions of one reader root and serialized plan admit one common exact annotation. -/
theorem same_raw_annotation_of_root_plans {κ : _root_.Address → Core.KKey} [∀ a, Core.Resolved (κ a)]
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
    ∃ raw annotated, IxVM.Consistency.Annotates annotated E_rd ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h₁ 0 (Core.posOf ps raw) (Core.posOf ps annotated) kp₁) ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ h₂ 0 (Core.posOf ps raw) (Core.posOf ps annotated) kp₂) := by
  have samePlan := Option.some.inj (planned₁.symm.trans planned₂)
  cases samePlan
  obtain ⟨rawLeft, left, annotates, first, firstTrace, firstRawTrace⟩ :=
    raw₁.toRawTmCExactTrace hperm hps_lt hkeyAt hself hblob₁ hread hlbb hdef
  obtain ⟨rawRight, right, _, second, secondTrace, secondRawTrace⟩ :=
    raw₂.toRawTmCExactTrace hperm hps_lt hkeyAt hself hblob₂ hread hlbb hdef
  have firstRead := firstTrace plan₁ levels₁ []
  have secondRead := secondTrace plan₁ levels₂ []
  have same := (applyBinderTrace_unique firstRead secondRead).1
  cases same
  have rawSame := (applyRawBinderTrace_unique
    (firstRawTrace plan₁ levels₁ []) (secondRawTrace plan₁ levels₂ [])).1
  cases rawSame
  exact ⟨rawLeft, left, annotates, first, second⟩

/-- Actual table construction and root conversion in two heaps produce a common exact
reader annotation. Literal agreement is required only for hashes in those root traces. -/
theorem observed_roots_same_raw_annotation {κ : _root_.Address → Core.KKey} [∀ a, Core.Resolved (κ a)]
    {ps : List Ix.Kernel.LevelParam}
    (hperm : ps.Perm (List.range ps.length)) (hps_lt : ps.length < 4294967296)
    {cx : Ix.Kernel.Reader.Ctx .anon} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM Core.KKey)}
    {recurAddrs : List _root_.Address} {blocks : List Ixon.BinderBlock}
    {before₁ before₂ h₁ h₂ after₁ after₂ : Heap F}
    {blocksPtr₁ blocksPtr₂ tbl₁ tbl₂ ep₁ ep₂ sh₁ sh₂ refs₁ refs₂ rec₁ rec₂ univs₁ univs₂
      kp₁ kp₂ : SourceValue F}
    {tableCalls₁ tableCalls₂ calls₁ calls₂ : List (Call F)} {root : F} {e : Ixon.Expr}
    (blocksRep₁ : Aiur.Library.List.RepList Deserialize.binderBlockListEnum
      Deserialize.RepBinderBlock before₁ blocks blocksPtr₁)
    (blocksRep₂ : Aiur.Library.List.RepList Deserialize.binderBlockListEnum
      Deserialize.RepBinderBlock before₂ blocks blocksPtr₂)
    (bounds : ∀ block ∈ blocks, ∀ node ∈ block.nodes.toList,
      BinderNodeParamsLt 4294967296 node)
    (table₁ : ObsFn Core.W "Convert::binder_table" [blocksPtr₁] before₁ tbl₁ h₁ tableCalls₁)
    (table₂ : ObsFn Core.W "Convert::binder_table" [blocksPtr₂] before₂ tbl₂ h₂ tableCalls₂)
    (expr₁ : RepExpr h₁ e ep₁) (expr₂ : RepExpr h₂ e ep₂)
    (sharing₁ : RepShareVec h₁ src.sharing.toList sh₁)
    (sharing₂ : RepShareVec h₂ src.sharing.toList sh₂)
    (refsRep₁ : Aiur.Library.List.RepList Deserialize.addressListEnum RepIxonAddressRef
      h₁ src.refs.toList refs₁)
    (refsRep₂ : Aiur.Library.List.RepList Deserialize.addressListEnum RepIxonAddressRef
      h₂ src.refs.toList refs₂)
    (recurRep₁ : Aiur.Library.List.RepList Deserialize.addressListEnum RepIxonAddressRef
      h₁ recurAddrs rec₁)
    (recurRep₂ : Aiur.Library.List.RepList Deserialize.addressListEnum RepIxonAddressRef
      h₂ recurAddrs rec₂)
    (univsRep₁ : Aiur.Library.List.RepList Deserialize.univListEnum RepUnivPtr
      h₁ src.univs.toList univs₁)
    (univsRep₂ : Aiur.Library.List.RepList Deserialize.univListEnum RepUnivPtr
      h₂ src.univs.toList univs₂)
    (converted₁ : ObsFn Core.W "Convert::convert_root"
      [ep₁, sh₁, refs₁, rec₁, univs₁, tbl₁, .field root] h₁ kp₁ after₁ calls₁)
    (converted₂ : ObsFn Core.W "Convert::convert_root"
      [ep₂, sh₂, refs₂, rec₂, univs₂, tbl₂, .field root] h₂ kp₂ after₂ calls₂)
    (keyed : ∀ a k, cx.keyAt a = .ok k → k = κ a)
    (selfKeyed : ∀ i a m k, recurAddrs[i]? = some a → self i = some m → m = .ok k → k = κ a)
    (blobs₁ : ∀ a bytes, Hashed calls₁ bytes → Address.blake3Pure bytes = a → cx.blob a = some bytes)
    (blobs₂ : ∀ a bytes, Hashed calls₂ bytes → Address.blake3Pure bytes = a → cx.blob a = some bytes)
    {readerType : Core.KExpr}
    (read : (Ix.Kernel.Reader.MemberReader.mk' cx src (Ix.Kernel.Reader.recParam ps) self).read e =
      .ok readerType)
    (varsBounded : readerType.looseBVarsBounded 0 = true)
    (levelsDefined : readerType.allLevelParamsDefined ps = true) :
    ∃ raw annotated, IxVM.Consistency.Annotates annotated readerType ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ after₁ 0 (Core.posOf ps raw) (Core.posOf ps annotated) kp₁) ∧
      (∀ d Γ, Decl.RawTmExact κ d Γ after₂ 0 (Core.posOf ps raw) (Core.posOf ps annotated) kp₂) := by
  obtain ⟨_, tree₁, built₁, represented₁, _, bounded₁⟩ :=
    binder_table_data_bounded_spec blocksRep₁ bounds table₁
  obtain ⟨_, tree₂, built₂, represented₂, _, bounded₂⟩ :=
    binder_table_data_bounded_spec blocksRep₂ bounds table₂
  have sameTree := built₁.unique built₂
  cases sameTree
  obtain ⟨_, loaded₁, hashed₁, raw₁, plan₁, planned₁, levels₁⟩ :=
    convert_root_trace_spec expr₁ sharing₁ refsRep₁ recurRep₁ univsRep₁ represented₁ bounded₁ converted₁
  obtain ⟨_, loaded₂, hashed₂, raw₂, plan₂, planned₂, levels₂⟩ :=
    convert_root_trace_spec expr₂ sharing₂ refsRep₂ recurRep₂ univsRep₂ represented₂ bounded₂ converted₂
  exact same_raw_annotation_of_root_plans hperm hps_lt keyed selfKeyed
    (fun a bytes member => blobs₁ a bytes (hashed₁ (a, bytes) member).1 (hashed₁ (a, bytes) member).2)
    (fun a bytes member => blobs₂ a bytes (hashed₂ (a, bytes) member).1 (hashed₂ (a, bytes) member).2)
    raw₁ raw₂ planned₁ planned₂ levels₁ levels₂ read varsBounded levelsDefined

end IxVM.Refinement.L1
