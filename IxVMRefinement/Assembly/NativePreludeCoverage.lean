import IxVMRefinement.Assembly.NativePreludeReader
import Ix.Cert.InductiveUnits

/-! # Actual member names read by the prelude

The successful native-family loops produce the member-key reads themselves, as well as
coverage of those keys by an inductive declaration. Applying this to the real prelude read
makes its former and constructor name witnesses concrete.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (ite_ok fail_bind)

/-- Successful singleton-family reading produces a key read for its former and each
actual constructor slot. -/
theorem readInductive_native_member_keys {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readInductive cx state owner source members = .ok result) :
    (∃ key, cx.memberKey (.member owner member) = .ok key) ∧
    (∀ slot ctor, ind.ctors[slot]? = some ctor → ∃ key, cx.memberKey (.ctor owner member slot) = .ok key) := by
  obtain ⟨_, _, _, row, _, _, _, former, ctors⟩ :=
    readInductive_one_native_frames indexBuilt stored kind memberAt one read
  refine ⟨⟨row.1.name, former.1⟩, ?_⟩
  intro slot ctor ctorAt
  have slotMember : (member, ctor, slot) ∈ nativeCtorSlots [(member, ind)] := by
    simp only [nativeCtorSlots, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.mem_map.mpr ⟨(ctor, slot),
      Array.mem_toList_iff.mpr (Array.mk_mem_zipIdx_iff_getElem?.mpr ctorAt), rfl⟩
  obtain ⟨ctorRow, _, frame⟩ := Ix.Cert.InductiveUnits.forall₂_mem_left ctors _ slotMember
  exact ⟨ctorRow.1.name, frame.1.1⟩

/-- A successful record read contains those same actual native member-key reads. -/
theorem readRecord_native_member_keys {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readRecord cx state owner source = .ok result) :
    (∃ key, cx.memberKey (.member owner member) = .ok key) ∧
    (∀ slot ctor, ind.ctors[slot]? = some ctor → ∃ key, cx.memberKey (.ctor owner member slot) = .ok key) := by
  have hasInductive : members.any (fun | .indc _ => true | _ => false) = true := by
    apply Array.any_eq_true'.mpr
    exact ⟨.indc ind, Array.mem_of_getElem? memberAt, rfl⟩
  unfold readRecord at read
  rw [kind] at read
  dsimp only at read
  rcases Ix.Cert.CtxAgree.ite_ok' read with ⟨_, read⟩ | ⟨absent, _⟩
  · rcases ite_ok read with rejected | read
    · exact (fail_bind rejected).elim
    · obtain ⟨_, nativeRead, _⟩ := except_bind_ok.mp read
      exact readInductive_native_member_keys indexBuilt stored kind memberAt one nativeRead
  · exact (absent hasInductive).elim

/-- A concrete singleton-family prelude record supplies actual member-key reads and
inductive declaration coverage in the prelude's own output. -/
theorem prelude_native_member_reads {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (present : (owner, source) ∈ prelude.records) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)]) :
    let cx := nativePreludeReaderCtx table prelude
    (∃ key, cx.memberKey (.member owner member) = .ok key ∧
      ReaderInductiveKey prelude.ix.decls.toList key) ∧
    (∀ slot ctor, ind.ctors[slot]? = some ctor → ∃ key, cx.memberKey (.ctor owner member slot) = .ok key ∧
      ReaderInductiveKey prelude.ix.decls.toList key) := by
  let cx := nativePreludeReaderCtx table prelude
  have stream := readRecords_spec (preludeFor_readRecords prepared)
  obtain ⟨state, result, read, contained⟩ := stream.mem (Array.mem_toList_iff.mpr present)
  have stored : cx.store owner = some source := by
    rw [nativePreludeReaderCtx_store]
    exact ReaderStoreTransfer.fallback_of_mem prepared (Array.mem_append_left _ present)
  have built : ∃ records : Array (_root_.Address × Ixon.Constant), cx.index = buildIndex cx.store records :=
    ⟨_, rfl⟩
  obtain ⟨records, indexBuilt⟩ := built
  have keys := readRecord_native_member_keys indexBuilt stored kind memberAt one read
  have names := readRecord_native_member_names indexBuilt stored kind memberAt one read
  have lift {key : Key .anon} (covered : ReaderInductiveKey result.decls.toList key) :
      ReaderInductiveKey prelude.ix.decls.toList key := by
    obtain ⟨block, params, declared, named⟩ := covered
    exact ⟨block, params, Array.mem_toList_iff.mpr
      (contained _ (Array.mem_toList_iff.mp declared)), named⟩
  obtain ⟨key, keyRead⟩ := keys.1
  refine ⟨⟨key, keyRead, lift (names.1 key keyRead)⟩, ?_⟩
  intro slot ctor ctorAt
  obtain ⟨key, keyRead⟩ := keys.2 slot ctor ctorAt
  exact ⟨key, keyRead, lift (names.2 slot ctor key ctorAt keyRead)⟩


/-- The native former is the first name of its actual inductive declaration. -/
theorem readInductive_native_former_head {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readInductive cx state owner source members = .ok result) :
    ∃ key, cx.memberKey (.member owner member) = .ok key ∧
      ∃ declaration ∈ result.decls.toList, Frontend.preludeKey declaration = some key := by
  obtain ⟨generated, bare, block, row, declarations, lowered, types, former, _⟩ :=
    readInductive_one_native_frames indexBuilt stored kind memberAt one read
  have bareDecl : bare.decls = #[Ix.Cert.CtxAgree.indDeclOf block] :=
    (lowerInductiveBare_spec lowered).2.1
  refine ⟨row.1.name, former.1, Ix.Cert.CtxAgree.indDeclOf block, ?_, ?_⟩
  · rw [declarations, bareDecl]
    simp
  · simp [Frontend.preludeKey, Ix.Cert.CtxAgree.indDeclOf, Declaration.names, types,
      ConstantInfo.name, ConstantInfo.toConstantVal]

/-- Finishing a record retains the declaration headed by its actual native former. -/
theorem readRecord_native_former_head {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readRecord cx state owner source = .ok result) :
    ∃ key, cx.memberKey (.member owner member) = .ok key ∧
      ∃ declaration ∈ result.decls.toList, Frontend.preludeKey declaration = some key := by
  have hasInductive : members.any (fun | .indc _ => true | _ => false) = true := by
    apply Array.any_eq_true'.mpr
    exact ⟨.indc ind, Array.mem_of_getElem? memberAt, rfl⟩
  unfold readRecord at read
  rw [kind] at read
  dsimp only at read
  rcases Ix.Cert.CtxAgree.ite_ok' read with ⟨_, read⟩ | ⟨absent, _⟩
  · rcases ite_ok read with rejected | read
    · exact (fail_bind rejected).elim
    · obtain ⟨native, nativeRead, finish⟩ := except_bind_ok.mp read
      obtain ⟨key, keyRead, declaration, declared, head⟩ :=
        readInductive_native_former_head indexBuilt stored kind memberAt one nativeRead
      refine ⟨key, keyRead, declaration, ?_, head⟩
      rcases finishInductiveRead_spec finish with rfl | ⟨twins, _, rfl⟩
      · exact declared
      · simpa only [Array.toList_append] using List.mem_append_left twins.decls.toList declared
  · exact (absent hasInductive).elim

/-- The actual prelude read exposes a declaration whose first name is this native former. -/
theorem prelude_native_former_head {table : RoleTable} {prelude : Prelude .anon}
    (prepared : preludeFor table = .ok prelude)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive}
    (present : (owner, source) ∈ prelude.records) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)]) :
    ∃ key, (nativePreludeReaderCtx table prelude).memberKey (.member owner member) = .ok key ∧
      ∃ declaration ∈ prelude.ix.decls.toList, Frontend.preludeKey declaration = some key := by
  let cx := nativePreludeReaderCtx table prelude
  have stream := readRecords_spec (preludeFor_readRecords prepared)
  obtain ⟨state, result, read, contained⟩ := stream.mem (Array.mem_toList_iff.mpr present)
  have stored : cx.store owner = some source := by
    rw [nativePreludeReaderCtx_store]
    exact ReaderStoreTransfer.fallback_of_mem prepared (Array.mem_append_left _ present)
  have built : ∃ records : Array (_root_.Address × Ixon.Constant), cx.index = buildIndex cx.store records :=
    ⟨_, rfl⟩
  obtain ⟨records, indexBuilt⟩ := built
  obtain ⟨key, keyRead, declaration, declared, head⟩ :=
    readRecord_native_former_head indexBuilt stored kind memberAt one read
  exact ⟨key, keyRead, declaration,
    Array.mem_toList_iff.mpr (contained _ (Array.mem_toList_iff.mp declared)), head⟩

end IxVM.Refinement.Assembly
