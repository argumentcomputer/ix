import IxVMRefinement.Assembly.NativeFormerReader
import IxVMRefinement.Assembly.GeneratedCloser
import IxVMRefinement.Assembly.PrepareFilter

/-! # Native member names in the actual reader output

The native family's former and constructor frames come from one successful lowering.
Their names therefore occur in that lowering's own inductive declaration and in the
record output, even when generated declarations or same-record twins surround it.
-/

namespace IxVM.Refinement.Assembly

open Ix.Kernel Ix.Kernel.Reader
open Ix.CompileCert.Loop (except_bind_ok)
open Ix.Cert.ReaderUnits (ite_ok fail_bind)

/-- A concrete inductive declaration in the output declares this member key. -/
def ReaderInductiveKey (output : List (Declaration .anon)) (key : Key .anon) : Prop :=
  ∃ block params, Declaration.indDecl block params ∈ output ∧
    key ∈ (Declaration.indDecl block params).names

private theorem ReaderInductiveKey.mono {source target : List (Declaration .anon)}
    (contained : ∀ declaration ∈ source, declaration ∈ target) {key : Key .anon}
    (covered : ReaderInductiveKey source key) : ReaderInductiveKey target key := by
  obtain ⟨block, params, member, named⟩ := covered
  exact ⟨block, params, contained _ member, named⟩

private theorem forall₂_member_right {α β : Type} {relation : α → β → Prop}
    {left : List α} {right : List β} (paired : List.Forall₂ relation left right)
    {entry : α} (member : entry ∈ left) :
    ∃ row ∈ right, relation entry row := by
  induction paired with
  | nil => cases member
  | cons paired rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, List.mem_cons_self, paired⟩
    · obtain ⟨row, present, related⟩ := ih later
      exact ⟨row, List.mem_cons_of_mem _ present, related⟩

/-- The actual singleton family contributes its former and each constructor name to the
same inductive declaration. No equality of independently chosen reader witnesses is used. -/
theorem readInductive_native_member_names {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readInductive cx state owner source members = .ok result) :
    (∀ key, cx.memberKey (.member owner member) = .ok key →
      ReaderInductiveKey result.decls.toList key) ∧
    (∀ slot ctor key, ind.ctors[slot]? = some ctor →
      cx.memberKey (.ctor owner member slot) = .ok key →
      ReaderInductiveKey result.decls.toList key) := by
  obtain ⟨generated, bare, block, row, declarations, lowered, types, former, ctors⟩ :=
    readInductive_one_native_frames indexBuilt stored kind memberAt one read
  have bareDecl : bare.decls = #[Ix.Cert.CtxAgree.indDeclOf block] :=
    (lowerInductiveBare_spec lowered).2.1
  have present : Ix.Cert.CtxAgree.indDeclOf block ∈ result.decls.toList := by
    rw [declarations, bareDecl]
    simp
  have covered {key : Key .anon} (named : key ∈ (Ix.Cert.CtxAgree.indDeclOf block).names) :
      ReaderInductiveKey result.decls.toList key := ⟨_, block.numParams, present, named⟩
  constructor
  · intro key keyed
    have same : key = row.1.name := Except.ok.inj (keyed.symm.trans former.1)
    apply covered
    rw [same]
    simp [Ix.Cert.CtxAgree.indDeclOf, Declaration.names, types, ConstantInfo.name]
  · intro slot ctor key ctorAt keyed
    have slotMember : (member, ctor, slot) ∈ nativeCtorSlots [(member, ind)] := by
      simp only [nativeCtorSlots, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.mem_map.mpr ⟨(ctor, slot),
        Array.mem_toList_iff.mpr (Array.mk_mem_zipIdx_iff_getElem?.mpr ctorAt), rfl⟩
    obtain ⟨ctorRow, ctorPresent, frame⟩ := forall₂_member_right ctors slotMember
    have same : key = ctorRow.1.name := Except.ok.inj (keyed.symm.trans frame.1.1)
    apply covered
    rw [same]
    have named : ctorRow.1.name ∈ block.ctors.toList.map (fun entry => entry.1.name) :=
      List.mem_map_of_mem ctorPresent
    simpa only [Ix.Cert.CtxAgree.indDeclOf, Declaration.names, List.map_append, List.map_map,
      ConstantInfo.name, ConstantInfo.toConstantVal, List.mem_append] using
      (Or.inr (Or.inl named) :
        ctorRow.1.name ∈ block.types.toList.map (fun entry => entry.1.name) ∨
          ctorRow.1.name ∈ block.ctors.toList.map (fun entry => entry.1.name) ∨
          ctorRow.1.name ∈ block.recs.toList.map (fun entry => entry.1.name))

/-- Finishing the record with its twin payloads retains the native family's declarations. -/
theorem readRecord_native_member_names {cx : Ctx .anon} {state : State .anon}
    {records : Array (_root_.Address × Ixon.Constant)}
    (indexBuilt : cx.index = buildIndex cx.store records)
    {owner : _root_.Address} {source : Ixon.Constant} {members : Array Ixon.MutConst}
    {member : Nat} {ind : Ixon.Inductive} {result : Read .anon}
    (stored : cx.store owner = some source) (kind : source.info = .muts members)
    (memberAt : members[member]? = some (.indc ind))
    (one : Ix.CompileCert.ReaderIndex.inductives members = #[(member, ind)])
    (read : readRecord cx state owner source = .ok result) :
    (∀ key, cx.memberKey (.member owner member) = .ok key →
      ReaderInductiveKey result.decls.toList key) ∧
    (∀ slot ctor key, ind.ctors[slot]? = some ctor →
      cx.memberKey (.ctor owner member slot) = .ok key →
      ReaderInductiveKey result.decls.toList key) := by
  have hasInductive : members.any (fun | .indc _ => true | _ => false) = true := by
    apply Array.any_eq_true'.mpr
    exact ⟨.indc ind, Array.mem_of_getElem? memberAt, rfl⟩
  unfold readRecord at read
  rw [kind] at read
  dsimp only at read
  rcases Ix.Cert.CtxAgree.ite_ok' read with ⟨_, read⟩ | ⟨absent, _⟩
  · rcases ite_ok read with read | read
    · exact (fail_bind read).elim
    · obtain ⟨native, nativeRead, finish⟩ := except_bind_ok.mp read
      have names := readInductive_native_member_names indexBuilt stored kind memberAt one nativeRead
      have retained : ∀ declaration ∈ native.decls.toList, declaration ∈ result.decls.toList := by
        rcases finishInductiveRead_spec finish with rfl | ⟨twins, _, rfl⟩
        · exact fun _ member => member
        · intro declaration member
          simpa only [Array.toList_append] using List.mem_append_left twins.decls.toList member
      exact ⟨fun key keyed => (names.1 key keyed).mono retained,
        fun slot ctor key found keyed => (names.2 slot ctor key found keyed).mono retained⟩
  · exact (absent hasInductive).elim

end IxVM.Refinement.Assembly
