import Ix.CompileCert.ReaderIndex

/-! Provenance of indexed recursors and correspondence between discovered
groups and indexed entries. The scanned-record/store equality needed by the
reader remains an explicit publication condition. -/

namespace Ix.CompileCert.ReaderIndexEntries

open Ix Kernel.Reader
open _root_.Ix.Kernel (ConstRef)
open ReaderIndex (Found BuildState inductives orderFor orderValid candidate recordStep completeStep)

def entryName (pins : Std.HashMap (ConstRef Address) Kernel.Name) (block : Address)
    (motive count : Nat) (order : Array Nat) : Kernel.Name :=
  let name (ref : ConstRef Address) := pins.getD ref (keyName ref)
  if motive < count then (name (.member block (order[motive]!))).str "rec"
  else (name (.member block (order[0]!))).str s!"rec_{motive - count + 1}"

def From (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (ref : ConstRef Address) (entry : RecEntry) : Prop :=
  ∃ owner constant position recursor carriers firstIndex blockConstant members firstSlot first,
    ref = .member owner position ∧ (owner, constant) ∈ records ∧
    (position, recursor) ∈ recursorMembers constant ∧
    analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) ∧
    carriers[0]? = some (.member entry.block firstIndex) ∧
    store entry.block = some blockConstant ∧ blockConstant.info = .muts members ∧
    (inductives members)[0]? = some (firstSlot, first) ∧
    orderValid firstIndex (inductives members) (orderFor carriers entry.block (inductives members).size) = true ∧
    entry.large = (recursor.lvls.toNat == first.lvls.toNat + 1) ∧
    entry.name = entryName pins entry.block entry.motive (inductives members).size
      (orderFor carriers entry.block (inductives members).size)

def Provenance (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (index : RecIndex) : Prop :=
  ∀ ref entry, index.recs[ref]? = some entry → From store pins records ref entry

def FoundMatches (state : BuildState) : Prop :=
  ∀ (block : Address) (pairs : Array (Nat × ConstRef Address)), state.2[block]? = some pairs →
    ∀ pair ∈ pairs, ∃ entry, state.1.recs[pair.2]? = some entry ∧ entry.block = block ∧ entry.motive = pair.1

def Grouped (index : RecIndex) : Prop :=
  ∀ (block : Address) (shape : BlockShape), index.blocks[block]? = some shape → ∀ ref ∈ shape.recs,
    ∃ entry : RecEntry, index.recs[ref]? = some entry ∧ entry.block = block

def Valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (state : BuildState) : Prop :=
  Provenance store pins records state.1 ∧ FoundMatches state ∧ Grouped state.1

def RecsExtend (before after : RecIndex) : Prop :=
  ∀ (ref : ConstRef Address) (entry : RecEntry), before.recs[ref]? = some entry → after.recs[ref]? = some entry

theorem recs_insert_extends (index : RecIndex) (ref : ConstRef Address) (entry : RecEntry)
    (fresh : index.recs.contains ref = false) : RecsExtend index { index with recs := index.recs.insert ref entry } := by
  intro query old found
  rw [Std.HashMap.getElem?_insert]
  by_cases same : ref == query
  · have equal := beq_iff_eq.mp same
    subst query
    rw [Std.HashMap.contains_eq_isSome_getElem?, found] at fresh
    cases fresh
  · simp only [same, Bool.false_eq_true, ↓reduceIte]
    exact found

theorem provenance_insert (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (index : RecIndex) (ref : ConstRef Address) (entry : RecEntry)
    (valid : Provenance store pins records index) (newEntry : From store pins records ref entry) :
    Provenance store pins records { index with recs := index.recs.insert ref entry } := by
  intro query value found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst query
    cases Option.some.inj found
    exact newEntry
  · exact valid query value found

theorem grouped_extends (before after : RecIndex) (sameBlocks : after.blocks = before.blocks)
    (growth : RecsExtend before after) (valid : Grouped before) : Grouped after := by
  intro block shape found ref present
  rw [sameBlocks] at found
  obtain ⟨entry, stored, owner⟩ := valid block shape found ref present
  exact ⟨entry, growth ref entry stored, owner⟩

theorem grouped_empty_insert (index : RecIndex) (owner : Address) (order : Array Nat) (valid : Grouped index) :
    Grouped { index with blocks := index.blocks.insert owner ⟨order, #[]⟩ } := by
  intro block shape found ref present
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases Option.some.inj found
    simp at present
  · exact valid block shape found ref present

theorem found_getD (state : BuildState) (valid : FoundMatches state) (block : Address) :
    ∀ pair ∈ state.2.getD block #[],
      ∃ entry, state.1.recs[pair.2]? = some entry ∧ entry.block = block ∧ entry.motive = pair.1 := by
  rw [Std.HashMap.getD_eq_getD_getElem?]
  cases found : state.2[block]? with
  | none => simp
  | some pairs => exact valid block pairs found

theorem found_insert (before : BuildState) (after : RecIndex) (ref : ConstRef Address) (entry : RecEntry)
    (valid : FoundMatches before) (growth : RecsExtend before.1 after) (inserted : after.recs[ref]? = some entry) :
    FoundMatches (after, before.2.insert entry.block ((before.2.getD entry.block #[]).push (entry.motive, ref))) := by
  intro block pairs found pair present
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst block
    cases Option.some.inj found
    rcases Array.mem_push.mp present with old | new
    · obtain ⟨oldEntry, stored, owner, motive⟩ := found_getD before valid entry.block pair old
      exact ⟨oldEntry, growth pair.2 oldEntry stored, owner, motive⟩
    · subst pair
      exact ⟨entry, inserted, rfl, rfl⟩
  · obtain ⟨oldEntry, stored, owner, motive⟩ := valid block pairs found pair present
    exact ⟨oldEntry, growth pair.2 oldEntry stored, owner, motive⟩

theorem valid_empty (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) : Valid store pins records ({}, {}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ref entry found; simp at found
  · intro block pairs found; simp at found
  · intro block shape found; simp at found

theorem update_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (before : BuildState) (ref : ConstRef Address) (entry : RecEntry)
    (valid : Valid store pins records before) (fresh : before.1.recs.contains ref = false)
    (newEntry : From store pins records ref entry) :
    Valid store pins records
      ({ before.1 with recs := before.1.recs.insert ref entry },
        before.2.insert entry.block ((before.2.getD entry.block #[]).push (entry.motive, ref))) := by
  have growth := recs_insert_extends before.1 ref entry fresh
  exact ⟨provenance_insert store pins records before.1 ref entry valid.1 newEntry,
    found_insert before _ ref entry valid.2.1 growth (by simp),
    grouped_extends before.1 _ rfl growth valid.2.2⟩

theorem new_block_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (state : BuildState) (owner : Address) (order : Array Nat)
    (valid : Valid store pins records state) :
    Valid store pins records ({ state.1 with blocks := state.1.blocks.insert owner ⟨order, #[]⟩ }, state.2) :=
  ⟨valid.1, valid.2.1, grouped_empty_insert state.1 owner order valid.2.2⟩

theorem candidate_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (owner : Address) (constant : Ixon.Constant)
    (present : (owner, constant) ∈ records) (member : Nat × Ixon.Recursor)
    (memberPresent : member ∈ recursorMembers constant) (before : BuildState)
    (valid : Valid store pins records before) :
    CanonUnivMeaning.StepHolds (Valid store pins records) (candidate store pins owner constant member before) := by
  rcases member with ⟨position, recursor⟩
  unfold candidate
  dsimp only
  split
  · exact valid
  · rename_i notPresent
    have fresh : before.1.recs.contains (.member owner position) = false := Bool.eq_false_iff.mpr notPresent
    split
    · rename_i motive carriers major foundAnalysis
      split
      · rename_i block firstIndex carrierFound
        split
        · rename_i blockRecord stored
          split
          · rename_i members kind
            split
            · rename_i firstSlot first firstFound
              split
              · rename_i guarded
                split
                · exact valid
                · let entry : RecEntry := ⟨block, motive, major,
                    recursor.lvls.toNat == first.lvls.toNat + 1,
                    entryName pins block motive (inductives members).size (orderFor carriers block (inductives members).size)⟩
                  have provenance : From store pins records (.member owner position) entry :=
                    ⟨owner, constant, position, recursor, carriers, firstIndex, blockRecord, members, firstSlot, first,
                      rfl, present, memberPresent, foundAnalysis, carrierFound, stored, kind, firstFound, guarded, rfl, rfl⟩
                  have updated := update_valid store pins records before (.member owner position) entry valid fresh provenance
                  split
                  · exact updated
                  · exact new_block_valid store pins records _ block _ updated
              · exact valid
            · exact valid
          · exact valid
        · exact valid
      · exact valid
    · exact valid

theorem record_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (record : Address × Ixon.Constant) (present : record ∈ records)
    (before : BuildState) (valid : Valid store pins records before) :
    CanonUnivMeaning.StepHolds (Valid store pins records) (recordStep store pins record before) := by
  apply CanonUnivEmit.arrayLoop_preserves (Valid store pins records) (recursorMembers record.2) before
    (candidate store pins record.1 record.2) valid
  intro member memberPresent state good
  exact candidate_valid store pins records record.1 record.2 present member memberPresent state good

theorem collect_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) :
    Valid store pins records (forIn (m := Id) records ({}, {}) (recordStep store pins)) := by
  apply CanonUnivEmit.arrayLoop_preserves (Valid store pins records) records ({}, {}) (recordStep store pins)
    (valid_empty store pins records)
  intro record present state good
  exact record_valid store pins records record present state good

theorem complete_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (found : Found)
    (pair : Address × Array (Nat × ConstRef Address)) (present : pair ∈ found.toList)
    (index : RecIndex) (valid : Valid store pins records (index, found)) :
    CanonUnivMeaning.StepHolds (fun next => Valid store pins records (next, found)) (completeStep pair index) := by
  have foundPair : found[pair.1]? = some pair.2 := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp present
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro block shape stored ref inShape
  change (index.blocks.insert pair.1
    { index.blocks.getD pair.1 default with recs := (pair.2.qsort (fun a b => a.1 < b.1)).map (·.2) })[block]? = some shape at stored
  rw [Std.HashMap.getElem?_insert] at stored
  split at stored
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst block
    cases Option.some.inj stored
    obtain ⟨entryPair, inSorted, rfl⟩ := Array.mem_map.mp inShape
    have inFound : entryPair ∈ pair.2 := Canon.mem_qsort.mp inSorted
    obtain ⟨entry, entryFound, owner, _⟩ := valid.2.1 pair.1 pair.2 foundPair entryPair inFound
    exact ⟨entry, entryFound, owner⟩
  · exact valid.2.2 block shape stored ref inShape

theorem run_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) :
    Provenance store pins records (ReaderIndex.run store pins records) ∧ Grouped (ReaderIndex.run store pins records) := by
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store pins)
  have valid : Valid store pins records collected := collect_valid store pins records
  have completed := CanonUnivMeaning.listLoop_preserves
    (fun index => Valid store pins records (index, collected.2)) collected.2.toList collected.1 completeStep valid
    (fun pair present index good => complete_valid store pins records collected.2 pair present index good)
  exact ⟨completed.1, completed.2.2⟩

theorem buildIndex_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) :
    Provenance store pins records (buildIndex store pins records) ∧ Grouped (buildIndex store pins records) := by
  rw [← ReaderIndex.run_eq]
  exact run_valid store pins records

def Coherent (store : Store) (records : Array (Address × Ixon.Constant)) : Prop :=
  ∀ owner constant, (owner, constant) ∈ records → store owner = some constant

/-- The lookup used later by the family reader is justified by record/store
coherence, separately from provenance in the scanned record array. -/
theorem entry_stored (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (ref : ConstRef Address) (entry : RecEntry)
    (found : (buildIndex store pins records).recs[ref]? = some entry) :
    ∃ owner constant position recursor carriers,
      ref = .member owner position ∧ store owner = some constant ∧
      (position, recursor) ∈ recursorMembers constant ∧
      analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) := by
  obtain ⟨owner, constant, position, recursor, carriers, _, _, _, _, _, reference, present, member, analysed, _⟩ :=
    (buildIndex_valid store pins records).1 ref entry found
  exact ⟨owner, constant, position, recursor, carriers, reference, coherent owner constant present, member, analysed⟩

/-- Every recursor reference placed in a completed block shape resolves to
an indexed entry owned by that block and retains its scanned-source origin. -/
theorem grouped_entry (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (block : Address) (shape : BlockShape)
    (shapeFound : (buildIndex store pins records).blocks[block]? = some shape)
    (ref : ConstRef Address) (present : ref ∈ shape.recs) :
    ∃ entry, (buildIndex store pins records).recs[ref]? = some entry ∧ entry.block = block ∧
      From store pins records ref entry := by
  have valid := buildIndex_valid store pins records
  obtain ⟨entry, found, owner⟩ := valid.2 block shape shapeFound ref present
  exact ⟨entry, found, owner, valid.1 ref entry found⟩

theorem member_source (constant : Ixon.Constant) (position : Nat) (recursor : Ixon.Recursor)
    (present : (position, recursor) ∈ recursorMembers constant) :
    match constant.info with
    | .recr value => position = 0 ∧ recursor = value
    | .muts members => members[position]? = some (.recr recursor)
    | _ => False := by
  cases kind : constant.info with
  | recr value => simpa [recursorMembers, kind] using present
  | muts members =>
    simp only [recursorMembers, kind] at present
    obtain ⟨⟨value, index⟩, indexed, selected⟩ := Array.mem_filterMap.mp present
    cases value with
    | defn value => cases selected
    | indc value => cases selected
    | recr value =>
      have same : (index, value) = (position, recursor) := Option.some.inj selected
      cases same
      exact Array.mk_mem_zipIdx_iff_getElem?.mp indexed
  | _ => simp [recursorMembers, kind] at present

theorem member_unique (constant : Ixon.Constant) (position : Nat) (first second : Ixon.Recursor)
    (left : (position, first) ∈ recursorMembers constant) (right : (position, second) ∈ recursorMembers constant) : first = second := by
  have firstSource := member_source constant position first left
  have secondSource := member_source constant position second right
  cases kind : constant.info with
  | recr value =>
    simp only [kind] at firstSource secondSource
    exact firstSource.2.trans secondSource.2.symm
  | muts members =>
    simp only [kind] at firstSource secondSource
    exact Ixon.MutConst.recr.inj (Option.some.inj (firstSource.symm.trans secondSource))
  | _ => simp [kind] at firstSource

/-- Position uniqueness of the actual recursor-member enumeration supplies
the `find?` lookup used by `readInductive`, without a new uniqueness premise. -/
theorem member_lookup (constant : Ixon.Constant) (position : Nat) (recursor : Ixon.Recursor)
    (present : (position, recursor) ∈ recursorMembers constant) :
    (recursorMembers constant).find? (·.1 == position) = some (position, recursor) := by
  cases found : (recursorMembers constant).find? (·.1 == position) with
  | none =>
    have absent := Array.find?_eq_none.mp found (position, recursor) present
    simp at absent
  | some pair =>
    rcases pair with ⟨index, value⟩
    have predicate := Array.find?_some (p := fun value : Nat × Ixon.Recursor => value.1 == position) found
    have same : index = position := beq_iff_eq.mp predicate
    subst index
    have equal := member_unique constant position value recursor (Array.mem_of_find?_eq_some found) present
    cases equal
    rfl

theorem entry_lookup (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (ref : ConstRef Address) (entry : RecEntry)
    (found : (buildIndex store pins records).recs[ref]? = some entry) :
    ∃ owner constant position recursor carriers,
      ref = .member owner position ∧ store owner = some constant ∧
      (recursorMembers constant).find? (·.1 == position) = some (position, recursor) ∧
      analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) := by
  obtain ⟨owner, constant, position, recursor, carriers, reference, stored, member, analysed⟩ :=
    entry_stored store pins records coherent ref entry found
  exact ⟨owner, constant, position, recursor, carriers, reference, stored,
    member_lookup constant position recursor member, analysed⟩

theorem grouped_lookup (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (block : Address) (shape : BlockShape) (shapeFound : (buildIndex store pins records).blocks[block]? = some shape)
    (ref : ConstRef Address) (present : ref ∈ shape.recs) :
    ∃ entry owner constant position recursor carriers,
      (buildIndex store pins records).recs[ref]? = some entry ∧ entry.block = block ∧
      ref = .member owner position ∧ store owner = some constant ∧
      (recursorMembers constant).find? (·.1 == position) = some (position, recursor) ∧
      analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) := by
  obtain ⟨entry, found, ownerEq, _⟩ := grouped_entry store pins records block shape shapeFound ref present
  obtain ⟨owner, constant, position, recursor, carriers, reference, stored, member, analysed⟩ :=
    entry_lookup store pins records coherent ref entry found
  exact ⟨entry, owner, constant, position, recursor, carriers, found, ownerEq, reference, stored, member, analysed⟩

end Ix.CompileCert.ReaderIndexEntries
