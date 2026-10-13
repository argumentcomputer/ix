import Ix.CompileCert.ReaderAdmissionRecords

/-! Completeness of the actual reader index for eligible recursor candidates.
The builder retains one candidate per block and motive. Discovery therefore
covers motives even when another eligible reference was encountered first. -/

namespace Ix.CompileCert.ReaderIndexDiscovery

open Ix Kernel.Reader
open Ix.CompileM
open _root_.Ix.Kernel (ConstRef)
open ReaderIndex (Found BuildState candidate recordStep completeStep inductives orderFor orderValid)
open ReaderIndexEntries (From Coherent Provenance RecsExtend)
open CanonUnivMeaning (StepHolds)

/-- Coherent scanned records give each candidate reference a unique block and
motive, including when the same record occurs more than once. -/
theorem from_role_unique (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (ref : ConstRef Address) (left right : RecEntry)
    (first : From store pins records ref left) (second : From store pins records ref right) :
    left.block = right.block ∧ left.motive = right.motive := by
  obtain ⟨owner, constant, position, recursor, carriers, firstIndex, blockConstant, members,
    firstSlot, firstInd, reference, present, member, analysed, carrier, _⟩ := first
  obtain ⟨owner', constant', position', recursor', carriers', firstIndex', blockConstant', members',
    firstSlot', firstInd', reference', present', member', analysed', carrier', _⟩ := second
  have refs := ConstRef.member.inj (reference.symm.trans reference')
  rcases refs with ⟨rfl, rfl⟩
  have sameConstant := Option.some.inj ((coherent owner constant present).symm.trans
    (coherent owner constant' present'))
  subst constant'
  have sameRecursor := ReaderIndexEntries.member_unique constant position recursor recursor' member member'
  subst recursor'
  have analysis := Option.some.inj (analysed.symm.trans analysed')
  have motive := congrArg Prod.fst analysis
  have sameCarriers : carriers = carriers' :=
    congrArg (fun value : Nat × Array (ConstRef Address) × ConstRef Address => value.2.1) analysis
  rw [sameCarriers] at carrier
  exact ⟨(ConstRef.member.inj (Option.some.inj (carrier.symm.trans carrier'))).1, motive⟩

def FoundExtend (before after : Found) : Prop :=
  ∀ (block : Address) (pair : Nat × ConstRef Address),
    pair ∈ before.getD block #[] → pair ∈ after.getD block #[]

def Backed (state : BuildState) : Prop :=
  ∀ (ref : ConstRef Address) (entry : RecEntry), state.1.recs[ref]? = some entry →
    (entry.motive, ref) ∈ state.2.getD entry.block #[]

def Covered (block : Address) (motive : Nat) (state : BuildState) : Prop :=
  ∃ ref, (motive, ref) ∈ state.2.getD block #[]

theorem found_push_extends (found : Found) (block : Address) (pair : Nat × ConstRef Address) :
    FoundExtend found (found.insert block ((found.getD block #[]).push pair)) := by
  intro query old present
  by_cases same : block == query
  · have equal := beq_iff_eq.mp same
    subst query
    simp only [Std.HashMap.getD_insert_self]
    exact Array.mem_push.mpr (.inl present)
  · rw [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert]
    simp only [same, Bool.false_eq_true, ↓reduceIte]
    simpa only [Std.HashMap.getD_eq_getD_getElem?] using present

theorem backed_insert (before : BuildState) (ref : ConstRef Address) (entry : RecEntry)
    (backed : Backed before) :
    Backed ({ before.1 with recs := before.1.recs.insert ref entry },
      before.2.insert entry.block ((before.2.getD entry.block #[]).push (entry.motive, ref))) := by
  intro query value stored
  change (before.1.recs.insert ref entry)[query]? = some value at stored
  rw [Std.HashMap.getElem?_insert] at stored
  split at stored
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst query
    cases Option.some.inj stored
    simp
  · exact found_push_extends before.2 entry.block (entry.motive, ref) value.block (value.motive, query)
      (backed query value stored)

/-- Every candidate step yields, preserves old recursor entries and discovered
pairs, and maintains the reverse link from entries to their discovered groups. -/
theorem candidate_transition (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (owner : Address) (constant : Ixon.Constant) (member : Nat × Ixon.Recursor) (before : BuildState) :
    ∃ after, candidate store pins owner constant member before = .yield after ∧
      RecsExtend before.1 after.1 ∧ FoundExtend before.2 after.2 ∧ (Backed before → Backed after) := by
  rcases member with ⟨position, recursor⟩
  have unchanged : ∃ after, ForInStep.yield before = .yield after ∧
      RecsExtend before.1 after.1 ∧ FoundExtend before.2 after.2 ∧ (Backed before → Backed after) :=
    ⟨before, rfl, fun _ _ h => h, fun _ _ h => h, id⟩
  unfold candidate
  dsimp only
  split
  · exact unchanged
  · rename_i absent
    have fresh : before.1.recs.contains (.member owner position) = false := Bool.eq_false_iff.mpr absent
    split
    · split
      · split
        · split
          · split
            · split
              · split
                · exact unchanged
                · split
                  · exact ⟨_, rfl, ReaderIndexEntries.recs_insert_extends before.1 _ _ fresh,
                      found_push_extends before.2 _ _, backed_insert before _ _⟩
                  · exact ⟨_, rfl, ReaderIndexEntries.recs_insert_extends before.1 _ _ fresh,
                      found_push_extends before.2 _ _, backed_insert before _ _⟩
              · exact unchanged
            · exact unchanged
          · exact unchanged
        · exact unchanged
      · exact unchanged
    · exact unchanged

theorem covered_extends (before after : Found) (growth : FoundExtend before after)
    (block : Address) (motive : Nat) (index first : RecIndex)
    (covered : Covered block motive (index, before)) : Covered block motive (first, after) := by
  obtain ⟨ref, present⟩ := covered
  exact ⟨ref, growth block (motive, ref) present⟩

/-- An eligible candidate either contributes its motive, finds that motive
already represented, or reuses its own coherently indexed reference. -/
theorem candidate_covers (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (owner : Address) (constant : Ixon.Constant) (position : Nat) (recursor : Ixon.Recursor)
    (present : (owner, constant) ∈ records) (member : (position, recursor) ∈ recursorMembers constant)
    (entry : RecEntry) (eligible : From store pins records (.member owner position) entry)
    (before : BuildState) (provenance : Provenance store pins records before.1) (backed : Backed before) :
    StepHolds (Covered entry.block entry.motive) (candidate store pins owner constant (position, recursor) before) := by
  have origin := eligible
  obtain ⟨actualOwner, actualConstant, actualPosition, actualRecursor, carriers, firstIndex, blockConstant,
    members, firstSlot, firstInd, reference, actualPresent, actualMember, analysed, carrier,
    stored, kind, firstFound, guarded, _, _⟩ := eligible
  have refs := ConstRef.member.inj reference
  rcases refs with ⟨rfl, rfl⟩
  have sameConstant := Option.some.inj ((coherent owner constant present).symm.trans
    (coherent owner actualConstant actualPresent))
  subst actualConstant
  have sameRecursor := ReaderIndexEntries.member_unique constant position recursor actualRecursor member actualMember
  subst actualRecursor
  unfold candidate
  dsimp only
  split
  · rename_i existing
    have oldFound := Std.HashMap.getElem?_eq_some_getD_of_contains (fallback := entry) existing
    have role := from_role_unique store pins records coherent (.member owner position)
      (before.1.recs.getD (.member owner position) entry) entry
      (provenance _ _ oldFound) origin
    refine ⟨.member owner position, ?_⟩
    simpa only [role.1, role.2] using backed _ _ oldFound
  · simp only [analysed, carrier, stored, kind, firstFound, guarded, ↓reduceIte]
    split
    · rename_i duplicate
      obtain ⟨pair, inPairs, same⟩ := Array.any_eq_true'.mp duplicate
      have same : pair.1 = entry.motive := beq_iff_eq.mp same
      have pairEq : pair = (entry.motive, pair.2) := Prod.ext same rfl
      exact ⟨pair.2, by rw [← pairEq]; exact inPairs⟩
    · split <;> exact ⟨.member owner position, by simp⟩

private theorem list_hit (P Q : β → Prop) (items : List α) (target : α) (present : target ∈ items)
    (body : α → β → Id (ForInStep β)) (initial : β) (start : P initial)
    (step : ∀ item ∈ items, ∀ before, P before → ∃ after, body item before = .yield after ∧
      P after ∧ (Q before → Q after) ∧ (item = target → Q after)) :
    Q (forIn items initial body : Id β) := by
  induction items generalizing initial with
  | nil => simp at present
  | cons item rest ih =>
    obtain ⟨after, ran, valid, growth, hit⟩ := step item (by simp) initial start
    have restStep : ∀ item ∈ rest, ∀ before, P before → ∃ after, body item before = .yield after ∧
        P after ∧ (Q before → Q after) ∧ (item = target → Q after) :=
      fun item member before good => step item (by simp [member]) before good
    have result : Q (forIn rest after body : Id β) := by
      rcases List.mem_cons.mp present with same | later
      · have keep := CanonUnivMeaning.listLoop_preserves (fun state => P state ∧ Q state) rest after body
          ⟨valid, hit same.symm⟩ (by
            intro item member before good
            obtain ⟨after, ran, valid, growth, _⟩ := restStep item member before good.1
            simpa only [ran, StepHolds] using And.intro valid (growth good.2))
        exact keep.2
      · exact ih later after valid restStep
    simpa only [List.forIn_cons, ran, pure, bind] using result

private theorem array_hit (P Q : β → Prop) (items : Array α) (target : α) (present : target ∈ items)
    (body : α → β → Id (ForInStep β)) (initial : β) (start : P initial)
    (step : ∀ item ∈ items, ∀ before, P before → ∃ after, body item before = .yield after ∧
      P after ∧ (Q before → Q after) ∧ (item = target → Q after)) :
    Q (forIn items initial body : Id β) := by
  rw [← Array.forIn_toList]
  exact list_hit P Q items.toList target (Array.mem_toList_iff.mpr present) body initial start
    (fun item member before good => step item (Array.mem_toList_iff.mp member) before good)

def Valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (state : BuildState) : Prop :=
  ReaderIndexEntries.Valid store pins records state ∧ Backed state

theorem valid_empty (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) : Valid store pins records ({}, {}) := by
  refine ⟨ReaderIndexEntries.valid_empty store pins records, ?_⟩
  intro ref entry stored
  simp at stored

theorem candidate_next (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (record : Address × Ixon.Constant) (present : record ∈ records)
    (member : Nat × Ixon.Recursor) (memberPresent : member ∈ recursorMembers record.2)
    (before : BuildState) (valid : Valid store pins records before) :
    ∃ after, candidate store pins record.1 record.2 member before = .yield after ∧
      Valid store pins records after ∧ FoundExtend before.2 after.2 := by
  obtain ⟨after, ran, _, growth, backed⟩ := candidate_transition store pins record.1 record.2 member before
  have entries := ReaderIndexEntries.candidate_valid store pins records record.1 record.2
    present member memberPresent before valid.1
  exact ⟨after, ran, ⟨by simpa only [ran, StepHolds] using entries, backed valid.2⟩, growth⟩

theorem record_next (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (record : Address × Ixon.Constant) (present : record ∈ records)
    (before : BuildState) (valid : Valid store pins records before) :
    ∃ after, recordStep store pins record before = .yield after ∧
      Valid store pins records after ∧ FoundExtend before.2 after.2 := by
  refine ⟨_, rfl, ?_⟩
  apply CanonUnivEmit.arrayLoop_preserves
    (fun state => Valid store pins records state ∧ FoundExtend before.2 state.2)
    (recursorMembers record.2) before (candidate store pins record.1 record.2)
    ⟨valid, fun _ _ h => h⟩
  intro member memberPresent state good
  obtain ⟨after, ran, valid, growth⟩ := candidate_next store pins records record present member memberPresent state good.1
  simpa only [ran, StepHolds] using And.intro valid
    (show FoundExtend before.2 after.2 from fun block pair h => growth block pair (good.2 block pair h))

theorem record_covers (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (record : Address × Ixon.Constant) (present : record ∈ records)
    (position : Nat) (recursor : Ixon.Recursor) (member : (position, recursor) ∈ recursorMembers record.2)
    (entry : RecEntry) (eligible : From store pins records (.member record.1 position) entry)
    (before : BuildState) (valid : Valid store pins records before) :
    StepHolds (Covered entry.block entry.motive) (recordStep store pins record before) := by
  apply array_hit (Valid store pins records) (Covered entry.block entry.motive)
    (recursorMembers record.2) (position, recursor) member
    (candidate store pins record.1 record.2) before valid
  intro item itemPresent state good
  obtain ⟨after, ran, valid, growth⟩ := candidate_next store pins records record present item itemPresent state good
  refine ⟨after, ran, valid, covered_extends state.2 after.2 growth entry.block entry.motive state.1 after.1, ?_⟩
  intro same
  subst item
  have hit := candidate_covers store pins records coherent record.1 record.2 position recursor
    present member entry eligible state good.1.1 good.2
  simpa only [ran, StepHolds] using hit

/-- Traversing the actual supplied record and member arrays discovers a
representative of every eligible block/motive, without requiring fresh keys. -/
theorem collect_covers (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (ref : ConstRef Address) (entry : RecEntry) (eligible : From store pins records ref entry) :
    Covered entry.block entry.motive (forIn (m := Id) records ({}, {}) (recordStep store pins)) := by
  have origin := eligible
  obtain ⟨owner, constant, position, recursor, carriers, firstIndex, blockConstant, members,
    firstSlot, firstInd, reference, present, member, _⟩ := eligible
  subst ref
  apply array_hit (Valid store pins records) (Covered entry.block entry.motive)
    records (owner, constant) present (recordStep store pins) ({}, {}) (valid_empty store pins records)
  intro record recordPresent state good
  obtain ⟨after, ran, valid, growth⟩ := record_next store pins records record recordPresent state good
  refine ⟨after, ran, valid, covered_extends state.2 after.2 growth entry.block entry.motive state.1 after.1, ?_⟩
  intro same
  subst record
  have hit := record_covers store pins records coherent (owner, constant) present position recursor member entry origin state good
  simpa only [ran, StepHolds] using hit

def GroupContains (block : Address) (ref : ConstRef Address) (index : RecIndex) : Prop :=
  ∃ shape, index.blocks[block]? = some shape ∧ ref ∈ shape.recs

theorem complete_pair (block : Address) (pairs : Array (Nat × ConstRef Address))
    (pair : Nat × ConstRef Address) (present : pair ∈ pairs) (index : RecIndex) :
    StepHolds (GroupContains block pair.2) (completeStep (block, pairs) index) := by
  refine ⟨{ index.blocks.getD block default with recs := (pairs.qsort (fun left right => left.1 < right.1)).map (·.2) },
    by simp, ?_⟩
  exact Array.mem_map.mpr ⟨pair, Canon.mem_qsort.mpr present, rfl⟩

theorem complete_preserves (found : Found) (block : Address) (pairs : Array (Nat × ConstRef Address))
    (stored : found[block]? = some pairs) (pair : Nat × ConstRef Address) (present : pair ∈ pairs)
    (item : Address × Array (Nat × ConstRef Address)) (itemPresent : item ∈ found.toList)
    (index : RecIndex) (already : GroupContains block pair.2 index) :
    StepHolds (GroupContains block pair.2) (completeStep item index) := by
  have itemStored := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp itemPresent
  rcases item with ⟨owner, values⟩
  by_cases same : owner == block
  · have equal := beq_iff_eq.mp same
    subst owner
    have valuesEq : values = pairs := Option.some.inj (itemStored.symm.trans stored)
    subst values
    exact complete_pair block pairs pair present index
  · obtain ⟨shape, shapeFound, inShape⟩ := already
    refine ⟨shape, ?_, inShape⟩
    change (index.blocks.insert owner _)[block]? = some shape
    rw [Std.HashMap.getElem?_insert]
    simp only [same, Bool.false_eq_true, ↓reduceIte]
    exact shapeFound

/-- Sorting and finalizing every discovered group retains each discovered
reference in the block shape consumed by `readInductive`. -/
theorem complete_covers (found : Found) (block : Address) (pairs : Array (Nat × ConstRef Address))
    (stored : found[block]? = some pairs) (pair : Nat × ConstRef Address) (present : pair ∈ pairs)
    (index : RecIndex) :
    GroupContains block pair.2 (forIn (m := Id) found.toList index completeStep) := by
  apply list_hit (fun _ => True) (GroupContains block pair.2) found.toList (block, pairs)
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr stored) completeStep index trivial
  intro item itemPresent before _
  refine ⟨_, rfl, trivial, ?_, ?_⟩
  · exact complete_preserves found block pairs stored pair present item itemPresent before
  · intro same
    subst item
    exact complete_pair block pairs pair present before

theorem complete_recs (found : Found) (index : RecIndex) :
    (forIn (m := Id) found.toList index completeStep).recs = index.recs := by
  apply CanonUnivMeaning.listLoop_preserves (fun next => next.recs = index.recs)
    found.toList index completeStep rfl
  intro item _ before same
  exact same

/-- Completeness is per block/motive: an eligible reference may lose to an
earlier candidate, but its motive still has an indexed and grouped member. -/
theorem buildIndex_covers (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (ref : ConstRef Address) (entry : RecEntry) (eligible : From store pins records ref entry) :
    ∃ selected chosen shape,
      (buildIndex store pins records).recs[selected]? = some chosen ∧
      chosen.block = entry.block ∧ chosen.motive = entry.motive ∧
      (buildIndex store pins records).blocks[entry.block]? = some shape ∧ selected ∈ shape.recs ∧
      From store pins records selected chosen := by
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store pins)
  obtain ⟨selected, inFound⟩ := collect_covers store pins records coherent ref entry eligible
  change (entry.motive, selected) ∈ collected.2.getD entry.block #[] at inFound
  have valid := ReaderIndexEntries.collect_valid store pins records
  obtain ⟨chosen, chosenFound, owner, motive⟩ := ReaderIndexEntries.found_getD collected valid.2.1
    entry.block (entry.motive, selected) inFound
  have afterFound : (ReaderIndex.run store pins records).recs[selected]? = some chosen := by
    unfold ReaderIndex.run
    rw [complete_recs]
    exact chosenFound
  have origin := valid.1 selected chosen chosenFound
  have completed : GroupContains entry.block selected (ReaderIndex.run store pins records) := by
    rw [Std.HashMap.getD_eq_getD_getElem?] at inFound
    cases stored : collected.2[entry.block]? with
    | none => simp [stored] at inFound
    | some pairs =>
      simp only [stored, Option.getD_some] at inFound
      exact complete_covers collected.2 entry.block pairs stored (entry.motive, selected) inFound collected.1
  obtain ⟨shape, shapeFound, member⟩ := completed
  rw [ReaderIndex.run_eq] at afterFound shapeFound
  exact ⟨selected, chosen, shape, afterFound, owner, motive, shapeFound, member, origin⟩

/-- If the source-side family proves that only one eligible reference has a
given role, discovery retains that exact reference. No uniqueness assumption
is needed for the general motive-coverage result above. -/
theorem buildIndex_unique_reference (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (coherent : Coherent store records)
    (ref : ConstRef Address) (entry : RecEntry) (eligible : From store pins records ref entry)
    (unique : ∀ other chosen, From store pins records other chosen →
      chosen.block = entry.block → chosen.motive = entry.motive → other = ref) :
    ∃ chosen shape, (buildIndex store pins records).recs[ref]? = some chosen ∧
      chosen.block = entry.block ∧ chosen.motive = entry.motive ∧
      (buildIndex store pins records).blocks[entry.block]? = some shape ∧ ref ∈ shape.recs := by
  obtain ⟨selected, chosen, shape, stored, owner, motive, shapeFound, member, origin⟩ :=
    buildIndex_covers store pins records coherent ref entry eligible
  have same := unique selected chosen origin owner motive
  subst selected
  exact ⟨chosen, shape, stored, owner, motive, shapeFound, member⟩

def OnePerMotive (found : Found) : Prop :=
  ∀ (block : Address) (left right : Nat × ConstRef Address),
    left ∈ found.getD block #[] → right ∈ found.getD block #[] → left.1 = right.1 → left.2 = right.2

theorem one_push (found : Found) (block : Address) (pair : Nat × ConstRef Address)
    (unique : OnePerMotive found) (fresh : (found.getD block #[]).any (·.1 == pair.1) = false) :
    OnePerMotive (found.insert block ((found.getD block #[]).push pair)) := by
  intro query left right leftPresent rightPresent sameMotive
  by_cases same : block == query
  · have equal := beq_iff_eq.mp same
    subst query
    simp only [Std.HashMap.getD_insert_self] at leftPresent rightPresent
    rcases Array.mem_push.mp leftPresent with leftOld | leftNew
    · rcases Array.mem_push.mp rightPresent with rightOld | rightNew
      · exact unique block left right leftOld rightOld sameMotive
      · subst right
        have detected : (found.getD block #[]).any (·.1 == pair.1) = true :=
          Array.any_eq_true'.mpr ⟨left, leftOld, beq_iff_eq.mpr sameMotive⟩
        rw [fresh] at detected
        cases detected
    · subst left
      rcases Array.mem_push.mp rightPresent with rightOld | rightNew
      · have detected : (found.getD block #[]).any (·.1 == pair.1) = true :=
          Array.any_eq_true'.mpr ⟨right, rightOld, beq_iff_eq.mpr sameMotive.symm⟩
        rw [fresh] at detected
        cases detected
      · subst right; rfl
  · simp only [Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_insert,
      same, Bool.false_eq_true, ↓reduceIte] at leftPresent rightPresent
    exact unique query left right
      (by simpa only [Std.HashMap.getD_eq_getD_getElem?] using leftPresent)
      (by simpa only [Std.HashMap.getD_eq_getD_getElem?] using rightPresent) sameMotive

theorem candidate_unique (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (owner : Address) (constant : Ixon.Constant) (member : Nat × Ixon.Recursor)
    (before : BuildState) (unique : OnePerMotive before.2) :
    StepHolds (fun after => OnePerMotive after.2) (candidate store pins owner constant member before) := by
  rcases member with ⟨position, recursor⟩
  unfold candidate
  dsimp only
  split
  · exact unique
  · split
    · split
      · split
        · split
          · split
            · split
              · split
                · exact unique
                · rename_i fresh
                  have absent := Bool.eq_false_iff.mpr fresh
                  split <;> exact one_push before.2 _ _ unique absent
              · exact unique
            · exact unique
          · exact unique
        · exact unique
      · exact unique
    · exact unique

theorem collect_unique (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) :
    OnePerMotive (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store pins)).2 := by
  apply CanonUnivEmit.arrayLoop_preserves (fun state => OnePerMotive state.2) records ({}, {})
    (recordStep store pins)
  · intro block left right present; simp at present
  · intro record _ before unique
    apply CanonUnivEmit.arrayLoop_preserves (fun state => OnePerMotive state.2)
      (recursorMembers record.2) before (candidate store pins record.1 record.2) unique
    intro member _ state good
    exact candidate_unique store pins record.1 record.2 member state good

theorem collect_backed (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) :
    Backed (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store pins)) := by
  have valid := CanonUnivEmit.arrayLoop_preserves (Valid store pins records) records
    (({} : RecIndex), ({} : Found)) (recordStep store pins) (valid_empty store pins records) (by
      intro record present before good
      obtain ⟨after, ran, valid, _⟩ := record_next store pins records record present before good
      simpa only [ran, StepHolds] using valid)
  exact valid.2

/-- The final recursor map contains at most one reference for each block and
motive, as enforced by the actual first-per-motive guard. -/
theorem buildIndex_role_unique (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (left right : ConstRef Address) (first second : RecEntry)
    (leftFound : (buildIndex store pins records).recs[left]? = some first)
    (rightFound : (buildIndex store pins records).recs[right]? = some second)
    (sameBlock : first.block = second.block) (sameMotive : first.motive = second.motive) : left = right := by
  rw [← ReaderIndex.run_eq] at leftFound rightFound
  unfold ReaderIndex.run at leftFound rightFound
  rw [complete_recs] at leftFound rightFound
  have backed := collect_backed store pins records
  have leftPair := backed left first leftFound
  have rightPair := backed right second rightFound
  rw [sameBlock] at leftPair
  exact collect_unique store pins records second.block (first.motive, left) (second.motive, right)
    leftPair rightPair sameMotive

/-- The production stream context supplies coherence through actual decoding
and the committed prelude. Only the candidate's concrete eligibility remains. -/
theorem stream_covers (environment : CompileEnv) (limits : Kernel.Admission.Limits)
    (constants : Kernel.Ingress.Constants)
    (decoded : Kernel.Admission.decodeRecords limits environment.constants.toList = .ok constants)
    (pins : Pins) (pre : Prelude) (preludeReady : builtinPrelude = .ok pre)
    (hint : ConstRef Address → Option Kernel.ReducibilityHint) (ref : ConstRef Address) (entry : RecEntry)
    (eligible : From (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).store
      pins.names (ReaderStore.allRecords constants.toArray pre.records) ref entry) :
    ∃ selected chosen shape,
      (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).index.recs[selected]? = some chosen ∧
      chosen.block = entry.block ∧ chosen.motive = entry.motive ∧
      (Kernel.Admission.streamContext pins pre constants environment.blobs.toList hint).index.blocks[entry.block]? = some shape ∧
      selected ∈ shape.recs := by
  obtain ⟨selected, chosen, shape, stored, owner, motive, shapeFound, member, _⟩ :=
    buildIndex_covers _ pins.names (ReaderStore.allRecords constants.toArray pre.records)
      (ReaderAdmissionRecords.stream_coherent environment limits constants decoded pins pre preludeReady hint) ref entry eligible
  exact ⟨selected, chosen, shape, stored, owner, motive, shapeFound, member⟩

open Ix.CompileCert.HeadWriterFrame in
/-- Public inductive compilation, checked publication, decoding and one
eligible recursor establish block discovery and singleton order together.
There is no assumed successful target read or pre-existing index entry. -/
theorem published_stream_order (before : DriverAcc) (lo : Name) (source : InductiveVal)
    (blockEnv : BlockEnv) (initial cache : BlockState) (output : BlockResult)
    (compiled : rawRun (compileConstantInfo (.inductInfo source)) (before.cenv, blockEnv) initial = (.ok output, cache))
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (codec : Sharing.Verify.BlockResultCodecWF output) (limits : Kernel.Admission.Limits)
    (constants : Kernel.Ingress.Constants)
    (decoded : Kernel.Admission.decodeRecords limits (mergeCompiledBlock before lo output cache).cenv.constants.toList = .ok constants)
    (pins : Pins) (pre : Prelude) (preludeReady : builtinPrelude = .ok pre)
    (hint : ConstRef Address → Option Kernel.ReducibilityHint) (ref : ConstRef Address) (entry : RecEntry)
    (eligible : From
      (Kernel.Admission.streamContext pins pre constants (mergeCompiledBlock before lo output cache).cenv.blobs.toList hint).store
      pins.names (ReaderStore.allRecords constants.toArray pre.records) ref entry)
    (owner : entry.block = output.blockAddr) :
    ∃ selected chosen shape,
      (Kernel.Admission.streamContext pins pre constants (mergeCompiledBlock before lo output cache).cenv.blobs.toList hint).index.recs[selected]? = some chosen ∧
      chosen.block = output.blockAddr ∧ chosen.motive = entry.motive ∧
      (Kernel.Admission.streamContext pins pre constants (mergeCompiledBlock before lo output cache).cenv.blobs.toList hint).index.blocks[output.blockAddr]? = some shape ∧
      selected ∈ shape.recs ∧ shape.order = #[0] := by
  obtain ⟨selected, chosen, shape, stored, block, motive, shapeFound, member⟩ :=
    stream_covers _ limits constants decoded pins pre preludeReady hint ref entry eligible
  rw [owner] at block shapeFound
  exact ⟨selected, chosen, shape, stored, block, motive, shapeFound, member,
    ReaderAdmissionRecords.published_stream_order before lo source blockEnv initial cache output compiled
      accepted codec limits constants decoded pins pre hint shape shapeFound⟩

end Ix.CompileCert.ReaderIndexDiscovery
