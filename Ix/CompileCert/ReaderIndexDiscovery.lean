import Ix.CompileCert.ReaderIndex

/-! # The reader's recursor index: coverage and one recursor per motive

The stream facts `stream_covers` and `published_stream_order` use admission's
store coherence and the compile driver's publication. Over records coherent
with the store:

* an eligible recursor (one whose analysis the builder would accept) gets
  its block and motive covered: some recursor indexed at that block and
  motive is in the block's shape (`buildIndex_covers`), the eligible one
  itself if no other eligible recursor has its role
  (`buildIndex_unique_reference`);
* the index holds at most one recursor per block and motive
  (`buildIndex_role_unique`). -/

namespace Ix.CompileCert.ReaderIndexDiscovery

open Ix.Kernel.Reader (Store RecIndex RecEntry BlockShape recursorMembers analyseRecursor buildIndex)
open Ix.Kernel (ConstRef)
open Ix.CompileCert.CanonUnivMeaning (StepHolds)
open Ix.CompileCert.ReaderIndex (Found BuildState candidate recordStep completeStep inductives orderFor orderValid
  From Coherent Provenance RecsExtend added Step candidate_step)

/-- Coherent scanned records give each indexed reference one block and
motive. -/
theorem from_role_unique (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (ref : ConstRef Address) (left right : RecEntry)
    (first : From store records ref left) (second : From store records ref right) :
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
  have sameRecursor := ReaderIndex.member_unique constant position recursor recursor' member member'
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

/-- Every indexed entry is discovered at its block and motive. -/
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

theorem added_recs (owner : Address) (member : Nat × Ixon.Recursor) (before : BuildState) (motive : Nat)
    (major : ConstRef Address) (block : Address) (order : Array Nat) (first : Ixon.Inductive) :
    (added owner member before motive major block order first).1.recs =
      before.1.recs.insert (.member owner member.1)
        ⟨block, motive, major, member.2.lvls.toNat == first.lvls.toNat + 1⟩ := by
  unfold added
  dsimp only
  split <;> rfl

theorem added_found (owner : Address) (member : Nat × Ixon.Recursor) (before : BuildState) (motive : Nat)
    (major : ConstRef Address) (block : Address) (order : Array Nat) (first : Ixon.Inductive) :
    (added owner member before motive major block order first).2 =
      before.2.insert block ((before.2.getD block #[]).push (motive, .member owner member.1)) := by
  unfold added
  dsimp only
  split <;> rfl

theorem backed_added (owner : Address) (member : Nat × Ixon.Recursor) (before : BuildState) (motive : Nat)
    (major : ConstRef Address) (block : Address) (order : Array Nat) (first : Ixon.Inductive)
    (backed : Backed before) : Backed (added owner member before motive major block order first) := by
  intro query value stored
  rw [added_recs] at stored
  rw [added_found]
  rw [Std.HashMap.getElem?_insert] at stored
  split at stored
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst query
    cases Option.some.inj stored
    simp
  · exact found_push_extends before.2 block (motive, .member owner member.1) value.block (value.motive, query)
      (backed query value stored)

/-- Every candidate step yields, preserves old recursor entries and
discovered pairs, and keeps every entry backed by its discovered pair. -/
theorem candidate_transition (store : Store) (owner : Address) (constant : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (before : BuildState) :
    ∃ after, candidate store owner constant member before = .yield after ∧
      RecsExtend before.1 after.1 ∧ FoundExtend before.2 after.2 ∧ (Backed before → Backed after) := by
  obtain ⟨after, ran, step⟩ := candidate_step store owner constant member before
  refine ⟨after, ran, ?_⟩
  cases step with
  | keep => exact ⟨fun _ _ h => h, fun _ _ h => h, id⟩
  | add motive carriers major block firstIndex blockRecord members slot first fresh =>
    refine ⟨?_, ?_, backed_added owner member before motive major block _ first⟩
    · intro query old found
      rw [added_recs]
      exact ReaderIndex.recs_insert_extends before.1 _ _ fresh query old found
    · rw [added_found]
      exact found_push_extends before.2 _ _

theorem covered_extends (before after : Found) (growth : FoundExtend before after)
    (block : Address) (motive : Nat) (index first : RecIndex)
    (covered : Covered block motive (index, before)) : Covered block motive (first, after) := by
  obtain ⟨ref, present⟩ := covered
  exact ⟨ref, growth block (motive, ref) present⟩

/-- An eligible candidate either contributes its motive, finds that motive
already represented, or reuses its own coherently indexed reference. -/
theorem candidate_covers (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (owner : Address) (constant : Ixon.Constant) (position : Nat)
    (recursor : Ixon.Recursor) (present : (owner, constant) ∈ records)
    (member : (position, recursor) ∈ recursorMembers constant)
    (entry : RecEntry) (eligible : From store records (.member owner position) entry)
    (before : BuildState) (provenance : Provenance store records before.1) (backed : Backed before) :
    StepHolds (Covered entry.block entry.motive) (candidate store owner constant (position, recursor) before) := by
  have origin := eligible
  obtain ⟨actualOwner, actualConstant, actualPosition, actualRecursor, carriers, firstIndex, blockConstant,
    members, firstSlot, firstInd, reference, actualPresent, actualMember, analysed, carrier,
    stored, kind, firstFound, guarded, _⟩ := eligible
  have refs := ConstRef.member.inj reference
  rcases refs with ⟨rfl, rfl⟩
  have sameConstant := Option.some.inj ((coherent owner constant present).symm.trans
    (coherent owner actualConstant actualPresent))
  subst actualConstant
  have sameRecursor := ReaderIndex.member_unique constant position recursor actualRecursor member actualMember
  subst actualRecursor
  rcases before with ⟨idx, found⟩
  unfold candidate
  dsimp only
  split
  · rename_i existing
    have oldFound := Std.HashMap.getElem?_eq_some_getD_of_contains (fallback := entry) existing
    have role := from_role_unique store records coherent (.member owner position)
      (idx.recs.getD (.member owner position) entry) entry (provenance _ _ oldFound) origin
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

def Valid (store : Store) (records : Array (Address × Ixon.Constant)) (state : BuildState) : Prop :=
  ReaderIndex.Origins store records state ∧ Backed state

theorem valid_empty (store : Store) (records : Array (Address × Ixon.Constant)) :
    Valid store records ({}, {}) := by
  refine ⟨ReaderIndex.origins_empty store records, ?_⟩
  intro ref entry stored
  simp at stored

theorem candidate_next (store : Store) (records : Array (Address × Ixon.Constant))
    (record : Address × Ixon.Constant) (present : record ∈ records)
    (member : Nat × Ixon.Recursor) (memberPresent : member ∈ recursorMembers record.2)
    (before : BuildState) (valid : Valid store records before) :
    ∃ after, candidate store record.1 record.2 member before = .yield after ∧
      Valid store records after ∧ FoundExtend before.2 after.2 := by
  obtain ⟨after, ran, _, growth, backed⟩ := candidate_transition store record.1 record.2 member before
  have origins := ReaderIndex.candidate_origins store records record.1 record.2
    present member memberPresent before valid.1
  exact ⟨after, ran, ⟨by simpa only [ran, StepHolds] using origins, backed valid.2⟩, growth⟩

theorem record_next (store : Store) (records : Array (Address × Ixon.Constant))
    (record : Address × Ixon.Constant) (present : record ∈ records)
    (before : BuildState) (valid : Valid store records before) :
    ∃ after, recordStep store record before = .yield after ∧
      Valid store records after ∧ FoundExtend before.2 after.2 := by
  refine ⟨_, rfl, ?_⟩
  apply CanonUnivEmit.arrayLoop_preserves
    (fun state => Valid store records state ∧ FoundExtend before.2 state.2)
    (recursorMembers record.2) before (candidate store record.1 record.2)
    ⟨valid, fun _ _ h => h⟩
  intro member memberPresent state good
  obtain ⟨after, ran, valid, growth⟩ :=
    candidate_next store records record present member memberPresent state good.1
  simpa only [ran, StepHolds] using And.intro valid
    (show FoundExtend before.2 after.2 from fun block pair h => growth block pair (good.2 block pair h))

theorem record_covers (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (record : Address × Ixon.Constant) (present : record ∈ records)
    (position : Nat) (recursor : Ixon.Recursor) (member : (position, recursor) ∈ recursorMembers record.2)
    (entry : RecEntry) (eligible : From store records (.member record.1 position) entry)
    (before : BuildState) (valid : Valid store records before) :
    StepHolds (Covered entry.block entry.motive) (recordStep store record before) := by
  apply array_hit (Valid store records) (Covered entry.block entry.motive)
    (recursorMembers record.2) (position, recursor) member
    (candidate store record.1 record.2) before valid
  intro item itemPresent state good
  obtain ⟨after, ran, valid, growth⟩ := candidate_next store records record present item itemPresent state good
  refine ⟨after, ran, valid, covered_extends state.2 after.2 growth entry.block entry.motive state.1 after.1, ?_⟩
  intro same
  subst item
  have hit := candidate_covers store records coherent record.1 record.2 position recursor
    present member entry eligible state good.1.1 good.2
  simpa only [ran, StepHolds] using hit

/-- Traversing the supplied records discovers a representative of every
eligible block and motive, without requiring fresh keys. -/
theorem collect_covers (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (ref : ConstRef Address) (entry : RecEntry)
    (eligible : From store records ref entry) :
    Covered entry.block entry.motive (forIn (m := Id) records ({}, {}) (recordStep store)) := by
  have origin := eligible
  obtain ⟨owner, constant, position, recursor, carriers, firstIndex, blockConstant, members,
    firstSlot, firstInd, reference, present, member, _⟩ := eligible
  subst ref
  apply array_hit (Valid store records) (Covered entry.block entry.motive)
    records (owner, constant) present (recordStep store) ({}, {}) (valid_empty store records)
  intro record recordPresent state good
  obtain ⟨after, ran, valid, growth⟩ := record_next store records record recordPresent state good
  refine ⟨after, ran, valid, covered_extends state.2 after.2 growth entry.block entry.motive state.1 after.1, ?_⟩
  intro same
  subst record
  have hit := record_covers store records coherent (owner, constant) present position recursor member entry
    origin state good
  simpa only [ran, StepHolds] using hit

def GroupContains (block : Address) (ref : ConstRef Address) (index : RecIndex) : Prop :=
  ∃ shape, index.blocks[block]? = some shape ∧ ref ∈ shape.recs

theorem complete_pair (block : Address) (pairs : Array (Nat × ConstRef Address))
    (pair : Nat × ConstRef Address) (present : pair ∈ pairs) (index : RecIndex) :
    StepHolds (GroupContains block pair.2) (completeStep (block, pairs) index) := by
  refine ⟨{ index.blocks.getD block default with
    recs := (pairs.qsort (fun left right => left.1 < right.1)).map (·.2) }, by simp, ?_⟩
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

/-- Sorting every discovered group keeps each discovered reference in the
block shape `readInductive` reads. -/
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

/-- **Coverage is per block and motive**: an eligible recursor may lose to
an earlier candidate, but its motive still has an indexed recursor in the
block's shape. -/
theorem buildIndex_covers (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (ref : ConstRef Address) (entry : RecEntry)
    (eligible : From store records ref entry) :
    ∃ selected chosen shape,
      (buildIndex store records).recs[selected]? = some chosen ∧
      chosen.block = entry.block ∧ chosen.motive = entry.motive ∧
      (buildIndex store records).blocks[entry.block]? = some shape ∧ selected ∈ shape.recs ∧
      From store records selected chosen := by
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  obtain ⟨selected, inFound⟩ := collect_covers store records coherent ref entry eligible
  change (entry.motive, selected) ∈ collected.2.getD entry.block #[] at inFound
  have valid := ReaderIndex.collect_origins store records
  obtain ⟨chosen, chosenFound, owner, motive⟩ := ReaderIndex.found_getD collected valid.2.1
    entry.block (entry.motive, selected) inFound
  have afterFound : (ReaderIndex.run store records).recs[selected]? = some chosen := by
    unfold ReaderIndex.run
    rw [complete_recs]
    exact chosenFound
  have origin := valid.1 selected chosen chosenFound
  have completed : GroupContains entry.block selected (ReaderIndex.run store records) := by
    rw [Std.HashMap.getD_eq_getD_getElem?] at inFound
    cases stored : collected.2[entry.block]? with
    | none => simp [stored] at inFound
    | some pairs =>
      simp only [stored, Option.getD_some] at inFound
      exact complete_covers collected.2 entry.block pairs stored (entry.motive, selected) inFound collected.1
  obtain ⟨shape, shapeFound, member⟩ := completed
  rw [ReaderIndex.run_eq] at afterFound shapeFound
  exact ⟨selected, chosen, shape, afterFound, owner, motive, shapeFound, member, origin⟩

/-- If only one eligible reference has a given role, discovery indexes that
exact reference. -/
theorem buildIndex_unique_reference (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (ref : ConstRef Address) (entry : RecEntry)
    (eligible : From store records ref entry)
    (unique : ∀ other chosen, From store records other chosen →
      chosen.block = entry.block → chosen.motive = entry.motive → other = ref) :
    ∃ chosen shape, (buildIndex store records).recs[ref]? = some chosen ∧
      chosen.block = entry.block ∧ chosen.motive = entry.motive ∧
      (buildIndex store records).blocks[entry.block]? = some shape ∧ ref ∈ shape.recs := by
  obtain ⟨selected, chosen, shape, stored, owner, motive, shapeFound, member, origin⟩ :=
    buildIndex_covers store records coherent ref entry eligible
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

theorem candidate_unique (store : Store) (owner : Address) (constant : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (before : BuildState) (unique : OnePerMotive before.2) :
    StepHolds (fun after => OnePerMotive after.2) (candidate store owner constant member before) := by
  obtain ⟨after, ran, step⟩ := candidate_step store owner constant member before
  rw [ran]
  cases step with
  | keep => exact unique
  | add motive carriers major block firstIndex blockRecord members slot first _ _ _ _ _ _ _ unused =>
    change OnePerMotive (added owner member before motive major block _ first).2
    rw [added_found]
    exact one_push before.2 block (motive, .member owner member.1) unique unused

theorem collect_unique (store : Store) (records : Array (Address × Ixon.Constant)) :
    OnePerMotive (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)).2 := by
  apply CanonUnivEmit.arrayLoop_preserves (fun state => OnePerMotive state.2) records ({}, {})
    (recordStep store)
  · intro block left right present; simp at present
  · intro record _ before unique
    apply CanonUnivEmit.arrayLoop_preserves (fun state => OnePerMotive state.2)
      (recursorMembers record.2) before (candidate store record.1 record.2) unique
    intro member _ state good
    exact candidate_unique store record.1 record.2 member state good

theorem collect_backed (store : Store) (records : Array (Address × Ixon.Constant)) :
    Backed (forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)) := by
  have valid := CanonUnivEmit.arrayLoop_preserves (Valid store records) records
    (({} : RecIndex), ({} : Found)) (recordStep store) (valid_empty store records) (by
      intro record present before good
      obtain ⟨after, ran, valid, _⟩ := record_next store records record present before good
      simpa only [ran, StepHolds] using valid)
  exact valid.2

/-- **One recursor per block and motive**, as the builder's first-per-motive
guard enforces. -/
theorem buildIndex_role_unique (store : Store) (records : Array (Address × Ixon.Constant))
    (left right : ConstRef Address) (first second : RecEntry)
    (leftFound : (buildIndex store records).recs[left]? = some first)
    (rightFound : (buildIndex store records).recs[right]? = some second)
    (sameBlock : first.block = second.block) (sameMotive : first.motive = second.motive) : left = right := by
  rw [← ReaderIndex.run_eq] at leftFound rightFound
  unfold ReaderIndex.run at leftFound rightFound
  rw [complete_recs] at leftFound rightFound
  have backed := collect_backed store records
  have leftPair := backed left first leftFound
  have rightPair := backed right second rightFound
  rw [sameBlock] at leftPair
  exact collect_unique store records second.block (first.motive, left) (second.motive, right)
    leftPair rightPair sameMotive

end Ix.CompileCert.ReaderIndexDiscovery
