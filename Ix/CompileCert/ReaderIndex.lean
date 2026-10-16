import Ix.CompileCert.ProjectionLayout
import Ix.CompileCert.Canon.QSort

/-! # The reader's recursor index, phase by phase

The certified reader indexes the recursors of its records before reading
them (`Ix.Kernel.Reader.buildIndex`): each recursor is keyed by its own
record's member reference (SP3 D8: never after the type it eliminates), and
its analysis (`analyseRecursor`) names the block it eliminates, its motive
and its major premise's carrier; an inductive block's shape is its motive
order and its recursors in motive order. This module (CT-16's
`ReaderIndex` and `ReaderIndexEntries`, re-derived for D8: no pin names,
`RecEntry` without a name) states the builder as its two loops (`run`,
`run_eq`) and proves, for every record array:

* every indexed block shape's order is an order the analysis validated
  against the block's record (`buildIndex_shapes`), so a compiled
  standalone inductive family is indexed at member 0 exactly
  (`buildIndex_singleton_order`, `compiled_order`);
* every indexed recursor comes from a scanned record whose analysis gave
  its entry (`buildIndex_valid`'s provenance) and every recursor in a block
  shape is indexed at that block (grouping); with records coherent with
  the store, the reader's own lookups succeed (`entry_lookup`,
  `grouped_lookup`). -/

namespace Ix.CompileCert.ReaderIndex

open Ix.Kernel.Reader (Store RecIndex RecEntry BlockShape recursorMembers analyseRecursor buildIndex)
open Ix.Kernel (ConstRef)
open Ix.CompileCert.CanonUnivMeaning (StepHolds)

abbrev Found := Std.HashMap Address (Array (Nat × ConstRef Address))
abbrev BuildState := RecIndex × Found

/-! ## The builder's phases -/

def inductives (members : Array Ixon.MutConst) : Array (Nat × Ixon.Inductive) :=
  members.zipIdx.filterMap fun | (.indc ind, index) => some (index, ind) | _ => none

def orderFor (carriers : Array (ConstRef Address)) (owner : Address) (count : Nat) : Array Nat :=
  (carriers.extract 0 count).filterMap fun
    | .member block index => if block == owner then some index else none
    | .ctor .. => none

def orderValid (firstIndex : Nat) (indcs : Array (Nat × Ixon.Inductive)) (order : Array Nat) : Bool :=
  order.size == indcs.size && order[0]? == some firstIndex &&
    order.all (fun index => indcs.any (·.1 == index)) && order.toList.eraseDups.length == indcs.size

/-- One recursor member of one record: indexed under its own reference
when its analysis names a block whose inductives it orders, and its motive
is not yet taken there. -/
def candidate (store : Store) (owner : Address) (constant : Ixon.Constant) (member : Nat × Ixon.Recursor)
    (before : BuildState) : Id (ForInStep BuildState) := do
  let (position, recursor) := member
  let (idx, found) := before
  let ref : ConstRef Address := .member owner position
  if idx.recs.contains ref then return .yield (idx, found)
  let some ((motive, carriers, major) : Nat × Array (ConstRef Address) × ConstRef Address) :=
    analyseRecursor store owner constant recursor | return .yield (idx, found)
  let some (ConstRef.member block firstIndex) := (carriers[0]? : Option (ConstRef Address))
    | return .yield (idx, found)
  let some blockRecord := store block | return .yield (idx, found)
  let .muts members := blockRecord.info | return .yield (idx, found)
  let indcs := inductives members
  let some (_, first) := indcs[0]? | return .yield (idx, found)
  let order := orderFor carriers block indcs.size
  unless orderValid firstIndex indcs order do return .yield (idx, found)
  if (found.getD block #[]).any (·.1 == motive) then return .yield (idx, found)
  let large := recursor.lvls.toNat == first.lvls.toNat + 1
  let idx := { idx with recs := idx.recs.insert ref ⟨block, motive, major, large⟩ }
  let found := found.insert block ((found.getD block #[]).push (motive, ref))
  if idx.blocks.contains block then return .yield (idx, found)
  else return .yield ({ idx with blocks := idx.blocks.insert block ⟨order, #[]⟩ }, found)

def recordStep (store : Store) (record : Address × Ixon.Constant) (before : BuildState) :
    Id (ForInStep BuildState) :=
  .yield (forIn (m := Id) (recursorMembers record.2) before (candidate store record.1 record.2))

def completeStep (entry : Address × Array (Nat × ConstRef Address)) (idx : RecIndex) : Id (ForInStep RecIndex) :=
  let sorted := entry.2.qsort (fun left right => left.1 < right.1)
  let shape := idx.blocks.getD entry.1 default
  .yield { idx with blocks := idx.blocks.insert entry.1 { shape with recs := sorted.map (·.2) } }

/-- The builder as its two loops: index the candidates, then sort each
block's recursors by motive. -/
def run (store : Store) (records : Array (Address × Ixon.Constant)) : RecIndex :=
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  forIn (m := Id) collected.2.toList collected.1 completeStep

theorem run_eq (store : Store) (records : Array (Address × Ixon.Constant)) :
    run store records = buildIndex store records := rfl

/-! ## One candidate step -/

/-- The state after a candidate indexes `member` of the record at `owner`
for `block`'s `motive`. -/
def added (owner : Address) (member : Nat × Ixon.Recursor) (before : BuildState) (motive : Nat)
    (major : ConstRef Address) (block : Address) (order : Array Nat) (first : Ixon.Inductive) : BuildState :=
  let ref : ConstRef Address := .member owner member.1
  let idx : RecIndex :=
    { before.1 with
      recs := before.1.recs.insert ref ⟨block, motive, major, member.2.lvls.toNat == first.lvls.toNat + 1⟩ }
  let found := before.2.insert block ((before.2.getD block #[]).push (motive, ref))
  if idx.blocks.contains block then (idx, found)
  else ({ idx with blocks := idx.blocks.insert block ⟨order, #[]⟩ }, found)

/-- What a candidate step does: keep the state, or index an eligible
recursor under its own reference. -/
inductive Step (store : Store) (owner : Address) (constant : Ixon.Constant) (member : Nat × Ixon.Recursor)
    (before : BuildState) : BuildState → Prop
  | keep : Step store owner constant member before before
  | add (motive : Nat) (carriers : Array (ConstRef Address)) (major : ConstRef Address) (block : Address)
      (firstIndex : Nat) (blockRecord : Ixon.Constant) (members : Array Ixon.MutConst) (slot : Nat)
      (first : Ixon.Inductive)
      (fresh : before.1.recs.contains (.member owner member.1) = false)
      (analysed : analyseRecursor store owner constant member.2 = some (motive, carriers, major))
      (carrier : carriers[0]? = some (.member block firstIndex))
      (stored : store block = some blockRecord) (kind : blockRecord.info = .muts members)
      (firstFound : (inductives members)[0]? = some (slot, first))
      (guarded : orderValid firstIndex (inductives members) (orderFor carriers block (inductives members).size) = true)
      (unused : ((before.2.getD block #[]).any (·.1 == motive)) = false) :
      Step store owner constant member before
        (added owner member before motive major block (orderFor carriers block (inductives members).size) first)

/-- **The candidate step's inversion.** -/
theorem candidate_step (store : Store) (owner : Address) (constant : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (before : BuildState) :
    ∃ after, candidate store owner constant member before = .yield after ∧
      Step store owner constant member before after := by
  rcases member with ⟨position, recursor⟩
  rcases before with ⟨idx, found⟩
  unfold candidate
  dsimp only
  split
  · exact ⟨_, rfl, .keep⟩
  · split
    · split
      · split
        · split
          · split
            · split
              · split
                · exact ⟨_, rfl, .keep⟩
                · rename_i fresh _ motive carriers major analysed _ block firstIndex carrier _ blockRecord stored _
                    members kind _ slot first firstFound guarded unused
                  refine ⟨_, ?_, .add motive carriers major block firstIndex blockRecord members slot first
                    (by simpa using fresh) analysed carrier stored kind firstFound guarded (by simpa using unused)⟩
                  unfold added
                  dsimp only
                  by_cases contained : idx.blocks.contains block = true <;> simp only [contained, ↓reduceIte] <;> rfl
              · exact ⟨_, rfl, .keep⟩
            · exact ⟨_, rfl, .keep⟩
          · exact ⟨_, rfl, .keep⟩
        · exact ⟨_, rfl, .keep⟩
      · exact ⟨_, rfl, .keep⟩
    · exact ⟨_, rfl, .keep⟩

/-! ## Block shapes -/

/-- An order the analysis validated against the block's record. -/
def OrderFrom (store : Store) (owner : Address) (order : Array Nat) : Prop :=
  ∃ constant members firstIndex first,
    store owner = some constant ∧ constant.info = .muts members ∧
      (inductives members)[0]? = some (firstIndex, first) ∧
      ∃ initialIndex, orderValid initialIndex (inductives members) order = true

def Shapes (store : Store) (index : RecIndex) : Prop :=
  ∀ owner shape, index.blocks[owner]? = some shape → OrderFrom store owner shape.order

/-- Every block with discovered recursors has a shape. -/
def Supported (state : BuildState) : Prop :=
  ∀ (owner : Address) (entries : Array (Nat × ConstRef Address)),
    state.2[owner]? = some entries → ∃ shape, state.1.blocks[owner]? = some shape

def Valid (store : Store) (state : BuildState) : Prop := Shapes store state.1 ∧ Supported state

theorem valid_empty (store : Store) : Valid store ({}, {}) := by
  constructor
  · intro owner shape found; simp at found
  · intro owner entries found; simp at found

theorem shapes_insert (store : Store) (index : RecIndex) (owner : Address) (shape : BlockShape)
    (valid : Shapes store index) (newShape : OrderFrom store owner shape.order) :
    Shapes store { index with blocks := index.blocks.insert owner shape } := by
  intro query value found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst query
    cases Option.some.inj found
    exact newShape
  · exact valid query value found

theorem supported_insert_shape (index : RecIndex) (found : Found) (owner : Address) (shape : BlockShape)
    (valid : Supported (index, found)) :
    Supported ({ index with blocks := index.blocks.insert owner shape }, found) := by
  intro query entries present
  obtain ⟨old, oldFound⟩ := valid query entries present
  by_cases same : owner == query
  · have equal := beq_iff_eq.mp same
    subst query
    exact ⟨shape, by simp⟩
  · refine ⟨old, ?_⟩
    rw [Std.HashMap.getElem?_insert]
    simp only [same, Bool.false_eq_true, ↓reduceIte]
    exact oldFound

theorem added_valid (store : Store) (owner : Address) (member : Nat × Ixon.Recursor) (before : BuildState)
    (motive : Nat) (major : ConstRef Address) (block : Address) (order : Array Nat) (first : Ixon.Inductive)
    (valid : Valid store before) (newShape : OrderFrom store block order) :
    Valid store (added owner member before motive major block order first) := by
  unfold added
  dsimp only
  split
  · rename_i present
    refine ⟨valid.1, ?_⟩
    intro query values found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · rename_i same
      have equal := beq_iff_eq.mp same
      subst query
      exact ⟨_, Std.HashMap.getElem?_eq_some_getD_of_contains (fallback := default) present⟩
    · exact valid.2 query values found
  · refine ⟨shapes_insert store _ block ⟨order, #[]⟩ valid.1 newShape, ?_⟩
    intro query values found
    rw [Std.HashMap.getElem?_insert] at found
    by_cases same : block == query
    · have equal := beq_iff_eq.mp same
      subst query
      exact ⟨⟨order, #[]⟩, by simp⟩
    · simp only [same, Bool.false_eq_true, ↓reduceIte] at found
      obtain ⟨old, oldFound⟩ := valid.2 query values found
      refine ⟨old, ?_⟩
      change ((before.1.blocks).insert block _)[query]? = some old
      rw [Std.HashMap.getElem?_insert]
      simp only [same, Bool.false_eq_true, ↓reduceIte]
      exact oldFound

theorem candidate_valid (store : Store) (owner : Address) (constant : Ixon.Constant)
    (member : Nat × Ixon.Recursor) (before : BuildState) (valid : Valid store before) :
    StepHolds (Valid store) (candidate store owner constant member before) := by
  obtain ⟨after, ran, step⟩ := candidate_step store owner constant member before
  rw [ran]
  cases step with
  | keep => exact valid
  | add motive carriers major block firstIndex blockRecord members slot first _ _ _ stored kind firstFound
      guarded _ =>
    exact added_valid store owner member before motive major block _ first valid
      ⟨blockRecord, members, slot, first, stored, kind, firstFound, firstIndex, guarded⟩

theorem record_valid (store : Store) (record : Address × Ixon.Constant) (before : BuildState)
    (valid : Valid store before) : StepHolds (Valid store) (recordStep store record before) :=
  CanonUnivEmit.arrayLoop_preserves (Valid store) (recursorMembers record.2) before
    (candidate store record.1 record.2) valid
    (fun member _ state good => candidate_valid store record.1 record.2 member state good)

theorem collect_valid (store : Store) (records : Array (Address × Ixon.Constant)) :
    Valid store (forIn (m := Id) records ({}, {}) (recordStep store)) :=
  CanonUnivEmit.arrayLoop_preserves (Valid store) records ({}, {}) (recordStep store) (valid_empty store)
    (fun record _ state good => record_valid store record state good)

theorem complete_valid (store : Store) (found : Found)
    (entry : Address × Array (Nat × ConstRef Address)) (present : entry ∈ found.toList)
    (index : RecIndex) (valid : Valid store (index, found)) :
    StepHolds (fun next => Valid store (next, found)) (completeStep entry index) := by
  have foundEntry : found[entry.1]? = some entry.2 := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp present
  obtain ⟨shape, stored⟩ := valid.2 entry.1 entry.2 foundEntry
  have defaultEq : index.blocks.getD entry.1 default = shape := by
    rw [Std.HashMap.getD_eq_getD_getElem?, stored]
    rfl
  unfold completeStep
  dsimp only
  rw [defaultEq]
  exact ⟨shapes_insert store index entry.1 _ valid.1 (valid.1 entry.1 shape stored),
    supported_insert_shape index found entry.1 _ valid.2⟩

theorem run_shapes (store : Store) (records : Array (Address × Ixon.Constant)) :
    Shapes store (run store records) := by
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  have valid : Valid store collected := collect_valid store records
  have completed := CanonUnivMeaning.listLoop_preserves (fun index => Valid store (index, collected.2))
    collected.2.toList collected.1 completeStep valid
    (fun entry present index good => complete_valid store collected.2 entry present index good)
  exact completed.1

/-- **Every indexed block shape's order was validated against the block's
record.** -/
theorem buildIndex_shapes (store : Store) (records : Array (Address × Ixon.Constant)) :
    Shapes store (buildIndex store records) := by
  rw [← run_eq]
  exact run_shapes store records

theorem singleton_inductives (source : Ixon.Inductive) : inductives #[.indc source] = #[(0, source)] := by
  simp [inductives]

theorem array_one (values : Array α) (count : values.size = 1) : ∃ value, values = #[value] := by
  rcases values with ⟨values⟩
  cases values with
  | nil => simp at count
  | cons value rest =>
    cases rest with
    | nil => exact ⟨value, rfl⟩
    | cons _ _ => simp at count

theorem singleton_order (source : Ixon.Inductive) (order : Array Nat) (firstIndex : Nat)
    (valid : orderValid firstIndex #[(0, source)] order = true) : order = #[0] := by
  simp only [orderValid, Bool.and_eq_true] at valid
  have count : order.size = 1 := by simpa using valid.1.1.1
  obtain ⟨index, rfl⟩ := array_one order count
  have position : 0 = index := by simpa using valid.1.2
  rw [← position]

/-- **The index gives a standalone inductive family's block exactly member
0**: no reader-success or supplied-order premise. -/
theorem buildIndex_singleton_order (store : Store) (records : Array (Address × Ixon.Constant))
    (owner : Address) (constant : Ixon.Constant) (source : Ixon.Inductive) (shape : BlockShape)
    (stored : store owner = some constant) (kind : constant.info = .muts #[.indc source])
    (indexed : (buildIndex store records).blocks[owner]? = some shape) : shape.order = #[0] := by
  obtain ⟨actual, members, firstIndex, first, actualStored, actualKind, _, initialIndex, guarded⟩ :=
    buildIndex_shapes store records owner shape indexed
  have same : actual = constant := Option.some.inj (actualStored.symm.trans stored)
  subst actual
  have membersEq : members = #[.indc source] := Ixon.ConstantInfo.muts.inj (actualKind.symm.trans kind)
  subst members
  rw [singleton_inductives] at guarded
  exact singleton_order source shape.order initialIndex guarded

open Ix.CompileM in
/-- **Public dispatch of an inductive plus the index**: a compiled
standalone family stored at its address is indexed at member 0 exactly. -/
theorem compiled_order (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (source : InductiveVal) {before after : BlockState} {output : BlockResult}
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after))
    (store : Store) (records : Array (Address × Ixon.Constant)) (shape : BlockShape)
    (stored : store output.blockAddr = some output.block)
    (indexed : (buildIndex store records).blocks[output.blockAddr]? = some shape) : shape.order = #[0] := by
  obtain ⟨_, _, target, _, _, kind, _⟩ := ProjectionLayout.dispatch_layout context free source ran
  exact buildIndex_singleton_order store records output.blockAddr output.block target shape stored kind indexed

/-! ## Provenance and grouping -/

/-- An entry's provenance: a scanned record's recursor member whose
analysis gave the entry, against the block's record. -/
def From (store : Store) (records : Array (Address × Ixon.Constant)) (ref : ConstRef Address)
    (entry : RecEntry) : Prop :=
  ∃ owner constant position recursor carriers firstIndex blockConstant members firstSlot first,
    ref = .member owner position ∧ (owner, constant) ∈ records ∧
    (position, recursor) ∈ recursorMembers constant ∧
    analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) ∧
    carriers[0]? = some (.member entry.block firstIndex) ∧
    store entry.block = some blockConstant ∧ blockConstant.info = .muts members ∧
    (inductives members)[0]? = some (firstSlot, first) ∧
    orderValid firstIndex (inductives members) (orderFor carriers entry.block (inductives members).size) = true ∧
    entry.large = (recursor.lvls.toNat == first.lvls.toNat + 1)

def Provenance (store : Store) (records : Array (Address × Ixon.Constant)) (index : RecIndex) : Prop :=
  ∀ ref entry, index.recs[ref]? = some entry → From store records ref entry

/-- Every discovered pair is an indexed entry of its block and motive. -/
def FoundMatches (state : BuildState) : Prop :=
  ∀ (block : Address) (pairs : Array (Nat × ConstRef Address)), state.2[block]? = some pairs →
    ∀ pair ∈ pairs, ∃ entry, state.1.recs[pair.2]? = some entry ∧ entry.block = block ∧ entry.motive = pair.1

/-- Every recursor of a block shape is indexed at that block. -/
def Grouped (index : RecIndex) : Prop :=
  ∀ (block : Address) (shape : BlockShape), index.blocks[block]? = some shape → ∀ ref ∈ shape.recs,
    ∃ entry : RecEntry, index.recs[ref]? = some entry ∧ entry.block = block

def Origins (store : Store) (records : Array (Address × Ixon.Constant)) (state : BuildState) : Prop :=
  Provenance store records state.1 ∧ FoundMatches state ∧ Grouped state.1

def RecsExtend (before after : RecIndex) : Prop :=
  ∀ (ref : ConstRef Address) (entry : RecEntry), before.recs[ref]? = some entry → after.recs[ref]? = some entry

theorem recs_insert_extends (index : RecIndex) (ref : ConstRef Address) (entry : RecEntry)
    (fresh : index.recs.contains ref = false) :
    RecsExtend index { index with recs := index.recs.insert ref entry } := by
  intro query old found
  change (index.recs.insert ref entry)[query]? = some old
  rw [Std.HashMap.getElem?_insert]
  by_cases same : ref == query
  · have equal := beq_iff_eq.mp same
    subst query
    rw [Std.HashMap.contains_eq_isSome_getElem?, found] at fresh
    cases fresh
  · simp only [same, Bool.false_eq_true, ↓reduceIte]
    exact found

theorem provenance_insert (store : Store) (records : Array (Address × Ixon.Constant)) (index : RecIndex)
    (ref : ConstRef Address) (entry : RecEntry)
    (valid : Provenance store records index) (newEntry : From store records ref entry) :
    Provenance store records { index with recs := index.recs.insert ref entry } := by
  intro query value found
  change (index.recs.insert ref entry)[query]? = some value at found
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
  change (index.blocks.insert owner ⟨order, #[]⟩)[block]? = some shape at found
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
  change (before.2.insert entry.block _)[block]? = some pairs at found
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

theorem origins_empty (store : Store) (records : Array (Address × Ixon.Constant)) :
    Origins store records ({}, {}) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ref entry found; simp at found
  · intro block pairs found; simp at found
  · intro block shape found; simp at found

theorem added_origins (store : Store) (records : Array (Address × Ixon.Constant)) (owner : Address)
    (member : Nat × Ixon.Recursor) (before : BuildState) (motive : Nat) (major : ConstRef Address)
    (block : Address) (order : Array Nat) (first : Ixon.Inductive) (valid : Origins store records before)
    (fresh : before.1.recs.contains (.member owner member.1) = false)
    (newEntry : From store records (.member owner member.1)
      ⟨block, motive, major, member.2.lvls.toNat == first.lvls.toNat + 1⟩) :
    Origins store records (added owner member before motive major block order first) := by
  let entry : RecEntry := ⟨block, motive, major, member.2.lvls.toNat == first.lvls.toNat + 1⟩
  have growth := recs_insert_extends before.1 (.member owner member.1) entry fresh
  have inserted : ({ before.1 with recs := before.1.recs.insert (.member owner member.1) entry } : RecIndex).recs[
      (ConstRef.member owner member.1 : ConstRef Address)]? = some entry := by
    change (before.1.recs.insert _ entry)[_]? = some entry
    simp
  have updated : Origins store records
      ({ before.1 with recs := before.1.recs.insert (.member owner member.1) entry },
        before.2.insert block ((before.2.getD block #[]).push (motive, .member owner member.1))) :=
    ⟨provenance_insert store records before.1 _ entry valid.1 newEntry,
      found_insert before _ (.member owner member.1) entry valid.2.1 growth inserted,
      grouped_extends before.1 _ rfl growth valid.2.2⟩
  unfold added
  dsimp only
  split
  · exact updated
  · exact ⟨updated.1, updated.2.1, grouped_empty_insert _ block order updated.2.2⟩

theorem candidate_origins (store : Store) (records : Array (Address × Ixon.Constant)) (owner : Address)
    (constant : Ixon.Constant) (present : (owner, constant) ∈ records) (member : Nat × Ixon.Recursor)
    (memberPresent : member ∈ recursorMembers constant) (before : BuildState)
    (valid : Origins store records before) :
    StepHolds (Origins store records) (candidate store owner constant member before) := by
  obtain ⟨after, ran, step⟩ := candidate_step store owner constant member before
  rw [ran]
  cases step with
  | keep => exact valid
  | add motive carriers major block firstIndex blockRecord members slot first fresh analysed carrier stored
      kind firstFound guarded _ =>
    exact added_origins store records owner member before motive major block _ first valid fresh
      ⟨owner, constant, member.1, member.2, carriers, firstIndex, blockRecord, members, slot, first,
        rfl, present, memberPresent, analysed, carrier, stored, kind, firstFound, guarded, rfl⟩

theorem record_origins (store : Store) (records : Array (Address × Ixon.Constant))
    (record : Address × Ixon.Constant) (present : record ∈ records) (before : BuildState)
    (valid : Origins store records before) :
    StepHolds (Origins store records) (recordStep store record before) :=
  CanonUnivEmit.arrayLoop_preserves (Origins store records) (recursorMembers record.2) before
    (candidate store record.1 record.2) valid
    (fun member memberPresent state good =>
      candidate_origins store records record.1 record.2 present member memberPresent state good)

theorem collect_origins (store : Store) (records : Array (Address × Ixon.Constant)) :
    Origins store records (forIn (m := Id) records ({}, {}) (recordStep store)) :=
  CanonUnivEmit.arrayLoop_preserves (Origins store records) records ({}, {}) (recordStep store)
    (origins_empty store records)
    (fun record present state good => record_origins store records record present state good)

theorem complete_origins (store : Store) (records : Array (Address × Ixon.Constant)) (found : Found)
    (pair : Address × Array (Nat × ConstRef Address)) (present : pair ∈ found.toList)
    (index : RecIndex) (valid : Origins store records (index, found)) :
    StepHolds (fun next => Origins store records (next, found)) (completeStep pair index) := by
  have foundPair : found[pair.1]? = some pair.2 := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp present
  refine ⟨valid.1, valid.2.1, ?_⟩
  intro block shape stored ref inShape
  change (index.blocks.insert pair.1
    { index.blocks.getD pair.1 default with recs := (pair.2.qsort (fun a b => a.1 < b.1)).map (·.2) })[block]? =
      some shape at stored
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

/-- **Every indexed recursor has its provenance, and every recursor of a
block shape is indexed at that block.** -/
theorem buildIndex_valid (store : Store) (records : Array (Address × Ixon.Constant)) :
    Provenance store records (buildIndex store records) ∧ Grouped (buildIndex store records) := by
  rw [← run_eq]
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store)
  have valid : Origins store records collected := collect_origins store records
  have completed := CanonUnivMeaning.listLoop_preserves
    (fun index => Origins store records (index, collected.2)) collected.2.toList collected.1 completeStep valid
    (fun pair present index good => complete_origins store records collected.2 pair present index good)
  exact ⟨completed.1, completed.2.2⟩

/-! ## The reader's lookups -/

/-- The scanned records are the store's. -/
def Coherent (store : Store) (records : Array (Address × Ixon.Constant)) : Prop :=
  ∀ owner constant, (owner, constant) ∈ records → store owner = some constant

theorem entry_stored (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (ref : ConstRef Address) (entry : RecEntry)
    (found : (buildIndex store records).recs[ref]? = some entry) :
    ∃ owner constant position recursor carriers,
      ref = .member owner position ∧ store owner = some constant ∧
      (position, recursor) ∈ recursorMembers constant ∧
      analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) := by
  obtain ⟨owner, constant, position, recursor, carriers, _, _, _, _, _, reference, present, member, analysed, _⟩ :=
    (buildIndex_valid store records).1 ref entry found
  exact ⟨owner, constant, position, recursor, carriers, reference, coherent owner constant present, member, analysed⟩

/-- Every recursor reference placed in a block shape is indexed at that
block and keeps its scanned origin. -/
theorem grouped_entry (store : Store) (records : Array (Address × Ixon.Constant)) (block : Address)
    (shape : BlockShape) (shapeFound : (buildIndex store records).blocks[block]? = some shape)
    (ref : ConstRef Address) (present : ref ∈ shape.recs) :
    ∃ entry, (buildIndex store records).recs[ref]? = some entry ∧ entry.block = block ∧
      From store records ref entry := by
  have valid := buildIndex_valid store records
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
    (left : (position, first) ∈ recursorMembers constant) (right : (position, second) ∈ recursorMembers constant) :
    first = second := by
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

/-- Position uniqueness of the recursor members supplies the `find?` lookup
`readInductive` makes. -/
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

theorem entry_lookup (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (ref : ConstRef Address) (entry : RecEntry)
    (found : (buildIndex store records).recs[ref]? = some entry) :
    ∃ owner constant position recursor carriers,
      ref = .member owner position ∧ store owner = some constant ∧
      (recursorMembers constant).find? (·.1 == position) = some (position, recursor) ∧
      analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) := by
  obtain ⟨owner, constant, position, recursor, carriers, reference, stored, member, analysed⟩ :=
    entry_stored store records coherent ref entry found
  exact ⟨owner, constant, position, recursor, carriers, reference, stored,
    member_lookup constant position recursor member, analysed⟩

/-- **The reader's lookups for a block shape's recursor succeed**: indexed
at the block, a member of a stored record, found by position, with the
analysis that indexed it. -/
theorem grouped_lookup (store : Store) (records : Array (Address × Ixon.Constant))
    (coherent : Coherent store records) (block : Address) (shape : BlockShape)
    (shapeFound : (buildIndex store records).blocks[block]? = some shape)
    (ref : ConstRef Address) (present : ref ∈ shape.recs) :
    ∃ entry owner constant position recursor carriers,
      (buildIndex store records).recs[ref]? = some entry ∧ entry.block = block ∧
      ref = .member owner position ∧ store owner = some constant ∧
      (recursorMembers constant).find? (·.1 == position) = some (position, recursor) ∧
      analyseRecursor store owner constant recursor = some (entry.motive, carriers, entry.major) := by
  obtain ⟨entry, found, ownerEq, _⟩ := grouped_entry store records block shape shapeFound ref present
  obtain ⟨owner, constant, position, recursor, carriers, reference, stored, member, analysed⟩ :=
    entry_lookup store records coherent ref entry found
  exact ⟨entry, owner, constant, position, recursor, carriers, found, ownerEq, reference, stored, member, analysed⟩

end Ix.CompileCert.ReaderIndex
