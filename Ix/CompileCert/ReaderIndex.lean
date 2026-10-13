import Ix.CompileCert.InductiveReading
import Ix.CompileCert.ProjectionLayout

/-! Proof-visible phases of the actual recursor index builder. Accepted
candidate guards and the found-key/block-shape invariant justify later
reader contexts; index existence and source recursor analysis remain separate. -/

namespace Ix.CompileCert.ReaderIndex

open Ix Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

abbrev Found := Std.HashMap Address (Array (Nat × ConstRef Address))
abbrev BuildState := RecIndex × Found

def inductives (members : Array Ixon.MutConst) : Array (Nat × Ixon.Inductive) :=
  members.zipIdx.filterMap fun | (.indc ind, index) => some (index, ind) | _ => none

def orderFor (carriers : Array (ConstRef Address)) (owner : Address) (count : Nat) : Array Nat :=
  (carriers.extract 0 count).filterMap fun
    | .member block index => if block == owner then some index else none
    | .ctor .. => none

def orderValid (firstIndex : Nat) (indcs : Array (Nat × Ixon.Inductive)) (order : Array Nat) : Bool :=
  order.size == indcs.size && order[0]? == some firstIndex &&
    order.all (fun index => indcs.any (·.1 == index)) && order.toList.eraseDups.length == indcs.size

def candidate (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (owner : Address) (constant : Ixon.Constant) (member : Nat × Ixon.Recursor) (before : BuildState) : Id (ForInStep BuildState) := do
  let (position, recursor) := member
  let (idx, found) := before
  let ref : ConstRef Address := .member owner position
  if idx.recs.contains ref then return .yield before
  let some ((motive, carriers, major) : Nat × Array (ConstRef Address) × ConstRef Address) :=
    analyseRecursor store owner constant recursor | return .yield before
  let some (ConstRef.member block firstIndex) := (carriers[0]? : Option (ConstRef Address)) | return .yield before
  let some blockRecord := store block | return .yield before
  let .muts members := blockRecord.info | return .yield before
  let indcs := inductives members
  let some (_, first) := indcs[0]? | return .yield before
  let order := orderFor carriers block indcs.size
  unless orderValid firstIndex indcs order do return .yield before
  let memberName (ref : ConstRef Address) := pins.getD ref (keyName ref)
  let base : ConstRef Address := .member block (order[0]!)
  let name := if motive < indcs.size then (memberName (.member block (order[motive]!))).str "rec"
    else (memberName base).str s!"rec_{motive - indcs.size + 1}"
  if (found.getD block #[]).any (·.1 == motive) then return .yield before
  let large := recursor.lvls.toNat == first.lvls.toNat + 1
  let idx := { idx with recs := idx.recs.insert ref ⟨block, motive, major, large, name⟩ }
  let found := found.insert block ((found.getD block #[]).push (motive, ref))
  if idx.blocks.contains block then return .yield (idx, found)
  else return .yield ({ idx with blocks := idx.blocks.insert block ⟨order, #[]⟩ }, found)

def recordStep (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (record : Address × Ixon.Constant) (before : BuildState) : Id (ForInStep BuildState) :=
  .yield (forIn (m := Id) (recursorMembers record.2) before (candidate store pins record.1 record.2))

def completeStep (entry : Address × Array (Nat × ConstRef Address)) (idx : RecIndex) : Id (ForInStep RecIndex) :=
  let sorted := entry.2.qsort (fun left right => left.1 < right.1)
  let shape := idx.blocks.getD entry.1 default
  .yield { idx with blocks := idx.blocks.insert entry.1 { shape with recs := sorted.map (·.2) } }

def run (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) : RecIndex :=
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store pins)
  forIn (m := Id) collected.2.toList collected.1 completeStep

theorem run_eq (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) : run store pins records = buildIndex store pins records := by
  unfold run recordStep candidate completeStep inductives orderFor orderValid buildIndex
  simp only [Id.run, pure, bind]
  rfl

def OrderFrom (store : Store) (owner : Address) (order : Array Nat) : Prop :=
  ∃ constant members firstIndex first,
    store owner = some constant ∧ constant.info = .muts members ∧
      (inductives members)[0]? = some (firstIndex, first) ∧
      ∃ initialIndex, orderValid initialIndex (inductives members) order = true

def Shapes (store : Store) (index : RecIndex) : Prop :=
  ∀ owner shape, index.blocks[owner]? = some shape → OrderFrom store owner shape.order

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

theorem update_existing_valid (store : Store) (before : BuildState) (ref : ConstRef Address)
    (entry : RecEntry) (owner : Address) (entries : Array (Nat × ConstRef Address))
    (valid : Valid store before) (present : ∃ shape, before.1.blocks[owner]? = some shape) :
    Valid store ({ before.1 with recs := before.1.recs.insert ref entry }, before.2.insert owner entries) := by
  refine ⟨valid.1, ?_⟩
  intro query values found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · rename_i same
    have equal := beq_iff_eq.mp same
    subst query
    exact present
  · exact valid.2 query values found

theorem update_new_valid (store : Store) (before : BuildState) (ref : ConstRef Address)
    (entry : RecEntry) (owner : Address) (entries : Array (Nat × ConstRef Address)) (shape : BlockShape)
    (valid : Valid store before) (newShape : OrderFrom store owner shape.order) :
    Valid store ({ before.1 with
      recs := before.1.recs.insert ref entry,
      blocks := before.1.blocks.insert owner shape }, before.2.insert owner entries) := by
  refine ⟨shapes_insert store { before.1 with recs := before.1.recs.insert ref entry } owner shape valid.1 newShape, ?_⟩
  intro query values found
  rw [Std.HashMap.getElem?_insert] at found
  by_cases same : owner == query
  · have equal := beq_iff_eq.mp same
    subst query
    exact ⟨shape, by simp⟩
  · simp only [same, Bool.false_eq_true, ↓reduceIte] at found
    obtain ⟨old, oldFound⟩ := valid.2 query values found
    refine ⟨old, ?_⟩
    rw [Std.HashMap.getElem?_insert]
    simp only [same, Bool.false_eq_true, ↓reduceIte]
    exact oldFound

theorem candidate_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (owner : Address) (constant : Ixon.Constant) (member : Nat × Ixon.Recursor) (before : BuildState)
    (valid : Valid store before) :
    CanonUnivMeaning.StepHolds (Valid store) (candidate store pins owner constant member before) := by
  rcases member with ⟨position, recursor⟩
  unfold candidate
  dsimp only
  split
  · exact valid
  · split
    · rename_i motive carriers major foundAnalysis
      split
      · rename_i block firstIndex carrierFound
        split
        · rename_i blockRecord stored
          split
          · rename_i members kind
            split
            · rename_i firstIndex' first firstFound
              split
              · rename_i guarded
                split
                · exact valid
                · split
                  · rename_i existsBlock
                    apply update_existing_valid store before _ _ block _ valid
                    exact ⟨before.1.blocks.getD block default,
                      Std.HashMap.getElem?_eq_some_getD_of_contains existsBlock⟩
                  · apply update_new_valid store before _ _ block _ _ valid
                    exact ⟨blockRecord, members, firstIndex', first, stored, kind, firstFound, firstIndex, guarded⟩
              · exact valid
            · exact valid
          · exact valid
        · exact valid
      · exact valid
    · exact valid

theorem record_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (record : Address × Ixon.Constant) (before : BuildState) (valid : Valid store before) :
    CanonUnivMeaning.StepHolds (Valid store) (recordStep store pins record before) := by
  apply CanonUnivEmit.arrayLoop_preserves (Valid store) (recursorMembers record.2) before
    (candidate store pins record.1 record.2) valid
  intro member _ state good
  exact candidate_valid store pins record.1 record.2 member state good

theorem collect_valid (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) :
    Valid store (forIn (m := Id) records ({}, {}) (recordStep store pins)) := by
  apply CanonUnivEmit.arrayLoop_preserves (Valid store) records ({}, {}) (recordStep store pins) (valid_empty store)
  intro record _ state good
  exact record_valid store pins record state good

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

theorem complete_valid (store : Store) (found : Found)
    (entry : Address × Array (Nat × ConstRef Address)) (present : entry ∈ found.toList)
    (index : RecIndex) (valid : Valid store (index, found)) :
    CanonUnivMeaning.StepHolds (fun next => Valid store (next, found)) (completeStep entry index) := by
  have foundEntry : found[entry.1]? = some entry.2 := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp present
  obtain ⟨shape, stored⟩ := valid.2 entry.1 entry.2 foundEntry
  have defaultEq : index.blocks.getD entry.1 default = shape := by
    rw [Std.HashMap.getD_eq_getD_getElem?, stored]
    rfl
  unfold completeStep
  dsimp only
  rw [defaultEq]
  refine ⟨shapes_insert store index entry.1 _ valid.1 (valid.1 entry.1 shape stored),
    supported_insert_shape index found entry.1 _ valid.2⟩

theorem run_shapes (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) : Shapes store (run store pins records) := by
  let collected := forIn (m := Id) records (({} : RecIndex), ({} : Found)) (recordStep store pins)
  have valid : Valid store collected := collect_valid store pins records
  have completed := CanonUnivMeaning.listLoop_preserves (fun index => Valid store (index, collected.2))
    collected.2.toList collected.1 completeStep valid
    (fun entry present index good => complete_valid store collected.2 entry present index good)
  exact completed.1

theorem buildIndex_shapes (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) : Shapes store (buildIndex store pins records) := by
  rw [← run_eq]
  exact run_shapes store pins records

theorem singleton_inductives (source : Ixon.Inductive) : inductives #[.indc source] = #[(0, source)] := by
  simp [inductives]

theorem singleton_order (source : Ixon.Inductive) (order : Array Nat) (firstIndex : Nat)
    (valid : orderValid firstIndex #[(0, source)] order = true) : order = #[0] := by
  simp only [orderValid, Bool.and_eq_true] at valid
  have count : order.size = 1 := by simpa using valid.1.1.1
  obtain ⟨index, rfl⟩ := HeaderBlock.array_one order count
  have position : 0 = index := by simpa using valid.1.2
  rw [← position]

/-- The actual completed index gives the emitted singleton inductive block
exactly member zero. It needs no reader-success or supplied-order premise. -/
theorem buildIndex_singleton_order (store : Store) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (owner : Address) (constant : Ixon.Constant)
    (source : Ixon.Inductive) (shape : BlockShape)
    (stored : store owner = some constant) (kind : constant.info = .muts #[.indc source])
    (indexed : (buildIndex store pins records).blocks[owner]? = some shape) : shape.order = #[0] := by
  obtain ⟨actual, members, firstIndex, first, actualStored, actualKind, _, initialIndex, guarded⟩ :=
    buildIndex_shapes store pins records owner shape indexed
  have same : actual = constant := Option.some.inj (actualStored.symm.trans stored)
  subst actual
  have membersEq : members = #[.indc source] := Ixon.ConstantInfo.muts.inj (actualKind.symm.trans kind)
  subst members
  rw [singleton_inductives] at guarded
  exact singleton_order source shape.order initialIndex guarded

open Ix.CompileM Ix.CompileCert.HeadWriterFrame in
theorem compiled_shape (source : InductiveVal) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    ∃ target, output.block.info = .muts #[.indc target] := by
  have infoRun : rawRun (compileInductiveInfo source) (DefinitionReading.singletonContext source.cnst.name context) before =
      (.ok output, after) := ran
  obtain ⟨constructors, _, familyRun⟩ := InductiveBlock.info_run source
    (DefinitionReading.singletonContext source.cnst.name context) before after output infoRun
  rw [compileInductiveFamilyInfo] at familyRun
  obtain ⟨done, middle, _, compiled⟩ := PreseedReferences.bind_ok _ _
    (InductiveBlock.familyContext source constructors (DefinitionReading.singletonContext source.cnst.name context))
    before output after familyRun
  obtain ⟨target, _, _, kind, _⟩ := ProjectionLayout.family_layout source constructors
    (InductiveBlock.familyContext source constructors (DefinitionReading.singletonContext source.cnst.name context))
    middle output after compiled
  exact ⟨target, kind⟩

open Ix.CompileM Ix.CompileCert.HeadWriterFrame in
/-- Public compilation plus real index construction discharges the previous
singleton-order premise. Publication and index presence remain explicit. -/
theorem compiled_order (source : InductiveVal) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after))
    (reader : Ctx) (pins : Std.HashMap (ConstRef Address) Kernel.Name)
    (records : Array (Address × Ixon.Constant)) (shape : BlockShape)
    (indexBuilt : reader.index = buildIndex reader.store pins records)
    (stored : reader.store output.blockAddr = some output.block)
    (indexed : reader.index.blocks[output.blockAddr]? = some shape) : shape.order = #[0] := by
  obtain ⟨target, kind⟩ := compiled_shape source context before after output ran
  exact buildIndex_singleton_order reader.store pins records output.blockAddr output.block target shape stored kind
    (by simpa only [indexBuilt] using indexed)

open Ix.CompileM Ix.CompileCert.HeadWriterFrame in
theorem compile_read_indexed (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (before after : BlockState) (output : BlockResult) (state : State) (shape : BlockShape)
    (recursors : Array FamilyRecursors.Input)
    (pins : Std.HashMap (ConstRef Address) Kernel.Name) (records : Array (Address × Ixon.Constant))
    (indexBuilt : reader.index = buildIndex reader.store pins records)
    (stored : reader.store output.blockAddr = some output.block)
    (scope : ExpressionScope.Scoped
      (ExpressionScope.SelfName (InductiveBlock.familyContext source constructors context).2
        (InductiveReading.selfAt reader output.blockAddr) names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors, ExpressionScope.Scoped
      (ExpressionScope.SelfName (InductiveBlock.familyContext source constructors context).2
        (InductiveReading.selfAt reader output.blockAddr) names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (found : (rawRun (lookupInductiveConstructors source) context before).1 = .ok constructors)
    (ready : DefinitionEmission.Ready bindings before) (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after))
    (indexed : reader.index.blocks[output.blockAddr]? = some shape) (safe : source.isUnsafe = false)
    (ctorReady : FamilyConstructors.SourceReady source.numParams (InductiveEmission.sourceData source constructors))
    (recursorOrder : shape.recs = recursors.map FamilyRecursors.Input.ref)
    (recursorValid : ∀ input ∈ recursors, FamilyRecursors.Valid (SharingRead.blobContext reader after)
      (InductiveReading.paramsFor reader output.blockAddr source) names input) :
    DefinitionEmission.Clean bindings after ∧ Sharing.Verify.BlockResultCodecWF output ∧
      (∃ metadata pairs, InductiveBlock.Wrapped source metadata pairs output) ∧
      ∃ target, output.block.info = .muts #[.indc target] ∧
        ∃ collected : FamilyReading.Collected (SharingRead.blobContext reader after) output.blockAddr names
            (InductiveReading.paramsFor reader output.blockAddr source) (InductiveReading.sourceFamily source constructors) recursors,
          (collected.Consistent source.numParams →
            readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block =
              (collected.assembly source.numParams #[(0, target)]).run state) ∧
          (collected.Consistent source.numParams →
            FamilySourceChecks.sourceNested (InductiveReading.sourceFamily source constructors) recursors = 0 →
            readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block =
              .ok ((collected.assembly source.numParams #[(0, target)]).result [])) ∧
          (0 < FamilySourceChecks.sourceNested (InductiveReading.sourceFamily source constructors) recursors →
            Kernel.Frontend.InModel.wants (collected.assembly source.numParams #[(0, target)]).model = true) :=
  InductiveReading.compile_read reader base names bindings context source constructors before after output state shape recursors
    scope ctorScope aligned external found ready tables widths ran indexed
    (compiled_order source context before after output ran reader pins records shape indexBuilt stored indexed)
    safe ctorReady recursorOrder recursorValid

end Ix.CompileCert.ReaderIndex
