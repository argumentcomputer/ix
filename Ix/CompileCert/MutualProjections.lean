import Ix.CompileCert.ProjectionLayout
import Ix.CompileCert.Canon.Loop
import Ix.CompileCert.Canon.Coarsest

/-! Actual mutual projection rows, codec facts and anonymous reference reading.
Class-shape agreement follows the existing canonicalization theorem under its
name-key and address-map assumptions. Source-index validity, installed-store
availability and whole-driver composition remain separate obligations. -/

namespace Ix.CompileCert.MutualProjections

open Ix Ix.CompileM

abbrev Row := Name × Ixon.Constant × Ixon.ConstantMeta

def logicalRows (rows : Array Row) : List (Name × Ixon.Constant) :=
  rows.toList.map fun row => (row.1, row.2.1)

def memberProjection (owner : Address) (index : UInt64) (source : MutConst) : Ixon.Constant :=
  ⟨match source with
    | .defn _ => .dPrj ⟨index, owner⟩
    | .indc _ => .iPrj ⟨index, owner⟩
    | .recr _ => .rPrj ⟨index, owner⟩, #[], #[], #[]⟩

def constructorProjection (owner : Address) (index ctorIndex : UInt64) : Ixon.Constant :=
  ⟨.cPrj ⟨index, ctorIndex, owner⟩, #[], #[], #[]⟩

def sourceRows (owner : Address) (index : UInt64) (source : MutConst) : List (Name × Ixon.Constant) :=
  (source.name, memberProjection owner index source) ::
    source.ctors.toList.zipIdx.map fun (ctor, ctorIndex) =>
      (ctor.cnst.name, constructorProjection owner index ctorIndex.toUInt64)

def expectedRows (owner : Address) (classes : List (List MutConst)) : List (Name × Ixon.Constant) :=
  classes.zipIdx.flatMap fun (members, index) =>
    members.flatMap (sourceRows owner index.toUInt64)

theorem indexed_rows (sources : List α) (initial : Array Row) (offset : Nat)
    (name : α → Name) (emit : UInt64 → α → Ixon.Constant) (metadata : α → Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources (initial, offset.toUInt64) (fun source state =>
      .yield (state.1.push (name source, emit state.2 source, metadata source), state.2 + 1))).1 =
      logicalRows initial ++ (sources.zipIdx offset).map (fun (source, index) => (name source, emit index.toUInt64 source)) := by
  induction sources generalizing initial offset with
  | nil => change logicalRows initial = logicalRows initial ++ []; simp
  | cons source rest ih =>
    rw [List.forIn_cons]
    change logicalRows (forIn (m := Id) rest
      (initial.push (name source, emit offset.toUInt64 source, metadata source), offset.toUInt64 + 1)
      (fun source state => .yield (state.1.push (name source, emit state.2 source, metadata source), state.2 + 1))).1 = _
    have next : offset.toUInt64 + 1 = (offset + 1).toUInt64 := by simp
    rw [next, ih]
    simp [logicalRows, List.zipIdx_cons, List.append_assoc]

theorem constructor_rows (sources : Array ConstructorVal) (initial : Array Row)
    (owner : Address) (index : UInt64) (metadata : Std.HashMap Name Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources (initial, (0 : UInt64)) (fun source state =>
      .yield (state.1.push (source.cnst.name, constructorProjection owner index state.2,
        (metadata.get? source.cnst.name).getD .empty), state.2 + 1))).1 =
      logicalRows initial ++ sources.toList.zipIdx.map (fun (source, ctorIndex) =>
        (source.cnst.name, constructorProjection owner index ctorIndex.toUInt64)) := by
  rw [← Array.forIn_toList]
  exact indexed_rows sources.toList initial 0 (·.cnst.name)
    (fun ctorIndex _ => constructorProjection owner index ctorIndex)
    (fun source => (metadata.get? source.cnst.name).getD .empty)

def memberStep (owner : Address) (index : UInt64) (metadata : Std.HashMap Name Ixon.ConstantMeta)
    (source : MutConst) (initial : Array Row) : Id (ForInStep (Array Row)) :=
  let rows := initial.push (source.name, memberProjection owner index source,
    (metadata.get? source.name).getD .empty)
  match source with
  | .indc value =>
    .yield (forIn (m := Id) value.ctors (rows, (0 : UInt64)) (fun ctor state =>
      .yield (state.1.push (ctor.cnst.name, constructorProjection owner index state.2,
        (metadata.get? ctor.cnst.name).getD .empty), state.2 + 1))).1
  | _ => .yield rows

theorem memberStep_yield (owner : Address) (index : UInt64) (metadata : Std.HashMap Name Ixon.ConstantMeta)
    (source : MutConst) (initial : Array Row) :
    memberStep owner index metadata source initial = .yield (memberStep owner index metadata source initial).value := by
  cases source <;> rfl

theorem memberStep_rows (owner : Address) (index : UInt64) (metadata : Std.HashMap Name Ixon.ConstantMeta)
    (source : MutConst) (initial : Array Row) :
    logicalRows (memberStep owner index metadata source initial).value = logicalRows initial ++ sourceRows owner index source := by
  cases source with
  | defn value | recr value => simp [memberStep, sourceRows, logicalRows, MutConst.ctors]
  | indc value =>
    change logicalRows (forIn (m := Id) value.ctors
      (initial.push (value.name, memberProjection owner index (.indc value), (metadata.get? value.name).getD .empty), (0 : UInt64))
      (fun ctor state => .yield (state.1.push (ctor.cnst.name, constructorProjection owner index state.2,
        (metadata.get? ctor.cnst.name).getD .empty), state.2 + 1))).1 = _
    rw [constructor_rows]
    simp [sourceRows, logicalRows, MutConst.ctors, MutConst.name, List.append_assoc]

theorem members_rows (sources : List MutConst) (initial : Array Row)
    (owner : Address) (index : UInt64) (metadata : Std.HashMap Name Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources initial (memberStep owner index metadata)) =
      logicalRows initial ++ sources.flatMap (sourceRows owner index) := by
  induction sources generalizing initial with
  | nil => change logicalRows initial = logicalRows initial ++ []; simp
  | cons source rest ih =>
    rw [List.forIn_cons, memberStep_yield]
    change logicalRows (forIn (m := Id) rest (memberStep owner index metadata source initial).value
      (memberStep owner index metadata)) = _
    rw [ih, memberStep_rows]
    simp [List.append_assoc]

def classStep (owner : Address) (metadata : Std.HashMap Name Ixon.ConstantMeta)
    (sources : List MutConst) (initial : Array Row × UInt64) : Id (ForInStep (Array Row × UInt64)) :=
  .yield (forIn (m := Id) sources initial.1 (memberStep owner initial.2 metadata), initial.2 + 1)

theorem classes_rows (sources : List (List MutConst)) (initial : Array Row) (offset : Nat)
    (owner : Address) (metadata : Std.HashMap Name Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources (initial, offset.toUInt64) (classStep owner metadata)).1 =
      logicalRows initial ++ (sources.zipIdx offset).flatMap (fun (members, index) => members.flatMap (sourceRows owner index.toUInt64)) := by
  induction sources generalizing initial offset with
  | nil => change logicalRows initial = logicalRows initial ++ []; simp
  | cons source rest ih =>
    rw [List.forIn_cons]
    change logicalRows (forIn (m := Id) rest
      (forIn (m := Id) source initial (memberStep owner offset.toUInt64 metadata), offset.toUInt64 + 1)
      (classStep owner metadata)).1 = _
    have next : offset.toUInt64 + 1 = (offset + 1).toUInt64 := by simp
    rw [next, ih, members_rows]
    simp [List.zipIdx_cons, List.append_assoc]

/-- The actual nested generator emits these exact anonymous constants and
source registration keys, independently of presentation metadata values. -/
theorem build_rows (sources : List (List MutConst)) (owner : Address)
    (metadata : Array (Name × Ixon.ConstantMeta)) :
    logicalRows (buildMutualProjections sources owner metadata) = expectedRows owner sources := by
  let lookup : Std.HashMap Name Ixon.ConstantMeta := metadata.foldl (fun table pair => table.insert pair.1 pair.2) {}
  change logicalRows (forIn (m := Id) sources (#[], (0 : UInt64)) (classStep owner lookup)).1 = _
  simpa [expectedRows, logicalRows] using classes_rows sources #[] 0 owner lookup

theorem empty_tables_wire (info : Ixon.ConstantInfo) (header : info.wireWF) :
    (⟨info, #[], #[], #[]⟩ : Ixon.Constant).wireWF :=
  ⟨header, by change 0 < UInt64.size; decide, by simp,
    by change 0 < UInt64.size; decide, by simp,
    by change 0 < UInt64.size; decide, by simp⟩

theorem member_wire (owner : Address) (width : owner.hash.size = 32) (index : UInt64) (source : MutConst) :
    (memberProjection owner index source).wireWF := by
  cases source <;> exact empty_tables_wire _ width

theorem constructor_wire (owner : Address) (width : owner.hash.size = 32) (index ctorIndex : UInt64) :
    (constructorProjection owner index ctorIndex).wireWF :=
  empty_tables_wire _ width

theorem source_rows_wire (owner : Address) (width : owner.hash.size = 32) (index : UInt64) (source : MutConst)
    (row : Name × Ixon.Constant) (present : row ∈ sourceRows owner index source) : row.2.wireWF := by
  rcases List.mem_cons.mp present with rfl | rest
  · exact member_wire owner width index source
  · obtain ⟨⟨ctor, ctorIndex⟩, _, rfl⟩ := List.mem_map.mp rest
    exact constructor_wire owner width index ctorIndex.toUInt64

theorem build_rows_wire (sources : List (List MutConst)) (owner : Address) (width : owner.hash.size = 32)
    (metadata : Array (Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildMutualProjections sources owner metadata) : row.2.1.wireWF := by
  have logical : (row.1, row.2.1) ∈ logicalRows (buildMutualProjections sources owner metadata) :=
    List.mem_map.mpr ⟨row, by simpa using present, rfl⟩
  rw [build_rows, expectedRows] at logical
  obtain ⟨⟨members, index⟩, _, inClass⟩ := List.mem_flatMap.mp logical
  obtain ⟨source, _, generated⟩ := List.mem_flatMap.mp inClass
  exact source_rows_wire owner width index.toUInt64 source (row.1, row.2.1) generated

theorem build_rows_codec (sources : List (List MutConst)) (owner : Address) (width : owner.hash.size = 32)
    (metadata : Array (Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildMutualProjections sources owner metadata) :
    Ixon.deConstant (Ixon.ser row.2.1) = .ok row.2.1 :=
  Ixon.Verify.deConstant_serConstant row.2.1 (build_rows_wire sources owner width metadata row present)

theorem pushed_rows (sources : List α) (initial : Array Row) (makeRow : α → Row) :
    logicalRows (forIn (m := Id) sources initial (fun source rows => .yield (rows.push (makeRow source)))) =
      logicalRows initial ++ sources.map (fun source => ((makeRow source).1, (makeRow source).2.1)) := by
  induction sources generalizing initial with
  | nil => change logicalRows initial = logicalRows initial ++ []; simp
  | cons source rest ih =>
    rw [List.forIn_cons]
    change logicalRows (forIn (m := Id) rest (initial.push (makeRow source))
      (fun source rows => .yield (rows.push (makeRow source)))) = _
    rw [ih]
    simp [logicalRows, List.append_assoc]

theorem standalone_classes_rows (sources : List (List MutConst)) (initial : Array Row)
    (block : Ixon.Constant) (metadata : Std.HashMap Name Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources initial (fun members rows =>
      .yield (forIn (m := Id) members rows (fun source rows =>
        .yield (rows.push (source.name, block, (metadata.get? source.name).getD .empty)))))) =
      logicalRows initial ++ sources.flatten.map (fun source => (source.name, block)) := by
  induction sources generalizing initial with
  | nil => change logicalRows initial = logicalRows initial ++ []; simp
  | cons source rest ih =>
    rw [List.forIn_cons]
    change logicalRows (forIn (m := Id) rest
      (forIn (m := Id) source initial (fun source rows =>
        .yield (rows.push (source.name, block, (metadata.get? source.name).getD .empty))))
      (fun members rows => .yield (forIn (m := Id) members rows (fun source rows =>
        .yield (rows.push (source.name, block, (metadata.get? source.name).getD .empty)))))) = _
    rw [ih, pushed_rows]
    simp [List.append_assoc]

theorem standalone_rows (sources : List (List MutConst)) (block : Ixon.Constant)
    (metadata : Array (Name × Ixon.ConstantMeta)) :
    logicalRows (buildStandaloneMutualProjections sources block metadata) =
      sources.flatten.map (fun source => (source.name, block)) := by
  let lookup : Std.HashMap Name Ixon.ConstantMeta := metadata.foldl (fun table pair => table.insert pair.1 pair.2) {}
  change logicalRows (forIn (m := Id) sources #[] (fun members rows =>
    .yield (forIn (m := Id) members rows (fun source rows =>
      .yield (rows.push (source.name, block, (lookup.get? source.name).getD .empty)))))) = _
  simpa [logicalRows] using standalone_classes_rows sources #[] block lookup

theorem standalone_rows_wire (sources : List (List MutConst)) (block : Ixon.Constant) (wire : block.wireWF)
    (metadata : Array (Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildStandaloneMutualProjections sources block metadata) : row.2.1.wireWF := by
  have logical : (row.1, row.2.1) ∈ logicalRows (buildStandaloneMutualProjections sources block metadata) :=
    List.mem_map.mpr ⟨row, by simpa using present, rfl⟩
  rw [standalone_rows] at logical
  obtain ⟨source, _, same⟩ := List.mem_map.mp logical
  have sameBlock := congrArg Prod.snd same
  change block = row.2.1 at sameBlock
  exact sameBlock ▸ wire

def ProjectionWire (output : BlockResult) : Prop := ∀ row ∈ output.projections, row.2.1.wireWF

theorem build_projection_wire (limits : Ix.Sharing.Exact.Limits) (classes : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Name × Ixon.ConstantMeta)) (state : BlockState)
    (output : BlockResult) (ran : buildCompiledMutualBlock limits classes members metadata state = .ok output)
    (main : output.block.wireWF) : ProjectionWire output := by
  unfold buildCompiledMutualBlock at ran
  cases chosen : standaloneMutConstInfo? members with
  | some info =>
    simp only [chosen] at ran
    obtain ⟨block, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact standalone_rows_wire classes block main metadata
  | none =>
    simp only [chosen] at ran
    obtain ⟨block, _, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    exact build_rows_wire classes (Address.blake3 (Ixon.ser block)) (WireTables.blake3_width _) metadata

open Ix.CompileCert.HeadWriterFrame
open DeclarationHeaders (Returns)

theorem finish_projection_wire (classes : List (List MutConst)) (members : Array Ixon.MutConst)
    (metadata : Array (Name × Ixon.ConstantMeta)) : Returns (finishMutualCompilation classes members metadata)
      (fun output => output.block.wireWF → ProjectionWire output) := by
  intro context before output after ran main
  unfold finishMutualCompilation at ran
  obtain ⟨done, middle, guarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := PayloadArrays.mutual_state members context before
  rw [guarded] at same
  dsimp only at same
  subst middle
  have readContext : rawRun (read : CompileM (CompileEnv × BlockEnv)) context before = (.ok context, before) := rfl
  simp only [rawRun_bind, rawRun_get, readContext, Ix.PhaseTimers.withPhase,
    Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV, ite_self] at rest
  cases built : buildCompiledMutualBlock context.1.sharingLimits classes members metadata before with
  | error reason => rw [built] at rest; cases rest
  | ok result =>
    rw [built, rawRun_pure] at rest
    cases Except.ok.inj (congrArg Prod.fst rest)
    exact build_projection_wire _ classes members metadata before output built main

theorem payload_projection_wire (sources : List (List MutConst)) : Returns (compileMutualPayload sources)
    (fun output => output.block.wireWF → ProjectionWire output) :=
  Returns.bindAny (compileMutConsts sources) fun compiled => finish_projection_wire sources compiled.1 compiled.2.2

theorem mutual_projection_wire (sources : List (List MutConst)) : Returns (compileMutualBlock sources)
    (fun output => output.block.wireWF → ProjectionWire output) := by
  unfold compileMutualBlock withMutCtx
  exact PayloadArrays.Returns.withBlockEnv (fun context => { context with mutCtx := MutConst.ctx sources })
    (Returns.bindAny (preseedExprTables (mutualPreseedExprs sources)) fun _ => payload_projection_wire sources)

theorem mutual_codec (sources : List (List MutConst)) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output ∧ ProjectionWire output ∧
      ∀ row ∈ output.projections, Ixon.deConstant (Ixon.ser row.2.1) = .ok row.2.1 := by
  have main := FamilyWire.mutualBlock_codec sources context bindings before after output ready tables widths ran
  have projections := mutual_projection_wire sources context before output after ran main.1
  exact ⟨main, projections, fun row present => Ixon.Verify.deConstant_serConstant row.2.1 (projections row present)⟩

theorem member_resolves (store : Kernel.Reader.Store) (owner : Address) (block : Ixon.Constant)
    (members : Array Ixon.MutConst) (source : MutConst) (target : Ixon.MutConst) (index : UInt64)
    (stored : store owner = some block) (info : block.info = .muts members)
    (member : members[index.toNat]? = some target)
    (shape : ProjectionLayout.memberShape target = ProjectionLayout.sourceShape source) :
    Kernel.Reader.resolveSource store (Address.blake3 (Ixon.ser (memberProjection owner index source)))
      (memberProjection owner index source) = some (.member owner index.toNat) := by
  cases source <;> cases target <;>
    simp_all [ProjectionLayout.memberShape, ProjectionLayout.sourceShape, memberProjection,
      Kernel.Reader.resolveSource, Kernel.Reader.emptyTables, guard]

theorem constructor_resolves (store : Kernel.Reader.Store) (owner : Address) (block : Ixon.Constant)
    (members : Array Ixon.MutConst) (source : Ind) (target : Ixon.Inductive) (index position : UInt64)
    (stored : store owner = some block) (info : block.info = .muts members)
    (member : members[index.toNat]? = some (.indc target))
    (indices : target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = source.ctors.toList.map (·.cidx))
    (inside : position.toNat < source.ctors.size) (sourceIndex : source.ctors[position.toNat].cidx = position.toNat) :
    Kernel.Reader.resolveSource store (Address.blake3 (Ixon.ser (constructorProjection owner index position)))
      (constructorProjection owner index position) = some (.ctor owner index.toNat position.toNat) := by
  have length : target.ctors.size = source.ctors.size := by simpa using congrArg List.length indices
  have targetInside : position.toNat < target.ctors.size := by omega
  have row := congrArg (fun values : List Nat => values[position.toNat]?) indices
  simp only [List.getElem?_map, Array.getElem?_toList] at row
  rw [Array.getElem?_eq_getElem targetInside, Array.getElem?_eq_getElem inside] at row
  have naturalIndex := (Option.some.inj row).trans sourceIndex
  have converted : target.ctors[position.toNat].cidx = position := UInt64.toNat_inj.mp naturalIndex
  simp [constructorProjection, Kernel.Reader.resolveSource, Kernel.Reader.emptyTables,
    stored, info, member, Array.getElem?_eq_getElem targetInside, converted, guard]

theorem selected_member (sources : List (List MutConst)) (targets : List Ixon.MutConst)
    (nonempty : ∀ members ∈ sources, members ≠ [])
    (shape : targets.map ProjectionLayout.memberShape = (sources.filterMap List.head?).map ProjectionLayout.sourceShape)
    (index : Nat) (inside : index < sources.length) :
    ∃ selected rest target, sources[index]? = some (selected :: rest) ∧ targets[index]? = some target ∧
      ProjectionLayout.memberShape target = ProjectionLayout.sourceShape selected := by
  induction sources generalizing targets index with
  | nil => simp at inside
  | cons members remaining ih =>
    have firstNonempty := nonempty members (by simp)
    cases members with
    | nil => exact False.elim (firstNonempty rfl)
    | cons selected rest =>
      cases targets with
      | nil => simp [List.filterMap] at shape
      | cons target targets =>
        have equal : ProjectionLayout.memberShape target = ProjectionLayout.sourceShape selected ∧
            targets.map ProjectionLayout.memberShape = (remaining.filterMap List.head?).map ProjectionLayout.sourceShape := by
          simpa [List.filterMap] using shape
        cases index with
        | zero => exact ⟨selected, rest, target, rfl, rfl, equal.1⟩
        | succ index =>
          have tailNonempty : ∀ members ∈ remaining, members ≠ [] := fun members present =>
            nonempty members (by simp [present])
          obtain ⟨next, suffix, member, sourceAt, targetAt, shapeAt⟩ :=
            ih targets tailNonempty equal.2 index (by simpa using inside)
          exact ⟨next, suffix, member, by simpa using sourceAt, by simpa using targetAt, shapeAt⟩

/-- The remaining class-specific condition needed for all aliases, beyond
the compiled representative's already-proved shape. -/
def ClassesAgree (sources : List (List MutConst)) : Prop :=
  ∀ members ∈ sources, ∀ left ∈ members, ∀ right ∈ members,
    ProjectionLayout.sourceShape left = ProjectionLayout.sourceShape right

theorem class_member (sources : List (List MutConst)) (targets : Array Ixon.MutConst)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : ClassesAgree sources)
    (shape : targets.toList.map ProjectionLayout.memberShape = (sources.filterMap List.head?).map ProjectionLayout.sourceShape)
    (index : Nat) (inside : index < sources.length) (source : MutConst) (present : source ∈ sources[index]) :
    ∃ target, targets[index]? = some target ∧ ProjectionLayout.memberShape target = ProjectionLayout.sourceShape source := by
  obtain ⟨selected, rest, target, sourceAt, targetAt, shapeAt⟩ := selected_member sources targets.toList nonempty shape index inside
  have sameClass : sources[index] = selected :: rest := by
    rw [List.getElem?_eq_getElem inside] at sourceAt
    exact Option.some.inj sourceAt
  have classPresent : sources[index] ∈ sources := List.getElem_mem inside
  have sameShape := agree sources[index] classPresent selected (by simp [sameClass]) source present
  exact ⟨target, by simpa using targetAt, shapeAt.trans sameShape⟩

open Ix.Compile.Canon (CmpCtx)

theorem cmpM_eq_parts (left right : Except String SOrder) (strength : Bool)
    (ran : SOrder.cmpM left right = .ok ⟨strength, .eq⟩) :
    ∃ first last, left = .ok ⟨first, .eq⟩ ∧ right = .ok ⟨last, .eq⟩ := by
  obtain ⟨⟨first, order⟩, leftRun, branch⟩ := Canon.cmpM_ok.mp ran
  rcases branch with ⟨different, same⟩ | ⟨equal, ⟨⟨last, lastOrder⟩, rightRun, same⟩⟩
  · have orderEq := congrArg SOrder.ord same
    exact False.elim (different orderEq.symm)
  · have orderEq := congrArg SOrder.ord same
    change order = .eq at equal
    change Ordering.eq = lastOrder at orderEq
    subst order
    subst lastOrder
    exact ⟨first, last, leftRun, rightRun⟩

theorem lex_eq_right (left right : Except String SOrder) (strength : Bool)
    (ran : Canon.lexIf left right = .ok ⟨strength, .eq⟩) : right = .ok ⟨strength, .eq⟩ := by
  obtain ⟨first, _, branch⟩ := Canon.lexIf_ok.mp ran
  rcases branch with ⟨different, same⟩ | ⟨_, rightRun⟩
  · exact False.elim (different (congrArg SOrder.ord same).symm)
  · exact rightRun

theorem ctor_compare_index (context : CmpCtx) (leftParams rightParams : List Name)
    (left right : ConstructorVal) (strength : Bool)
    (ran : Canon.ctorP context leftParams rightParams left right = .ok ⟨strength, .eq⟩) : left.cidx = right.cidx := by
  unfold Canon.ctorP at ran
  obtain ⟨_, tailStrength, _, tail⟩ := cmpM_eq_parts _ _ strength ran
  obtain ⟨_, _, scalar, _⟩ := cmpM_eq_parts _ _ tailStrength tail
  have compared := congrArg SOrder.ord (Except.ok.inj scalar)
  exact Nat.compare_eq_eq.mp compared

theorem ctor_list_indices (context : CmpCtx) (leftParams rightParams : List Name)
    (left right : List ConstructorVal) (strength : Bool)
    (ran : SOrder.zipM (Canon.ctorP context leftParams rightParams) left right = .ok ⟨strength, .eq⟩) :
    left.map (·.cidx) = right.map (·.cidx) := by
  induction left generalizing right strength with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail => simp [SOrder.zipM, pure, Except.pure] at ran
  | cons head tail ih =>
    cases right with
    | nil => simp [SOrder.zipM, pure, Except.pure] at ran
    | cons other rest =>
      rw [Canon.zipM_cons] at ran
      obtain ⟨first, last, compared, remaining⟩ := cmpM_eq_parts _ _ strength ran
      have index := ctor_compare_index context leftParams rightParams head other first compared
      simp only [List.map_cons, index, ih rest last remaining]

theorem inductive_compare_indices (context : CmpCtx) (left right : Ind) (strength : Bool)
    (ran : Canon.indP context left right = .ok ⟨strength, .eq⟩) :
    left.ctors.toList.map (·.cidx) = right.ctors.toList.map (·.cidx) := by
  have body := lex_eq_right _ _ strength ran
  obtain ⟨_, last, _, ctors⟩ := cmpM_eq_parts _ _ strength body
  exact ctor_list_indices context left.levelParams.toList right.levelParams.toList left.ctors.toList right.ctors.toList last ctors

theorem const_compare_shape (context : CmpCtx) (left right : MutConst) (strength : Bool)
    (ran : Canon.constP context left right = .ok ⟨strength, .eq⟩) :
    ProjectionLayout.sourceShape left = ProjectionLayout.sourceShape right := by
  cases left <;> cases right
  all_goals first
    | rfl
    | exact congrArg ProjectionLayout.MemberShape.indc (inductive_compare_indices context _ _ strength ran)
    | simp [Canon.constP, Ix.Compile.Canon.kindTag, pure, Except.pure] at ran

theorem compared_shape (context : CmpCtx) (left right : MutConst)
    (ran : (Canon.constP context left right).map SOrder.ord = .ok .eq) :
    ProjectionLayout.sourceShape left = ProjectionLayout.sourceShape right := by
  cases result : Canon.constP context left right with
  | error reason => simp [result, Except.map] at ran
  | ok value =>
    rcases value with ⟨strength, order⟩
    simp only [result, Except.map, Except.ok.injEq] at ran
    subst order
    exact const_compare_shape context left right strength result

theorem ordered_shape (rules : Ix.Compile.Canon.Rules) (addresses : Name → Option Address)
    (context : MutCtx) (left right : MutConst)
    (ran : Canon.constOrd rules addresses context left right = .ok .eq) :
    ProjectionLayout.sourceShape left = ProjectionLayout.sourceShape right := by
  unfold Canon.constOrd at ran
  cases mode : rules.tieBreak with
  | inline | blind => simp only [mode] at ran; exact compared_shape _ left right ran
  | byAddress =>
    simp only [mode] at ran
    cases first : (Canon.constP (Canon.ctxOf rules addresses .blind context) left right).map SOrder.ord with
    | error reason => simp [first, bind, Except.bind] at ran
    | ok order =>
      cases order with
      | lt | gt => simp [first, bind, Except.bind, pure, Except.pure] at ran
      | eq => exact compared_shape _ left right first

theorem sorted_classes_agree (rules : Ix.Compile.Canon.Rules) (fixed : rules.portFixes = true)
    (addresses : Name → Option Address) (congruent : Canon.AddrCongr addresses)
    (sources : List MutConst) (keys : Canon.KeysDistinct sources) (classes : List (List MutConst))
    (stats : Ix.Compile.Canon.SortStats)
    (ran : Ix.Compile.Canon.sortClasses rules addresses sources = .ok (classes, stats)) : ClassesAgree classes := by
  have consistent := (Canon.sortClasses_coarsest fixed congruent keys ran).2.1
  intro members present left leftIn right rightIn
  by_cases same : left = right
  · exact same ▸ rfl
  · exact ordered_shape rules addresses (MutConst.ctx classes) left right
      (consistent members present left leftIn right rightIn same)

theorem reordered_member (sources : List (List MutConst)) (members : List MutConst)
    (present : members ∈ orderRecursorFamily sources) : members ∈ sources := by
  unfold orderRecursorFamily at present
  split at present
  · exact present
  · simp only [Array.mem_toList_iff, Array.mem_map] at present
    obtain ⟨entry, sorted, rfl⟩ := present
    rw [Canon.mem_qsort] at sorted
    obtain ⟨pair, paired, rfl⟩ := Array.mem_map.mp sorted
    simpa using Array.fst_mem_of_mem_zipIdx paired

theorem reordered_classes_agree (sources : List (List MutConst)) (agree : ClassesAgree sources) :
    ClassesAgree (orderRecursorFamily sources) :=
  fun members present => agree members (reordered_member sources members present)

theorem production_classes (addresses : Name → Option Address) (congruent : Canon.AddrCongr addresses)
    (sources : List MutConst) (keys : Canon.KeysDistinct sources) (classes : List (List MutConst))
    (stats : Ix.Compile.Canon.SortStats)
    (ran : Ix.Compile.Canon.sortClasses Ix.Compile.Canon.Rules.compiler addresses sources = .ok (classes, stats)) :
    (∀ members ∈ orderRecursorFamily classes, members ≠ []) ∧ ClassesAgree (orderRecursorFamily classes) :=
  ⟨ProjectionLayout.ordered_nonempty classes
      (ProjectionLayout.sorted_nonempty Ix.Compile.Canon.Rules.compiler addresses sources classes stats ran),
    reordered_classes_agree classes
      (sorted_classes_agree Ix.Compile.Canon.Rules.compiler rfl addresses congruent sources keys classes stats ran)⟩

def ConstructorPositions (source : MutConst) : Prop :=
  ∀ index, (inside : index < source.ctors.size) → source.ctors[index].cidx = index

def readRows (store : Kernel.Reader.Store) (rows : List (Name × Ixon.Constant)) :
    List (Name × Option (Kernel.ConstRef Address)) :=
  rows.map fun row => (row.1, Kernel.Reader.resolveSource store (Address.blake3 (Ixon.ser row.2)) row.2)

def sourceReferences (owner : Address) (index : Nat) (source : MutConst) :
    List (Name × Option (Kernel.ConstRef Address)) :=
  (source.name, some (.member owner index)) :: source.ctors.toList.zipIdx.map fun (ctor, position) =>
    (ctor.cnst.name, some (.ctor owner index position))

def expectedReferences (owner : Address) (sources : List (List MutConst)) :
    List (Name × Option (Kernel.ConstRef Address)) :=
  sources.zipIdx.flatMap fun (members, index) => members.flatMap (sourceReferences owner index)

theorem source_rows_resolve (store : Kernel.Reader.Store) (owner : Address) (block : Ixon.Constant)
    (members : Array Ixon.MutConst) (source : MutConst) (target : Ixon.MutConst) (index : Nat)
    (stored : store owner = some block) (info : block.info = .muts members) (wire : block.wireWF)
    (member : members[index]? = some target)
    (shape : ProjectionLayout.memberShape target = ProjectionLayout.sourceShape source)
    (positions : ConstructorPositions source) :
    readRows store (sourceRows owner index.toUInt64 source) = sourceReferences owner index source := by
  have memberBounds : index < members.size := (Array.getElem?_eq_some_iff.mp member).1
  have membersWire : (.muts members : Ixon.ConstantInfo).wireWF := info ▸ wire.1
  have indexExact := DeclarationHeaders.exact_header index (Nat.lt_trans memberBounds membersWire.1)
  have targetWire := membersWire.2 target (Array.mem_of_getElem? member)
  have main := member_resolves store owner block members source target index.toUInt64 stored info
    (by simpa only [indexExact] using member) shape
  have mainExact : Kernel.Reader.resolveSource store
      (Address.blake3 (Ixon.ser (memberProjection owner index.toUInt64 source)))
      (memberProjection owner index.toUInt64 source) = some (.member owner index) := by
    simpa only [indexExact] using main
  simp only [readRows, sourceRows, sourceReferences, List.map_cons, mainExact]
  congr 1
  cases source with
  | defn value | recr value => rfl
  | indc value =>
    cases target with
    | defn value | recr value => cases shape
    | indc target =>
      have indices := ProjectionLayout.MemberShape.indc.inj shape
      have length : target.ctors.size = value.ctors.size := by simpa using congrArg List.length indices
      simp only [MutConst.ctors, List.map_map]
      apply List.map_congr_left
      rintro ⟨ctor, position⟩ present
      have inside : position < value.ctors.size := by simpa using List.snd_lt_of_mem_zipIdx present
      have capacity : value.ctors.size < UInt64.size := length ▸ targetWire.2.1
      have positionExact := DeclarationHeaders.exact_header position (Nat.lt_trans inside capacity)
      have resolves := constructor_resolves store owner block members value target index.toUInt64 position.toUInt64
        stored info (by simpa only [indexExact] using member) indices
        (by simpa only [positionExact] using inside)
        (by simpa only [positionExact, MutConst.ctors] using positions position inside)
      simpa only [constructorProjection, indexExact, positionExact, Function.comp_def] using
        congrArg (fun result => (ctor.cnst.name, result)) resolves

/-- Every generated mutual projection resolves to its source-indexed logical
reference. The source layout and installed block are explicit; admission and
source-domain discharge are not assumed to follow from a codec theorem. -/
theorem build_resolves (store : Kernel.Reader.Store) (owner : Address) (block : Ixon.Constant)
    (sources : List (List MutConst)) (targets : Array Ixon.MutConst)
    (metadata : Array (Name × Ixon.ConstantMeta))
    (stored : store owner = some block) (info : block.info = .muts targets) (wire : block.wireWF)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : ClassesAgree sources)
    (shape : targets.toList.map ProjectionLayout.memberShape = (sources.filterMap List.head?).map ProjectionLayout.sourceShape)
    (positions : ∀ source ∈ sources.flatten, ConstructorPositions source) :
    readRows store (logicalRows (buildMutualProjections sources owner metadata)) = expectedReferences owner sources := by
  rw [build_rows]
  simp only [readRows, expectedRows, expectedReferences, List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  rintro ⟨members, index⟩ present
  have inside : index < sources.length := by simpa using List.snd_lt_of_mem_zipIdx present
  have classAt : sources[index] = members := by simpa using (List.fst_eq_of_mem_zipIdx present).symm
  have classPresent := List.fst_mem_of_mem_zipIdx present
  apply congrArg List.flatten
  apply List.map_congr_left
  intro source sourceIn
  obtain ⟨target, targetAt, sourceShape⟩ := class_member sources targets nonempty agree shape index inside source
    (by simpa only [classAt] using sourceIn)
  exact source_rows_resolve store owner block targets source target index stored info wire targetAt sourceShape
    (positions source (List.mem_flatten.mpr ⟨members, classPresent, sourceIn⟩))

end Ix.CompileCert.MutualProjections
