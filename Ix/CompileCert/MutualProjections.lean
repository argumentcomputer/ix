import Ix.CompileCert.ProjectionLayout
import Ix.CompileCert.Canon.EqSound

/-! # A mutual block's projection rows: what they are, their codec, what they read as

CT-15's `MutualProjections` (R9a), ported from the donor `a9cf3607`:

* `build_rows`: the mutual wrapper's projection rows are exactly, class by
  class and member by member, a member projection (`dPrj`/`iPrj`/`rPrj` at
  the class index) and, for an inductive, one constructor projection per
  constructor position (`cPrj`), registered under the source names;
  `standalone_rows`: a collapsed lone definition or recursor registers every
  source name to the block itself;
* their codec: every row is a wire-valid projection (`build_rows_wire`,
  `standalone_rows_wire`), so it decodes exactly; `mutual_codec`: a
  successful mutual block decodes exactly and so do all its projections;
* `build_resolves`: in a store holding the block, every row resolves under
  the certified reader to its source-indexed reference (the member of the
  class index, or the constructor at its position), given the class shapes
  agree within each class (`ClassesAgree`) and the source constructors
  declare their positions (`ConstructorPositions`).

Adapted: `Address.admissionHash` for `Address.blake3`, the mutual
finisher's inversion (`ProjectionLayout.finish_mutual_ok`), dispatch under
`surgeryFree` (until CQ3.5).

R9b discharges `ClassesAgree` for the compiler's classes (`sort_classes`):
the donor's comparator lemmas (`ctor_compare_index` … `production_classes`)
become `match_shape` over `Canon.ConstMatch` and `sorted_classes_agree` over
`Canon.sortClasses_match` (CS-01's coarsest partition and `eq` soundness,
re-derived for `Ix.Compile.Canon.sortClasses` since CQ2.18). The driver's
`orderRecursorFamily` step between the sort and the compile permutes the
classes, so the premises carry over (`MutualArtifact.mutual_ordered_correct`,
N-READS N5 a). -/

namespace Ix.CompileCert.MutualProjections

open Ix.CompileM Ix.CompileCert
open Ix.CompileCert.ProjectionLayout (memberShape sourceShape MemberShape)
open Ix.Kernel.Reader (Store resolveSource emptyTables)

abbrev Row := Ix.Name × Ixon.Constant × Ixon.ConstantMeta

def logicalRows (rows : Array Row) : List (Ix.Name × Ixon.Constant) :=
  rows.toList.map fun row => (row.1, row.2.1)

def memberProjection (owner : Address) (index : UInt64) (source : MutConst) : Ixon.Constant :=
  ⟨match source with
    | .defn _ => .dPrj ⟨index, owner⟩
    | .indc _ => .iPrj ⟨index, owner⟩
    | .recr _ => .rPrj ⟨index, owner⟩, #[], #[], #[]⟩

def constructorProjection (owner : Address) (index ctorIndex : UInt64) : Ixon.Constant :=
  ⟨.cPrj ⟨index, ctorIndex, owner⟩, #[], #[], #[]⟩

def sourceRows (owner : Address) (index : UInt64) (source : MutConst) : List (Ix.Name × Ixon.Constant) :=
  (source.name, memberProjection owner index source) ::
    source.ctors.toList.zipIdx.map fun (ctor, ctorIndex) =>
      (ctor.cnst.name, constructorProjection owner index ctorIndex.toUInt64)

def expectedRows (owner : Address) (classes : List (List MutConst)) : List (Ix.Name × Ixon.Constant) :=
  classes.zipIdx.flatMap fun (members, index) =>
    members.flatMap (sourceRows owner index.toUInt64)

/-! ## The rows -/

theorem indexed_rows (sources : List α) (initial : Array Row) (offset : Nat)
    (name : α → Ix.Name) (emit : UInt64 → α → Ixon.Constant) (metadata : α → Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources (initial, offset.toUInt64) (fun source state =>
      .yield (state.1.push (name source, emit state.2 source, metadata source), state.2 + 1))).1 =
      logicalRows initial ++
        (sources.zipIdx offset).map (fun (source, index) => (name source, emit index.toUInt64 source)) := by
  induction sources generalizing initial offset with
  | nil => change logicalRows initial = logicalRows initial ++ []; simp
  | cons source rest ih =>
    rw [List.forIn_cons]
    change logicalRows (forIn (m := Id) rest
      (initial.push (name source, emit offset.toUInt64 source, metadata source), offset.toUInt64 + 1)
      (fun source state => .yield (state.1.push (name source, emit state.2 source, metadata source),
        state.2 + 1))).1 = _
    have next : offset.toUInt64 + 1 = (offset + 1).toUInt64 := by simp
    rw [next, ih]
    simp [logicalRows, List.zipIdx_cons, List.append_assoc]

theorem constructor_rows (sources : Array ConstructorVal) (initial : Array Row)
    (owner : Address) (index : UInt64) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources (initial, (0 : UInt64)) (fun source state =>
      .yield (state.1.push (source.cnst.name, constructorProjection owner index state.2,
        (metadata.get? source.cnst.name).getD .empty), state.2 + 1))).1 =
      logicalRows initial ++ sources.toList.zipIdx.map (fun (source, ctorIndex) =>
        (source.cnst.name, constructorProjection owner index ctorIndex.toUInt64)) := by
  rw [← Array.forIn_toList]
  exact indexed_rows sources.toList initial 0 (·.cnst.name)
    (fun ctorIndex _ => constructorProjection owner index ctorIndex)
    (fun source => (metadata.get? source.cnst.name).getD .empty)

def memberStep (owner : Address) (index : UInt64) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta)
    (source : MutConst) (initial : Array Row) : Id (ForInStep (Array Row)) :=
  let rows := initial.push (source.name, memberProjection owner index source,
    (metadata.get? source.name).getD .empty)
  match source with
  | .indc value =>
    .yield (forIn (m := Id) value.ctors (rows, (0 : UInt64)) (fun ctor state =>
      .yield (state.1.push (ctor.cnst.name, constructorProjection owner index state.2,
        (metadata.get? ctor.cnst.name).getD .empty), state.2 + 1))).1
  | _ => .yield rows

theorem memberStep_yield (owner : Address) (index : UInt64) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta)
    (source : MutConst) (initial : Array Row) :
    memberStep owner index metadata source initial =
      .yield (memberStep owner index metadata source initial).value := by
  cases source <;> rfl

theorem memberStep_rows (owner : Address) (index : UInt64) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta)
    (source : MutConst) (initial : Array Row) :
    logicalRows (memberStep owner index metadata source initial).value =
      logicalRows initial ++ sourceRows owner index source := by
  cases source with
  | defn value | recr value => simp [memberStep, sourceRows, logicalRows, MutConst.ctors]
  | indc value =>
    change logicalRows (forIn (m := Id) value.ctors
      (initial.push (value.name, memberProjection owner index (.indc value),
        (metadata.get? value.name).getD .empty), (0 : UInt64))
      (fun ctor state => .yield (state.1.push (ctor.cnst.name, constructorProjection owner index state.2,
        (metadata.get? ctor.cnst.name).getD .empty), state.2 + 1))).1 = _
    rw [constructor_rows]
    simp [sourceRows, logicalRows, MutConst.ctors, MutConst.name, List.append_assoc]

theorem members_rows (sources : List MutConst) (initial : Array Row)
    (owner : Address) (index : UInt64) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta) :
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

def classStep (owner : Address) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta)
    (sources : List MutConst) (initial : Array Row × UInt64) : Id (ForInStep (Array Row × UInt64)) :=
  .yield (forIn (m := Id) sources initial.1 (memberStep owner initial.2 metadata), initial.2 + 1)

theorem classes_rows (sources : List (List MutConst)) (initial : Array Row) (offset : Nat)
    (owner : Address) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources (initial, offset.toUInt64) (classStep owner metadata)).1 =
      logicalRows initial ++ (sources.zipIdx offset).flatMap (fun (members, index) =>
        members.flatMap (sourceRows owner index.toUInt64)) := by
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

/-- **The mutual wrapper's rows**: the compiler emits exactly these
anonymous projections under the source registration names, independently
of the metadata values. -/
theorem build_rows (sources : List (List MutConst)) (owner : Address)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) :
    logicalRows (buildMutualProjections sources owner metadata) = expectedRows owner sources := by
  let lookup : Std.HashMap Ix.Name Ixon.ConstantMeta :=
    metadata.foldl (fun table pair => table.insert pair.1 pair.2) {}
  change logicalRows (forIn (m := Id) sources (#[], (0 : UInt64)) (classStep owner lookup)).1 = _
  simpa [expectedRows, logicalRows] using classes_rows sources #[] 0 owner lookup

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
    (block : Ixon.Constant) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta) :
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

/-- **A collapsed block's rows** register every source name to the block
itself. -/
theorem standalone_rows (sources : List (List MutConst)) (block : Ixon.Constant)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) :
    logicalRows (buildStandaloneMutualProjections sources block metadata) =
      sources.flatten.map (fun source => (source.name, block)) := by
  let lookup : Std.HashMap Ix.Name Ixon.ConstantMeta :=
    metadata.foldl (fun table pair => table.insert pair.1 pair.2) {}
  change logicalRows (forIn (m := Id) sources #[] (fun members rows =>
    .yield (forIn (m := Id) members rows (fun source rows =>
      .yield (rows.push (source.name, block, (lookup.get? source.name).getD .empty)))))) = _
  simpa [logicalRows] using standalone_classes_rows sources #[] block lookup

/-! ## Wire validity and codec -/

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
    (row : Ix.Name × Ixon.Constant) (present : row ∈ sourceRows owner index source) : row.2.wireWF := by
  rcases List.mem_cons.mp present with rfl | rest
  · exact member_wire owner width index source
  · obtain ⟨⟨ctor, ctorIndex⟩, _, rfl⟩ := List.mem_map.mp rest
    exact constructor_wire owner width index ctorIndex.toUInt64

theorem build_rows_wire (sources : List (List MutConst)) (owner : Address) (width : owner.hash.size = 32)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildMutualProjections sources owner metadata) : row.2.1.wireWF := by
  have logical : (row.1, row.2.1) ∈ logicalRows (buildMutualProjections sources owner metadata) :=
    List.mem_map.mpr ⟨row, by simpa using present, rfl⟩
  rw [build_rows, expectedRows] at logical
  obtain ⟨⟨members, index⟩, _, inClass⟩ := List.mem_flatMap.mp logical
  obtain ⟨source, _, generated⟩ := List.mem_flatMap.mp inClass
  exact source_rows_wire owner width index.toUInt64 source (row.1, row.2.1) generated

theorem build_rows_codec (sources : List (List MutConst)) (owner : Address) (width : owner.hash.size = 32)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildMutualProjections sources owner metadata) :
    Ixon.deConstant (Ixon.ser row.2.1) = .ok row.2.1 :=
  Ixon.Verify.deConstant_serConstant row.2.1 (build_rows_wire sources owner width metadata row present)

theorem standalone_rows_wire (sources : List (List MutConst)) (block : Ixon.Constant) (wire : block.wireWF)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildStandaloneMutualProjections sources block metadata) : row.2.1.wireWF := by
  have logical : (row.1, row.2.1) ∈ logicalRows (buildStandaloneMutualProjections sources block metadata) :=
    List.mem_map.mpr ⟨row, by simpa using present, rfl⟩
  rw [standalone_rows] at logical
  obtain ⟨source, _, same⟩ := List.mem_map.mp logical
  have sameBlock := congrArg Prod.snd same
  change block = row.2.1 at sameBlock
  exact sameBlock ▸ wire

/-- Every projection row of a block result is wire-valid. -/
def ProjectionWire (output : BlockResult) : Prop := ∀ row ∈ output.projections, row.2.1.wireWF

theorem build_projection_wire (limits : Ix.Sharing.Exact.Limits) (classes : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (state : BlockState)
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
    exact build_rows_wire classes (Address.admissionHash (Ixon.ser block))
      (Ixon.Authenticated.admissionHash_width _) metadata

theorem finish_projection_wire (classes : List (List MutConst)) (members : Array Ixon.MutConst)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) :
    Emission.Yields (finishMutualCompilation classes members metadata)
      (fun output => output.block.wireWF → ProjectionWire output) := by
  intro context before output after ran main
  obtain ⟨rfl, _, built⟩ := ProjectionLayout.finish_mutual_ok context classes members metadata ran
  exact build_projection_wire _ classes members metadata _ output built main

theorem payload_projection_wire (sources : List (List MutConst)) :
    Emission.Yields (compileMutualPayload sources) (fun output => output.block.wireWF → ProjectionWire output) := by
  unfold compileMutualPayload
  exact Emission.Yields.bindAny (compileMutConsts sources) fun compiled =>
    finish_projection_wire sources compiled.1 compiled.2.2

theorem mutual_projection_wire (sources : List (List MutConst)) :
    Emission.Yields (compileMutualBlock sources) (fun output => output.block.wireWF → ProjectionWire output) :=
  ProjectionLayout.mutual_block _ sources (payload_projection_wire sources)

/-- **A mutual block and all its projections decode exactly**: under an
environment without Pass 3 records, a successful compile from a state
whose tables are on the wire. -/
theorem mutual_codec (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (sources : List (List MutConst)) {before after : BlockState} {output : BlockResult}
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output ∧ ProjectionWire output ∧
      ∀ row ∈ output.projections, Ixon.deConstant (Ixon.ser row.2.1) = .ok row.2.1 := by
  have main := EmissionDispatch.mutualBlock_codec context free sources wire ran
  have projections := mutual_projection_wire sources context before output after ran main.1
  exact ⟨main, projections, fun row present => Ixon.Verify.deConstant_serConstant row.2.1 (projections row present)⟩

/-! ## The rows resolve -/

theorem member_resolves (store : Store) (owner : Address) (block : Ixon.Constant)
    (members : Array Ixon.MutConst) (source : MutConst) (target : Ixon.MutConst) (index : UInt64)
    (stored : store owner = some block) (info : block.info = .muts members)
    (member : members[index.toNat]? = some target)
    (shape : memberShape target = sourceShape source) :
    resolveSource store (Address.admissionHash (Ixon.ser (memberProjection owner index source)))
      (memberProjection owner index source) = some (.member owner index.toNat) := by
  cases source <;> cases target <;>
    simp_all [memberShape, sourceShape, memberProjection, resolveSource, emptyTables, guard]

theorem constructor_resolves (store : Store) (owner : Address) (block : Ixon.Constant)
    (members : Array Ixon.MutConst) (source : Ix.Ind) (target : Ixon.Inductive) (index position : UInt64)
    (stored : store owner = some block) (info : block.info = .muts members)
    (member : members[index.toNat]? = some (.indc target))
    (indices : target.ctors.toList.map (fun ctor => ctor.cidx.toNat) = source.ctors.toList.map (·.cidx))
    (inside : position.toNat < source.ctors.size)
    (sourceIndex : source.ctors[position.toNat].cidx = position.toNat) :
    resolveSource store (Address.admissionHash (Ixon.ser (constructorProjection owner index position)))
      (constructorProjection owner index position) = some (.ctor owner index.toNat position.toNat) := by
  have length : target.ctors.size = source.ctors.size := by simpa using congrArg List.length indices
  have targetInside : position.toNat < target.ctors.size := by omega
  have row := congrArg (fun values : List Nat => values[position.toNat]?) indices
  simp only [List.getElem?_map, Array.getElem?_toList] at row
  rw [Array.getElem?_eq_getElem targetInside, Array.getElem?_eq_getElem inside] at row
  have naturalIndex := (Option.some.inj row).trans sourceIndex
  have converted : target.ctors[position.toNat].cidx = position := UInt64.toNat_inj.mp naturalIndex
  simp [constructorProjection, resolveSource, emptyTables,
    stored, info, member, Array.getElem?_eq_getElem targetInside, converted, guard]

theorem selected_member (sources : List (List MutConst)) (targets : List Ixon.MutConst)
    (nonempty : ∀ members ∈ sources, members ≠ [])
    (shape : targets.map memberShape = (sources.filterMap List.head?).map sourceShape)
    (index : Nat) (inside : index < sources.length) :
    ∃ selected rest target, sources[index]? = some (selected :: rest) ∧ targets[index]? = some target ∧
      memberShape target = sourceShape selected := by
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
        have equal : memberShape target = sourceShape selected ∧
            targets.map memberShape = (remaining.filterMap List.head?).map sourceShape := by
          simpa [List.filterMap] using shape
        cases index with
        | zero => exact ⟨selected, rest, target, rfl, rfl, equal.1⟩
        | succ index =>
          have tailNonempty : ∀ members ∈ remaining, members ≠ [] := fun members present =>
            nonempty members (by simp [present])
          obtain ⟨next, suffix, member, sourceAt, targetAt, shapeAt⟩ :=
            ih targets tailNonempty equal.2 index (by simpa using inside)
          exact ⟨next, suffix, member, by simpa using sourceAt, by simpa using targetAt, shapeAt⟩

/-- The class-specific condition needed for every alias of a class, beyond
the compiled representative's shape: the members of a class have one shape.
(The compiler's classes satisfy it: `sort_classes`, R9b.) -/
def ClassesAgree (sources : List (List MutConst)) : Prop :=
  ∀ members ∈ sources, ∀ left ∈ members, ∀ right ∈ members, sourceShape left = sourceShape right

theorem class_member (sources : List (List MutConst)) (targets : Array Ixon.MutConst)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : ClassesAgree sources)
    (shape : targets.toList.map memberShape = (sources.filterMap List.head?).map sourceShape)
    (index : Nat) (inside : index < sources.length) (source : MutConst) (present : source ∈ sources[index]) :
    ∃ target, targets[index]? = some target ∧ memberShape target = sourceShape source := by
  obtain ⟨selected, rest, target, sourceAt, targetAt, shapeAt⟩ :=
    selected_member sources targets.toList nonempty shape index inside
  have sameClass : sources[index] = selected :: rest := by
    rw [List.getElem?_eq_getElem inside] at sourceAt
    exact Option.some.inj sourceAt
  have classPresent : sources[index] ∈ sources := List.getElem_mem inside
  have sameShape := agree sources[index] classPresent selected (by simp [sameClass]) source present
  exact ⟨target, by simpa using targetAt, shapeAt.trans sameShape⟩

/-- A source member's constructors declare their own positions. -/
def ConstructorPositions (source : MutConst) : Prop :=
  ∀ index, (inside : index < source.ctors.size) → source.ctors[index].cidx = index

/-- What the certified reader resolves each row's record to. -/
def readRows (store : Store) (rows : List (Ix.Name × Ixon.Constant)) :
    List (Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  rows.map fun row => (row.1, resolveSource store (Address.admissionHash (Ixon.ser row.2)) row.2)

def sourceReferences (owner : Address) (index : Nat) (source : MutConst) :
    List (Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  (source.name, some (.member owner index)) :: source.ctors.toList.zipIdx.map fun (ctor, position) =>
    (ctor.cnst.name, some (.ctor owner index position))

def expectedReferences (owner : Address) (sources : List (List MutConst)) :
    List (Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  sources.zipIdx.flatMap fun (members, index) => members.flatMap (sourceReferences owner index)

theorem source_rows_resolve (store : Store) (owner : Address) (block : Ixon.Constant)
    (members : Array Ixon.MutConst) (source : MutConst) (target : Ixon.MutConst) (index : Nat)
    (stored : store owner = some block) (info : block.info = .muts members) (wire : block.wireWF)
    (member : members[index]? = some target)
    (shape : memberShape target = sourceShape source)
    (positions : ConstructorPositions source) :
    readRows store (sourceRows owner index.toUInt64 source) = sourceReferences owner index source := by
  have memberBounds : index < members.size := (Array.getElem?_eq_some_iff.mp member).1
  have membersWire : (Ixon.ConstantInfo.muts members).wireWF := info ▸ wire.1
  have indexExact := Emission.exact_header index (Nat.lt_trans memberBounds membersWire.1)
  have targetWire := membersWire.2 target (Array.mem_of_getElem? member)
  have main := member_resolves store owner block members source target index.toUInt64 stored info
    (by simpa only [indexExact] using member) shape
  have mainExact : resolveSource store
      (Address.admissionHash (Ixon.ser (memberProjection owner index.toUInt64 source)))
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
      have indices := MemberShape.indc.inj shape
      have length : target.ctors.size = value.ctors.size := by simpa using congrArg List.length indices
      simp only [MutConst.ctors, List.map_map]
      apply List.map_congr_left
      rintro ⟨ctor, position⟩ present
      have inside : position < value.ctors.size := by simpa using List.snd_lt_of_mem_zipIdx present
      have capacity : value.ctors.size < UInt64.size := length ▸ targetWire.2.1
      have positionExact := Emission.exact_header position (Nat.lt_trans inside capacity)
      have resolves := constructor_resolves store owner block members value target index.toUInt64
        position.toUInt64 stored info (by simpa only [indexExact] using member) indices
        (by simpa only [positionExact] using inside)
        (by simpa only [positionExact, MutConst.ctors] using positions position inside)
      simpa only [constructorProjection, indexExact, positionExact, Function.comp_def] using
        congrArg (fun result => (ctor.cnst.name, result)) resolves

/-- **Every generated mutual projection resolves to its source-indexed
reference**: in a store holding the wire-valid block, the rows read as the
class index's member (and its constructors at their positions), given
non-empty classes whose members agree in shape and source constructors that
declare their positions. -/
theorem build_resolves (store : Store) (owner : Address) (block : Ixon.Constant)
    (sources : List (List MutConst)) (targets : Array Ixon.MutConst)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta))
    (stored : store owner = some block) (info : block.info = .muts targets) (wire : block.wireWF)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : ClassesAgree sources)
    (shape : targets.toList.map memberShape = (sources.filterMap List.head?).map sourceShape)
    (positions : ∀ source ∈ sources.flatten, ConstructorPositions source) :
    readRows store (logicalRows (buildMutualProjections sources owner metadata)) =
      expectedReferences owner sources := by
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


/-! ## The class sort's classes agree (R9b) -/

theorem ctor_match_indices {c : Ix.Compile.Canon.CmpCtx} {xl yl : List Ix.Name} :
    ∀ {left right : List Ix.ConstructorVal}, List.Forall₂ (Canon.CtorMatch c xl yl) left right →
      left.map (·.cidx) = right.map (·.cidx)
  | _, _, .nil => rfl
  | _, _, .cons head tail => by simp only [List.map_cons, head.cidx, ctor_match_indices tail]

/-- Two constants the comparator identifies have one shape (the donor's
`const_compare_shape`, through `Canon.ConstMatch`). -/
theorem match_shape {c : Ix.Compile.Canon.CmpCtx} {left right : MutConst}
    (matched : Canon.ConstMatch c left right) : sourceShape left = sourceShape right := by
  cases left <;> cases right <;> simp only [Canon.ConstMatch] at matched
  · rfl
  · exact congrArg MemberShape.indc (ctor_match_indices matched.ctors)
  · rfl

/-- **The class sort's classes agree in shape**: two members of one class
of `sortClasses` match under the classes' context (`Canon.sortClasses_match`,
from the coarsest partition's consistency), so they have one shape. -/
theorem sorted_classes_agree (rules : Ix.Compile.Canon.Rules) {addresses : Ix.Name → Option Address}
    {sources : List MutConst} (keys : Canon.KeysDistinct sources)
    {classes : List (List MutConst)} {stats : Ix.Compile.Canon.SortStats}
    (ran : Ix.Compile.Canon.sortClasses rules addresses sources = .ok (classes, stats)) :
    ClassesAgree classes := by
  intro members present left leftIn right rightIn
  by_cases same : left = right
  · exact same ▸ rfl
  · exact match_shape (Canon.sortClasses_match rules keys ran members present left leftIn
      right rightIn same)

/-- **The compiler's class sort returns a partition of its members whose
classes agree in shape** (R9b: `ClassesAgree` discharged), for members whose
member and constructor names are pairwise distinct. -/
theorem sort_classes (sources : List MutConst) (keys : Canon.KeysDistinct sources) :
    Emission.Yields (sortConsts sources)
      (fun classes => Canon.Partition classes sources ∧ ClassesAgree classes) := by
  intro context before classes after ran
  obtain ⟨-, addresses, stats, sorted⟩ := ProjectionLayout.sort_run sources ran
  exact ⟨(Canon.sortClasses_coarsest _ keys sorted).1, sorted_classes_agree _ keys sorted⟩

end Ix.CompileCert.MutualProjections
