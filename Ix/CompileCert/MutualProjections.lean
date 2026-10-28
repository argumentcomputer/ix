import Ix.CompileCert.ProjectionLayout
import Ix.CompileCert.Canon.Ctx

/-! # A mutual block's projection rows

The compiler emits one member projection at each source member's index and
one constructor projection at each constructor position. These rows are
wire-valid and decode exactly. In a store holding the wire-valid block, they
resolve to the corresponding source-indexed references when the source
constructors declare their positions. A lone definition or recursor instead
registers its name directly to the standalone block.
-/

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

def expectedRows (owner : Address) (classes : List MutConst) : List (Ix.Name × Ixon.Constant) :=
  classes.zipIdx.flatMap fun (member, index) => sourceRows owner index.toUInt64 member

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

def indexedMemberStep (owner : Address) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta)
    (source : MutConst) (initial : Array Row × UInt64) : Id (ForInStep (Array Row × UInt64)) :=
  .yield ((memberStep owner initial.2 metadata source initial.1).value, initial.2 + 1)

theorem members_rows (sources : List MutConst) (initial : Array Row) (offset : Nat)
    (owner : Address) (metadata : Std.HashMap Ix.Name Ixon.ConstantMeta) :
    logicalRows (forIn (m := Id) sources (initial, offset.toUInt64) (indexedMemberStep owner metadata)).1 =
      logicalRows initial ++ (sources.zipIdx offset).flatMap (fun (member, index) =>
        sourceRows owner index.toUInt64 member) := by
  induction sources generalizing initial offset with
  | nil => change logicalRows initial = logicalRows initial ++ []; simp
  | cons source rest ih =>
    rw [List.forIn_cons]
    change logicalRows (forIn (m := Id) rest
      ((memberStep owner offset.toUInt64 metadata source initial).value, offset.toUInt64 + 1)
      (indexedMemberStep owner metadata)).1 = _
    have next : offset.toUInt64 + 1 = (offset + 1).toUInt64 := by simp
    rw [next, ih, memberStep_rows]
    simp [List.zipIdx_cons, List.append_assoc]

/-- **The mutual wrapper's rows**: the compiler emits exactly these
anonymous projections under the source registration names, independently
of the metadata values. -/
theorem build_rows (sources : List MutConst) (owner : Address)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) :
    logicalRows (buildMutualProjections sources owner metadata) = expectedRows owner sources := by
  let lookup : Std.HashMap Ix.Name Ixon.ConstantMeta :=
    metadata.foldl (fun table pair => table.insert pair.1 pair.2) {}
  change logicalRows (forIn (m := Id) sources (#[], (0 : UInt64)) (indexedMemberStep owner lookup)).1 = _
  simpa [expectedRows, logicalRows] using members_rows sources #[] 0 owner lookup

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

/-- A collapsed block registers each source name to the block itself. -/
theorem standalone_rows (sources : List MutConst) (block : Ixon.Constant)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) :
    logicalRows (buildStandaloneMutualProjections sources block metadata) =
      sources.map (fun source => (source.name, block)) := by
  let lookup : Std.HashMap Ix.Name Ixon.ConstantMeta :=
    metadata.foldl (fun table pair => table.insert pair.1 pair.2) {}
  change logicalRows (forIn (m := Id) sources #[] (fun source rows =>
    .yield (rows.push (source.name, block, (lookup.get? source.name).getD .empty)))) = _
  simpa [logicalRows] using pushed_rows sources #[]
    (fun source => (source.name, block, (lookup.get? source.name).getD .empty))

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

theorem build_rows_wire (sources : List MutConst) (owner : Address) (width : owner.hash.size = 32)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildMutualProjections sources owner metadata) : row.2.1.wireWF := by
  have logical : (row.1, row.2.1) ∈ logicalRows (buildMutualProjections sources owner metadata) :=
    List.mem_map.mpr ⟨row, by simpa using present, rfl⟩
  rw [build_rows, expectedRows] at logical
  obtain ⟨⟨source, index⟩, _, generated⟩ := List.mem_flatMap.mp logical
  exact source_rows_wire owner width index.toUInt64 source (row.1, row.2.1) generated

theorem build_rows_codec (sources : List MutConst) (owner : Address) (width : owner.hash.size = 32)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (row : Row)
    (present : row ∈ buildMutualProjections sources owner metadata) :
    Ixon.deConstant (Ixon.ser row.2.1) = .ok row.2.1 :=
  Ixon.Verify.deConstant_serConstant row.2.1 (build_rows_wire sources owner width metadata row present)

theorem standalone_rows_wire (sources : List MutConst) (block : Ixon.Constant) (wire : block.wireWF)
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

theorem build_projection_wire (limits : Ix.Sharing.Exact.Limits) (classes : List MutConst)
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

theorem finish_projection_wire (classes : List MutConst) (members : Array Ixon.MutConst)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta)) :
    Emission.Yields (finishMutualCompilation classes members metadata)
      (fun output => output.block.wireWF → ProjectionWire output) := by
  intro context before output after ran main
  obtain ⟨rfl, _, built⟩ := ProjectionLayout.finish_mutual_ok context classes members metadata ran
  exact build_projection_wire _ classes members metadata _ output built main

theorem payload_projection_wire (sources : List MutConst) :
    Emission.Yields (compileMutualPayload sources) (fun output => output.block.wireWF → ProjectionWire output) := by
  unfold compileMutualPayload
  exact Emission.Yields.bindAny (compileMutConsts sources) fun compiled =>
    finish_projection_wire sources compiled.1 compiled.2.2

theorem mutual_projection_wire (sources : List MutConst) :
    Emission.Yields (compileMutualBlock sources) (fun output => output.block.wireWF → ProjectionWire output) :=
  ProjectionLayout.mutual_block _ sources (payload_projection_wire sources)

/-- **A mutual block and all its projections decode exactly**: under an
environment without Pass 3 records, a successful compile from a state
whose tables are on the wire. -/
theorem mutual_codec (context : CompileEnv × BlockEnv)
    (sources : List MutConst) {before after : BlockState} {output : BlockResult}
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output ∧ ProjectionWire output ∧
      ∀ row ∈ output.projections, Ixon.deConstant (Ixon.ser row.2.1) = .ok row.2.1 := by
  have main := EmissionDispatch.mutualBlock_codec context sources wire ran
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

theorem selected_member (sources : List MutConst) (targets : Array Ixon.MutConst)
    (shape : targets.toList.map memberShape = sources.map sourceShape)
    (index : Nat) (source : MutConst) (sourceAt : sources[index]? = some source) :
    ∃ target, targets[index]? = some target ∧ memberShape target = sourceShape source := by
  have atIndex := congrArg (fun values : List MemberShape => values[index]?) shape
  simp only [List.getElem?_map, Array.getElem?_toList, sourceAt, Option.map_some] at atIndex
  cases targetAt : targets[index]? with
  | none => simp [targetAt] at atIndex
  | some target => exact ⟨target, targetAt, Option.some.inj (by simpa [targetAt] using atIndex)⟩

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

def expectedReferences (owner : Address) (sources : List MutConst) :
    List (Ix.Name × Option (Ix.Kernel.ConstRef Address)) :=
  sources.zipIdx.flatMap fun (member, index) => sourceReferences owner index member

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

/-- Every generated projection resolves to its source member or constructor
at the same position, in any store holding the wire-valid block. -/
theorem build_resolves (store : Store) (owner : Address) (block : Ixon.Constant)
    (sources : List MutConst) (targets : Array Ixon.MutConst)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta))
    (stored : store owner = some block) (info : block.info = .muts targets) (wire : block.wireWF)
    (shape : targets.toList.map memberShape = sources.map sourceShape)
    (positions : ∀ source ∈ sources, ConstructorPositions source) :
    readRows store (logicalRows (buildMutualProjections sources owner metadata)) =
      expectedReferences owner sources := by
  rw [build_rows]
  simp only [readRows, expectedRows, expectedReferences, List.map_flatMap]
  apply congrArg List.flatten
  apply List.map_congr_left
  rintro ⟨source, index⟩ present
  have sourceAt : sources[index]? = some source := List.mem_zipIdx_iff_getElem?.mp present
  obtain ⟨target, targetAt, sourceShape⟩ := selected_member sources targets shape index source sourceAt
  exact source_rows_resolve store owner block targets source target index stored info wire targetAt sourceShape
    (positions source (List.fst_mem_of_mem_zipIdx present))

end Ix.CompileCert.MutualProjections
