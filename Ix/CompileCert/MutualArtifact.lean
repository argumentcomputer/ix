import Ix.CompileCert.MutualProjections

/-! # A mutual block's artifact: decoded, and its rows read as their sources

CT-15's `MutualArtifact` (R9a), the block half, ported from the donor
`a9cf3607`. A mutual block either keeps the mutual wrapper (its rows are
`buildMutualProjections`') or collapses a lone definition or recursor to a
standalone record (every source name registered to the block itself);
`build_cases` says which, with the block's address. In both cases the rows
read under the certified reader, in any store holding the wire-valid block,
as the source-indexed references (`build_resolves`), and
`mutual_correct` composes it with the codec: under an environment without
Pass 3 records, a successful mutual block from a state whose tables are on
the wire decodes exactly, its projections decode exactly, and its rows read
as `expectedReferences`. `mutual_sorted_correct` (R9b) is the driver's two
steps, `sortConsts` then `compileMutualBlock`, with `mutual_correct`'s class
premises (non-empty classes, `ClassesAgree`) discharged by the sort;
`mutual_ordered_correct` (N-READS N5 a) is the driver's actual three, with
`orderRecursorFamily` between them, a permutation of the classes
(`orderRecursorFamily_perm`) that keeps those premises.

Adapted: `Address.admissionHash`, the write-back through `erase`
(`writeback_standalone`), the mutual finisher's inversion, `surgeryFree`
(until CQ3.5). Not ported here (R13): the donor's `published_*` and
`compile_merge_references`, which are about the driver's merge
(`DriverAcc`, `mergeCompiledBlock`); CQ2.14 replaced the driver with the
pure wave fold, and they are re-derived against it with CT-09's merge
specification. -/

namespace Ix.CompileCert.MutualArtifact

open Ix.CompileM Ix.CompileCert
open Ix.CompileCert.ProjectionLayout (memberShape sourceShape MemberShape)
open Ix.CompileCert.MutualProjections (logicalRows expectedRows expectedReferences readRows)
open Ix.Kernel.Reader (Store resolveSource)

/-- A collapsed lone member: a definition or a recursor record. -/
def Standalone : Ixon.ConstantInfo → Prop
  | .defn _ | .recr _ => True
  | _ => False

theorem standalone_erase (info : Ixon.ConstantInfo) : Standalone (SharingRoots.erase info) ↔ Standalone info := by
  cases info <;> exact Iff.rfl

/-- The write-back keeps a standalone record standalone. -/
theorem writeback_standalone (source target : Ixon.ConstantInfo) (roots : Array Ixon.Expr)
    (standalone : Standalone source) (ran : Ix.Sharing.Exact.withRoots source roots = .ok target) :
    Standalone target :=
  (standalone_erase target).mp ((SharingRoots.withRoots_inv ran).2 ▸ (standalone_erase source).mpr standalone)

theorem sharing_standalone (limits : Ix.Sharing.Exact.Limits) (source : Ixon.ConstantInfo)
    (refs : Array Address) (univs : Array Ixon.Univ) (block : Ixon.Constant)
    (standalone : Standalone source) (ran : buildConstantWithSharing limits source refs univs = .ok block) :
    Standalone block.info :=
  (standalone_erase block.info).mp ((SharingRoots.build_roots (md := .anon) limits source refs univs block ran).1 ▸
    (standalone_erase source).mpr standalone)

theorem chosen_standalone (members : Array Ixon.MutConst) (info : Ixon.ConstantInfo)
    (chosen : standaloneMutConstInfo? members = some info) :
    Standalone info ∧ ∃ kind, (kind = MemberShape.defn ∨ kind = MemberShape.recr) ∧
      members.toList.map memberShape = [kind] := by
  rcases members with ⟨members⟩
  cases members with
  | nil => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
  | cons member rest =>
    cases rest with
    | cons next rest => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
    | nil =>
      cases member with
      | defn value =>
        change some (Ixon.ConstantInfo.defn value) = some info at chosen
        cases Option.some.inj chosen
        exact ⟨True.intro, .defn, Or.inl rfl, rfl⟩
      | indc value => change (none : Option Ixon.ConstantInfo) = some info at chosen; cases chosen
      | recr value =>
        change some (Ixon.ConstantInfo.recr value) = some info at chosen
        cases Option.some.inj chosen
        exact ⟨True.intro, .recr, Or.inr rfl, rfl⟩

/-- The mutual wrapper's case: the block's members have the payload's
shapes and the rows are the wrapper's projections. -/
def WrappedRows (sources : List (List MutConst)) (members : Array Ixon.MutConst) (output : BlockResult) : Prop :=
  ∃ targets metadata, output.block.info = .muts targets ∧
    targets.toList.map memberShape = members.toList.map memberShape ∧
    output.projections = buildMutualProjections sources output.blockAddr metadata

/-- The collapsed case: a lone definition or recursor, every source name
registered to the block itself. -/
def CollapsedRows (sources : List (List MutConst)) (members : Array Ixon.MutConst) (output : BlockResult) : Prop :=
  Standalone output.block.info ∧
    (∃ kind, (kind = MemberShape.defn ∨ kind = MemberShape.recr) ∧ members.toList.map memberShape = [kind]) ∧
    logicalRows output.projections = sources.flatten.map (fun source => (source.name, output.block))

/-- **The mutual builder's two cases**, with the block's address. -/
theorem build_cases (limits : Ix.Sharing.Exact.Limits) (sources : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (state : BlockState)
    (output : BlockResult) (ran : buildCompiledMutualBlock limits sources members metadata state = .ok output) :
    output.blockAddr = Address.admissionHash (Ixon.ser output.block) ∧
      (WrappedRows sources members output ∨ CollapsedRows sources members output) := by
  unfold buildCompiledMutualBlock at ran
  cases chosen : standaloneMutConstInfo? members with
  | some info =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    have selected := chosen_standalone members info chosen
    exact ⟨rfl, .inr ⟨sharing_standalone limits info state.refs state.univs block selected.1 built,
      selected.2, MutualProjections.standalone_rows sources block metadata⟩⟩
  | none =>
    simp only [chosen] at ran
    obtain ⟨block, built, returned⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases Except.ok.inj returned
    obtain ⟨targets, info, shape⟩ :=
      ProjectionLayout.sharing_mutual_shape limits members state.refs state.univs block built
    exact ⟨rfl, .inl ⟨targets, metadata, info, shape, rfl⟩⟩

theorem selected_length (sources : List (List MutConst)) (nonempty : ∀ members ∈ sources, members ≠ []) :
    (sources.filterMap List.head?).length = sources.length := by
  induction sources with
  | nil => rfl
  | cons members rest ih =>
    have first := nonempty members (by simp)
    have tail : ∀ members ∈ rest, members ≠ [] := fun members present => nonempty members (by simp [present])
    cases members with
    | nil => exact False.elim (first rfl)
    | cons member members => simpa [List.filterMap] using congrArg Nat.succ (ih tail)

theorem no_ctor_references (owner : Address) (index : Nat) (source : MutConst) (kind : MemberShape)
    (standalone : kind = .defn ∨ kind = .recr) (shape : sourceShape source = kind) :
    MutualProjections.sourceReferences owner index source = [(source.name, some (.member owner index))] := by
  rcases standalone with rfl | rfl
  all_goals cases source
  all_goals first | rfl | cases shape

theorem collapsed_references (owner : Address) (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (kind : MemberShape) (standalone : kind = .defn ∨ kind = .recr)
    (shape : (sources.filterMap List.head?).map sourceShape = [kind]) :
    expectedReferences owner sources = sources.flatten.map (fun source => (source.name, some (.member owner 0))) := by
  have length : sources.length = 1 := by
    have counted := congrArg List.length shape
    simpa only [List.length_map, selected_length sources nonempty, List.length_cons, List.length_nil] using counted
  cases sources with
  | nil => simp at length
  | cons members rest =>
    cases rest with
    | cons other rest => simp at length
    | nil =>
      have firstNonempty := nonempty members (by simp)
      cases members with
      | nil => exact False.elim (firstNonempty rfl)
      | cons representative rest =>
        have firstShape : sourceShape representative = kind := by simpa [List.filterMap] using shape
        suffices allRows : (representative :: rest).flatMap (MutualProjections.sourceReferences owner 0) =
            (representative :: rest).map (fun source => (source.name, some (.member owner 0))) by
          simpa [expectedReferences] using allRows
        rw [List.map_eq_flatMap]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro source present
        have same := agree (representative :: rest) (by simp) source present representative (by simp)
        exact no_ctor_references owner 0 source kind standalone (same.trans firstShape)

theorem standalone_resolves (store : Store) (owner : Address) (block : Ixon.Constant)
    (standalone : Standalone block.info) :
    resolveSource store owner block = some (.member owner 0) := by
  cases info : block.info <;> simp [info, Standalone] at standalone
  all_goals simp [resolveSource, info]

/-- **The built block's rows read as their sources**, in either case. -/
theorem build_resolves (limits : Ix.Sharing.Exact.Limits) (sources : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (state : BlockState)
    (output : BlockResult) (ran : buildCompiledMutualBlock limits sources members metadata state = .ok output)
    (shape : members.toList.map memberShape = (sources.filterMap List.head?).map sourceShape)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source)
    (store : Store) (stored : store output.blockAddr = some output.block) (wire : output.block.wireWF) :
    readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources := by
  obtain ⟨address, wrapped | collapsed⟩ := build_cases limits sources members metadata state output ran
  · obtain ⟨targets, metadata, info, targetShape, projections⟩ := wrapped
    rw [projections]
    exact MutualProjections.build_resolves store output.blockAddr output.block sources targets metadata
      stored info wire nonempty agree (targetShape.trans shape) positions
  · obtain ⟨standalone, ⟨kind, kindStandalone, kindShape⟩, rows⟩ := collapsed
    have expected := collapsed_references output.blockAddr sources nonempty agree kind kindStandalone
      (shape.symm.trans kindShape)
    rw [rows, expected]
    simp only [readRows, List.map_map]
    apply List.map_congr_left
    intro source _
    have resolved := standalone_resolves store (Address.admissionHash (Ixon.ser output.block)) output.block
      standalone
    simpa only [address, Function.comp_def] using congrArg (fun result => (source.name, result)) resolved

/-- In every store holding the wire-valid block, its rows read as the
source-indexed references. -/
def References (sources : List (List MutConst)) (output : BlockResult) : Prop :=
  ∀ store : Store, store output.blockAddr = some output.block → output.block.wireWF →
    readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources

theorem finish_references (sources : List (List MutConst)) (members : Array Ixon.MutConst)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta))
    (shape : members.toList.map memberShape = (sources.filterMap List.head?).map sourceShape)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source) :
    Emission.Yields (finishMutualCompilation sources members metadata) (References sources) := by
  intro context before output after ran store stored wire
  obtain ⟨rfl, _, built⟩ := ProjectionLayout.finish_mutual_ok context sources members metadata ran
  exact build_resolves _ sources members metadata _ output built shape nonempty agree positions store stored wire

theorem payload_references (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source) :
    Emission.Yields (compileMutualPayload sources) (References sources) := by
  unfold compileMutualPayload
  exact Emission.Yields.bind (ProjectionLayout.payload_shapes sources) fun compiled shape =>
    finish_references sources compiled.1 compiled.2.2 shape nonempty agree positions

theorem mutual_references (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source) :
    Emission.Yields (compileMutualBlock sources) (References sources) :=
  ProjectionLayout.mutual_block _ sources (payload_references sources nonempty agree positions)

/-- **A compiled mutual block is a correct artifact**: under an environment
without Pass 3 records, a successful compile from a state whose tables are
on the wire returns a block that decodes exactly, projections that decode
exactly, and rows that read, in any store holding the block, as the
source-indexed references; given non-empty classes whose members agree in
shape and source constructors that declare their positions. -/
theorem mutual_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (sources : List (List MutConst)) {before after : BlockState} {output : BlockResult}
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output ∧ MutualProjections.ProjectionWire output ∧
      ∀ store : Store, store output.blockAddr = some output.block →
        readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources := by
  have codec := MutualProjections.mutual_codec context free sources wire ran
  exact ⟨codec.1, codec.2.1, fun store stored =>
    mutual_references sources nonempty agree positions context before output after ran store stored codec.1.1⟩


/-- **A sorted and compiled mutual block is a correct artifact, with no class
premise** (R9b): the compiler's two steps for a mutual block, `sortConsts`
then `compileMutualBlock` (`Ix.CompileDriver`), under an environment without
Pass 3 records and from a state whose tables are on the wire, return classes
that partition the members and a block that decodes exactly, whose
projections decode exactly, and whose rows read, in any store holding the
block, as the classes' source-indexed references; given members whose member
and constructor names are pairwise distinct and whose constructors declare
their positions. `mutual_correct`'s `nonempty` and `ClassesAgree` premises are
discharged by the sort (`MutualProjections.sort_classes`). -/
theorem mutual_sorted_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (members : List MutConst) {before after : BlockState} {output : BlockResult}
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (keys : Canon.KeysDistinct members)
    (positions : ∀ member ∈ members, MutualProjections.ConstructorPositions member)
    (ran : rawRun (sortConsts members >>= compileMutualBlock) context before = (.ok output, after)) :
    ∃ classes, Canon.Partition classes members ∧
      Ix.Sharing.Verify.BlockResultCodecWF output ∧ MutualProjections.ProjectionWire output ∧
      ∀ store : Store, store output.blockAddr = some output.block →
        readRows store (logicalRows output.projections) = expectedReferences output.blockAddr classes := by
  obtain ⟨classes, middle, sorted, compiled⟩ := bind_ok ran
  obtain ⟨rfl, -⟩ := ProjectionLayout.sort_run members sorted
  obtain ⟨partition, agree⟩ := MutualProjections.sort_classes members keys context middle
    classes middle sorted
  refine ⟨classes, partition, mutual_correct context free classes wire partition.2 agree
    (fun source present => positions source (partition.1.mem_iff.1 present)) compiled⟩

/-! ## The driver's recursor-family order (N-READS, N5 a) -/

/-- Sorting the classes decorated with a key and their index, then dropping
the decoration, permutes them. -/
private theorem keyed_perm (key : List MutConst → UInt64) (classes : List (List MutConst))
    (lt : UInt64 × Nat × List MutConst → UInt64 × Nat × List MutConst → Bool) :
    (((classes.toArray.zipIdx.map fun (cls, i) => (key cls, i, cls)).qsort lt).map
        (·.2.2)).toList.Perm classes := by
  have sorted := Canon.qsort_perm (classes.toArray.zipIdx.map fun (cls, i) => (key cls, i, cls)) lt
  have mapped := (Array.perm_iff_toList_perm.1 sorted).map (fun entry => entry.2.2)
  rw [← Array.toList_map, ← Array.toList_map, Array.map_map] at mapped
  refine mapped.trans ?_
  have same : ((fun entry : UInt64 × Nat × List MutConst => entry.2.2) ∘
      fun (pair : List MutConst × Nat) => (key pair.1, pair.2, pair.1)) = Prod.fst := by
    funext pair; rfl
  rw [same, Array.zipIdx_map_fst, List.toList_toArray]

/-- **`orderRecursorFamily` permutes the classes**: it returns them unchanged
unless every class is a recursor class, and otherwise sorts them by their
family position (`Canon.qsort_perm`). -/
theorem orderRecursorFamily_perm (classes : List (List MutConst)) :
    (orderRecursorFamily classes).Perm classes := by
  unfold orderRecursorFamily
  split
  · exact List.Perm.refl _
  · exact keyed_perm _ classes _

/-- The reordered classes partition the members the sorted classes did. -/
theorem ordered_partition {classes : List (List MutConst)} {members : List MutConst}
    (partition : Canon.Partition classes members) :
    Canon.Partition (orderRecursorFamily classes) members :=
  have perm := orderRecursorFamily_perm classes
  ⟨perm.flatten.trans partition.1, fun members present => partition.2 members (perm.mem_iff.1 present)⟩

/-- The reordered classes agree in shape where the sorted classes did. -/
theorem ordered_agree {classes : List (List MutConst)} (agree : MutualProjections.ClassesAgree classes) :
    MutualProjections.ClassesAgree (orderRecursorFamily classes) :=
  fun members present => agree members ((orderRecursorFamily_perm classes).mem_iff.1 present)

/-- **A sorted, family-ordered and compiled mutual block is a correct
artifact, with no class premise** (N-READS, N5 a): the driver's steps for a
mutual block, `sortConsts`, `orderRecursorFamily` and `compileMutualBlock`
(`Ix.CompileM.compileBlock`), under an environment without
Pass 3 records and from a state whose tables are on the wire, return classes
that partition the members and a block that decodes exactly, whose
projections decode exactly, and whose rows read, in any store holding the
block, as the classes' source-indexed references; given members whose member
and constructor names are pairwise distinct and whose constructors declare
their positions. The classes are the family-ordered ones, a permutation of
the sorted ones (`orderRecursorFamily_perm`), so `mutual_correct`'s premises
carry over from `sort_classes`. The Pass 3 hooks (CQ4.2 d) act before the
block (`prepareBlock`, the identity on a block that references no image head)
and after its aux tail (`editChangedBlock`, on a changed block only); this is
the step between them. -/
theorem mutual_ordered_correct (context : CompileEnv × BlockEnv) (free : context.1.surgeryFree = true)
    (members : List MutConst) {before after : BlockState} {output : BlockResult}
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (keys : Canon.KeysDistinct members)
    (positions : ∀ member ∈ members, MutualProjections.ConstructorPositions member)
    (ran : rawRun (sortConsts members >>= fun sorted => compileMutualBlock (orderRecursorFamily sorted))
      context before = (.ok output, after)) :
    ∃ classes, Canon.Partition classes members ∧
      Ix.Sharing.Verify.BlockResultCodecWF output ∧ MutualProjections.ProjectionWire output ∧
      ∀ store : Store, store output.blockAddr = some output.block →
        readRows store (logicalRows output.projections) = expectedReferences output.blockAddr classes := by
  obtain ⟨sorted, middle, sortRan, compiled⟩ := bind_ok ran
  obtain ⟨rfl, -⟩ := ProjectionLayout.sort_run members sortRan
  obtain ⟨partition, agree⟩ := MutualProjections.sort_classes members keys context middle
    sorted middle sortRan
  have ordered := ordered_partition partition
  refine ⟨orderRecursorFamily sorted, ordered, mutual_correct context free _ wire ordered.2
    (ordered_agree agree) (fun source present => positions source (ordered.1.mem_iff.1 present)) compiled⟩

end Ix.CompileCert.MutualArtifact
