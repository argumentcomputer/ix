import Ix.CompileCert.MutualProjections

/-! # A mutual block's decoded artifact and source references

A mutual block either retains its wrapper and projections or collapses a lone
definition or recursor to a standalone record. Both cases decode exactly;
their rows resolve to the source-indexed references in any store holding the
wire-valid block. The member and constructor positions are preserved by
compilation and sharing's write-back.
-/

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
def WrappedRows (sources : List MutConst) (members : Array Ixon.MutConst) (output : BlockResult) : Prop :=
  ∃ targets metadata, output.block.info = .muts targets ∧
    targets.toList.map memberShape = members.toList.map memberShape ∧
    output.projections = buildMutualProjections sources output.blockAddr metadata

/-- The collapsed case: a lone definition or recursor, every source name
registered to the block itself. -/
def CollapsedRows (sources : List MutConst) (members : Array Ixon.MutConst) (output : BlockResult) : Prop :=
  Standalone output.block.info ∧
    (∃ kind, (kind = MemberShape.defn ∨ kind = MemberShape.recr) ∧ members.toList.map memberShape = [kind]) ∧
    logicalRows output.projections = sources.map (fun source => (source.name, output.block))

/-- **The mutual builder's two cases**, with the block's address. -/
theorem build_cases (limits : Ix.Sharing.Exact.Limits) (sources : List MutConst)
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

theorem no_ctor_references (owner : Address) (index : Nat) (source : MutConst) (kind : MemberShape)
    (standalone : kind = .defn ∨ kind = .recr) (shape : sourceShape source = kind) :
    MutualProjections.sourceReferences owner index source = [(source.name, some (.member owner index))] := by
  rcases standalone with rfl | rfl
  all_goals cases source
  all_goals first | rfl | cases shape

theorem collapsed_references (owner : Address) (sources : List MutConst)
    (kind : MemberShape) (standalone : kind = .defn ∨ kind = .recr)
    (shape : sources.map sourceShape = [kind]) :
    expectedReferences owner sources = sources.map (fun source => (source.name, some (.member owner 0))) := by
  have length : sources.length = 1 := by simpa using congrArg List.length shape
  cases sources with
  | nil => simp at length
  | cons source rest =>
    cases rest with
    | cons other rest => simp at length
    | nil =>
      have sourceKind : sourceShape source = kind := by simpa using shape
      simpa [expectedReferences] using no_ctor_references owner 0 source kind standalone sourceKind

theorem standalone_resolves (store : Store) (owner : Address) (block : Ixon.Constant)
    (standalone : Standalone block.info) :
    resolveSource store owner block = some (.member owner 0) := by
  cases info : block.info <;> simp [info, Standalone] at standalone
  all_goals simp [resolveSource, info]

/-- **The built block's rows read as their sources**, in either case. -/
theorem build_resolves (limits : Ix.Sharing.Exact.Limits) (sources : List MutConst)
    (members : Array Ixon.MutConst) (metadata : Array (Ix.Name × Ixon.ConstantMeta)) (state : BlockState)
    (output : BlockResult) (ran : buildCompiledMutualBlock limits sources members metadata state = .ok output)
    (shape : members.toList.map memberShape = sources.map sourceShape)
    (positions : ∀ source ∈ sources, MutualProjections.ConstructorPositions source)
    (store : Store) (stored : store output.blockAddr = some output.block) (wire : output.block.wireWF) :
    readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources := by
  obtain ⟨address, wrapped | collapsed⟩ := build_cases limits sources members metadata state output ran
  · obtain ⟨targets, metadata, info, targetShape, projections⟩ := wrapped
    rw [projections]
    exact MutualProjections.build_resolves store output.blockAddr output.block sources targets metadata
      stored info wire (targetShape.trans shape) positions
  · obtain ⟨standalone, ⟨kind, kindStandalone, kindShape⟩, rows⟩ := collapsed
    have expected := collapsed_references output.blockAddr sources kind kindStandalone
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
def References (sources : List MutConst) (output : BlockResult) : Prop :=
  ∀ store : Store, store output.blockAddr = some output.block → output.block.wireWF →
    readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources

theorem finish_references (sources : List MutConst) (members : Array Ixon.MutConst)
    (metadata : Array (Ix.Name × Ixon.ConstantMeta))
    (shape : members.toList.map memberShape = sources.map sourceShape)
    (positions : ∀ source ∈ sources, MutualProjections.ConstructorPositions source) :
    Emission.Yields (finishMutualCompilation sources members metadata) (References sources) := by
  intro context before output after ran store stored wire
  obtain ⟨rfl, _, built⟩ := ProjectionLayout.finish_mutual_ok context sources members metadata ran
  exact build_resolves _ sources members metadata _ output built shape positions store stored wire

theorem payload_references (sources : List MutConst)
    (positions : ∀ source ∈ sources, MutualProjections.ConstructorPositions source) :
    Emission.Yields (compileMutualPayload sources) (References sources) := by
  unfold compileMutualPayload
  exact Emission.Yields.bind (ProjectionLayout.payload_shapes sources) fun compiled shape =>
    finish_references sources compiled.1 compiled.2.2 shape positions

theorem mutual_references (sources : List MutConst)
    (positions : ∀ source ∈ sources, MutualProjections.ConstructorPositions source) :
    Emission.Yields (compileMutualBlock sources) (References sources) :=
  ProjectionLayout.mutual_block _ sources (payload_references sources positions)

/-- A successful mutual compile from wire-valid tables returns a block and
projections that decode exactly. In any store holding the block, the rows
resolve to source-indexed references, provided constructors declare their
positions. -/
theorem mutual_correct (context : CompileEnv × BlockEnv)
    (sources : List MutConst) {before after : BlockState} {output : BlockResult}
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (positions : ∀ source ∈ sources, MutualProjections.ConstructorPositions source)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output ∧ MutualProjections.ProjectionWire output ∧
      ∀ store : Store, store output.blockAddr = some output.block →
        readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources := by
  have codec := MutualProjections.mutual_codec context sources wire ran
  exact ⟨codec.1, codec.2.1, fun store stored =>
    mutual_references sources positions context before output after ran store stored codec.1.1⟩

end Ix.CompileCert.MutualArtifact
