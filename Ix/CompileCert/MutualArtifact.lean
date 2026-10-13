import Ix.CompileCert.MutualProjections
import Ix.CompileCert.ReferencePublication

/-! The reference/storage part of a mutual-unit extension, through the actual
returned artifact and checked publication merge. Both mutual wrappers and
singleton collapse are covered. Source field semantics, declaration admission,
progress and remaining source/prefix-invariant dischargers remain separate. -/

namespace Ix.CompileCert.MutualArtifact

open Ix Ix.CompileM
open ProjectionLayout (memberShape sourceShape MemberShape)
open MutualProjections (logicalRows expectedRows expectedReferences readRows)

def Standalone : Ixon.ConstantInfo → Prop
  | .defn _ | .recr _ => True
  | _ => False

theorem writeback_standalone (source target : Ixon.ConstantInfo) (roots : Array Ixon.Expr)
    (standalone : Standalone source) (ran : Ix.Sharing.Exact.withRoots source roots = .ok target) :
    Standalone target := by
  cases source with
  | defn value | recr value =>
    simp only [Ix.Sharing.Exact.withRoots] at ran
    split at ran
    · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at ran
    obtain ⟨⟨member, rest⟩, _, tail⟩ := Ix.Sharing.Verify.except_bind_eq_ok ran
    cases member
    all_goals simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at tail
    all_goals cases Ix.Sharing.Verify.withRoots_tail tail; trivial
  | _ => cases standalone

theorem sharing_standalone (limits : Ix.Sharing.Exact.Limits) (source : Ixon.ConstantInfo)
    (refs : Array Address) (univs : Array Ixon.Univ) (block : Ixon.Constant)
    (standalone : Standalone source) (ran : buildConstantWithSharing limits source refs univs = .ok block) :
    Standalone block.info := by
  obtain ⟨shared, info, _, _, written, built⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  unfold withRootExprs at written
  cases result : Ix.Sharing.Exact.withRoots source shared.result.roots with
  | error reason => simp [result, Except.mapError] at written
  | ok target =>
    simp only [result, Except.mapError, Except.ok.injEq] at written
    subst info
    subst block
    exact writeback_standalone source target shared.result.roots standalone result

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

def WrappedRows (sources : List (List MutConst)) (members : Array Ixon.MutConst) (output : BlockResult) : Prop :=
  ∃ targets metadata, output.block.info = .muts targets ∧
    targets.toList.map memberShape = members.toList.map memberShape ∧
    output.projections = buildMutualProjections sources output.blockAddr metadata

def CollapsedRows (sources : List (List MutConst)) (members : Array Ixon.MutConst) (output : BlockResult) : Prop :=
  Standalone output.block.info ∧
    (∃ kind, (kind = MemberShape.defn ∨ kind = MemberShape.recr) ∧ members.toList.map memberShape = [kind]) ∧
    logicalRows output.projections = sources.flatten.map (fun source => (source.name, output.block))

theorem build_cases (limits : Ix.Sharing.Exact.Limits) (sources : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Name × Ixon.ConstantMeta)) (state : BlockState)
    (output : BlockResult) (ran : buildCompiledMutualBlock limits sources members metadata state = .ok output) :
    output.blockAddr = Address.blake3 (Ixon.ser output.block) ∧
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
    obtain ⟨targets, info, shape⟩ := ProjectionLayout.sharing_mutual_shape limits members state.refs state.univs block built
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

theorem standalone_resolves (store : Kernel.Reader.Store) (owner : Address) (block : Ixon.Constant)
    (standalone : Standalone block.info) :
    Kernel.Reader.resolveSource store owner block = some (.member owner 0) := by
  cases info : block.info <;> simp [info, Standalone] at standalone
  all_goals simp [Kernel.Reader.resolveSource, info]

theorem build_resolves (limits : Ix.Sharing.Exact.Limits) (sources : List (List MutConst))
    (members : Array Ixon.MutConst) (metadata : Array (Name × Ixon.ConstantMeta)) (state : BlockState)
    (output : BlockResult) (ran : buildCompiledMutualBlock limits sources members metadata state = .ok output)
    (shape : members.toList.map memberShape = (sources.filterMap List.head?).map sourceShape)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source)
    (store : Kernel.Reader.Store) (stored : store output.blockAddr = some output.block) (wire : output.block.wireWF) :
    readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources := by
  obtain ⟨address, wrapped | collapsed⟩ := build_cases limits sources members metadata state output ran
  · obtain ⟨targets, metadata, info, targetShape, projections⟩ := wrapped
    rw [projections]
    exact MutualProjections.build_resolves store output.blockAddr output.block sources targets metadata
      stored info wire nonempty agree (targetShape.trans shape) positions
  · obtain ⟨standalone, ⟨kind, kindStandalone, kindShape⟩, rows⟩ := collapsed
    have expected := collapsed_references output.blockAddr sources nonempty agree kind kindStandalone (shape.symm.trans kindShape)
    rw [rows, expected]
    simp only [readRows, List.map_map]
    apply List.map_congr_left
    intro source _
    have resolved := standalone_resolves store (Address.blake3 (Ixon.ser output.block)) output.block standalone
    simpa only [address, Function.comp_def] using congrArg (fun result => (source.name, result)) resolved

def References (sources : List (List MutConst)) (output : BlockResult) : Prop :=
  ∀ store : Kernel.Reader.Store, store output.blockAddr = some output.block → output.block.wireWF →
    readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources

open Ix.CompileCert.HeadWriterFrame
open DeclarationHeaders (Returns)

theorem finish_references (sources : List (List MutConst)) (members : Array Ixon.MutConst)
    (metadata : Array (Name × Ixon.ConstantMeta))
    (shape : members.toList.map memberShape = (sources.filterMap List.head?).map sourceShape)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source) :
    Returns (finishMutualCompilation sources members metadata) (References sources) := by
  intro context before output after ran store stored wire
  unfold finishMutualCompilation at ran
  obtain ⟨done, middle, guarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := PayloadArrays.mutual_state members context before
  rw [guarded] at same
  dsimp only at same
  subst middle
  have readContext : rawRun (read : CompileM (CompileEnv × BlockEnv)) context before = (.ok context, before) := rfl
  simp only [rawRun_bind, rawRun_get, readContext, Ix.PhaseTimers.withPhase,
    Ix.PhaseTimers.enterV, Ix.PhaseTimers.exitV, ite_self] at rest
  cases built : buildCompiledMutualBlock context.1.sharingLimits sources members metadata before with
  | error reason => rw [built] at rest; cases rest
  | ok result =>
    rw [built, rawRun_pure] at rest
    cases Except.ok.inj (congrArg Prod.fst rest)
    exact build_resolves _ sources members metadata before output built shape nonempty agree positions store stored wire

theorem payload_references (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source) :
    Returns (compileMutualPayload sources) (References sources) :=
  Returns.bind (ProjectionLayout.payload_shapes sources) fun compiled shape =>
    finish_references sources compiled.1 compiled.2.2 shape nonempty agree positions

theorem mutual_references (sources : List (List MutConst))
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source) :
    Returns (compileMutualBlock sources) (References sources) := by
  unfold compileMutualBlock withMutCtx
  exact PayloadArrays.Returns.withBlockEnv (fun context => { context with mutCtx := MutConst.ctx sources })
    (Returns.bindAny (preseedExprTables (mutualPreseedExprs sources)) fun _ => payload_references sources nonempty agree positions)

theorem mutual_correct (sources : List (List MutConst)) (context : CompileEnv × BlockEnv)
    (bindings : ExpressionState.Bindings) (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before) (tables : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source)
    (ran : rawRun (compileMutualBlock sources) context before = (.ok output, after)) :
    Ix.Sharing.Verify.BlockResultCodecWF output ∧ MutualProjections.ProjectionWire output ∧
      ∀ store : Kernel.Reader.Store, store output.blockAddr = some output.block →
        readRows store (logicalRows output.projections) = expectedReferences output.blockAddr sources := by
  have codec := MutualProjections.mutual_codec sources context bindings before after output ready tables widths ran
  exact ⟨codec.1, codec.2.1, fun store stored =>
    mutual_references sources nonempty agree positions context before output after ran store stored codec.1.1⟩

def decodedStore (environment : CompileEnv) : Kernel.Reader.Store := fun address =>
  environment.constants[address]?.bind fun bytes => (Ixon.deConstant bytes).toOption

theorem published_block (before : DriverAcc) (lo : Name) (output : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (codec : Ix.Sharing.Verify.BlockResultCodecWF output) :
    decodedStore (mergeCompiledBlock before lo output cache).cenv output.blockAddr = some output.block := by
  have stored := (Publication.checkCompiledBlock_present before lo output cache accepted).1
    output.blockAddr output.blockBytes (List.mem_cons_self)
  simp only [decodedStore, stored, Option.bind_some, codec.2, Except.toOption]

theorem published_projection (before : DriverAcc) (lo : Name) (output : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (wire : MutualProjections.ProjectionWire output) (row : MutualProjections.Row) (present : row ∈ output.projections) :
    decodedStore (mergeCompiledBlock before lo output cache).cenv (Address.blake3 (Ixon.ser row.2.1)) = some row.2.1 := by
  have written : (Address.blake3 (Ixon.ser row.2.1), Ixon.ser row.2.1) ∈ Publication.recordWrites output cache := by
    apply List.mem_cons_of_mem
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨row, by simpa using present, rfl⟩
  have stored := (Publication.checkCompiledBlock_present before lo output cache accepted).1 _ _ written
  have decoded := Ixon.Verify.deConstant_serConstant row.2.1 (wire row present)
  simp only [decodedStore, stored, Option.bind_some]
  change (Ixon.deConstant (Ixon.serConstant row.2.1)).toOption = _
  rw [decoded]
  rfl

def publishedRows (environment : CompileEnv) (output : BlockResult) : List (Name × Option (Kernel.ConstRef Address)) :=
  output.projections.toList.map fun row =>
    (row.1, Kernel.Reader.resolve (decodedStore environment) (Address.blake3 (Ixon.ser row.2.1)))

theorem published_rows (before : DriverAcc) (lo : Name) (output : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ()) (wire : MutualProjections.ProjectionWire output) :
    publishedRows (mergeCompiledBlock before lo output cache).cenv output =
      readRows (decodedStore (mergeCompiledBlock before lo output cache).cenv) (logicalRows output.projections) := by
  simp only [publishedRows, readRows, logicalRows, List.map_map]
  apply List.map_congr_left
  intro row present
  have stored := published_projection before lo output cache accepted wire row (by simpa using present)
  simp [Kernel.Reader.resolve, stored]

theorem projection_claim (lo : Name) (output : BlockResult) (row : MutualProjections.Row)
    (present : row ∈ output.projections) :
    (row.1, Address.blake3 (Ixon.ser row.2.1)) ∈ (primaryClaims lo output).toList := by
  have nonempty : output.projections.isEmpty = false := by
    cases empty : output.projections.isEmpty
    · rfl
    · have absent : output.projections = #[] := Array.isEmpty_iff.mp empty
      simp [absent] at present
  simp only [primaryClaims, nonempty, Bool.false_eq_true, ↓reduceIte, Array.toList_map]
  exact List.mem_map.mpr ⟨row, by simpa using present, rfl⟩

theorem published_named (before : DriverAcc) (lo : Name) (output : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (expected : List (Name × Option (Kernel.ConstRef Address)))
    (references : publishedRows (mergeCompiledBlock before lo output cache).cenv output = expected)
    (name : Name) (reference : Kernel.ConstRef Address) (present : (name, some reference) ∈ expected) :
    ∃ address, (mergeCompiledBlock before lo output cache).cenv.nameToAddr[name]? = some address ∧
      Kernel.Reader.resolve (decodedStore (mergeCompiledBlock before lo output cache).cenv) address = some reference := by
  rw [← references] at present
  obtain ⟨row, rowPresent, same⟩ := List.mem_map.mp present
  have named := congrArg Prod.fst same
  have resolved := congrArg Prod.snd same
  change row.1 = name at named
  change Kernel.Reader.resolve (decodedStore (mergeCompiledBlock before lo output cache).cenv)
    (Address.blake3 (Ixon.ser row.2.1)) = some reference at resolved
  have claim := projection_claim lo output row (by simpa using rowPresent)
  rw [named] at claim
  exact ⟨_, ReferencePublication.checked_merge_primary_present before lo output cache accepted _ _ claim, resolved⟩

def StoreExtends (before after : Kernel.Reader.Store) : Prop :=
  ∀ address constant, before address = some constant → after address = some constant

theorem decoded_extends (before after : CompileEnv) (preserved : Publication.Extends before.constants after.constants) :
    StoreExtends (decodedStore before) (decodedStore after) := by
  intro address constant found
  unfold decodedStore at found ⊢
  obtain ⟨bytes, selected, decoded⟩ := Option.bind_eq_some_iff.mp found
  rw [preserved address bytes selected]
  exact decoded

theorem resolveSource_extends (before after : Kernel.Reader.Store) (preserved : StoreExtends before after)
    (address : Address) (constant : Ixon.Constant) (reference : Kernel.ConstRef Address)
    (resolved : Kernel.Reader.resolveSource before address constant = some reference) :
    Kernel.Reader.resolveSource after address constant = some reference := by
  cases info : constant.info with
  | defn value | recr value | axio value | quot value =>
    simpa only [Kernel.Reader.resolveSource, info] using resolved
  | muts values => simp only [Kernel.Reader.resolveSource, info] at resolved; cases resolved
  | cPrj projection | rPrj projection | iPrj projection | dPrj projection =>
    cases found : before projection.block with
    | none => simp [Kernel.Reader.resolveSource, info, found, guard] at resolved
    | some block =>
      have retained := preserved projection.block block found
      simpa only [Kernel.Reader.resolveSource, info, found, retained] using resolved

theorem resolve_extends (before after : Kernel.Reader.Store) (preserved : StoreExtends before after)
    (address : Address) (reference : Kernel.ConstRef Address)
    (resolved : Kernel.Reader.resolve before address = some reference) :
    Kernel.Reader.resolve after address = some reference := by
  unfold Kernel.Reader.resolve at resolved ⊢
  obtain ⟨constant, found, read⟩ := Option.bind_eq_some_iff.mp resolved
  rw [preserved address constant found]
  exact resolveSource_extends before after preserved address constant reference read

theorem checked_merge_prior_reference (before : DriverAcc) (lo : Name) (output : BlockResult) (cache : BlockState)
    (accepted : checkCompiledBlock before.cenv lo output cache = .ok ())
    (name : Name) (address : Address) (reference : Kernel.ConstRef Address)
    (named : before.cenv.nameToAddr[name]? = some address)
    (resolved : Kernel.Reader.resolve (decodedStore before.cenv) address = some reference) :
    (mergeCompiledBlock before lo output cache).cenv.nameToAddr[name]? = some address ∧
      Kernel.Reader.resolve (decodedStore (mergeCompiledBlock before lo output cache).cenv) address = some reference :=
  ⟨ReferencePublication.checked_merge_primary_extends before lo output cache accepted name address named,
    resolve_extends _ _ (decoded_extends _ _ (Publication.checkCompiledBlock_extends before lo output cache accepted).1)
      address reference resolved⟩

/-- The reference/storage part of an actual successful mutual-unit step.
Source field semantics, admission and progress are separate obligations. -/
theorem compile_merge_references (accumulator : DriverAcc) (lo : Name) (environment : BlockEnv)
    (sources : List (List MutConst)) (bindings : ExpressionState.Bindings)
    (initial finished : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings initial) (tables : Ix.Sharing.Verify.BlockWireTablesWF initial)
    (widths : ReferenceWidths.LookupWidths accumulator.cenv initial)
    (nonempty : ∀ members ∈ sources, members ≠ []) (agree : MutualProjections.ClassesAgree sources)
    (positions : ∀ source ∈ sources.flatten, MutualProjections.ConstructorPositions source)
    (ran : rawRun (compileMutualBlock sources) (accumulator.cenv, environment) initial = (.ok output, finished))
    (accepted : checkCompiledBlock accumulator.cenv lo output finished = .ok ()) :
    let next := (mergeCompiledBlock accumulator lo output finished).cenv
    Publication.Extends accumulator.cenv.constants next.constants ∧
      Publication.Extends accumulator.cenv.blobs next.blobs ∧
      ReferencePublication.ReferencesExtend accumulator.cenv.nameToAddr next.nameToAddr ∧
      publishedRows next output = expectedReferences output.blockAddr sources ∧
      ∀ name reference, (name, some reference) ∈ expectedReferences output.blockAddr sources →
        ∃ address, next.nameToAddr[name]? = some address ∧ Kernel.Reader.resolve (decodedStore next) address = some reference := by
  have compiled := mutual_correct sources (accumulator.cenv, environment) bindings initial finished output
    ready tables widths nonempty agree positions ran
  have stored := published_block accumulator lo output finished accepted compiled.1
  have resolved := compiled.2.2 (decodedStore (mergeCompiledBlock accumulator lo output finished).cenv) stored
  have rows := (published_rows accumulator lo output finished accepted compiled.2.1).trans resolved
  have preserved := Publication.checkCompiledBlock_extends accumulator lo output finished accepted
  exact ⟨preserved.1, preserved.2,
    ReferencePublication.checked_merge_primary_extends accumulator lo output finished accepted,
    rows, fun name reference present => published_named accumulator lo output finished accepted _ rows name reference present⟩

end Ix.CompileCert.MutualArtifact
