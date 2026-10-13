import Ix.CompileCert.FamilyReading

/-! Public inductive compilation instantiated at the whole-record family
reader's actual singleton context. Source scope and indexed recursor-family
readiness remain explicit; emitted payloads and reader contexts are derived. -/

namespace Ix.CompileCert.InductiveReading

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Kernel.Reader

def selfAt (reader : Ctx) (owner : Address) : Nat → Option Kernel.Name :=
  fun index => if index < 1 then some (reader.nameOf (.member owner index)) else none

def paramsFor (reader : Ctx) (owner : Address) (source : InductiveVal) : List Kernel.Name :=
  reader.lpsOf (.member owner 0) source.cnst.levelParams.size

theorem params_length (reader : Ctx) (owner : Address) (source : InductiveVal) :
    (paramsFor reader owner source).length = source.cnst.levelParams.size :=
  DefinitionReading.lpsOf_length _ _ _

theorem blob_params (reader : Ctx) (state : BlockState) (owner : Address) (source : InductiveVal) :
    paramsFor (SharingRead.blobContext reader state) owner source = paramsFor reader owner source := rfl

theorem blob_self (reader : Ctx) (state : BlockState) (owner : Address) :
    selfAt (SharingRead.blobContext reader state) owner = selfAt reader owner := rfl

theorem singleton_params (reader : Ctx) (owner : Address) (source : InductiveVal) (target : Ixon.Inductive)
    (levels : target.lvls.toNat = source.cnst.levelParams.size) :
    FamilyCollection.blockParams reader owner #[(0, target)] target = paramsFor reader owner source := by
  simp [FamilyCollection.blockParams, paramsFor, levels]

theorem singleton_reader (reader : Ctx) (owner : Address) (constant : Ixon.Constant)
    (source : InductiveVal) (target : Ixon.Inductive) (levels : target.lvls.toNat = source.cnst.levelParams.size) :
    FamilyCollection.memberReader reader owner constant #[.indc target] #[(0, target)] target =
      MemberReader.mk' reader constant (paramOf (paramsFor reader owner source)) (selfAt reader owner) := by
  simp only [FamilyCollection.memberReader, singleton_params reader owner source target levels]
  rfl

theorem singleton_family (target : Ixon.Inductive) : FamilyReading.FamilyOnly #[.indc target] := by
  intro member present
  have same : member = .indc target := by simpa using present
  subst member
  trivial

theorem singleton_selection (shape : BlockShape) (target : Ixon.Inductive) (order : shape.order = #[0]) :
    FamilyCollection.selected shape #[.indc target] = #[(0, target)] := by
  simp [FamilyCollection.selected, order]

/-- The compiler supplies the singleton payload and exact header arity, so
the shared source relation can use the kernel family's actual reader rather
than an arbitrary supplied parameter/self interpretation. -/
theorem compile_raw (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (before after : BlockState) (output : BlockResult)
    (scope : ExpressionScope.Scoped
      (ExpressionScope.SelfName (InductiveBlock.familyContext source constructors context).2 (selfAt reader output.blockAddr) names)
      source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors, ExpressionScope.Scoped
      (ExpressionScope.SelfName (InductiveBlock.familyContext source constructors context).2 (selfAt reader output.blockAddr) names)
      ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (found : (rawRun (lookupInductiveConstructors source) context before).1 = .ok constructors)
    (ready : DefinitionEmission.Ready bindings before) (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Sharing.Verify.BlockResultCodecWF output ∧
      (∃ metadata pairs, InductiveBlock.Wrapped source metadata pairs output) ∧
      ∃ target, output.block.info = .muts #[.indc target] ∧
        target.lvls.toNat = source.cnst.levelParams.size ∧ target.params.toNat = source.numParams ∧
        InductiveEmission.Related
          (FamilyCollection.memberReader (SharingRead.blobContext reader after) output.blockAddr output.block
            #[.indc target] #[(0, target)] target)
          names source.cnst.levelParams.toList (paramsFor reader output.blockAddr source)
          (InductiveEmission.sourceData source constructors) target := by
  have compiled := InductiveBlock.constant_correct reader base (selfAt reader output.blockAddr) names
    (paramsFor reader output.blockAddr source) bindings context source constructors (params_length reader output.blockAddr source)
    scope ctorScope aligned external before after output found ready tables widths ran
  obtain ⟨wrapped, target, kind, related⟩ := compiled.2.1
  have levels : target.lvls.toNat = source.cnst.levelParams.size := related.2.1
  have parameters : target.params.toNat = source.numParams := related.2.2.1
  refine ⟨compiled.1, compiled.2.2, wrapped, target, kind, levels, parameters, ?_⟩
  rw [singleton_reader (SharingRead.blobContext reader after) output.blockAddr output.block source target levels,
    blob_params, blob_self]
  exact related

def sourceFamily (source : InductiveVal) (constructors : Array ConstructorVal) : Array (Nat × Ind) :=
  #[(0, InductiveEmission.sourceData source constructors)]

/-- Actual public compilation produces the block and codec evidence used by
whole-record reading. Singleton shape, selected member, universe arity and
common header counts are derived; source scope/index readiness remain explicit. -/
theorem compile_read (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (before after : BlockState) (output : BlockResult) (state : State) (shape : BlockShape)
    (recursors : Array FamilyRecursors.Input)
    (scope : ExpressionScope.Scoped
      (ExpressionScope.SelfName (InductiveBlock.familyContext source constructors context).2 (selfAt reader output.blockAddr) names)
      source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors, ExpressionScope.Scoped
      (ExpressionScope.SelfName (InductiveBlock.familyContext source constructors context).2 (selfAt reader output.blockAddr) names)
      ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (found : (rawRun (lookupInductiveConstructors source) context before).1 = .ok constructors)
    (ready : DefinitionEmission.Ready bindings before) (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after))
    (indexed : reader.index.blocks[output.blockAddr]? = some shape) (order : shape.order = #[0])
    (safe : source.isUnsafe = false)
    (ctorReady : FamilyConstructors.SourceReady source.numParams (InductiveEmission.sourceData source constructors))
    (recursorOrder : shape.recs = recursors.map FamilyRecursors.Input.ref)
    (recursorValid : ∀ input ∈ recursors,
      FamilyRecursors.Valid (SharingRead.blobContext reader after) (paramsFor reader output.blockAddr source) names input) :
    DefinitionEmission.Clean bindings after ∧ Sharing.Verify.BlockResultCodecWF output ∧
      (∃ metadata pairs, InductiveBlock.Wrapped source metadata pairs output) ∧
      ∃ target, output.block.info = .muts #[.indc target] ∧
        ∃ collected : FamilyReading.Collected (SharingRead.blobContext reader after) output.blockAddr names
            (paramsFor reader output.blockAddr source) (sourceFamily source constructors) recursors,
          (collected.Consistent source.numParams →
            readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block =
              (collected.assembly source.numParams #[(0, target)]).run state) ∧
          (collected.Consistent source.numParams →
            FamilySourceChecks.sourceNested (sourceFamily source constructors) recursors = 0 →
            readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block =
              .ok ((collected.assembly source.numParams #[(0, target)]).result [])) ∧
          (0 < FamilySourceChecks.sourceNested (sourceFamily source constructors) recursors →
            Kernel.Frontend.InModel.wants (collected.assembly source.numParams #[(0, target)]).model = true) := by
  obtain ⟨clean, codec, wrapped, target, kind, levels, parameters, payload⟩ := compile_raw reader base names bindings context
    source constructors before after output scope ctorScope aligned external found ready tables widths ran
  have params : FamilyCollection.blockParams (SharingRead.blobContext reader after) output.blockAddr #[(0, target)] target =
      paramsFor reader output.blockAddr source :=
    (singleton_params (SharingRead.blobContext reader after) output.blockAddr source target levels).trans
      (blob_params reader after output.blockAddr source)
  have paired : List.Forall₂
      (FamilyTypes.Paired
        (FamilyCollection.memberReader (SharingRead.blobContext reader after) output.blockAddr output.block
          #[.indc target] #[(0, target)] target) names
        (FamilyCollection.blockParams (SharingRead.blobContext reader after) output.blockAddr #[(0, target)] target))
      (sourceFamily source constructors).toList #[(0, target)].toList := by
    refine .cons ⟨rfl, ?_⟩ .nil
    simpa only [params, InductiveEmission.sourceData] using payload
  have sourceSafe : ∀ value ∈ sourceFamily source constructors, value.2.isUnsafe = false := by
    intro value present
    have same : value = (0, InductiveEmission.sourceData source constructors) := by simpa [sourceFamily] using present
    subst value
    exact safe
  have sourceParams : ∀ value ∈ sourceFamily source constructors, value.2.numParams = target.params.toNat := by
    intro value present
    have same : value = (0, InductiveEmission.sourceData source constructors) := by simpa [sourceFamily] using present
    subst value
    exact parameters.symm
  have sourceCtors : ∀ value ∈ sourceFamily source constructors, FamilyConstructors.SourceReady target.params.toNat value.2 := by
    intro value present
    have same : value = (0, InductiveEmission.sourceData source constructors) := by simpa [sourceFamily] using present
    subst value
    simpa only [parameters] using ctorReady
  have recs : ∀ input ∈ recursors, FamilyRecursors.Valid (SharingRead.blobContext reader after)
      (FamilyCollection.blockParams (SharingRead.blobContext reader after) output.blockAddr #[(0, target)] target) names input := by
    rw [params]
    exact recursorValid
  have result := FamilyReading.read_record (SharingRead.blobContext reader after) state output.blockAddr output.block
    #[.indc target] shape (sourceFamily source constructors) #[(0, target)] 0 target names recursors
    kind (singleton_family target) indexed (singleton_selection shape target order) (by simp [order]) rfl
    paired sourceSafe sourceParams sourceCtors recursorOrder recs
  rw [params, parameters] at result
  obtain ⟨collected, complete, ordinary, model⟩ := result
  refine ⟨clean, codec, wrapped, target, kind, collected, complete, ?_, ?_⟩
  · intro valid plain
    exact ordinary valid (by simp [sourceFamily]) plain
  · intro nested
    exact model (.inr ⟨by simp [sourceFamily], nested⟩)

end Ix.CompileCert.InductiveReading
