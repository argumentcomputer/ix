import Ix.CompileCert.RecursorSharing
import Ix.CompileCert.FamilyWire

/-! The actual public recursor compiler returns the source-related shared
type/rules and exact serialized artifact. The indexed inductive-family reader
and declaration admission remain separate obligations. -/

namespace Ix.CompileCert.RecursorBlock

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

theorem block_run (source : RecursorVal) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileRecursorBlock source) context before = (.ok output, after)) :
    ∃ payload : Ixon.Recursor × Ixon.ConstantMeta × Ixon.Expr,
      rawRun (compileRecursor source) context before = (.ok payload, after) ∧
      buildConstantWithSharing context.1.sharingLimits (.recr payload.1) after.refs after.univs = .ok output.block ∧
      DefinitionBlock.Wrapped output := by
  rw [compileRecursorBlock] at ran
  obtain ⟨payload, middle, compiled, finished⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  rw [DefinitionBlock.rawRun_timedC, DefinitionBlock.finish_run] at finished
  cases built : buildConstantWithSharing context.1.sharingLimits (.recr payload.1) middle.refs middle.univs with
  | error error => simp [built, Except.map] at finished
  | ok block =>
    simp only [built, Except.map, Prod.mk.injEq, Except.ok.injEq] at finished
    obtain ⟨rfl, rfl⟩ := finished
    exact ⟨payload, compiled, built, DefinitionBlock.wrapped_mk _ _⟩

def Related (reader : Kernel.Reader.Ctx) (self : Nat → Option Kernel.Name)
    (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (state : BlockState) (source : RecursorVal) (output : BlockResult) : Prop :=
  DefinitionBlock.Wrapped output ∧ ∃ target, output.block.info = .recr target ∧
    RecursorEmission.Related
      (Kernel.Reader.MemberReader.mk' (SharingRead.blobContext reader state) output.block
        (Kernel.Reader.paramOf params) self)
      names source.cnst.levelParams.toList params source target

theorem block_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (arity : params.length = source.cnst.levelParams.size)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (output : BlockResult) (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compileRecursorBlock source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Related reader self names params after source output := by
  obtain ⟨payload, compiled, shared, wrapped⟩ := block_run source context before after output ran
  have emitted := RecursorEmission.compile_correct reader base self names params bindings context source
    arity aligned external selfSound before after payload ready compiled
  have meaning := RecursorSharing.build_payload reader base self names source.cnst.levelParams.toList params after
    emitted.1.2.2 source payload.1 emitted.2.2.1 context.1.sharingLimits output.block shared
  exact ⟨emitted.1, wrapped, meaning⟩

/-- Preseeding and the actual sharing/serialization path yield both source
type/rule readings and byte round-trip in the same returned artifact. -/
theorem info_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (arity : params.length = source.cnst.levelParams.size)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 self names)
    (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before)
    (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileRecursorInfo source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Related reader self names params after source output ∧
      Sharing.Verify.BlockResultCodecWF output := by
  have codec := FamilyWire.recursorInfo_codec source context bindings before after output ready tables widths ran
  rw [compileRecursorInfo] at ran
  obtain ⟨done, middle, seeded, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases done
  have prepared := PreseedState.preseed_ready_checked context (recursorPreseedExprs source)
    bindings before middle ready seeded
  have meaning := block_correct reader base self names params bindings context source
    arity aligned external selfSound middle after output prepared.1 compiled
  exact ⟨meaning.1, meaning.2, codec⟩

theorem constant_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : RecursorVal) (arity : params.length = source.cnst.levelParams.size)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect
      (DefinitionReading.singletonContext source.cnst.name context).2 self names)
    (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before)
    (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.recInfo source)) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Related reader self names params after source output ∧
      Sharing.Verify.BlockResultCodecWF output :=
  info_correct reader base self names params bindings (DefinitionReading.singletonContext source.cnst.name context)
    source arity aligned external selfSound before after output ready tables widths ran

end Ix.CompileCert.RecursorBlock
