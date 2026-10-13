import Ix.CompileCert.HeaderEmission

/-! Production axiom/quotient block assembly, including primary-table wire
preservation, canonical sharing and exact serialized bytes. -/

namespace Ix.CompileCert.HeaderBlock

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open HeaderEmission (payload finish compile body contextFor finishNames)
open Ix.Sharing.Verify (BlockWireTablesWF)

abbrev Source := HeaderEmission.Source

theorem finish_bound (source : Source) (type : Ixon.Expr) (root : UInt64)
    (context : CompileEnv × BlockEnv) (before after : BlockState) (output : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr)
    (ran : rawRun (finish source type root) context before = (.ok output, after)) : source.cnst.levelParams.size < UInt64.size := by
  obtain ⟨_, expanded⟩ := HeaderEmission.finish_run source type root context before
  rw [expanded] at ran
  obtain ⟨count, middle, guarded, _⟩ := PreseedReferences.bind_ok _ _ context _ output after ran
  exact (Interning.checkedTableCount_value "declaration universe parameters" source.cnst.levelParams.size context
    (DefinitionEmission.drained before) (congrArg Prod.fst guarded)).2

theorem compile_bound (source : Source) (context : CompileEnv × BlockEnv) (before after : BlockState)
    (output : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr)
    (ran : rawRun (compile source) context before = (.ok output, after)) : source.cnst.levelParams.size < UInt64.size := by
  rw [HeaderEmission.compile_run, body] at ran
  obtain ⟨type, middle, _, finished⟩ := PreseedReferences.bind_ok _ _ (contextFor source context) _ output after ran
  exact finish_bound source type.1 type.2 (contextFor source context) middle after output finished

theorem finish_shape (source : Source) (type : Ixon.Expr) (root : UInt64)
    (context : CompileEnv × BlockEnv) (before after : BlockState) (output : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr)
    (ran : rawRun (finish source type root) context before = (.ok output, after)) :
    output.1 = payload source type ∧ output.2.2 = type := by
  obtain ⟨metadata, expanded⟩ := HeaderEmission.finish_run source type root context before
  rw [expanded] at ran
  have result : DeclarationHeaders.Returns (do
      let _ ← checkedTableCount "declaration universe parameters" source.cnst.levelParams.size
      finishNames source
      pure (payload source type, metadata, type)) (fun output => output.1 = payload source type ∧ output.2.2 = type) :=
    DeclarationHeaders.Returns.bindAny _ fun _ => DeclarationHeaders.Returns.bindAny _ fun _ =>
      DeclarationHeaders.Returns.pure ⟨rfl, rfl⟩
  exact result context _ output after ran

theorem compile_shape (source : Source) (context : CompileEnv × BlockEnv) (before after : BlockState)
    (output : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr)
    (ran : rawRun (compile source) context before = (.ok output, after)) :
    output.1 = payload source output.2.2 := by
  rw [HeaderEmission.compile_run, body] at ran
  obtain ⟨type, middle, _, finished⟩ := PreseedReferences.bind_ok _ _ (contextFor source context) _ output after ran
  have shape := finish_shape source type.1 type.2 (contextFor source context) middle after output finished
  rw [shape.2]
  exact shape.1

theorem finish_wire (source : Source) (type : Ixon.Expr) (root : UInt64) : EmissionWire.Safe (finish source type root) := by
  intro context before valid output after ran
  obtain ⟨metadata, expanded⟩ := HeaderEmission.finish_run source type root context before
  rw [expanded] at ran
  have names : EmissionWire.Safe (finishNames source) :=
    EmissionWire.Safe.seq (EmissionWire.Safe.compileName _) (fun _ => EmissionWire.Safe.compileNames _)
  have prepared : EmissionWire.Valid context.1 (DefinitionEmission.drained before) := valid.of_view rfl
  exact EmissionWire.Safe.seq (EmissionWire.Safe.checkedCount _ _) (fun _ =>
    EmissionWire.Safe.seq names (fun _ => EmissionWire.Safe.pure _)) context _ prepared output after ran

theorem compile_wire (source : Source) : EmissionWire.Safe (compile source) := by
  intro context before valid output after ran
  rw [HeaderEmission.compile_run, body] at ran
  have prepared : EmissionWire.Valid context.1 (DefinitionEmission.prepared before) := valid.of_view rfl
  exact EmissionWire.Safe.seq (EmissionWire.Safe.expression source.cnst.type) (fun type => finish_wire source type.1 type.2)
    (contextFor source context) _ prepared output after ran

def block : Source → CompileM BlockResult
  | .axio source => compileAxiomBlock source
  | .quot source => compileQuotientBlock source

theorem block_eq (source : Source) : block source = (do
    let output ← compile source
    timedC .sharing (finishConstantInfoWithSharing output.1 output.2.1)) := by
  cases source <;>
    simp only [block, compile, compileAxiomBlock, compileQuotientBlock, map_eq_pure_bind, bind_assoc, pure_bind]

theorem block_run (source : Source) (context : CompileEnv × BlockEnv) (before after : BlockState) (output : BlockResult)
    (ran : rawRun (block source) context before = (.ok output, after)) :
    ∃ value : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr,
      rawRun (compile source) context before = (.ok value, after) ∧
      buildConstantWithSharing context.1.sharingLimits value.1 after.refs after.univs = .ok output.block ∧
      DefinitionBlock.Wrapped output := by
  rw [block_eq] at ran
  obtain ⟨value, middle, compiled, finished⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  rw [DefinitionBlock.rawRun_timedC, DefinitionBlock.finish_run] at finished
  cases built : buildConstantWithSharing context.1.sharingLimits value.1 middle.refs middle.univs with
  | error error => simp [built, Except.map] at finished
  | ok target =>
    simp only [built, Except.map, Prod.mk.injEq, Except.ok.injEq] at finished
    obtain ⟨rfl, rfl⟩ := finished
    exact ⟨value, compiled, built, DefinitionBlock.wrapped_mk _ _⟩

theorem array_one (values : Array α) (size : values.size = 1) : ∃ value, values = #[value] := by
  rcases values with ⟨values⟩
  cases values with
  | nil => simp at size
  | cons value rest =>
    have empty : rest = [] := by simpa using size
    subst rest
    exact ⟨value, rfl⟩

theorem payload_roots (source : Source) (type : Ixon.Expr) : constantInfoRootExprs (payload source type) = #[type] := by
  cases source <;> rfl

theorem writeback (source : Source) (type : Ixon.Expr) (roots : Array Ixon.Expr) (info : Ixon.ConstantInfo)
    (size : roots.size = 1) (ran : withRootExprs (payload source type) roots = .ok info) :
    ∃ output, roots = #[output] ∧ info = payload source output := by
  obtain ⟨output, rfl⟩ := array_one roots size
  have actual : withRootExprs (payload source type) #[output] = .ok (payload source output) := by
    cases source <;> rfl
  rw [actual] at ran
  exact ⟨output, rfl, (Except.ok.inj ran).symm⟩

theorem sharing_read (reader : Kernel.Reader.Ctx) (params : Nat → Kernel.Name)
    (self : Nat → Option Kernel.Name) (limits : Ix.Sharing.Exact.Limits) (source : Source)
    (type : Ixon.Expr) (refs : Array Address) (univs : Array Ixon.Univ) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (payload source type) refs univs = .ok output) :
    ∃ target, output.info = payload source target ∧
      (Kernel.Reader.MemberReader.mk' reader output params self).read target =
        (Kernel.Reader.MemberReader.mk' reader { info := payload source type, sharing := #[], refs, univs } params self).read type := by
  obtain ⟨shared, info, sharedRan, size, written, shape⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  rw [payload_roots] at sharedRan size
  obtain ⟨target, roots, header⟩ := writeback source type shared.result.roots info size written
  subst info
  subst output
  have meaning := Ix.Sharing.Verify.CanonicalMeaning.canonicalSharingTiered_meaning .tagN limits #[type] shared sharedRan
  rw [roots] at meaning
  have readings := SharingRead.meaning_read_before reader
    { info := payload source type, sharing := #[], refs, univs }
    { info := payload source target, sharing := shared.result.sharing, refs, univs }
    params self rfl rfl rfl #[type] #[target] meaning
  refine ⟨target, rfl, ?_⟩
  have first := congrArg (fun results : Array (Kernel.Reader.ReadM Kernel.Expr) => results[0]?) readings
  simpa using first

theorem sharing_wire (limits : Ix.Sharing.Exact.Limits) (source : Source) (type : Ixon.Expr)
    (state : BlockState) (wire : BlockWireTablesWF state) (output : Ixon.Constant)
    (ran : buildConstantWithSharing limits (payload source type) state.refs state.univs = .ok output) : output.wireWF := by
  obtain ⟨shared, info, sharedRan, size, written, shape⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok ran
  obtain ⟨entries, rootsWire, capacity, _, _⟩ := Ix.Sharing.Verify.Tiered.canonicalSharingTiered_format sharedRan
  rw [payload_roots] at size
  obtain ⟨target, roots, header⟩ := writeback source type shared.result.roots info size written
  subst info
  subst output
  rw [roots] at rootsWire
  refine ⟨?_, capacity, ?_, wire.refsCount, wire.refs, wire.univsCount, wire.univs⟩
  · cases source <;> exact rootsWire target (by simp)
  · intro expression member
    exact entries expression (by simpa using member)

theorem block_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Source) (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.NoSelf context.2 source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : BlockResult) (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (block source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Wrapped output ∧
      source.cnst.levelParams.size < UInt64.size ∧
      HeaderEmission.Related (Kernel.Reader.MemberReader.mk' (SharingRead.blobContext reader after) output.block
        (Kernel.Reader.paramOf params) (fun _ => none)) names params source output.block.info := by
  obtain ⟨value, compiled, built, wrapped⟩ := block_run source context before after output ran
  have headerBound := compile_bound source context before after value compiled
  obtain ⟨clean, type, target, info, related, read⟩ := HeaderEmission.compile_correct reader base names params bindings context source
    arity scope aligned external before after value ready compiled
  rw [info] at built
  obtain ⟨sharedType, outputInfo, sharedRead⟩ := sharing_read (SharingRead.blobContext reader after) (Kernel.Reader.paramOf params)
    (fun _ => none) context.1.sharingLimits source type after.refs after.univs output.block built
  rw [SharingRead.unshared_read reader base (Kernel.Reader.paramOf params) (fun _ => none) after clean.2.2] at sharedRead
  exact ⟨clean, wrapped, headerBound, sharedType, target, outputInfo, related, sharedRead.trans read⟩

theorem block_wire (source : Source) (context : CompileEnv × BlockEnv) (before after : BlockState) (output : BlockResult)
    (valid : EmissionWire.Valid context.1 before)
    (ran : rawRun (block source) context before = (.ok output, after)) :
    output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block := by
  obtain ⟨value, compiled, built, wrapped⟩ := block_run source context before after output ran
  have finalWire := (compile_wire source context before valid value after compiled).1.2.1
  rw [compile_shape source context before after value compiled] at built
  have outputWire := sharing_wire context.1.sharingLimits source value.2.2 after finalWire output.block built
  refine ⟨outputWire, ?_⟩
  rw [wrapped.1]
  exact Ixon.Verify.deConstant_serConstant output.block outputWire

def info : Source → CompileM BlockResult
  | .axio source => compileAxiomInfo source
  | .quot source => compileQuotientInfo source

theorem info_eq (source : Source) : info source = (do
    preseedExprTables #[(source.cnst.type, source.cnst.levelParams.toList)]
    block source) := by cases source <;> rfl

theorem block_shape (source : Source) (context : CompileEnv × BlockEnv) (before after : BlockState) (output : BlockResult)
    (ran : rawRun (block source) context before = (.ok output, after)) :
    DefinitionBlock.Wrapped output ∧ source.cnst.levelParams.size < UInt64.size ∧
      ∃ type, output.block.info = payload source type := by
  obtain ⟨value, compiled, built, wrapped⟩ := block_run source context before after output ran
  have bounded := compile_bound source context before after value compiled
  rw [compile_shape source context before after value compiled] at built
  obtain ⟨shared, targetInfo, _, size, written, shape⟩ := Ix.Sharing.Verify.buildConstantWithSharing_eq_ok built
  rw [payload_roots] at size
  obtain ⟨type, _, header⟩ := writeback source value.2.2 shared.result.roots targetInfo size written
  rw [shape, header]
  exact ⟨wrapped, bounded, type, rfl⟩

theorem info_shape (source : Source) (context : CompileEnv × BlockEnv) (before after : BlockState) (output : BlockResult)
    (ran : rawRun (info source) context before = (.ok output, after)) :
    DefinitionBlock.Wrapped output ∧ source.cnst.levelParams.size < UInt64.size ∧
      ∃ type, output.block.info = payload source type := by
  rw [info_eq] at ran
  obtain ⟨_, middle, _, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  exact block_shape source context middle after output compiled

theorem info_correct_checked (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Source) (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.NoSelf context.2 source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : BlockResult) (ready : DefinitionEmission.Ready bindings before)
    (wire : BlockWireTablesWF before) (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (info source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Wrapped output ∧
      source.cnst.levelParams.size < UInt64.size ∧ output.block.wireWF ∧
      Ixon.deConstant output.blockBytes = .ok output.block ∧
      HeaderEmission.Related (Kernel.Reader.MemberReader.mk' (SharingRead.blobContext reader after) output.block
        (Kernel.Reader.paramOf params) (fun _ => none)) names params source output.block.info := by
  rw [info_eq] at ran
  obtain ⟨done, middle, seeded, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases done
  have prepared := PreseedState.preseed_ready_checked context _ bindings before middle ready seeded
  have tables := PreseedWire.preseed_wire_checked context _ before middle wire widths seeded
  have middleWidths : ReferenceWidths.LookupWidths context.1 middle := by
    intro name address found
    rw [prepared.1.bindings, ← ready.bindings] at found
    exact widths name address found
  have related := block_correct reader base names params bindings context source arity scope aligned external middle after output prepared.1 compiled
  have codec := block_wire source context middle after output ⟨middleWidths, tables, prepared.2.1⟩ compiled
  exact ⟨related.1, related.2.1, related.2.2.1, codec.1, codec.2, related.2.2.2⟩

theorem info_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Source) (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.NoSelf context.2 source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : BlockResult) (ready : DefinitionEmission.Ready bindings before)
    (wire : BlockWireTablesWF before) (widths : ReferenceWidths.LookupWidths context.1 before)
    (bounded : PreseedBounds.ExprBound source.cnst.type)
    (ran : rawRun (info source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Wrapped output ∧
      source.cnst.levelParams.size < UInt64.size ∧ output.block.wireWF ∧
      Ixon.deConstant output.blockBytes = .ok output.block ∧
      HeaderEmission.Related (Kernel.Reader.MemberReader.mk' (SharingRead.blobContext reader after) output.block
        (Kernel.Reader.paramOf params) (fun _ => none)) names params source output.block.info :=
  (fun _ => info_correct_checked reader base names params bindings context source arity scope aligned external
    before after output ready wire widths ran) bounded

end Ix.CompileCert.HeaderBlock
