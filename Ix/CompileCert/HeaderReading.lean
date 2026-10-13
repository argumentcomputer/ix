import Ix.CompileCert.HeaderBlock

/-! Axiom and quotient constant dispatch through the actual anonymous reader.
The source type's self-scope condition is explicit. Unsafe axiom records are
refused independently of their type reading; kernel admission remains separate. -/

namespace Ix.CompileCert.HeaderReading

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame Kernel.Reader
abbrev Source := HeaderEmission.Source

def constant : Source → ConstantInfo
  | .axio source => .axiomInfo source
  | .quot source => .quotInfo source

theorem constant_run (source : Source) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (compileConstantInfo (constant source)) context before =
      rawRun (HeaderBlock.info source) (DefinitionReading.singletonContext source.cnst.name context) before := by
  cases source <;> rfl

def paramsFor (reader : Ctx) (owner : Address) (source : Source) : List Kernel.Name :=
  reader.lpsOf (.member owner 0) source.cnst.levelParams.size

theorem params_length (reader : Ctx) (owner : Address) (source : Source) :
    (paramsFor reader owner source).length = source.cnst.levelParams.size := DefinitionReading.lpsOf_length _ _ _

def declaration (reader : Ctx) (owner : Address) (source : Source) (type : Kernel.Expr) : Kernel.Declaration :=
  let header : Kernel.ConstantVal := ⟨reader.nameOf (.member owner 0), paramsFor reader owner source, type⟩
  match source with
  | .axio _ => .axiomDecl header
  | .quot source => .quotDecl (quotKind (convertQuotKind source.kind)) header

def Readable : Source → Prop
  | .axio source => source.isUnsafe = false
  | .quot _ => True

theorem read_payload (reader : Ctx) (state : State) (owner : Address) (source : Source)
    (record : Ixon.Constant) (type : Ixon.Expr) (value : Kernel.Expr)
    (info : record.info = HeaderEmission.payload source type)
    (bounded : source.cnst.levelParams.size < UInt64.size)
    (read : (MemberReader.mk' reader record (paramOf (paramsFor reader owner source)) (fun _ => none)).read type = .ok value)
    (safe : Readable source) :
    readRecord reader state owner record = .ok { decls := #[declaration reader owner source value] } := by
  have count := UInt64.toNat_ofNat_of_lt' bounded
  cases source with
  | axio source =>
    change source.isUnsafe = false at safe
    simp only [HeaderEmission.payload] at info
    simp only [readRecord, info, safe, Bool.false_eq_true, ↓reduceIte]
    change source.cnst.levelParams.size.toUInt64.toNat = source.cnst.levelParams.size at count
    rw [count]
    change (do
      let type ← (MemberReader.mk' reader record (paramOf (paramsFor reader owner (.axio source))) (fun _ => none)).read type
      pure ({ decls := #[declaration reader owner (.axio source) type] } : Read)) = _
    rw [read]
    rfl
  | quot source =>
    simp only [HeaderEmission.payload] at info
    simp only [readRecord, info]
    change source.cnst.levelParams.size.toUInt64.toNat = source.cnst.levelParams.size at count
    rw [count]
    change (do
      let type ← (MemberReader.mk' reader record (paramOf (paramsFor reader owner (.quot source))) (fun _ => none)).read type
      pure ({ decls := #[declaration reader owner (.quot source) type] } : Read)) = _
    rw [read]
    rfl

theorem unsafe_axiom (reader : Ctx) (state : State) (owner : Address)
    (source : AxiomVal) (record : Ixon.Constant) (type : Ixon.Expr)
    (info : record.info = HeaderEmission.payload (.axio source) type) (unsafeSource : source.isUnsafe = true) :
    readRecord reader state owner record = .error (.declined "unsafe axiom") := by
  simp [readRecord, info, HeaderEmission.payload, unsafeSource, declined, throw, throwThe, MonadExceptOf.throw]
  rfl

/-- An unsafe axiom produced by the actual dispatcher is refused before its
type is read. No source-type scope or reader-prefix premise is required. -/
theorem constant_declines (reader : Ctx) (state : State) (context : CompileEnv × BlockEnv)
    (source : AxiomVal) (unsafeSource : source.isUnsafe = true)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileConstantInfo (.axiomInfo source)) context before = (.ok output, after)) :
    readRecord reader state output.blockAddr output.block = .error (.declined "unsafe axiom") := by
  change rawRun (compileConstantInfo (constant (.axio source))) context before = (.ok output, after) at ran
  rw [constant_run] at ran
  obtain ⟨_, _, type, info⟩ := HeaderBlock.info_shape (.axio source) _ before after output ran
  exact unsafe_axiom reader state output.blockAddr source output.block type info unsafeSource

/-- Complete public axiom/quotient dispatch, sharing, bytes and whole-record
reading, under the source type's actual self-scope and prefix/resource contract.
The result contains exactly the expected declaration; it is not an admission
or source-domain totality theorem. -/
theorem constant_reads_checked (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (source : Source)
    (before after : BlockState) (output : BlockResult) (state : State)
    (scope : ExpressionScope.NoSelf (DefinitionReading.singletonContext source.cnst.name context).2 source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (ready : DefinitionEmission.Ready bindings before) (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (safe : Readable source)
    (ran : rawRun (compileConstantInfo (constant source)) context before = (.ok output, after)) :
    DefinitionBlock.Wrapped output ∧ output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block ∧
      ∃ type, ExpressionState.Related names source.cnst.levelParams.toList (paramsFor reader output.blockAddr source) source.cnst.type type ∧
        readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block =
          .ok { decls := #[declaration reader output.blockAddr source type] } := by
  rw [constant_run] at ran
  obtain ⟨_, wrapped, headerBound, outputWire, bytes, target, type, info, related, read⟩ :=
    HeaderBlock.info_correct_checked reader base names (paramsFor reader output.blockAddr source) bindings
      (DefinitionReading.singletonContext source.cnst.name context) source (params_length reader output.blockAddr source)
      scope aligned external before after output ready wire widths ran
  have recordRead := read_payload (SharingRead.blobContext reader after) state output.blockAddr source output.block target type info headerBound read safe
  exact ⟨wrapped, outputWire, bytes, type, related, recordRead⟩

theorem constant_reads (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (source : Source)
    (before after : BlockState) (output : BlockResult) (state : State)
    (scope : ExpressionScope.NoSelf (DefinitionReading.singletonContext source.cnst.name context).2 source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (ready : DefinitionEmission.Ready bindings before) (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (bounded : PreseedBounds.ExprBound source.cnst.type) (safe : Readable source)
    (ran : rawRun (compileConstantInfo (constant source)) context before = (.ok output, after)) :
    DefinitionBlock.Wrapped output ∧ output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block ∧
      ∃ type, ExpressionState.Related names source.cnst.levelParams.toList (paramsFor reader output.blockAddr source) source.cnst.type type ∧
        readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block =
          .ok { decls := #[declaration reader output.blockAddr source type] } :=
  (fun _ => constant_reads_checked reader base names bindings context source before after output state scope aligned external
    ready wire widths safe ran) bounded

end Ix.CompileCert.HeaderReading
