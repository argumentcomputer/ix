import Ix.CompileCert.DeclarationHeaders
import Ix.CompileCert.EmissionWire
import IxC.Kernel.Ixon.ReaderSpec
import Ix.CompileCert.Canon.Ctx

/-! Connect actual singleton compilation to the kernel's whole-record reader.
Parameter arity is derived, and safety refusal is explicit. The reader's
projection rewrite is recorded by its existing specification; this module
does not assume that rewrite preserves denotation or that the record is admitted. -/

namespace Ix.CompileCert.DefinitionReading

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame
open Kernel.Reader
open _root_.Ix.Kernel (ConstRef)

def selfAt (reader : Ctx) (owner : Address) : Nat → Option Kernel.Name :=
  fun index => if index == 0 then some (reader.nameOf (.member owner 0)) else none

def paramsFor (reader : Ctx) (owner : Address) (source : Def) : List Kernel.Name :=
  reader.lpsOf (.member owner 0) source.levelParams.size

theorem lpsOf_length (reader : Ctx) (reference : ConstRef Address) (count : Nat) :
    (reader.lpsOf reference count).length = count := by
  unfold Ctx.lpsOf
  cases reader.pins.levels[reference]? with
  | none => simp [levelNames]
  | some params =>
    dsimp only
    by_cases equal : params.length = count
    · simp [equal]
    · simp [equal, levelNames]

theorem params_length (reader : Ctx) (owner : Address) (source : Def) :
    (paramsFor reader owner source).length = source.levelParams.size := lpsOf_length _ _ _

theorem blob_params (reader : Ctx) (state : BlockState) (owner : Address) (source : Def) :
    paramsFor (SharingRead.blobContext reader state) owner source = paramsFor reader owner source := rfl

theorem blob_self (reader : Ctx) (state : BlockState) (owner : Address) :
    selfAt (SharingRead.blobContext reader state) owner = selfAt reader owner := rfl

/-- The actual reader's policy, expressed on source header fields. It does not
classify source typing or define the compiler's validity domain. -/
def safetyReason (source : Def) : Option String :=
  safetyDecline (DefinitionEmission.definitionPayload source (.sort 0) (.var 0))

def Readable (source : Def) : Prop :=
  match source.kind with
  | .defn => source.safety = .safe
  | .opaq => source.safety ≠ .unsaf
  | .thm => True

theorem safetyReason_none (source : Def) : safetyReason source = none ↔ Readable source := by
  cases kind : source.kind <;> cases safety : source.safety <;>
    simp [safetyReason, safetyDecline, DefinitionEmission.definitionPayload, Readable, kind, safety]
  all_goals rfl

theorem safety_eq (source : Def) (target : Ixon.Definition)
    (kind : target.kind = source.kind) (safety : target.safety = source.safety) :
    safetyDecline target = safetyReason source := by
  simp only [safetyDecline, safetyReason, DefinitionEmission.definitionPayload, kind, safety]
  rfl

theorem definition_returns (reader : Ctx) (state : State) (heights : Kernel.Name → Nat)
    (reference : ConstRef Address) (params : List Kernel.Name) (member : MemberReader)
    (target : Ixon.Definition) (type value : Kernel.Expr)
    (typeRead : member.read target.typ = .ok type) (valueRead : member.read target.value = .ok value)
    (safe : safetyDecline target = none) :
    ∃ declaration rewritten, readDefinition reader state heights reference params member target = .ok (declaration, rewritten) ∧
      DefinitionDecl ⟨reader.nameOf reference, params, type⟩ value
        (projRewrite state ⟨reader.nameOf reference, params, type⟩ value) target.kind declaration := by
  have succeeds : ∃ declaration rewritten,
      readDefinition reader state heights reference params member target = .ok (declaration, rewritten) := by
    unfold readDefinition
    simp only [typeRead, valueRead, safe, bind, Except.bind]
    exact ⟨_, _, rfl⟩
  obtain ⟨declaration, rewritten, read⟩ := succeeds
  obtain ⟨actualType, actualValue, actualTypeRead, actualValueRead, specified⟩ := readDefinition_spec read
  have sameType := Except.ok.inj (actualTypeRead.symm.trans typeRead)
  have sameValue := Except.ok.inj (actualValueRead.symm.trans valueRead)
  subst actualType
  subst actualValue
  exact ⟨declaration, rewritten, read, specified⟩

theorem definition_declines (reader : Ctx) (state : State) (heights : Kernel.Name → Nat)
    (reference : ConstRef Address) (params : List Kernel.Name) (member : MemberReader)
    (target : Ixon.Definition) (type value : Kernel.Expr) (reason : String)
    (typeRead : member.read target.typ = .ok type) (valueRead : member.read target.value = .ok value)
    (policy : safetyDecline target = some reason) :
    readDefinition reader state heights reference params member target = .error (.declined reason) := by
  simp [readDefinition, typeRead, valueRead, policy, bind, Except.bind, declined, throw, throwThe, MonadExceptOf.throw]

theorem singleton_returns (reader : Ctx) (state : State) (owner : Address)
    (record : Ixon.Constant) (target : Ixon.Definition) (info : record.info = .defn target)
    (type value : Kernel.Expr)
    (typeRead : (definitionReader reader owner record target).read target.typ = .ok type)
    (valueRead : (definitionReader reader owner record target).read target.value = .ok value)
    (safe : safetyDecline target = none) :
    ∃ result declaration, readRecord reader state owner record = .ok result ∧ result.decls = #[declaration] ∧
      DefinitionDecl ⟨reader.nameOf (.member owner 0), singletonLps reader owner target.lvls, type⟩ value
        (projRewrite state ⟨reader.nameOf (.member owner 0), singletonLps reader owner target.lvls, type⟩ value)
        target.kind declaration := by
  obtain ⟨declaration, rewritten, read, specified⟩ := definition_returns reader state (state.heights.getD · 0)
    (.member owner 0) (singletonLps reader owner target.lvls) (definitionReader reader owner record target)
    target type value typeRead valueRead safe
  refine ⟨{ decls := #[declaration], projRewrites := if rewritten then 1 else 0 }, declaration, ?_, rfl, specified⟩
  simp only [readRecord, info]
  change (do
    let (decl, flag) ← readDefinition reader state (state.heights.getD · 0) (.member owner 0)
      (singletonLps reader owner target.lvls) (definitionReader reader owner record target) target
    pure ({ decls := #[decl], projRewrites := if flag then 1 else 0 } : Read)) = _
  rw [read]
  rfl

theorem singleton_declines (reader : Ctx) (state : State) (owner : Address)
    (record : Ixon.Constant) (target : Ixon.Definition) (info : record.info = .defn target)
    (type value : Kernel.Expr) (reason : String)
    (typeRead : (definitionReader reader owner record target).read target.typ = .ok type)
    (valueRead : (definitionReader reader owner record target).read target.value = .ok value)
    (policy : safetyDecline target = some reason) :
    readRecord reader state owner record = .error (.declined reason) := by
  have read := definition_declines reader state (state.heights.getD · 0) (.member owner 0)
    (singletonLps reader owner target.lvls) (definitionReader reader owner record target)
    target type value reason typeRead valueRead policy
  simp only [readRecord, info]
  change (do
    let (decl, flag) ← readDefinition reader state (state.heights.getD · 0) (.member owner 0)
      (singletonLps reader owner target.lvls) (definitionReader reader owner record target) target
    pure ({ decls := #[decl], projRewrites := if flag then 1 else 0 } : Read)) = _
  rw [read]
  rfl

/-- Source correspondence uses the exact parameter names and self slot chosen
by the whole-record reader. It concerns the body before projection rewriting. -/
def RawReading (reader : Ctx) (owner : Address) (source : Def) (record : Ixon.Constant)
    (names : Name → Kernel.Name → Prop) : Prop :=
  ∃ target : Ixon.Definition, ∃ type value : Kernel.Expr,
    record.info = .defn target ∧ target.kind = source.kind ∧ target.safety = source.safety ∧
      target.lvls.toNat = source.levelParams.size ∧
      ExpressionState.Related names source.levelParams.toList (paramsFor reader owner source) source.type type ∧
      ExpressionState.Related names source.levelParams.toList (paramsFor reader owner source) source.value value ∧
      (definitionReader reader owner record target).read target.typ = .ok type ∧
      (definitionReader reader owner record target).read target.value = .ok value

theorem compile_raw_checked (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (source : Def)
    (before after : BlockState) (output : BlockResult)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 (selfAt reader output.blockAddr) names)
    (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Wrapped output ∧
      RawReading (SharingRead.blobContext reader after) output.blockAddr source output.block names := by
  have compiled := PreseedState.compileDefinitionDataInfo_correct_checked reader base (selfAt reader output.blockAddr) names
    (paramsFor reader output.blockAddr source) bindings context source (params_length reader output.blockAddr source)
    aligned external selfSound before ready output after ran
  obtain ⟨clean, wrapped, target, info, kind, safety, _, type, value, typeRel, valueRel, typeRead, valueRead⟩ := compiled
  obtain ⟨headerTarget, headerInfo, headerLevels⟩ := DeclarationHeaders.definitionInfo source context before output after ran
  have sameTarget := Ixon.ConstantInfo.defn.inj (info.symm.trans headerInfo)
  subst headerTarget
  have paramsEq : singletonLps (SharingRead.blobContext reader after) output.blockAddr target.lvls =
      paramsFor reader output.blockAddr source := by
    unfold singletonLps paramsFor
    rw [headerLevels]
    rfl
  have readerEq : definitionReader (SharingRead.blobContext reader after) output.blockAddr output.block target =
      MemberReader.mk' (SharingRead.blobContext reader after) output.block
        (paramOf (paramsFor reader output.blockAddr source)) (selfAt reader output.blockAddr) := by
    unfold definitionReader
    rw [paramsEq]
    rfl
  refine ⟨clean, wrapped, target, type, value, info, kind, safety, headerLevels, typeRel, valueRel, ?_, ?_⟩
  · rw [readerEq]; exact typeRead
  · rw [readerEq]; exact valueRead

theorem compile_raw (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (source : Def)
    (before after : BlockState) (output : BlockResult)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 (selfAt reader output.blockAddr) names)
    (ready : DefinitionEmission.Ready bindings before)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ DefinitionBlock.Wrapped output ∧
      RawReading (SharingRead.blobContext reader after) output.blockAddr source output.block names :=
  (fun _ _ => compile_raw_checked reader base names bindings context source before after output aligned external selfSound ready ran) typeBound valueBound

/-- The real declaration shape, retaining the reader's specified projection
rewrite. Denotational preservation of that rewrite is a separate obligation. -/
def DeclarationReading (reader : Ctx) (state : State) (owner : Address) (source : Def)
    (names : Name → Kernel.Name → Prop) (result : Read) : Prop :=
  ∃ type value declaration,
    result.decls = #[declaration] ∧
    ExpressionState.Related names source.levelParams.toList (paramsFor reader owner source) source.type type ∧
    ExpressionState.Related names source.levelParams.toList (paramsFor reader owner source) source.value value ∧
    DefinitionDecl ⟨reader.nameOf (.member owner 0), paramsFor reader owner source, type⟩ value
      (projRewrite state ⟨reader.nameOf (.member owner 0), paramsFor reader owner source, type⟩ value)
      source.kind declaration

theorem RawReading.reads {reader : Ctx} {owner : Address} {source : Def} {record : Ixon.Constant}
    {names : Name → Kernel.Name → Prop} (raw : RawReading reader owner source record names)
    (state : State) (safe : safetyReason source = none) :
    ∃ result, readRecord reader state owner record = .ok result ∧ DeclarationReading reader state owner source names result := by
  obtain ⟨target, type, value, info, kind, safety, levels, typeRel, valueRel, typeRead, valueRead⟩ := raw
  have policy := (safety_eq source target kind safety).trans safe
  obtain ⟨result, declaration, read, singleton, specified⟩ := singleton_returns reader state owner record target info
    type value typeRead valueRead policy
  have paramsEq : singletonLps reader owner target.lvls = paramsFor reader owner source := by
    unfold singletonLps paramsFor
    rw [levels]
  rw [paramsEq, kind] at specified
  exact ⟨result, read, type, value, declaration, singleton, typeRel, valueRel, specified⟩

theorem RawReading.declines {reader : Ctx} {owner : Address} {source : Def} {record : Ixon.Constant}
    {names : Name → Kernel.Name → Prop} (raw : RawReading reader owner source record names)
    (state : State) (reason : String) (policy : safetyReason source = some reason) :
    readRecord reader state owner record = .error (.declined reason) := by
  obtain ⟨target, type, value, info, kind, safety, _, _, _, typeRead, valueRead⟩ := raw
  exact singleton_declines reader state owner record target info type value reason typeRead valueRead
    ((safety_eq source target kind safety).trans policy)

/-- Successful production compilation supplies actual whole-record reader
success under the explicit source safety policy. Neither reader success nor
an arbitrary parameter telescope is assumed. -/
theorem compile_reads (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (source : Def)
    (before after : BlockState) (output : BlockResult) (state : State)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 (selfAt reader output.blockAddr) names)
    (ready : DefinitionEmission.Ready bindings before)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (safe : safetyReason source = none)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    ∃ result, readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block = .ok result ∧
      DeclarationReading (SharingRead.blobContext reader after) state output.blockAddr source names result :=
  (compile_raw reader base names bindings context source before after output aligned external selfSound ready typeBound valueBound ran).2.2.reads state safe

theorem compile_declines (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv) (source : Def)
    (before after : BlockState) (output : BlockResult) (state : State) (reason : String)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (selfSound : ExpressionState.SelfCorrect context.2 (selfAt reader output.blockAddr) names)
    (ready : DefinitionEmission.Ready bindings before)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (policy : safetyReason source = some reason)
    (ran : rawRun (compileDefinitionDataInfo source) context before = (.ok output, after)) :
    readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block = .error (.declined reason) :=
  (compile_raw reader base names bindings context source before after output aligned external selfSound ready typeBound valueBound ran).2.2.declines state reason policy

/-- Exact definition-like source extraction, matching the three public
constant-dispatch branches. It is independent of compiler success. -/
def sourceData : ConstantInfo → Option Def
  | .defnInfo value => some (definitionValData value)
  | .thmInfo value => some (theoremValData value)
  | .opaqueInfo value => some (opaqueValData value)
  | _ => none

def singletonContext (name : Name) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := (Std.TreeMap.empty : MutCtx).insert name 0 })

theorem constant_run (info : ConstantInfo) (source : Def) (view : sourceData info = some source)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (compileConstantInfo info) context before =
      rawRun (compileDefinitionDataInfo source) (singletonContext source.name context) before := by
  cases info <;> simp only [sourceData] at view
  all_goals cases view <;> rfl

/-- The compiler's Name comparison is hash-based. State the needed local
alias correspondence explicitly rather than assuming hash injectivity. -/
def SelfAliases (source : Name) (target : Kernel.Name) (names : Name → Kernel.Name → Prop) : Prop :=
  ∀ query, (source == query) = true → names query target

theorem singleton_self (reader : Ctx) (owner : Address) (source : Def)
    (context : CompileEnv × BlockEnv) (names : Name → Kernel.Name → Prop)
    (aliases : SelfAliases source.name (reader.nameOf (.member owner 0)) names) :
    ExpressionState.SelfCorrect (singletonContext source.name context).2 (selfAt reader owner) names := by
  intro query index found
  change ((Std.TreeMap.empty : MutCtx).insert source.name 0)[query]? = some index at found
  rw [Canon.treeMap_insert_getElem?] at found
  split at found
  · rename_i sameKey
    cases Option.some.inj found
    exact ⟨reader.nameOf (.member owner 0), by simp [selfAt], aliases query sameKey⟩
  · simp at found

/-- Public constant dispatch, actual singleton self binding and the whole
kernel record reader, with returned-byte decoding. The source safety policy
and prefix/source resource conditions are explicit; kernel admission and
projection-rewrite semantic preservation are not assumed or asserted. -/
theorem constant_reads_checked (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (info : ConstantInfo) (source : Def) (view : sourceData info = some source)
    (before after : BlockState) (output : BlockResult) (state : State)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (aliases : SelfAliases source.name (reader.nameOf (.member output.blockAddr 0)) names)
    (ready : DefinitionEmission.Ready bindings before)
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (safe : Readable source)
    (ran : rawRun (compileConstantInfo info) context before = (.ok output, after)) :
    DefinitionBlock.Wrapped output ∧ output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block ∧
      ∃ result, readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block = .ok result ∧
        DeclarationReading (SharingRead.blobContext reader after) state output.blockAddr source names result := by
  rw [constant_run info source view] at ran
  have raw := compile_raw_checked reader base names bindings (singletonContext source.name context) source before after output
    aligned external (singleton_self reader output.blockAddr source context names aliases) ready ran
  have reading := raw.2.2.reads state ((safetyReason_none source).mpr safe)
  have codec := EmissionWire.compileDefinitionDataInfo_codec_checked (singletonContext source.name context) source bindings before after
    ready wire widths output ran
  exact ⟨raw.2.1, codec.2.1, codec.2.2, reading⟩

theorem constant_reads (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (info : ConstantInfo) (source : Def) (view : sourceData info = some source)
    (before after : BlockState) (output : BlockResult) (state : State)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (aliases : SelfAliases source.name (reader.nameOf (.member output.blockAddr 0)) names)
    (ready : DefinitionEmission.Ready bindings before)
    (wire : Ix.Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (safe : Readable source)
    (ran : rawRun (compileConstantInfo info) context before = (.ok output, after)) :
    DefinitionBlock.Wrapped output ∧ output.block.wireWF ∧ Ixon.deConstant output.blockBytes = .ok output.block ∧
      ∃ result, readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block = .ok result ∧
        DeclarationReading (SharingRead.blobContext reader after) state output.blockAddr source names result :=
  (fun _ _ => constant_reads_checked reader base names bindings context info source view before after output state
    aligned external aliases ready wire widths safe ran) typeBound valueBound

theorem constant_declines_checked (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (info : ConstantInfo) (source : Def) (view : sourceData info = some source)
    (before after : BlockState) (output : BlockResult) (state : State) (reason : String)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (aliases : SelfAliases source.name (reader.nameOf (.member output.blockAddr 0)) names)
    (ready : DefinitionEmission.Ready bindings before)
    (policy : safetyReason source = some reason)
    (ran : rawRun (compileConstantInfo info) context before = (.ok output, after)) :
    readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block = .error (.declined reason) := by
  rw [constant_run info source view] at ran
  exact (compile_raw_checked reader base names bindings (singletonContext source.name context) source before after output
    aligned external (singleton_self reader output.blockAddr source context names aliases) ready ran).2.2.declines state reason policy

theorem constant_declines (reader : Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (info : ConstantInfo) (source : Def) (view : sourceData info = some source)
    (before after : BlockState) (output : BlockResult) (state : State) (reason : String)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (aliases : SelfAliases source.name (reader.nameOf (.member output.blockAddr 0)) names)
    (ready : DefinitionEmission.Ready bindings before)
    (typeBound : PreseedBounds.ExprBound source.type) (valueBound : PreseedBounds.ExprBound source.value)
    (policy : safetyReason source = some reason)
    (ran : rawRun (compileConstantInfo info) context before = (.ok output, after)) :
    readRecord (SharingRead.blobContext reader after) state output.blockAddr output.block = .error (.declined reason) :=
  (fun _ _ => constant_declines_checked reader base names bindings context info source view before after output state reason
    aligned external aliases ready policy ran) typeBound valueBound

end Ix.CompileCert.DefinitionReading
