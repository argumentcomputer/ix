import Ix.CompileCert.ConstructorEmission

/-! Actual ordinary and mutual inductive payload compilation, with exact
anonymous headers and source-related type/constructor readings. This is before
sharing and whole-record reading; source-family validity and admission remain
separate obligations. -/

namespace Ix.CompileCert.InductiveEmission

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

def sourceData (source : InductiveVal) (constructors : Array ConstructorVal) : Ind :=
  ⟨source.cnst.name, source.cnst.levelParams, source.cnst.type, source.numParams,
    source.numIndices, source.all, constructors, source.numNested, source.isRec,
    source.isReflexive, source.isUnsafe⟩

theorem compileInductive_eq (source : InductiveVal) (constructors : Array ConstructorVal) :
    compileInductive source constructors = compileInductiveData (sourceData source constructors) := rfl

def payload (source : Ind) (type : Ixon.Expr) (constructors : Array Ixon.Constructor) : Ixon.Inductive :=
  { isUnsafe := source.isUnsafe, lvls := source.levelParams.size.toUInt64,
    params := source.numParams.toUInt64, indices := source.numIndices.toUInt64,
    typ := type, ctors := constructors }

def finishChecks (source : Ind) (count : Nat) (block : BlockEnv) : CompileM Unit := do
  let _ ← checkedTableCount "declaration universe parameters" source.levelParams.size
  let _ ← checkedTableCount "inductive parameters" source.numParams
  let _ ← checkedTableCount "inductive indices" source.numIndices
  let _ ← checkedTableCount "inductive constructors" count
  compileName source.name
  compileNames source.levelParams
  compileNames source.all
  compileNames (block.mutCtx.toList.toArray.map (·.1))

theorem metadata_run (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ metadata, rawRun takeInductiveTypeCompileMeta context before =
      (.ok metadata, DefinitionEmission.drained before) := by
  simp only [takeInductiveTypeCompileMeta, takeArena, takeMetaSharing, takeMetaRefs,
    takeUnivPatches, clearExprCache, rawRun_bind, Interning.rawRun_modifyGet,
    rawRun_modify, rawRun_pure, DefinitionEmission.drained]
  exact ⟨_, rfl⟩

theorem finish_run (source : Ind) (type : Ixon.Expr) (root : UInt64)
    (typeMeta : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ metadata, rawRun (finishInductiveDataCompilation source type root typeMeta constructors) context before =
      rawRun (do
        finishChecks source constructors.ctors.size context.2
        pure (payload source type constructors.ctors, metadata, constructors.ctorMetaPairs,
          constructors.ctorExprs)) context before := by
  simp only [finishInductiveDataCompilation, finishChecks, getMutCtxAddrs,
    UniverseMeaning.rawRun_readBlock, rawRun_bind, rawRun_pure, bind_assoc, payload]
  exact ⟨_, rfl⟩

section Finish

variable (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
  (self : Nat → Option Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)

theorem checks_preserve (source : Ind) (count : Nat)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address) :
    DefinitionEmission.Preserves reader base param self bindings context (finishChecks source count context.2) := by
  unfold finishChecks
  with_reducible repeat' first
    | exact HeaderEmission.count_preserves reader base param self bindings context _ _
    | exact DefinitionEmission.Preserves.compileName reader base param self bindings context _ aligned
    | exact DefinitionEmission.Preserves.compileNames reader base param self bindings context _ aligned
    | refine DefinitionEmission.Preserves.bind reader base param self bindings context ?_ (fun _ => ?_)

theorem finish_correct (source : Ind) (type : Ixon.Expr) (root : UInt64)
    (typeMeta : InductiveTypeCompileMeta) (constructors : InductiveConstructorCompileState)
    (before after : BlockState)
    (output : Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr)
    (clean : DefinitionEmission.Clean bindings before)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (ran : rawRun (finishInductiveDataCompilation source type root typeMeta constructors) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends (ExpressionRead.blockReader reader base param self before).ecx
        (ExpressionRead.blockReader reader base param self after).ecx ∧
      output.1 = payload source type constructors.ctors ∧
      output.2.2 = (constructors.ctorMetaPairs, constructors.ctorExprs) := by
  obtain ⟨metadata, expanded⟩ := finish_run source type root typeMeta constructors context before
  rw [expanded] at ran
  obtain ⟨done, middle, checkedRun, returned⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  rw [rawRun_pure] at returned
  obtain ⟨outEq, stateEq⟩ := Prod.mk.inj returned
  cases stateEq
  have preserved := checks_preserve reader base param self bindings context source constructors.ctors.size aligned before clean
  rw [checkedRun] at preserved
  cases Except.ok.inj outEq
  exact ⟨preserved.1, preserved.2, rfl, rfl⟩

end Finish

def Related (reader : Kernel.Reader.MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (source : Ind) (target : Ixon.Inductive) : Prop :=
  target.isUnsafe = source.isUnsafe ∧ target.lvls.toNat = source.levelParams.size ∧
    target.params.toNat = source.numParams ∧ target.indices.toNat = source.numIndices ∧
    (∃ type, ExpressionState.Related names sourceParams params source.type type ∧ reader.read target.typ = .ok type) ∧
    List.Forall₂ (ConstructorEmission.Related reader names sourceParams params) source.ctors.toList target.ctors.toList

def body (source : Ind) :
    CompileM (Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr) := do
  let (type, root) ← compileExpr source.type
  let metadata ← takeInductiveTypeCompileMeta
  let constructors ← compileInductiveConstructors source.ctors.toList { ctorExprs := #[type] }
  finishInductiveDataCompilation source type root metadata constructors

def contextFor (source : Ind) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with current := source.name, univCtx := source.levelParams.toList })

theorem compile_run (source : Ind) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (compileInductiveData source) context before =
      rawRun (body source) (contextFor source context) (DefinitionEmission.prepared before) := by
  simp only [compileInductiveData, withCurrent, withUnivCtx, resetArena, body,
    DefinitionEmission.rawRun_withBlockEnv, rawRun_bind, rawRun_modify,
    contextFor, DefinitionEmission.prepared]

theorem body_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Ind) (arity : params.length = context.2.univCtx.length)
    (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.type)
    (ctorScope : ∀ ctor ∈ source.ctors,
      ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState)
    (output : Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (body source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names context.2.univCtx params source output.1 ∧
      output.2.2.2.toList = output.1.typ :: output.1.ctors.toList.map (·.typ) := by
  rw [body] at ran
  obtain ⟨type, typed, typeRun, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have checked := MetadataErasure.compile_scoped reader base self names params bindings context arity aligned external
    source.type scope before typed type clean typeRun
  obtain ⟨value, meaning, typeRead⟩ := checked.1.2.2 type rfl
  obtain ⟨metadata, drained, drainRun, rest⟩ := PreseedReferences.bind_ok _ _ context typed output after rest
  obtain ⟨actualMetadata, drainEq⟩ := metadata_run context typed
  rw [drainEq] at drainRun
  have stateEq := congrArg Prod.snd drainRun
  cases stateEq
  obtain ⟨constructors, compiled, ctorRun, finishRun⟩ :=
    PreseedReferences.bind_ok _ _ context (DefinitionEmission.drained typed) output after rest
  have ctors := ConstructorEmission.constructors_correct reader base self names params bindings context
    source.ctors.toList arity (fun ctor present => ctorScope ctor (by simpa using present)) aligned external
    { ctorExprs := #[type.1] } (DefinitionEmission.drained typed) compiled constructors
    (DefinitionEmission.drained_clean bindings typed checked.1.1.1 checked.2) ctorRun
  rw [DefinitionEmission.drained_reader reader base (Kernel.Reader.paramOf params) self typed checked.2] at ctors
  have finished := finish_correct reader base (Kernel.Reader.paramOf params) self bindings context source type.1 type.2
    metadata constructors compiled after output ctors.1 aligned finishRun
  have headers := DeclarationHeaders.inductiveDataHeader source type.1 type.2 metadata constructors
    context compiled output after finishRun
  have growth := ExpressionState.extends_trans ctors.2.1 finished.2.1
  obtain ⟨targets, targetEq, ctorMeanings, rootEq⟩ := ctors.2.2
  have targetEq : constructors.ctors.toList = targets := by simpa using targetEq
  have rootEq : constructors.ctorExprs.toList = type.1 :: targets.map (·.typ) := by simpa using rootEq
  refine ⟨finished.1, ExpressionState.extends_trans checked.1.2.1 growth, ?_, ?_⟩
  · refine ⟨?_, headers.1, headers.2.1, headers.2.2, ?_, ?_⟩
    · rw [finished.2.2.1]; rfl
    · refine ⟨value, meaning, ?_⟩
      rw [finished.2.2.1]
      exact ExpressionRead.convExpr_preserves growth (table := #[]) (nextTable := #[])
        (by intros; assumption) type.1 value typeRead
    · rw [finished.2.2.1]
      change List.Forall₂ _ source.ctors.toList constructors.ctors.toList
      rw [targetEq]
      exact ConstructorEmission.list_grows reader base self names context.2.univCtx params
        compiled after finished.2.1 source.ctors.toList targets ctorMeanings
  · rw [finished.2.2.2, finished.2.2.1]
    change constructors.ctorExprs.toList = type.1 :: constructors.ctors.toList.map (·.typ)
    rw [targetEq, rootEq]

theorem compile_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Ind) (arity : params.length = source.levelParams.size)
    (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.type)
    (ctorScope : ∀ ctor ∈ source.ctors,
      ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState)
    (output : Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr)
    (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compileInductiveData source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names source.levelParams.toList params source output.1 ∧
      output.2.2.2.toList = output.1.typ :: output.1.ctors.toList.map (·.typ) := by
  rw [compile_run] at ran
  have result := body_correct reader base self names params bindings (contextFor source context)
    source (by simpa [contextFor] using arity) scope ctorScope aligned external _ after output
    (DefinitionEmission.prepared_clean bindings before ready) ran
  rw [DefinitionEmission.prepared_reader reader base (Kernel.Reader.paramOf params) self before ready.mode] at result
  exact result

theorem ordinary_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors,
      ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState)
    (output : Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr)
    (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compileInductive source constructors) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names source.cnst.levelParams.toList params (sourceData source constructors) output.1 ∧
      output.2.2.2.toList = output.1.typ :: output.1.ctors.toList.map (·.typ) :=
  compile_correct reader base self names params bindings context (sourceData source constructors)
    arity scope ctorScope aligned external before after output ready ran

end Ix.CompileCert.InductiveEmission
