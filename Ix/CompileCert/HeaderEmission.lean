import Ix.CompileCert.MetadataErasure

/-! Actual one-expression axiom and quotient payload compilation. The source
type's self scope is explicit; the installed mutual context is never replaced.
Metadata contributes only state/reader-preservation obligations. -/

namespace Ix.CompileCert.HeaderEmission

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

inductive Source where
  | axio (value : AxiomVal)
  | quot (value : QuotVal)

def Source.cnst : Source → ConstantVal
  | .axio value => value.cnst
  | .quot value => value.cnst

def payload (source : Source) (type : Ixon.Expr) : Ixon.ConstantInfo :=
  match source with
  | .axio value => .axio ⟨value.isUnsafe, value.cnst.levelParams.size.toUInt64, type⟩
  | .quot value => .quot ⟨convertQuotKind value.kind, value.cnst.levelParams.size.toUInt64, type⟩

def finish (source : Source) (type : Ixon.Expr) (root : UInt64) : CompileM (Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr) :=
  match source with
  | .axio value => (fun output => (.axio output.1, output.2)) <$> finishAxiomCompilation value type root
  | .quot value => (fun output => (.quot output.1, output.2)) <$> finishQuotientCompilation value type root

def compile (source : Source) : CompileM (Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr) :=
  match source with
  | .axio value => (fun output => (.axio output.1, output.2)) <$> compileAxiom value
  | .quot value => (fun output => (.quot output.1, output.2)) <$> compileQuotient value

def body (source : Source) : CompileM (Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr) := do
  let (type, root) ← compileExpr source.cnst.type
  finish source type root

def contextFor (source : Source) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with current := source.cnst.name, univCtx := source.cnst.levelParams.toList })

theorem compile_run (source : Source) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (compile source) context before = rawRun (body source) (contextFor source context) (DefinitionEmission.prepared before) := by
  cases source <;>
    simp only [compile, body, finish, Source.cnst, compileAxiom, compileQuotient,
      withCurrent, withUnivCtx, resetArena, map_eq_pure_bind,
      DefinitionEmission.rawRun_withBlockEnv, rawRun_bind, rawRun_modify, rawRun_pure,
      contextFor, DefinitionEmission.prepared]
  all_goals
    rename_i value
    cases compiled : rawRun (compileExpr value.cnst.type)
      (context.1, { context.2 with current := value.cnst.name, univCtx := value.cnst.levelParams.toList })
      (DefinitionEmission.prepared before) with
    | mk result state =>
      simp only [DefinitionEmission.prepared] at compiled
      rw [compiled]
      cases result <;> rfl

def finishNames (source : Source) : CompileM Unit := do
  compileName source.cnst.name
  compileNames source.cnst.levelParams

theorem finish_run (source : Source) (type : Ixon.Expr) (root : UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ metadata, rawRun (finish source type root) context before =
      rawRun (do
        let _ ← checkedTableCount "declaration universe parameters" source.cnst.levelParams.size
        finishNames source
        pure (payload source type, metadata, type)) context (DefinitionEmission.drained before) := by
  cases source <;>
    simp only [finish, finishAxiomCompilation, finishQuotientCompilation, takeArena,
      takeMetaSharing, takeMetaRefs, takeUnivPatches, clearExprCache, map_eq_pure_bind,
      bind_assoc, pure_bind, rawRun_bind, Interning.rawRun_modifyGet, rawRun_modify,
      finishNames, Source.cnst, payload, DefinitionEmission.drained, rawRun_pure]
  all_goals exact ⟨_, rfl⟩

section Finish

variable (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
  (self : Nat → Option Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)

theorem count_preserves (label : String) (count : Nat) :
    DefinitionEmission.Preserves reader base param self bindings context (checkedTableCount label count) := by
  intro before clean
  rw [Interning.checkedTableCount_state]
  exact ⟨clean, ExpressionState.extends_refl _⟩

theorem names_preserves (source : Source) (aligned : ∀ address, reader.blob address = context.1.blobs.get? address) :
    DefinitionEmission.Preserves reader base param self bindings context (finishNames source) :=
  DefinitionEmission.Preserves.bind reader base param self bindings context
    (DefinitionEmission.Preserves.compileName reader base param self bindings context _ aligned)
    (fun _ => DefinitionEmission.Preserves.compileNames reader base param self bindings context _ aligned)

theorem finish_correct (source : Source) (type : Ixon.Expr) (root : UInt64)
    (before after : BlockState) (output : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr)
    (sound : ExpressionState.StateSound bindings before) (mode : before.p3MetaMode = false)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (ran : rawRun (finish source type root) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends (ExpressionRead.blockReader reader base param self before).ecx
        (ExpressionRead.blockReader reader base param self after).ecx ∧
      output.1 = payload source type ∧ output.2.2 = type := by
  obtain ⟨metadata, expanded⟩ := finish_run source type root context before
  rw [expanded] at ran
  let action : CompileM Unit := do
    let _ ← checkedTableCount "declaration universe parameters" source.cnst.levelParams.size
    finishNames source
  have grouped : rawRun (do
      action
      pure (payload source type, metadata, type)) context (DefinitionEmission.drained before) = (.ok output, after) := by
    simpa only [action, bind_assoc] using ran
  obtain ⟨done, middle, checkedRun, returned⟩ := PreseedReferences.bind_ok _ _ context _ output after grouped
  rw [rawRun_pure] at returned
  obtain ⟨outEq, stateEq⟩ := Prod.mk.inj returned
  cases stateEq
  have preserved := DefinitionEmission.Preserves.bind reader base param self bindings context
    (count_preserves reader base param self bindings context "declaration universe parameters" source.cnst.levelParams.size)
    (fun _ => names_preserves reader base param self bindings context source aligned)
    (DefinitionEmission.drained before) (DefinitionEmission.drained_clean bindings before sound mode)
  change DefinitionEmission.Clean bindings (rawRun action context (DefinitionEmission.drained before)).2 ∧ _ at preserved
  rw [checkedRun] at preserved
  rw [DefinitionEmission.drained_reader reader base param self before mode] at preserved
  cases Except.ok.inj outEq
  exact ⟨preserved.1, preserved.2, rfl, rfl⟩

end Finish

def Related (reader : Kernel.Reader.MemberReader) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (source : Source) (info : Ixon.ConstantInfo) : Prop :=
  ∃ type value, info = payload source type ∧
    ExpressionState.Related names source.cnst.levelParams.toList params source.cnst.type value ∧ reader.read type = .ok value

theorem body_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Source) (arity : params.length = context.2.univCtx.length)
    (parameterContext : context.2.univCtx = source.cnst.levelParams.toList)
    (scope : ExpressionScope.NoSelf context.2 source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (body source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) (fun _ => none) after) names params source output.1 := by
  rw [body] at ran
  obtain ⟨type, middle, compiled, finished⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have checked := MetadataErasure.compile_scoped reader base (fun _ => none) names params bindings context arity aligned external
    source.cnst.type (ExpressionScope.NoSelf.scoped _ _ scope _ names) before middle type clean compiled
  obtain ⟨value, related, read⟩ := checked.1.2.2 type rfl
  have finalized := finish_correct reader base (Kernel.Reader.paramOf params) (fun _ => none) bindings context source type.1 type.2
    middle after output checked.1.1.1 checked.2 aligned finished
  have grows := ExpressionRead.convExpr_preserves finalized.2.1
    (table := #[]) (nextTable := #[]) (by intros; assumption) type.1
  refine ⟨finalized.1, type.1, value, finalized.2.2.1, ?_, grows value read⟩
  simpa only [parameterContext] using related

theorem compile_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : Source) (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.NoSelf context.2 source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : Ixon.ConstantInfo × Ixon.ConstantMeta × Ixon.Expr)
    (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compile source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) (fun _ => none) after) names params source output.1 := by
  rw [compile_run] at ran
  exact body_correct reader base names params bindings (contextFor source context) source (by simpa [contextFor] using arity)
    rfl scope aligned external _ after output (DefinitionEmission.prepared_clean bindings before ready) ran

end Ix.CompileCert.HeaderEmission
