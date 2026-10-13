import Ix.CompileCert.HeaderEmission
import Ix.CompileCert.DeclarationHeaders

/-! Source-related constructor payloads through the actual production loop.
Constructors inherit their family's universe context and raw-universe cache.
Only anonymous fields and type reading enter the relation; metadata writes
contribute state preservation and reader extension. -/

namespace Ix.CompileCert.ConstructorEmission

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

/-- The actual constructor initializer does not run `withUnivCtx`. -/
def reset (state : BlockState) : BlockState :=
  { state with
    arena := {}, metaUnivs := #[], metaUnivsIndex := {},
    univPatches := #[], p3MetaRefs := #[], p3MetaRefsIndex := {}, p3Records := {} }

theorem reset_clean (bindings : ExpressionState.Bindings) (before : BlockState)
    (clean : DefinitionEmission.Clean bindings before) :
    DefinitionEmission.Clean bindings (reset before) :=
  ⟨⟨⟨clean.1.1.rawCache, clean.1.1.canonCache, clean.1.1.tables.1,
    Interning.IndexSound.empty⟩, clean.1.2.1, Interning.IndexSound.empty,
    clean.1.2.2.2⟩, clean.2.1, clean.2.2⟩

theorem reset_reader (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (param : Nat → Kernel.Name) (self : Nat → Option Kernel.Name)
    (before : BlockState) (mode : before.p3MetaMode = false) :
    ExpressionRead.blockReader reader base param self (reset before) =
      ExpressionRead.blockReader reader base param self before := by
  simp only [ExpressionRead.blockReader, reset, mode, Bool.false_eq_true, ↓reduceIte]

def payload (source : ConstructorVal) (type : Ixon.Expr) : Ixon.Constructor :=
  { isUnsafe := source.isUnsafe, lvls := source.cnst.levelParams.size.toUInt64,
    cidx := source.cidx.toUInt64, params := source.numParams.toUInt64,
    fields := source.numFields.toUInt64, typ := type }

def body (source : ConstructorVal) : CompileM (Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr) := do
  let (type, root) ← compileExpr source.cnst.type
  finishConstructorCompilation source type root

def contextFor (source : ConstructorVal) (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with current := source.cnst.name })

theorem compile_run (source : ConstructorVal) (context : CompileEnv × BlockEnv) (before : BlockState) :
    rawRun (compileConstructor source) context before =
      rawRun (body source) (contextFor source context) (reset before) := by
  simp only [compileConstructor, withCurrent, resetArena, body,
    DefinitionEmission.rawRun_withBlockEnv, rawRun_bind, rawRun_modify, contextFor, reset]

def finishChecks (source : ConstructorVal) : CompileM Unit := do
  let _ ← checkedTableCount "declaration universe parameters" source.cnst.levelParams.size
  let _ ← checkedTableIndex "constructor index" source.cidx
  let _ ← checkedTableCount "constructor parameters" source.numParams
  let _ ← checkedTableCount "constructor fields" source.numFields
  compileName source.cnst.name
  compileNames source.cnst.levelParams

theorem finish_run (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64)
    (context : CompileEnv × BlockEnv) (before : BlockState) :
    ∃ metadata, rawRun (finishConstructorCompilation source type root) context before =
      rawRun (do
        finishChecks source
        pure (payload source type, metadata, type)) context (DefinitionEmission.drained before) := by
  simp only [finishConstructorCompilation, takeArena, takeMetaSharing, takeMetaRefs,
    takeUnivPatches, clearExprCache, rawRun_bind, Interning.rawRun_modifyGet, rawRun_modify,
    finishChecks, payload, DefinitionEmission.drained, bind_assoc, rawRun_pure]
  exact ⟨_, rfl⟩

section Finish

variable (reader : Kernel.Reader.Ctx) (base : Ixon.Constant) (param : Nat → Kernel.Name)
  (self : Nat → Option Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)

theorem index_preserves (label : String) (index : Nat) :
    DefinitionEmission.Preserves reader base param self bindings context (checkedTableIndex label index) := by
  intro before clean
  rw [Interning.checkedTableIndex_state]
  exact ⟨clean, ExpressionState.extends_refl _⟩

theorem checks_preserve (source : ConstructorVal)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address) :
    DefinitionEmission.Preserves reader base param self bindings context (finishChecks source) := by
  unfold finishChecks
  with_reducible repeat' first
    | exact HeaderEmission.count_preserves reader base param self bindings context _ _
    | exact index_preserves reader base param self bindings context _ _
    | exact DefinitionEmission.Preserves.compileName reader base param self bindings context _ aligned
    | exact DefinitionEmission.Preserves.compileNames reader base param self bindings context _ aligned
    | refine DefinitionEmission.Preserves.bind reader base param self bindings context ?_ (fun _ => ?_)

theorem finish_correct (source : ConstructorVal) (type : Ixon.Expr) (root : UInt64)
    (before after : BlockState) (output : Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr)
    (sound : ExpressionState.StateSound bindings before) (mode : before.p3MetaMode = false)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (ran : rawRun (finishConstructorCompilation source type root) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends (ExpressionRead.blockReader reader base param self before).ecx
        (ExpressionRead.blockReader reader base param self after).ecx ∧
      output.1 = payload source type ∧ output.2.2 = type := by
  obtain ⟨metadata, expanded⟩ := finish_run source type root context before
  rw [expanded] at ran
  obtain ⟨done, middle, checkedRun, returned⟩ :=
    PreseedReferences.bind_ok _ _ context _ output after ran
  rw [rawRun_pure] at returned
  obtain ⟨outEq, stateEq⟩ := Prod.mk.inj returned
  cases stateEq
  have preserved := checks_preserve reader base param self bindings context source aligned
    (DefinitionEmission.drained before) (DefinitionEmission.drained_clean bindings before sound mode)
  rw [checkedRun, DefinitionEmission.drained_reader reader base param self before mode] at preserved
  cases Except.ok.inj outEq
  exact ⟨preserved.1, preserved.2, rfl, rfl⟩

end Finish

/-- Exact natural header fields and source-related type in the inherited
universe context. Equality with the constructor's own parameter list is a
separate source-family fact, not an initializer assumption. -/
def Related (reader : Kernel.Reader.MemberReader) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name)
    (source : ConstructorVal) (target : Ixon.Constructor) : Prop :=
  target.isUnsafe = source.isUnsafe ∧ target.lvls.toNat = source.cnst.levelParams.size ∧
    target.cidx.toNat = source.cidx ∧ target.params.toNat = source.numParams ∧
    target.fields.toNat = source.numFields ∧
    ∃ type, ExpressionState.Related names sourceParams params source.cnst.type type ∧
      reader.read target.typ = .ok type

theorem related_grows (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (before after : BlockState)
    (growth : ExpressionRead.Extends
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx)
    (source : ConstructorVal) (target : Ixon.Constructor)
    (related : Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before)
      names sourceParams params source target) :
    Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
      names sourceParams params source target := by
  obtain ⟨safety, levels, index, parameters, fields, type, meaning, read⟩ := related
  exact ⟨safety, levels, index, parameters, fields, type, meaning,
    ExpressionRead.convExpr_preserves growth (table := #[]) (nextTable := #[])
      (by intros; assumption) target.typ type read⟩

theorem list_grows (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (sourceParams : List Name) (params : List Kernel.Name) (before after : BlockState)
    (growth : ExpressionRead.Extends
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
      (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx)
    (sources : List ConstructorVal) (targets : List Ixon.Constructor)
    (related : List.Forall₂
      (Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before)
        names sourceParams params) sources targets) :
    List.Forall₂
      (Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names sourceParams params) sources targets := by
  induction related with
  | nil => exact .nil
  | cons head rest ih =>
    exact .cons (related_grows reader base self names sourceParams params before after growth _ _ head) ih

theorem body_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : ConstructorVal) (arity : params.length = context.2.univCtx.length)
    (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (body source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names context.2.univCtx params source output.1 ∧ output.2.2 = output.1.typ := by
  rw [body] at ran
  obtain ⟨type, middle, compiled, finished⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have checked := MetadataErasure.compile_scoped reader base self names params bindings context arity aligned external
    source.cnst.type scope before middle type clean compiled
  obtain ⟨value, related, read⟩ := checked.1.2.2 type rfl
  have finalized := finish_correct reader base (Kernel.Reader.paramOf params) self bindings context source type.1 type.2
    middle after output checked.1.1.1 checked.2 aligned finished
  have headers := DeclarationHeaders.constructorHeader source type.1 type.2 context middle output after finished
  have grows := ExpressionRead.convExpr_preserves finalized.2.1
    (table := #[]) (nextTable := #[]) (by intros; assumption) type.1
  refine ⟨finalized.1, ExpressionState.extends_trans checked.1.2.1 finalized.2.1,
    ?_, by rw [finalized.2.2.1]; exact finalized.2.2.2⟩
  refine ⟨?_, headers.1, headers.2.1, headers.2.2.1, headers.2.2.2, value, related, ?_⟩
  · rw [finalized.2.2.1]; rfl
  · rw [finalized.2.2.1]; exact grows value read

theorem compile_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : ConstructorVal) (arity : params.length = context.2.univCtx.length)
    (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : Ixon.Constructor × Ixon.ConstantMeta × Ixon.Expr)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (compileConstructor source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
        names context.2.univCtx params source output.1 ∧ output.2.2 = output.1.typ := by
  rw [compile_run] at ran
  have result := body_correct reader base self names params bindings (contextFor source context)
    source arity scope aligned external (reset before) after output (reset_clean bindings before clean) ran
  rw [reset_reader reader base (Kernel.Reader.paramOf params) self before clean.2.2] at result
  exact result

/-- Every newly appended constructor is related in the final reader, so later
constructors cannot invalidate the types already compiled. Existing accumulator
payloads and expression roots are retained verbatim. -/
theorem constructors_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (sources : List ConstructorVal) (arity : params.length = context.2.univCtx.length)
    (scope : ∀ source ∈ sources,
      ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (initial : InductiveConstructorCompileState)
    (before after : BlockState) (output : InductiveConstructorCompileState)
    (clean : DefinitionEmission.Clean bindings before)
    (ran : rawRun (compileInductiveConstructors sources initial) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧
      ExpressionRead.Extends
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self before).ecx
        (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after).ecx ∧
      ∃ targets, output.ctors.toList = initial.ctors.toList ++ targets ∧
        List.Forall₂
          (Related (ExpressionRead.blockReader reader base (Kernel.Reader.paramOf params) self after)
            names context.2.univCtx params) sources targets ∧
        output.ctorExprs.toList = initial.ctorExprs.toList ++ targets.map (·.typ) := by
  induction sources generalizing initial before with
  | nil =>
    change ((Except.ok initial : Except CompileError _), before) = (.ok output, after) at ran
    obtain ⟨outEq, stateEq⟩ := Prod.mk.inj ran
    cases stateEq
    cases Except.ok.inj outEq
    exact ⟨clean, ExpressionState.extends_refl _, [], by simp, .nil, by simp⟩
  | cons source rest ih =>
    rw [compileInductiveConstructors] at ran
    obtain ⟨compiled, middle, first, last⟩ := PreseedReferences.bind_ok _ _ context before output after ran
    have head := compile_correct reader base self names params bindings context source arity
      (scope source (by simp)) aligned external before middle compiled clean first
    have tail := ih (fun source present => scope source (by simp [present]))
      { ctors := initial.ctors.push compiled.1
        ctorMetaPairs := initial.ctorMetaPairs.push (source.cnst.name, compiled.2.1)
        ctorNameAddrs := initial.ctorNameAddrs.push source.cnst.name.getHash
        ctorExprs := initial.ctorExprs.push compiled.2.2 } middle head.1 last
    obtain ⟨targets, payloads, meanings, roots⟩ := tail.2.2
    refine ⟨tail.1, ExpressionState.extends_trans head.2.1 tail.2.1,
      compiled.1 :: targets, ?_, .cons ?_ meanings, ?_⟩
    · simpa only [Array.toList_push, List.append_assoc, List.singleton_append] using payloads
    · exact related_grows reader base self names context.2.univCtx params middle after
        tail.2.1 source compiled.1 head.2.2.1
    · simpa only [Array.toList_push, head.2.2.2, List.map_cons, List.append_assoc,
        List.singleton_append] using roots

end Ix.CompileCert.ConstructorEmission
