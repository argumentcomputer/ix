import Ix.CompileCert.InductiveSharing
import Ix.CompileCert.FamilyWire

/-! Source-related types and exact bytes in the inductive block actually
returned by production compilation, including preseeding and family sharing.
The whole-record reader, recursor family and admission remain separate. -/

namespace Ix.CompileCert.InductiveBlock

open Ix Ix.CompileM Ix.CompileCert.HeadWriterFrame

/-- Exact production serialization and address computation. No name-metadata
value or address-injectivity premise is involved. -/
def Wrapped (source : InductiveVal) (metadata : Ixon.ConstantMeta)
    (constructors : Array (Name × Ixon.ConstantMeta)) (output : BlockResult) : Prop :=
  output.blockBytes = Ixon.serConstant output.block ∧
    output.blockAddr = Address.blake3 output.blockBytes ∧
    output.projections = buildInductiveProjections source metadata constructors output.blockAddr ∧
    output.classNames = #[]

theorem finish_run (source : InductiveVal) (ind : Ixon.Inductive) (metadata : Ixon.ConstantMeta)
    (constructors : Array (Name × Ixon.ConstantMeta)) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (finishInductiveFamilyBlock source ind metadata constructors) context before = (.ok output, after)) :
    after = before ∧
      buildConstantWithSharing context.1.sharingLimits (.muts #[.indc ind]) before.refs before.univs = .ok output.block ∧
      Wrapped source metadata constructors output := by
  unfold finishInductiveFamilyBlock at ran
  obtain ⟨count, middle, guarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := Interning.checkedTableCount_state "inductive constructors" source.ctors.size context before
  rw [guarded] at same
  dsimp only at same
  subst middle
  obtain ⟨pairCount, middle, pairGuarded, rest⟩ := PreseedReferences.bind_ok _ _ context before output after rest
  have pairSame := Interning.checkedTableCount_state "constructor projections" constructors.size context before
  rw [pairGuarded] at pairSame
  dsimp only at pairSame
  subst middle
  rw [rawRun_bind, rawRun_get] at rest
  obtain ⟨block, finalState, built, returned⟩ := PreseedReferences.bind_ok _ _ context before output after rest
  rw [DefinitionBlock.rawRun_timedC, FamilyWire.build_block_run] at built
  have buildResult := congrArg Prod.fst built
  have buildState := congrArg Prod.snd built
  dsimp only at buildState
  subst finalState
  rw [rawRun_pure] at returned
  obtain ⟨values, states⟩ := Prod.mk.inj returned
  cases Except.ok.inj values
  exact ⟨states.symm, buildResult, rfl, rfl, rfl, rfl⟩

theorem family_run (source : InductiveVal) (constructors : Array ConstructorVal)
    (context : CompileEnv × BlockEnv) (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileInductiveFamilyBlock source constructors) context before = (.ok output, after)) :
    ∃ payload : Ixon.Inductive × Ixon.ConstantMeta × Array (Name × Ixon.ConstantMeta) × Array Ixon.Expr,
      rawRun (compileInductive source constructors) context before = (.ok payload, after) ∧
      buildConstantWithSharing context.1.sharingLimits (.muts #[.indc payload.1]) after.refs after.univs = .ok output.block ∧
      Wrapped source payload.2.1 payload.2.2.1 output := by
  rw [compileInductiveFamilyBlock] at ran
  obtain ⟨payload, middle, compiled, finished⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have finalizer := finish_run source payload.1 payload.2.1 payload.2.2.1 context middle after output finished
  cases finalizer.1
  exact ⟨payload, compiled, finalizer.2⟩

def Related (reader : Kernel.Reader.Ctx) (self : Nat → Option Kernel.Name)
    (names : Name → Kernel.Name → Prop) (params : List Kernel.Name)
    (state : BlockState) (source : InductiveVal) (constructors : Array ConstructorVal) (output : BlockResult) : Prop :=
  (∃ metadata pairs, Wrapped source metadata pairs output) ∧
    ∃ target, output.block.info = .muts #[.indc target] ∧
      InductiveEmission.Related
        (Kernel.Reader.MemberReader.mk' (SharingRead.blobContext reader state) output.block
          (Kernel.Reader.paramOf params) self)
        names source.cnst.levelParams.toList params (InductiveEmission.sourceData source constructors) target

theorem family_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors,
      ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : BlockResult) (ready : DefinitionEmission.Ready bindings before)
    (ran : rawRun (compileInductiveFamilyBlock source constructors) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Related reader self names params after source constructors output := by
  obtain ⟨payload, compiled, shared, wrapped⟩ := family_run source constructors context before after output ran
  have emitted := InductiveEmission.ordinary_correct reader base self names params bindings context source constructors
    arity scope ctorScope aligned external before after payload ready compiled
  have meaning := InductiveSharing.build_payload reader base self names source.cnst.levelParams.toList params after
    emitted.1.2.2 (InductiveEmission.sourceData source constructors) payload.1 emitted.2.2.1
    context.1.sharingLimits output.block shared
  exact ⟨emitted.1, ⟨payload.2.1, payload.2.2.1, wrapped⟩, meaning⟩

/-- The preseeded family compiler supplies the actual source-related shared
block and byte round-trip together. Table readiness and source scope remain
caller obligations; no suitable output artifact is assumed. -/
theorem family_info_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors,
      ExpressionScope.Scoped (ExpressionScope.SelfName context.2 self names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : BlockResult)
    (ready : DefinitionEmission.Ready bindings before)
    (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileInductiveFamilyInfo source constructors) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Related reader self names params after source constructors output ∧
      Sharing.Verify.BlockResultCodecWF output := by
  have codec := FamilyWire.inductiveFamilyInfo_codec source constructors context bindings before after output ready tables widths ran
  rw [compileInductiveFamilyInfo] at ran
  obtain ⟨done, middle, seeded, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  cases done
  have prepared := PreseedState.preseed_ready_checked context (inductivePreseedExprs source constructors)
    bindings before middle ready seeded
  have meaning := family_correct reader base self names params bindings context source constructors
    arity scope ctorScope aligned external middle after output prepared.1 compiled
  exact ⟨meaning.1, meaning.2, codec⟩

theorem constructors_context (sources : List Name) (initial : Array ConstructorVal)
    (environment : CompileEnv) (first last : BlockEnv) (state : BlockState) :
    rawRun (collectInductiveConstructors sources initial) (environment, first) state =
      rawRun (collectInductiveConstructors sources initial) (environment, last) state := by
  induction sources generalizing initial with
  | nil => rfl
  | cons source rest ih =>
    simp only [collectInductiveConstructors, rawRun_bind, findConst, rawRun_read]
    cases environment.env.get? source with
    | none => rfl
    | some value =>
      cases value <;> first | rfl | exact ih _

def familyContext (source : InductiveVal) (constructors : Array ConstructorVal)
    (context : CompileEnv × BlockEnv) : CompileEnv × BlockEnv :=
  (context.1, { context.2 with mutCtx := buildInductiveMutCtx source constructors })

/-- Actual source lookup supplies the constructor array, preserving state,
before the production driver installs the family's real mutual context. -/
theorem info_run (source : InductiveVal) (context : CompileEnv × BlockEnv)
    (before after : BlockState) (output : BlockResult)
    (ran : rawRun (compileInductiveInfo source) context before = (.ok output, after)) :
    ∃ constructors, rawRun (lookupInductiveConstructors source) context before = (.ok constructors, before) ∧
      rawRun (compileInductiveFamilyInfo source constructors) (familyContext source constructors context) before = (.ok output, after) := by
  rw [compileInductiveInfo] at ran
  obtain ⟨constructors, middle, found, compiled⟩ := PreseedReferences.bind_ok _ _ context before output after ran
  have same := FamilyWire.constructors_state source.ctors.toList #[] context before
  change (rawRun (lookupInductiveConstructors source) context before).2 = before at same
  rw [found] at same
  dsimp only at same
  subst middle
  exact ⟨constructors, found, compiled⟩

theorem info_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.Scoped
      (ExpressionScope.SelfName (familyContext source constructors context).2 self names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors, ExpressionScope.Scoped
      (ExpressionScope.SelfName (familyContext source constructors context).2 self names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : BlockResult)
    (found : (rawRun (lookupInductiveConstructors source) context before).1 = .ok constructors)
    (ready : DefinitionEmission.Ready bindings before)
    (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileInductiveInfo source) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Related reader self names params after source constructors output ∧
      Sharing.Verify.BlockResultCodecWF output := by
  obtain ⟨actual, actualLookup, compiled⟩ := info_run source context before after output ran
  have same : actual = constructors := Except.ok.inj ((congrArg Prod.fst actualLookup).symm.trans found)
  subst actual
  exact family_info_correct reader base self names params bindings (familyContext source constructors context)
    source constructors arity scope ctorScope aligned external before after output ready tables widths compiled

/-- Public inductive dispatch retains exact lookup, family initialization,
preseeding, shared source-related payloads and the returned byte artifact. -/
theorem constant_correct (reader : Kernel.Reader.Ctx) (base : Ixon.Constant)
    (self : Nat → Option Kernel.Name) (names : Name → Kernel.Name → Prop)
    (params : List Kernel.Name) (bindings : ExpressionState.Bindings) (context : CompileEnv × BlockEnv)
    (source : InductiveVal) (constructors : Array ConstructorVal)
    (arity : params.length = source.cnst.levelParams.size)
    (scope : ExpressionScope.Scoped
      (ExpressionScope.SelfName (familyContext source constructors context).2 self names) source.cnst.type)
    (ctorScope : ∀ ctor ∈ constructors, ExpressionScope.Scoped
      (ExpressionScope.SelfName (familyContext source constructors context).2 self names) ctor.cnst.type)
    (aligned : ∀ address, reader.blob address = context.1.blobs.get? address)
    (external : ExpressionState.BindingsCorrect context.1 bindings reader names)
    (before after : BlockState) (output : BlockResult)
    (found : (rawRun (lookupInductiveConstructors source) context before).1 = .ok constructors)
    (ready : DefinitionEmission.Ready bindings before)
    (tables : Sharing.Verify.BlockWireTablesWF before)
    (widths : ReferenceWidths.LookupWidths context.1 before)
    (ran : rawRun (compileConstantInfo (.inductInfo source)) context before = (.ok output, after)) :
    DefinitionEmission.Clean bindings after ∧ Related reader self names params after source constructors output ∧
      Sharing.Verify.BlockResultCodecWF output := by
  apply info_correct reader base self names params bindings
    (DefinitionReading.singletonContext source.cnst.name context) source constructors
    arity scope ctorScope aligned external before after output _ ready tables widths ran
  change (rawRun (collectInductiveConstructors source.ctors.toList #[])
    (context.1, (DefinitionReading.singletonContext source.cnst.name context).2) before).1 = .ok constructors
  rw [constructors_context source.ctors.toList #[] context.1 _ context.2 before]
  exact found

end Ix.CompileCert.InductiveBlock
